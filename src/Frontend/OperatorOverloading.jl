#= /*
* This file is part of OpenModelica.
*
* Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
* c/o Linköpings universitet, Department of Computer and Information Science,
* SE-58183 Linköping, Sweden.
*
* All rights reserved.
*
* THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
* THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
* ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
* RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
* ACCORDING TO RECIPIENTS CHOICE.
*
* The OpenModelica software and the Open Source Modelica
* Consortium (OSMC) Public License (OSMC-PL) are obtained
* from OSMC, either from the above address,
* from the URLs: http:www.ida.liu.se/projects/OpenModelica or
* http:www.openmodelica.org, and in the OpenModelica distribution.
* GNU version 3 is obtained from: http:www.gnu.org/copyleft/gpl.html.
*
* This program is distributed WITHOUT ANY WARRANTY; without
* even the implied warranty of  MERCHANTABILITY or FITNESS
* FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
* IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
*
* See the full OSMC Public License conditions for more details.
*
*/ =#

module OperatorOverloading
using MetaModelica
using ExportAll

  import Absyn
import AbsynUtil
import DAE
import FCore
import FCoreUtil
import Prefix
import SCode
import Util

import Ceval
import ClassInf
import Config
import Debug
import Dump
import Error
import Expression
import ExpressionDump
import ExpressionSimplify
import FGraph
import Flags
import Global
import Inline
import ListUtil
import Lookup
import PrefixUtil
import AbsynToSCode
import SCodeUtil
import Static
import Types
import Values

function binary(inCache::FCore.Cache, inEnv::FCore.Graph, inOperator1::Absyn.Operator, inProp1::DAE.Properties, inExp1::DAE.Exp, inProp2::DAE.Properties, inExp2::DAE.Exp, AbExp::Absyn.Exp #= needed for function replaceOperatorWithFcall (not  really sure what is done in there though.) =#, AbExp1::Absyn.Exp #= We need this when/if we elaborate user defined operator functions =#, AbExp2::Absyn.Exp #= We need this when/if we elaborate user defined operator functions =#, inImpl::Bool, inPre::Prefix.PrefixType #= For error-messages only =#, inInfo::SourceInfo #= For error-messages only =#) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
  local outProp::DAE.Properties
  local outExp::DAE.Exp
  local outCache::FCore.Cache

  (outCache, outExp, outProp) = begin
    local cache::FCore.Cache
    local env::FCore.Graph
    local opList::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local type1::DAE.Type
    local type2::DAE.Type
    local otype::DAE.Type
    local exp1::DAE.Exp
    local exp2::DAE.Exp
    local exp::DAE.Exp
    local const1::DAE.Const
    local const2::DAE.Const
    local constVar::DAE.Const
    local oper::DAE.Operator
    local aboper::Absyn.Operator
    local prop::DAE.Properties
    local props1::DAE.Properties
    local props2::DAE.Properties
    local absexp1::Absyn.Exp
    local absexp2::Absyn.Exp
    local lastRound::Bool
    local n::DAE.Dimension
    local m1::DAE.Dimension
    local m2::DAE.Dimension
    local p::DAE.Dimension
    local functionTree::DAE.FunctionTree
    local didInline::Bool
    #=  handle tuple op non_tuple
    =#
    @match (inCache, inEnv, inOperator1, inProp1, inExp1, inProp2, inExp2) begin
      (_, _, _, props1 && DAE.PROP_TUPLE(__), _, DAE.PROP(__), _) where (! Config.acceptMetaModelicaGrammar())  => begin
        @match prop && DAE.PROP(type1, _) = Types.propTupleFirstProp(props1)
        exp = DAE.TSUB(inExp1, 1, type1)
        (cache, exp, prop) = binary(inCache, inEnv, inOperator1, prop, exp, inProp2, inExp2, AbExp, AbExp1, AbExp2, inImpl, inPre, inInfo)
        (cache, exp, prop)
      end

      (_, _, _, DAE.PROP(__), _, props2 && DAE.PROP_TUPLE(__), _) where (! Config.acceptMetaModelicaGrammar())  => begin
        @match prop && DAE.PROP(type2, _) = Types.propTupleFirstProp(props2)
        exp = DAE.TSUB(inExp2, 1, type2)
        (cache, exp, prop) = binary(inCache, inEnv, inOperator1, inProp1, inExp1, prop, exp, AbExp, AbExp1, AbExp2, inImpl, inPre, inInfo)
        (cache, exp, prop)
      end

      (cache, env, aboper, DAE.PROP(type1, const1), exp1, DAE.PROP(type2, const2), exp2)  => begin
        #=  handle non_tuple op tuple
        =#
        if Types.isRecord(Types.arrayElementType(type1)) || Types.isRecord(Types.arrayElementType(type2))
          (cache, exp, _, otype) = binaryUserdef(cache, env, aboper, inExp1, inExp2, type1, type2, inImpl, inPre, inInfo)
          functionTree = FCoreUtil.getFunctionTree(cache)
          (exp, _) = ExpressionSimplify.simplify1(exp)
          (exp, _, didInline, _) = Inline.inlineExp(exp, (SOME(functionTree), list(DAE.BUILTIN_EARLY_INLINE(), DAE.EARLY_INLINE())), DAE.emptyElementSource)
          exp = ExpressionSimplify.condsimplify(didInline, exp)
          constVar = Types.constAnd(const1, const2)
          prop = DAE.PROP(otype, constVar)
        else
          if Types.isBoxedType(type1) && Types.isBoxedType(type2)
            (exp1, type1) = Types.matchType(exp1, type1, Types.unboxedType(type1), true)
            (exp2, type2) = Types.matchType(exp2, type2, Types.unboxedType(type2), true)
          end
          (opList, type1, exp1, type2, exp2) = operatorsBinary(aboper, type1, exp1, type2, exp2)
          @match (oper, exp1 <| exp2 <| nil, otype) = deoverload(opList, list((exp1, type1), (exp2, type2)), AbExp, inPre, inInfo)
          constVar = Types.constAnd(const1, const2)
          exp = replaceOperatorWithFcall(AbExp, exp1, oper, SOME(exp2), constVar)
          exp = ExpressionSimplify.simplify(exp)
          prop = DAE.PROP(otype, constVar)
          warnUnsafeRelations(inEnv, AbExp, constVar, type1, type2, exp1, exp2, oper, inPre, inInfo)
        end
        #=  Overloaded records
        =#
        #=  Normal operator deoverloading
        =#
        #=  Do the MetaModelica type-casting here for simplicity
        =#
        (cache, exp, prop)
      end
    end
  end
  (outCache, outExp, outProp)
end

#= used to resolve unary operations.

also used to resolve user overloaded unary operators for operator records
It looks if there is an operator function defined for the specific
operation. If there is then it will call that function and returns the
resulting expression.  =#
function unary(inCache::FCore.Cache, inEnv::FCore.Graph, inOperator1::Absyn.Operator, inProp1::DAE.Properties, inExp1::DAE.Exp, AbExp::Absyn.Exp #= needed for function replaceOperatorWithFcall (not  really sure what is done in there though.) =#, AbExp1::Absyn.Exp #= We need this when/if we elaborate user defined operator functions =#, inImpl::Bool, inPre::Prefix.PrefixType #= For error-messages only =#, inInfo::SourceInfo #= For error-messages only =#) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
  local outProp::DAE.Properties
  local outExp::DAE.Exp
  local outCache::FCore.Cache

  (outCache, outExp, outProp) = begin
    local str1::String
    local cache::FCore.Cache
    local operNames::List{Absyn.Path}
    local path::Absyn.Path
    local operatorEnv::FCore.Graph
    local recordEnv::FCore.Graph
    local operatorCl::SCode.Element
    local types::List{DAE.Type}
    local env::FCore.Graph
    local opList::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local type1::DAE.Type
    local otype::DAE.Type
    local exp1::DAE.Exp
    local exp::DAE.Exp
    local constVar::DAE.Const
    local oper::DAE.Operator
    local aboper::Absyn.Operator
    local prop::DAE.Properties
    local absexp1::Absyn.Exp
    #=  handle op tuple
    =#
    @matchcontinue (inCache, inEnv, inOperator1, inProp1, inExp1, AbExp, AbExp1) begin
      (_, _, _, DAE.PROP_TUPLE(__), exp1, _, _)  => begin
        @match false = Config.acceptMetaModelicaGrammar()
        @match (@match DAE.PROP(type1, _) = prop) = Types.propTupleFirstProp(inProp1)
        exp = DAE.TSUB(exp1, 1, type1)
        (cache, exp, prop) = unary(inCache, inEnv, inOperator1, prop, exp, AbExp, AbExp1, inImpl, inPre, inInfo)
        (cache, exp, prop)
      end

      (_, _, aboper, DAE.PROP(type1, constVar), exp1, _, _)  => begin
        @match false = Types.isRecord(Types.arrayElementType(type1))
        opList = operatorsUnary(aboper)
        @match (oper, list(exp1), otype) = deoverload(opList, list((exp1, type1)), AbExp, inPre, inInfo)
        exp = replaceOperatorWithFcall(AbExp, exp1, oper, NONE(), constVar)
        prop = DAE.PROP(otype, constVar)
        (inCache, exp, prop)
      end

      (cache, env, aboper, DAE.PROP(type1, _), _, _, absexp1)  => begin
        path = getRecordPath(type1)
        path = AbsynUtil.makeFullyQualified(path)
        (cache, _, recordEnv) = Lookup.lookupClass(cache, env, path)
        str1 = "'" + Dump.opSymbolCompact(aboper) + "'"
        path = AbsynUtil.joinPaths(path, Absyn.IDENT(str1))
        (cache, operatorCl, operatorEnv) = Lookup.lookupClass(cache, recordEnv, path)
        @match true = SCodeUtil.isOperator(operatorCl)
        operNames = AbsynToSCode.getListofQualOperatorFuncsfromOperator(operatorCl)
        @match (cache, types && _ <| _) = Lookup.lookupFunctionsListInEnv(cache, operatorEnv, operNames, inInfo, nil)
        @match (cache, SOME((exp, prop))) = Static.elabCallArgs3(cache, env, types, path, list(absexp1), nil, inImpl, inPre, inInfo)
        (cache, exp, prop)
      end
    end
  end
  #=  (exp,_) = ExpressionSimplify.simplify(exp);
  =#
  #=  if we have a record check for overloaded operators
  =#
  #=  TODO: Improve this the same way we improved binary operators!
  =#
  (outCache, outExp, outProp)
end

#= This functions checks if the builtin function string is overloaded for opertor records =#
function string(inCache::FCore.Cache, inEnv::FCore.Graph, inExp1::Absyn.Exp, inImpl::Bool, inDoVect::Bool, inPre::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
  local outProp::DAE.Properties
  local outExp::DAE.Exp
  local outCache::FCore.Cache

  (outCache, outExp, outProp) = begin
    local str1::String
    local path::Absyn.Path
    local operNames::List{Absyn.Path}
    local recordEnv::FCore.Graph
    local operatorEnv::FCore.Graph
    local env::FCore.Graph
    local operatorCl::SCode.Element
    local cache::FCore.Cache
    local types::List{DAE.Type}
    local prop::DAE.Properties
    local type1::DAE.Type
    local exp1::Absyn.Exp
    local daeExp::DAE.Exp
    local restargs::List{Absyn.Exp}
    local nargs::List{Absyn.NamedArg}
    @match (inCache, inEnv, inExp1) begin
      (cache, env, Absyn.CALL(function_ = Absyn.CREF_IDENT("String", _), functionArgs = Absyn.FUNCTIONARGS(args = exp1 <| restargs, argNames = nargs)))  => begin
        @match (cache, _, DAE.PROP(type1, _)) = Static.elabExp(cache, env, exp1, inImpl, inDoVect, inPre, inInfo)
        path = getRecordPath(type1)
        path = AbsynUtil.makeFullyQualified(path)
        (cache, _, recordEnv) = Lookup.lookupClass(cache, env, path)
        str1 = "'String'"
        path = AbsynUtil.joinPaths(path, Absyn.IDENT(str1))
        (cache, operatorCl, operatorEnv) = Lookup.lookupClass(cache, recordEnv, path)
        @match true = SCodeUtil.isOperator(operatorCl)
        operNames = AbsynToSCode.getListofQualOperatorFuncsfromOperator(operatorCl)
        @match (cache, types && _ <| _) = Lookup.lookupFunctionsListInEnv(cache, operatorEnv, operNames, inInfo, nil)
        @match (cache, SOME((daeExp, prop))) = Static.elabCallArgs3(cache, env, types, path, _cons(exp1, restargs), nargs, inImpl, inPre, inInfo)
        (cache, daeExp, prop)
      end
    end
  end
  (outCache, outExp, outProp)
end

#= Given a list of parameter types and an argument list, this
function tries to match the two, promoting the type of
arguments when necessary. =#
function elabArglist(inTypes::List{<:DAE.Type}, inArgs::List{<:Tuple{<:DAE.Exp, DAE.Type}}) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
  local outTypes::List{DAE.Type}
  local outArgs::List{DAE.Exp}

  (outArgs, outTypes) = begin
    local arg_1::DAE.Exp
    local arg::DAE.Exp
    local atype_1::DAE.Type
    local pt::DAE.Type
    local atype::DAE.Type
    local args_1::List{DAE.Exp}
    local atypes_1::List{DAE.Type}
    local pts::List{DAE.Type}
    local args::List{Tuple{DAE.Exp, DAE.Type}}
    #=  empty lists
    =#
    @match (inTypes, inArgs) begin
      ( nil(),  nil())  => begin
        (nil, nil)
      end

      (pt <| pts, (arg, atype) <| args)  => begin
        (arg_1, atype_1) = Types.matchType(arg, atype, pt, false)
        (args_1, atypes_1) = elabArglist(pts, args)
        (_cons(arg_1, args_1), _cons(atype_1, atypes_1))
      end
    end
  end
  #=  we have something
  =#
  (outArgs, outTypes)
end

module AvlTreePathPathEnv


using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

  import Absyn

using BaseAvlTree
Key = Absyn.Path
Value = Absyn.Path

#= TODO! FIXME! handle redeclare ... extends stuff
redeclare function extends keyStr
algorithm
outString := AbsynUtil.pathString(inKey);
end keyStr;
redeclare function extends valueStr
algorithm
outString := AbsynUtil.pathString(inValue);
end valueStr;
redeclare function extends keyCompare
algorithm
outResult := AbsynUtil.pathCompareNoQual(inKey1,inKey2);
end keyCompare;
redeclare function addConflictDefault = addConflictKeep;
=#

addConflictDefault = addConflictKeep

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

module AvlTreePathOperatorTypes


using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

  import Absyn

using BaseAvlTree
Key = Absyn.Path
Value = List

#= TODO! FIXME! handle redeclare ... extends stuff
redeclare function extends keyStr
algorithm
outString := AbsynUtil.pathString(inKey);
end keyStr;
redeclare function extends valueStr
algorithm
outString := Types.unparseType(DAE.T_METATUPLE(inValue));
end valueStr;
redeclare function extends keyCompare
algorithm
outResult := AbsynUtil.pathCompareNoQual(inKey1,inKey2);
end keyCompare;
redeclare function addConflictDefault = addConflictKeep;
=#

addConflictDefault = addConflictKeep

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

function initCache()
  setGlobalRoot(Global.operatorOverloadingCache, (AvlTreePathPathEnv.EMPTY(), AvlTreePathOperatorTypes.EMPTY()))
end

function deoverloadBinaryUserdefNoConstructor(inTypeList::List{<:DAE.Type}, inLhs::DAE.Exp, inRhs::DAE.Exp, lhsType::DAE.Type, rhsType::DAE.Type, inAcc::List{<:Tuple{<:DAE.Exp, Option{<:DAE.Type}}}) ::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local outExps::List{Tuple{DAE.Exp, Option{DAE.Type}}}

  outExps = begin
    local types::List{DAE.Type}
    local scalartypes::List{DAE.Type}
    local arraytypes::List{DAE.Type}
    local cache::FCore.Cache
    local daeExp::DAE.Exp
    local prop::DAE.Properties
    local str1::String
    local restArgs::List{DAE.FuncArg}
    local funcTy::DAE.Type
    local ty::DAE.Type
    local ty1::DAE.Type
    local ty2::DAE.Type
    local attr::DAE.FunctionAttributes
    local path::Absyn.Path
    local lhs::DAE.Exp
    local rhs::DAE.Exp
    local acc::List{Tuple{DAE.Exp, Option{DAE.Type}}}
    local tpl::Tuple{DAE.Exp, Option{DAE.Type}}
    #=  Matching types. Yay.
    =#
    @matchcontinue (inTypeList, inLhs, inRhs, lhsType, rhsType, inAcc) begin
      (DAE.T_FUNCTION(path = path, funcResultType = ty, functionAttributes = attr, funcArg = DAE.FUNCARG(ty = ty1) <| DAE.FUNCARG(ty = ty2) <| restArgs) <| types, _, _, _, _, acc)  => begin
        (lhs, _) = Types.matchType(inLhs, lhsType, ty1, false)
        (rhs, _) = Types.matchType(inRhs, rhsType, ty2, false)
        daeExp = makeCallFillRestDefaults(path, list(lhs, rhs), restArgs, Types.makeCallAttr(ty, attr))
        tpl = (daeExp, overloadFoldType(ty1, ty2, ty))
        acc = deoverloadBinaryUserdefNoConstructor(types, inLhs, inRhs, lhsType, rhsType, _cons(tpl, acc))
        acc
      end

      (_ <| types, _, _, _, _, _)  => begin
        acc = deoverloadBinaryUserdefNoConstructor(types, inLhs, inRhs, lhsType, rhsType, inAcc)
        acc
      end

      ( nil(), _, _, _, _, _)  => begin
        inAcc
      end
    end
  end
  outExps
end

#= It is only possible to fold this overloaded function if it has the same inputs and output =#
function overloadFoldType(inType1::DAE.Type, inType2::DAE.Type, inType3::DAE.Type) ::Option{DAE.Type}
  local optType::Option{DAE.Type}

  optType = if Types.equivtypesOrRecordSubtypeOf(inType1, inType2) && Types.equivtypesOrRecordSubtypeOf(inType1, inType3)
    SOME(inType1)
  else
    NONE()
  end
  optType
end

function deoverloadBinaryUserdefNoConstructorListLhs(types::List{<:DAE.Type}, inLhs::List{<:DAE.Exp}, inRhs::DAE.Exp, rhsType::DAE.Type, inAcc::List{<:Tuple{<:DAE.Exp, Option{<:DAE.Type}}}) ::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local outExps::List{Tuple{DAE.Exp, Option{DAE.Type}}}

  outExps = begin
    local scalartypes::List{DAE.Type}
    local arraytypes::List{DAE.Type}
    local cache::FCore.Cache
    local prop::DAE.Properties
    local str1::String
    local restArgs::List{DAE.FuncArg}
    local ty::DAE.Type
    local ty1::DAE.Type
    local ty2::DAE.Type
    local attr::DAE.FunctionAttributes
    local path::Absyn.Path
    local lhs::DAE.Exp
    local rhs::DAE.Exp
    local acc::List{Tuple{DAE.Exp, Option{DAE.Type}}}
    local rest::List{DAE.Exp}
    #=  Matching types. Yay. =#
    @match (types, inLhs, inRhs, rhsType, inAcc) begin
      (_, lhs <| rest, _, _, acc)  => begin
        acc = deoverloadBinaryUserdefNoConstructor(types, lhs, inRhs, Expression.typeof(lhs), rhsType, acc)
        acc = deoverloadBinaryUserdefNoConstructorListLhs(types, rest, inRhs, rhsType, acc)
        acc
      end

      _  => begin
        inAcc
      end
    end
  end
  outExps
end

function deoverloadBinaryUserdefNoConstructorListRhs(types::List{<:DAE.Type}, inLhs::DAE.Exp, inRhs::List{<:DAE.Exp}, lhsType::DAE.Type, inAcc::List{<:Tuple{<:DAE.Exp, Option{<:DAE.Type}}}) ::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local outExps::List{Tuple{DAE.Exp, Option{DAE.Type}}}

  outExps = begin
    local scalartypes::List{DAE.Type}
    local arraytypes::List{DAE.Type}
    local cache::FCore.Cache
    local prop::DAE.Properties
    local str1::String
    local restArgs::List{DAE.FuncArg}
    local ty::DAE.Type
    local ty1::DAE.Type
    local ty2::DAE.Type
    local attr::DAE.FunctionAttributes
    local path::Absyn.Path
    local lhs::DAE.Exp
    local rhs::DAE.Exp
    local acc::List{Tuple{DAE.Exp, Option{DAE.Type}}}
    local rest::List{DAE.Exp}
    #=  Matching types. Yay.
    =#
    @match (types, inLhs, inRhs, lhsType, inAcc) begin
      (_, _, rhs <| rest, _, acc)  => begin
        acc = deoverloadBinaryUserdefNoConstructor(types, inLhs, rhs, lhsType, Expression.typeof(rhs), acc)
        acc = deoverloadBinaryUserdefNoConstructorListRhs(types, inLhs, rest, lhsType, acc)
        acc
      end

      _  => begin
        inAcc
      end
    end
  end
  outExps
end

function deoverloadUnaryUserdefNoConstructor(inTypeList::List{<:DAE.Type}, inExp::DAE.Exp, inType::DAE.Type, inAcc::List{<:DAE.Exp}) ::List{DAE.Exp}
  local outExps::List{DAE.Exp}

  outExps = begin
    local types::List{DAE.Type}
    local scalartypes::List{DAE.Type}
    local arraytypes::List{DAE.Type}
    local cache::FCore.Cache
    local exp::DAE.Exp
    local daeExp::DAE.Exp
    local prop::DAE.Properties
    local str1::String
    local restArgs::List{DAE.FuncArg}
    local ty::DAE.Type
    local ty1::DAE.Type
    local ty2::DAE.Type
    local attr::DAE.FunctionAttributes
    local path::Absyn.Path
    local lhs::DAE.Exp
    local rhs::DAE.Exp
    local acc::List{DAE.Exp}
    #=  Matching types. Yay.
    =#
    @matchcontinue (inTypeList, inExp, inType, inAcc) begin
      (DAE.T_FUNCTION(path = path, funcResultType = ty, functionAttributes = attr, funcArg = DAE.FUNCARG(ty = ty1) <| restArgs) <| types, _, _, acc)  => begin
        (exp, _) = Types.matchType(inExp, inType, ty1, false)
        daeExp = makeCallFillRestDefaults(path, list(exp), restArgs, Types.makeCallAttr(ty, attr))
        acc = deoverloadUnaryUserdefNoConstructor(types, inExp, ty, _cons(daeExp, acc))
        acc
      end

      (_ <| types, _, _, _)  => begin
        acc = deoverloadUnaryUserdefNoConstructor(types, inExp, inType, inAcc)
        acc
      end

      ( nil(), _, _, _)  => begin
        inAcc
      end
    end
  end
  outExps
end

#= used to resolve overloaded binary operators for operator records
It looks if there is an operator function defined for the specific
operation. If there is then it will call that function and returns the
resulting expression.  =#
function binaryUserdef(inCache::FCore.Cache, inEnv::FCore.Graph, inOper::Absyn.Operator, inExp1::DAE.Exp, inExp2::DAE.Exp, inType1::DAE.Type, inType2::DAE.Type, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, Option{DAE.Type}, DAE.Type}
  local outType::DAE.Type
  local foldType::Option{DAE.Type}
  local outExp::DAE.Exp
  local outCache::FCore.Cache

  (outCache, outExp, foldType, outType) = begin
    local bool1::Bool
    local bool2::Bool
    local opStr::String
    local path::Absyn.Path
    local path2::Absyn.Path
    local operNames::List{Absyn.Path}
    local recordEnv::FCore.Graph
    local env::FCore.Graph
    local operatorCl::SCode.Element
    local cache::FCore.Cache
    local types::List{DAE.Type}
    local types1::List{DAE.Type}
    local types2::List{DAE.Type}
    local prop::DAE.Properties
    local type1::DAE.Type
    local type2::DAE.Type
    local exp1::DAE.Exp
    local exp2::DAE.Exp
    local op::Absyn.Operator
    local comRef::Absyn.ComponentRef
    local daeExp::DAE.Exp
    local exps::List{Tuple{DAE.Exp, Option{DAE.Type}}}
    @match (inCache, inEnv, inOper, inExp1, inExp2, inType1, inType2) begin
      (cache, env, op, exp1, exp2, type1, type2)  => begin
        bool1 = Types.arrayType(type1)
        bool2 = Types.arrayType(type2)
        if bool1 && bool2 && AbsynUtil.opIsElementWise(op)
          types = nil
        else
          opStr = "'" + Dump.opSymbolCompact(op) + "'"
          (cache, types1) = getOperatorFuncsOrEmpty(cache, env, list(type1), opStr, info, nil)
          (cache, types2) = getOperatorFuncsOrEmpty(cache, env, list(type2), opStr, info, nil)
          types = ListUtil.union(types1, types2)
          types = ListUtil.select1(types, isOperatorBinaryFunctionOrWarn, info)
        end
        exps = deoverloadBinaryUserdefNoConstructor(types, exp1, exp2, type1, type2, nil)
        (cache, exps) = binaryCastConstructor(cache, env, inExp1, inExp2, inType1, inType2, exps, types, info)
        (cache, exps) = binaryUserdefArray(cache, env, exps, bool1 || bool2, inOper, inExp1, inExp2, inType1, inType2, impl, pre, info)
        @match list((daeExp, foldType)) = exps
        (cache, daeExp, foldType, Expression.typeof(daeExp))
      end
    end
  end
  (outCache, outExp, foldType, outType)
end

function binaryUserdefArray(inCache::FCore.Cache, env::FCore.Graph, inExps::List{<:Tuple{<:DAE.Exp, Option{<:DAE.Type}}}, isArray::Bool, inOper::Absyn.Operator, inExp1::DAE.Exp, inExp2::DAE.Exp, inType1::DAE.Type, inType2::DAE.Type, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{Tuple{DAE.Exp, Option{DAE.Type}}}}
  local exps::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local cache::FCore.Cache

  (cache, exps) = begin
    local isRelation::Bool
    local isLogical::Bool
    local isVector1::Bool
    local isVector2::Bool
    local isScalar1::Bool
    local isScalar2::Bool
    local isMatrix1::Bool
    local isMatrix2::Bool
    #=  Already found a match
    =#
    @match (env, inExps, isArray) begin
      (_, _ <|  nil(), _)  => begin
        (inCache, inExps)
      end

      (_,  nil(), true)  => begin
        isRelation = listMember(inOper, list(Absyn.LESS(), Absyn.LESSEQ(), Absyn.GREATER(), Absyn.GREATEREQ(), Absyn.EQUAL(), Absyn.NEQUAL()))
        Error.assertionOrAddSourceMessage(! isRelation, Error.COMPILER_ERROR, list("Not supporting overloading of relation array operations"), info)
        isScalar1 = ! Types.arrayType(inType1)
        isScalar2 = ! Types.arrayType(inType2)
        isVector1 = Types.isArray1D(inType1)
        isVector2 = Types.isArray1D(inType2)
        isMatrix1 = Types.isArray2D(inType1)
        isMatrix2 = Types.isArray2D(inType2)
        (cache, exps) = binaryUserdefArray2(inCache, env, isScalar1, isVector1, isMatrix1, isScalar2, isVector2, isMatrix2, inOper, inExp1, inExp2, inType1, inType2, impl, pre, info)
        (cache, exps)
      end

      _  => begin
        errorMultipleValid(ListUtil.map(inExps, Util.tuple21), info)
        fail()
      end
    end
  end
  (cache, exps)
end

function binaryUserdefArray2(inCache::FCore.Cache, env::FCore.Graph, isScalar1::Bool, isVector1::Bool, isMatrix1::Bool, isScalar2::Bool, isVector2::Bool, isMatrix2::Bool, inOper::Absyn.Operator, inExp1::DAE.Exp, inExp2::DAE.Exp, inType1::DAE.Type, inType2::DAE.Type, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{Tuple{DAE.Exp, Option{DAE.Type}}}}
  local exps::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local cache::FCore.Cache

  (cache, exps) = begin
    local mulExp::DAE.Exp
    local exp::DAE.Exp
    local cr::DAE.Exp
    local cr1::DAE.Exp
    local cr2::DAE.Exp
    local cr3::DAE.Exp
    local cr4::DAE.Exp
    local cr5::DAE.Exp
    local cr6::DAE.Exp
    local foldExp::DAE.Exp
    local transposed::DAE.Exp
    local newType1::DAE.Type
    local newType2::DAE.Type
    local resType::DAE.Type
    local newType1_1::DAE.Type
    local newType2_1::DAE.Type
    local ty::DAE.Type
    local dim1::DAE.Dimension
    local dim2::DAE.Dimension
    local dim1_1::DAE.Dimension
    local dim1_2::DAE.Dimension
    local dim2_1::DAE.Dimension
    local dim2_2::DAE.Dimension
    local iter::DAE.ReductionIterator
    local iter1::DAE.ReductionIterator
    local iter2::DAE.ReductionIterator
    local iter3::DAE.ReductionIterator
    local iter4::DAE.ReductionIterator
    local foldName::String
    local resultName::String
    local foldName1::String
    local resultName1::String
    local foldName2::String
    local resultName2::String
    local foldName3::String
    local resultName3::String
    local foldName4::String
    local resultName4::String
    local iterName::String
    local iterName1::String
    local iterName2::String
    local iterName3::String
    local iterName4::String
    local zeroConstructor::Option{Values.Value}
    local foldType::Option{DAE.Type}
    local zeroTypes::List{DAE.Type}
    local op::Absyn.Operator
    @match (inCache, env, isScalar1, isVector1, isMatrix1, isScalar2, isVector2, isMatrix2, inOper) begin
      (cache, _, false, _, _, true, _, _, _)  => begin
        @match DAE.T_ARRAY(ty = newType1, dims = _cons(dim1, nil)) = inType1
        op = Util.assoc(inOper, list((Absyn.ADD_EW(), Absyn.ADD_EW()), (Absyn.SUB_EW(), Absyn.SUB_EW()), (Absyn.MUL(), Absyn.MUL_EW()), (Absyn.MUL_EW(), Absyn.MUL_EW()), (Absyn.DIV(), Absyn.DIV_EW()), (Absyn.DIV_EW(), Absyn.DIV_EW()), (Absyn.POW_EW(), Absyn.POW_EW())))
        iterName = Util.getTempVariableIndex()
        foldName = Util.getTempVariableIndex()
        resultName = Util.getTempVariableIndex()
        cr = DAE.CREF(DAE.CREF_IDENT(iterName, newType1, nil), newType1)
        (cache, exp, _, resType) = binaryUserdef(cache, env, op, cr, inExp2, newType1, inType2, impl, pre, info)
        resType = Types.liftArray(resType, dim1)
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.COMBINE(), resType, NONE(), foldName, resultName, NONE()), exp, _cons(DAE.REDUCTIONITER(iterName, inExp1, NONE(), newType1), nil))
        (cache, list((exp, NONE())))
      end

      (cache, _, true, _, _, false, _, _, _)  => begin
        op = Util.assoc(inOper, list((Absyn.ADD_EW(), Absyn.ADD_EW()), (Absyn.SUB_EW(), Absyn.SUB_EW()), (Absyn.MUL(), Absyn.MUL_EW()), (Absyn.MUL_EW(), Absyn.MUL_EW()), (Absyn.DIV_EW(), Absyn.DIV_EW()), (Absyn.POW_EW(), Absyn.POW_EW())))
        @match DAE.T_ARRAY(ty = newType2, dims = _cons(dim2, _)) = inType2
        iterName = Util.getTempVariableIndex()
        foldName = Util.getTempVariableIndex()
        resultName = Util.getTempVariableIndex()
        cr = DAE.CREF(DAE.CREF_IDENT(iterName, newType2, nil), newType2)
        (cache, exp, _, resType) = binaryUserdef(cache, env, op, inExp1, cr, inType1, newType2, impl, pre, info)
        resType = DAE.T_ARRAY(resType, list(dim2))
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.COMBINE(), resType, NONE(), foldName, resultName, NONE()), exp, _cons(DAE.REDUCTIONITER(iterName, inExp2, NONE(), newType2), nil))
        (cache, list((exp, NONE())))
      end

      (_, _, _, true, _, _, true, _, Absyn.MUL(__))  => begin
        fail()
      end

      (_, _, _, true, _, _, _, true, Absyn.MUL(__))  => begin
        fail()
      end

      (cache, _, _, _, true, _, true, _, Absyn.MUL(__))  => begin
        @match DAE.T_ARRAY(ty = newType1_1, dims = _cons(dim1_1, nil)) = inType1
        @match DAE.T_ARRAY(ty = newType1, dims = _cons(dim1_2, nil)) = newType1_1
        @match DAE.T_ARRAY(ty = newType2, dims = _cons(dim2, nil)) = inType2
        @match true = Expression.dimensionsEqual(dim1_2, dim2)
        foldName1 = Util.getTempVariableIndex()
        resultName1 = Util.getTempVariableIndex()
        foldName2 = Util.getTempVariableIndex()
        resultName2 = Util.getTempVariableIndex()
        iterName = Util.getTempVariableIndex()
        iterName1 = Util.getTempVariableIndex()
        iterName2 = Util.getTempVariableIndex()
        cr = DAE.CREF(DAE.CREF_IDENT(iterName, newType1_1, nil), newType1)
        cr1 = DAE.CREF(DAE.CREF_IDENT(iterName1, newType1, nil), newType1)
        cr2 = DAE.CREF(DAE.CREF_IDENT(iterName2, newType2, nil), newType2)
        cr3 = DAE.CREF(DAE.CREF_IDENT(foldName1, newType1, nil), newType1)
        cr4 = DAE.CREF(DAE.CREF_IDENT(resultName1, newType2, nil), newType2)
        @match (cache, exp, SOME(ty), resType) = binaryUserdef(cache, env, Absyn.ADD(), cr1, cr2, newType1, newType2, impl, pre, info)
        (cache, foldExp, _, _) = binaryUserdef(cache, env, Absyn.ADD(), cr3, cr4, ty, ty, impl, pre, info)
        (cache, zeroTypes) = getOperatorFuncsOrEmpty(cache, env, list(ty), "'0'", info, nil)
        (cache, zeroConstructor) = getZeroConstructor(cache, env, ListUtil.filterMap(zeroTypes, getZeroConstructorExpression), impl, info)
        resType = DAE.T_ARRAY(resType, list(dim1_1))
        iter = DAE.REDUCTIONITER(iterName1, cr, NONE(), newType1)
        iter1 = DAE.REDUCTIONITER(iterName, inExp1, NONE(), newType1)
        iter2 = DAE.REDUCTIONITER(iterName2, inExp2, NONE(), newType2)
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("sum"), Absyn.THREAD(), resType, zeroConstructor, foldName1, resultName1, SOME(foldExp)), exp, _cons(iter, _cons(iter2, nil)))
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.COMBINE(), resType, NONE(), foldName2, resultName2, NONE()), exp, _cons(iter1, nil))
        (cache, list((exp, NONE())))
      end

      (cache, _, _, _, true, _, _, true, Absyn.MUL(__))  => begin
        @match DAE.T_ARRAY(ty = newType1_1, dims = _cons(dim1_1, nil)) = inType1
        @match DAE.T_ARRAY(ty = newType1, dims = _cons(dim1_2, nil)) = newType1_1
        @match DAE.T_ARRAY(ty = newType2_1, dims = _cons(dim2_1, nil)) = inType2
        @match DAE.T_ARRAY(ty = newType2, dims = _cons(dim2_2, nil)) = newType2_1
        @match true = Expression.dimensionsEqual(dim1_2, dim2_1)
        transposed = Expression.makePureBuiltinCall("transpose", list(inExp2), Types.liftArray(Types.liftArray(newType2, dim2_1), dim2_2))
        iterName1 = Util.getTempVariableIndex()
        iterName2 = Util.getTempVariableIndex()
        iterName3 = Util.getTempVariableIndex()
        iterName4 = Util.getTempVariableIndex()
        foldName1 = Util.getTempVariableIndex()
        resultName1 = Util.getTempVariableIndex()
        foldName2 = Util.getTempVariableIndex()
        resultName2 = Util.getTempVariableIndex()
        foldName = Util.getTempVariableIndex()
        resultName = Util.getTempVariableIndex()
        cr1 = DAE.CREF(DAE.CREF_IDENT(iterName1, newType1_1, nil), newType1_1)
        cr2 = DAE.CREF(DAE.CREF_IDENT(iterName2, newType2_1, nil), newType2_1)
        cr3 = DAE.CREF(DAE.CREF_IDENT(iterName3, newType1, nil), newType1)
        cr4 = DAE.CREF(DAE.CREF_IDENT(iterName4, newType2, nil), newType2)
        (cache, mulExp, _, ty) = binaryUserdef(cache, env, Absyn.MUL(), cr3, cr4, newType1, newType2, impl, pre, info)
        cr5 = DAE.CREF(DAE.CREF_IDENT(foldName, ty, nil), ty)
        cr6 = DAE.CREF(DAE.CREF_IDENT(resultName, ty, nil), ty)
        @match (cache, foldExp, SOME(ty), _) = binaryUserdef(cache, env, Absyn.ADD(), cr5, cr6, ty, ty, impl, pre, info)
        (cache, zeroTypes) = getOperatorFuncsOrEmpty(cache, env, list(ty), "'0'", info, nil)
        (cache, zeroConstructor) = getZeroConstructor(cache, env, ListUtil.filterMap(zeroTypes, getZeroConstructorExpression), impl, info)
        iter1 = DAE.REDUCTIONITER(iterName1, inExp1, NONE(), newType1_1)
        iter2 = DAE.REDUCTIONITER(iterName2, transposed, NONE(), newType2_1)
        iter3 = DAE.REDUCTIONITER(iterName3, cr1, NONE(), newType1_1)
        iter4 = DAE.REDUCTIONITER(iterName4, cr2, NONE(), newType2_1)
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("sum"), Absyn.THREAD(), ty, zeroConstructor, foldName, resultName, SOME(foldExp)), mulExp, _cons(iter3, _cons(iter4, nil)))
        ty = Types.liftArray(ty, dim2_2)
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.COMBINE(), ty, NONE(), foldName2, resultName2, NONE()), exp, _cons(iter2, nil))
        ty = Types.liftArray(ty, dim1_1)
        exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.COMBINE(), ty, NONE(), foldName1, resultName1, NONE()), exp, _cons(iter1, nil))
        (cache, list((exp, NONE())))
      end

(cache, _, false, _, _, false, _, _, _)  => begin
  op = Util.assoc(inOper, list((Absyn.ADD(), Absyn.ADD_EW()), (Absyn.ADD_EW(), Absyn.ADD_EW()), (Absyn.SUB(), Absyn.SUB_EW()), (Absyn.SUB_EW(), Absyn.SUB_EW()), (Absyn.MUL_EW(), Absyn.MUL_EW()), (Absyn.DIV_EW(), Absyn.DIV_EW()), (Absyn.POW_EW(), Absyn.POW_EW()), (Absyn.AND(), Absyn.AND()), (Absyn.OR(), Absyn.OR())))
  @match DAE.T_ARRAY(ty = newType1, dims = _cons(dim1, nil)) = inType1
  @match DAE.T_ARRAY(ty = newType2, dims = _cons(dim2, nil)) = inType2
  @match true = Expression.dimensionsEqual(dim1, dim2)
  foldName = Util.getTempVariableIndex()
  resultName = Util.getTempVariableIndex()
  iterName1 = Util.getTempVariableIndex()
  iterName2 = Util.getTempVariableIndex()
  cr1 = DAE.CREF(DAE.CREF_IDENT(iterName1, newType1, nil), newType1)
  cr2 = DAE.CREF(DAE.CREF_IDENT(iterName2, newType2, nil), newType2)
  (cache, exp, _, resType) = binaryUserdef(cache, env, op, cr1, cr2, newType1, newType2, impl, pre, info)
  resType = DAE.T_ARRAY(resType, list(dim2))
  iter1 = DAE.REDUCTIONITER(iterName1, inExp1, NONE(), newType1)
  iter2 = DAE.REDUCTIONITER(iterName2, inExp2, NONE(), newType2)
  exp = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("array"), Absyn.THREAD(), resType, NONE(), foldName, resultName, NONE()), exp, _cons(iter1, _cons(iter2, nil)))
  (cache, list((exp, NONE())))
end
end
end
#=  non-scalar op scalar
=#
#=  Not all operators are valid operations
=#
#=  exp = ExpressionSimplify.simplify1(exp);
=#
#=  scalar op non-scalar
=#
#=  exp = ExpressionSimplify.simplify1(exp);
=#
#=  '*' invalid operations: vector*vector or vector*matrix
=#
#=  matrix-vector-multiply
=#
#=  true = Types.equivtypes(newType1,newType2);  Else we cannot sum() the expressions - we need to be able to fold them...
=#
#=  print(\"Got mvm (3)\\n\");
=#
#=  array(sum(a*rhs[b] for a in lhs[:,b]) for b in size(rhs,1))
=#
#=  array(sum(a*b for a in c) for c in lhs, b in rhs)
=#
#=  TODO: SUM?
=#
#=  TODO: Check that the expression can be folded? Pass it as input to the function, or pass the chosen function as output, or pass the chosen lhs,rhs types as outputs!
=#
#=  matrix-matrix-multiply
=#
#=  The rest are array op array, which are element-wise operations
=#
#=  We thus change the operator to the element-wise one to avoid other vector operations than this one
=#
#=  array op array, 1-D through n-D
=#
(cache, exps)
end

module OperatorsBinary
using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
  import DAE

#= /* We have these as constants instead of function calls as done previously
* because it takes a long time to generate these types over and over again.
* The types are a bit hard to read, but they are simply 1 through 9-dimensional
* arrays of the basic types. */ =#
const intarrtypes = list(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())))::List
const realarrtypes = list(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())))::List
const boolarrtypes = list(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())))::List
const stringarrtypes = list(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())))::List

const intarrtypes = list(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())), list(DAE.DIM_UNKNOWN())))::List
#= /* Simply a list of 9 of that basic type; used to match with the array types */ =#
const inttypes = list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT)::List
const realtypes = list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT)::List
const stringtypes = list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT)::List

const int_scalar = DAE.T_INTEGER_DEFAULT::DAE.Type
const real_scalar = DAE.T_REAL_DEFAULT::DAE.Type
const bool_scalar = DAE.T_BOOL_DEFAULT::DAE.Type
const int_mul = DAE.MUL(int_scalar)::DAE.Operator
const real_mul = DAE.MUL(real_scalar)::DAE.Operator
const real_div = DAE.DIV(real_scalar)::DAE.Operator
const real_pow = DAE.POW(real_scalar)::DAE.Operator
const int_mul_sp = DAE.MUL_SCALAR_PRODUCT(int_scalar)::DAE.Operator
const real_mul_sp = DAE.MUL_SCALAR_PRODUCT(real_scalar)::DAE.Operator
const int_mul_mp = DAE.MUL_MATRIX_PRODUCT(DAE.T_INTEGER_DEFAULT)::DAE.Operator
const real_mul_mp = DAE.MUL_MATRIX_PRODUCT(DAE.T_REAL_DEFAULT)::DAE.Operator
const int_vector = DAE.T_ARRAY(int_scalar, list(DAE.DIM_UNKNOWN()))::DAE.Type
const int_matrix = DAE.T_ARRAY(int_vector, list(DAE.DIM_UNKNOWN()))::DAE.Type
const real_vector = DAE.T_ARRAY(real_scalar, list(DAE.DIM_UNKNOWN()))::DAE.Type
const real_matrix = DAE.T_ARRAY(real_vector, list(DAE.DIM_UNKNOWN()))::DAE.Type
const addIntArrays = list((DAE.ADD_ARR(int_vector), list(at, at), at) for at in intarrtypes)::List
const addRealArrays = list((DAE.ADD_ARR(real_vector), list(at, at), at) for at in realarrtypes)::List
const addStringArrays = list((DAE.ADD_ARR(DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_UNKNOWN()))), list(at, at), at) for at in stringarrtypes)::List
const addScalars = list((DAE.ADD(int_scalar), list(int_scalar, int_scalar), int_scalar), (DAE.ADD(real_scalar), list(real_scalar, real_scalar), real_scalar), (DAE.ADD(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_STRING_DEFAULT))::List
# TODO! FIXME! uncomment these below and fix the conversion!
const addTypes = _listAppend(addScalars, _listAppend(addIntArrays, _listAppend(addRealArrays, addStringArrays)))::List
const addIntArrayScalars = list(@do_threaded_for (DAE.ADD_ARRAY_SCALAR(int_vector), list(at, rhs), at) (at, rhs) (intarrtypes, inttypes))::List
const addRealArrayScalars = list(@do_threaded_for (DAE.ADD_ARRAY_SCALAR(real_vector), list(at, rhs), at) (at, rhs) (realarrtypes, realtypes))::List
const addStringArrayScalars = nil::List
const addEwTypes = _listAppend(addIntArrayScalars, _listAppend(addRealArrayScalars, _listAppend(addStringArrayScalars, addTypes)))::List
const subIntArrays = list((DAE.SUB_ARR(int_vector), list(at, at), at) for at in intarrtypes)::List
const subRealArrays = list((DAE.SUB_ARR(real_vector), list(at, at), at) for at in realarrtypes)::List
const subScalars = list((DAE.SUB(int_scalar), list(int_scalar, int_scalar), int_scalar), (DAE.SUB(real_scalar), list(real_scalar, real_scalar), real_scalar))::List
const subTypes = _listAppend(subScalars, _listAppend(subIntArrays, subRealArrays))::List
const subIntArrayScalars = list(@do_threaded_for (DAE.SUB_SCALAR_ARRAY(int_vector), list(lhs, at), at) (at, lhs) (intarrtypes, inttypes))::List
const subRealArrayScalars = list(@do_threaded_for (DAE.SUB_SCALAR_ARRAY(real_vector), list(lhs, at), at) (at, lhs) (realarrtypes, realtypes))::List
const subEwTypes = _listAppend(subScalars, _listAppend(subIntArrayScalars, _listAppend(subRealArrayScalars, _listAppend(subIntArrays, subRealArrays))))::List
const mulScalars = list((int_mul, list(int_scalar, int_scalar), int_scalar), (real_mul, list(real_scalar, real_scalar), real_scalar))::List
const mulScalarProduct = list((int_mul_sp, list(int_vector, int_vector), int_scalar), (real_mul_sp, list(real_vector, real_vector), real_scalar))::List
const mulMatrixProduct = list((int_mul_mp, list(int_vector, int_matrix), int_vector), (int_mul_mp, list(int_matrix, int_vector), int_vector), (int_mul_mp, list(int_matrix, int_matrix), int_matrix), (real_mul_mp, list(real_vector, real_matrix), real_vector), (real_mul_mp, list(real_matrix, real_vector), real_vector), (real_mul_mp, list(real_matrix, real_matrix), real_matrix))::List
const mulIntArrayScalars = list(@do_threaded_for (DAE.MUL_ARRAY_SCALAR(int_vector), list(at, rhs), at) (at, rhs) (intarrtypes, inttypes))::List
const mulRealArrayScalars = list(@do_threaded_for (DAE.MUL_ARRAY_SCALAR(real_vector), list(at, rhs), at) (at, rhs) (realarrtypes, realtypes))::List
const mulTypes = _listAppend(mulScalars, _listAppend(mulIntArrayScalars, _listAppend(mulRealArrayScalars, _listAppend(mulScalarProduct, mulMatrixProduct))))::List
const mulIntArray = list((DAE.MUL_ARR(int_vector), list(at, at), at) for at in intarrtypes)::List
const mulRealArray = list((DAE.MUL_ARR(real_vector), list(at, at), at) for at in realarrtypes)::List
const mulEwTypes = _listAppend(mulScalars, _listAppend(mulIntArrayScalars, _listAppend(mulRealArrayScalars, _listAppend(mulIntArray, mulRealArray))))::List
const divTypes = _cons((real_div, list(real_scalar, real_scalar), real_scalar), list(@do_threaded_for (DAE.DIV_ARRAY_SCALAR(real_vector), list(at, rhs), at) (at, rhs) (realarrtypes, realtypes)))::List
const divRealScalarArray = list(@do_threaded_for (DAE.DIV_SCALAR_ARRAY(real_vector), list(lhs, at), at) (at, lhs) (realarrtypes, realtypes))::List
const divArrs = list((DAE.DIV_ARR(real_vector), list(at, at), at) for at in realarrtypes)::List
const divEwTypes = _listAppend(divTypes, _listAppend(divRealScalarArray, divArrs))::List
const powTypes = list((real_pow, list(real_scalar, real_scalar), real_scalar), (DAE.POW_ARR(real_scalar), list(real_matrix, int_scalar), real_matrix))::List
#TODO fix andTypes and orTypes
const andTypes = #_cons((DAE.AND(bool_scalar), list(bool_scalar, bool_scalar), bool_scalar), list(@do_threaded_for (DAE.AND(bool_scalar), list(at, at), at), at, boolarrtypes))::List
const orTypes = #_cons((DAE.OR(bool_scalar), list(bool_scalar, bool_scalar), bool_scalar), list(@do_threaded_for(DAE.OR(bool_scalar), list(at, at), at), at, (boolarrtypes)))::List
#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

#= This function relates the operators in the abstract syntax to the
de-overloaded operators in the SCode. It produces a list of available
types for a specific operator, that the overload function chooses from.
Therefore, in order for the builtin type conversion from Integer to
Real to work, operators that work on both Integers and Reals must
return the Integer type -before- the Real type in the list. =#
function operatorsBinary(inOperator::Absyn.Operator, t1::DAE.Type, e1::DAE.Exp, t2::DAE.Type, e2::DAE.Exp) ::Tuple{List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}, DAE.Type, DAE.Exp, DAE.Type, DAE.Exp}
  local oe2::DAE.Exp = e2
  local oty2::DAE.Type = t2
  local oe1::DAE.Exp = e1
  local oty1::DAE.Type = t1
  local ops::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
  local t::DAE.Type
  local e::DAE.Exp
  local op::Absyn.Operator = inOperator
  local ia1::Bool = Types.isArray(t1)
  local ia2::Bool = Types.isArray(t2)
  if ia2 && ! ia1
    (e1, e2, t1, t2) = begin
      @match op begin
        Absyn.ADD_EW(__)  => begin
          (e2, e1, t2, t1)
        end

        Absyn.MUL(__)  => begin
          (e2, e1, t2, t1)
        end

        Absyn.MUL_EW(__)  => begin
          (e2, e1, t2, t1)
        end

        _  => begin
          (e1, e2, t1, t2)
        end
      end
    end
  elseif ia1 && ! ia2
    (op, e2) = begin
      @match op begin
        Absyn.SUB_EW(__)  => begin
          (Absyn.ADD_EW(), Expression.negate(e2))
        end

        _  => begin
          (op, e2)
        end
      end
    end
  end

  try
    ops = begin
      local intarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local realarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local boolarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local stringarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local scalars::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local arrays::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local types::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local scalarprod::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local matrixprod::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local intscalararrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local realscalararrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local intarrsscalar::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local realarrsscalar::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local realarrscalar::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local arrscalar::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local stringarrsscalar::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
      local enum_op::Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}
      local int_scalar::DAE.Type
      local int_vector::DAE.Type
      local int_matrix::DAE.Type
      local real_scalar::DAE.Type
      local real_vector::DAE.Type
      local real_matrix::DAE.Type
      local int_mul::DAE.Operator
      local real_mul::DAE.Operator
      local int_mul_sp::DAE.Operator
      local real_mul_sp::DAE.Operator
      local int_mul_mp::DAE.Operator
      local real_mul_mp::DAE.Operator
      local real_div::DAE.Operator
      local real_pow::DAE.Operator
      @match op begin
        Absyn.ADD(__)  => begin
          OperatorsBinary.addTypes
        end

        Absyn.ADD_EW(__)  => begin
          OperatorsBinary.addEwTypes
        end

        Absyn.SUB(__)  => begin
          OperatorsBinary.subTypes
        end

        Absyn.SUB_EW(__)  => begin
          OperatorsBinary.subEwTypes
        end

        Absyn.MUL(__)  => begin
          println("MUL!")
          ops = OperatorsBinary.mulTypes
          ops
        end

        Absyn.MUL_EW(__)  => begin
          OperatorsBinary.mulEwTypes
        end

        Absyn.DIV(__)  => begin
          OperatorsBinary.divTypes
        end

        Absyn.DIV_EW(__)  => begin
          OperatorsBinary.divEwTypes
        end

        Absyn.POW(__)  => begin
          OperatorsBinary.powTypes
        end

        Absyn.POW_EW(__)  => begin
          realarrs = operatorReturn(DAE.POW_ARR2(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN()))), realarrtypes, realarrtypes, realarrtypes)
          scalars = list((DAE.POW(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_REAL_DEFAULT))
          realscalararrs = operatorReturn(DAE.POW_SCALAR_ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN()))), realtypes, realarrtypes, realarrtypes)
          realarrsscalar = operatorReturn(DAE.POW_ARRAY_SCALAR(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN()))), realarrtypes, realtypes, realarrtypes)
          types = ListUtil.flatten(list(scalars, realscalararrs, realarrsscalar, realarrs))
          types
        end

        Absyn.AND(__)  => begin
          OperatorsBinary.andTypes
        end

        Absyn.OR(__)  => begin
          OperatorsBinary.orTypes
        end

        Absyn.LESS(__)  => begin
          enum_op = makeEnumOperator(DAE.LESS(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          scalars = list((DAE.LESS(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), enum_op, (DAE.LESS(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.LESS(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.LESS(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT))
          types = ListUtil.flatten(list(scalars))
          types
        end

        Absyn.LESSEQ(__)  => begin
          enum_op = makeEnumOperator(DAE.LESSEQ(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          scalars = list((DAE.LESSEQ(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), enum_op, (DAE.LESSEQ(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.LESSEQ(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.LESSEQ(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT))
          types = ListUtil.flatten(list(scalars))
          types
        end

        Absyn.GREATER(__)  => begin
          enum_op = makeEnumOperator(DAE.GREATER(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          scalars = list((DAE.GREATER(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), enum_op, (DAE.GREATER(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.GREATER(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.GREATER(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT))
          types = ListUtil.flatten(list(scalars))
          types
        end

        Absyn.GREATEREQ(__)  => begin
          enum_op = makeEnumOperator(DAE.GREATEREQ(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          scalars = list((DAE.GREATEREQ(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), enum_op, (DAE.GREATEREQ(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.GREATEREQ(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), (DAE.GREATEREQ(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT))
          types = ListUtil.flatten(list(scalars))
          types
        end

        Absyn.EQUAL(__)  => begin
          enum_op = makeEnumOperator(DAE.EQUAL(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          types = _cons((DAE.EQUAL(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), _cons(enum_op, _cons((DAE.EQUAL(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), _cons((DAE.EQUAL(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT), _cons((DAE.EQUAL(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), nil)))))
          types
        end

        Absyn.NEQUAL(__)  => begin
          enum_op = makeEnumOperator(DAE.NEQUAL(DAE.T_ENUMERATION_DEFAULT), t1, t2)
          types = _cons((DAE.NEQUAL(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT, DAE.T_INTEGER_DEFAULT), DAE.T_BOOL_DEFAULT), _cons(enum_op, _cons((DAE.NEQUAL(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), DAE.T_BOOL_DEFAULT), _cons((DAE.NEQUAL(DAE.T_STRING_DEFAULT), list(DAE.T_STRING_DEFAULT, DAE.T_STRING_DEFAULT), DAE.T_BOOL_DEFAULT), _cons((DAE.NEQUAL(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), nil)))))
          types
        end
end
end
catch
@match true = Flags.isSet(Flags.FAILTRACE)
Debug.traceln("OperatorOverloading.operatorsBinary failed, op: " + Dump.opSymbol(op))
fail()
end
#=  Relational operators
=#
(ops, oty1, oe1, oty2, oe2)
end

#= This function relates the operators in the abstract syntax to the
de-overloaded operators in the SCode. It produces a list of available
types for a specific operator, that the overload function chooses from.
Therefore, in order for the builtin type conversion from Integer to
Real to work, operators that work on both Integers and Reals must
return the Integer type -before- the Real type in the list. =#
function operatorsUnary(op::Absyn.Operator) ::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
  local ops::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}

  ops = begin
    local intarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local realarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local boolarrs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local scalars::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local types::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    @match op begin
      Absyn.UMINUS(__)  => begin
        scalars = list((DAE.UMINUS(DAE.T_INTEGER_DEFAULT), list(DAE.T_INTEGER_DEFAULT), DAE.T_INTEGER_DEFAULT), (DAE.UMINUS(DAE.T_REAL_DEFAULT), list(DAE.T_REAL_DEFAULT), DAE.T_REAL_DEFAULT)) #= The UMINUS operator, unary minus =#
        intarrs = operatorReturnUnary(DAE.UMINUS_ARR(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN()))), intarrtypes, intarrtypes)
        realarrs = operatorReturnUnary(DAE.UMINUS_ARR(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN()))), realarrtypes, realarrtypes)
        types = ListUtil.flatten(list(scalars, intarrs, realarrs))
        types
      end

      Absyn.NOT(__)  => begin
        scalars = list((DAE.NOT(DAE.T_BOOL_DEFAULT), list(DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT))
        boolarrs = operatorReturnUnary(DAE.NOT(DAE.T_BOOL_DEFAULT), boolarrtypes, boolarrtypes)
        types = ListUtil.flatten(list(scalars, boolarrs))
        types
      end

      _  => begin
        @match true = Flags.isSet(Flags.FAILTRACE)
        Debug.traceln("OperatorOverloading.operatorsUnary failed, op: " + Dump.opSymbol(op))
        fail()
      end
    end
  end
  ops
end

#= Used by operators to create an operator with enumeration type. It sets the
correct expected type of the operator, so that for example integer=>enum type
casts work correctly without matching things that it shouldn't match. =#
function makeEnumOperator(inOp::DAE.Operator, inType1::DAE.Type, inType2::DAE.Type) ::Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}
  local outOp::Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}

  outOp = begin
    local op_ty::DAE.Type
    local op::DAE.Operator
    @matchcontinue (inType1, inType2) begin
      (DAE.T_ENUMERATION(__), DAE.T_ENUMERATION(__))  => begin
        op_ty = Types.simplifyType(inType1)
        op = Expression.setOpType(inOp, op_ty)
        (op, list(inType1, inType2), DAE.T_BOOL_DEFAULT)
      end

      (DAE.T_ENUMERATION(__), _)  => begin
        op_ty = Types.simplifyType(inType1)
        op = Expression.setOpType(inOp, op_ty)
        (op, list(inType1, inType1), DAE.T_BOOL_DEFAULT)
      end

      (_, DAE.T_ENUMERATION(__))  => begin
        op_ty = Types.simplifyType(inType2)
        op = Expression.setOpType(inOp, op_ty)
        (op, list(inType2, inType2), DAE.T_BOOL_DEFAULT)
      end

      _  => begin
        (inOp, list(DAE.T_ENUMERATION_DEFAULT, DAE.T_ENUMERATION_DEFAULT), DAE.T_BOOL_DEFAULT)
      end
    end
  end
  outOp
end

#= This function takes the types operator overloaded user functions and
builds  the type list structure suitable for the deoverload function. =#
function buildOperatorTypes(inTypes::List{<:DAE.Type}, inPath::Absyn.Path) ::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
  local outOperatorTypes::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}

  outOperatorTypes = begin
    local argtypes::List{DAE.Type}
    local tps::List{DAE.Type}
    local rest::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local args::List{DAE.FuncArg}
    local tp::DAE.Type
    local funcname::Absyn.Path
    @match (inTypes, inPath) begin
      ( nil(), _)  => begin
        nil
      end

      (DAE.T_FUNCTION(funcArg = args, funcResultType = tp) <| tps, funcname)  => begin
        argtypes = ListUtil.map(args, Types.funcArgType)
        rest = buildOperatorTypes(tps, funcname)
        _cons((DAE.USERDEFINED(funcname), argtypes, tp), rest)
      end
    end
  end
  outOperatorTypes
end

#= This function collects the types and operator lists into a tuple list, suitable
for the deoverloading function for binary operations. =#
function operatorReturn(inOperator::DAE.Operator, inLhsTypes::List{<:DAE.Type}, inRhsTypes::List{<:DAE.Type}, inReturnTypes::List{<:DAE.Type}) ::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
  local outOperators::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}

  outOperators = list(@do_threaded_for (inOperator, list(l, r), re) (l, r, re) (inLhsTypes, inRhsTypes, inReturnTypes))
  outOperators
end

#= This function collects the types and operator lists into a tuple list,
suitable for the deoverloading function to be used for unary
expressions. =#
function operatorReturnUnary(inOperator::DAE.Operator, inArgTypes::List{<:DAE.Type}, inReturnTypes::List{<:DAE.Type}) ::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
  local outOperators::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}

  outOperators = begin
    local rest::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local t::Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}
    local op::DAE.Operator
    local l::DAE.Type
    local re::DAE.Type
    local lr::List{DAE.Type}
    local rer::List{DAE.Type}
    @match (inOperator, inArgTypes, inReturnTypes) begin
      (_,  nil(),  nil())  => begin
        nil
      end

      (op, l <| lr, re <| rer)  => begin
        rest = operatorReturnUnary(op, lr, rer)
        t = (op, list(l), re) #= list only contains one type, i.e. for UNARY operations =#
        _cons(t, rest)
      end
    end
  end
  outOperators
end

function getOperatorFuncsOrEmpty(inCache::FCore.Cache, env::FCore.Graph, tys::List{<:DAE.Type}, opName::String, info::SourceInfo, acc::List{<:DAE.Type}) ::Tuple{FCore.Cache, List{DAE.Type}}
  local funcs::List{DAE.Type}
  local cache::FCore.Cache

  (cache, funcs) = begin
    local path::Absyn.Path
    local opNamePath::Absyn.Path
    local operatorCl::SCode.Element
    local recordEnv::FCore.Graph
    local operEnv::FCore.Graph
    local paths::List{Absyn.Path}
    local ty::DAE.Type
    local scalarType::DAE.Type
    local rest::List{DAE.Type}
    @matchcontinue (inCache, env, tys, opName, info, acc) begin
      (_, _, ty <| rest, _, _, _)  => begin
        (cache, funcs) = getOperatorFuncsOrEmptySingleTy(inCache, env, ty, opName, info)
        (cache, funcs) = getOperatorFuncsOrEmpty(cache, env, rest, opName, info, _listAppend(funcs, acc))
        (cache, funcs)
      end

      (_, _, _ <| rest, _, _, _)  => begin
        (cache, funcs) = getOperatorFuncsOrEmpty(inCache, env, rest, opName, info, acc)
        (cache, funcs)
      end

      (_, _,  nil(), _, _, _)  => begin
        @match (cache, Util.SUCCESS()) = Static.instantiateDaeFunctionFromTypes(inCache, env, acc, false, NONE(), true, Util.SUCCESS())
        @match (DAE.T_TUPLE(funcs, _), _) = Types.traverseType(DAE.T_TUPLE(acc, NONE()), -1, Types.makeExpDimensionsUnknown)
        (cache, funcs)
      end
    end
  end
  (cache, funcs)
end

function getOperatorFuncsOrEmptySingleTy(cache::FCore.Cache, env::FCore.Graph, ty::DAE.Type, opName::String, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Type}}
  local funcs::List{DAE.Type}
  local path::Absyn.Path
  local pathIn::Absyn.Path
  local opNamePath::Absyn.Path
  local operatorCl::SCode.Element
  local recordEnv::FCore.Graph
  local operEnv::FCore.Graph
  local paths::List{Absyn.Path}
  local scalarType::DAE.Type
  local tree1::AvlTreePathPathEnv.Tree
  local tree2::AvlTreePathOperatorTypes.Tree
  local trees::Tuple{AvlTreePathPathEnv.Tree, AvlTreePathOperatorTypes.Tree}

  scalarType = Types.arrayElementType(ty)
  pathIn = AbsynUtil.makeFullyQualified(getRecordPath(scalarType))
  trees = getGlobalRoot(Global.operatorOverloadingCache)
  (tree1, tree2) = trees
  try
    path = AvlTreePathPathEnv.get(tree1, pathIn)
  catch
    (cache, operatorCl, recordEnv) = Lookup.lookupClass(cache, env, pathIn)
    (cache, path, recordEnv) = lookupOperatorBaseClass(cache, recordEnv, operatorCl)
    tree1 = AvlTreePathPathEnv.add(tree1, pathIn, path)
    setGlobalRoot(Global.operatorOverloadingCache, (tree1, tree2))
  end
  opNamePath = Absyn.IDENT(opName)
  path = AbsynUtil.makeFullyQualified(AbsynUtil.joinPaths(path, opNamePath))
  try
    funcs = AvlTreePathOperatorTypes.get(tree2, path)
  catch
    (cache, operatorCl, operEnv) = Lookup.lookupClass(cache, env, path)
    @match true = SCodeUtil.isOperator(operatorCl)
    paths = AbsynToSCode.getListofQualOperatorFuncsfromOperator(operatorCl)
    (cache, funcs) = Lookup.lookupFunctionsListInEnv(cache, operEnv, paths, info, nil)
    funcs = ListUtil.select2(funcs, if opName == "'constructor'" || opName == "'0'"
                             checkOperatorFunctionOutput
                             else
                             checkOperatorFunctionOneOutput
                             end, scalarType, info)
    tree2 = AvlTreePathOperatorTypes.add(tree2, path, funcs)
    setGlobalRoot(Global.operatorOverloadingCache, (tree1, tree2))
  end
  #=  check if the operator is defined. i.e overloaded
  =#
  #=  get the list of functions in the operator. !! there can be multiple options
  =#
  (cache, funcs)
end

#= From a derived class, we find the parent.
This is required because we take the union of functions from lhs and rhs.
If one is Complex and one is named ComplexVoltage, we would get different types.
This also reduces the total number of functions that are instantiated.
=#
function lookupOperatorBaseClass(inCache::FCore.Cache, inEnv::FCore.Graph, inClass::SCode.Element) ::Tuple{FCore.Cache, Absyn.Path, FCore.Graph}
  local env::FCore.Graph
  local path::Absyn.Path
  local cache::FCore.Cache

  (cache, path, env) = begin
    local cl::SCode.Element
    local name::String
    @match (inCache, inEnv, inClass) begin
      (cache, env, SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path, NONE()))))  => begin
        (cache, cl, env) = Lookup.lookupClass(cache, env, path)
        (cache, path, env) = lookupOperatorBaseClass(cache, env, cl)
        (cache, path, env)
      end

      (cache, env, SCode.CLASS(name = name))  => begin
        path = FGraph.joinScopePath(env, Absyn.IDENT(name))
        (cache, path, env)
      end
    end
  end
  (cache, path, env)
end

function checkOperatorFunctionOneOutput(ty::DAE.Type, opType::DAE.Type, info::SourceInfo) ::Bool
  local isOK::Bool

  isOK = begin
    local ty1::DAE.Type
    local ty2::DAE.Type
    local p::Absyn.Path
    local b::Bool
    @match (ty, opType, info) begin
      (DAE.T_FUNCTION(funcResultType = DAE.T_TUPLE(__)), _, _)  => begin
        false
      end

      (DAE.T_FUNCTION(funcArg = DAE.FUNCARG(ty = ty1, defaultBinding = NONE()) <| DAE.FUNCARG(ty = ty2, defaultBinding = NONE()) <| _), _, _)  => begin
        b = Types.equivtypesOrRecordSubtypeOf(Types.arrayElementType(ty1), opType) || Types.equivtypesOrRecordSubtypeOf(Types.arrayElementType(ty2), opType)
        checkOperatorFunctionOneOutputError(b, opType, ty, info)
        b
      end

      (DAE.T_FUNCTION(funcArg = DAE.FUNCARG(ty = ty1, defaultBinding = NONE()) <| _), _, _)  => begin
        b = Types.equivtypesOrRecordSubtypeOf(Types.arrayElementType(ty1), opType)
        checkOperatorFunctionOneOutputError(b, opType, ty, info)
        b
      end

      _  => begin
        true
      end
    end
  end
  isOK
end

function checkOperatorFunctionOneOutputError(ok::Bool, opType::DAE.Type, ty::DAE.Type, info::SourceInfo)
  _ = begin
    local str1::String
    local str2::String
    @match (ok, opType, ty, info) begin
      (true, _, _, _)  => begin
        ()
      end

      _  => begin
        str1 = Types.unparseType(opType)
        str2 = Types.unparseType(ty)
        Error.addSourceMessage(Error.OP_OVERLOAD_OPERATOR_NOT_INPUT, list(str1, str2), info)
        fail()
      end
    end
  end
end

function checkOperatorFunctionOutput(ty::DAE.Type, expected::DAE.Type, info::SourceInfo) ::Bool
  local isOK::Bool

  isOK = begin
    local actual::DAE.Type
    @match (ty, expected, info) begin
      (DAE.T_FUNCTION(funcResultType = actual), _, _)  => begin
        isOK = Types.equivtypesOrRecordSubtypeOf(actual, expected)
        isOK
      end

      _  => begin
        false
      end
    end
  end
  isOK
end

function isOperatorBinaryFunctionOrWarn(ty::DAE.Type, info::SourceInfo) ::Bool
  local isBinaryFunc::Bool

  isBinaryFunc = begin
    local rest::List{DAE.FuncArg}
    @match (ty, info) begin
      (DAE.T_FUNCTION(funcArg = _ <|  nil()), _)  => begin
        false
      end

      (DAE.T_FUNCTION(funcArg = DAE.FUNCARG(defaultBinding = NONE()) <| DAE.FUNCARG(defaultBinding = NONE()) <| rest), _)  => begin
        isBinaryFunc = ListUtil.mapMapBoolAnd(rest, Types.funcArgDefaultBinding, isSome)
        isBinaryFunc
      end

      _  => begin
        false
      end
    end
  end
  isBinaryFunc
end

function isOperatorUnaryFunction(ty::DAE.Type) ::Bool
  local isBinaryFunc::Bool

  isBinaryFunc = begin
    local rest::List{DAE.FuncArg}
    @match ty begin
      DAE.T_FUNCTION(funcArg = DAE.FUNCARG(defaultBinding = NONE()) <| rest)  => begin
        isBinaryFunc = ListUtil.mapMapBoolAnd(rest, Types.funcArgDefaultBinding, isSome)
        isBinaryFunc
      end

      _  => begin
        false
      end
    end
  end
  isBinaryFunc
end

function getZeroConstructorExpression(ty::DAE.Type) ::DAE.Exp
  local result::DAE.Exp

  result = begin
    local args::List{DAE.FuncArg}
    local path::Absyn.Path
    local attr::DAE.FunctionAttributes
    @match ty begin
      DAE.T_FUNCTION(funcArg = args, functionAttributes = attr, path = path)  => begin
        result = makeCallFillRestDefaults(path, nil, args, Types.makeCallAttr(ty, attr))
        result
      end
    end
  end
  result
end

function makeCallFillRestDefaults(path::Absyn.Path, inExps::List{<:DAE.Exp}, restArgs::List{<:DAE.FuncArg}, attr::DAE.CallAttributes) ::DAE.Exp
  local exp::DAE.Exp

  local exps::List{DAE.Exp}

  exps = _listAppend(inExps, ListUtil.mapMap(restArgs, Types.funcArgDefaultBinding, Util.getOption))
  exp = DAE.CALL(path, exps, attr)
  exp
end

function getRecordPath(inType1::DAE.Type) ::Absyn.Path
  local outPath::Absyn.Path

  @match DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(outPath)) = Types.arrayElementType(inType1)
  outPath
end

#= Given several lists of parameter types and one argument list,
this function tries to find one list of parameter types which
is compatible with the argument list. It uses elabArglist to
do the matching, which means that automatic type conversions
will be made when necessary.  The new argument list, together
with a new operator that corresponds to the parameter type list
is returned.

The basic principle is that the first operator that matches is chosen.
. =#
function deoverload(inOperators::List{<:Tuple{<:DAE.Operator, List{<:DAE.Type}, DAE.Type}}, inArgs::List{<:Tuple{<:DAE.Exp, DAE.Type}}, aexp::Absyn.Exp #= for error-messages =#, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{DAE.Operator, List{DAE.Exp}, DAE.Type}
  local outType::DAE.Type
  local outArgs::List{DAE.Exp}
  local outOperator::DAE.Operator

  (outOperator, outArgs, outType) = begin
    local exps::List{DAE.Exp}
    local args_1::List{DAE.Exp}
    local types_1::List{DAE.Type}
    local params::List{DAE.Type}
    local tps::List{DAE.Type}
    local rtype_1::DAE.Type
    local rtype::DAE.Type
    local op::DAE.Operator
    local args::List{Tuple{DAE.Exp, DAE.Type}}
    local xs::List{Tuple{DAE.Operator, List{DAE.Type}, DAE.Type}}
    local pre::Prefix.PrefixType
    local ty::DAE.Type
    local exps_str::List{String}
    local tps_str::List{String}
    local estr::String
    local pre_str::String
    local s::String
    local tpsstr::String
    @matchcontinue (inOperators, inArgs, aexp, inPrefix, info) begin
      ((op, params, rtype) <| _, args, _, pre, _)  => begin
        (args_1, types_1) = elabArglist(params, args)
        rtype_1 = computeReturnType(op, types_1, rtype, pre, info)
        ty = Types.simplifyType(rtype_1)
        op = Expression.setOpType(op, ty)
        (op, args_1, rtype_1)
      end

      (_ <| xs, args, _, pre, _)  => begin
        (op, args_1, rtype) = deoverload(xs, args, aexp, pre, info)
        (op, args_1, rtype)
      end

      ( nil(), args, _, pre, _)  => begin
        s = Dump.printExpStr(aexp)
        exps = ListUtil.map(args, Util.tuple21)
        tps = ListUtil.map(args, Util.tuple22)
        exps_str = ListUtil.map(exps, ExpressionDump.printExpStr)
        _ = stringDelimitList(exps_str, ", ")
        tps_str = ListUtil.map(tps, Types.unparseType)
        tpsstr = stringDelimitList(tps_str, ", ")
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.UNRESOLVABLE_TYPE, list(s, tpsstr, pre_str), info)
        fail()
      end
    end
  end
  (outOperator, outArgs, outType)
end

#= This function determines the return type of
an operator and the types of the operands. =#
function computeReturnType(inOperator::DAE.Operator, inTypesTypeLst::List{<:DAE.Type}, inType::DAE.Type, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::DAE.Type
  local outType::DAE.Type

  outType = begin
    local typ1::DAE.Type
    local typ2::DAE.Type
    local rtype::DAE.Type
    local etype::DAE.Type
    local typ::DAE.Type
    local t1_str::String
    local t2_str::String
    local pre_str::String
    local n1::DAE.Dimension
    local n2::DAE.Dimension
    local m::DAE.Dimension
    local n::DAE.Dimension
    local m1::DAE.Dimension
    local m2::DAE.Dimension
    local p::DAE.Dimension
    local pre::Prefix.PrefixType
    @matchcontinue (inOperator, inTypesTypeLst, inType, inPrefix, inInfo) begin
      (DAE.ADD_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        typ1
      end

      (DAE.ADD_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        typ1
      end

      (DAE.ADD_ARR(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("vector addition", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.SUB_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        typ1
      end

      (DAE.SUB_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        typ1
      end

      (DAE.SUB_ARR(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("vector subtraction", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.MUL_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        typ1
      end

      (DAE.MUL_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        typ1
      end

      (DAE.MUL_ARR(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("vector elementwise multiplication", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.DIV_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        typ1
      end

      (DAE.DIV_ARR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        typ1
      end

      (DAE.DIV_ARR(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("vector elementwise division", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.POW_ARR(__), typ1 <| _ <|  nil(), _, _, _)  => begin
        @match 2 = nDims(typ1)
        n = Types.getDimensionNth(typ1, 1)
        m = Types.getDimensionNth(typ1, 2)
        @match true = Expression.dimensionsKnownAndEqual(n, m)
        typ1
      end

      (DAE.POW_ARR2(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        typ1
      end

      (DAE.POW_ARR2(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        typ1
      end

      (DAE.POW_ARR2(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("elementwise vector^vector", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.MUL_SCALAR_PRODUCT(__), typ1 <| typ2 <|  nil(), rtype, _, _)  => begin
        @match true = Types.subtype(typ1, typ2)
        rtype
      end

      (DAE.MUL_SCALAR_PRODUCT(__), typ1 <| typ2 <|  nil(), rtype, _, _)  => begin
        @match true = Types.subtype(typ2, typ1)
        rtype
      end

      (DAE.MUL_SCALAR_PRODUCT(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
        t1_str = Types.unparseType(typ1)
        t2_str = Types.unparseType(typ2)
        pre_str = PrefixUtil.printPrefixStr3(pre)
        Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("scalar product", pre_str, t1_str, t2_str), inInfo)
        fail()
      end

      (DAE.MUL_MATRIX_PRODUCT(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match 1 = nDims(typ1)
        @match 2 = nDims(typ2)
        n1 = Types.getDimensionNth(typ1, 1)
        n2 = Types.getDimensionNth(typ2, 1)
        m = Types.getDimensionNth(typ2, 2)
        @match true = isValidMatrixProductDims(n1, n2)
        etype = elementType(typ1)
        rtype = Types.liftArray(etype, m)
        rtype
      end

      (DAE.MUL_MATRIX_PRODUCT(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match 2 = nDims(typ1)
        @match 1 = nDims(typ2)
        n = Types.getDimensionNth(typ1, 1)
        m1 = Types.getDimensionNth(typ1, 2)
        m2 = Types.getDimensionNth(typ2, 1)
        @match true = isValidMatrixProductDims(m1, m2)
        etype = elementType(typ2)
        rtype = Types.liftArray(etype, n)
        rtype
      end

      (DAE.MUL_MATRIX_PRODUCT(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
        @match 2 = nDims(typ1)
        @match 2 = nDims(typ2)
        n = Types.getDimensionNth(typ1, 1)
        m1 = Types.getDimensionNth(typ1, 2)
        m2 = Types.getDimensionNth(typ2, 1)
        p = Types.getDimensionNth(typ2, 2)
        @match true = isValidMatrixProductDims(m1, m2)
        etype = elementType(typ1)
        rtype = Types.liftArrayListDims(etype, list(n, p))
        rtype
      end

(DAE.MUL_MATRIX_PRODUCT(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
  t1_str = Types.unparseType(typ1)
  t2_str = Types.unparseType(typ2)
  pre_str = PrefixUtil.printPrefixStr3(pre)
  Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("matrix multiplication", pre_str, t1_str, t2_str), inInfo)
  fail()
end

(DAE.MUL_ARRAY_SCALAR(__), typ1 <| _ <|  nil(), _, _, _)  => begin
  typ1
end

(DAE.ADD_ARRAY_SCALAR(__), typ1 <| _ <|  nil(), _, _, _)  => begin
  typ1
end

(DAE.SUB_SCALAR_ARRAY(__), _ <| typ2 <|  nil(), _, _, _)  => begin
  typ2
end

(DAE.DIV_SCALAR_ARRAY(__), _ <| typ2 <|  nil(), _, _, _)  => begin
  typ2
end

(DAE.DIV_ARRAY_SCALAR(__), typ1 <| _ <|  nil(), _, _, _)  => begin
  typ1
end

(DAE.POW_ARRAY_SCALAR(__), typ1 <| _ <|  nil(), _, _, _)  => begin
  typ1
end

(DAE.POW_SCALAR_ARRAY(__), _ <| typ2 <|  nil(), _, _, _)  => begin
  typ2
end

(DAE.ADD(__), _, typ, _, _)  => begin
  typ
end

(DAE.SUB(__), _, typ, _, _)  => begin
  typ
end

(DAE.MUL(__), _, typ, _, _)  => begin
  typ
end

(DAE.DIV(__), _, typ, _, _)  => begin
  typ
end

(DAE.POW(__), _, typ, _, _)  => begin
  typ
end

(DAE.UMINUS(__), _, typ, _, _)  => begin
  typ
end

(DAE.UMINUS_ARR(__), typ1 <| _, _, _, _)  => begin
  typ1
end

(DAE.AND(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
  @match true = Types.equivtypes(typ1, typ2)
  typ1
end

(DAE.AND(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
  t1_str = Types.unparseType(typ1)
  t2_str = Types.unparseType(typ2)
  pre_str = PrefixUtil.printPrefixStr3(pre)
  Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("and", pre_str, t1_str, t2_str), inInfo)
  fail()
end

(DAE.OR(__), typ1 <| typ2 <|  nil(), _, _, _)  => begin
  @match true = Types.equivtypes(typ1, typ2)
  typ1
end

(DAE.OR(__), typ1 <| typ2 <|  nil(), _, pre, _)  => begin
  t1_str = Types.unparseType(typ1)
  t2_str = Types.unparseType(typ2)
  pre_str = PrefixUtil.printPrefixStr3(pre)
  Error.addSourceMessage(Error.INCOMPATIBLE_TYPES, list("or", pre_str, t1_str, t2_str), inInfo)
  fail()
end

(DAE.NOT(__), typ1 <|  nil(), _, _, _)  => begin
  typ1
end

(DAE.LESS(__), _, typ, _, _)  => begin
  typ
end

(DAE.LESSEQ(__), _, typ, _, _)  => begin
  typ
end

(DAE.GREATER(__), _, typ, _, _)  => begin
  typ
end

(DAE.GREATEREQ(__), _, typ, _, _)  => begin
  typ
end

(DAE.EQUAL(__), _, typ, _, _)  => begin
  typ
end

(DAE.NEQUAL(__), _, typ, _, _)  => begin
  typ
end

(DAE.USERDEFINED(__), _, typ, _, _)  => begin
  typ
end
end
end
outType
end

#= Returns the number of dimensions of a Type. =#
function nDims(inType::DAE.Type) ::ModelicaInteger
  local outInteger::ModelicaInteger

  outInteger = begin
    local ns::ModelicaInteger
    local t::DAE.Type
    @match inType begin
      DAE.T_INTEGER(__)  => begin
        0
      end

      DAE.T_REAL(__)  => begin
        0
      end

      DAE.T_STRING(__)  => begin
        0
      end

      DAE.T_BOOL(__)  => begin
        0
      end

      DAE.T_ARRAY(ty = t)  => begin
        ns = nDims(t)
        ns + 1
      end

      DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
        ns = nDims(t)
        ns
      end
    end
  end
  outInteger
end

#= Checks if two dimensions are equal, which is a prerequisite for matrix
multiplication. =#
function isValidMatrixProductDims(dim1::DAE.Dimension, dim2::DAE.Dimension) ::Bool
  Expression.dimensionsKnownAndEqual(dim1, dim2) || ! (Expression.dimensionKnown(dim1) || Expression.dimensionKnown(dim2)) || Flags.getConfigBool(Flags.CHECK_MODEL) && Expression.dimensionsEqual(dim1, dim2)
end

#= Returns the element type of a type, i.e. for arrays, return the
element type, and for bulitin scalar types return the type itself. =#
function elementType(inType::DAE.Type) ::DAE.Type
  local outType::DAE.Type

  outType = begin
    local t::DAE.Type
    local t_1::DAE.Type
    @match inType begin
      t && DAE.T_INTEGER(__)  => begin
        t
      end

      t && DAE.T_REAL(__)  => begin
        t
      end

      t && DAE.T_STRING(__)  => begin
        t
      end

      t && DAE.T_BOOL(__)  => begin
        t
      end

      DAE.T_ARRAY(ty = t)  => begin
        t_1 = elementType(t)
        t_1
      end

      DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
        t_1 = elementType(t)
        t_1
      end
    end
  end
  outType
end

#= Replaces a userdefined operator expression with a corresponding function
call expression. Other expressions just passes through. =#
function replaceOperatorWithFcall(AbExp::Absyn.Exp, inExp1::DAE.Exp, inOper::DAE.Operator, inExp2::Option{<:DAE.Exp}, inConst::DAE.Const) ::DAE.Exp
  local outExp::DAE.Exp

  outExp = begin
    local e1::DAE.Exp
    local e2::DAE.Exp
    local funcname::Absyn.Path
    local c::DAE.Const
    @matchcontinue (AbExp, inExp1, inOper, inExp2, inConst) begin
      (Absyn.BINARY(_, _, _), e1, DAE.USERDEFINED(fqName = funcname), SOME(e2), _)  => begin
        DAE.CALL(funcname, list(e1, e2), DAE.callAttrOther)
      end

      (Absyn.BINARY(_, _, _), e1, _, SOME(e2), _)  => begin
        DAE.BINARY(e1, inOper, e2)
      end

      (Absyn.UNARY(_, _), e1, DAE.USERDEFINED(fqName = funcname), NONE(), _)  => begin
        DAE.CALL(funcname, list(e1), DAE.callAttrOther)
      end

      (Absyn.UNARY(_, _), e1, _, NONE(), _)  => begin
        DAE.UNARY(inOper, e1)
      end

      (Absyn.LBINARY(_, _, _), e1, DAE.USERDEFINED(fqName = funcname), SOME(e2), _)  => begin
        DAE.CALL(funcname, list(e1, e2), DAE.callAttrOther)
      end

      (Absyn.LBINARY(_, _, _), e1, _, SOME(e2), _)  => begin
        DAE.LBINARY(e1, inOper, e2)
      end

      (Absyn.LUNARY(_, _), e1, DAE.USERDEFINED(fqName = funcname), NONE(), _)  => begin
        DAE.CALL(funcname, list(e1), DAE.callAttrOther)
      end

      (Absyn.LUNARY(_, _), e1, _, NONE(), _)  => begin
        DAE.LUNARY(inOper, e1)
      end

      (Absyn.RELATION(_, _, _), e1, DAE.USERDEFINED(fqName = funcname), SOME(e2), _)  => begin
        DAE.CALL(funcname, list(e1, e2), DAE.callAttrOther)
      end

      (Absyn.RELATION(_, _, _), e1, _, SOME(e2), _)  => begin
        DAE.RELATION(e1, inOper, e2, -1, NONE())
      end
    end
  end
  outExp
end

""" Check if we have Real == Real or Real != Real, if so give a warning. """
function warnUnsafeRelations(inEnv::FCore.Graph, inExp::Absyn.Exp, variability::DAE.Const, t1::DAE.Type, t2::DAE.Type, e1::DAE.Exp, e2::DAE.Exp, op::DAE.Operator, inPrefix::Prefix.PrefixType, inInfo::SourceInfo)
  _ = begin
    local b1::Bool
    local b2::Bool
    local stmtString::String
    local opString::String
    local pre_str::String
    local pre::Prefix.PrefixType
    #=  == or != on Real is permitted in functions, so don't print an error if
    =#
    #=  we're in a function.
    =#
    @matchcontinue (inEnv, inExp, variability, t1, t2, e1, e2, op, inPrefix, inInfo) begin
      (_, _, _, _, _, _, _, _, _, _)  => begin
        @match true = FGraph.inFunctionScope(inEnv)
        ()
      end

      (_, Absyn.RELATION(_, _, _), DAE.C_VAR(__), _, _, _, _, _, pre, _)  => begin
        b1 = Types.isReal(t1)
        b2 = Types.isReal(t1)
        @match true = boolOr(b1, b2)
        verifyOp(op)
        opString = ExpressionDump.relopSymbol(op)
        stmtString = ExpressionDump.printExpStr(e1) + opString + ExpressionDump.printExpStr(e2)
        Error.addSourceMessage(Error.WARNING_RELATION_ON_REAL, list(stmtString, opString), inInfo)
        ()
      end

      _  => begin
        ()
      end
    end
  end
end

"""
  Helper function for warnUnsafeRelations
  We only want to check DAE.EQUAL and Expression.NEQUAL since they are the only illegal real operations.
  """
function verifyOp(op::DAE.Operator)
  _ = begin
    @match op begin
      DAE.EQUAL(_)  => begin
        ()
      end

      DAE.NEQUAL(_)  => begin
        ()
      end
    end
  end
end

function errorMultipleValid(exps::List{<:DAE.Exp}, info::SourceInfo)
  local str1::String
  local str2::String
  str1 = intString(listLength(exps))
  str2 = stringDelimitList(ListUtil.map(exps, ExpressionDump.printExpStr), ",")
  Error.addSourceMessage(Error.OP_OVERLOAD_MULTIPLE_VALID, list(str1, str2), info)
end

function binaryCastConstructor(inCache::FCore.Cache, env::FCore.Graph, inExp1::DAE.Exp, inExp2::DAE.Exp, inType1::DAE.Type, inType2::DAE.Type, exps::List{<:Tuple{<:DAE.Exp, Option{<:DAE.Type}}}, types::List{<:DAE.Type}, info::SourceInfo) ::Tuple{FCore.Cache, List{Tuple{DAE.Exp, Option{DAE.Type}}}}
  local resExps::List{Tuple{DAE.Exp, Option{DAE.Type}}}
  local cache::FCore.Cache

  (cache, resExps) = begin
    local args::List{List{DAE.FuncArg}}
    local tys1::List{DAE.Type}
    local tys2::List{DAE.Type}
    local exps1::List{DAE.Exp}
    local exps2::List{DAE.Exp}
    @match (inCache, env, inExp1, inExp2, inType1, inType2, exps, types, info) begin
      (_, _, _, _, _, _, _ <|  nil(), _, _)  => begin
        (inCache, exps)
      end

      (_, _, _, _, _, _,  nil(), _, _)  => begin
        args = ListUtil.map(types, Types.getFuncArg)
        tys1 = ListUtil.mapMap(args, listHead, Types.funcArgType)
        args = ListUtil.map(args, ListUtil.rest)
        tys2 = ListUtil.mapMap(args, listHead, Types.funcArgType)
        tys1 = ListUtil.setDifference(ListUtil.union(tys1, nil), list(inType1))
        tys2 = ListUtil.setDifference(ListUtil.union(tys2, nil), list(inType2))
        (cache, tys1) = getOperatorFuncsOrEmpty(inCache, env, tys1, "'constructor'", info, nil)
        (cache, tys2) = getOperatorFuncsOrEmpty(cache, env, tys2, "'constructor'", info, nil)
        tys1 = ListUtil.select(tys1, isOperatorUnaryFunction)
        tys2 = ListUtil.select(tys2, isOperatorUnaryFunction)
        exps1 = deoverloadUnaryUserdefNoConstructor(tys1, inExp1, inType1, nil)
        exps2 = deoverloadUnaryUserdefNoConstructor(tys2, inExp2, inType2, nil)
        resExps = deoverloadBinaryUserdefNoConstructorListLhs(types, exps1, inExp2, inType2, nil)
        resExps = deoverloadBinaryUserdefNoConstructorListRhs(types, inExp1, exps2, inType1, resExps)
        (cache, resExps)
      end

      _  => begin
        errorMultipleValid(ListUtil.map(exps, Util.tuple21), info)
        fail()
      end
    end
  end
  (cache, resExps)
end

function getZeroConstructor(inCache::FCore.Cache, env::FCore.Graph, zexps::List{<:DAE.Exp}, impl::Bool, info::SourceInfo) ::Tuple{FCore.Cache, Option{Values.Value}}
  local zeroExpression::Option{Values.Value}
  local cache::FCore.Cache

  (cache, zeroExpression) = begin
    local zc::DAE.Exp
    local v::Values.Value
    @match zexps begin
      nil()  => begin
        (inCache, NONE())
      end

      zc <|  nil()  => begin
        (cache, v) = Ceval.ceval(inCache, env, zc, impl, Absyn.MSG(info), 0)
        (cache, SOME(v))
      end

      _  => begin
        errorMultipleValid(zexps, info)
        fail()
      end
    end
  end
  (cache, zeroExpression)
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

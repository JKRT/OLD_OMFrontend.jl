
#module StaticInterface
#import Patternm
#end

module Static


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    using Setfield

    @UniontypeDecl Slot
    PartialElabExpFunc = Function

    extraFunc = Function

    HandlerFunc = Function

    HandlerFunc = Function
    @UniontypeDecl ForceFunctionInst

         #= /*
         * This file is part of OpenModelica.
         *
         * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
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
        import Absyn
        import DAE
        import FCore
        import FCoreUtil
        import Prefix
        import SCode
        import Values

        import AbsynToSCode
        import AbsynUtil
        import FGraphUtil
        import FNode
        # import InstMeta
        # import MetaUtil
        import Util
         const SLOT_NOT_EVALUATED = 0::ModelicaInteger
         const SLOT_EVALUATING = 1::ModelicaInteger
         const SLOT_EVALUATED = 2::ModelicaInteger

         @Uniontype Slot begin
              @Record SLOT begin

                       defaultArg #= The slots default argument. =#::DAE.FuncArg
                       slotFilled #= True if the slot has been filled, otherwise false. =#::Bool
                       arg #= The argument for the slot given by the function call. =#::Option{DAE.Exp}
                       dims #= The dimensions of the slot. =#::DAE.Dimensions
                       idx #= The index of the slot, 1 = first slot etc. =#::ModelicaInteger
                       evalStatus::ModelicaInteger
              end
         end

         const BUILTIN_TIME = SOME((DAE.CREF(DAE.CREF_IDENT("time", DAE.T_REAL_DEFAULT, nil), DAE.T_REAL_DEFAULT), DAE.PROP(DAE.T_REAL_DEFAULT, DAE.C_VAR()), DAE.dummyAttrInput))::Option
        import ArrayUtil
        # import BackendInterface
        import Ceval
        import ClassInf
        import ComponentReference
        import Config
        import DAEUtil
        import Debug
        import Dump
        import Error
        import ErrorExt
        import Expression
        import ExpressionDump
        import ExpressionSimplify
        import Flags
        import Global
        import Inline
        import Inst
        import InstFunction
        import InstTypes
        import InnerOuterTypes
        import ListUtil
        import Lookup
        import Mutable
        import OperatorOverloading
        import PrefixUtil
        import Print
        import SCodeDump
        import SCodeUtil
        import System
        import Types
        import ValuesUtil
        import VarTransform

        MutableType = Mutable.MutableType

         #= Expression elaboration of Absyn.Exp list, i.e. lists of expressions. =#
        function elabExpList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:Absyn.Exp}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inLastType::DAE.Type = DAE.T_UNKNOWN_DEFAULT #= The type of the last evaluated expression; used to speed up instantiation of enumeration :) =#) ::Tuple{FCore.Cache, List{DAE.Exp}, List{DAE.Properties}}
              local outProperties::List{DAE.Properties} = nil
              local outExpl::List{DAE.Exp} = nil
              local outCache::FCore.Cache = inCache

              local exp::DAE.Exp
              local prop::DAE.Properties
              local last_ty::DAE.Type = inLastType

              for e in inExpl
                _ = begin
                    local cr::Absyn.ComponentRef
                    local path::Absyn.Path
                    local path1::Absyn.Path
                    local path2::Absyn.Path
                    local name::String
                    local names::List{String}
                    local idx::ModelicaInteger
                     #=  Hack to make enumeration arrays elaborate a _lot_ faster
                     =#
                  @matchcontinue (e, last_ty) begin
                    (Absyn.CREF(cr && Absyn.CREF_FULLYQUALIFIED(__)), DAE.T_ENUMERATION(path = path2, names = names))  => begin
                        path = AbsynUtil.crefToPath(cr)
                        @match (path1, Absyn.IDENT(name)) = AbsynUtil.splitQualAndIdentPath(path)
                        @match true = AbsynUtil.pathEqual(path1, path2)
                        idx = ListUtil.position(name, names)
                        exp = DAE.ENUM_LITERAL(path, idx)
                        prop = DAE.PROP(last_ty, DAE.C_CONST())
                      ()
                    end

                    _  => begin
                          (outCache, exp, prop) = elabExpInExpression(outCache, inEnv, e, inImplicit, inDoVect, inPrefix, inInfo)
                          last_ty = Types.getPropType(prop)
                        ()
                    end
                  end
                end
                outExpl = _cons(exp, outExpl)
                outProperties = _cons(prop, outProperties)
              end
              outExpl = listReverse(outExpl)
              outProperties = listReverse(outProperties)
          (outCache, outExpl, outProperties)
        end

        function elabExpList_enum(inExp::Absyn.Exp, inLastType::DAE.Type) ::ModelicaInteger
              local outIndex::ModelicaInteger

              outIndex = begin
                  local cr::Absyn.ComponentRef
                  local path::Absyn.Path
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local name::String
                  local names::List{String}
                @matchcontinue (inExp, inLastType) begin
                  (Absyn.CREF(cr && Absyn.CREF_FULLYQUALIFIED(__)), DAE.T_ENUMERATION(path = path2, names = names))  => begin
                      path = AbsynUtil.crefToPath(cr)
                      @match (path1, Absyn.IDENT(name)) = AbsynUtil.splitQualAndIdentPath(path)
                      @match true = AbsynUtil.pathEqual(path1, path2)
                    ListUtil.position(name, names)
                  end

                  _  => begin
                      -1
                  end
                end
              end
          outIndex
        end

         #= Expression elaboration of lists of lists of expressions.
          Used in for instance matrices, etc. =#
        function elabExpListList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:List{<:Absyn.Exp}}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inLastType::DAE.Type = DAE.T_UNKNOWN_DEFAULT #= The type of the last evaluated expression; used to speed up instantiation of enumerations :) =#) ::Tuple{FCore.Cache, List{List{DAE.Exp}}, List{List{DAE.Properties}}}
              local outProperties::List{List{DAE.Properties}} = nil
              local outExpl::List{List{DAE.Exp}} = nil
              local outCache::FCore.Cache = inCache

              local expl::List{DAE.Exp}
              local props::List{DAE.Properties}
              local last_ty::DAE.Type = inLastType

              for lst in inExpl
                (outCache, expl, props) = elabExpList(outCache, inEnv, lst, inImplicit, inDoVect, inPrefix, inInfo, last_ty)
                outExpl = _cons(expl, outExpl)
                outProperties = _cons(props, outProperties)
                last_ty = Types.getPropType(listHead(props))
              end
              outExpl = listReverse(outExpl)
              outProperties = listReverse(outProperties)
          (outCache, outExpl, outProperties)
        end

         #=
          elabExp, but for Option<Absyn.Exp>,DAE.Type => Option<DAE.Exp> =#
        function elabExpOptAndMatchType(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Option{<:Absyn.Exp}, inDefaultType::DAE.Type, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, Option{DAE.Exp}, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::Option{DAE.Exp}
              local outCache::FCore.Cache = inCache

              local exp::Absyn.Exp
              local dexp::DAE.Exp
              local prop::DAE.Properties

              outProperties = DAE.PROP(inDefaultType, DAE.C_CONST())
              if isSome(inExp)
                @match SOME(exp) = inExp
                (outCache, dexp, prop) = elabExpInExpression(outCache, inEnv, exp, inImplicit, inDoVect, inPrefix, inInfo)
                (dexp, outProperties) = Types.matchProp(dexp, prop, outProperties, true)
                outExp = SOME(dexp)
              else
                outExp = NONE()
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_BuiltinType(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              println("elabExp_BuiltinType")
              @show inExp

              (outExp, outProperties) = begin
                @match inExp begin
                  Absyn.INTEGER(__)  => begin
                    (DAE.ICONST(inExp.value), DAE.PROP(DAE.T_INTEGER_DEFAULT, DAE.C_CONST()))
                  end

                  Absyn.REAL(__)  => begin
                    (DAE.RCONST(stringReal(inExp.value)), DAE.PROP(DAE.T_REAL_DEFAULT, DAE.C_CONST()))
                  end

                  Absyn.STRING(__)  => begin
                    (DAE.SCONST(System.unescapedString(inExp.value)), DAE.PROP(DAE.T_STRING_DEFAULT, DAE.C_CONST()))
                  end

                  Absyn.BOOL(__)  => begin
                    (DAE.BCONST(inExp.value), DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_CONST()))
                  end
                end
              end
               #=  The types below should contain the default values of the attributes of the builtin
               =#
               #=  types. But since they are default, we can leave them out for now, unit=\\\"\\\" is not
               =#
               #=  that interesting to find out.
               =#
          (outCache, outExp, outProperties)
        end

        function elabExp_Cref(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local cr::Absyn.ComponentRef
              local ty::DAE.Type
              local c::DAE.Const

              @match Absyn.CREF(componentRef = cr) = inExp
              @match (outCache, SOME((outExp, outProperties, _))) = elabCref(inCache, inEnv, cr, inImplicit, inDoVect, inPrefix, inInfo)
               #=  BoschRexroth specifics, convert param to var.
               =#
              if ! Flags.getConfigBool(Flags.CEVAL_EQUATION)
                @match DAE.PROP(ty, c) = outProperties
                outProperties = if Types.isParameter(c)
                      DAE.PROP(ty, DAE.C_VAR())
                    else
                      outProperties
                    end
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_Binary(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local e1::Absyn.Exp
              local e2::Absyn.Exp
              local op::Absyn.Operator
              local prop1::DAE.Properties
              local prop2::DAE.Properties
              local exp1::DAE.Exp
              local exp2::DAE.Exp

              (e1, op, e2) = begin
                @match inExp begin
                  Absyn.BINARY(exp1 = e1, op = op, exp2 = e2)  => begin
                    (e1, op, e2)
                  end

                  Absyn.LBINARY(exp1 = e1, op = op, exp2 = e2)  => begin
                    (e1, op, e2)
                  end

                  Absyn.RELATION(exp1 = e1, op = op, exp2 = e2)  => begin
                    (e1, op, e2)
                  end
                end
              end
              (outCache, exp1, prop1) = elabExpInExpression(inCache, inEnv, e1, inImplicit, inDoVect, inPrefix, inInfo)
              (outCache, exp2, prop2) = elabExpInExpression(outCache, inEnv, e2, inImplicit, inDoVect, inPrefix, inInfo)
              (outCache, outExp, outProperties) = OperatorOverloading.binary(outCache, inEnv, op, prop1, exp1, prop2, exp2, inExp, e1, e2, inImplicit, inPrefix, inInfo)
           (outCache, outExp, outProperties)
        end

        function elabExp_Unary(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local e::Absyn.Exp
              local op::Absyn.Operator
              local ty::DAE.Type
              local c::DAE.Const

              @match Absyn.UNARY(op = op, exp = e) = inExp
              @match (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, inDoVect, inPrefix, inInfo)
              @match DAE.PROP(ty, c) = outProperties
              if ! (valueEq(op, Absyn.UPLUS()) && Types.isIntegerOrRealOrSubTypeOfEither(Types.arrayElementType(ty)))
                (outCache, outExp, outProperties) = OperatorOverloading.unary(outCache, inEnv, op, outProperties, outExp, inExp, e, inImplicit, inPrefix, inInfo)
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_LUnary(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local e::Absyn.Exp
              local op::Absyn.Operator

              @match Absyn.LUNARY(op = op, exp = e) = inExp
              (outCache, outExp, outProperties) = elabExpInExpression(outCache, inEnv, e, inImplicit, inDoVect, inPrefix, inInfo)
              (outCache, outExp, outProperties) = OperatorOverloading.unary(outCache, inEnv, op, outProperties, outExp, inExp, e, inImplicit, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= Elaborates an if-expression. If one of the branches can not be elaborated and
           the condition is parameter or constant; it is evaluated and the correct branch is selected.
           This is a dirty hack to make MSL CombiTable models work!
           Note: Because of this, the function has to rollback or delete an ErrorExt checkpoint. =#
        function elabExp_If(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local cond_e::Absyn.Exp
              local true_e::Absyn.Exp
              local false_e::Absyn.Exp
              local cond_exp::DAE.Exp
              local true_exp::DAE.Exp
              local false_exp::DAE.Exp
              local cond_prop::DAE.Properties
              local true_prop::DAE.Properties
              local false_prop::DAE.Properties
              local cache::FCore.Cache
              local b::Bool

              @match Absyn.IFEXP(ifExp = cond_e, trueBranch = true_e, elseBranch = false_e) = AbsynUtil.canonIfExp(inExp)
              (cache, cond_exp, cond_prop) = elabExpInExpression(inCache, inEnv, cond_e, inImplicit, inDoVect, inPrefix, inInfo)
              _ = begin
                @matchcontinue () begin
                  ()  => begin
                      ErrorExt.setCheckpoint("Static.elabExp:IFEXP")
                      (outCache, true_exp, true_prop) = elabExpInExpression(cache, inEnv, true_e, inImplicit, inDoVect, inPrefix, inInfo)
                      (outCache, false_exp, false_prop) = elabExpInExpression(outCache, inEnv, false_e, inImplicit, inDoVect, inPrefix, inInfo)
                      (outCache, outExp, outProperties) = makeIfExp(outCache, inEnv, cond_exp, cond_prop, true_exp, true_prop, false_exp, false_prop, inImplicit, inPrefix, inInfo)
                      ErrorExt.delCheckpoint("Static.elabExp:IFEXP")
                    ()
                  end

                  ()  => begin
                      ErrorExt.setCheckpoint("Static.elabExp:IFEXP:HACK") #= Extra rollback point so we get the regular error message only once if the hack fails =#
                      @match true = Types.isParameterOrConstant(Types.propAllConst(cond_prop))
                      @match (outCache, Values.BOOL(b)) = Ceval.ceval(cache, inEnv, cond_exp, inImplicit, Absyn.MSG(inInfo))
                      (outCache, outExp, outProperties) = elabExpInExpression(outCache, inEnv, if b
                            true_e
                          else
                            false_e
                          end, inImplicit, inDoVect, inPrefix, inInfo)
                      ErrorExt.delCheckpoint("Static.elabExp:IFEXP:HACK")
                      ErrorExt.rollBack("Static.elabExp:IFEXP")
                    ()
                  end

                  _  => begin
                        ErrorExt.rollBack("Static.elabExp:IFEXP:HACK")
                        ErrorExt.delCheckpoint("Static.elabExp:IFEXP")
                      fail()
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_Call(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local func_name::Absyn.ComponentRef
              local args::Absyn.FunctionArgs
              local arg::Absyn.Exp
              local last_id::String

              @match Absyn.CALL(function_ = func_name, functionArgs = args) = inExp
              _ = begin
                @match args begin
                  Absyn.FUNCTIONARGS(__)  => begin
                      (outCache, outExp, outProperties) = elabCall(inCache, inEnv, func_name, args.args, args.argNames, inImplicit, inPrefix, inInfo)
                      (outExp, _) = ExpressionSimplify.simplify1(outExp)
                    ()
                  end

                  Absyn.FOR_ITER_FARG(__)  => begin
                      (outCache, outExp, outProperties) = elabCallReduction(inCache, inEnv, func_name, args.exp, args.iterType, args.iterators, inImplicit, inDoVect, inPrefix, inInfo)
                    ()
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_Dot(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              (outExp, outProperties) = begin
                  local s::String
                  local ty::DAE.Type
                @match inExp begin
                  Absyn.DOT(__)  => begin
                      s = begin
                        @match inExp.index begin
                          Absyn.CREF(Absyn.CREF_IDENT(name = s))  => begin
                            s
                          end

                          _  => begin
                                Error.addSourceMessage(Error.COMPILER_ERROR, list("Dot operator is only allowed when indexing using a single simple name, got: " + Dump.printExpStr(inExp.index)), inInfo)
                              fail()
                          end
                        end
                      end
                      (outCache, outExp, outProperties) = elabExp(inCache, inEnv, inExp.exp, inImplicit, inDoVect, inPrefix, inInfo)
                      ty = Types.getPropType(outProperties)
                      _ = begin
                          local names::List{String}
                          local i::ModelicaInteger
                        @match ty begin
                          DAE.T_TUPLE(names = SOME(names))  => begin
                              if ! listMember(s, names)
                                Error.addSourceMessage(Error.COMPILER_ERROR, list("Dot operator could not find " + s + " in " + Types.unparseType(ty)), inInfo)
                                fail()
                              end
                              i = ListUtil.position(s, names)
                              outExp = DAE.TSUB(outExp, i, listGet(ty.types, i))
                              outProperties = DAE.PROP(listGet(ty.types, i), Types.propAllConst(outProperties))
                            ()
                          end

                          _  => begin
                                Error.addSourceMessage(Error.COMPILER_ERROR, list("Dot operator is only allowed when the expression returns a named tuple. Got expression: " + ExpressionDump.printExpStr(outExp) + " with type " + Types.unparseType(ty)), inInfo)
                              fail()
                          end
                        end
                      end
                    (outExp, outProperties)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= turns an Absyn.PARTEVALFUNCTION into an DAE.PARTEVALFUNCTION =#
        function elabExp_PartEvalFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local cref::Absyn.ComponentRef
              local pos_args::List{Absyn.Exp}
              local named_args::List{Absyn.NamedArg}
              local path::Absyn.Path
              local ty::DAE.Type
              local tty::DAE.Type
              local tty2::DAE.Type
              local args::List{DAE.Exp}
              local consts::List{DAE.Const}
              local slots::List{Slot}
              local c::DAE.Const

              @match Absyn.PARTEVALFUNCTION(cref, Absyn.FUNCTIONARGS(pos_args, named_args)) = inExp
              if listEmpty(pos_args) && listEmpty(named_args)
                (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, Absyn.CREF(cref), inImplicit, inDoVect, inPrefix, inInfo)
              else
                path = AbsynUtil.crefToPath(cref)
                @match (outCache, list(tty)) = Lookup.lookupFunctionsInEnv(inCache, inEnv, path, inInfo)
                tty = Types.makeFunctionPolymorphicReference(tty)
                (outCache, args, consts, _, tty, _, slots) = elabTypes(outCache, inEnv, pos_args, named_args, list(tty), true, true, inImplicit, inPrefix, inInfo)
                if ! Types.isFunctionPointer(tty)
                  (outCache, path) = Inst.makeFullyQualified(outCache, inEnv, path)
                  @match (outCache, Util.SUCCESS()) = instantiateDaeFunction(outCache, inEnv, path, false, NONE(), true)
                end
                tty2 = stripExtraArgsFromType(slots, tty)
                tty2 = Types.makeFunctionPolymorphicReference(tty2)
                ty = Types.simplifyType(tty2)
                tty = Types.simplifyType(tty)
                c = ListUtil.fold(consts, Types.constAnd, DAE.C_CONST(), DAE.Const)
                outExp = DAE.PARTEVALFUNCTION(path, args, ty, tty)
                outProperties = DAE.PROP(tty2, c)
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_Tuple(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              (outCache, outExp, outProperties) = elabExp_Tuple_LHS_RHS(inCache, inEnv, inExp, inImplicit, inDoVect, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

        function elabExp_Tuple_LHS_RHS(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, isLhs::Bool = false) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local el::List{Absyn.Exp}
              local expl::List{DAE.Exp}
              local props::List{DAE.Properties}
              local types::List{DAE.Type}
              local consts::List{DAE.TupleConst}

              @match Absyn.TUPLE(expressions = el) = inExp
              (outCache, expl, props) = elabTuple(outCache, inEnv, el, inImplicit, inDoVect, inPrefix, inInfo, isLhs)
              (types, consts) = splitProps(props)
              (outExp, outProperties) = fixTupleMetaModelica(expl, types, consts)
          (outCache, outExp, outProperties)
        end

         #= Special check for tuples, which only occur on the LHS =#
        function elabExpLHS(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              (outCache, outExp, outProperties) = begin
                @match inExp begin
                  Absyn.TUPLE(__)  => begin
                      (outCache, outExp, outProperties) = elabExp_Tuple_LHS_RHS(inCache, inEnv, inExp, inImplicit, inDoVect, inPrefix, inInfo, isLhs = true)
                    (outCache, outExp, outProperties)
                  end

                  _  => begin
                        (outCache, outExp, outProperties) = elabExp(inCache, inEnv, inExp, inImplicit, inDoVect, inPrefix, inInfo)
                      (outCache, outExp, outProperties)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= Elaborates a range expression on the form start:stop or start:step:stop. =#
        function elabExp_Range(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local start::Absyn.Exp
              local step::Absyn.Exp
              local stop::Absyn.Exp
              local ostep::Option{Absyn.Exp}
              local start_exp::DAE.Exp
              local step_exp::DAE.Exp
              local stop_exp::DAE.Exp
              local ostep_exp::Option{DAE.Exp} = NONE()
              local start_ty::DAE.Type
              local step_ty::DAE.Type
              local stop_ty::DAE.Type
              local ety::DAE.Type
              local ty::DAE.Type
              local ostep_ty::Option{DAE.Type} = NONE()
              local start_c::DAE.Const
              local step_c::DAE.Const
              local stop_c::DAE.Const
              local c::DAE.Const

              @match Absyn.RANGE(start = start, step = ostep, stop = stop) = inExp
               #=  Elaborate start and stop of the range.
               =#
              @match (outCache, start_exp, DAE.PROP(start_ty, start_c)) = elabExpInExpression(inCache, inEnv, start, inImplicit, inDoVect, inPrefix, inInfo)
              @match (outCache, stop_exp, DAE.PROP(stop_ty, stop_c)) = elabExpInExpression(outCache, inEnv, stop, inImplicit, inDoVect, inPrefix, inInfo)
              c = Types.constAnd(start_c, stop_c)
               #=  If step was given, elaborate it too.
               =#
              if isSome(ostep)
                @match SOME(step) = ostep
                @match (outCache, step_exp, DAE.PROP(step_ty, step_c)) = elabExpInExpression(outCache, inEnv, step, inImplicit, inDoVect, inPrefix, inInfo)
                ostep_exp = SOME(step_exp)
                ostep_ty = SOME(step_ty)
                c = Types.constAnd(c, step_c)
              end
              if Types.isBoxedType(start_ty)
                (start_exp, start_ty) = Types.matchType(start_exp, start_ty, Types.unboxedType(start_ty), true)
              end
              if Types.isBoxedType(stop_ty)
                (stop_exp, stop_ty) = Types.matchType(stop_exp, stop_ty, Types.unboxedType(stop_ty), true)
              end
              (start_exp, ostep_exp, stop_exp, ety) = deoverloadRange(start_exp, start_ty, ostep_exp, ostep_ty, stop_exp, stop_ty, inInfo)
              (outCache, ty) = elabRangeType(outCache, inEnv, start_exp, ostep_exp, stop_exp, start_ty, ety, c, inImplicit)
              outExp = DAE.RANGE(ety, start_exp, ostep_exp, stop_exp)
              outProperties = DAE.PROP(ty, c)
          (outCache, outExp, outProperties)
        end

        #= Checks that an array type is valid. =#
       function checkArrayType(inType::DAE.Type)
             local el_ty::DAE.Type

             el_ty = Types.arrayElementType(inType)
             @match false = ! Types.isString(el_ty) && Types.isBoxedType(el_ty) || Flags.isSet(Flags.RML)
       end


        function elabExp_Array(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local es::List{Absyn.Exp}
              local expl::List{DAE.Exp}
              local props::List{DAE.Properties}
              local ty::DAE.Type
              local arr_ty::DAE.Type
              local c::DAE.Const
              local exp::DAE.Exp

              (outExp, outProperties) = begin
                @matchcontinue inExp begin
                  Absyn.ARRAY( nil()) where (Config.acceptMetaModelicaGrammar())  => begin
                    (DAE.LIST(nil), DAE.PROP(DAE.T_METALIST_DEFAULT, DAE.C_CONST()))
                  end

                  Absyn.ARRAY(arrayExp = es)  => begin
                       #=  Part of the MetaModelica extension. This eliminates elabArray failed
                       =#
                       #=  failtraces when using the empty list. sjoelund
                       =#
                       #=  array expressions, e.g. {1,2,3}
                       =#
                      (outCache, expl, props) = elabExpList(inCache, inEnv, es, inImplicit, inDoVect, inPrefix, inInfo)
                      @match (expl, DAE.PROP(ty, c)) = elabArray(expl, props, inPrefix, inInfo)
                       #=  type-checking the array
                       =#
                      arr_ty = DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(listLength(expl))))
                      exp = DAE.ARRAY(Types.simplifyType(arr_ty), ! Types.isArray(ty), expl)
                      checkArrayType(ty)
                      exp = elabMatrixToMatrixExp(exp)
                    (exp, DAE.PROP(arr_ty, c))
                  end

                  Absyn.ARRAY(arrayExp = es) where (Config.acceptMetaModelicaGrammar())  => begin
                       #=  Part of the MetaModelica extension. KS
                       =#
                      (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, Absyn.LIST(es), inImplicit, inDoVect, inPrefix, inInfo)
                    (outExp, outProperties)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabExp_Matrix(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local ess::List{List{Absyn.Exp}}
              local dess::List{List{DAE.Exp}}
              local dess2::List{List{DAE.Exp}}
              local props::List{List{DAE.Properties}}
              local tps::List{List{DAE.Type}}
              local tys::List{DAE.Type}
              local tys2::List{DAE.Type}
              local nmax::ModelicaInteger
              local have_real::Bool
              local ty::DAE.Type
              local c::DAE.Const
              local dim1::DAE.Dimension
              local dim2::DAE.Dimension
              local expl::List{DAE.Exp}

               #=  Elaborate the individual expressions.
               =#
              @match Absyn.MATRIX(matrix = ess) = inExp
              (outCache, dess, props) = elabExpListList(inCache, inEnv, ess, inImplicit, inDoVect, inPrefix, inInfo)
               #=  Check if any of the expressions is of Real type.
               =#
              tys = listAppend(list(Types.getPropType(p) for p in pl) for pl in props)
              nmax = matrixConstrMaxDim(tys)
              have_real = Types.containReal(tys)
               #=  If we have any Real expressions, cast any Integer expressions to Real.
               =#
              if have_real
                (dess, props) = ListUtil.threadMapList_2(dess, props, elabExp_Matrix_realCast)
              end
              @match (outCache, outExp, DAE.PROP(ty, c), dim1, dim2) = elabMatrixSemi(outCache, inEnv, dess, props, inImplicit, have_real, nmax, inDoVect, inPrefix, inInfo)
              outExp = elabMatrixToMatrixExp(outExp)
              ty = Types.unliftArray(Types.unliftArray(ty))
               #=  All elts promoted to matrix, therefore unlifting.
               =#
              ty = DAE.T_ARRAY(ty, list(dim2))
              ty = DAE.T_ARRAY(ty, list(dim1))
              outProperties = DAE.PROP(ty, c)
          (outCache, outExp, outProperties)
        end

         #= Casts an expression and property to Real if it's current type is Integer. =#
        function elabExp_Matrix_realCast(inExp::DAE.Exp, inProperties::DAE.Properties) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              local ty::DAE.Type

              ty = Types.getPropType(inProperties)
              if Types.isInteger(ty)
                ty = Types.setArrayElementType(ty, DAE.T_REAL_DEFAULT)
                outProperties = Types.setPropType(inProperties, ty)
                ty = Types.simplifyType(ty)
                (outExp, _) = ExpressionSimplify.simplify1(DAE.CAST(ty, inExp))
              else
                outExp = inExp
                outProperties = inProperties
              end
          (outExp, outProperties)
        end

        function elabExp_Code(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local ty::DAE.Type
              local ty2::DAE.Type
              local cn::Absyn.CodeNode

              @match Absyn.CODE(code = cn) = inExp
              ty = elabCodeType(cn)
              ty2 = Types.simplifyType(ty)
              outExp = DAE.CODE(cn, ty2)
              outProperties = DAE.PROP(ty, DAE.C_CONST())
          (outCache, outExp, outProperties)
        end

        function elabExp_ConselabExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local e1::Absyn.Exp
              local e2::Absyn.Exp
              local exp1::DAE.Exp
              local exp2::DAE.Exp
              local prop1::DAE.Properties
              local ty::DAE.Type
              local ty1::DAE.Type
              local ty2::DAE.Type
              local c1::DAE.Const
              local c2::DAE.Const
              local exp_str::String
              local ty1_str::String
              local ty2_str::String

              @match Absyn.CONS(e1, e2) = inExp
              # @match list(e1, e2) = MetaUtil.transformArrayNodesToListNodes(list(e1, e2))
               #=  Elaborate both sides of the cons expression.
               =#
              (outCache, exp1, prop1) = elabExpInExpression(outCache, inEnv, e1, inImplicit, inDoVect, inPrefix, inInfo)
              @match (outCache, exp2, DAE.PROP(DAE.T_METALIST(ty = ty2), c2)) = elabExpInExpression(outCache, inEnv, e2, inImplicit, inDoVect, inPrefix, inInfo)
              try
                ty1 = Types.getUniontypeIfMetarecordReplaceAllSubtypes(Types.getPropType(prop1))
                ty2 = Types.getUniontypeIfMetarecordReplaceAllSubtypes(ty2)
                c1 = Types.propAllConst(prop1)
                ty = Types.getUniontypeIfMetarecordReplaceAllSubtypes(Types.superType(Types.boxIfUnboxedType(ty1), Types.boxIfUnboxedType(ty2)))
                (exp1, _) = Types.matchType(exp1, ty1, ty, true)
                ty = DAE.T_METALIST(ty)
                (exp2, _) = Types.matchType(exp2, ty, DAE.T_METALIST(ty2), true)
                outExp = DAE.CONS(exp1, exp2)
                outProperties = DAE.PROP(ty, Types.constAnd(c1, c2))
              catch
                exp_str = Dump.printExpStr(inExp)
                ty1_str = Types.unparseType(Types.getPropType(prop1))
                ty2_str = Types.unparseType(ty2)
                Error.addSourceMessage(Error.META_CONS_TYPE_MATCH, list(exp_str, ty1_str, ty2_str), inInfo)
                fail()
              end
               #=  Replace all metarecords with uniontypes with.
               =#
               #=  Make sure the operands have correct types.
               =#
          (outCache, outExp, outProperties)
        end

        function elabExp_ListelabExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache
              local es::List{Absyn.Exp}
              local expl::List{DAE.Exp}
              local props::List{DAE.Properties}
              local types::List{DAE.Type}
              local consts::List{DAE.Const}
              local c::DAE.Const
              local ty::DAE.Type

              @match Absyn.LIST(exps = es) = inExp
               #=  The Absyn.LIST() node is used for list expressions that are transformed
               =#
               #=  from Absyn.ARRAY()
               =#
              if listEmpty(es)
                outExp = DAE.LIST(nil)
                outProperties = DAE.PROP(DAE.T_METALIST_DEFAULT, DAE.C_CONST())
              else
                (outCache, expl, props) = elabExpList(inCache, inEnv, es, inImplicit, inDoVect, inPrefix, inInfo)
                types = list(Types.getPropType(p) for p in props)
                consts = Types.getConstList(props)
                c = ListUtil.fold(consts, Types.constAnd, DAE.C_CONST(), DAE.Const)
                ty = Types.boxIfUnboxedType(ListUtil.reduce(types, Types.superType))
                expl = Types.matchTypes(expl, types, ty, true)
                outExp = DAE.LIST(expl)
                outProperties = DAE.PROP(DAE.T_METALIST(ty), c)
              end

          (outCache, outExp, outProperties)
        end

        #=
       function: elabExp
         Static analysis of expressions means finding out the properties of
         the expression.  These properties are described by the
         DAE.Properties type, and include the type and the variability of the
         expression.  This function performs analysis, and returns an
         DAE.Exp and the properties. =#
       function elabExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
             local outProperties::DAE.Properties
             local outExp::DAE.Exp
             local outCache::FCore.Cache = inCache

             local e::Absyn.Exp
             local num_errmsgs::ModelicaInteger
             local exp::DAE.Exp
             local exp1::DAE.Exp
             local exp2::DAE.Exp
             local prop1::DAE.Properties
             local prop2::DAE.Properties
             local ty::DAE.Type
             local c::DAE.Const
             local elabfunc::PartialElabExpFunc

             println("elabExp")
              #=  Apply any rewrite rules we have, if any.
              =#
             e = inExp #= if BackendInterface.noRewriteRulesFrontEnd()
                   inExp
                 else
                   BackendInterface.rewriteFrontEnd(inExp)
                 end =#
             num_errmsgs = Error.getNumErrorMessages()
             try
               elabfunc = begin
                 @match e begin
                   Absyn.END(__)  => begin
                       Error.addSourceMessage(Error.END_ILLEGAL_USE_ERROR, nil, inInfo)
                     fail()
                   end

                   Absyn.CREF(__)  => begin
                     elabExp_Cref
                   end

                   Absyn.BINARY(__)  => begin
                     elabExp_Binary
                   end

                   Absyn.UNARY(__)  => begin
                     elabExp_Unary
                   end

                   Absyn.LBINARY(__)  => begin
                     elabExp_Binary
                   end

                   Absyn.LUNARY(__)  => begin
                     elabExp_LUnary
                   end

                   Absyn.RELATION(__)  => begin
                     elabExp_Binary
                   end

                   Absyn.IFEXP(__)  => begin
                     elabExp_If
                   end

                   Absyn.CALL(__)  => begin
                     elabExp_Call
                   end

                   Absyn.PARTEVALFUNCTION(__)  => begin
                     elabExp_PartEvalFunction
                   end

                   Absyn.TUPLE(__)  => begin
                     elabExp_Tuple
                   end

                   Absyn.RANGE(__)  => begin
                     elabExp_Range
                   end

                   Absyn.ARRAY(__)  => begin
                     elabExp_Array
                   end

                   Absyn.MATRIX(__)  => begin
                     elabExp_Matrix
                   end

                   Absyn.CODE(__)  => begin
                     elabExp_Code
                   end

                   Absyn.CONS(__)  => begin
                     elabExp_Cons
                   end

                   Absyn.LIST(__)  => begin
                     elabExp_List
                   end

                   #Absyn.MATCHEXP(__)  => begin
                    # StaticInterface.elabMatchExpression
                   #end

                   Absyn.DOT(__)  => begin
                     elabExp_Dot
                   end

                   _  => begin
                       elabExp_BuiltinType
                   end
                 end
               end
               (outCache, outExp, outProperties) = elabfunc(inCache, inEnv, e, inImplicit, inDoVect, inPrefix, inInfo)
             catch ex
               @match true = num_errmsgs == Error.getNumErrorMessages()
               Error.addSourceMessage(Error.GENERIC_ELAB_EXPRESSION, list(Dump.printExpStr(e)), inInfo)
               fail()
             end
         (outCache, outExp, outProperties)
       end

         #= Like elabExp but casts PROP_TUPLE to a PROP =#
        function elabExpInExpression(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inImplicit::Bool, performVectorization::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = elabExp(inCache, inEnv, inExp, inImplicit, performVectorization, inPrefix, info)
              (outExp, outProperties) = elabExpInExpression2(outExp, outProperties)
          (outCache, outExp, outProperties)
        end

        function elabExpInExpression2(inExp::DAE.Exp, inProperties::DAE.Properties) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProperties) = begin
                  local ty::DAE.Type
                  local c::DAE.Const
                @match (inExp, inProperties) begin
                  (_, DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types = ty <| _), tupleConst = DAE.TUPLE_CONST(tupleConstLst = DAE.SINGLE_CONST(constType = c) <| _)))  => begin
                    (DAE.TSUB(inExp, 1, ty), DAE.PROP(ty, c))
                  end

                  _  => begin
                      (inExp, inProperties)
                  end
                end
              end
          (outExp, outProperties)
        end

        function checkAssignmentToInput(inExp::Absyn.Exp, inAttributes::DAE.Attributes, inEnv::FCore.Graph, inAllowTopLevelInputs::Bool, inInfo::SourceInfo)
               #=  If we don't allow top level inputs and we're in a function scope and not
               =#
               #=  using parmodelica, check for assignment to input.
               =#
              if ! inAllowTopLevelInputs && FGraphUtil.inFunctionScope(inEnv) && ! Config.acceptParModelicaGrammar()
                checkAssignmentToInput2(inExp, inAttributes, inInfo)
              end
        end

        function checkAssignmentToInput2(inExp::Absyn.Exp, inAttributes::DAE.Attributes, inInfo::SourceInfo)
              _ = begin
                  local cr::Absyn.ComponentRef
                  local cr_str::String
                @match (inExp, inAttributes, inInfo) begin
                  (Absyn.CREF(cr), DAE.ATTR(direction = Absyn.INPUT(__)), _)  => begin
                      cr_str = Dump.printComponentRefStr(cr)
                      Error.addSourceMessage(Error.ASSIGN_READONLY_ERROR, list("input", cr_str), inInfo)
                    fail()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkAssignmentToInputs(inExpCrefs::List{<:Absyn.Exp}, inAttributes::List{<:DAE.Attributes}, inEnv::FCore.Graph, inInfo::SourceInfo)
              if FGraphUtil.inFunctionScope(inEnv)
                ListUtil.threadMap1_0(inExpCrefs, inAttributes, checkAssignmentToInput2, inInfo)
              end
        end

         #= elaborates a list of expressions that are only component references. =#
        function elabExpCrefNoEvalList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:Absyn.Exp}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Exp}, List{DAE.Properties}, List{DAE.Attributes}}
              local outAttributes::List{DAE.Attributes} = nil
              local outProperties::List{DAE.Properties} = nil
              local outExpl::List{DAE.Exp} = nil
              local outCache::FCore.Cache = inCache

              local num_err::ModelicaInteger = Error.getNumErrorMessages()
              local exp::DAE.Exp
              local prop::DAE.Properties
              local props::List{DAE.Properties} = nil
              local attr::DAE.Attributes
              local cr::Absyn.ComponentRef
              local ty::DAE.Type
              local c::DAE.Const

              for e in inExpl
                try
                  @match Absyn.CREF(componentRef = cr) = e
                  (outCache, exp, prop, attr) = elabCrefNoEval(outCache, inEnv, cr, inImplicit, inDoVect, inPrefix, inInfo)
                  outExpl = _cons(exp, outExpl)
                  outAttributes = _cons(attr, outAttributes)
                  props = _cons(prop, props)
                catch
                  @match true = num_err == Error.getNumErrorMessages()
                  Error.addSourceMessage(Error.GENERIC_ELAB_EXPRESSION, list(Dump.printExpStr(e)), inInfo)
                end
              end
               #=  BoschRexroth specifics, convert all params to vars.
               =#
              if ! Flags.getConfigBool(Flags.CEVAL_EQUATION)
                for p in props
                  @match DAE.PROP(ty, c) = p
                  p = if Types.isParameter(c)
                        DAE.PROP(ty, DAE.C_VAR())
                      else
                        p
                      end
                  outProperties = _cons(p, outProperties)
                end
              else
                outProperties = listReverse(props)
              end
              outExpl = listReverse(outExpl)
              outAttributes = listReverse(outAttributes)
          (outCache, outExpl, outProperties, outAttributes)
        end

         #=  Part of MetaModelica extension
         =#

         #= Function that elaborates the MetaModelica list type,
        for instance list<Integer>.
        This is used by Inst.mo when handling a var := {...} statement =#
        function elabListExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExpList::List{<:Absyn.Exp}, inProp::DAE.Properties, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local expl::List{DAE.Exp}
                  local props::List{DAE.Properties}
                  local types::List{DAE.Type}
                  local c::DAE.Const
                  local ty::DAE.Type
                @matchcontinue inExpList begin
                   nil()  => begin
                    (inCache, DAE.LIST(nil), inProp)
                  end

                  _  => begin
                      @match DAE.PROP(DAE.T_METALIST(), c) = inProp
                      (outCache, expl, props) = elabExpList(inCache, inEnv, inExpList, inImplicit, inDoVect, inPrefix, inInfo)
                      types = list(Types.getPropType(p) for p in props)
                      (expl, ty) = Types.listMatchSuperType(expl, types, true)
                      outProperties = DAE.PROP(DAE.T_METALIST(ty), c)
                    (outCache, DAE.LIST(expl), outProperties)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Static.elabListExp failed, non-matching args in list constructor?")
                      fail()
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= /* ------------------------------- */ =#

         #=  Converts equations to algorithm assignments.
         Matchcontinue expressions may contain statements that you won't find
         in a normal equation section. For instance:

         case(...)
         local
         equation
             (var1,_,MYREC(...)) = func(...);
            fail();
         then 1; =#
        function fromEquationsToAlgAssignments(cp::Absyn.ClassPart) ::List{Absyn.AlgorithmItem}
              local algsOut::List{Absyn.AlgorithmItem}

              algsOut = begin
                  local rest::List{Absyn.EquationItem}
                  local alg::List{Absyn.AlgorithmItem}
                  local str::String
                @match cp begin
                  Absyn.ALGORITHMS(alg)  => begin
                    alg
                  end

                  Absyn.EQUATIONS(rest)  => begin
                    fromEquationsToAlgAssignmentsWork(rest)
                  end

                  _  => begin
                        str = Dump.unparseClassPart(cp)
                        Error.addInternalError("Static.fromEquationsToAlgAssignments: Unknown classPart in match expression:\\n" + str, sourceInfo())
                      fail()
                  end
                end
              end
          algsOut
        end

         #= Converts equations to algorithm assignments.
           Matchcontinue expressions may contain statements that you won't find
           in a normal equation section. For instance:

             case(...)
               equation
                 (var1, _, MYREC(...)) = func(...);
                 fail();
               then
                 1; =#
        function fromEquationsToAlgAssignmentsWork(eqsIn::List{<:Absyn.EquationItem}) ::List{Absyn.AlgorithmItem}
              local algsOut::List{Absyn.AlgorithmItem} = nil

              for ei in eqsIn
                _ = begin
                    local eq::Absyn.Equation
                    local comment::Option{Absyn.Comment}
                    local info::SourceInfo
                    local algs::List{Absyn.AlgorithmItem}
                  @match ei begin
                    Absyn.EQUATIONITEM(equation_ = eq, comment = comment, info = info)  => begin
                        algs = fromEquationToAlgAssignment(eq, comment, info)
                        algsOut = listAppend(algs, algsOut)
                      ()
                    end

                    Absyn.EQUATIONITEMCOMMENT(__)  => begin
                      ()
                    end
                  end
                end
              end
              algsOut = listReverse(algsOut)
          algsOut
        end

         #= Converts equations to algorithm assignments. =#
        function fromEquationBranchesToAlgBranches(eqsIn::List{<:Tuple{<:Absyn.Exp, List{<:Absyn.EquationItem}}}) ::List{Tuple{Absyn.Exp, List{Absyn.AlgorithmItem}}}
              local algsOut::List{Tuple{Absyn.Exp, List{Absyn.AlgorithmItem}}} = nil

              local e::Absyn.Exp
              local eqs::List{Absyn.EquationItem}
              local algs::List{Absyn.AlgorithmItem}

              for branch in eqsIn
                (e, eqs) = branch
                algs = fromEquationsToAlgAssignmentsWork(eqs)
                algsOut = _cons((e, algs), algsOut)
              end
              algsOut = listReverse(algsOut)
          algsOut
        end

         #= function: fromEquationToAlgAssignment =#
        function fromEquationToAlgAssignment(eq::Absyn.Equation, comment::Option{<:Absyn.Comment}, info::SourceInfo) ::List{Absyn.AlgorithmItem}
              local algStatement::List{Absyn.AlgorithmItem}

              algStatement = begin
                  local str::String
                  local strLeft::String
                  local strRight::String
                  local left::Absyn.Exp
                  local right::Absyn.Exp
                  local e::Absyn.Exp
                  local algItem::Absyn.AlgorithmItem
                  local algItem1::Absyn.AlgorithmItem
                  local algItem2::Absyn.AlgorithmItem
                  local eq2::Absyn.Equation
                  local comment2::Option{Absyn.Comment}
                  local info2::SourceInfo
                  local res::Absyn.AlgorithmItem
                  local cref::Absyn.ComponentRef
                  local fargs::Absyn.FunctionArgs
                  local algs::List{Absyn.AlgorithmItem}
                  local algTrueItems::List{Absyn.AlgorithmItem}
                  local algElseItems::List{Absyn.AlgorithmItem}
                  local algBranches::List{Tuple{Absyn.Exp, List{Absyn.AlgorithmItem}}}
                  local eqTrueItems::List{Absyn.EquationItem}
                  local eqElseItems::List{Absyn.EquationItem}
                  local eqBranches::List{Tuple{Absyn.Exp, List{Absyn.EquationItem}}}
                @matchcontinue eq begin
                  Absyn.EQ_EQUALS(Absyn.CREF(Absyn.CREF_IDENT(strLeft,  nil())), Absyn.CREF(Absyn.CREF_IDENT(strRight,  nil())))  => begin
                      @match true = strLeft == strRight
                    nil
                  end

                  Absyn.EQ_EQUALS(left, Absyn.BOOL(true))  => begin
                      @shouldFail @match Absyn.CREF(_) = left
                      algItem1 = Absyn.ALGORITHMITEM(Absyn.ALG_NORETCALL(Absyn.CREF_IDENT("fail", nil), Absyn.FUNCTIONARGS(nil, nil)), comment, info)
                      algItem2 = Absyn.ALGORITHMITEM(Absyn.ALG_IF(Absyn.LUNARY(Absyn.NOT(), left), list(algItem1), nil, nil), comment, info)
                    list(algItem2)
                  end

                  Absyn.EQ_EQUALS(left, Absyn.BOOL(false))  => begin
                      @shouldFail @match Absyn.CREF(_) = left
                      algItem1 = Absyn.ALGORITHMITEM(Absyn.ALG_NORETCALL(Absyn.CREF_IDENT("fail", nil), Absyn.FUNCTIONARGS(nil, nil)), comment, info)
                      algItem2 = Absyn.ALGORITHMITEM(Absyn.ALG_IF(left, list(algItem1), nil, nil), comment, info)
                    list(algItem2)
                  end

                  Absyn.EQ_PDE(__)  => begin
                      fail()
                    nil
                  end

                  Absyn.EQ_NORETCALL(Absyn.CREF_IDENT("fail", _), _)  => begin
                      algItem = Absyn.ALGORITHMITEM(Absyn.ALG_NORETCALL(Absyn.CREF_IDENT("fail", nil), Absyn.FUNCTIONARGS(nil, nil)), comment, info)
                    list(algItem)
                  end

                  Absyn.EQ_NORETCALL(cref, fargs)  => begin
                      algItem = Absyn.ALGORITHMITEM(Absyn.ALG_NORETCALL(cref, fargs), comment, info)
                    list(algItem)
                  end

                  Absyn.EQ_EQUALS(left, right)  => begin
                      algItem = Absyn.ALGORITHMITEM(Absyn.ALG_ASSIGN(left, right), comment, info)
                    list(algItem)
                  end

                  Absyn.EQ_FAILURE(Absyn.EQUATIONITEM(eq2, comment2, info2))  => begin
                      algs = fromEquationToAlgAssignment(eq2, comment2, info2)
                      res = Absyn.ALGORITHMITEM(Absyn.ALG_FAILURE(algs), comment, info)
                    list(res)
                  end

                  Absyn.EQ_IF(ifExp = e, equationTrueItems = eqTrueItems, elseIfBranches = eqBranches, equationElseItems = eqElseItems)  => begin
                      algTrueItems = fromEquationsToAlgAssignmentsWork(eqTrueItems)
                      algElseItems = fromEquationsToAlgAssignmentsWork(eqElseItems)
                      algBranches = fromEquationBranchesToAlgBranches(eqBranches)
                      res = Absyn.ALGORITHMITEM(Absyn.ALG_IF(e, algTrueItems, algBranches, algElseItems), comment, info)
                    list(res)
                  end

                  _  => begin
                        str = Dump.equationName(eq)
                        Error.addSourceMessage(Error.META_MATCH_EQUATION_FORBIDDEN, list(str), info)
                      fail()
                  end
                end
              end
               #=  match x case x then ... produces equation x = x; we save a bit of time by removing it here :)
               =#
               #=  The syntax n>=0 = true; is also used
               =#
               #=  If lhs is a CREF, it should be an assignment
               =#
               #=  If lhs is a CREF, it should be an assignment
               =#
          algStatement
        end

         #= Convert an 2-dimensional array expression to a matrix expression. =#
        function elabMatrixToMatrixExp(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local mexpl::List{List{DAE.Exp}}
                  local a::DAE.Type
                  local d1::ModelicaInteger
                  local expl::List{DAE.Exp}
                   #=  Convert a 2-dimensional array to a matrix.
                   =#
                @matchcontinue inExp begin
                  DAE.ARRAY(ty = a && DAE.T_ARRAY(dims = _ <| _ <|  nil()), array = expl)  => begin
                      mexpl = ListUtil.map(expl, Expression.arrayContent)
                      d1 = listLength(mexpl)
                      @match true = Expression.typeBuiltin(Expression.unliftArray(Expression.unliftArray(a)))
                    DAE.MATRIX(a, d1, mexpl)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #=  if fails, skip conversion, use generic array expression as is.
               =#
          outExp
        end

         #= Helper function to elabExp (MATRIX).
          Determines the maximum dimension of the array arguments to the matrix
          constructor as.
          max(2, ndims(A), ndims(B), ndims(C),..) for matrix constructor arguments
          A, B, C, ... =#
        function matrixConstrMaxDim(inTypes::List{<:DAE.Type}) ::ModelicaInteger
              local outMaxDim::ModelicaInteger = 2

              for ty in inTypes
                outMaxDim = max(Types.numberOfDimensions(ty), outMaxDim)
              end
          outMaxDim
        end

         #= This function elaborates reduction expressions that look like function
          calls. For example an array constructor. =#
        function elabCallReduction(inCache::FCore.Cache, inEnv::FCore.Graph, inReductionFn::Absyn.ComponentRef, inReductionExp::Absyn.Exp, inIterType::Absyn.ReductionIterType, inIterators::Absyn.ForIterators, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local env::FCore.Graph
              local fold_env::FCore.Graph
              local reduction_iters::List{DAE.ReductionIterator}
              local dims::List{DAE.Dimension}
              local iter_const::DAE.Const
              local exp_const::DAE.Const
              local c::DAE.Const
              local has_guard_exp::Bool
              local exp::DAE.Exp
              local afold_exp::Option{Absyn.Exp}
              local fold_exp::Option{DAE.Exp}
              local exp_ty::DAE.Type
              local res_ty::DAE.Type
              local fn::Absyn.Path
              local v::Option{Values.Value}
              local fold_id::String
              local res_id::String

              try
                env = FGraphUtil.openScope(inEnv, SCode.NOT_ENCAPSULATED(), FCore.forIterScopeName, NONE())
                (outCache, env, reduction_iters, dims, iter_const, has_guard_exp) = elabCallReductionIterators(inCache, env, listReverse(inIterators), inReductionExp, inImplicit, inDoVect, inPrefix, inInfo)
                dims = fixDimsIterType(inIterType, listReverse(dims))
                @match (outCache, exp, DAE.PROP(exp_ty, exp_const)) = elabExpInExpression(outCache, env, inReductionExp, inImplicit, inDoVect, inPrefix, inInfo)
                c = Types.constAnd(exp_const, iter_const)
                fn = begin
                  @match inReductionFn begin
                    Absyn.CREF_IDENT("\$array",  nil())  => begin
                      Absyn.IDENT("array")
                    end

                    _  => begin
                        AbsynUtil.crefToPath(inReductionFn)
                    end
                  end
                end
                (outCache, exp, exp_ty, res_ty, v, fn) = reductionType(outCache, inEnv, fn, exp, exp_ty, Types.unboxedType(exp_ty), dims, has_guard_exp, inInfo)
                outProperties = DAE.PROP(exp_ty, c)
                fold_id = Util.getTempVariableIndex()
                res_id = Util.getTempVariableIndex()
                (fold_env, afold_exp) = makeReductionFoldExp(env, fn, exp_ty, res_ty, fold_id, res_id)
                (outCache, fold_exp, _) = elabExpOptAndMatchType(outCache, fold_env, afold_exp, res_ty, inImplicit, inDoVect, inPrefix, inInfo)
                outExp = DAE.REDUCTION(DAE.REDUCTIONINFO(fn, inIterType, exp_ty, v, fold_id, res_id, fold_exp), exp, reduction_iters)
              catch
                if listLength(inIterators) > 1
                  Error.addSourceMessage(Error.INTERNAL_ERROR, list("Reductions using multiple iterators is not yet implemented. Try rewriting the expression using nested reductions (e.g. array(i+j for i, j) => array(array(i+j for i) for j)."), inInfo)
                else
                  @match true = Flags.isSet(Flags.FAILTRACE)
                  Debug.traceln("Static.elabCallReduction - failed!")
                end
                fail()
              end
               #=  Elaborate the iterators.
               =#
               #=  Elaborate the expression.
               =#
               #=  Figure out the type of the reduction.
               =#
               #=  Construct the reduction expression.
               =#
          (outCache, outExp, outProperties)
        end

        function fixDimsIterType(iterType::Absyn.ReductionIterType, dims::List{<:DAE.Dimension}) ::List{DAE.Dimension}
              local outDims::List{DAE.Dimension}

              outDims = begin
                @match iterType begin
                  Absyn.COMBINE(__)  => begin
                    dims
                  end

                  _  => begin
                      list(listHead(dims))
                  end
                end
              end
               #=  TODO: Get the best dimension (if several, choose the one that is integer
               =#
               #=  constant; we do run-time checks to assert they are all equal)
               =#
          outDims
        end

        function elabCallReductionIterators(inCache::FCore.Cache, inEnv::FCore.Graph, inIterators::Absyn.ForIterators, inReductionExp::Absyn.Exp, inImpl::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, List{DAE.ReductionIterator}, List{DAE.Dimension}, DAE.Const, Bool}
              local outHasGuard::Bool = false
              local outConst::DAE.Const = DAE.C_CONST()
              local outDims::List{DAE.Dimension} = nil
              local outIterators::List{DAE.ReductionIterator} = nil
              local outIteratorsEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local iter_name::String
              local aiter_exp::Absyn.Exp
              local oaguard_exp::Option{Absyn.Exp}
              local oaiter_exp::Option{Absyn.Exp}
              local iter_exp::DAE.Exp
              local guard_exp::Option{DAE.Exp}
              local full_iter_ty::DAE.Type
              local iter_ty::DAE.Type
              local iter_const::DAE.Const
              local guard_const::DAE.Const
              local c::DAE.Const
              local dim::DAE.Dimension
              local env::FCore.Graph

              for iter in inIterators
                @match Absyn.ITERATOR(iter_name, oaguard_exp, oaiter_exp) = iter
                if isSome(oaiter_exp)
                  @match SOME(aiter_exp) = oaiter_exp
                  @match (outCache, iter_exp, DAE.PROP(full_iter_ty, iter_const)) = elabExpInExpression(outCache, inEnv, aiter_exp, inImpl, inDoVect, inPrefix, inInfo)
                else
                  @match (iter_exp, DAE.PROP(full_iter_ty, iter_const), outCache) = deduceIterationRange(iter_name, AbsynUtil.findIteratorIndexedCrefs(inReductionExp, iter_name), inEnv, outCache, inInfo)
                end
                c = if FGraphUtil.inFunctionScope(inEnv)
                      iter_const
                    else
                      DAE.C_CONST()
                    end
                (outCache, iter_exp, _) = Ceval.cevalIfConstant(outCache, inEnv, iter_exp, DAE.PROP(full_iter_ty, c), inImpl, inInfo)
                (iter_ty, dim) = Types.unliftArrayOrList(full_iter_ty)
                env = FGraphUtil.addForIterator(inEnv, iter_name, iter_ty, DAE.UNBOUND(), SCode.CONST(), SOME(iter_const))
                outIteratorsEnv = FGraphUtil.addForIterator(outIteratorsEnv, iter_name, iter_ty, DAE.UNBOUND(), SCode.CONST(), SOME(iter_const))
                @match (outCache, guard_exp, DAE.PROP(_, guard_const)) = elabExpOptAndMatchType(outCache, env, oaguard_exp, DAE.T_BOOL_DEFAULT, inImpl, inDoVect, inPrefix, inInfo)
                if isSome(guard_exp)
                  outHasGuard = true
                  dim = DAE.DIM_UNKNOWN()
                end
                outConst = Types.constAnd(outConst, Types.constAnd(guard_const, iter_const))
                outIterators = _cons(DAE.REDUCTIONITER(iter_name, iter_exp, guard_exp, iter_ty), outIterators)
                outDims = _cons(dim, outDims)
              end
               #=  An explicit iteration range, elaborate it.
               =#
               #=  An implicit iteration range, try to deduce the range based on how the
               =#
               #=  iterator is used.
               =#
               #=  We need to evaluate the iterator because the rest of the compiler is stupid.
               =#
               #=  The iterator needs to be added to two different environments, to hide the
               =#
               #=  iterators from the different guard-expressions.
               =#
               #=  Elaborate the guard expression.
               =#
               #=  If we have a guard expression we don't determine the dimension, since the
               =#
               #=  number of elements depend on the guard.
               =#
              outIterators = listReverse(outIterators)
              outDims = listReverse(outDims)
          (outCache, outIteratorsEnv, outIterators, outDims, outConst, outHasGuard)
        end

         #= This function tries to deduce the size of an iteration range for a reduction
           based on how an iterator is used. It does this by analysing the reduction
           expression to find out where the iterator is used as a subscript, and uses
           the subscripted components' dimensions to determine the size of the range. =#
        function deduceIterationRange(inIterator::String, inCrefs::List{<:AbsynUtil.IteratorIndexedCref}, inEnv::FCore.Graph, inCache::FCore.Cache, inInfo::Absyn.Info) ::Tuple{DAE.Exp, DAE.Properties, FCore.Cache}
              local outCache::FCore.Cache = inCache
              local outProperties::DAE.Properties
              local outRange::DAE.Exp

              local acref::Absyn.ComponentRef
              local cref::DAE.ComponentRef
              local idx::ModelicaInteger
              local i1::ModelicaInteger
              local i2::ModelicaInteger
              local ty::DAE.Type
              local dims::List{DAE.Dimension}
              local dim::DAE.Dimension
              local range::DAE.Exp
              local ranges::List{DAE.Exp} = nil
              local cr_str1::String
              local cr_str2::String

               #=  Check that we have some crefs, otherwise we print an error and fail.
               =#
              if listLength(inCrefs) < 1
                Error.addSourceMessageAndFail(Error.IMPLICIT_ITERATOR_NOT_FOUND_IN_LOOP_BODY, list(inIterator), inInfo)
              end
               #=  For each cref-index pair, figure out the range of the subscripted dimension.
               =#
              for cr in inCrefs
                (acref, idx) = cr
                cref = ComponentReference.toExpCref(acref)
                try
                  (outCache, _, ty) = Lookup.lookupVar(outCache, inEnv, cref)
                catch
                  Error.addSourceMessageAndFail(Error.LOOKUP_VARIABLE_ERROR, list(Dump.printComponentRefStr(acref), ""), inInfo)
                end
                dims = Types.getDimensions(ty)
                if idx <= listLength(dims)
                  dim = listGet(dims, idx)
                  (range, outProperties) = deduceReductionIterationRange2(dim, cref, ty, idx)
                else
                  range = DAE.ICONST(0)
                  outProperties = DAE.PROP(DAE.T_ARRAY(DAE.T_UNKNOWN_DEFAULT, list(DAE.DIM_INTEGER(0))), DAE.C_UNKNOWN())
                end
                ranges = _cons(range, ranges)
              end
               #=  Look the cref up to get its type.
               =#
               #=  Get the cref's dimensions.
               =#
               #=  Check that the indexed dimension actually exists.
               =#
               #=  Get the indexed dimension and construct a range from it.
               =#
               #=  The indexed dimension doesn't exist, i.e. we have too many subscripts.
               =#
               #=  Return some dummy variables, and let elabCallReduction handle the error
               =#
               #=  reporting since we don't know how many subscripts were used here.
               =#
               #=  If we have more than one range we must check that they are all equal,
               =#
               #=  otherwise it's not possible to determine the actual iteration range.
               =#
               #=  If they are equal we can just return anyone of them.
               =#
              @match outRange <| ranges = ranges
              idx = 2
              for r in ranges
                if ! Expression.expEqual(r, outRange)
                  (acref, i1) = listHead(inCrefs)
                  cr_str1 = Dump.printComponentRefStr(acref)
                  (acref, i2) = listGet(inCrefs, idx)
                  cr_str2 = Dump.printComponentRefStr(acref)
                  Error.addSourceMessageAndFail(Error.INCOMPATIBLE_IMPLICIT_RANGES, list(intString(i2), cr_str2, intString(i1), cr_str1), inInfo)
                end
                idx = idx + 1
              end
          (outRange, outProperties, outCache)
        end

         #= Checks whether two cref-index pairs are equal. =#
        function iteratorIndexedCrefsEqual(inCref1::Tuple{<:Absyn.ComponentRef, ModelicaInteger}, inCref2::Tuple{<:Absyn.ComponentRef, ModelicaInteger}) ::Bool
              local outEqual::Bool

              local cr1::Absyn.ComponentRef
              local cr2::Absyn.ComponentRef
              local idx1::ModelicaInteger
              local idx2::ModelicaInteger

              (cr1, idx1) = inCref1
              (cr2, idx2) = inCref2
              outEqual = idx1 == idx2 && AbsynUtil.crefEqual(cr1, cr2)
          outEqual
        end

         #= Traversal function used by deduceReductionIterationRange. Used to find crefs
           which are subscripted by a given iterator. =#
        function deduceReductionIterationRange_traverser(inExp::Absyn.Exp, inCrefs::List{<:Tuple{<:Absyn.ComponentRef, ModelicaInteger}}, inIterator::String) ::Tuple{Absyn.Exp, List{Tuple{Absyn.ComponentRef, ModelicaInteger}}}
              local outCrefs::List{Tuple{Absyn.ComponentRef, ModelicaInteger}}
              local outExp::Absyn.Exp = inExp

              outCrefs = begin
                  local cref::Absyn.ComponentRef
                @match inExp begin
                  Absyn.CREF(componentRef = cref)  => begin
                    getIteratorIndexedCrefs(cref, inIterator, inCrefs)
                  end

                  _  => begin
                      inCrefs
                  end
                end
              end
          (outExp, outCrefs)
        end

         #= Checks if the given component reference is subscripted by the given iterator.
           Only cases where a subscript consists of only the iterator is considered.
           If so it adds a cref-index pair to the list, where the cref is the subscripted
           cref without subscripts, and the index is the subscripted dimension. E.g. for
           iterator i:
             a[i] => (a, 1), b[1, i] => (b, 2), c[i+1] => (), d[2].e[i] => (d[2].e, 1) =#
        function getIteratorIndexedCrefs(inCref::Absyn.ComponentRef, inIterator::String, inCrefs::List{<:Tuple{<:Absyn.ComponentRef, ModelicaInteger}}) ::List{Tuple{Absyn.ComponentRef, ModelicaInteger}}
              local outCrefs::List{Tuple{Absyn.ComponentRef, ModelicaInteger}} = inCrefs

              local crefs::List{Tuple{Absyn.ComponentRef, ModelicaInteger}}

              outCrefs = begin
                  local subs::List{Absyn.Subscript}
                  local idx::ModelicaInteger
                  local name::String
                  local id::String
                  local cref::Absyn.ComponentRef
                @match inCref begin
                  Absyn.CREF_IDENT(name = id, subscripts = subs)  => begin
                       #=  For each subscript, check if the subscript consists of only the
                       =#
                       #=  iterator we're looking for.
                       =#
                      idx = 1
                      for sub in subs
                        _ = begin
                          @match sub begin
                            Absyn.SUBSCRIPT(subscript = Absyn.CREF(componentRef = Absyn.CREF_IDENT(name = name, subscripts =  nil())))  => begin
                                if name == inIterator
                                  outCrefs = _cons((Absyn.CREF_IDENT(id, nil), idx), outCrefs)
                                end
                              ()
                            end

                            _  => begin
                                ()
                            end
                          end
                        end
                        idx = idx + 1
                      end
                    outCrefs
                  end

                  Absyn.CREF_QUAL(name = id, subscripts = subs, componentRef = cref)  => begin
                      crefs = getIteratorIndexedCrefs(cref, inIterator, nil)
                       #=  Append the prefix from the qualified cref to any matches, and add
                       =#
                       #=  them to the result list.
                       =#
                      for cr in crefs
                        (cref, idx) = cr
                        outCrefs = _cons((Absyn.CREF_QUAL(id, subs, cref), idx), outCrefs)
                      end
                    getIteratorIndexedCrefs(Absyn.CREF_IDENT(id, subs), inIterator, outCrefs)
                  end

                  Absyn.CREF_FULLYQUALIFIED(componentRef = cref)  => begin
                      crefs = getIteratorIndexedCrefs(cref, inIterator, nil)
                       #=  Make any matches fully qualified, and add the to the result list.
                       =#
                      for cr in crefs
                        (cref, idx) = cr
                        outCrefs = _cons((Absyn.CREF_FULLYQUALIFIED(cref), idx), outCrefs)
                      end
                    outCrefs
                  end

                  _  => begin
                      inCrefs
                  end
                end
              end
          outCrefs
        end

         #= Helper function to deduceReductionIterationRange. Constructs a range based on
           the given dimension. =#
        function deduceReductionIterationRange2(inDimension::DAE.Dimension, inCref::DAE.ComponentRef #= The subscripted component without subscripts. =#, inType::DAE.Type #= The type of the subscripted component. =#, inIndex::ModelicaInteger #= The index of the dimension. =#) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties #= The properties of the range expression. =#
              local outRange::DAE.Exp #= The range expression. =#

              local range_ty::DAE.Type
              local range_const::DAE.Const
              local enum_path::Absyn.Path
              local enum_start::Absyn.Path
              local enum_end::Absyn.Path
              local enum_lits::List{String}
              local sz::ModelicaInteger

              outRange = begin
                @match inDimension begin
                  DAE.DIM_BOOLEAN(__)  => begin
                       #=  Boolean dimension => false:true
                       =#
                      range_ty = DAE.T_BOOL_DEFAULT
                      range_const = DAE.C_CONST()
                    DAE.RANGE(range_ty, DAE.BCONST(false), NONE(), DAE.BCONST(true))
                  end

                  DAE.DIM_ENUM(enumTypeName = enum_path, literals = enum_lits)  => begin
                       #=  Enumeration dimension => Enum.first:Enum.last
                       =#
                      enum_start = AbsynUtil.suffixPath(enum_path, listHead(enum_lits))
                      enum_end = AbsynUtil.suffixPath(enum_path, ListUtil.last(enum_lits))
                      range_ty = DAE.T_ENUMERATION(NONE(), enum_path, enum_lits, nil, nil)
                      range_const = DAE.C_CONST()
                    DAE.RANGE(range_ty, DAE.ENUM_LITERAL(enum_start, 1), NONE(), DAE.ENUM_LITERAL(enum_end, listLength(enum_lits)))
                  end

                  DAE.DIM_INTEGER(integer = sz)  => begin
                       #=  Integer dimension => 1:size
                       =#
                      range_ty = DAE.T_INTEGER_DEFAULT
                      range_const = DAE.C_CONST()
                    DAE.RANGE(range_ty, DAE.ICONST(1), NONE(), DAE.ICONST(sz))
                  end

                  _  => begin
                         #=  Any other kind of dimension => 1:size(cref, index)
                         =#
                        range_ty = DAE.T_INTEGER_DEFAULT
                        range_const = DAE.C_PARAM()
                      DAE.RANGE(range_ty, DAE.ICONST(1), NONE(), DAE.SIZE(DAE.CREF(inCref, inType), SOME(DAE.ICONST(inIndex))))
                  end
                end
              end
               #=  Set the properties of the range expression.
               =#
              outProperties = DAE.PROP(DAE.T_ARRAY(range_ty, list(inDimension)), range_const)
          (outRange #= The range expression. =#, outProperties #= The properties of the range expression. =#)
        end

        function makeReductionFoldExp(inEnv::FCore.Graph, path::Absyn.Path, expty::DAE.Type, resultTy::DAE.Type, foldId::String, resultId::String) ::Tuple{FCore.Graph, Option{Absyn.Exp}}
              local afoldExp::Option{Absyn.Exp}
              local outEnv::FCore.Graph

              local func_name::String

              (outEnv, afoldExp) = begin
                  local exp::Absyn.Exp
                  local cr::Absyn.ComponentRef
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                  local env::FCore.Graph
                @match AbsynUtil.makeNotFullyQualified(path) begin
                  Absyn.IDENT("\$array")  => begin
                    (inEnv, NONE())
                  end

                  Absyn.IDENT("array")  => begin
                    (inEnv, NONE())
                  end

                  Absyn.IDENT("list")  => begin
                    (inEnv, NONE())
                  end

                  Absyn.IDENT("listReverse")  => begin
                    (inEnv, NONE())
                  end

                  Absyn.IDENT("sum")  => begin
                      env = FGraphUtil.addForIterator(inEnv, foldId, expty, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                      env = FGraphUtil.addForIterator(env, resultId, expty, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                      cr1 = Absyn.CREF_IDENT(foldId, nil)
                      cr2 = Absyn.CREF_IDENT(resultId, nil)
                      exp = Absyn.BINARY(Absyn.CREF(cr2), Absyn.ADD(), Absyn.CREF(cr1))
                    (env, SOME(exp))
                  end

                  Absyn.IDENT("product")  => begin
                      env = FGraphUtil.addForIterator(inEnv, foldId, expty, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                      env = FGraphUtil.addForIterator(env, resultId, expty, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                      cr1 = Absyn.CREF_IDENT(foldId, nil)
                      cr2 = Absyn.CREF_IDENT(resultId, nil)
                      exp = Absyn.BINARY(Absyn.CREF(cr2), Absyn.MUL(), Absyn.CREF(cr1))
                    (env, SOME(exp))
                  end

                  _  => begin
                        cr = AbsynUtil.pathToCref(path)
                        env = FGraphUtil.addForIterator(inEnv, foldId, expty, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                        env = FGraphUtil.addForIterator(env, resultId, resultTy, DAE.UNBOUND(), SCode.VAR(), SOME(DAE.C_VAR()))
                        cr1 = Absyn.CREF_IDENT(foldId, nil)
                        cr2 = Absyn.CREF_IDENT(resultId, nil)
                        exp = Absyn.CALL(cr, Absyn.FUNCTIONARGS(list(Absyn.CREF(cr1), Absyn.CREF(cr2)), nil))
                      (env, SOME(exp))
                  end
                end
              end
               #=  print(\"makeReductionFoldExp => \" + AbsynUtil.pathString(path) + Types.unparseType(expty) + \"\\n\");
               =#
          (outEnv, afoldExp)
        end

        function reductionType(inCache::FCore.Cache, inEnv::FCore.Graph, inFn::Absyn.Path, inExp::DAE.Exp, inType::DAE.Type, unboxedType::DAE.Type, dims::DAE.Dimensions, hasGuardExp::Bool, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Type, DAE.Type, Option{Values.Value}, Absyn.Path}
              local outPath::Absyn.Path
              local defaultValue::Option{Values.Value}
              local resultType::DAE.Type
              local outType::DAE.Type
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local fn::Absyn.Path = AbsynUtil.makeNotFullyQualified(inFn)

              (outExp, outType, resultType, defaultValue, outPath) = begin
                  local b::Bool
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local fnTypes::List{DAE.Type}
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local typeA::DAE.Type
                  local typeB::DAE.Type
                  local resType::DAE.Type
                  local path::Absyn.Path
                  local v::Values.Value
                  local exp::DAE.Exp
                  local bindings::InstTypes.PolymorphicBindings
                  local defaultBinding::Option{Values.Value}
                @match (fn, unboxedType) begin
                  (Absyn.IDENT(name = "array"), _)  => begin
                      ty = ListUtil.foldr(dims, Types.liftArray, inType)
                    (inExp, ty, ty, SOME(Values.ARRAY(nil, list(0))), fn)
                  end

                  (Absyn.IDENT(name = "\$array"), _)  => begin
                      ty = ListUtil.foldr(dims, Types.liftArray, inType)
                    (inExp, ty, ty, SOME(Values.ARRAY(nil, list(0))), fn)
                  end

                  (Absyn.IDENT(name = "list"), _)  => begin
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_METABOXED_DEFAULT, true)
                      ty = ListUtil.foldr(dims, Types.liftList, ty)
                    (exp, ty, ty, SOME(Values.LIST(nil)), fn)
                  end

                  (Absyn.IDENT(name = "listReverse"), _)  => begin
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_METABOXED_DEFAULT, true)
                      ty = ListUtil.foldr(dims, Types.liftList, ty)
                    (exp, ty, ty, SOME(Values.LIST(nil)), fn)
                  end

                  (Absyn.IDENT("min"), DAE.T_REAL(__))  => begin
                      r = System.realMaxLit()
                      v = Values.REAL(r)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_REAL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("min"), DAE.T_INTEGER(__))  => begin
                      i = System.intMaxLit()
                      v = Values.INTEGER(i)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_INTEGER_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("min"), DAE.T_BOOL(__))  => begin
                      v = Values.BOOL(true)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_BOOL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("min"), DAE.T_STRING(__))  => begin
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_STRING_DEFAULT, true)
                    (exp, ty, ty, NONE(), fn)
                  end

                  (Absyn.IDENT("min"), DAE.T_ENUMERATION(__))  => begin
                      v = Values.ENUM_LITERAL(AbsynUtil.suffixPath(unboxedType.path, ListUtil.last(unboxedType.names)), listLength(unboxedType.names))
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_ENUMERATION_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("max"), DAE.T_REAL(__))  => begin
                      r = realNeg(System.realMaxLit())
                      v = Values.REAL(r)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_REAL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("max"), DAE.T_INTEGER(__))  => begin
                      i = intNeg(System.intMaxLit())
                      v = Values.INTEGER(i)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_INTEGER_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("max"), DAE.T_BOOL(__))  => begin
                      v = Values.BOOL(false)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_BOOL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("max"), DAE.T_STRING(__))  => begin
                      v = Values.STRING("")
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_STRING_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("max"), DAE.T_ENUMERATION(__))  => begin
                      v = Values.ENUM_LITERAL(AbsynUtil.suffixPath(unboxedType.path, listHead(unboxedType.names)), 1)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_ENUMERATION_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("sum"), DAE.T_REAL(__))  => begin
                      v = Values.REAL(0.0)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_REAL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("sum"), DAE.T_INTEGER(__))  => begin
                      v = Values.INTEGER(0)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_INTEGER_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("sum"), DAE.T_BOOL(__))  => begin
                      v = Values.BOOL(false)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_BOOL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("sum"), DAE.T_STRING(__))  => begin
                      v = Values.STRING("")
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_STRING_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("sum"), DAE.T_ARRAY(__))  => begin
                    (inExp, inType, inType, NONE(), fn)
                  end

                  (Absyn.IDENT("product"), DAE.T_REAL(__))  => begin
                      v = Values.REAL(1.0)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_REAL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("product"), DAE.T_INTEGER(__))  => begin
                      v = Values.INTEGER(1)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_INTEGER_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("product"), DAE.T_BOOL(__))  => begin
                      v = Values.BOOL(true)
                      (exp, ty) = Types.matchType(inExp, inType, DAE.T_BOOL_DEFAULT, true)
                    (exp, ty, ty, SOME(v), fn)
                  end

                  (Absyn.IDENT("product"), DAE.T_STRING(__))  => begin
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list("product reduction not defined for String"), info)
                    fail()
                  end

                  (Absyn.IDENT("product"), DAE.T_ARRAY(__))  => begin
                    (inExp, inType, inType, NONE(), fn)
                  end

                  _  => begin
                        (outCache, fnTypes) = Lookup.lookupFunctionsInEnv(inCache, inEnv, inFn, info)
                        (typeA, typeB, resType, defaultBinding, path) = checkReductionType1(inEnv, inFn, fnTypes, info)
                        ty2 = if isSome(defaultBinding)
                              typeB
                            else
                              inType
                            end
                        (exp, typeA, bindings) = Types.matchTypePolymorphicWithError(inExp, inType, typeA, SOME(path), nil, info)
                        (_, typeB, bindings) = Types.matchTypePolymorphicWithError(DAE.CREF(DAE.CREF_IDENT("result", DAE.T_ANYTYPE_DEFAULT, nil), DAE.T_ANYTYPE_DEFAULT), ty2, typeB, SOME(path), bindings, info)
                        bindings = Types.solvePolymorphicBindings(bindings, info, path)
                        typeA = Types.fixPolymorphicRestype(typeA, bindings, info)
                        typeB = Types.fixPolymorphicRestype(typeB, bindings, info)
                        resType = Types.fixPolymorphicRestype(resType, bindings, info)
                        (exp, ty) = checkReductionType2(exp, inType, typeA, typeB, resType, Types.equivtypes(typeA, typeB) || isSome(defaultBinding), Types.equivtypes(typeB, resType), info)
                        @match (outCache, Util.SUCCESS()) = instantiateDaeFunction(outCache, inEnv, path, false, NONE(), true)
                        Error.assertionOrAddSourceMessage(Config.acceptMetaModelicaGrammar() || Flags.isSet(Flags.EXPERIMENTAL_REDUCTIONS), Error.COMPILER_NOTIFICATION, list("Custom reduction functions are an OpenModelica extension to the Modelica Specification. Do not use them if you need your model to compile using other tools or if you are concerned about using experimental features. Use -d=experimentalReductions to disable this message."), info)
                      (exp, ty, typeB, defaultBinding, path)
                  end
                end
              end
          (outCache, outExp, outType, resultType, defaultValue, outPath)
        end

        function checkReductionType1(inEnv::FCore.Graph, inPath::Absyn.Path, fnTypes::List{<:DAE.Type}, info::SourceInfo) ::Tuple{DAE.Type, DAE.Type, DAE.Type, Option{Values.Value}, Absyn.Path}
              local outPath::Absyn.Path
              local startValue::Option{Values.Value}
              local resType::DAE.Type
              local typeB::DAE.Type
              local typeA::DAE.Type

              (typeA, typeB, resType, startValue, outPath) = begin
                  local str1::String
                  local str2::String
                  local path::Absyn.Path
                  local env::FCore.Graph
                  local e::DAE.Exp
                  local v::Values.Value
                @match fnTypes begin
                   nil()  => begin
                      str1 = AbsynUtil.pathString(inPath)
                      str2 = FGraphUtil.printGraphPathStr(inEnv)
                      Error.addSourceMessage(Error.LOOKUP_FUNCTION_ERROR, list(str1, str2), info)
                    fail()
                  end

                  DAE.T_FUNCTION(funcArg = DAE.FUNCARG(ty = typeA, constType = DAE.C_VAR(__)) <| DAE.FUNCARG(ty = typeB, constType = DAE.C_VAR(__), defaultBinding = SOME(e)) <|  nil(), funcResultType = resType, path = path) <|  nil()  => begin
                      v = Ceval.cevalSimple(e)
                    (typeA, typeB, resType, SOME(v), path)
                  end

                  DAE.T_FUNCTION(funcArg = DAE.FUNCARG(ty = typeA, constType = DAE.C_VAR(__)) <| DAE.FUNCARG(ty = typeB, constType = DAE.C_VAR(__), defaultBinding = NONE()) <|  nil(), funcResultType = resType, path = path) <|  nil()  => begin
                    (typeA, typeB, resType, NONE(), path)
                  end

                  _  => begin
                        str1 = stringDelimitList(ListUtil.map(fnTypes, Types.unparseType), ",")
                        Error.addSourceMessage(Error.UNSUPPORTED_REDUCTION_TYPE, list(str1), info)
                      fail()
                  end
                end
              end
          (typeA, typeB, resType, startValue, outPath)
        end

        function checkReductionType2(inExp::DAE.Exp, expType::DAE.Type, typeA::DAE.Type, typeB::DAE.Type, typeC::DAE.Type, equivAB::Bool, equivBC::Bool, info::SourceInfo) ::Tuple{DAE.Exp, DAE.Type}
              local outTy::DAE.Type
              local outExp::DAE.Exp

              (outExp, outTy) = begin
                  local str1::String
                  local str2::String
                  local exp::DAE.Exp
                @match (equivAB, equivBC) begin
                  (true, true)  => begin
                    (inExp, typeA)
                  end

                  (_, false)  => begin
                       #=  (exp,outTy) = Types.matchType(exp,expType,typeA,true);
                       =#
                      str1 = Types.unparseType(typeB)
                      str2 = Types.unparseType(typeC)
                      Error.addSourceMessage(Error.REDUCTION_TYPE_ERROR, list("second argument", "result-type", "identical", str1, str2), info)
                    fail()
                  end

                  (false, true)  => begin
                      str1 = Types.unparseType(typeA)
                      str2 = Types.unparseType(typeB)
                      Error.addSourceMessage(Error.REDUCTION_TYPE_ERROR, list("first", "second arguments", "identical", str1, str2), info)
                    fail()
                  end

                  (true, true)  => begin
                      str1 = Types.unparseType(expType)
                      str2 = Types.unparseType(typeA)
                      Error.addSourceMessage(Error.REDUCTION_TYPE_ERROR, list("reduction expression", "first argument", "compatible", str1, str2), info)
                    fail()
                  end
                end
              end
          (outExp, outTy)
        end

         #= translates an DAE.Const to a SCode.Variability =#
        function constToVariability(constType::DAE.Const) ::SCode.Variability
              local variability::SCode.Variability

              variability = begin
                @match constType begin
                  DAE.C_VAR(__)  => begin
                    SCode.VAR()
                  end

                  DAE.C_PARAM(__)  => begin
                    SCode.PARAM()
                  end

                  DAE.C_CONST(__)  => begin
                    SCode.CONST()
                  end

                  DAE.C_UNKNOWN(__)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Static.constToVariability failed on DAE.C_UNKNOWN()\\n")
                    fail()
                  end
                end
              end
          variability
        end

         #= Helper function for elabCallReduction. Combines the type of the expression in
            an array constructor with the type of the generated array by replacing the
            placeholder T_UNKNOWN in arrayType with expType. Example:
              r[i] for i in 1:5 =>
                arrayType = type(i in 1:5) = (T_ARRAY(DIM(5), T_UNKNOWN),NONE())
                expType = type(r[i]) = (T_REAL,NONE())
              => resType = (T_ARRAY(DIM(5), (T_REAL,NONE())),NONE()) =#
        function constructArrayType(arrayType::DAE.Type, expType::DAE.Type) ::DAE.Type
              local resType::DAE.Type

              resType = begin
                  local ty::DAE.Type
                  local dim::DAE.Dimension
                  local path::Option{Absyn.Path}
                @match arrayType begin
                  DAE.T_UNKNOWN(__)  => begin
                    expType
                  end

                  DAE.T_ARRAY(dims = dim <|  nil(), ty = ty)  => begin
                      ty = constructArrayType(ty, expType)
                    DAE.T_ARRAY(ty, list(dim))
                  end
                end
              end
          resType
        end

         #= This function will construct the correct type for the given Code expression.
           The types are built-in classes of different types. E.g. the class TypeName is
           the type of Code expressions corresponding to a type name Code expression. =#
        function elabCodeType(inCode::Absyn.CodeNode) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inCode begin
                  Absyn.C_TYPENAME(__)  => begin
                    DAE.T_CODE(DAE.C_TYPENAME())
                  end

                  Absyn.C_VARIABLENAME(__)  => begin
                    DAE.T_CODE(DAE.C_VARIABLENAME())
                  end

                  Absyn.C_EQUATIONSECTION(__)  => begin
                    DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("EquationSection")), nil, NONE())
                  end

                  Absyn.C_ALGORITHMSECTION(__)  => begin
                    DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("AlgorithmSection")), nil, NONE())
                  end

                  Absyn.C_ELEMENT(__)  => begin
                    DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("Element")), nil, NONE())
                  end

                  Absyn.C_EXPRESSION(__)  => begin
                    DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("Expression")), nil, NONE())
                  end

                  Absyn.C_MODIFICATION(__)  => begin
                    DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("Modification")), nil, NONE())
                  end
                end
              end
          outType
        end

         #= investigating Modelica 2.0 graphical annotations.
          These have an array of records representing graphical objects. These
          elements can have different types, therefore elab_graphic_exp will allow
          arrays with elements of varying types.  =#
        function elabGraphicsExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local i::ModelicaInteger
                  local l::ModelicaInteger
                  local nmax::ModelicaInteger
                  local r::ModelicaReal
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local b::Bool
                  local impl::Bool
                  local a::Bool
                  local havereal::Bool
                  local s::String
                  local ps::String
                  local dexp::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e_1::DAE.Exp
                  local e3_1::DAE.Exp
                  local start_1::DAE.Exp
                  local stop_1::DAE.Exp
                  local start_2::DAE.Exp
                  local stop_2::DAE.Exp
                  local step_1::DAE.Exp
                  local step_2::DAE.Exp
                  local mexp::DAE.Exp
                  local mexp_1::DAE.Exp
                  local prop::DAE.Properties
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop3::DAE.Properties
                  local env::FCore.Graph
                  local cr::Absyn.ComponentRef
                  local fn::Absyn.ComponentRef
                  local t::DAE.Type
                  local start_t::DAE.Type
                  local stop_t::DAE.Type
                  local step_t::DAE.Type
                  local t_1::DAE.Type
                  local t_2::DAE.Type
                  local c1::DAE.Const
                  local c::DAE.Const
                  local c_start::DAE.Const
                  local c_stop::DAE.Const
                  local constType::DAE.Const
                  local c_step::DAE.Const
                  local e::Absyn.Exp
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                  local e3::Absyn.Exp
                  local start::Absyn.Exp
                  local stop::Absyn.Exp
                  local step::Absyn.Exp
                  local exp::Absyn.Exp
                  local op::Absyn.Operator
                  local args::List{Absyn.Exp}
                  local rest::List{Absyn.Exp}
                  local es::List{Absyn.Exp}
                  local nargs::List{Absyn.NamedArg}
                  local es_1::List{DAE.Exp}
                  local props::List{DAE.Properties}
                  local types::List{DAE.Type}
                  local tps_2::List{DAE.Type}
                  local consts::List{DAE.TupleConst}
                  local rt::DAE.Type
                  local at::DAE.Type
                  local tps::List{List{DAE.Properties}}
                  local tps_1::List{List{DAE.Type}}
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local ess::List{List{Absyn.Exp}}
                  local dess::List{List{DAE.Exp}}
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inPrefix, info) begin
                  (cache, _, Absyn.INTEGER(value = i), _, _, _)  => begin
                    (cache, DAE.ICONST(i), DAE.PROP(DAE.T_INTEGER_DEFAULT, DAE.C_CONST()))
                  end

                  (cache, _, Absyn.REAL(value = s), _, _, _)  => begin
                      r = stringReal(s)
                    (cache, DAE.RCONST(r), DAE.PROP(DAE.T_REAL_DEFAULT, DAE.C_CONST()))
                  end

                  (cache, _, Absyn.STRING(value = s), _, _, _)  => begin
                      s = System.unescapedString(s)
                    (cache, DAE.SCONST(s), DAE.PROP(DAE.T_STRING_DEFAULT, DAE.C_CONST()))
                  end

                  (cache, _, Absyn.BOOL(value = b), _, _, _)  => begin
                    (cache, DAE.BCONST(b), DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_CONST()))
                  end

                  (cache, env, Absyn.CREF(componentRef = cr), impl, pre, _)  => begin
                      @match (cache, SOME((dexp, prop, _))) = elabCref(cache, env, cr, impl, true, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, exp && Absyn.BINARY(exp1 = e1, op = op, exp2 = e2), impl, pre, _)  => begin
                      (cache, e1_1, prop1) = elabGraphicsExp(cache, env, e1, impl, pre, info)
                      (cache, e2_1, prop2) = elabGraphicsExp(cache, env, e2, impl, pre, info)
                      (cache, dexp, prop) = OperatorOverloading.binary(cache, env, op, prop1, e1_1, prop2, e2_1, exp, e1, e2, impl, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, e && Absyn.UNARY(op = Absyn.UPLUS(__)), impl, pre, _)  => begin
                      @match (cache, e_1, DAE.PROP(t, c)) = elabGraphicsExp(cache, env, e, impl, pre, info)
                      @match true = Types.isRealOrSubTypeReal(Types.arrayElementType(t))
                      prop = DAE.PROP(t, c)
                    (cache, e_1, prop)
                  end

                  (cache, env, exp && Absyn.UNARY(op = op, exp = e), impl, pre, _)  => begin
                      (cache, e_1, prop1) = elabGraphicsExp(cache, env, e, impl, pre, info)
                      (cache, dexp, prop) = OperatorOverloading.unary(cache, env, op, prop1, e_1, exp, e, impl, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, exp && Absyn.LBINARY(exp1 = e1, op = op, exp2 = e2), impl, pre, _)  => begin
                      (cache, e1_1, prop1) = elabGraphicsExp(cache, env, e1, impl, pre, info)
                      (cache, e2_1, prop2) = elabGraphicsExp(cache, env, e2, impl, pre, info)
                      (cache, dexp, prop) = OperatorOverloading.binary(cache, env, op, prop1, e1_1, prop2, e2_1, exp, e1, e2, impl, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, exp && Absyn.LUNARY(op = op, exp = e), impl, pre, _)  => begin
                      (cache, e_1, prop1) = elabGraphicsExp(cache, env, e, impl, pre, info)
                      (cache, dexp, prop) = OperatorOverloading.unary(cache, env, op, prop1, e_1, exp, e, impl, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, exp && Absyn.RELATION(exp1 = e1, op = op, exp2 = e2), impl, pre, _)  => begin
                      (cache, e1_1, prop1) = elabGraphicsExp(cache, env, e1, impl, pre, info)
                      (cache, e2_1, prop2) = elabGraphicsExp(cache, env, e2, impl, pre, info)
                      (cache, dexp, prop) = OperatorOverloading.binary(cache, env, op, prop1, e1_1, prop2, e2_1, exp, e1, e2, impl, pre, info)
                    (cache, dexp, prop)
                  end

                  (cache, env, e && Absyn.IFEXP(__), impl, pre, _)  => begin
                      @match Absyn.IFEXP(ifExp = e1, trueBranch = e2, elseBranch = e3) = AbsynUtil.canonIfExp(e)
                      (cache, e1_1, prop1) = elabGraphicsExp(cache, env, e1, impl, pre, info)
                      (cache, e2_1, prop2) = elabGraphicsExp(cache, env, e2, impl, pre, info)
                      (cache, e3_1, prop3) = elabGraphicsExp(cache, env, e3, impl, pre, info)
                      (cache, e_1, prop) = makeIfExp(cache, env, e1_1, prop1, e2_1, prop2, e3_1, prop3, impl, pre, info)
                    (cache, e_1, prop)
                  end

                  (cache, env, Absyn.CALL(function_ = fn, functionArgs = Absyn.FUNCTIONARGS(args = args, argNames = nargs)), _, pre, _)  => begin
                      (cache, e_1, prop) = elabCall(cache, env, fn, args, nargs, true, pre, info)
                    (cache, e_1, prop)
                  end

                  (cache, env, Absyn.TUPLE(expressions = es && _ <| _), impl, pre, _)  => begin
                      (cache, es_1, props) = elabTuple(cache, env, es, impl, false, pre, info, false)
                      (types, consts) = splitProps(props)
                    (cache, DAE.TUPLE(es_1), DAE.PROP_TUPLE(DAE.T_TUPLE(types, NONE()), DAE.TUPLE_CONST(consts)))
                  end

                  (cache, env, Absyn.RANGE(start = start, step = NONE(), stop = stop), impl, pre, _)  => begin
                      @match (cache, start_1, DAE.PROP(start_t, c_start)) = elabGraphicsExp(cache, env, start, impl, pre, info)
                      @match (cache, stop_1, DAE.PROP(stop_t, c_stop)) = elabGraphicsExp(cache, env, stop, impl, pre, info)
                      @match (_, NONE(), _, rt) = deoverloadRange(start_1, start_t, NONE(), NONE(), stop_1, stop_t, info)
                      constType = Types.constAnd(c_start, c_stop)
                      (cache, t) = elabRangeType(cache, env, start_1, NONE(), stop_1, start_t, rt, constType, impl)
                    (cache, DAE.RANGE(rt, start_1, NONE(), stop_1), DAE.PROP(t, constType))
                  end

                  (cache, env, Absyn.RANGE(start = start, step = SOME(step), stop = stop), impl, pre, _)  => begin
                      @match (cache, start_1, DAE.PROP(start_t, c_start)) = elabGraphicsExp(cache, env, start, impl, pre, info) #= fprintln(\\\"setr\\\", \\\"elab_graphics_exp_range2\\\") & =#
                      @match (cache, step_1, DAE.PROP(step_t, c_step)) = elabGraphicsExp(cache, env, step, impl, pre, info)
                      @match (cache, stop_1, DAE.PROP(stop_t, c_stop)) = elabGraphicsExp(cache, env, stop, impl, pre, info)
                      @match (start_2, SOME(step_2), stop_2, rt) = deoverloadRange(start_1, start_t, SOME(step_1), SOME(step_t), stop_1, stop_t, info)
                      c1 = Types.constAnd(c_start, c_step)
                      constType = Types.constAnd(c1, c_stop)
                      (cache, t) = elabRangeType(cache, env, start_1, SOME(step_1), stop_1, start_t, rt, constType, impl)
                    (cache, DAE.RANGE(rt, start_2, SOME(step_2), stop_2), DAE.PROP(t, constType))
                  end

                  (cache, env, Absyn.ARRAY(arrayExp = es), impl, pre, _)  => begin
                      @match (cache, es_1, DAE.PROP(t, constType)) = elabGraphicsArray(cache, env, es, impl, pre, info)
                      l = listLength(es_1)
                      at = Types.simplifyType(t)
                      a = Types.isArray(t)
                    (cache, DAE.ARRAY(at, a, es_1), DAE.PROP(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(l))), constType))
                  end

                  (cache, env, Absyn.MATRIX(matrix = ess), impl, pre, _)  => begin
                      (cache, dess, tps) = elabExpListList(cache, env, ess, impl, true, pre, info)
                      tps_1 = ListUtil.mapList(tps, Types.getPropType)
                      tps_2 = ListUtil.flatten(tps_1)
                      nmax = matrixConstrMaxDim(tps_2)
                      havereal = Types.containReal(tps_2)
                      @match (cache, mexp, DAE.PROP(t, c), dim1, dim2) = elabMatrixSemi(cache, env, dess, tps, impl, havereal, nmax, true, pre, info)
                      _ = elabMatrixToMatrixExp(mexp)
                      t_1 = Types.unliftArray(t)
                      t_2 = Types.unliftArray(t_1)
                    (cache, mexp, DAE.PROP(DAE.T_ARRAY(DAE.T_ARRAY(t_2, list(dim2)), list(dim1)), c))
                  end

                  (_, _, e, _, pre, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Print.printErrorBuf("- Inst.elabGraphicsExp failed: ")
                      ps = PrefixUtil.printPrefixStr2(pre)
                      s = Dump.printExpStr(e)
                      Print.printErrorBuf(ps + s)
                      Print.printErrorBuf("\\n")
                    fail()
                  end
                end
              end
               #= /* impl */ =#
               #=  adrpo: 2010-11-17 this is now fixed!
               =#
               #=  adrpo, if we have useHeatPort, return false.
               =#
               #=  this is a workaround for handling Modelica.Electrical.Analog.Basic.Resistor
               =#
               #=  case (cache,env,Absyn.CREF(componentRef = cr as Absyn.CREF_IDENT(\"useHeatPort\", _)),impl,pre,info)
               =#
               #=    equation
               =#
               #=      dexp  = DAE.BCONST(false);
               =#
               #=      prop = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_CONST());
               =#
               #=    then
               =#
               #=      (cache,dexp,prop);
               =#
               #= /*perform vectorization*/ =#
               #=  Binary and unary operations
               =#
               #=  Logical binary expressions
               =#
               #=  Logical unary expressions
               =#
               #=  Relation expressions
               =#
               #=  Conditional expressions
               =#
               #=  Function calls
               =#
               #=  PR. Get the properties for each expression in the tuple.
               =#
               #=  Each expression has its own constflag.
               =#
               #=  The output from functions does just have one const flag. Fix this!!
               =#
               #=  array-related expressions
               =#
               #=  TODO: Does this do anything?
               =#
          (outCache, outExp, outProperties)
        end

         #= Does deoverloading of range expressions.
          They can be both Integer ranges and Real ranges.
          This function determines which one to use. =#
        function deoverloadRange(inStartExp::DAE.Exp, inStartType::DAE.Type, inStepExp::Option{<:DAE.Exp}, inStepType::Option{<:DAE.Type}, inStopExp::DAE.Exp, inStopType::DAE.Type, inInfo::SourceInfo) ::Tuple{DAE.Exp, Option{DAE.Exp}, DAE.Exp, DAE.Type}
              local outRangeType::DAE.Type
              local outStop::DAE.Exp
              local outStep::Option{DAE.Exp}
              local outStart::DAE.Exp

              (outStart, outStep, outStop, outRangeType) = begin
                  local step_exp::DAE.Exp
                  local step_ty::DAE.Type
                  local et::DAE.Type
                  local ns::List{String}
                  local ne::List{String}
                  local e1_str::String
                  local e2_str::String
                  local t1_str::String
                  local t2_str::String
                   #=  Boolean range has no step value.
                   =#
                @match (inStartType, inStepType, inStopType) begin
                  (DAE.T_BOOL(__), NONE(), DAE.T_BOOL(__))  => begin
                    (inStartExp, NONE(), inStopExp, DAE.T_BOOL_DEFAULT)
                  end

                  (DAE.T_INTEGER(__), NONE(), DAE.T_INTEGER(__))  => begin
                    (inStartExp, inStepExp, inStopExp, DAE.T_INTEGER_DEFAULT)
                  end

                  (DAE.T_INTEGER(__), SOME(DAE.T_INTEGER(__)), DAE.T_INTEGER(__))  => begin
                    (inStartExp, inStepExp, inStopExp, DAE.T_INTEGER_DEFAULT)
                  end

                  (DAE.T_ENUMERATION(names = ns), NONE(), DAE.T_ENUMERATION(names = ne))  => begin
                       #=  Enumeration range has no step value.
                       =#
                       #=  check if enumtype start and end are equal
                       =#
                      if ListUtil.isEqual(ns, ne, true)
                        et = Types.simplifyType(inStartType)
                      else
                        e1_str = ExpressionDump.printExpStr(inStartExp)
                        e2_str = ExpressionDump.printExpStr(inStopExp)
                        t1_str = Types.unparseTypeNoAttr(inStartType)
                        _ = Types.unparseTypeNoAttr(inStopType)
                        Error.addSourceMessageAndFail(Error.UNRESOLVABLE_TYPE, list(e1_str + ":" + e2_str, t1_str + ", " + t1_str, ""), inInfo)
                      end
                       #=  convert vars
                       =#
                       #=  Print an error if the enumerations are different for start and stop.
                       =#
                    (inStartExp, NONE(), inStopExp, et)
                  end

                  (_, NONE(), _)  => begin
                      @match (list(outStart, outStop), _) = OperatorOverloading.elabArglist(list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), list((inStartExp, inStartType), (inStopExp, inStopType)))
                    (outStart, NONE(), outStop, DAE.T_REAL_DEFAULT)
                  end

                  (_, SOME(step_ty), _)  => begin
                      @match SOME(step_exp) = inStepExp
                      @match (list(outStart, step_exp, outStop), _) = OperatorOverloading.elabArglist(list(DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT, DAE.T_REAL_DEFAULT), list((inStartExp, inStartType), (step_exp, step_ty), (inStopExp, inStopType)))
                    (outStart, SOME(step_exp), outStop, DAE.T_REAL_DEFAULT)
                  end
                end
              end
          (outStart, outStep, outStop, outRangeType)
        end

         #= This function creates a type for a range expression given by a start, stop,
          and optional step expression. This function always succeeds, but may return an
          array-type of unknown size if the expressions can't be constant evaluated. =#
        function elabRangeType(inCache::FCore.Cache, inEnv::FCore.Graph, inStart::DAE.Exp, inStep::Option{<:DAE.Exp}, inStop::DAE.Exp, inType::DAE.Type, inExpType::DAE.Type, co::DAE.Const, inImpl::Bool) ::Tuple{FCore.Cache, DAE.Type}
              local outType::DAE.Type
              local outCache::FCore.Cache

              (outCache, outType) = begin
                  local step_exp::DAE.Exp
                  local start_val::Values.Value
                  local step_val::Values.Value
                  local stop_val::Values.Value
                  local dim::ModelicaInteger
                  local cache::FCore.Cache
                @matchcontinue (inStep, co) begin
                  (_, DAE.C_VAR(__))  => begin
                    (inCache, DAE.T_ARRAY(inType, list(DAE.DIM_UNKNOWN())))
                  end

                  (NONE(), _)  => begin
                      (cache, start_val) = Ceval.ceval(inCache, inEnv, inStart, inImpl)
                      (cache, stop_val) = Ceval.ceval(cache, inEnv, inStop, inImpl)
                      dim = elabRangeSize(start_val, NONE(), stop_val)
                    (cache, DAE.T_ARRAY(inType, list(DAE.DIM_INTEGER(dim))))
                  end

                  (SOME(step_exp), _)  => begin
                      (cache, start_val) = Ceval.ceval(inCache, inEnv, inStart, inImpl)
                      (cache, step_val) = Ceval.ceval(cache, inEnv, step_exp, inImpl)
                      (cache, stop_val) = Ceval.ceval(cache, inEnv, inStop, inImpl)
                      dim = elabRangeSize(start_val, SOME(step_val), stop_val)
                    (cache, DAE.T_ARRAY(inType, list(DAE.DIM_INTEGER(dim))))
                  end

                  _  => begin
                      (inCache, DAE.T_ARRAY(inType, list(DAE.DIM_UNKNOWN())))
                  end
                end
              end
               #=  No step value.
               =#
               #=  Some step value.
               =#
               #=  Ceval failed in previous cases, return an array of unknown size.
               =#
          (outCache, outType)
        end

         #= Returns the size of a range, given a start, stop, and optional step value. =#
        function elabRangeSize(inStartValue::Values.Value, inStepValue::Option{<:Values.Value}, inStopValue::Values.Value) ::ModelicaInteger
              local outSize::ModelicaInteger

              outSize = begin
                  local int_start::ModelicaInteger
                  local int_step::ModelicaInteger
                  local int_stop::ModelicaInteger
                  local dim::ModelicaInteger
                  local real_start::ModelicaReal
                  local real_step::ModelicaReal
                  local real_stop::ModelicaReal
                   #=  start:stop where start > stop gives an empty vector.
                   =#
                @matchcontinue (inStartValue, inStepValue, inStopValue) begin
                  (_, NONE(), _)  => begin
                      @match false = ValuesUtil.safeLessEq(inStartValue, inStopValue)
                    0
                  end

                  (Values.INTEGER(int_start), NONE(), Values.INTEGER(int_stop))  => begin
                      dim = int_stop - int_start + 1
                    dim
                  end

                  (Values.INTEGER(int_start), SOME(Values.INTEGER(int_step)), Values.INTEGER(int_stop))  => begin
                      dim = int_stop - int_start
                      dim = intDiv(dim, int_step) + 1
                    dim
                  end

                  (Values.REAL(real_start), NONE(), Values.REAL(real_stop))  => begin
                    Util.realRangeSize(real_start, 1.0, real_stop)
                  end

                  (Values.REAL(real_start), SOME(Values.REAL(real_step)), Values.REAL(real_stop))  => begin
                    Util.realRangeSize(real_start, real_step, real_stop)
                  end

                  (Values.ENUM_LITERAL(index = int_start), NONE(), Values.ENUM_LITERAL(index = int_stop))  => begin
                      dim = int_stop - int_start + 1
                    dim
                  end

                  (Values.BOOL(true), NONE(), Values.BOOL(false))  => begin
                    0
                  end

                  (Values.BOOL(false), NONE(), Values.BOOL(true))  => begin
                    2
                  end

                  (Values.BOOL(_), NONE(), Values.BOOL(_))  => begin
                    1
                  end
                end
              end
               #=  start > stop == not (start <= stop)
               =#
          outSize
        end

         #= This function does elaboration of tuples, i.e. function calls returning several values. =#
        function elabTuple(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:Absyn.Exp}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, isLhs::Bool) ::Tuple{FCore.Cache, List{DAE.Exp}, List{DAE.Properties}}
              local outProperties::List{DAE.Properties} = nil
              local outExpl::List{DAE.Exp} = nil
              local outCache::FCore.Cache = inCache

              local exp::DAE.Exp
              local prop::DAE.Properties

              if if ! isLhs
                    ! Config.acceptMetaModelicaGrammar()
                  else
                    false
                  end
                Error.addSourceMessage(Error.RHS_TUPLE_EXPRESSION, list(Dump.printExpStr(Absyn.TUPLE(inExpl))), inInfo)
                fail()
              end
              for e in inExpl
                (outCache, exp, prop) = elabExp(outCache, inEnv, e, inImplicit, inDoVect, inPrefix, inInfo)
                if AbsynUtil.isTuple(e)
                  (exp, prop) = Types.matchProp(exp, prop, DAE.PROP(DAE.T_METABOXED_DEFAULT, DAE.C_CONST()), true)
                end
                outExpl = _cons(exp, outExpl)
                outProperties = _cons(prop, outProperties)
              end
              outExpl = listReverse(outExpl)
              outProperties = listReverse(outProperties)
          (outCache, outExpl, outProperties)
        end

        function stripExtraArgsFromType(slots::List{<:Slot}, inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type = inType

              outType = begin
                @matchcontinue outType begin
                  DAE.T_FUNCTION(__)  => begin
                      outType.funcArg = stripExtraArgsFromType2(slots, outType.funcArg)
                    outType
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Static.stripExtraArgsFromType failed\\n")
                      fail()
                  end
                end
              end
          outType
        end

        function stripExtraArgsFromType2(inSlots::List{<:Slot}, inType::List{<:DAE.FuncArg}, inAccumType::List{<:DAE.FuncArg} = nil) ::List{DAE.FuncArg}
              local outType::List{DAE.FuncArg}

              outType = begin
                  local slotsRest::List{Slot}
                  local rest::List{DAE.FuncArg}
                  local arg::DAE.FuncArg
                @match (inSlots, inType) begin
                  (SLOT(slotFilled = true) <| slotsRest, _ <| rest)  => begin
                    stripExtraArgsFromType2(slotsRest, rest, inAccumType)
                  end

                  (SLOT(slotFilled = false) <| slotsRest, arg <| rest)  => begin
                    stripExtraArgsFromType2(slotsRest, rest, _cons(arg, inAccumType))
                  end

                  ( nil(),  nil())  => begin
                    listReverse(inAccumType)
                  end
                end
              end
          outType
        end

         #= This function elaborates on array expressions.

           All types of an array should be equivalent. However, mixed Integer and Real
           elements are allowed in an array and in that case the Integer elements are
           converted to Real elements. =#
        function elabArray(inExpl::List{<:DAE.Exp}, inProps::List{<:DAE.Properties}, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{List{DAE.Exp}, DAE.Properties}
              local outProperties::DAE.Properties
              local outExpLst::List{DAE.Exp}

              local types::List{DAE.Type} = nil
              local ty::DAE.Type
              local c::DAE.Const = DAE.C_CONST()
              local c2::DAE.Const
              local mixed::Bool

               #=  Empty array constructors are not allowed in Modelica.
               =#
              if listEmpty(inExpl)
                Error.addSourceMessage(Error.EMPTY_ARRAY, nil, inInfo)
                fail()
              end
               #=  Get the types of all elements, and the array's variability.
               =#
              for p in inProps
                @match DAE.PROP(type_ = ty, constFlag = c2) = p
                types = _cons(ty, types)
                c = Types.constAnd(c, c2)
              end
              types = listReverse(types)
               #=  Check if the array contains a mix of ints and reals.
               =#
              (ty, mixed) = elabArrayHasMixedIntReals(types)
              if mixed
                outExpLst = elabArrayReal2(inExpl, types, ty)
              else
                (outExpLst, ty) = elabArray2(inExpl, types, inPrefix, inInfo)
              end
              outProperties = DAE.PROP(ty, c)
          (outExpLst, outProperties)
        end

         #= Helper function to elabArray. Checks if a list of types contains both
           Integer and Real types, and returns the first Real type if it does. =#
        function elabArrayHasMixedIntReals(inTypes::List{<:DAE.Type}) ::Tuple{DAE.Type, Bool}
              local outIsMixed::Bool = true
              local outType::DAE.Type

              local has_int::Bool = false
              local has_real::Bool = false
              local ty::DAE.Type
              local rest_tys::List{DAE.Type}

              @match outType <| rest_tys = inTypes
               #=  If the first element is a Real, search for an Integer.
               =#
              if Types.isReal(outType)
                while ! listEmpty(rest_tys)
                  @match ty <| rest_tys = rest_tys
                  if Types.isInteger(ty)
                    return (outType, outIsMixed)
                  end
                end
              elseif Types.isInteger(outType)
                while ! listEmpty(rest_tys)
                  @match outType <| rest_tys = rest_tys
                  if Types.isReal(outType)
                    return (outType, outIsMixed)
                  end
                end
              end
               #=  If the first element is an Integer, search for a Real.
               =#
              outIsMixed = false
          (outType, outIsMixed)
        end

         #= Constructs a const value from a list of properties, using constAnd. =#
        function elabArrayConst(inProperties::List{<:DAE.Properties}) ::DAE.Const
              local outConst::DAE.Const = DAE.C_CONST()

              for prop in inProperties
                outConst = Types.constAnd(outConst, Types.getPropConst(prop))
              end
          outConst
        end

         #= Applies type_convert to all expressions in a list to the type given as
           argument. =#
        function elabArrayReal2(inExpl::List{<:DAE.Exp}, inTypes::List{<:DAE.Type}, inExpectedType::DAE.Type) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp} = nil

              local exp::DAE.Exp
              local rest_expl::List{DAE.Exp} = inExpl

              for ty in inTypes
                @match exp <| rest_expl = rest_expl
                if ! Types.equivtypes(ty, inExpectedType)
                  (exp, _) = Types.matchType(exp, ty, inExpectedType, true)
                end
                outExpl = _cons(exp, outExpl)
              end
               #=  If the types are not equivalent, type convert the expression.
               =#
              outExpl = listReverse(outExpl)
          outExpl
        end

         #= Helper function to elabArray, checks that all elements are equivalent. =#
        function elabArray2(inExpl::List{<:DAE.Exp}, inTypes::List{<:DAE.Type}, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{List{DAE.Exp}, DAE.Type}
              local outType::DAE.Type
              local outExpl::List{DAE.Exp}

              local ty2::DAE.Type
              local rest_tys::List{DAE.Type}
              local exp1::DAE.Exp
              local rest_expl::List{DAE.Exp}
              local pre_str::String
              local exp_str::String
              local expl_str::String
              local ty1_str::String
              local ty2_str::String

              @match exp1 <| rest_expl = inExpl
              @match outType <| rest_tys = inTypes
              outExpl = list(exp1)
              outType = Types.getUniontypeIfMetarecordReplaceAllSubtypes(outType)
              for exp2 in rest_expl
                @match ty2 <| rest_tys = rest_tys
                ty2 = Types.getUniontypeIfMetarecordReplaceAllSubtypes(ty2)
                if ! Types.equivtypes(outType, ty2)
                  try
                    (exp2, outType) = Types.matchType(exp2, outType, ty2, false)
                  catch
                    ty1_str = Types.unparseTypeNoAttr(outType)
                    ty2_str = Types.unparseTypeNoAttr(ty2)
                    Types.typeErrorSanityCheck(ty1_str, ty2_str, inInfo)
                    pre_str = PrefixUtil.printPrefixStr(inPrefix)
                    exp_str = ExpressionDump.printExpStr(exp2)
                    expl_str = ListUtil.toString(inExpl, ExpressionDump.printExpStr, "", "[", ",", "]", true)
                    Error.addSourceMessageAndFail(Error.TYPE_MISMATCH_ARRAY_EXP, list(pre_str, exp_str, ty1_str, expl_str, ty2_str), inInfo)
                  end
                end
                outExpl = _cons(exp2, outExpl)
              end
               #=  If the types are not equivalent, try type conversion.
               =#
              outExpl = listReverse(outExpl)
          (outExpl, outType)
        end

         #= This function elaborates array expressions for graphics elaboration. =#
        function elabGraphicsArray(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:Absyn.Exp}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Exp}, DAE.Properties}
              local outProperties::DAE.Properties
              local outExpl::List{DAE.Exp} = nil
              local outCache::FCore.Cache = inCache

              local c::DAE.Const = DAE.C_CONST()
              local c2::DAE.Const
              local exp::DAE.Exp
              local ty::DAE.Type

               #=  Empty array constructors are not allowed in Modelica.
               =#
              if listEmpty(inExpl)
                Error.addSourceMessage(Error.EMPTY_ARRAY, nil, inInfo)
                fail()
              end
              for e in inExpl
                @match (outCache, exp, DAE.PROP(ty, c2)) = elabGraphicsExp(outCache, inEnv, e, inImplicit, inPrefix, inInfo)
                outExpl = _cons(exp, outExpl)
                c = Types.constAnd(c, c2)
              end
              outExpl = listReverse(outExpl)
              outProperties = DAE.PROP(ty, c)
          (outCache, outExpl, outProperties)
        end

         #= This function is a helper function for elabMatrixSemi.
          It elaborates one matrix row of a matrix. =#
        function elabMatrixComma(inExpl::List{<:DAE.Exp}, inProps::List{<:DAE.Properties}, inHaveReal::Bool, inDims::ModelicaInteger, inInfo::SourceInfo) ::Tuple{DAE.Exp, DAE.Properties, DAE.Dimension, DAE.Dimension}
              local outDim2::DAE.Dimension
              local outDim1::DAE.Dimension
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              local exp::DAE.Exp
              local rest_expl::List{DAE.Exp}
              local accum_expl::List{DAE.Exp} = nil
              local prop::DAE.Properties
              local rest_props::List{DAE.Properties}
              local ty::DAE.Type
              local sty::DAE.Type
              local dim1::DAE.Dimension
              local dim2::DAE.Dimension

              try
                @match exp <| rest_expl = inExpl
                @match prop <| rest_props = inProps
                @match (exp, outProperties) = promoteExp(exp, prop, inDims)
                @match DAE.PROP(type_ = ty) = outProperties
                accum_expl = _cons(exp, accum_expl)
                @match outDim1 <| outDim2 <| _ = Types.getDimensions(ty)
                while ! listEmpty(rest_expl)
                  @match exp <| rest_expl = rest_expl
                  @match prop <| rest_props = rest_props
                  @match (exp, prop) = promoteExp(exp, prop, inDims)
                  @match DAE.PROP(type_ = ty) = prop
                  accum_expl = _cons(exp, accum_expl)
                  @match dim1 <| dim2 <| _ = Types.getDimensions(ty)
                  if ! Expression.dimensionsEqual(dim1, outDim1)
                    Error.addSourceMessageAndFail(Error.COMMA_OPERATOR_DIFFERENT_SIZES, list(ExpressionDump.printExpStr(listHead(inExpl)), ExpressionDump.dimensionString(outDim1), ExpressionDump.printExpStr(exp), ExpressionDump.dimensionString(dim1)), inInfo)
                  end
                  outDim2 = Expression.dimensionsAdd(dim2, outDim2)
                  outProperties = Types.matchWithPromote(prop, outProperties, inHaveReal)
                end
                sty = Expression.liftArrayLeftList(Expression.unliftArrayX(ty, 2), list(outDim1, outDim2))
                outExp = DAE.ARRAY(sty, false, listReverse(accum_expl))
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- Static.elabMatrixComma failed")
                fail()
              end
               #=  Comma between matrices => concatenation along second dimension.
               =#
          (outExp, outProperties, outDim1, outDim2)
        end

         #= author: PA
          This function takes an array expression of dimension >=3 and
          concatenates each array element along the second dimension.
          For instance
          elab_matrix_cat_two( {{1,2;5,6}, {3,4;7,8}}) => {1,2,3,4;5,6,7,8} =#
        function elabMatrixCatTwoExp(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local expl::List{DAE.Exp}

              try
                @match DAE.ARRAY(array = expl) = inExp
                expl = ExpressionSimplify.simplifyList(expl)
                expl = list(Expression.matrixToArray(e) for e in expl)
                outExp = elabMatrixCatTwo(expl)
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- Static.elabMatrixCatTwoExp failed")
              end
          outExp
        end

         #= author: PA
          Concatenates a list of matrix(or higher dim) expressions along
          the second dimension. =#
        function elabMatrixCatTwo(inExpl::List{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              local ty::DAE.Type

              try
                outExp = elabMatrixCatTwo2(e for e in listReverse(inExpl))
              catch
                ty = Expression.typeOf(listHead(inExpl))
                outExp = Expression.makePureBuiltinCall("cat", _cons(DAE.ICONST(2), inExpl), ty)
              end
          outExp
        end

         #= Helper function to elabMatrixCatTwo
          Concatenates two array expressions that are matrices (or higher dimension)
          along the first dimension (row). =#
        function elabMatrixCatTwo2(inExp1::DAE.Exp, inExp2::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local expl1::List{DAE.Exp}
              local expl2::List{DAE.Exp}
              local sc::Bool
              local ty::DAE.Type

              @match DAE.ARRAY(scalar = sc, array = expl1) = inExp1
              @match DAE.ARRAY(array = expl2) = inExp2
              expl1 = list(@do_threaded_for elabMatrixCatTwo3(e1, e2) (e1, e2) (expl1, expl2))
              ty = Expression.typeOf(listHead(expl1))
              ty = Expression.liftArrayLeft(ty, DAE.DIM_INTEGER(listLength(expl1)))
              outExp = DAE.ARRAY(ty, sc, expl1)
          outExp
        end

        function elabMatrixCatTwo3(inExp1::DAE.Exp, inExp2::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local ty1::DAE.Type
              local ty2::DAE.Type
              local sc::Bool
              local expl1::List{DAE.Exp}
              local expl2::List{DAE.Exp}

              @match DAE.ARRAY(ty = ty1, scalar = sc, array = expl1) = inExp1
              @match DAE.ARRAY(ty = ty2, array = expl2) = inExp2
              expl2 = listAppend(expl1, expl2)
              ty1 = Expression.concatArrayType(ty1, ty2)
              outExp = DAE.ARRAY(ty1, sc, expl2)
          outExp
        end

         #= author: PA
          Concatenates a list of matrix(or higher dim) expressions along
          the first dimension.
          i.e. elabMatrixCatOne( { {1,2;3,4}, {5,6;7,8} }) => {1,2;3,4;5,6;7,8} =#
        function elabMatrixCatOne(inExpl::List{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              local ty::DAE.Type

              try
                outExp = ListUtil.reduce(inExpl, elabMatrixCatOne2)
              catch
                ty = Expression.typeOf(listHead(inExpl))
                outExp = Expression.makePureBuiltinCall("cat", _cons(DAE.ICONST(1), inExpl), ty)
              end
          outExp
        end

         #= Helper function to elabMatrixCatOne. Concatenates two arrays along the
          first dimension. =#
        function elabMatrixCatOne2(inArray1::DAE.Exp, inArray2::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local ety::DAE.Type
              local at::Bool
              local dim::DAE.Dimension
              local dim1::DAE.Dimension
              local dim2::DAE.Dimension
              local dim_rest::DAE.Dimensions
              local expl::List{DAE.Exp}
              local expl1::List{DAE.Exp}
              local expl2::List{DAE.Exp}

              @match DAE.ARRAY(DAE.T_ARRAY(ety, dim1 <| dim_rest), at, expl1) = inArray1
              @match DAE.ARRAY(ty = DAE.T_ARRAY(dims = dim2 <| _), array = expl2) = inArray2
              expl = listAppend(expl1, expl2)
              dim = Expression.dimensionsAdd(dim1, dim2)
              outExp = DAE.ARRAY(DAE.T_ARRAY(ety, _cons(dim, dim_rest)), at, expl)
          outExp
        end

         #= Wrapper function for Expression.promoteExp which also handles Properties. =#
        function promoteExp(inExp::DAE.Exp, inProperties::DAE.Properties, inDims::ModelicaInteger) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              local ty::DAE.Type
              local c::DAE.Const

              try
                @match DAE.PROP(ty, c) = inProperties
                (outExp, ty) = Expression.promoteExp(inExp, ty, inDims)
                outProperties = DAE.PROP(ty, c)
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- Static.promoteExp failed")
              end
          (outExp, outProperties)
        end

         #= This function elaborates Matrix expressions, e.g. {1,0;2,1}
          A row is elaborated with elabMatrixComma. =#
        function elabMatrixSemi(inCache::FCore.Cache, inEnv::FCore.Graph, inMatrix::List{<:List{<:DAE.Exp}}, inProperties::List{<:List{<:DAE.Properties}}, inImpl::Bool, inHaveReal::Bool, inDims::ModelicaInteger, inDoVectorization::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties, DAE.Dimension, DAE.Dimension}
              local outDim2::DAE.Dimension
              local outDim1::DAE.Dimension
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local expl::List{DAE.Exp}
              local rest_expl::List{List{DAE.Exp}}
              local props::List{DAE.Properties}
              local rest_props::List{List{DAE.Properties}}
              local exp::DAE.Exp
              local prop::DAE.Properties
              local dim1::DAE.Dimension
              local dim2::DAE.Dimension
              local dim1_str::String
              local dim2_str::String
              local pre_str::String
              local el_str::String
              local ty1_str::String
              local ty2_str::String

               #=  Elaborate the first row so we have something to compare against.
               =#
              @match expl <| rest_expl = inMatrix
              @match props <| rest_props = inProperties
              (outExp, outProperties, outDim1, outDim2) = elabMatrixComma(expl, props, inHaveReal, inDims, inInfo)
              outExp = elabMatrixCatTwoExp(outExp)
               #=  Elaborate the rest of the rows (if any).
               =#
              while ! listEmpty(rest_expl)
                @match expl <| rest_expl = rest_expl
                @match props <| rest_props = rest_props
                (exp, prop, dim1, dim2) = elabMatrixComma(expl, props, inHaveReal, inDims, inInfo)
                if ! Expression.dimensionsEqual(dim2, outDim2)
                  dim1_str = ExpressionDump.dimensionString(dim1)
                  dim2_str = ExpressionDump.dimensionString(dim2)
                  pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                  el_str = ListUtil.toString(expl, ExpressionDump.printExpStr, "", "{", ", ", "}", true)
                  Error.addSourceMessageAndFail(Error.MATRIX_EXP_ROW_SIZE, list(pre_str, el_str, dim1_str, dim2_str), inInfo)
                end
                try
                  outProperties = Types.matchWithPromote(outProperties, prop, inHaveReal)
                catch
                  ty1_str = Types.unparsePropTypeNoAttr(outProperties)
                  ty2_str = Types.unparsePropTypeNoAttr(prop)
                  Types.typeErrorSanityCheck(ty1_str, ty2_str, inInfo)
                  pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                  el_str = ListUtil.toString(expl, ExpressionDump.printExpStr, "", "{", ", ", "}", true)
                  Error.addSourceMessageAndFail(Error.TYPE_MISMATCH_MATRIX_EXP, list(pre_str, el_str, ty1_str, ty2_str), inInfo)
                end
                exp = elabMatrixCatTwoExp(exp)
                outExp = elabMatrixCatOne(list(outExp, exp))
                outDim1 = Expression.dimensionsAdd(dim1, outDim1)
              end
               #=  Check that all rows have the same size, otherwise print an error and fail.
               =#
               #=  Check that all rows are of the same type, otherwise print an error and fail.
               =#
               #=  Add the row to the matrix.
               =#
          (outCache, outExp, outProperties, outDim1, outDim2)
        end

         #=
         Author BZ, 2009-02
          This function validates that arguments to function are of a correct type.
          Then call elabCallArgs to vectorize/type-match. =#
        function verifyBuiltInHandlerType(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:Absyn.Exp}, inImplicit::Bool, inTypeChecker::extraFunc, inFnName::String, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local ty::DAE.Type

              @match list(e) = inExpl
              (outCache, _, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              ty = Types.getPropType(outProperties)
              ty = Types.arrayElementType(ty)
              @match true = inTypeChecker(ty)
              @match (outCache, outExp, (@match DAE.PROP() = outProperties)) = elabCallArgs(outCache, inEnv, Absyn.FULLYQUALIFIED(Absyn.IDENT(inFnName)), list(e), nil, inImplicit, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= author: PA
          This function elaborates the cardinality operator. =#
        function elabBuiltinCardinality(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type
              local e::Absyn.Exp

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "cardinality", inInfo)
              @match list(e) = inPosArgs
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(type_ = ty) = outProperties
              ty = Types.liftArrayListDims(DAE.T_INTEGER_DEFAULT, Types.getDimensions(ty))
              outExp = Expression.makePureBuiltinCall("cardinality", list(outExp), ty)
              outProperties = DAE.PROP(ty, DAE.C_CONST())
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the smooth operator.
          smooth(p,expr) - If p>=0 smooth(p, expr) returns expr and states that expr is p times
          continuously differentiable, i.e.: expr is continuous in all real variables appearing in
          the expression and all partial derivatives with respect to all appearing real variables
          exist and are continuous up to order p.
          The only allowed types for expr in smooth are: real expressions, arrays of
          allowed expressions, and records containing only components of allowed
          expressions. =#
        function elabBuiltinSmooth(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local msg_str::String
              local p::Absyn.Exp
              local expr::Absyn.Exp
              local dp::DAE.Exp
              local dexpr::DAE.Exp
              local ty::DAE.Type
              local c::DAE.Const

              if listLength(inPosArgs) != 2 || ! listEmpty(inNamedArgs)
                msg_str = ", expected smooth(p, expr)"
                printBuiltinFnArgError("smooth", msg_str, inPosArgs, inNamedArgs, inPrefix, inInfo)
              end
              @match list(p, expr) = inPosArgs
              @match (outCache, dp, DAE.PROP(ty, c)) = elabExpInExpression(inCache, inEnv, p, inImplicit, true, inPrefix, inInfo)
              if ! Types.isParameterOrConstant(c) || ! Types.isInteger(ty)
                msg_str = ", first argument must be a constant or parameter expression of type Integer"
                printBuiltinFnArgError("smooth", msg_str, inPosArgs, inNamedArgs, inPrefix, inInfo)
              end
              @match (outCache, dexpr, (@match DAE.PROP(ty, c) = outProperties)) = elabExpInExpression(outCache, inEnv, expr, inImplicit, true, inPrefix, inInfo)
              if ! (Types.isReal(ty) || Types.isRecordWithOnlyReals(ty))
                msg_str = ", second argument must be a Real, array of Reals or record only containing Reals"
                printBuiltinFnArgError("smooth", msg_str, inPosArgs, inNamedArgs, inPrefix, inInfo)
              end
              ty = Types.simplifyType(ty)
              outExp = Expression.makePureBuiltinCall("smooth", list(dp, dexpr), ty)
          (outCache, outExp, outProperties)
        end

        function printBuiltinFnArgError(inFnName::String, inMsg::String, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inPrefix::Prefix.PrefixType, inInfo::SourceInfo)
              local args_str::String
              local pre_str::String
              local msg_str::String
              local pos_args::List{String}
              local named_args::List{String}

              pos_args = list(Dump.printExpStr(arg) for arg in inPosArgs)
              named_args = list(Dump.printNamedArgStr(arg) for arg in inNamedArgs)
              args_str = stringDelimitList(listAppend(pos_args, named_args), ", ")
              pre_str = PrefixUtil.printPrefixStr3(inPrefix)
              msg_str = inFnName + "(" + args_str + ")" + inMsg
              Error.addSourceMessageAndFail(Error.WRONG_TYPE_OR_NO_OF_ARGS, list(msg_str, pre_str), inInfo)
        end

         #= This function elaborates the size operator.
          Input is the list of arguments to size as Absyn.Exp
          expressions and the environment, FCore.Graph. =#
        function elabBuiltinSize(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local dimp::DAE.Exp
                  local arraycrefe::DAE.Exp
                  local exp::DAE.Exp
                  local arrtp::DAE.Type
                  local prop::DAE.Properties
                  local impl::Bool
                  local env::FCore.Graph
                  local arraycr::Absyn.Exp
                  local dim::Absyn.Exp
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local ety::DAE.Type
                  local dims::DAE.Dimensions
                  local dims1::DAE.Dimensions
                  local dims2::DAE.Dimensions
                @match (inCache, inEnv, inAbsynExpLst, inBoolean, inPrefix) begin
                  (cache, env, arraycr <| dim <|  nil(), impl, pre)  => begin
                      (cache, dimp, _) = elabExpInExpression(cache, env, dim, impl, true, pre, info)
                      (cache, arraycrefe, prop) = elabExpInExpression(cache, env, arraycr, impl, false, pre, info)
                      ety = Expression.typeOf(arraycrefe)
                      dims1 = Expression.arrayDimension(ety)
                      (_, dims2) = Types.flattenArrayType(Types.getPropType(prop))
                      dims = if listLength(dims1) >= listLength(dims2)
                            dims1
                          else
                            dims2
                          end #= In case there is a zero-size array somewhere... =#
                      @match (SOME(exp), SOME(prop)) = elabBuiltinSizeIndex(arraycrefe, prop, ety, dimp, dims, env, info)
                    (cache, exp, prop)
                  end

                  (cache, env, arraycr <|  nil(), impl, pre)  => begin
                      @match (cache, arraycrefe, DAE.PROP(arrtp, _)) = elabExpInExpression(cache, env, arraycr, impl, false, pre, info)
                      ety = Expression.typeOf(arraycrefe)
                      dims = Expression.arrayDimension(ety)
                      (exp, prop) = elabBuiltinSizeNoIndex(arraycrefe, ety, dims, arrtp, info)
                    (cache, exp, prop)
                  end
                end
              end
               #=  sent in the props of the arraycrefe as if the array is constant then the size(x, 1) is constant!
               =#
               #=  see Modelica.Media.Incompressible.Examples.Glycol47 and Modelica.Media.Incompressible.TableBased (hasDensity)
               =#
          (outCache, outExp, outProperties)
        end

         #= Helper function to elabBuiltinSize. Elaborates the size(A) operator. =#
        function elabBuiltinSizeNoIndex(inArrayExp::DAE.Exp, inArrayExpType::DAE.Type, inDimensions::DAE.Dimensions, inArrayType::DAE.Type, inInfo::SourceInfo) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outSizeExp::DAE.Exp

              (outSizeExp, outProperties) = begin
                  local dim_expl::List{DAE.Exp}
                  local dim_int::ModelicaInteger
                  local exp::DAE.Exp
                  local prop::DAE.Properties
                  local b::Bool
                  local cnst::DAE.Const
                  local ty::DAE.Type
                  local exp_str::String
                  local size_str::String
                   #=  size of a scalar is not allowed.
                   =#
                @matchcontinue inDimensions begin
                   nil()  => begin
                      @match false = Types.isUnknownType(inArrayExpType)
                      exp_str = ExpressionDump.printExpStr(inArrayExp)
                      size_str = "size(" + exp_str + ")"
                      Error.addSourceMessage(Error.INVALID_ARGUMENT_TYPE_FIRST_ARRAY, list(size_str), inInfo)
                    fail()
                  end

                  _ <| _  => begin
                      dim_expl = ListUtil.map(inDimensions, Expression.dimensionSizeExp)
                      dim_int = listLength(dim_expl)
                      ty = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(dim_int)))
                      exp = DAE.ARRAY(ty, true, dim_expl)
                      prop = DAE.PROP(ty, DAE.C_CONST())
                    (exp, prop)
                  end

                  _ <| _  => begin
                      b = Types.dimensionsKnown(inArrayType)
                      cnst = Types.boolConstSize(b)
                      exp = DAE.SIZE(inArrayExp, NONE())
                      ty = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN()))
                      prop = DAE.PROP(ty, cnst)
                    (exp, prop)
                  end
                end
              end
               #=  Make sure that we have a proper type here. We might get DAE.T_UNKNOWN if
               =#
               #=  the size expression is part of a modifier, in which case we can't
               =#
               #=  determine if it's a scalar or array.
               =#
               #=  size(A) for an array A with known dimensions.
               =#
               #=  Returns an array of all dimensions of A.
               =#
               #=  If we couldn't evaluate the size expression or find any problems with it,
               =#
               #=  just generate a call to size and let the runtime sort it out.
               =#
          (outSizeExp, outProperties)
        end

         #= Helper function to elabBuiltinSize. Elaborates the size(A, x) operator. =#
        function elabBuiltinSizeIndex(inArrayExp::DAE.Exp, inArrayProp::DAE.Properties, inArrayType::DAE.Type, inIndexExp::DAE.Exp, inDimensions::DAE.Dimensions, inEnv::FCore.Graph, inInfo::SourceInfo) ::Tuple{Option{DAE.Exp}, Option{DAE.Properties}}
              local outProperties::Option{DAE.Properties}
              local outSizeExp::Option{DAE.Exp}

              (outSizeExp, outProperties) = begin
                  local dim_int::ModelicaInteger
                  local dim_count::ModelicaInteger
                  local exp::DAE.Exp
                  local dim::DAE.Dimension
                  local prop::DAE.Properties
                  local cnst::DAE.Const
                  local exp_str::String
                  local index_str::String
                  local size_str::String
                  local dim_str::String
                   #=  size of a scalar is not allowed.
                   =#
                @matchcontinue inDimensions begin
                   nil()  => begin
                      @match false = Types.isUnknownType(inArrayType)
                      exp_str = ExpressionDump.printExpStr(inArrayExp)
                      index_str = ExpressionDump.printExpStr(inIndexExp)
                      size_str = "size(" + exp_str + ", " + index_str + ")"
                      Error.addSourceMessage(Error.INVALID_ARGUMENT_TYPE_FIRST_ARRAY, list(size_str), inInfo)
                    (NONE(), NONE())
                  end

                  _  => begin
                      dim_int = Expression.expInt(inIndexExp)
                      dim_count = listLength(inDimensions)
                      @match true = dim_int > 0 && dim_int <= dim_count
                      dim = listGet(inDimensions, dim_int)
                      exp = Expression.dimensionSizeConstantExp(dim)
                      prop = DAE.PROP(DAE.T_INTEGER_DEFAULT, DAE.C_CONST())
                    (SOME(exp), SOME(prop))
                  end

                  _  => begin
                      @match false = Types.isUnknownType(inArrayType)
                      dim_int = Expression.expInt(inIndexExp)
                      dim_count = listLength(inDimensions)
                      @match true = dim_int <= 0 || dim_int > dim_count
                      index_str = intString(dim_int)
                      exp_str = ExpressionDump.printExpStr(inArrayExp)
                      dim_str = intString(dim_count)
                      Error.addSourceMessage(Error.INVALID_SIZE_INDEX, list(index_str, exp_str, dim_str), inInfo)
                    (NONE(), NONE())
                  end

                  _  => begin
                        exp = DAE.SIZE(inArrayExp, SOME(inIndexExp))
                        cnst = DAE.C_PARAM()
                        cnst = if FGraphUtil.inFunctionScope(inEnv)
                              DAE.C_VAR()
                            else
                              cnst
                            end
                        prop = DAE.PROP(DAE.T_INTEGER_DEFAULT, cnst)
                      (SOME(exp), SOME(prop))
                  end
                end
              end
               #=  Make sure that we have a proper type here. We might get T_UNKNOWN if
               =#
               #=  the size expression is part of a modifier, in which case we can't
               =#
               #=  determine if it's a scalar or array.
               =#
               #=  size(A, x) for an array A with known dimensions and constant x.
               =#
               #=  Returns the size of the x:th dimension.
               =#
               #=  The index is out of bounds.
               =#
               #=  If we couldn't evaluate the size expression or find any problems with it,
               =#
               #=  just generate a call to size and let the runtime sort it out.
               =#
               #=  Types.getPropConst(inArrayProp);
               =#
          (outSizeExp, outProperties)
        end

         #= @author Stefan Vorkoetter <svorkoetter@maplesoft.com>
         ndims(A) : Returns the number of dimensions k of array expression A, with k >= 0.
         =#
        function elabBuiltinNDims(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local arraycrefe::DAE.Exp
                  local exp::DAE.Exp
                  local arrtp::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local arraycr::Absyn.Exp
                  local cache::FCore.Cache
                  local expl::List{Absyn.Exp}
                  local nd::ModelicaInteger
                  local pre::Prefix.PrefixType
                  local sp::String
                @matchcontinue (inCache, inEnv, inAbsynExpLst, inNamedArg, inBoolean, inPrefix, info) begin
                  (cache, env, arraycr <|  nil(), _, impl, pre, _)  => begin
                      @match (cache, _, DAE.PROP(arrtp, _)) = elabExpInExpression(cache, env, arraycr, impl, true, pre, info)
                      nd = Types.numberOfDimensions(arrtp)
                      exp = DAE.ICONST(nd)
                    (cache, exp, DAE.PROP(DAE.T_INTEGER_DEFAULT, DAE.C_CONST()))
                  end

                  (_, _, expl, _, _, pre, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      sp = PrefixUtil.printPrefixStr3(pre)
                      Debug.traceln("- Static.elabBuiltinNdims failed for: ndims(" + Dump.printExpLstStr(expl) + " in component: " + sp)
                    fail()
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator fill.
          The input is the arguments to fill as Absyn.Exp expressions and the environment FCore.Graph =#
        function elabBuiltinFill(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local s_1::DAE.Exp
                  local exp::DAE.Exp
                  local prop::DAE.Properties
                  local dims_1::List{DAE.Exp}
                  local dimprops::List{DAE.Properties}
                  local sty::DAE.Type
                  local dimvals::List{Values.Value}
                  local env::FCore.Graph
                  local s::Absyn.Exp
                  local dims::List{Absyn.Exp}
                  local impl::Bool
                  local implstr::String
                  local expstr::String
                  local str::String
                  local sp::String
                  local expstrs::List{String}
                  local cache::FCore.Cache
                  local c1::DAE.Const
                  local pre::Prefix.PrefixType
                  local exp_type::DAE.Type
                   #=  try to constant evaluate dimensions
                   =#
                @matchcontinue (inCache, inEnv, inAbsynExpLst, inNamedArg, inBoolean, inPrefix, info) begin
                  (cache, env, s <| dims, _, impl, pre, _)  => begin
                      (cache, s_1, prop) = elabExpInExpression(cache, env, s, impl, true, pre, info)
                      (cache, dims_1, dimprops) = elabExpList(cache, env, dims, impl, true, pre, info)
                      (dims_1, _) = Types.matchTypes(dims_1, ListUtil.map(dimprops, Types.getPropType), DAE.T_INTEGER_DEFAULT, false)
                      c1 = Types.propertiesListToConst(dimprops)
                      @shouldFail @match DAE.C_VAR() = c1
                      c1 = Types.constAnd(c1, Types.propAllConst(prop))
                      sty = Types.getPropType(prop)
                      (cache, dimvals) = Ceval.cevalList(cache, env, dims_1, impl, Absyn.NO_MSG(), 0)
                      (cache, exp, prop) = elabBuiltinFill2(cache, env, s_1, sty, dimvals, c1, pre, dims, info)
                    (cache, exp, prop)
                  end

                  (cache, env, s <| dims, _, impl, pre, _)  => begin
                      c1 = unevaluatedFunctionVariability(env)
                      (cache, s_1, prop) = elabExpInExpression(cache, env, s, impl, true, pre, info)
                      (cache, dims_1, dimprops) = elabExpList(cache, env, dims, impl, true, pre, info)
                      (dims_1, _) = Types.matchTypes(dims_1, ListUtil.map(dimprops, Types.getPropType), DAE.T_INTEGER_DEFAULT, false)
                      sty = Types.getPropType(prop)
                      sty = Types.liftArrayListExp(sty, dims_1)
                      exp_type = Types.simplifyType(sty)
                      prop = DAE.PROP(sty, c1)
                      exp = Expression.makePureBuiltinCall("fill", _cons(s_1, dims_1), exp_type)
                    (cache, exp, prop)
                  end

                  (cache, env, s <| dims, _, impl, pre, _)  => begin
                      @match false = Config.splitArrays()
                      @match (cache, s_1, DAE.PROP(sty, c1)) = elabExpInExpression(cache, env, s, impl, true, pre, info)
                      (cache, dims_1, _) = elabExpList(cache, env, dims, impl, true, pre, info)
                      sty = Types.liftArrayListExp(sty, dims_1)
                      exp_type = Types.simplifyType(sty)
                      c1 = Types.constAnd(c1, DAE.C_PARAM())
                      prop = DAE.PROP(sty, c1)
                      exp = Expression.makePureBuiltinCall("fill", _cons(s_1, dims_1), exp_type)
                    (cache, exp, prop)
                  end

                  (_, env, dims, _, _, _, _)  => begin
                      str = "Static.elabBuiltinFill failed in component" + PrefixUtil.printPrefixStr3(inPrefix) + " and scope: " + FGraphUtil.printGraphPathStr(env) + " for expression: fill(" + Dump.printExpLstStr(dims) + ")"
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), info)
                    fail()
                  end

                  (_, _, dims, _, impl, pre, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Static.elabBuiltinFill: Couldn't elaborate fill(): ")
                      implstr = boolString(impl)
                      expstrs = ListUtil.map(dims, Dump.printExpStr)
                      expstr = stringDelimitList(expstrs, ", ")
                      sp = PrefixUtil.printPrefixStr3(pre)
                      str = stringAppendList(list(expstr, " impl=", implstr, ", in component: ", sp))
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
               #=  If the previous case failed we probably couldn't constant evaluate the
               =#
               #=  dimensions. Create a function call to fill instead, and let the compiler sort it out later.
               =#
               #=  Non-constant dimensons are also allowed in the case of non-expanded arrays
               =#
               #=  TODO: check that the diemnsions are parametric?
               =#
          (outCache, outExp, outProperties)
        end

         #=
          function: elabBuiltinFill2
          Helper function to: elabBuiltinFill

          Public since it is used by ExpressionSimplify.simplifyBuiltinCalls.
         =#
        function elabBuiltinFill2(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inType::DAE.Type, inValuesValueLst::List{<:Values.Value}, constVar::DAE.Const, inPrefix::Prefix.PrefixType, inDims::List{<:Absyn.Exp}, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local arraylist::List{DAE.Exp}
                  local at::DAE.Type
                  local a::Bool
                  local env::FCore.Graph
                  local s::DAE.Exp
                  local exp::DAE.Exp
                  local sty::DAE.Type
                  local ty::DAE.Type
                  local sty2::DAE.Type
                  local v::ModelicaInteger
                  local con::DAE.Const
                  local rest::List{Values.Value}
                  local cache::FCore.Cache
                  local c1::DAE.Const
                  local pre::Prefix.PrefixType
                  local str::String
                   #=  we might get here negative integers!
                   =#
                @matchcontinue (inCache, inEnv, inExp, inType, inValuesValueLst, constVar, inPrefix, inDims, inInfo) begin
                  (cache, _, s, sty, Values.INTEGER(integer = v) <|  nil(), c1, _, _, _)  => begin
                      @match true = intLt(v, 0)
                      v = 0
                      arraylist = ListUtil.fill(s, v)
                      sty2 = DAE.T_ARRAY(sty, list(DAE.DIM_INTEGER(v)))
                      at = Types.simplifyType(sty2)
                      a = Types.isArray(sty2)
                    (cache, DAE.ARRAY(at, a, arraylist), DAE.PROP(sty2, c1))
                  end

                  (cache, _, s, sty, Values.INTEGER(integer = v) <|  nil(), c1, _, _, _)  => begin
                      arraylist = ListUtil.fill(s, v)
                      sty2 = DAE.T_ARRAY(sty, list(DAE.DIM_INTEGER(v)))
                      at = Types.simplifyType(sty2)
                      a = Types.isArray(sty2)
                    (cache, DAE.ARRAY(at, a, arraylist), DAE.PROP(sty2, c1))
                  end

                  (cache, env, s, sty, Values.INTEGER(integer = v) <| rest, c1, pre, _, _)  => begin
                      @match (cache, exp, DAE.PROP(ty, _)) = elabBuiltinFill2(cache, env, s, sty, rest, c1, pre, inDims, inInfo)
                      arraylist = ListUtil.fill(exp, v)
                      sty2 = DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(v)))
                      at = Types.simplifyType(sty2)
                      a = Types.isArray(sty2)
                    (cache, DAE.ARRAY(at, a, arraylist), DAE.PROP(sty2, c1))
                  end

                  _  => begin
                        str = "Static.elabBuiltinFill2 failed in component" + PrefixUtil.printPrefixStr3(inPrefix) + " and scope: " + FGraphUtil.printGraphPathStr(inEnv) + " for expression: fill(" + Dump.printExpLstStr(inDims) + ")"
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), inInfo)
                      fail()
                  end
                end
              end
               #=  fill with 0 then!
               =#
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator symmetric =#
        function elabBuiltinSymmetric(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local tp::DAE.Type
                  local impl::Bool
                  local d1::DAE.Dimension
                  local d2::DAE.Dimension
                  local eltp::DAE.Type
                  local newtp::DAE.Type
                  local prop::DAE.Properties
                  local c::DAE.Const
                  local env::FCore.Graph
                  local matexp::Absyn.Exp
                  local exp_1::DAE.Exp
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                @match (inCache, inEnv, inAbsynExpLst, inNamedArg, inBoolean, inPrefix, info) begin
                  (cache, env, matexp <|  nil(), _, impl, pre, _)  => begin
                      @match (cache, exp_1, DAE.PROP(DAE.T_ARRAY(dims = list(d1), ty = DAE.T_ARRAY(dims = list(d2), ty = eltp)), c)) = elabExpInExpression(cache, env, matexp, impl, true, pre, info)
                      newtp = DAE.T_ARRAY(DAE.T_ARRAY(eltp, list(d1)), list(d2))
                      tp = Types.simplifyType(newtp)
                      exp = Expression.makePureBuiltinCall("symmetric", list(exp_1), tp)
                      prop = DAE.PROP(newtp, c)
                    (cache, exp, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinClassDirectory(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local str::String
                  local fileName::String
                @match info begin
                  SOURCEINFO(fileName = fileName)  => begin
                      str = stringAppend(System.dirname(fileName), "/")
                      Error.addSourceMessage(Error.NON_STANDARD_OPERATOR_CLASS_DIRECTORY, nil, info)
                    (inCache, DAE.SCONST(str), DAE.PROP(DAE.T_STRING_DEFAULT, DAE.C_CONST()))
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinSourceInfo(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              @match nil = inAbsynExpLst
              (outCache, outExp, outProperties) = begin
                  local args::List{DAE.Exp}
                @match info begin
                  SOURCEINFO(__)  => begin
                      args = list(DAE.SCONST(info.fileName), DAE.BCONST(info.isReadOnly), DAE.ICONST(info.lineNumberStart), DAE.ICONST(info.columnNumberStart), DAE.ICONST(info.lineNumberEnd), DAE.ICONST(info.columnNumberEnd), DAE.RCONST(info.lastModification))
                      outExp = DAE.METARECORDCALL(Absyn.QUALIFIED("SourceInfo", Absyn.IDENT("SOURCEINFO")), args, list("fileName", "isReadOnly", "lineNumberStart", "columnNumberStart", "lineNumberEnd", "columnNumberEnd", "lastEditTime"), 0, nil)
                    (inCache, outExp, DAE.PROP(DAE.T_SOURCEINFO_DEFAULT, DAE.C_CONST()))
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinSome(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local arg::DAE.Exp
              local prop::DAE.Properties
              local ty::DAE.Type
              local c::DAE.Const

               #=  SOME should have exactly one positional argument.
               =#
              if listLength(inPosArgs) != 1 || ! listEmpty(inNamedArgs)
                Error.addSourceMessageAndFail(Error.WRONG_TYPE_OR_NO_OF_ARGS, list("SOME", ""), inInfo)
              else
                (outCache, arg, prop) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
                ty = Types.getPropType(prop)
                (arg, ty) = Types.matchType(arg, ty, DAE.T_METABOXED_DEFAULT, true)
                c = Types.propAllConst(prop)
                outExp = DAE.META_OPTION(SOME(arg))
                outProperties = DAE.PROP(DAE.T_METAOPTION(ty), c)
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinNone(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local arg::DAE.Exp
              local prop::DAE.Properties
              local ty::DAE.Type
              local c::DAE.Const

               #=  NONE shouldn't have any arguments.
               =#
              if ! listEmpty(inPosArgs) || ! listEmpty(inNamedArgs)
                Error.addSourceMessageAndFail(Error.WRONG_TYPE_OR_NO_OF_ARGS, list("NONE", ""), inInfo)
              else
                outExp = DAE.META_OPTION(NONE())
                outProperties = DAE.PROP(DAE.T_METAOPTION(DAE.T_UNKNOWN_DEFAULT), DAE.C_CONST())
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinHomotopy(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local replaceWith::String
              local e::Absyn.Exp
              local e1::Absyn.Exp
              local e2::Absyn.Exp

              replaceWith = Flags.getConfigString(Flags.REPLACE_HOMOTOPY)
               #=  Replace homotopy if Flags.REPLACE_HOMOTOPY is \"actual\" or \"simplified\"
               =#
              if replaceWith == "actual" || replaceWith == "simplified"
                @match list(e1, e2) = getHomotopyArguments(inPosArgs, inNamedArgs)
                e = if replaceWith == "actual"
                      e1
                    else
                      e2
                    end
                (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              else
                (outCache, outExp, outProperties) = elabCallArgs(inCache, inEnv, Absyn.IDENT("homotopy"), inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
              end
               #=  Otherwise, handle it like a normal function.
               =#
          (outCache, outExp, outProperties)
        end

        function getHomotopyArguments(args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}) ::List{Absyn.Exp}
              local outPositionalArgs::List{Absyn.Exp}

              outPositionalArgs = begin
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                   #=  only positional
                   =#
                @match (args, nargs) begin
                  (e1 <| e2 <|  nil(), _)  => begin
                    list(e1, e2)
                  end

                  ( nil(), Absyn.NAMEDARG("actual", e1) <| Absyn.NAMEDARG("simplified", e2) <|  nil())  => begin
                    list(e1, e2)
                  end

                  ( nil(), Absyn.NAMEDARG("simplified", e2) <| Absyn.NAMEDARG("actual", e1) <|  nil())  => begin
                    list(e1, e2)
                  end

                  (e1 <|  nil(), Absyn.NAMEDARG("simplified", e2) <|  nil())  => begin
                    list(e1, e2)
                  end

                  _  => begin
                        Error.addCompilerError("+replaceHomotopy: homotopy called with wrong arguments: " + Dump.printFunctionArgsStr(Absyn.FUNCTIONARGS(args, nargs)))
                      fail()
                  end
                end
              end
               #=  only named
               =#
               #=  combination
               =#
          outPositionalArgs
        end

         #= Elaborates DynamicSelect statements in annotations for OMEdit.
           Currently only text annotations with one String statement accessing
           one variable are supported. Otherwise the first argument is returned. =#
        function elabBuiltinDynamicSelect(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local msg_str::String
              local astatic::Absyn.Exp
              local adynamic::Absyn.Exp
              local dstatic::DAE.Exp
              local ddynamic::DAE.Exp
              local ty::DAE.Type

              if listLength(inPosArgs) != 2 || ! listEmpty(inNamedArgs)
                msg_str = ", expected DynamicSelect(staticExp, dynamicExp)"
                printBuiltinFnArgError("DynamicSelect", msg_str, inPosArgs, inNamedArgs, inPrefix, inInfo)
              end
              @match list(astatic, adynamic) = inPosArgs
              @match (outCache, dstatic, (@match DAE.PROP(ty, _) = outProperties)) = elabExpInExpression(inCache, inEnv, astatic, inImplicit, true, inPrefix, inInfo)
              try
                outExp = begin
                    local acref::Absyn.ComponentRef
                    local digits::ModelicaInteger
                    local namedArgs::List{Absyn.NamedArg}
                    local bconst::Bool
                     #=  keep DynamicSelect for String with cref arg (textString)
                     =#
                  @match (astatic, adynamic) begin
                    (Absyn.STRING(__), Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "String"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(componentRef = acref) <|  nil(), argNames = namedArgs)))  => begin
                        @match (outCache, dstatic, (@match DAE.PROP(ty, _) = outProperties)) = elabExpInExpression(inCache, inEnv, astatic, inImplicit, true, inPrefix, inInfo)
                        ddynamic = Expression.crefToExp(absynCrefToComponentReference(acref))
                         #=  Note: can't generate Modelica syntax as OMEdit only parses lists
                         =#
                         #= outExp := Expression.makePureBuiltinCall(\"DynamicSelect\", {dstatic,
                         =#
                         #=   Expression.makePureBuiltinCall(\"String\", {ddynamic}, ty)}, ty);
                         =#
                        outExp = begin
                          @match namedArgs begin
                            Absyn.NAMEDARG(argName = "significantDigits", argValue = Absyn.INTEGER(value = digits)) <|  nil()  => begin
                              Expression.makeArray(list(dstatic, ddynamic, DAE.ICONST(digits)), ty, true)
                            end

                            Absyn.NAMEDARG(__) <| Absyn.NAMEDARG(argName = "significantDigits", argValue = Absyn.INTEGER(value = digits)) <|  nil()  => begin
                              Expression.makeArray(list(dstatic, ddynamic, DAE.ICONST(digits)), ty, true)
                            end

                            _  => begin
                                Expression.makeArray(list(dstatic, ddynamic), ty, true)
                            end
                          end
                        end
                      outExp
                    end

                    (Absyn.BOOL(__), Absyn.CREF(componentRef = acref))  => begin
                      Expression.makeArray(list(dstatic, Expression.crefToExp(absynCrefToComponentReference(acref))), ty, true)
                    end
                  end
                end
              catch
                outExp = dstatic
              end
               #=  keep DynamicSelect for Boolean with cref arg (visible, primitivesVisible)
               =#
               #=  return first argument of DynamicSelect for model editing per default
               =#
          (outCache, outExp, outProperties)
        end

         #= Elaborates the builtin operator transpose. =#
        function elabBuiltinTranspose(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local cache::FCore.Cache
              local aexp::Absyn.Exp
              local exp::DAE.Exp
              local ty::DAE.Type
              local el_ty::DAE.Type
              local c::DAE.Const
              local d1::DAE.Dimension
              local d2::DAE.Dimension

              @match list(aexp) = inPosArgs
              @match (outCache, exp, DAE.PROP(ty, c)) = elabExpInExpression(inCache, inEnv, aexp, inImpl, true, inPrefix, inInfo)
               #=  Transpose the type.
               =#
              @match DAE.T_ARRAY(DAE.T_ARRAY(el_ty, list(d1)), list(d2)) = ty
              ty = DAE.T_ARRAY(DAE.T_ARRAY(el_ty, list(d2)), list(d1))
              outProperties = DAE.PROP(ty, c)
               #=  Simplify the type and make a call to transpose.
               =#
              ty = Types.simplifyType(ty)
              outExp = Expression.makePureBuiltinCall("transpose", list(exp), ty)
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator sum.
          The input is the arguments to fill as Absyn.Exp expressions and the environment FCore.Graph =#
        function elabBuiltinSum(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local exp_1::DAE.Exp
                  local exp_2::DAE.Exp
                  local t::DAE.Type
                  local tp::DAE.Type
                  local c::DAE.Const
                  local env::FCore.Graph
                  local arrexp::Absyn.Exp
                  local impl::Bool
                  local b::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local estr::String
                  local tstr::String
                  local etp::DAE.Type
                @match (inCache, inEnv, inAbsynExpLst, inBoolean, inPrefix) begin
                  (cache, env, arrexp <|  nil(), impl, pre)  => begin
                      @match (cache, exp_1, DAE.PROP(t, c)) = elabExpInExpression(cache, env, arrexp, impl, true, pre, info)
                      tp = Types.arrayElementType(t)
                      etp = Types.simplifyType(tp)
                      b = Types.isArray(t)
                      b = b && Types.isSimpleType(tp)
                      estr = Dump.printExpStr(arrexp)
                      tstr = Types.unparseType(t)
                      Error.assertionOrAddSourceMessage(b, Error.SUM_EXPECTED_ARRAY, list(estr, tstr), info)
                      exp_2 = Expression.makePureBuiltinCall("sum", list(exp_1), etp)
                    (cache, exp_2, DAE.PROP(tp, c))
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator product.
          The input is the arguments to fill as Absyn.Exp expressions and the environment FCore.Graph =#
        function elabBuiltinProduct(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local exp_1::DAE.Exp
                  local exp_2::DAE.Exp
                  local dim::DAE.Dimension
                  local t::DAE.Type
                  local tp::DAE.Type
                  local c::DAE.Const
                  local env::FCore.Graph
                  local arrexp::Absyn.Exp
                  local impl::Bool
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local str_exp::String
                  local str_pre::String
                  local etp::DAE.Type
                @matchcontinue (inCache, inEnv, inAbsynExpLst, inBoolean, inPrefix) begin
                  (cache, env, arrexp <|  nil(), impl, pre)  => begin
                      @match (cache, exp_1, DAE.PROP(ty, c)) = elabExpInExpression(cache, env, arrexp, impl, true, pre, info)
                      (exp_1, _) = Types.matchType(exp_1, ty, DAE.T_INTEGER_DEFAULT, true)
                      str_exp = "product(" + Dump.printExpStr(arrexp) + ")"
                      str_pre = PrefixUtil.printPrefixStr3(pre)
                      Error.addSourceMessage(Error.BUILTIN_FUNCTION_PRODUCT_HAS_SCALAR_PARAMETER, list(str_exp, str_pre), info)
                    (cache, exp_1, DAE.PROP(DAE.T_INTEGER_DEFAULT, c))
                  end

                  (cache, env, arrexp <|  nil(), impl, pre)  => begin
                      @match (cache, exp_1, DAE.PROP(ty, c)) = elabExpInExpression(cache, env, arrexp, impl, true, pre, info)
                      (exp_1, _) = Types.matchType(exp_1, ty, DAE.T_REAL_DEFAULT, true)
                      str_exp = "product(" + Dump.printExpStr(arrexp) + ")"
                      str_pre = PrefixUtil.printPrefixStr3(pre)
                      Error.addSourceMessage(Error.BUILTIN_FUNCTION_PRODUCT_HAS_SCALAR_PARAMETER, list(str_exp, str_pre), info)
                    (cache, exp_1, DAE.PROP(DAE.T_REAL_DEFAULT, c))
                  end

                  (cache, env, arrexp <|  nil(), impl, pre)  => begin
                      @match (cache, exp_1, DAE.PROP((@match DAE.T_ARRAY(dims = list(_), ty = tp) = t), c)) = elabExpInExpression(cache, env, arrexp, impl, true, pre, info)
                      tp = Types.arrayElementType(t)
                      etp = Types.simplifyType(tp)
                      exp_2 = Expression.makePureBuiltinCall("product", list(exp_1), etp)
                      exp_2 = elabBuiltinProduct2(exp_2)
                    (cache, exp_2, DAE.PROP(tp, c))
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= Replaces product({a1,a2,...an}) with a1*a2*...*an} and
           product([a11,a12,...,a1n;...,am1,am2,..amn]) with a11*a12*...*amn =#
        function elabBuiltinProduct2(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local array_exp::DAE.Exp
                  local expl::List{DAE.Exp}
                @matchcontinue inExp begin
                  DAE.CALL(expLst = array_exp <|  nil())  => begin
                    Expression.makeProductLst(Expression.arrayElements(array_exp))
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= This function elaborates the builtin operator pre.
          Input is the arguments to the pre operator and the environment, FCore.Graph. =#
        function elabBuiltinPre(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local exp::DAE.Exp
              local ty::DAE.Type
              local ty2::DAE.Type
              local c::DAE.Const
              local expl::List{DAE.Exp}
              local sc::Bool
              local exp_str::String
              local pre_str::String

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "pre", inInfo)
              @match (outCache, exp, DAE.PROP(ty, c)) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
               #=  A matrix?
               =#
              if Expression.isMatrix(exp)
                @match DAE.T_ARRAY(ty = ty2) = ty
                ty2 = Types.unliftArray(ty2)
                outExp = Expression.makePureBuiltinCall("pre", list(exp), Types.simplifyType(ty2))
                outExp = elabBuiltinPreMatrix(outExp, ty2)
              elseif Types.isArray(ty)
                ty2 = Types.unliftArray(ty)
                outExp = Expression.makePureBuiltinCall("pre", list(exp), Types.simplifyType(ty2))
                (expl, sc) = elabBuiltinPre2(outExp, ty2)
                outExp = DAE.ARRAY(Types.simplifyType(ty), sc, expl)
              else
                ty = Types.arrayElementType(ty)
                if Types.basicType(ty)
                  outExp = Expression.makePureBuiltinCall("pre", list(exp), Types.simplifyType(ty))
                else
                  exp_str = ExpressionDump.printExpStr(exp)
                  pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                  Error.addSourceMessageAndFail(Error.OPERAND_BUILTIN_TYPE, list("pre", pre_str, exp_str), inInfo)
                end
              end
               #=  An array?
               =#
               #=  A scalar?
               =#
              outProperties = DAE.PROP(ty, c)
          (outCache, outExp, outProperties)
        end

         #= Help function for elabBuiltinPre, when type is array, send it here. =#
        function elabBuiltinPre2(inExp::DAE.Exp, inType::DAE.Type) ::Tuple{List{DAE.Exp}, Bool}
              local outScalar::Bool
              local outExp::List{DAE.Exp}

              (outExp, outScalar) = begin
                  local sc::Bool
                  local expl::List{DAE.Exp}
                  local i::ModelicaInteger
                  local mexpl::List{List{DAE.Exp}}
                  local ty::DAE.Type
                @matchcontinue inExp begin
                  DAE.CALL(expLst = DAE.ARRAY(scalar = sc, array = expl) <|  nil())  => begin
                    (makePreLst(expl, inType), sc)
                  end

                  DAE.CALL(expLst = DAE.MATRIX(ty = ty, integer = i, matrix = mexpl) <|  nil())  => begin
                      mexpl = list(makePreLst(e, inType) for e in mexpl)
                    (list(DAE.MATRIX(ty, i, mexpl)), false)
                  end

                  _  => begin
                      (list(inExp), false)
                  end
                end
              end
          (outExp, outScalar)
        end

         #= This function elaborates the builtin operator inStream.
          Input is the arguments to the inStream operator and the environment, FCore.Graph. =#
        function elabBuiltinInStream(inCache::FCore.Cache, inEnv::FCore.Graph, inArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local exp::DAE.Exp
              local ty::DAE.Type

              @match list(e) = inArgs
              (outCache, exp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImpl, true, inPrefix, inInfo)
              ty = Types.getPropType(outProperties)
              outExp = elabBuiltinStreamOperator(outCache, inEnv, "inStream", exp, ty, inInfo)
               #=  Use elabCallArgs to also try vectorized calls
               =#
              if Types.dimensionsKnown(ty)
                (outCache, outExp, outProperties) = elabCallArgs(outCache, inEnv, Absyn.IDENT("inStream"), list(e), nil, inImpl, inPrefix, inInfo)
              end
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator actualStream.
          Input is the arguments to the actualStream operator and the environment, FCore.Graph. =#
        function elabBuiltinActualStream(inCache::FCore.Cache, inEnv::FCore.Graph, inArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local exp::DAE.Exp
              local ty::DAE.Type

              @match list(e) = inArgs
              (outCache, exp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImpl, true, inPrefix, inInfo)
              ty = Types.getPropType(outProperties)
              outExp = elabBuiltinStreamOperator(outCache, inEnv, "actualStream", exp, ty, inInfo)
               #=  Use elabCallArgs to also try vectorized calls
               =#
              if Types.dimensionsKnown(ty)
                (outCache, outExp, outProperties) = elabCallArgs(outCache, inEnv, Absyn.IDENT("actualStream"), list(e), nil, inImpl, inPrefix, inInfo)
              end
          (outCache, outExp, outProperties)
        end

        function elabBuiltinStreamOperator(inCache::FCore.Cache, inEnv::FCore.Graph, inOperator::String, inExp::DAE.Exp, inType::DAE.Type, inInfo::SourceInfo) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local et::DAE.Type
                  local exp::DAE.Exp
                @match inExp begin
                  DAE.ARRAY(array =  nil())  => begin
                    inExp
                  end

                  _  => begin
                        @match exp <| _ = Expression.flattenArrayExpToList(inExp)
                        validateBuiltinStreamOperator(inCache, inEnv, exp, inType, inOperator, inInfo)
                        et = Types.simplifyType(inType)
                        exp = Expression.makePureBuiltinCall(inOperator, list(exp), et)
                      exp
                  end
                end
              end
          outExp
        end

        function validateBuiltinStreamOperator(inCache::FCore.Cache, inEnv::FCore.Graph, inOperand::DAE.Exp, inType::DAE.Type, inOperator::String, inInfo::SourceInfo)
              _ = begin
                  local cr::DAE.ComponentRef
                  local attr::DAE.Attributes
                  local op_str::String
                   #=  Operand is a stream variable, ok!
                   =#
                @matchcontinue inOperand begin
                  DAE.CREF(componentRef = cr)  => begin
                      (_, attr) = Lookup.lookupVar(inCache, inEnv, cr)
                      @match DAE.ATTR(connectorType = DAE.STREAM()) = attr
                    ()
                  end

                  _  => begin
                         #=  Operand is not a stream variable, error!
                         =#
                        op_str = ExpressionDump.printExpStr(inOperand)
                        Error.addSourceMessage(Error.NON_STREAM_OPERAND_IN_STREAM_OPERATOR, list(op_str, inOperator), inInfo)
                      fail()
                  end
                end
              end
        end

         #= Takes a list of expressions and makes a list of pre - expressions =#
        function makePreLst(inExpl::List{<:DAE.Exp}, inType::DAE.Type) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp}

              local ty::DAE.Type

              ty = Types.simplifyType(inType)
              outExpl = list(Expression.makePureBuiltinCall("pre", list(e), ty) for e in inExpl)
          outExpl
        end

         #= Help function for elabBuiltinPreMatrix, when type is matrix, send it here. =#
        function elabBuiltinPreMatrix(inExp::DAE.Exp, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local exp::DAE.Exp
                @match inExp begin
                  DAE.CALL(expLst = exp && DAE.MATRIX(__) <|  nil())  => begin
                      exp.matrix = list(makePreLst(row, inType) for row in exp.matrix)
                    exp
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #=
          This function elaborates the builtin operator \\'array\\'. For instance,
          array(1,4,6) which is the same as {1,4,6}.
          Input is the list of arguments to the operator, as Absyn.Exp list.
         =#
        function elabBuiltinArray(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local expl::List{DAE.Exp}
              local props::List{DAE.Properties}
              local ty::DAE.Type
              local arr_ty::DAE.Type
              local c::DAE.Const
              local len::ModelicaInteger

              (outCache, expl, props) = elabExpList(inCache, inEnv, inPosArgs, inImplicit, true, inPrefix, inInfo)
              @match (_, DAE.PROP(ty, c)) = elabBuiltinArray2(expl, props, inPrefix, inInfo)
              len = listLength(expl)
              arr_ty = DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(len)))
              outProperties = DAE.PROP(arr_ty, c)
              arr_ty = Types.simplifyType(arr_ty)
              outExp = DAE.ARRAY(arr_ty, Types.isArray(ty), expl)
          (outCache, outExp, outProperties)
        end

         #= Helper function to elabBuiltinArray.
           Asserts that all types are of same dimensionality and of same builtin types. =#
        function elabBuiltinArray2(inExpl::List{<:DAE.Exp}, inProperties::List{<:DAE.Properties}, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{List{DAE.Exp}, DAE.Properties}
              local outProperties::DAE.Properties
              local outExpl::List{DAE.Exp}

              local pre_str::String
              local types::List{DAE.Types}
              local have_real::Bool = false
              local prop::DAE.Properties

              if ! sameDimensions(inProperties)
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.DIFFERENT_DIM_SIZE_IN_ARGUMENTS, list("array", pre_str), inInfo)
              end
              prop = if Types.propsContainReal(inProperties)
                    DAE.PROP(DAE.T_REAL_DEFAULT, DAE.C_VAR())
                  else
                    listHead(inProperties)
                  end
              (outExpl, outProperties) = elabBuiltinArray3(inExpl, inProperties, prop)
          (outExpl, outProperties)
        end

         #= Helper function to elab_builtin_array. =#
        function elabBuiltinArray3(inExpl::List{<:DAE.Exp}, inPropertiesLst::List{<:DAE.Properties}, inProperties::DAE.Properties) ::Tuple{List{DAE.Exp}, DAE.Properties}
              local outProperties::DAE.Properties = listHead(inPropertiesLst)
              local outExpl::List{DAE.Exp} = nil

              local prop::DAE.Properties
              local rest_props::List{DAE.Properties} = inPropertiesLst

              for e in inExpl
                @match prop <| rest_props = rest_props
                e = Types.matchProp(e, prop, inProperties, true)
                outExpl = _cons(e, outExpl)
              end
              outExpl = listReverse(outExpl)
          (outExpl, outProperties)
        end

         #= This function elaborates the builtin operator zeros(n). =#
        function elabBuiltinZeros(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = elabBuiltinFill(inCache, inEnv, _cons(Absyn.INTEGER(0), inPosArgs), nil, inImplicit, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= This function returns true if all properties, containing types, have the same
          dimensions, otherwise false. =#
        function sameDimensions(inProps::List{<:DAE.Properties}) ::Bool
              local res::Bool

              local types::List{DAE.Type}
              local dims::List{DAE.Dimensions}

              types = ListUtil.map(inProps, Types.getPropType)
              dims = ListUtil.map(types, Types.getDimensions)
              res = sameDimensions2(dims)
          res
        end

         #= This function returns true if all properties, containing types, have the same
          dimensions (except for dimension X), otherwise false. =#
        function sameDimensionsExceptionDimX(inProps::List{<:DAE.Properties}, dimException::ModelicaInteger) ::Bool
              local res::Bool

              local types::List{DAE.Type}
              local dims::List{DAE.Dimensions}

              types = ListUtil.map(inProps, Types.getPropType)
              dims = ListUtil.map(types, Types.getDimensions)
              dims = ListUtil.map1(dims, listDelete, dimException)
              res = sameDimensions2(dims)
          res
        end

         #= Helper function to sameDimensions. Checks that each list of dimensions has
           the same dimensions as the other lists. =#
        function sameDimensions2(inDimensions::List{<:DAE.Dimensions}) ::Bool
              local outSame::Bool = true

              local dims::DAE.Dimensions
              local rest_dims::List{DAE.Dimensions} = inDimensions

              if listEmpty(inDimensions)
                return outSame
              end
              while ! listEmpty(listHead(rest_dims))
                dims = list(listHead(d) for d in rest_dims)
                if ! sameDimensions3(dims)
                  outSame = false
                  return outSame
                end
                rest_dims = list(listRest(d) for d in rest_dims)
              end
               #=  Make sure the lists were the same length.
               =#
              for d in rest_dims
                @match true = listEmpty(d)
              end
          outSame
        end

         #= Helper function to sameDimensions2. Check that all dimensions in a list are equal. =#
        function sameDimensions3(inDims::DAE.Dimensions) ::Bool
              local outSame::Bool = true

              local dim1::DAE.Dimension

              if listEmpty(inDims)
                return outSame
              end
              dim1 = listHead(inDims)
              for dim2 in listRest(inDims)
                if ! Expression.dimensionsEqual(dim1, dim2)
                  outSame = false
                  return outSame
                end
              end
          outSame
        end

         #= This function elaborates on the builtin opeator ones(n). =#
        function elabBuiltinOnes(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = elabBuiltinFill(inCache, inEnv, _cons(Absyn.INTEGER(1), inPosArgs), nil, inImplicit, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= This function elaborates on the builtin operator max(a, b). =#
        function elabBuiltinMax(inCache::FCore.Cache, inEnv::FCore.Graph, inFnArgs::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = elabBuiltinMinMaxCommon(inCache, inEnv, "max", inFnArgs, inImpl, inPrefix, info)
          (outCache, outExp, outProperties)
        end

         #= This function elaborates the builtin operator min(a, b) =#
        function elabBuiltinMin(inCache::FCore.Cache, inEnv::FCore.Graph, inFnArgs::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = elabBuiltinMinMaxCommon(inCache, inEnv, "min", inFnArgs, inImpl, inPrefix, info)
          (outCache, outExp, outProperties)
        end

         #= Helper function to elabBuiltinMin and elabBuiltinMax, containing common
          functionality. =#
        function elabBuiltinMinMaxCommon(cache::FCore.Cache, env::FCore.Graph, inFnName::String, inFnArgs::List{<:Absyn.Exp}, impl::Bool, prefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp


              (outExp, outProperties) = begin
                  local arrexp_1::DAE.Exp
                  local s1_1::DAE.Exp
                  local s2_1::DAE.Exp
                  local call::DAE.Exp
                  local tp::DAE.Type
                  local ty::DAE.Type
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local elt_ty::DAE.Type
                  local c::DAE.Const
                  local c1::DAE.Const
                  local c2::DAE.Const
                  local arrexp::Absyn.Exp
                  local s1::Absyn.Exp
                  local s2::Absyn.Exp
                  local p::DAE.Properties
                   #=  min|max(vector)
                   =#
                @match inFnArgs begin
                  arrexp <|  nil()  => begin
                      @match (cache, arrexp_1, DAE.PROP(ty, c)) = elabExpInExpression(cache, env, arrexp, impl, true, prefix, info)
                      @match true = Types.isArray(ty)
                      arrexp_1 = Expression.matrixToArray(arrexp_1)
                      elt_ty = Types.arrayElementType(ty)
                      tp = Types.simplifyType(elt_ty)
                      @match false = Types.isString(tp)
                      call = Expression.makePureBuiltinCall(inFnName, list(arrexp_1), tp)
                    (call, DAE.PROP(elt_ty, c))
                  end

                  s1 <| s2 <|  nil()  => begin
                      @match (cache, s1_1, DAE.PROP(ty1, c1)) = elabExpInExpression(cache, env, s1, impl, true, prefix, info)
                      @match (cache, s2_1, DAE.PROP(ty2, c2)) = elabExpInExpression(cache, env, s2, impl, true, prefix, info)
                      @match (s1_1, s2_1, ty, true) = Types.checkTypeCompat(s1_1, ty1, s2_1, ty2)
                      c = Types.constAnd(c1, c2)
                      tp = Types.simplifyType(ty)
                      @match false = Types.isString(tp)
                      call = Expression.makePureBuiltinCall(inFnName, list(s1_1, s2_1), tp)
                    (call, DAE.PROP(ty, c))
                  end
                end
              end
               #=  min|max(x,y) where x & y are scalars.
               =#
          (cache, outExp, outProperties)
        end

         #= Author: BTH
           This function elaborates the builtin Clock constructor Clock(..). =#
        function elabBuiltinClock(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local interval::DAE.Exp
                  local intervalCounter::DAE.Exp
                  local resolution::DAE.Exp
                  local condition::DAE.Exp
                  local startInterval::DAE.Exp
                  local c::DAE.Exp
                  local solverMethod::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop::DAE.Properties = DAE.PROP(DAE.T_CLOCK_DEFAULT, DAE.C_VAR())
                  local ainterval::Absyn.Exp
                  local aintervalCounter::Absyn.Exp
                  local aresolution::Absyn.Exp
                  local acondition::Absyn.Exp
                  local astartInterval::Absyn.Exp
                  local ac::Absyn.Exp
                  local asolverMethod::Absyn.Exp
                  local rInterval::ModelicaReal
                  local rStartInterval::ModelicaReal
                  local iIntervalCounter::ModelicaInteger
                  local iResolution::ModelicaInteger
                  local variability::DAE.Const
                  local strSolverMethod::String
                  local val::Values.Value
                   #=  Inferred clock \"Clock()\"
                   =#
                @matchcontinue (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, _,  nil(),  nil(), _, _, _)  => begin
                      call = DAE.CLKCONST(DAE.INFERRED_CLOCK())
                    (cache, call, DAE.PROP(DAE.T_CLOCK_DEFAULT, DAE.C_VAR()))
                  end

                  (cache, env, aintervalCounter <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, intervalCounter, prop1) = elabExpInExpression(cache, env, aintervalCounter, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      (intervalCounter, _) = Types.matchType(intervalCounter, ty1, DAE.T_INTEGER_DEFAULT, true)
                      call = DAE.CLKCONST(DAE.INTEGER_CLOCK(intervalCounter, DAE.ICONST(1)))
                    (cache, call, prop)
                  end

                  (cache, env, aintervalCounter <| aresolution <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, intervalCounter, prop1) = elabExpInExpression(cache, env, aintervalCounter, impl, true, pre, info)
                      (cache, resolution, prop2) = elabExpInExpression(cache, env, aresolution, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty2 = Types.arrayElementType(Types.getPropType(prop2))
                      (intervalCounter, _) = Types.matchType(intervalCounter, ty1, DAE.T_INTEGER_DEFAULT, true)
                      (resolution, _) = Types.matchType(resolution, ty2, DAE.T_INTEGER_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, resolution, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(val) >= 1, Error.WRONG_VALUE_OF_ARG, list("Clock", "resolution", ValuesUtil.valString(val), ">= 1"), info)
                      resolution = ValuesUtil.valueExp(val)
                      call = DAE.CLKCONST(DAE.INTEGER_CLOCK(intervalCounter, resolution))
                    (cache, call, prop)
                  end

                  (cache, env, ainterval <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, interval, prop1) = elabExpInExpression(cache, env, ainterval, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      (interval, _) = Types.matchType(interval, ty1, DAE.T_REAL_DEFAULT, true)
                      call = DAE.CLKCONST(DAE.REAL_CLOCK(interval))
                    (cache, call, prop)
                  end

                  (cache, env, acondition <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, condition, prop1) = elabExpInExpression(cache, env, acondition, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      (condition, _) = Types.matchType(condition, ty1, DAE.T_BOOL_DEFAULT, true)
                      call = DAE.CLKCONST(DAE.BOOLEAN_CLOCK(condition, DAE.RCONST(0.0)))
                    (cache, call, prop)
                  end

                  (cache, env, acondition <| astartInterval <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, condition, prop1) = elabExpInExpression(cache, env, acondition, impl, true, pre, info)
                      (cache, startInterval, prop2) = elabExpInExpression(cache, env, astartInterval, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty2 = Types.arrayElementType(Types.getPropType(prop2))
                      (condition, _) = Types.matchType(condition, ty1, DAE.T_BOOL_DEFAULT, true)
                      (startInterval, _) = Types.matchType(startInterval, ty2, DAE.T_REAL_DEFAULT, true)
                      call = DAE.CLKCONST(DAE.BOOLEAN_CLOCK(condition, startInterval))
                    (cache, call, prop)
                  end

                  (cache, env, ac <| asolverMethod <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, c, prop1) = elabExpInExpression(cache, env, ac, impl, true, pre, info)
                      (cache, solverMethod, prop2) = elabExpInExpression(cache, env, asolverMethod, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty2 = Types.arrayElementType(Types.getPropType(prop2))
                      (c, _) = Types.matchType(c, ty1, DAE.T_CLOCK_DEFAULT, true)
                      (solverMethod, _) = Types.matchType(solverMethod, ty2, DAE.T_STRING_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, solverMethod, false, Absyn.MSG(info), 0)
                      solverMethod = ValuesUtil.valueExp(val)
                      call = DAE.CLKCONST(DAE.SOLVER_CLOCK(c, solverMethod))
                    (cache, call, prop)
                  end

                  (cache, env, ac <|  nil(), Absyn.NAMEDARG(argName = "solverMethod", argValue = asolverMethod) <|  nil(), impl, pre, _)  => begin
                      (cache, c, prop1) = elabExpInExpression(cache, env, ac, impl, true, pre, info)
                      (cache, solverMethod, prop2) = elabExpInExpression(cache, env, asolverMethod, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty2 = Types.arrayElementType(Types.getPropType(prop2))
                      (c, _) = Types.matchType(c, ty1, DAE.T_CLOCK_DEFAULT, true)
                      (solverMethod, _) = Types.matchType(solverMethod, ty2, DAE.T_STRING_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, solverMethod, false, Absyn.MSG(info), 0)
                      solverMethod = ValuesUtil.valueExp(val)
                      call = DAE.CLKCONST(DAE.SOLVER_CLOCK(c, solverMethod))
                    (cache, call, prop)
                  end
                end
              end
               #=  clock with Integer interval \"Clock(intervalCounter)\"
               =#
               #=  clock with Integer interval \"Clock(intervalCounter, resolution)\"
               =#
               #=  evaluate and check if resolution >= 1 (rfranke)
               =#
               #=  clock with Real interval \"Clock(interval)\"
               =#
               #=  Boolean Clock (clock triggered by zero-crossing events) \"Clock(condition)\"
               =#
               #=  Boolean Clock (clock triggered by zero-crossing events) \"Clock(condition, startInterval)\"
               =#
               #=  TODO! check if expression startInterval is >= 0.0
               =#
               #=  rStartInterval = Expression.toReal(startInterval);
               =#
               #=  true = rStartInterval >= 0.0;
               =#
               #=  Solver Clock \"Clock(c, solverMethod)\"
               =#
               #=  evaluate structural solverMethod (rfranke)
               =#
               #=  Solver Clock \"Clock(c, solverMethod=solverMethod)\" with named arguments
               =#
               #=  evaluate structural solverMethod (rfranke)
               =#
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator hold(u). =#
        function elabBuiltinHold(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, au <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("hold"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("hold"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator sample(..) variants. =#
        function elabBuiltinSample(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local c::DAE.Exp
                  local start::DAE.Exp
                  local interval::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop::DAE.Properties
                  local variability::DAE.Const
                  local au::Absyn.Exp
                  local ac::Absyn.Exp
                  local astart::Absyn.Exp
                  local ainterval::Absyn.Exp
                   #=  The time event triggering sample(start, interval)
                   =#
                @matchcontinue (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, astart <| ainterval <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, start, prop1) = elabExpInExpression(cache, env, astart, impl, true, pre, info)
                      (cache, interval, prop2) = elabExpInExpression(cache, env, ainterval, impl, true, pre, info)
                      ty1 = Types.getPropType(prop1)
                      ty2 = Types.getPropType(prop2)
                      (start, _) = Types.matchType(start, ty1, DAE.T_REAL_DEFAULT, true)
                      (interval, _) = Types.matchType(interval, ty2, DAE.T_REAL_DEFAULT, true)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("start", DAE.T_REAL_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("interval", DAE.T_REAL_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE())), DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("sample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("sample"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <| ac <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      (cache, c, prop2) = elabExpInExpression(cache, env, ac, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty2 = Types.arrayElementType(Types.getPropType(prop2))
                      variability = Types.getPropConst(prop1)
                      (c, _) = Types.matchType(c, ty2, DAE.T_CLOCK_DEFAULT, true)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, variability, DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("c", ty2, DAE.C_VAR(), DAE.NON_PARALLEL(), SOME(DAE.CLKCONST(DAE.INFERRED_CLOCK())))), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("sample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("sample"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      variability = Types.getPropConst(prop1)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, variability, DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("c", DAE.T_CLOCK_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), SOME(DAE.CLKCONST(DAE.INFERRED_CLOCK())))), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("sample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("sample"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
               #=  The sample from the Synchronous Language Elements chapter (Modelica 3.3)
               =#
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator shiftSample(u,shiftCounter,resolution). =#
        function elabBuiltinShiftSample(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local shiftCounter::DAE.Exp
                  local resolution::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop3::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                  local ashiftCounter::Absyn.Exp
                  local aresolution::Absyn.Exp
                  local val::Values.Value
                  local rval::Values.Value
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, au <| ashiftCounter <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      (cache, shiftCounter, prop2) = elabExpInExpression(cache, env, ashiftCounter, impl, true, pre, info)
                      (shiftCounter, _) = Types.matchType(shiftCounter, Types.getPropType(prop2), DAE.T_INTEGER_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, shiftCounter, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(val) >= 0, Error.WRONG_VALUE_OF_ARG, list("shiftSample", "shiftCounter", ValuesUtil.valString(val), ">= 0"), info)
                      ashiftCounter = Absyn.INTEGER(ValuesUtil.valueInteger(val))
                      aresolution = Absyn.INTEGER(1)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("shiftCounter", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("resolution", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("shiftSample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("shiftSample"), list(au, ashiftCounter, aresolution), nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <| ashiftCounter <| aresolution <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      (cache, shiftCounter, prop2) = elabExpInExpression(cache, env, ashiftCounter, impl, true, pre, info)
                      (shiftCounter, _) = Types.matchType(shiftCounter, Types.getPropType(prop2), DAE.T_INTEGER_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, shiftCounter, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(val) >= 0, Error.WRONG_VALUE_OF_ARG, list("shiftSample", "shiftCounter", ValuesUtil.valString(val), ">= 0"), info)
                      ashiftCounter = Absyn.INTEGER(ValuesUtil.valueInteger(val))
                      (cache, resolution, prop3) = elabExpInExpression(cache, env, aresolution, impl, true, pre, info)
                      (resolution, _) = Types.matchType(resolution, Types.getPropType(prop3), DAE.T_INTEGER_DEFAULT, true)
                      (cache, rval) = Ceval.ceval(cache, env, resolution, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(rval) >= 1, Error.WRONG_VALUE_OF_ARG, list("shiftSample", "resolution", ValuesUtil.valString(rval), ">= 1"), info)
                      aresolution = Absyn.INTEGER(ValuesUtil.valueInteger(rval))
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("shiftCounter", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("resolution", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("shiftSample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("shiftSample"), list(au, ashiftCounter, aresolution), nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
               #=  evaluate and check if shiftCounter >= 0 (rfranke)
               =#
               #=  Pretend that shiftSample(u,shiftCounter) was shiftSample(u,shiftCounter,1) (resolution=1 is default value)
               =#
               #=  evaluate and check if shiftCounter >= 0 (rfranke)
               =#
               #=  evaluate and check if resolution >= 1 (rfranke)
               =#
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator backSample(u,backCounter,resolution). =#
        function elabBuiltinBackSample(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local backCounter::DAE.Exp
                  local resolution::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop3::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                  local abackCounter::Absyn.Exp
                  local aresolution::Absyn.Exp
                  local val::Values.Value
                  local rval::Values.Value
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, au <| abackCounter <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      (cache, backCounter, prop2) = elabExpInExpression(cache, env, abackCounter, impl, true, pre, info)
                      (backCounter, _) = Types.matchType(backCounter, Types.getPropType(prop2), DAE.T_INTEGER_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, backCounter, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(val) >= 0, Error.WRONG_VALUE_OF_ARG, list("backSample", "backCounter", ValuesUtil.valString(val), ">= 0"), info)
                      abackCounter = Absyn.INTEGER(ValuesUtil.valueInteger(val))
                      aresolution = Absyn.INTEGER(1)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("backCounter", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("resolution", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("backSample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("backSample"), list(au, abackCounter, aresolution), nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <| abackCounter <| aresolution <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      (cache, backCounter, prop2) = elabExpInExpression(cache, env, abackCounter, impl, true, pre, info)
                      (backCounter, _) = Types.matchType(backCounter, Types.getPropType(prop2), DAE.T_INTEGER_DEFAULT, true)
                      (cache, val) = Ceval.ceval(cache, env, backCounter, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(val) >= 0, Error.WRONG_VALUE_OF_ARG, list("backSample", "backCounter", ValuesUtil.valString(val), ">= 0"), info)
                      abackCounter = Absyn.INTEGER(ValuesUtil.valueInteger(val))
                      (cache, resolution, prop3) = elabExpInExpression(cache, env, aresolution, impl, true, pre, info)
                      (resolution, _) = Types.matchType(resolution, Types.getPropType(prop3), DAE.T_INTEGER_DEFAULT, true)
                      (cache, rval) = Ceval.ceval(cache, env, resolution, false, Absyn.MSG(info), 0)
                      Error.assertionOrAddSourceMessage(ValuesUtil.valueInteger(rval) >= 1, Error.WRONG_VALUE_OF_ARG, list("backSample", "resolution", ValuesUtil.valString(rval), ">= 1"), info)
                      aresolution = Absyn.INTEGER(ValuesUtil.valueInteger(rval))
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("backCounter", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("resolution", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("backSample"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("backSample"), list(au, abackCounter, aresolution), nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
               #=  evaluate and check if backCounter >= 0 (rfranke)
               =#
               #=  Pretend that backSample(u,backCounter) was backSample(u,backCounter,1) (resolution=1 is default value)
               =#
               #=  evaluate and check if backCounter >= 0 (rfranke)
               =#
               #=  evaluate and check if resolution >= 1 (rfranke)
               =#
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator noClock(u). =#
        function elabBuiltinNoClock(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, au <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), ty1, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("noClock"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("noClock"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
         This function elaborates the builtin operator firstTick(u). =#
        function elabBuiltinFirstTick(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local ty1::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env,  nil(),  nil(), impl, pre, _)  => begin
                      ty = DAE.T_FUNCTION(nil, DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("firstTick"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("firstTick"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("firstTick"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("firstTick"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator interval(u). =#
        function elabBuiltinInterval(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local u::DAE.Exp
                  local ty1::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local au::Absyn.Exp
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env,  nil(),  nil(), impl, pre, _)  => begin
                      ty = DAE.T_FUNCTION(nil, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("interval"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("interval"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end

                  (cache, env, au <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, au, impl, true, pre, info)
                      ty1 = Types.arrayElementType(Types.getPropType(prop1))
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("u", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("interval"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("interval"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        Helper function to elabBuiltinTransition.
        This function checks whether a type is complex.
        It is used as a workaround to check for block instances in elabBuiltinTransition, elabBultinActiveState and elabBuiltinInitalState.
        This is not perfect since there are also other instances that are 'complex' types which are not block instances.
        But allowing more might not be so bad anyway, since the MLS 3.3 restriction to block seems more restrictive than necessary,
        e.g., one can be more lenient and allow models as states, too... =#
        function isBlockTypeWorkaround(ity::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ity begin
                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    isBlockTypeWorkaround(ity.complexType)
                  end

                  DAE.T_COMPLEX(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=
        Author: BTH
        This function elaborates the builtin operator
        transition(from, to, condition, immediate=true, reset=true, synchronize=false, priority=1). =#
        function elabBuiltinTransition(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop::DAE.Properties
                  local n::ModelicaInteger
                  local nFrom::ModelicaInteger
                  local strMsg0::String
                  local strPre::String
                  local s1::String
                  local s2::String
                  local slist::List{String}
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, _, _, impl, pre, _)  => begin
                      slist = ListUtil.map(nargs, Dump.printNamedArgStr)
                      s1 = Dump.printExpLstStr(args)
                      s2 = stringDelimitList(_cons(s1, slist), ", ")
                      strMsg0 = "transition(" + s2 + ")"
                      strPre = PrefixUtil.printPrefixStr3(pre)
                      n = listLength(args)
                      ty1 = elabBuiltinTransition2(cache, env, args, nargs, impl, pre, info, "from", n, strMsg0, strPre)
                      ty2 = elabBuiltinTransition2(cache, env, args, nargs, impl, pre, info, "to", n, strMsg0, strPre)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("from", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("to", ty2, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("condition", DAE.T_BOOL_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("immediate", DAE.T_BOOL_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), SOME(DAE.BCONST(true))), DAE.FUNCARG("reset", DAE.T_BOOL_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), SOME(DAE.BCONST(true))), DAE.FUNCARG("synchronize", DAE.T_BOOL_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), SOME(DAE.BCONST(false))), DAE.FUNCARG("priority", DAE.T_INTEGER_DEFAULT, DAE.C_PARAM(), DAE.NON_PARALLEL(), SOME(DAE.ICONST(1)))), DAE.T_NORETCALL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("transition"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("transition"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
               #=  Check if \"from\" and \"to\" arguments are of complex type and return their type
               =#
               #=  Alternatively, ty1 and ty2 could be replaced by DAE.T_CODE(DAE.C_VARIABLENAME,{}), not sure if that would be a better solution
               =#
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        Helper function to elabBuiltinTransition.
        Check if the \\\"from\\\" argument or the \\\"to\\\" argument is of complex type. =#
        function elabBuiltinTransition2(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo, argName::Absyn.Ident, n::ModelicaInteger, strMsg0::String, strPre::String) ::DAE.Type
              local ty::DAE.Type

              local arg1::Absyn.Exp
              local prop1::DAE.Properties
              local nPos::ModelicaInteger
              local s1::String
              local s2::String
              local strPos::String
              local strMsg1::String
              local b1::Bool

              strPos = if argName == "from"
                    "first"
                  else
                    "second"
                  end
              nPos = if argName == "from"
                    1
                  else
                    2
                  end
              b1 = ListUtil.isMemberOnTrue(argName, nargs, elabBuiltinTransition3)
              s1 = strMsg0 + ", named argument \\" + argName + "\\ already has a value."
              Error.assertionOrAddSourceMessage(! (b1 && n >= nPos), Error.WRONG_TYPE_OR_NO_OF_ARGS, list(s1, strPre), info)
              s2 = strMsg0 + ", missing value for " + strPos + " argument \\" + argName + "\\."
              Error.assertionOrAddSourceMessage(b1 || n >= nPos, Error.WRONG_TYPE_OR_NO_OF_ARGS, list(s2, strPre), info)
              arg1 = elabBuiltinTransition5(argName, b1, args, nargs)
              (_, _, prop1) = elabExpInExpression(inCache, inEnv, arg1, inBoolean, true, inPrefix, info)
              ty = Types.getPropType(prop1)
              strMsg1 = strMsg0 + ", " + strPos + "argument needs to be a block instance."
              Error.assertionOrAddSourceMessage(isBlockTypeWorkaround(ty), Error.WRONG_TYPE_OR_NO_OF_ARGS, list(strMsg1, strPre), info)
          ty
        end

         #=
        Author: BTH
        Helper function to elabBuiltinTransition.
        Checks if namedArg.argName == name =#
        function elabBuiltinTransition3(name::Absyn.Ident, namedArg::Absyn.NamedArg) ::Bool
              local outIsEqual::Bool

              outIsEqual = begin
                  local argName::Absyn.Ident
                  local argValue::Absyn.Exp
                @match namedArg begin
                  Absyn.NAMEDARG(__)  => begin
                    stringEq(name, namedArg.argName)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsEqual
        end

         #=
        Author: BTH
        Helper function to elabBuiltinTransition.
        Extract element argValue. =#
        function elabBuiltinTransition4(inElement::Absyn.NamedArg) ::Absyn.Exp
              local argValue::Absyn.Exp

              @match Absyn.NAMEDARG(argValue = argValue) = inElement
          argValue
        end

         #=
        Author: BTH
        Helper function to elabBuiltinTransition. =#
        function elabBuiltinTransition5(argName::String, getAsNamedArg::Bool, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}) ::Absyn.Exp
              local argValue::Absyn.Exp

              argValue = begin
                  local namedArg::Absyn.NamedArg
                @match (argName, getAsNamedArg) begin
                  ("from", true)  => begin
                      namedArg = ListUtil.getMemberOnTrue("from", nargs, elabBuiltinTransition3)
                    elabBuiltinTransition4(namedArg)
                  end

                  ("from", false)  => begin
                    listHead(args)
                  end

                  ("to", true)  => begin
                      namedArg = ListUtil.getMemberOnTrue("to", nargs, elabBuiltinTransition3)
                    elabBuiltinTransition4(namedArg)
                  end

                  ("to", false)  => begin
                    listGet(args, 2)
                  end
                end
              end
          argValue
        end

         #=
        Author: BTH
        This function elaborates the builtin operator
        initialState(state). =#
        function elabBuiltinInitialState(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local state::DAE.Exp
                  local ty1::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local astate::Absyn.Exp
                  local strMsg::String
                  local strPre::String
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, astate <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, astate, impl, true, pre, info)
                      ty1 = Types.getPropType(prop1)
                      strMsg = "initialState(" + Dump.printExpLstStr(args) + "), Argument needs to be a block instance."
                      strPre = PrefixUtil.printPrefixStr3(pre)
                      Error.assertionOrAddSourceMessage(isBlockTypeWorkaround(ty1), Error.WRONG_TYPE_OR_NO_OF_ARGS, list(strMsg, strPre), info)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("state", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_NORETCALL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("initialState"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("initialState"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator
        activeState(state). =#
        function elabBuiltinActiveState(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local state::DAE.Exp
                  local ty1::DAE.Type
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local astate::Absyn.Exp
                  local strMsg::String
                  local strPre::String
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env, astate <|  nil(),  nil(), impl, pre, _)  => begin
                      (cache, _, prop1) = elabExpInExpression(cache, env, astate, impl, true, pre, info)
                      ty1 = Types.getPropType(prop1)
                      strMsg = "activeState(" + Dump.printExpLstStr(args) + "), Argument needs to be a block instance."
                      strPre = PrefixUtil.printPrefixStr3(pre)
                      Error.assertionOrAddSourceMessage(isBlockTypeWorkaround(ty1), Error.WRONG_TYPE_OR_NO_OF_ARGS, list(strMsg, strPre), info)
                      ty = DAE.T_FUNCTION(list(DAE.FUNCARG("state", ty1, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("activeState"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("activeState"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator
        ticksInState(). =#
        function elabBuiltinTicksInState(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop::DAE.Properties
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env,  nil(),  nil(), impl, pre, _)  => begin
                      ty = DAE.T_FUNCTION(nil, DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("ticksInState"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("ticksInState"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #=
        Author: BTH
        This function elaborates the builtin operator
        timeInState(). =#
        function elabBuiltinTimeInState(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local call::DAE.Exp
                  local ty::DAE.Type
                  local impl::Bool
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local prop::DAE.Properties
                @match (inCache, inEnv, args, nargs, inBoolean, inPrefix, info) begin
                  (cache, env,  nil(),  nil(), impl, pre, _)  => begin
                      ty = DAE.T_FUNCTION(nil, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN_IMPURE, Absyn.IDENT("timeInState"))
                      @match (cache, SOME((call, prop))) = elabCallArgs3(cache, env, list(ty), Absyn.IDENT("timeInState"), args, nargs, impl, pre, info)
                    (cache, call, prop)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= This function elaborates on the builtin operator boolean, which extracts
           the boolean value of a Real, Integer or Boolean value. =#
        function elabBuiltinBoolean(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = verifyBuiltInHandlerType(inCache, inEnv, inPosArgs, inImplicit, Types.isIntegerOrRealOrBooleanOrSubTypeOfEither, "boolean", inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= This function elaborates on the builtin operator Integer for Enumerations, which extracts
          the Integer value of a Enumeration element. =#
        function elabBuiltinIntegerEnum(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = verifyBuiltInHandlerType(inCache, inEnv, inPosArgs, inImplicit, Types.isEnumeration, "Integer", inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

         #= The builtin operator noEvent makes sure that events are not generated for the
           expression. =#
        function elabBuiltinNoevent(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "noEvent", inInfo)
              e = listHead(inPosArgs)
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              outExp = Expression.makePureBuiltinCall("noEvent", list(outExp), DAE.T_BOOL_DEFAULT)
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in edge operator. =#
        function elabBuiltinEdge(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type
              local c::DAE.Const
              local msg::String

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "edge", inInfo)
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(ty, c) = outProperties
               #=  Print an error if the argument is not a Boolean.
               =#
              if ! Types.isScalarBoolean(ty)
                msg = "edge(" + ExpressionDump.printExpStr(outExp) + ")"
                Error.addSourceMessageAndFail(Error.TYPE_ERROR, list(msg), inInfo)
              end
               #=  If the argument is a variable, make a call to edge. Otherwise the
               =#
               #=  expression is false.
               =#
              if Types.isVar(c)
                outExp = Expression.makePureBuiltinCall("edge", list(outExp), DAE.T_BOOL_DEFAULT)
              else
                outExp = DAE.BCONST(false)
              end
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in der operator. =#
        function elabBuiltinDer(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type
              local c::DAE.Const
              local dims::List{DAE.Dimension}
              local exp_str::String
              local ty_str::String

              if FGraphUtil.inFunctionScope(inEnv)
                Error.addSourceMessageAndFail(Error.DERIVATIVE_FUNCTION_CONTEXT, nil, inInfo)
              end
              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "der", inInfo)
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(ty, c) = outProperties
               #=  Make sure the argument's type is a subtype of Real.
               =#
              if ! Types.isRealOrSubTypeReal(Types.arrayElementType(ty))
                exp_str = Dump.printExpStr(listHead(inPosArgs))
                ty_str = Types.unparseTypeNoAttr(ty)
                Error.addSourceMessageAndFail(Error.DERIVATIVE_NON_REAL, list(exp_str, ty_str), inInfo)
              end
              if Types.isVar(c)
                if Types.dimensionsKnown(ty)
                  (outCache, outExp, outProperties) = elabCallArgs(inCache, inEnv, Absyn.IDENT("der"), inPosArgs, nil, inImplicit, inPrefix, inInfo)
                else
                  outExp = Expression.makePureBuiltinCall("der", list(outExp), Types.simplifyType(ty))
                end
              else
                dims = Types.getDimensions(ty)
                (outExp, ty) = Expression.makeZeroExpression(dims)
                outProperties = DAE.PROP(ty, DAE.C_CONST())
              end
               #=  Use elabCallArgs to handle vectorization if possible.
               =#
               #=  Otherwise just create a call to der.
               =#
               #=  der(constant) = 0.
               =#
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in change operator. =#
        function elabBuiltinChange(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local pre_str::String
              local ty::DAE.Type
              local c::DAE.Const
              local attr::DAE.Attributes
              local cref::DAE.ComponentRef
              local var::SCode.Variability

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "change", inInfo)
              e = listHead(inPosArgs)
               #=  Check that the argument is a variable (i.e. a component reference).
               =#
              if ! AbsynUtil.isCref(e)
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.ARGUMENT_MUST_BE_VARIABLE, list("First", "change", pre_str), inInfo)
              end
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(ty, c) = outProperties
              if Types.isSimpleType(ty)
                if Types.isParameterOrConstant(c)
                  outExp = DAE.BCONST(false)
                  outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_CONST())
                elseif Types.isDiscreteType(ty)
                  outExp = Expression.makePureBuiltinCall("change", list(outExp), DAE.T_BOOL_DEFAULT)
                  outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_VAR())
                else
                  cref = Expression.getCrefFromCrefOrAsub(outExp)
                  (outCache, attr) = Lookup.lookupVar(outCache, inEnv, cref)
                  @match DAE.ATTR(variability = var) = attr
                  if valueEq(var, SCode.DISCRETE())
                    outExp = Expression.makePureBuiltinCall("change", list(outExp), DAE.T_BOOL_DEFAULT)
                    outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_VAR())
                  else
                    pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                    Error.addSourceMessageAndFail(Error.ARGUMENT_MUST_BE_DISCRETE_VAR, list("First", "change", pre_str), inInfo)
                  end
                end
              else
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.TYPE_MUST_BE_SIMPLE, list("operand to change", pre_str), inInfo)
              end
               #=  change(constant) = false
               =#
               #=  If the argument is discrete, make a call to change.
               =#
               #=  Workaround for discrete Reals. Does not handle Reals that become
               =#
               #=  discrete due to when-section.
               =#
               #=  Look up the component's variability.
               =#
               #=  If it's discrete, make a call to change.
               =#
               #=  Otherwise, print an error and fail.
               =#
               #=  If the argument does not have a simple type, print an error and fail.
               =#
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in cat operator. =#
        function elabBuiltinCat(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local dim_exp::DAE.Exp
              local dim_props::DAE.Properties
              local dim_ty::DAE.Type
              local ty::DAE.Type
              local result_ty::DAE.Type
              local dim_c::DAE.Const
              local arr_c::DAE.Const
              local c::DAE.Const
              local pre_str::String
              local exp_str::String
              local dim_int::ModelicaInteger
              local arr_expl::List{DAE.Exp}
              local arr_props::List{DAE.Properties}
              local arr_tys::List{DAE.Type}
              local tys::List{DAE.Type}
              local dims::List{DAE.Dimension}
              local dim::DAE.Dimension

              if listLength(inPosArgs) < 2 || ! listEmpty(inNamedArgs)
                Error.addSourceMessageAndFail(Error.WRONG_NO_OF_ARGS, list("cat"), inInfo)
              end
               #=  Elaborate the first argument, the dimension to concatenate along.
               =#
              (outCache, dim_exp, dim_props) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(dim_ty, dim_c) = dim_props
               #=  The first argument must be an integer.
               =#
              if ! Types.isScalarInteger(dim_ty)
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.ARGUMENT_MUST_BE_INTEGER, list("First", "cat", pre_str), inInfo)
              end
               #=  Evaluate the first argument.
               =#
              @match (outCache, Values.INTEGER(dim_int)) = Ceval.ceval(inCache, inEnv, dim_exp, false, Absyn.MSG(inInfo))
               #=  Elaborate the rest of the arguments, the arrays to concatenate.
               =#
              (outCache, arr_expl, arr_props) = elabExpList(outCache, inEnv, listRest(inPosArgs), inImplicit, true, inPrefix, inInfo)
               #=  Type check the arguments and check that all dimensions except the one we
               =#
               #=  will concatenate along is equal.
               =#
              arr_tys = list(Types.getPropType(p) for p in arr_props)
              @match ty <| tys = list(Types.makeNthDimUnknown(t, dim_int) for t in arr_tys)
              result_ty = ListUtil.fold1(tys, Types.arraySuperType, inInfo, ty)
              try
                (arr_expl, arr_tys) = Types.matchTypes(arr_expl, arr_tys, result_ty, false)
              catch
                exp_str = stringDelimitList(list(Dump.printExpStr(e) for e in inPosArgs), ", ")
                exp_str = "cat(" + exp_str + ")"
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.DIFFERENT_DIM_SIZE_IN_ARGUMENTS, list(exp_str, pre_str), inInfo)
              end
               #=  Mismatched types, print an error and fail.
               =#
               #=  Calculate the size of the concatenated dimension, and insert it in the
               =#
               #=  result type.
               =#
              dims = list(Types.getDimensionNth(t, dim_int) for t in arr_tys)
              dim = Expression.dimensionsAdd(d for d in dims)
              result_ty = Types.setDimensionNth(result_ty, dim, dim_int)
               #=  Construct a call to cat.
               =#
              arr_c = elabArrayConst(arr_props)
              c = Types.constAnd(dim_c, arr_c)
              ty = Types.simplifyType(result_ty)
              outExp = Expression.makePureBuiltinCall("cat", _cons(dim_exp, arr_expl), ty)
              outProperties = DAE.PROP(result_ty, c)
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in identity operator. =#
        function elabBuiltinIdentity(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type
              local exp_ty::DAE.Type
              local c::DAE.Const
              local pre_str::String
              local msg::Absyn.Msg
              local sz::ModelicaInteger
              local dim_size::DAE.Dimension
              local dim_exp::DAE.Exp
              local check_model::Bool

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "identity", inInfo)
              (outCache, dim_exp, outProperties) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
              @match DAE.PROP(ty, c) = outProperties
               #=  Check that the argument is an Integer.
               =#
              if ! Types.isScalarInteger(ty)
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.ARGUMENT_MUST_BE_INTEGER, list("First", "identity", pre_str), inInfo)
              end
              if Types.isParameterOrConstant(c)
                check_model = Flags.getConfigBool(Flags.CHECK_MODEL)
                msg = if check_model
                      Absyn.NO_MSG()
                    else
                      Absyn.MSG(inInfo)
                    end
                try
                  @match (outCache, Values.INTEGER(sz)) = Ceval.ceval(outCache, inEnv, dim_exp, false, msg)
                  dim_size = DAE.DIM_INTEGER(sz)
                  dim_exp = DAE.ICONST(sz)
                catch
                  if check_model
                    dim_size = DAE.DIM_UNKNOWN()
                  else
                    fail()
                  end
                end
              else
                dim_size = DAE.DIM_UNKNOWN()
              end
               #=  If the argument is a parameter or constant, evaluate it.
               =#
               #=  Allow evaluation to fail if checkModel is used.
               =#
              ty = Types.liftArrayListDims(DAE.T_INTEGER_DEFAULT, list(dim_size, dim_size))
              exp_ty = Types.simplifyType(ty)
              outExp = Expression.makePureBuiltinCall("identity", list(dim_exp), exp_ty)
              outProperties = DAE.PROP(ty, c)
          (outCache, outExp, outProperties)
        end

        function zeroSizeOverconstrainedOperator(inExp::DAE.Exp, inFExp::DAE.Exp, inInfo::SourceInfo)
              _ = begin
                  local s::String
                @match inExp begin
                  DAE.ARRAY(array =  nil())  => begin
                      s = ExpressionDump.printExpStr(inFExp)
                      Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO_RETURN_FALSE, list(s), inInfo)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= This function elaborates on the builtin operator Connections.isRoot. =#
        function elabBuiltinIsRoot(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local exp::DAE.Exp

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "Connections.isRoot", inInfo)
              (outCache, exp) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), false, false, inPrefix, inInfo)
              outExp = DAE.CALL(Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), list(exp), DAE.callAttrBuiltinBool)
              outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_VAR())
              zeroSizeOverconstrainedOperator(exp, outExp, inInfo)
          (outCache, outExp, outProperties)
        end

         #= author: adrpo
          This function handles the built-in rooted operator. (MultiBody).
          See more here: http:trac.modelica.org/Modelica/ticket/95 =#
        function elabBuiltinRooted(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local exp::DAE.Exp

               #=  this operator is not even specified in the specification!
               =#
               #=  see: http:trac.modelica.org/Modelica/ticket/95
               =#
              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "rooted", inInfo)
              (outCache, exp) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), false, false, inPrefix, inInfo)
              outExp = DAE.CALL(Absyn.IDENT("rooted"), list(exp), DAE.callAttrBuiltinBool)
              outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_VAR())
              zeroSizeOverconstrainedOperator(exp, outExp, inInfo)
          (outCache, outExp, outProperties)
        end

         #= This function elaborates on the builtin operator Connections.uniqueRootIndices.
         TODO: assert size(second arg) <= size(first arg)
         See Modelica_StateGraph2:
          https:github.com/modelica/Modelica_StateGraph2
          and
          https:trac.modelica.org/Modelica/ticket/984
          and
          http:www.ep.liu.se/ecp/043/041/ecp09430108.pdf
         for a specification of this operator =#
        function elabBuiltinUniqueRootIndices(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inNamedArg::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local impl::Bool
                  local aexp1::Absyn.Exp
                  local aexp2::Absyn.Exp
                  local aexp3::Absyn.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local exp3::DAE.Exp
                  local pre::Prefix.PrefixType
                  local dims::DAE.Dimensions
                  local props::DAE.Properties
                  local lst::List{DAE.Exp}
                  local dim::ModelicaInteger
                  local ty::DAE.Type
                @match (inCache, inEnv, inAbsynExpLst, inNamedArg, inBoolean, inPrefix, info) begin
                  (cache, env, aexp1 <| aexp2 <|  nil(),  nil(), _, pre, _)  => begin
                      @match (cache, (@match DAE.ARRAY(array = lst) = exp1), _) = elabExpInExpression(cache, env, aexp1, false, false, pre, info)
                      dim = listLength(lst)
                      (cache, exp2, _) = elabExpInExpression(cache, env, aexp2, false, false, pre, info)
                      exp3 = DAE.SCONST("")
                      ty = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(dim)))
                    (cache, DAE.CALL(Absyn.QUALIFIED("Connections", Absyn.IDENT("uniqueRootIndices")), list(exp1, exp2, exp3), DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())), DAE.PROP(ty, DAE.C_VAR()))
                  end

                  (cache, env, aexp1 <| aexp2 <| _ <|  nil(),  nil(), _, pre, _)  => begin
                      @match (cache, (@match DAE.ARRAY(array = lst) = exp1), _) = elabExpInExpression(cache, env, aexp1, false, false, pre, info)
                      dim = listLength(lst)
                      (cache, exp2, _) = elabExpInExpression(cache, env, aexp2, false, false, pre, info)
                      (cache, exp3, _) = elabExpInExpression(cache, env, aexp2, false, false, pre, info)
                      ty = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(dim)))
                    (cache, DAE.CALL(Absyn.QUALIFIED("Connections", Absyn.IDENT("uniqueRootIndices")), list(exp1, exp2, exp3), DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())), DAE.PROP(ty, DAE.C_VAR()))
                  end

                  (cache, env, aexp1 <| aexp2 <|  nil(), Absyn.NAMEDARG("message", _) <|  nil(), _, pre, _)  => begin
                      @match (cache, (@match DAE.ARRAY(array = lst) = exp1), _) = elabExpInExpression(cache, env, aexp1, false, false, pre, info)
                      dim = listLength(lst)
                      (cache, exp2, _) = elabExpInExpression(cache, env, aexp2, false, false, pre, info)
                      (cache, exp3, _) = elabExpInExpression(cache, env, aexp2, false, false, pre, info)
                      ty = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(dim)))
                    (cache, DAE.CALL(Absyn.QUALIFIED("Connections", Absyn.IDENT("uniqueRootIndices")), list(exp1, exp2, exp3), DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())), DAE.PROP(ty, DAE.C_VAR()))
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in scalar operator.
           For example, scalar({1}) => 1 or scalar({a}) => a =#
        function elabBuiltinScalar(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type
              local scalar_ty::DAE.Type
              local c::DAE.Const
              local dims::List{DAE.Dimension}
              local ty_str::String

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "scalar", inInfo)
              @match (outCache, outExp, DAE.PROP(ty, c)) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImplicit, true, inPrefix, inInfo)
              (scalar_ty, dims) = Types.flattenArrayType(ty)
               #=  Check that any known dimensions have size 1.
               =#
              for dim in dims
                if Expression.dimensionKnown(dim) && Expression.dimensionSize(dim) != 1
                  ty_str = Types.unparseTypeNoAttr(ty)
                  Error.addSourceMessageAndFail(Error.INVALID_ARRAY_DIM_IN_CONVERSION_OP, list(ty_str), inInfo)
                end
              end
               #=  If the argument is an array, make a call to scalar. Otherwise the
               =#
               #=  expression is already a scalar, so return it as it is.
               =#
              if ! listEmpty(dims)
                outExp = Expression.makePureBuiltinCall("scalar", list(outExp), scalar_ty)
              end
              (outExp, _) = ExpressionSimplify.simplify1(outExp)
              outProperties = DAE.PROP(scalar_ty, c)
          (outCache, outExp, outProperties)
        end

         const STRING_ARG_MINLENGTH = SLOT(DAE.FUNCARG("minimumLength", DAE.T_INTEGER_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), false, SOME(DAE.ICONST(0)), nil, 2, SLOT_NOT_EVALUATED)::Slot
         const STRING_ARG_LEFTJUSTIFIED = SLOT(DAE.FUNCARG("leftJustified", DAE.T_BOOL_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), false, SOME(DAE.BCONST(true)), nil, 3, SLOT_NOT_EVALUATED)::Slot
         const STRING_ARG_SIGNIFICANT_DIGITS = SLOT(DAE.FUNCARG("significantDigits", DAE.T_INTEGER_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), false, SOME(DAE.ICONST(6)), nil, 4, SLOT_NOT_EVALUATED)::Slot

         #=
          author: PA
          This function handles the built-in String operator. =#
        function elabBuiltinString(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local exp::DAE.Exp
              local ty::DAE.Type
              local c::DAE.Const
              local args::List{DAE.Exp}
              local consts::List{DAE.Const}
              local val_slot::Slot
              local format_slot::Slot
              local format_arg::Option{DAE.Exp} = NONE()
              local slots::List{Slot}

              try
                e = Absyn.CALL(Absyn.CREF_IDENT("String", nil), Absyn.FUNCTIONARGS(inPosArgs, inNamedArgs))
                (outCache, outExp, outProperties) = OperatorOverloading.string(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
              catch
                e = listHead(inPosArgs)
                @match (outCache, exp, DAE.PROP(ty, c)) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
                if Types.isMetaBoxedType(ty)
                  ty = Types.unboxedType(ty)
                  exp = DAE.UNBOX(exp, ty)
                end
                val_slot = SLOT(DAE.FUNCARG("x", ty, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), false, NONE(), nil, 1, SLOT_NOT_EVALUATED)
                try
                  slots = list(STRING_ARG_MINLENGTH, STRING_ARG_LEFTJUSTIFIED)
                  if Types.isRealOrSubTypeReal(ty)
                    slots = _cons(STRING_ARG_SIGNIFICANT_DIGITS, slots)
                  end
                  slots = _cons(val_slot, slots)
                  (outCache, args, _, consts) = elabInputArgs(outCache, inEnv, inPosArgs, inNamedArgs, slots, false, true, inImplicit, inPrefix, inInfo, DAE.T_UNKNOWN_DEFAULT, Absyn.IDENT("String"))
                catch
                  if Types.isRealOrSubTypeReal(ty)
                    format_arg = SOME(DAE.SCONST("f"))
                  elseif Types.isIntegerOrSubTypeInteger(ty)
                    format_arg = SOME(DAE.SCONST("d"))
                  elseif Types.isString(ty)
                    format_arg = SOME(DAE.SCONST("s"))
                  else
                    format_arg = NONE()
                  end
                  if isSome(format_arg)
                    slots = list(val_slot, SLOT(DAE.FUNCARG("format", DAE.T_STRING_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), false, format_arg, nil, 2, SLOT_NOT_EVALUATED))
                  else
                    slots = list(val_slot)
                  end
                  (outCache, args, _, consts) = elabInputArgs(outCache, inEnv, inPosArgs, inNamedArgs, slots, false, true, inImplicit, inPrefix, inInfo, DAE.T_UNKNOWN_DEFAULT, Absyn.IDENT("String"))
                end
                c = ListUtil.fold(consts, Types.constAnd, DAE.C_CONST(), DAE.Const)
                outExp = Expression.makePureBuiltinCall("String", args, DAE.T_STRING_DEFAULT)
                outProperties = DAE.PROP(DAE.T_STRING_DEFAULT, c)
              end
               #=  Check if 'String' is overloaded.
               =#
               #=  Elaborate the first argument so we know what type we're dealing with.
               =#
               #=  Try the String(val, <option>) format.
               =#
               #=  Only String(Real) has the significantDigits option.
               =#
               #=  Try the String(val, format = s) format.
               =#
          (outCache, outExp, outProperties)
        end

        function elabBuiltinGetInstanceName(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local str::String
              local name::Absyn.Path
              local envName::Absyn.Path

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 0, "getInstanceName", inInfo)
              @match FCore.CACHE(modelName = name) = inCache
              if PrefixUtil.isNoPrefix(inPrefix)
                envName = FGraphUtil.getGraphNameNoImplicitScopes(inEnv)
                str = if AbsynUtil.pathEqual(envName, name)
                      AbsynUtil.pathLastIdent(name)
                    else
                      AbsynUtil.pathString(envName)
                    end
              else
                str = AbsynUtil.pathLastIdent(name) + "." + PrefixUtil.printPrefixStr(inPrefix)
              end
              outExp = DAE.SCONST(str)
              outProperties = DAE.PROP(DAE.T_STRING_DEFAULT, DAE.C_CONST())
          (outCache, outExp, outProperties)
        end

        function elabBuiltinIsPresent(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local str::String
              local direction::Absyn.Direction
              local exp::Absyn.Exp

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "isPresent", info)
              if ! FGraphUtil.inFunctionScope(inEnv)
                Error.addSourceMessage(Error.IS_PRESENT_WRONG_SCOPE, list(SCodeDump.restrString(FGraphUtil.getScopeRestriction(FGraphUtil.currentScope(inEnv)))), info)
              end
              outExp = begin
                @match listGet(inPosArgs, 1) begin
                  Absyn.CREF(Absyn.CREF_IDENT(name = str))  => begin
                      @match (outCache, DAE.TYPES_VAR(attributes = DAE.ATTR(direction = direction)), _, _, _, _) = Lookup.lookupIdentLocal(outCache, inEnv, str)
                      _ = begin
                        @match direction begin
                          Absyn.BIDIR(__)  => begin
                              Error.addSourceMessage(Error.IS_PRESENT_WRONG_DIRECTION, nil, info)
                            fail()
                          end

                          _  => begin
                              ()
                          end
                        end
                      end
                    Expression.makeImpureBuiltinCall("isPresent", _cons(DAE.CREF(DAE.CREF_IDENT(str, DAE.T_BOOL_DEFAULT, nil), DAE.T_BOOL_DEFAULT), nil), DAE.T_BOOL_DEFAULT)
                  end

                  exp  => begin
                      Error.addSourceMessage(Error.IS_PRESENT_INVALID_EXP, list(Dump.printExpStr(exp)), info)
                    fail()
                  end
                end
              end
              outProperties = DAE.PROP(DAE.T_BOOL_DEFAULT, DAE.C_VAR())
          (outCache, outExp, outProperties)
        end

         #= This function handles the built in vector operator. =#
        function elabBuiltinVector(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local e::Absyn.Exp
              local ty::DAE.Type
              local arr_ty::DAE.Type
              local exp_ty::DAE.Type
              local el_ty::DAE.Type
              local c::DAE.Const
              local expl::List{DAE.Exp}

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "vector", inInfo)
              e = listHead(inPosArgs)
              @match (outCache, outExp, (@match DAE.PROP(ty, c) = outProperties)) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
               #=  Scalar
               =#
              if Types.isSimpleType(ty)
                arr_ty = Types.liftArray(ty, DAE.DIM_INTEGER(1))
                exp_ty = Types.simplifyType(arr_ty)
                outExp = DAE.ARRAY(exp_ty, true, list(outExp))
                outProperties = DAE.PROP(arr_ty, c)
              elseif Expression.isArray(outExp) || Expression.isMatrix(outExp)
                if Types.numberOfDimensions(ty) != 1
                  checkBuiltinVectorDims(e, inEnv, ty, inPrefix, inInfo)
                  expl = Expression.getArrayOrMatrixContents(outExp)
                  expl = flattenArray(expl)
                  el_ty = Types.arrayElementType(ty)
                  arr_ty = Types.liftArray(el_ty, DAE.DIM_INTEGER(listLength(expl)))
                  outExp = DAE.ARRAY(Types.simplifyType(arr_ty), false, expl)
                  outProperties = DAE.PROP(arr_ty, c)
                end
              else
                ty = Types.liftArray(Types.arrayElementType(ty), DAE.DIM_UNKNOWN())
                exp_ty = Types.simplifyType(ty)
                outExp = Expression.makePureBuiltinCall("vector", list(outExp), exp_ty)
                outProperties = DAE.PROP(ty, c)
              end
               #=  vector(scalar) = {scalar}
               =#
               #=  Array or Matrix
               =#
               #=  If the array/matrix has more than one dimension, flatten it into a one-
               =#
               #=  dimensional array. Otherwise, do nothing and return the expression as is.
               =#
               #=  Anything else
               =#
               #=  For any other type of expression, make a call to vector.
               =#
          (outCache, outExp, outProperties)
        end

         #= Checks that the argument to vector has at most one dimension which is larger
           than one, otherwise prints an error and fails. =#
        function checkBuiltinVectorDims(inExp::Absyn.Exp, inEnv::FCore.Graph, inType::DAE.Type, inPrefix::Prefix.PrefixType, inInfo::SourceInfo)
              local found_dim_sz_one::Bool = false
              local dims::List{ModelicaInteger}
              local arg_str::String
              local scope_str::String
              local dim_str::String
              local pre_str::String

              dims = Types.getDimensionSizes(inType)
              for dim in dims
                if dim > 1
                  if found_dim_sz_one
                    scope_str = FGraphUtil.printGraphPathStr(inEnv)
                    arg_str = "vector(" + Dump.printExpStr(inExp) + ")"
                    dim_str = "[" + stringDelimitList(list(intString(d) for d in dims), ", ") + "]"
                    pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                    Error.addSourceMessageAndFail(Error.BUILTIN_VECTOR_INVALID_DIMENSIONS, list(scope_str, pre_str, dim_str, arg_str), inInfo)
                  else
                    found_dim_sz_one = true
                  end
                end
              end
        end

        function flattenArray(arr::List{<:DAE.Exp}) ::List{DAE.Exp}
              local flattenedExpl::List{DAE.Exp}

              flattenedExpl = begin
                  local e::DAE.Exp
                  local expl::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local rest_expl::List{DAE.Exp}
                @match arr begin
                   nil()  => begin
                    nil
                  end

                  DAE.ARRAY(array = expl) <| rest_expl  => begin
                      expl = flattenArray(expl)
                      expl2 = flattenArray(rest_expl)
                      expl2 = listAppend(expl, expl2)
                    expl2
                  end

                  DAE.MATRIX(matrix = e <|  nil() <|  nil()) <| rest_expl  => begin
                      expl = flattenArray(rest_expl)
                    _cons(e, expl)
                  end

                  e <| expl  => begin
                      expl = flattenArray(expl)
                    _cons(e, expl)
                  end
                end
              end
          flattenedExpl
        end

         #= Elaborates the builtin matrix function. =#
        function elabBuiltinMatrix(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImpl::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local ty::DAE.Type

              checkBuiltinCallArgs(inPosArgs, inNamedArgs, 1, "matrix", inInfo)
              (outCache, outExp, outProperties) = elabExpInExpression(inCache, inEnv, listHead(inPosArgs), inImpl, true, inPrefix, inInfo)
              ty = Types.getPropType(outProperties)
              (outExp, outProperties) = elabBuiltinMatrix2(inCache, inEnv, outExp, outProperties, ty, inInfo)
          (outCache, outExp, outProperties)
        end

         #= Helper function to elabBuiltinMatrix, evaluates the matrix function given the
           elaborated argument. =#
        function elabBuiltinMatrix2(inCache::FCore.Cache, inEnv::FCore.Graph, inArg::DAE.Exp, inProperties::DAE.Properties, inType::DAE.Type, inInfo::SourceInfo) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProperties) = begin
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local props::DAE.Properties
                  local expl::List{DAE.Exp}
                  local ety::DAE.Type
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local scalar::Bool
                   #=  Scalar
                   =#
                @match inArg begin
                  _ where (Types.isSimpleType(inType))  => begin
                      (exp, props) = promoteExp(inArg, inProperties, 2)
                    (exp, props)
                  end

                  _ where (Types.numberOfDimensions(inType) == 1)  => begin
                       #=  1-dimensional array
                       =#
                      (exp, props) = promoteExp(inArg, inProperties, 2)
                    (exp, props)
                  end

                  DAE.MATRIX(__)  => begin
                    (inArg, inProperties)
                  end

                  DAE.ARRAY(ty = DAE.T_ARRAY(ety, dim1 <| dim2 <| _), scalar = scalar, array = expl)  => begin
                       #=  Matrix
                       =#
                       #=  n-dimensional array
                       =#
                      expl = ListUtil.map1(expl, elabBuiltinMatrix3, inInfo)
                      ty = Types.arrayElementType(inType)
                      ty = Types.liftArrayListDims(ty, list(dim1, dim2))
                      props = Types.setPropType(inProperties, ty)
                    (DAE.ARRAY(DAE.T_ARRAY(ety, list(dim1, dim2)), scalar, expl), props)
                  end
                end
              end
          (outExp, outProperties)
        end

         #= Helper function to elabBuiltinMatrix2. =#
        function elabBuiltinMatrix3(inExp::DAE.Exp, inInfo::SourceInfo) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local ety::DAE.Type
                  local ety2::DAE.Type
                  local scalar::Bool
                  local expl::List{DAE.Exp}
                  local dim::DAE.Dimension
                  local dims::DAE.Dimensions
                  local matrix_expl::List{List{DAE.Exp}}
                @match inExp begin
                  DAE.ARRAY(ty = DAE.T_ARRAY(ety, dim <| _), scalar = scalar, array = expl)  => begin
                      expl = list(arrayScalar(e, 3, "matrix", inInfo) for e in expl)
                    DAE.ARRAY(DAE.T_ARRAY(ety, list(dim)), scalar, expl)
                  end

                  DAE.MATRIX(ty = DAE.T_ARRAY(ety, dim <| dims), matrix = matrix_expl)  => begin
                      ety2 = DAE.T_ARRAY(ety, dims)
                      expl = list(Expression.makeArray(e, ety2, true) for e in matrix_expl)
                      expl = list(arrayScalar(e, 3, "matrix", inInfo) for e in expl)
                    DAE.ARRAY(DAE.T_ARRAY(ety, list(dim)), true, expl)
                  end
                end
              end
          outExp
        end

         #= Returns the scalar value of an array, or prints an error message and fails if
           any dimension of the array isn't of size 1. =#
        function arrayScalar(inExp::DAE.Exp, inDim::ModelicaInteger #= The current dimension, used for error message. =#, inOperator::String #= The current operator name, used for error message. =#, inInfo::SourceInfo) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local exp::DAE.Exp
                  local ty::DAE.Type
                  local expl::List{DAE.Exp}
                  local mexpl::List{List{DAE.Exp}}
                  local dim_str::String
                  local size_str::String
                   #=  An array with one element.
                   =#
                @match inExp begin
                  DAE.ARRAY(array = exp <|  nil())  => begin
                    arrayScalar(exp, inDim + 1, inOperator, inInfo)
                  end

                  DAE.ARRAY(array = expl)  => begin
                       #=  Any other array.
                       =#
                      dim_str = intString(inDim)
                      size_str = intString(listLength(expl))
                      Error.addSourceMessage(Error.INVALID_ARRAY_DIM_IN_CONVERSION_OP, list(dim_str, inOperator, "1", size_str), inInfo)
                    fail()
                  end

                  DAE.MATRIX(ty = ty, matrix = expl <|  nil())  => begin
                    arrayScalar(DAE.ARRAY(ty, true, expl), inDim + 1, inOperator, inInfo)
                  end

                  DAE.MATRIX(matrix = mexpl)  => begin
                       #=  A matrix where the first dimension is 1.
                       =#
                       #=  Any other matrix.
                       =#
                      dim_str = intString(inDim)
                      size_str = intString(listLength(mexpl))
                      Error.addSourceMessage(Error.INVALID_ARRAY_DIM_IN_CONVERSION_OP, list(dim_str, inOperator, "1", size_str), inInfo)
                    fail()
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #=  Anything else is assumed to be a scalar.
               =#
          outExp
        end

         #= This function dispatches the elaboration of builtin operators by returning
           the appropriate function. When a new builtin operator is added, a new rule
           has to be added to this function. =#
        function elabBuiltinHandler(inIdent::String) ::HandlerFunc
              local outHandler::HandlerFunc

              outHandler = begin
                @match inIdent begin
                  "smooth"  => begin
                    elabBuiltinSmooth
                  end

                  "size"  => begin
                    elabBuiltinSize
                  end

                  "ndims"  => begin
                    elabBuiltinNDims
                  end

                  "zeros"  => begin
                    elabBuiltinZeros
                  end

                  "ones"  => begin
                    elabBuiltinOnes
                  end

                  "fill"  => begin
                    elabBuiltinFill
                  end

                  "max"  => begin
                    elabBuiltinMax
                  end

                  "min"  => begin
                    elabBuiltinMin
                  end

                  "transpose"  => begin
                    elabBuiltinTranspose
                  end

                  "symmetric"  => begin
                    elabBuiltinSymmetric
                  end

                  "array"  => begin
                    elabBuiltinArray
                  end

                  "sum"  => begin
                    elabBuiltinSum
                  end

                  "product"  => begin
                    elabBuiltinProduct
                  end

                  "pre"  => begin
                    elabBuiltinPre
                  end

                  "firstTick"  => begin
                    elabBuiltinFirstTick
                  end

                  "interval"  => begin
                    elabBuiltinInterval
                  end

                  "boolean"  => begin
                    elabBuiltinBoolean
                  end

                  "noEvent"  => begin
                    elabBuiltinNoevent
                  end

                  "edge"  => begin
                    elabBuiltinEdge
                  end

                  "der"  => begin
                    elabBuiltinDer
                  end

                  "change"  => begin
                    elabBuiltinChange
                  end

                  "cat"  => begin
                    elabBuiltinCat
                  end

                  "identity"  => begin
                    elabBuiltinIdentity
                  end

                  "vector"  => begin
                    elabBuiltinVector
                  end

                  "matrix"  => begin
                    elabBuiltinMatrix
                  end

                  "scalar"  => begin
                    elabBuiltinScalar
                  end

                  "String"  => begin
                    elabBuiltinString
                  end

                  "rooted"  => begin
                    elabBuiltinRooted
                  end

                  "Integer"  => begin
                    elabBuiltinIntegerEnum
                  end

                  "EnumToInteger"  => begin
                    elabBuiltinIntegerEnum
                  end

                  "inStream"  => begin
                    elabBuiltinInStream
                  end

                  "actualStream"  => begin
                    elabBuiltinActualStream
                  end

                  "getInstanceName"  => begin
                    elabBuiltinGetInstanceName
                  end

                  "classDirectory"  => begin
                    elabBuiltinClassDirectory
                  end

                  "sample"  => begin
                    elabBuiltinSample
                  end

                  "cardinality"  => begin
                    elabBuiltinCardinality
                  end

                  "homotopy"  => begin
                    elabBuiltinHomotopy
                  end

                  "DynamicSelect"  => begin
                    elabBuiltinDynamicSelect
                  end

                  "Clock"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinClock
                  end

                  "hold"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinHold
                  end

                  "shiftSample"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinShiftSample
                  end

                  "backSample"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinBackSample
                  end

                  "noClock"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinNoClock
                  end

                  "transition"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinTransition
                  end

                  "initialState"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinInitialState
                  end

                  "activeState"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinActiveState
                  end

                  "ticksInState"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinTicksInState
                  end

                  "timeInState"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    elabBuiltinTimeInState
                  end

                  "sourceInfo"  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    elabBuiltinSourceInfo
                  end

                  "SOME"  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    elabBuiltinSome
                  end

                  "NONE"  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    elabBuiltinNone
                  end

                  "isPresent"  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    elabBuiltinIsPresent
                  end
                end
              end
          outHandler
        end

         #= Returns true if the function name given as argument
          is a builtin function, which either has a elabBuiltinHandler function
          or can be found in the builtin environment. =#
        function isBuiltinFunc(inPath::Absyn.Path #= the path of the found function =#, ty::DAE.Type) ::Tuple{DAE.FunctionBuiltin, Bool, Absyn.Path}
              local outPath::Absyn.Path #= make the path non-FQ =#
              local b::Bool
              local isBuiltin::DAE.FunctionBuiltin

              (isBuiltin, b, outPath) = begin
                  local id::String
                  local path::Absyn.Path
                @matchcontinue (inPath, ty) begin
                  (path, DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isBuiltin = isBuiltin && DAE.FUNCTION_BUILTIN(_))))  => begin
                      path = AbsynUtil.makeNotFullyQualified(path)
                    (isBuiltin, true, path)
                  end

                  (path, DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isBuiltin = isBuiltin && DAE.FUNCTION_BUILTIN_PTR(__))))  => begin
                      path = AbsynUtil.makeNotFullyQualified(path)
                    (isBuiltin, false, path)
                  end

                  (Absyn.IDENT(name = id), _)  => begin
                      elabBuiltinHandler(id)
                    (DAE.FUNCTION_BUILTIN(SOME(id), false), true, inPath)
                  end

                  (Absyn.FULLYQUALIFIED(path), _)  => begin
                      @match ((@match DAE.FUNCTION_BUILTIN() = isBuiltin), _, path) = isBuiltinFunc(path, ty)
                    (isBuiltin, true, path)
                  end

                  (Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), _)  => begin
                    (DAE.FUNCTION_BUILTIN(NONE(), false), true, inPath)
                  end

                  _  => begin
                      (DAE.FUNCTION_NOT_BUILTIN(), false, inPath)
                  end
                end
              end
          (isBuiltin, b, outPath #= make the path non-FQ =#)
        end

         #= This function elaborates on builtin operators (such as \\\"pre\\\", \\\"der\\\" etc.),
           by calling the builtin handler to retrieve the correct function to call. =#
        function elabCallBuiltin(inCache::FCore.Cache, inEnv::FCore.Graph, inFnName::Absyn.ComponentRef, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local handler::HandlerFunc
                  local cr::Absyn.ComponentRef
                @match inFnName begin
                  Absyn.CREF_IDENT(subscripts =  nil())  => begin
                      handler = elabBuiltinHandler(inFnName.name)
                    handler(inCache, inEnv, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "isRoot"))  => begin
                    elabBuiltinIsRoot(inCache, inEnv, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "uniqueRootIndices"))  => begin
                      Error.addSourceMessage(Error.NON_STANDARD_OPERATOR, list("Connections.uniqueRootIndices"), inInfo)
                    elabBuiltinUniqueRootIndices(inCache, inEnv, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "rooted"))  => begin
                    elabBuiltinRooted(inCache, inEnv, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
                  end

                  Absyn.CREF_FULLYQUALIFIED(cr)  => begin
                    elabCallBuiltin(inCache, inEnv, cr, inPosArgs, inNamedArgs, inImplicit, inPrefix, inInfo)
                  end
                end
              end
          (outCache, outExp, outProperties)
        end

         #= This function elaborates on a function call.  It converts the name to a
           Absyn.Path, and used the Static.elabCallArgs to do the rest of the work. =#
        function elabCall(cache::FCore.Cache, env::FCore.Graph, fn::Absyn.ComponentRef, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local prop::DAE.Properties
              local e::DAE.Exp


              local numErrorMessages::ModelicaInteger = Error.getNumErrorMessages()
              local handles::List{ModelicaInteger}
              local name::String
              local s::String
              local s1::String
              local s2::String

              if hasBuiltInHandler(fn)
                try
                  (cache, e, prop) = elabCallBuiltin(cache, env, fn, args, nargs, impl, pre, info) #= Built in functions (e.g. \\\"pre\\\", \\\"der\\\"), have only possitional arguments =#
                  return (cache, e, prop)
                catch
                  @match true = numErrorMessages == Error.getNumErrorMessages()
                  name = AbsynUtil.printComponentRefStr(fn)
                  s1 = stringDelimitList(ListUtil.map(args, Dump.printExpStr), ", ")
                  s2 = stringDelimitList(ListUtil.map(nargs, Dump.printNamedArgStr), ", ")
                  s = if s2 == ""
                        s1
                      else
                        s1 + ", " + s2
                      end
                  s = stringAppendList(list(name, "(", s, ").\\n"))
                  Error.addSourceMessage(Error.WRONG_TYPE_OR_NO_OF_ARGS, list(s, PrefixUtil.printPrefixStr3(pre)), info)
                  fail()
                end
              end
              handles = nil
              (cache, e, prop) = begin
                  local fn_1::Absyn.Path
                  local fnstr::String
                  local argstr::String
                  local prestr::String
                  local env_str::String
                  local argstrs::List{String}
                   #=  Interactive mode
                   =#
                @matchcontinue () begin
                  ()  => begin
                      ErrorExt.setCheckpoint("elabCall_InteractiveFunction")
                      fn_1 = AbsynUtil.crefToPath(fn)
                      (cache, e, prop) = elabCallArgs(cache, env, fn_1, args, nargs, impl, pre, info)
                      ErrorExt.delCheckpoint("elabCall_InteractiveFunction")
                    (cache, e, prop)
                  end

                  ()  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Static.elabCall failed\\n")
                      Debug.trace(" function: ")
                      fnstr = Dump.printComponentRefStr(fn)
                      Debug.trace(fnstr)
                      Debug.trace("   posargs: ")
                      argstrs = ListUtil.map(args, Dump.printExpStr)
                      argstr = stringDelimitList(argstrs, ", ")
                      Debug.traceln(argstr)
                      Debug.trace(" prefix: ")
                      prestr = PrefixUtil.printPrefixStr(pre)
                      Debug.traceln(prestr)
                    fail()
                  end

                  ()  => begin
                       #= /* Handle the scripting interface */ =#
                       @assert(false, "no support for interactive calls!")
                      #(cache, e, prop) = BackendInterface.elabCallInteractive(cache, env, fn, args, nargs, impl, pre, info) #= Elaborate interactive function calls, such as simulate(), plot() etc. =#
                    (cache, e, prop)
                  end
                end
              end
          (cache, e, prop)
        end

         #= Determine if a function has a builtin handler or not. =#
        function hasBuiltInHandler(fn::Absyn.ComponentRef) ::Bool
              local b::Bool

              b = begin
                  local cr::Absyn.ComponentRef
                  local name::String
                @matchcontinue fn begin
                  Absyn.CREF_IDENT(name = name, subscripts =  nil())  => begin
                      elabBuiltinHandler(name)
                    true
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "isRoot"))  => begin
                    true
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "uniqueRootIndices"))  => begin
                    true
                  end

                  Absyn.CREF_QUAL(name = "Connections", componentRef = Absyn.CREF_IDENT(name = "rooted"))  => begin
                    true
                  end

                  Absyn.CREF_FULLYQUALIFIED(cr)  => begin
                    hasBuiltInHandler(cr)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= This function elaborates variablenames to DAE.Expression. A variablename can
          be used in e.g. plot(model,{v1{3},v2.t}) It should only be used in interactive
          functions that uses variablenames as componentreferences.
         =#
        function elabVariablenames(inExpl::List{<:Absyn.Exp}) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp} = nil

              local exp::DAE.Exp
              local cr::Absyn.ComponentRef

              outExpl = list(begin
                @match e begin
                  Absyn.CREF(__)  => begin
                    DAE.CODE(Absyn.C_VARIABLENAME(e.componentRef), DAE.T_UNKNOWN_DEFAULT)
                  end

                  Absyn.CALL(Absyn.CREF_IDENT(name = "der"), Absyn.FUNCTIONARGS(Absyn.CREF(__) <|  nil(),  nil()))  => begin
                    DAE.CODE(Absyn.C_EXPRESSION(e), DAE.T_UNKNOWN_DEFAULT)
                  end
                end
              end for e in inExpl)
          outExpl
        end

        function getOptionalNamedArgExpList(name::String, nargs::List{<:Absyn.NamedArg}) ::List{DAE.Exp}
              local out::List{DAE.Exp}

              out = begin
                  local absynExpList::List{Absyn.Exp}
                  local argName::String
                  local rest::List{Absyn.NamedArg}
                @matchcontinue nargs begin
                   nil()  => begin
                    nil
                  end

                  Absyn.NAMEDARG(argName = argName, argValue = Absyn.ARRAY(arrayExp = absynExpList)) <| _  => begin
                      @match true = stringEq(name, argName)
                    absynExpListToDaeExpList(absynExpList)
                  end

                  _ <| rest  => begin
                    getOptionalNamedArgExpList(name, rest)
                  end
                end
              end
          out
        end

        function absynExpListToDaeExpList(absynExpList::List{<:Absyn.Exp}) ::List{DAE.Exp}
              local out::List{DAE.Exp}

              out = begin
                  local daeExpList::List{DAE.Exp}
                  local absynRest::List{Absyn.Exp}
                  local absynCr::Absyn.ComponentRef
                  local absynPath::Absyn.Path
                  local daeCr::DAE.ComponentRef
                  local crefExp::DAE.Exp
                @match absynExpList begin
                   nil()  => begin
                    nil
                  end

                  Absyn.CREF(componentRef = absynCr) <| absynRest  => begin
                      absynPath = AbsynUtil.crefToPath(absynCr)
                      daeCr = ComponentReference.pathToCref(absynPath)
                      crefExp = Expression.crefExp(daeCr)
                      daeExpList = absynExpListToDaeExpList(absynRest)
                    _cons(crefExp, daeExpList)
                  end

                  _ <| absynRest  => begin
                    absynExpListToDaeExpList(absynRest)
                  end
                end
              end
          out
        end

         #= This function is used to 'elaborate' interactive functions' optional parameters,
           e.g. simulate(A.b, startTime=1), startTime is an optional parameter. =#
        function getOptionalNamedArg(inCache::FCore.Cache, inEnv::FCore.Graph, inImplicit::Bool, inArgName::String, inType::DAE.Type, inArgs::List{<:Absyn.NamedArg}, inDefaultExp::DAE.Exp, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp}
              local outExp::DAE.Exp = inDefaultExp
              local outCache::FCore.Cache = inCache

              local name::String
              local exp_str::String
              local ty_str::String
              local ety_str::String
              local ty::DAE.Type
              local e::Absyn.Exp
              local ty_match::Bool

              for arg in inArgs
                @match Absyn.NAMEDARG(argName = name) = arg
                if name == inArgName
                  try
                    @match Absyn.NAMEDARG(argValue = e) = arg
                    @match (outCache, outExp, DAE.PROP(type_ = ty)) = elabExpInExpression(inCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
                    (outExp, _) = Types.matchType(outExp, ty, inType, true)
                  catch
                  end
                  break
                end
              end
               #=  Found the argument, try to evaluate it.
               =#
               #=  The argument couldn't be evaluated, possibly due to having the wrong
               =#
               #=  type. We should print an error for this, but some API functions like
               =#
               #=  simulate depend on the default arguments having the wrong type.
               =#
          (outCache, outExp)
        end

         #= This function elaborates a ComponentRef without adding type information.
           Environment is passed along, such that constant subscripts can be elabed
           using existing functions. =#
        function elabUntypedCref(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outCref::DAE.ComponentRef
              local outCache::FCore.Cache

              outCref = begin
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match inCref begin
                  Absyn.CREF_IDENT(__)  => begin
                      (outCache, subs) = elabSubscripts(inCache, inEnv, inCref.subscripts, inImplicit, inPrefix, inInfo)
                    ComponentReference.makeCrefIdent(inCref.name, DAE.T_UNKNOWN_DEFAULT, subs)
                  end

                  Absyn.CREF_QUAL(__)  => begin
                      (outCache, subs) = elabSubscripts(inCache, inEnv, inCref.subscripts, inImplicit, inPrefix, inInfo)
                      (outCache, cr) = elabUntypedCref(outCache, inEnv, inCref.componentRef, inImplicit, inPrefix, inInfo)
                    ComponentReference.makeCrefQual(inCref.name, DAE.T_UNKNOWN_DEFAULT, subs, cr)
                  end
                end
              end
          (outCache, outCref)
        end

        function needToRebuild(newFile::String, oldFile::String, buildTime::ModelicaReal) ::Bool
              local buildNeeded::Bool

              buildNeeded = begin
                  local newf::String
                  local oldf::String
                  local bt::ModelicaReal
                  local nfmt::ModelicaReal
                @matchcontinue (newFile, oldFile) begin
                  ("", "")  => begin
                    true
                  end

                  (newf, oldf)  => begin
                      @match true = stringEq(newf, oldf)
                      @match SOME(nfmt) = System.getFileModificationTime(newf)
                      @match true = realGt(buildTime, nfmt)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  rebuild all the time if the function has no file!
               =#
               #=  the files should be the same!
               =#
               #=  the new file nf should have an older modification time than the last build
               =#
               #=  the file was not modified since last build
               =#
          buildNeeded
        end

        function createDummyFarg(name::String) ::DAE.FuncArg
              local farg::DAE.FuncArg

              farg = DAE.FUNCARG(name, DAE.T_UNKNOWN_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())
          farg
        end

         #=
        function: elabCallArgs
          Given the name of a function and two lists of expression and
          NamedArg respectively to be used
          as actual arguments in a function call to that function, this
          function finds the function definition and matches the actual
          arguments to the formal parameters. =#
        function elabCallArgs(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path, inAbsynExpLst::List{<:Absyn.Exp}, inAbsynNamedArgLst::List{<:Absyn.NamedArg}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              @match (outCache, SOME((outExp, outProperties))) = elabCallArgs2(inCache, inEnv, inPath, inAbsynExpLst, inAbsynNamedArgLst, inBoolean, Mutable.create(false), inPrefix, info, Error.getNumErrorMessages())
              (outCache, outProperties) = elabCallArgsEvaluateArrayLength(outCache, inEnv, outProperties, inPrefix, info)
          (outCache, outExp, outProperties)
        end

         #= Evaluate array dimensions in the returned type. For a call f(n) we might get
           Integer[n] back, where n is a parameter expression.  We consider any such
           parameter structural since it decides the dimension of an array.  We fall
           back to not evaluating the parameter if we fail since the dimension may not
           be structural (used in another call or reduction, etc). =#
        function elabCallArgsEvaluateArrayLength(inCache::FCore.Cache, env::FCore.Graph, inProperties::DAE.Properties, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Properties}
              local outProperties::DAE.Properties
              local outCache::FCore.Cache

              local ty::DAE.Type

              try
                @match true = FGraphUtil.checkScopeType(list(FGraphUtil.lastScopeRef(env)), SOME(FCore.CLASS_SCOPE()))
                ty = Types.getPropType(inProperties)
                (ty, (outCache, _)) = Types.traverseType(ty, (inCache, env), elabCallArgsEvaluateArrayLength2)
                outProperties = Types.setPropType(inProperties, ty)
              catch
                outCache = inCache
                outProperties = inProperties
              end
               #=  Unsure if we want to evaluate dimensions inside function scope.
               =#
               #=  Last scope ref in env is a class scope.
               =#
          (outCache, outProperties)
        end

        function elabCallArgsEvaluateArrayLength2(ty::DAE.Type, inTpl::Tuple{<:FCore.Cache, FCore.Graph}) ::Tuple{DAE.Type, Tuple{FCore.Cache, FCore.Graph}}
              local outTpl::Tuple{FCore.Cache, FCore.Graph}
              local oty::DAE.Type = ty

              (oty, outTpl) = begin
                  local tpl::Tuple{FCore.Cache, FCore.Graph}
                  local dims::DAE.Dimensions
                @matchcontinue (oty, inTpl) begin
                  (DAE.T_ARRAY(__), tpl)  => begin
                      (dims, tpl) = ListUtil.mapFold(oty.dims, elabCallArgsEvaluateArrayLength3, tpl)
                      oty.dims = dims
                    (oty, tpl)
                  end

                  _  => begin
                      (oty, inTpl)
                  end
                end
              end
          (oty, outTpl)
        end

        function elabCallArgsEvaluateArrayLength3(inDim::DAE.Dimension, inTpl::Tuple{<:FCore.Cache, FCore.Graph}) ::Tuple{DAE.Dimension, Tuple{FCore.Cache, FCore.Graph}}
              local outTpl::Tuple{FCore.Cache, FCore.Graph}
              local outDim::DAE.Dimension

              (outDim, outTpl) = begin
                  local i::ModelicaInteger
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @matchcontinue (inDim, inTpl) begin
                  (DAE.DIM_EXP(exp), (cache, env))  => begin
                      @match (cache, Values.INTEGER(i)) = Ceval.ceval(cache, env, exp, false, Absyn.NO_MSG(), 0)
                    (DAE.DIM_INTEGER(i), (cache, env))
                  end

                  _  => begin
                      (inDim, inTpl)
                  end
                end
              end
          (outDim, outTpl)
        end

         #= @author: adrpo
          This function will add the binding expressions for inputs
          to the variable replacement structure. This is needed to
          be able to replace input variables in default values.
          Example: ...  =#
        function createInputVariableReplacements(inSlotLst::List{<:Slot}, inVarsRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local outVarsRepl::VarTransform.VariableReplacements

              outVarsRepl = begin
                  local o::VarTransform.VariableReplacements
                  local id::String
                  local e::DAE.Exp
                  local rest::List{Slot}
                   #=  handle empty
                   =#
                @matchcontinue inSlotLst begin
                   nil()  => begin
                    inVarsRepl
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = id), slotFilled = true, arg = SOME(e)) <| rest  => begin
                       #=  only interested in filled slots that have a optional expression
                       =#
                      o = VarTransform.addReplacement(inVarsRepl, ComponentReference.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil), e)
                    createInputVariableReplacements(rest, o)
                  end

                  _  => begin
                      createInputVariableReplacements(listRest(inSlotLst), inVarsRepl)
                  end
                end
              end
               #=  try the next.
               =#
          outVarsRepl
        end

         #=
        function: elabCallArgs
          Given the name of a function and two lists of expression and
          NamedArg respectively to be used
          as actual arguments in a function call to that function, this
          function finds the function definition and matches the actual
          arguments to the formal parameters. =#
        function elabCallArgs2(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path, inAbsynExpLst::List{<:Absyn.Exp}, inAbsynNamedArgLst::List{<:Absyn.NamedArg}, inBoolean::Bool, stopElab::MutableType #= {<:Bool} =#, inPrefix::Prefix.PrefixType, info::SourceInfo, numErrors::ModelicaInteger) ::Tuple{FCore.Cache, Option{Tuple{DAE.Exp, DAE.Properties}}}
              local expProps::Option{Tuple{DAE.Exp, DAE.Properties}}
              local outCache::FCore.Cache

              (outCache, expProps) = begin
                  local t::DAE.Type
                  local outtype::DAE.Type
                  local restype::DAE.Type
                  local functype::DAE.Type
                  local tp1::DAE.Type
                  local fargs::List{DAE.FuncArg}
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local env::FCore.Graph
                  local classEnv::FCore.Graph
                  local recordEnv::FCore.Graph
                  local slots::List{Slot}
                  local newslots::List{Slot}
                  local newslots2::List{Slot}
                  local args_1::List{DAE.Exp}
                  local args_2::List{DAE.Exp}
                  local constlist::List{DAE.Const}
                  local constInputArgs::List{DAE.Const}
                  local constDefaultArgs::List{DAE.Const}
                  local constType::DAE.Const
                  local tyconst::DAE.TupleConst
                  local prop::DAE.Properties
                  local prop_1::DAE.Properties
                  local cl::SCode.Element
                  local scodeClass::SCode.Element
                  local recordCl::SCode.Element
                  local fn::Absyn.Path
                  local fn_1::Absyn.Path
                  local fqPath::Absyn.Path
                  local utPath::Absyn.Path
                  local fnPrefix::Absyn.Path
                  local componentType::Absyn.Path
                  local correctFunctionPath::Absyn.Path
                  local functionClassPath::Absyn.Path
                  local path::Absyn.Path
                  local args::List{Absyn.Exp}
                  local t4::List{Absyn.Exp}
                  local argexp::Absyn.Exp
                  local nargs::List{Absyn.NamedArg}
                  local translatedNArgs::List{Absyn.NamedArg}
                  local impl::Bool
                  local typelist::List{DAE.Type}
                  local vect_dims::DAE.Dimensions
                  local call_exp::DAE.Exp
                  local callExp::DAE.Exp
                  local daeexp::DAE.Exp
                  local t_lst::List{String}
                  local names::List{String}
                  local fn_str::String
                  local types_str::String
                  local scope::String
                  local pre_str::String
                  local componentName::String
                  local fnIdent::String
                  local s::String
                  local name::String
                  local argStr::String
                  local stringifiedInstanceFunctionName::String
                  local cache::FCore.Cache
                  local tp::DAE.Type
                  local pre::Prefix.PrefixType
                  local re::SCode.Restriction
                  local index::ModelicaInteger
                  local vars::List{DAE.Var}
                  local comps::List{SCode.Element}
                  local innerOuter::Absyn.InnerOuter
                  local operNames::List{Absyn.Path}
                  local cref::Absyn.ComponentRef
                  local daecref::DAE.ComponentRef
                  local func::DAE.Function
                  local source::DAE.ElementSource
                   #= /* Record constructors that might have come from Graphical expressions with unknown array sizes */ =#
                   #= /*
                       * adrpo: HACK! HACK! TODO! remove this case if records with unknown sizes can be instantiated
                       * this could be also fixed by transforming the function call arguments into modifications and
                       * send the modifications as an option in Lookup.lookup* functions!
                       */ =#
                @matchcontinue (inCache, inEnv, inPath, inAbsynExpLst, inAbsynNamedArgLst, inBoolean, inPrefix) begin
                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      @match (cache, (@match SCode.CLASS(restriction = SCode.R_PACKAGE()) = cl), _) = Lookup.lookupClassIdent(cache, env, "GraphicalAnnotationsProgram____")
                      @match (cache, (@match SCode.CLASS(restriction = SCode.R_RECORD(_)) = cl), env_1) = Lookup.lookupClass(cache, env, fn)
                      (cache, cl, env_2) = Lookup.lookupRecordConstructorClass(cache, env_1, fn)
                      (_, _ <| names) = SCodeUtil.getClassComponents(cl)
                      fargs = ListUtil.map(names, createDummyFarg)
                      slots = makeEmptySlots(fargs)
                      (cache, _, newslots, _, _) = elabInputArgs(cache, env, args, nargs, slots, true, false, impl, pre, info, DAE.T_UNKNOWN_DEFAULT, fn, true)
                      (cache, newslots2, _, _) = fillGraphicsDefaultSlots(cache, newslots, cl, env_2, impl, pre, info)
                      args_2 = slotListArgs(newslots2)
                      tp = complexTypeFromSlots(newslots2, ClassInf.UNKNOWN(Absyn.IDENT("")))
                    (cache, SOME((DAE.CALL(fn, args_2, DAE.CALL_ATTR(tp, false, false, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())), DAE.PROP(DAE.T_UNKNOWN_DEFAULT, DAE.C_CONST()))))
                  end

                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      ErrorExt.setCheckpoint("RecordConstructor")
                      (cache, func) = InstFunction.getRecordConstructorFunction(cache, env, fn)
                      @match DAE.RECORD_CONSTRUCTOR(path, tp1, _) = func
                      @match DAE.T_FUNCTION(fargs, outtype, _, path) = tp1
                      slots = makeEmptySlots(fargs)
                      (cache, _, newslots, constInputArgs, _) = elabInputArgs(cache, env, args, nargs, slots, true, true, impl, pre, info, tp1, path)
                      (args_2, newslots2) = addDefaultArgs(newslots, info)
                      vect_dims = slotsVectorizable(newslots2, info)
                      constlist = constInputArgs
                      constType = ListUtil.fold(constlist, Types.constAnd, DAE.C_CONST(), DAE.Const)
                      tyconst = elabConsts(outtype, constType)
                      prop = getProperties(outtype, tyconst)
                      callExp = DAE.CALL(path, args_2, DAE.CALL_ATTR(outtype, false, false, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
                      (call_exp, prop_1) = vectorizeCall(callExp, vect_dims, newslots2, prop, info)
                      expProps = SOME((call_exp, prop_1))
                      Mutable.update(stopElab, true)
                      ErrorExt.rollBack("RecordConstructor")
                    (cache, expProps)
                  end

                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      @match false = Mutable.access(stopElab)
                      (cache, recordCl, recordEnv) = Lookup.lookupClass(cache, env, fn)
                      @match true = SCodeUtil.isOperatorRecord(recordCl)
                      fn_1 = AbsynUtil.joinPaths(fn, Absyn.IDENT("'constructor'"))
                      (cache, recordCl, recordEnv) = Lookup.lookupClass(cache, recordEnv, fn_1)
                      @match true = SCodeUtil.isOperator(recordCl)
                      operNames = AbsynToSCode.getListofQualOperatorFuncsfromOperator(recordCl)
                      @match (cache, typelist && _ <| _) = Lookup.lookupFunctionsListInEnv(cache, recordEnv, operNames, info, nil)
                      Mutable.update(stopElab, true)
                      (cache, expProps) = elabCallArgs3(cache, env, typelist, fn_1, args, nargs, impl, pre, info)
                      ErrorExt.rollBack("RecordConstructor")
                    (cache, expProps)
                  end

                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      ErrorExt.delCheckpoint("RecordConstructor")
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopElab)
                      @match (cache, t, _) = Lookup.lookupType(cache, env, fn, NONE())
                      @match DAE.T_METARECORD() = t
                      Mutable.update(stopElab, true)
                      (cache, expProps) = elabCallArgsMetarecord(cache, env, t, args, nargs, impl, stopElab, pre, info)
                    (cache, expProps)
                  end

                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      ErrorExt.setCheckpoint("elabCallArgs2FunctionLookup")
                      @match false = Mutable.access(stopElab)
                      @match (cache, typelist && _ <| _) = Lookup.lookupFunctionsInEnv(cache, env, fn, info) #= PR. A function can have several types. Taking an array with
                               different dimensions as parameter for example. Because of this we
                               cannot just lookup the function name and trust that it
                               returns the correct function. It returns just one
                               functiontype of several possibilites. The solution is to send
                               in the function type of the user function and check both the
                               function name and the function\\'s type. =#
                      Mutable.update(stopElab, true)
                      (cache, expProps) = elabCallArgs3(cache, env, typelist, fn, args, nargs, impl, pre, info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, expProps)
                  end

                  (cache, env, fn, args, nargs, impl, pre)  => begin
                      @match (cache, typelist && tp1 <| _) = Lookup.lookupFunctionsInEnv(cache, env, fn, info)
                      (cache, args_1, _, _, functype, _, _) = elabTypes(cache, env, args, nargs, typelist, true, false, impl, pre, info)
                      argStr = ExpressionDump.printExpListStr(args_1)
                      pre_str = PrefixUtil.printPrefixStr3(pre)
                      fn_str = AbsynUtil.pathString(fn) + "(" + argStr + ")\\nof type\\n  " + Types.unparseType(functype)
                      types_str = "\\n  " + Types.unparseType(tp1)
                      Error.assertionOrAddSourceMessage(Error.getNumErrorMessages() != numErrors, Error.NO_MATCHING_FUNCTION_FOUND, list(fn_str, pre_str, types_str), info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, NONE())
                  end

                  (cache, env, fn, _, _, _, _)  => begin
                      @match (cache, SCode.CLASS(restriction = re), _) = Lookup.lookupClass(cache, env, fn)
                      @match false = SCodeUtil.isFunctionRestriction(re)
                      fn_str = AbsynUtil.pathString(fn)
                      s = SCodeDump.restrString(re)
                      Error.addSourceMessage(Error.LOOKUP_FUNCTION_GOT_CLASS, list(fn_str, s), info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, NONE())
                  end

                  (cache, env, fn, _, _, _, pre)  => begin
                      @match (cache, typelist && _ <| _ <| _) = Lookup.lookupFunctionsInEnv(cache, env, fn, info)
                      t_lst = ListUtil.map(typelist, Types.unparseType)
                      fn_str = AbsynUtil.pathString(fn)
                      pre_str = PrefixUtil.printPrefixStr3(pre)
                      types_str = stringDelimitList(t_lst, "\\n -")
                      Error.addSourceMessage(Error.NO_MATCHING_FUNCTION_FOUND, list(fn_str, pre_str, types_str), info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, NONE())
                  end

                  (cache, env, fn, Absyn.CREF(Absyn.CREF_IDENT(name, _)) <|  nil(), _, impl, pre) where (Config.acceptOptimicaGrammar())  => begin
                      cref = AbsynUtil.pathToCref(fn)
                      @match (cache, SOME(((@match DAE.CREF(daecref, tp) = daeexp), prop, _))) = elabCref(cache, env, cref, impl, true, pre, info)
                      ErrorExt.rollBack("elabCallArgs2FunctionLookup")
                      daeexp = DAE.CREF(DAE.OPTIMICA_ATTR_INST_CREF(daecref, name), tp)
                      expProps = SOME((daeexp, prop))
                    (cache, expProps)
                  end

                  (cache, env, fn, _, _, _, _)  => begin
                      @shouldFail (_, _, _) = Lookup.lookupType(cache, env, fn, NONE()) #= msg =#
                      scope = FGraphUtil.printGraphPathStr(env) + " (looking for a function or record)"
                      fn_str = AbsynUtil.pathString(fn)
                      Error.addSourceMessage(Error.LOOKUP_ERROR, list(fn_str, scope), info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, NONE())
                  end

                  (cache, env, fn, _, _, _, pre)  => begin
                      @match (cache, nil) = Lookup.lookupFunctionsInEnv(cache, env, fn, info)
                      fn_str = AbsynUtil.pathString(fn)
                      pre_str = PrefixUtil.printPrefixStr3(pre)
                      fn_str = fn_str + " in component " + pre_str
                      Error.addSourceMessage(Error.NO_MATCHING_FUNCTION_FOUND_NO_CANDIDATE, list(fn_str), info)
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                    (cache, NONE())
                  end

                  (_, env, fn, _, _, _, _)  => begin
                      ErrorExt.delCheckpoint("elabCallArgs2FunctionLookup")
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Static.elabCallArgs failed on: " + AbsynUtil.pathString(fn) + " in env: " + FGraphUtil.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #= /* env */ =#
               #=  remove the first one as it is the result!
               =#
               #= /*
                      (cache,(t as (DAE.T_FUNCTION(fargs,(outtype as (DAE.T_COMPLEX(complexClassType as ClassInf.RECORD(name),_,_,_),_))),_)),env_1)
                        = Lookup.lookupType(cache, env, fn, SOME(info));
                      */ =#
               #= /*checkTypes*/ =#
               #=  Record constructors, user defined or implicit, try the hard stuff first
               =#
               #=  For unrolling errors if an overloaded 'constructor' matches later.
               =#
               #= /* If the default constructor failed and we have an operator record
                      look for overloaded Record constructors (operators), user defined.
                      mahge:TODO move this to a function and call it from above.
                      avoids uneccesary lookup since we already have a record.*/ =#
               #= /* ------ */ =#
               #= /* Metamodelica extension, added by simbj */ =#
               #= /* ..Other functions */ =#
               #= /* no matching type found, with -one- candidate */ =#
               #= /* Do not check types*/ =#
               #= /* class found; not function */ =#
               #= /* no matching type found, with candidates */ =#
               #= fn_str = fn_str + \" in component \" + pre_str;
               =#
               #=  In Optimica there is an odd syntax like for eg.,  x(finalTime) + y(finalTime); where both x and y are normal variables
               =#
               #=  not functions. So it is not really a call Exp but the compiler treats it as if it is up until this point.
               =#
               #=  This is a kind of trick to handle that.
               =#
               #=  No need to add prefix because only depends on scope?
               =#
               #= /* no matching type found, no candidates. */ =#
          (outCache, expProps)
        end

         #= Elaborates the input given a set of viable function candidates, and vectorizes the arguments+performs type checking =#
        function elabCallArgs3(inCache::FCore.Cache, inEnv::FCore.Graph, typelist::List{<:DAE.Type}, fn::Absyn.Path, args::List{<:Absyn.Exp}, nargs::List{<:Absyn.NamedArg}, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, Option{Tuple{DAE.Exp, DAE.Properties}}}
              local expProps::Option{Tuple{DAE.Exp, DAE.Properties}}
              local outCache::FCore.Cache

              local callExp::DAE.Exp
              local call_exp::DAE.Exp
              local args_1::List{DAE.Exp}
              local args_2::List{DAE.Exp}
              local constlist::List{DAE.Const}
              local constType::DAE.Const
              local restype::DAE.Type
              local functype::DAE.Type
              local isBuiltin::DAE.FunctionBuiltin
              local funcParal::DAE.FunctionParallelism
              local isPure::Bool
              local tuple_::Bool
              local builtin::Bool
              local isImpure::Bool
              local inlineType::DAE.InlineType
              local fn_1::Absyn.Path
              local prop::DAE.Properties
              local prop_1::DAE.Properties
              local tp::DAE.Type
              local tyconst::DAE.TupleConst
              local vect_dims::DAE.Dimensions
              local slots::List{Slot}
              local slots2::List{Slot}
              local functionTree::DAE.FunctionTree
              local status::Util.Status
              local cache::FCore.Cache
              local didInline::Bool
              local b::Bool
              local onlyOneFunction::Bool
              local isFunctionPointer::Bool

              onlyOneFunction = listLength(typelist) == 1
              @match (cache, args_1, constlist, restype, functype, vect_dims, slots) =
                elabTypes(inCache, inEnv, args, nargs, typelist, onlyOneFunction, true, impl, pre, info) #= The constness of a function depends on the inputs. If all inputs are constant the call itself is constant. =#
              @match DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isOpenModelicaPure = isPure, isImpure = isImpure, inline = inlineType, isFunctionPointer = isFunctionPointer, functionParallelism = funcParal)) = functype
               #= /* Check types*/ =#
              (fn_1, functype) = deoverloadFuncname(fn, functype, inEnv)
              tuple_ = Types.isTuple(restype)
              (isBuiltin, builtin, fn_1) = isBuiltinFunc(fn_1, functype)
              inlineType = inlineBuiltin(isBuiltin, inlineType)
               #= check the env to see if a call to a parallel or kernel function is a valid one.
               =#
              @match true = isValidWRTParallelScope(fn, builtin, funcParal, inEnv, info)
              constType = ListUtil.fold(constlist, Types.constAnd, DAE.C_CONST(), DAE.Const)
              constType = if Flags.isSet(Flags.RML) && ! builtin || ! isPure
                    DAE.C_VAR()
                  else
                    constType
                  end #= in RML no function needs to be ceval'ed; this speeds up compilation significantly when bootstrapping =#
              (cache, constType) = determineConstSpecialFunc(cache, inEnv, constType, fn_1)
              tyconst = elabConsts(restype, constType)
              prop = getProperties(restype, tyconst)
              tp = Types.simplifyType(restype)
               #=  adrpo: 2011-09-30 NOTE THAT THIS WILL NOT ADD DEFAULT ARGS
               =#
               #=                    FROM extends (THE BASE CLASS)
               =#
              (args_2, slots2) = addDefaultArgs(slots, info)
               #=  DO NOT CHECK IF ALL SLOTS ARE FILLED!
               =#
              @match true = ListUtil.fold(slots2, slotAnd, true)
              callExp = DAE.CALL(fn_1, args_2, DAE.CALL_ATTR(tp, tuple_, builtin, isImpure || ! isPure, isFunctionPointer, inlineType, DAE.NO_TAIL()))
               #=  ExpressionDump.dumpExpWithTitle(\"function elabCallArgs3: \", callExp);
               =#
               #=  create a replacement for input variables -> their binding
               =#
               #= inputVarsRepl = createInputVariableReplacements(slots2, VarTransform.emptyReplacements());
               =#
               #= print(\"Repls: \" + VarTransform.dumpReplacementsStr(inputVarsRepl) + \"\\n\");
               =#
               #=  replace references to inputs in the arguments
               =#
               #= callExp = VarTransform.replaceExp(callExp, inputVarsRepl, NONE());
               =#
               #= debugPrintString = if_(Util.isEqual(DAE.NORM_INLINE,inline),\" Inline: \" + AbsynUtil.pathString(fn_1) + \"\\n\", \"\");print(debugPrintString);
               =#
              (call_exp, prop_1) = vectorizeCall(callExp, vect_dims, slots2, prop, info)
               #=  print(\"3 Prefix: \" + PrefixUtil.printPrefixStr(pre) + \" path: \" + AbsynUtil.pathString(fn_1) + \"\\n\");
               =#
               #=  Instantiate the function and add to dae function tree
               =#
              (cache, status) = instantiateDaeFunction(cache, inEnv, if Lookup.isFunctionCallViaComponent(cache, inEnv, fn)
                    fn
                  else
                    fn_1
                  end, builtin, NONE(), true)
               #=  don't use the fully qualified name for calling component functions
               =#
               #=  Instantiate any implicit record constructors needed and add them to the dae function tree
               =#
              cache = instantiateImplicitRecordConstructors(cache, inEnv, args_1)
              functionTree = FCoreUtil.getFunctionTree(cache)
              (call_exp, _, didInline, _) = Inline.inlineExp(call_exp, (SOME(functionTree), list(DAE.BUILTIN_EARLY_INLINE(), DAE.EARLY_INLINE())), DAE.emptyElementSource)
              (call_exp, _) = ExpressionSimplify.condsimplify(didInline, call_exp)
              didInline = didInline && ! Config.acceptMetaModelicaGrammar()
               #= /* Some weird errors when inlining. Becomes boxed even if it shouldn't... */ =#
              prop_1 = if didInline
                    Types.setPropType(prop_1, restype)
                  else
                    prop_1
                  end
              if ! isImpure
                (cache, call_exp, prop_1) = Ceval.cevalIfConstant(cache, inEnv, call_exp, prop_1, impl, info)
              end
              expProps = if Util.isSuccess(status)
                    SOME((call_exp, prop_1))
                  else
                    NONE()
                  end
              outCache = cache
          (outCache, expProps)
        end

        function inlineBuiltin(isBuiltin::DAE.FunctionBuiltin, inlineType::DAE.InlineType) ::DAE.InlineType
              local outInlineType::DAE.InlineType

              outInlineType = begin
                @match isBuiltin begin
                  DAE.FUNCTION_BUILTIN_PTR(__)  => begin
                    DAE.BUILTIN_EARLY_INLINE()
                  end

                  _  => begin
                      inlineType
                  end
                end
              end
          outInlineType
        end

        function isValidWRTParallelScope(inFn::Absyn.Path, isBuiltin::Bool, inFuncParallelism::DAE.FunctionParallelism, inEnv::FCore.Graph, inInfo::SourceInfo) ::Bool
              local isValid::Bool

              isValid = isValidWRTParallelScope_dispatch(inFn, isBuiltin, inFuncParallelism, FGraphUtil.currentScope(inEnv), inInfo)
          isValid
        end

        function isValidWRTParallelScope_dispatch(inFn::Absyn.Path, isBuiltin::Bool, inFuncParallelism::DAE.FunctionParallelism, inScope::FCore.Scope, inInfo::SourceInfo) ::Bool
              local isValid::Bool

              isValid = begin
                  local scopeName::String
                  local errorString::String
                  local restScope::FCore.Scope
                  local ref::FCore.MMRef
                   #=  non-parallel builtin function call is OK everywhere.
                   =#
                @matchcontinue (inFn, isBuiltin, inFuncParallelism, inScope, inInfo) begin
                  (_, true, DAE.FP_NON_PARALLEL(__), _, _)  => begin
                    true
                  end

                  (_, _, _, ref <| restScope, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = listMember(scopeName, FCore.implicitScopeNames)
                      @match false = stringEq(scopeName, FCore.parForScopeName)
                    isValidWRTParallelScope_dispatch(inFn, isBuiltin, inFuncParallelism, restScope, inInfo)
                  end

                  (_, _, DAE.FP_NON_PARALLEL(__), ref <| _, _)  => begin
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.CLASS_SCOPE()))
                    true
                  end

                  (_, _, DAE.FP_NON_PARALLEL(__), ref <| _, _)  => begin
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.FUNCTION_SCOPE()))
                    true
                  end

                  (_, _, DAE.FP_NON_PARALLEL(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.PARALLEL_SCOPE()))
                      errorString = "\\n" + "- Non-Parallel function '" + AbsynUtil.pathString(inFn) + "' can not be called from a parallel scope." + "\\n" + "- Here called from :" + scopeName + "\\n" + "- Please declare the function as parallel function."
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_PARALLEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.PARALLEL_SCOPE()))
                      @match false = stringEqual(scopeName, AbsynUtil.pathString(inFn))
                    true
                  end

                  (_, _, DAE.FP_PARALLEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.PARALLEL_SCOPE()))
                      @match true = stringEqual(scopeName, AbsynUtil.pathString(inFn))
                      errorString = "\\n" + "- Parallel function '" + AbsynUtil.pathString(inFn) + "' can not call itself. Recurrsion is not allowed for parallel functions currently." + "\\n" + "- Parallel functions can only be called from: 'kernel' functions," + " OTHER 'parallel' functions (no recurrsion) or from a body of a" + " 'parfor' loop"
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_PARALLEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = stringEqual(scopeName, FCore.parForScopeName)
                    true
                  end

                  (_, _, DAE.FP_PARALLEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      errorString = "\\n" + "- Parallel function '" + AbsynUtil.pathString(inFn) + "' can not be called from a non parallel scope '" + scopeName + "'.\\n" + "- Parallel functions can only be called from: 'kernel' functions," + " other 'parallel' functions (no recurrsion) or from a body of a" + " 'parfor' loop"
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_KERNEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = stringEqual(scopeName, AbsynUtil.pathString(inFn))
                      errorString = "\\n" + "- Kernel function '" + AbsynUtil.pathString(inFn) + "' can not call itself. " + "\\n" + "- Recurrsion is not allowed for Kernel functions. "
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_KERNEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = FGraphUtil.checkScopeType(list(ref), SOME(FCore.PARALLEL_SCOPE()))
                      errorString = "\\n" + "- Kernel function '" + AbsynUtil.pathString(inFn) + "' can not be called from a parallel scope '" + scopeName + "'.\\n" + "- Kernel functions CAN NOT be called from: 'kernel' functions," + " 'parallel' functions or from a body of a" + " 'parfor' loop"
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_KERNEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match true = stringEqual(scopeName, FCore.parForScopeName)
                      errorString = "\\n" + "- Kernel function '" + AbsynUtil.pathString(inFn) + "' can not be called from inside parallel for (parfor) loop body." + "'.\\n" + "- Kernel functions CAN NOT be called from: 'kernel' functions," + " 'parallel' functions or from a body of a" + " 'parfor' loop"
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  (_, _, DAE.FP_KERNEL_FUNCTION(__), ref <| _, _)  => begin
                      @match false = FNode.isRefTop(ref)
                      scopeName = FNode.refName(ref)
                      @match false = stringEqual(scopeName, AbsynUtil.pathString(inFn))
                    true
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  If we have a function call in an implicit scope type, then go
               =#
               #=  up recursively to find the actuall scope and then check.
               =#
               #=  But parfor scope is a parallel type so is handled differently.
               =#
               #=  This two are common cases so keep them at the top.
               =#
               #=  normal(non parallel) function call in a normal scope (function and class scopes) is OK.
               =#
               #=  Normal function call in a prallel scope is error, if it is not a built-in function.
               =#
               #=  parallel function call in a parallel scope (kernel function, parallel function) is OK.
               =#
               #=  Except when it is calling itself, recurssion
               =#
               #=  make sure the function is not calling itself
               =#
               #=  recurrsion is not allowed.
               =#
               #=  If the above case failed (parallel function recurssion) this will print the error message
               =#
               #=  make sure the function is not calling itself
               =#
               #=  recurrsion is not allowed.
               =#
               #=  parallel function call in a parfor scope is OK.
               =#
               #= parallel function call in non parallel scope types is error.
               =#
               #=  Kernel functions should not call themselves.
               =#
               #=  make sure the function is not calling itself
               =#
               #=  recurrsion is not allowed.
               =#
               #= kernel function call in a parallel scope (kernel function, parallel function) is Error.
               =#
               #= kernel function call in a parfor loop is Error too (similar to above). just different error message.
               =#
               #=  Kernel function call in a non-parallel scope is OK.
               =#
               #=  Except when it is calling itself, recurssion
               =#
               #=  make sure the function is not calling itself
               =#
               #=  recurrsion is not allowed.
               =#
               #= /*
                  Normal (non parallel) function call in a normal function scope is OK.
                  case(DAE.FP_NON_PARALLEL(), FCore.N(scopeType = FCore.FUNCTION_SCOPE())) then();
                  Normal (non parallel) function call in a normal class scope is OK.
                  case(DAE.FP_NON_PARALLEL(), FCore.N(scopeType = FCore.CLASS_SCOPE())) then();
                  Normal (non parallel) function call in a normal function scope is OK.
                  case(DAE.FP_NON_PARALLEL(), FCore.N(scopeType = FCore.FUNCTION_SCOPE())) then();
                  Normal (non parallel) function call in a normal class scope is OK.
                  case(DAE.FP_KERNEL_FUNCTION(), FCore.N(scopeType = FCore.CLASS_SCOPE())) then();
                  Normal (non parallel) function call in a normal function scope is OK.
                  case(DAE.FP_KERNEL_FUNCTION(), FCore.N(scopeType = FCore.FUNCTION_SCOPE())) then();
                  */ =#
          isValid
        end

        function elabCallArgsMetarecord(inCache::FCore.Cache, inEnv::FCore.Graph, inType::DAE.Type, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplicit::Bool, stopElab::MutableType #= {<:Bool} =#, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, Option{Tuple{DAE.Exp, DAE.Properties}}}
              local expProps::Option{Tuple{DAE.Exp, DAE.Properties}}
              local outCache::FCore.Cache

              (outCache, expProps) = begin
                  local fq_path::Absyn.Path
                  local ut_path::Absyn.Path
                  local str::String
                  local fn_str::String
                  local field_names::List{String}
                  local tys::List{DAE.Type}
                  local typeVars::List{DAE.Type}
                  local fargs::List{DAE.FuncArg}
                  local slots::List{Slot}
                  local const_lst::List{DAE.Const}
                  local constType::DAE.Const
                  local ty_const::DAE.TupleConst
                  local prop::DAE.Properties
                  local args::List{DAE.Exp}
                  local bindings::InstTypes.PolymorphicBindings
                @matchcontinue (@match inType = ty) begin
                  DAE.T_METARECORD(path = fq_path)  => begin
                      @match DAE.TYPES_VAR(name = str) = ListUtil.find(inType.fields, Types.varHasMetaRecordType)
                      fn_str = AbsynUtil.pathString(fq_path)
                      Error.addSourceMessage(Error.METARECORD_CONTAINS_METARECORD_MEMBER, list(fn_str, str), inInfo)
                    (inCache, NONE())
                  end

                  DAE.T_METARECORD(__)  => begin
                      @match false = listLength(inType.fields) == listLength(inPosArgs) + listLength(inNamedArgs)
                      fn_str = Types.unparseType(inType)
                      Error.addSourceMessage(Error.WRONG_NO_OF_ARGS, list(fn_str), inInfo)
                    (inCache, NONE())
                  end

                  DAE.T_METARECORD(path = fq_path)  => begin
                      field_names = list(Types.getVarName(var) for var in inType.fields)
                      tys = list(Types.getVarType(var) for var in inType.fields)
                      fargs = list(@do_threaded_for Types.makeDefaultFuncArg(n, t) (n, t) (field_names, tys))
                      slots = makeEmptySlots(fargs)
                      (outCache, _, slots, const_lst, bindings) = elabInputArgs(inCache, inEnv, inPosArgs, inNamedArgs, slots, true, true, inImplicit, inPrefix, inInfo, inType, inType.utPath)
                      constType = ListUtil.fold(const_lst, Types.constAnd, DAE.C_CONST(), DAE.Const)
                      ty_const = elabConsts(inType, constType)
                      @match true = ListUtil.fold(slots, slotAnd, true)
                      args = slotListArgs(slots)
                      if ! listEmpty(bindings)
                        bindings = Types.solvePolymorphicBindings(bindings, inInfo, inType.path)
                        typeVars = list(Types.fixPolymorphicRestype(tv, bindings, inInfo) for tv in inType.typeVars)
                        ty.typeVars = typeVars
                        prop = getProperties(ty, ty_const)
                      else
                        prop = getProperties(ty, ty_const)
                      end
                    (outCache, SOME((DAE.METARECORDCALL(fq_path, args, field_names, inType.index, inType.typeVars), prop)))
                  end

                  DAE.T_METARECORD(path = fq_path)  => begin
                       #=  MetaRecord failure.
                       =#
                      (outCache, _, prop) = elabExpInExpression(inCache, inEnv, Absyn.TUPLE(inPosArgs), false, false, inPrefix, inInfo)
                      tys = list(Types.getVarType(var) for var in inType.fields)
                      str = "Failed to match types:\\n    actual:   " + Types.unparseType(Types.getPropType(prop)) + "\\n    expected: " + Types.unparseType(DAE.T_TUPLE(tys, NONE()))
                      fn_str = AbsynUtil.pathString(fq_path)
                      Error.addSourceMessage(Error.META_RECORD_FOUND_FAILURE, list(fn_str, str), inInfo)
                    (outCache, NONE())
                  end

                  DAE.T_METARECORD(path = fq_path)  => begin
                       #=  MetaRecord failure (args).
                       =#
                      str = "Failed to elaborate arguments " + Dump.printExpStr(Absyn.TUPLE(inPosArgs))
                      fn_str = AbsynUtil.pathString(fq_path)
                      Error.addSourceMessage(Error.META_RECORD_FOUND_FAILURE, list(fn_str, str), inInfo)
                    (inCache, NONE())
                  end
                end
              end
          (outCache, expProps)
        end

         @Uniontype ForceFunctionInst begin
              @Record FORCE_FUNCTION_INST begin

              end

              @Record NORMAL_FUNCTION_INST begin

              end
         end

         #= Help function to elabCallArgs. Instantiates the function as a DAE and adds it
           to the functiontree of a newly created DAE. =#
        function instantiateDaeFunction(inCache::FCore.Cache, env::FCore.Graph, name::Absyn.Path, builtin::Bool #= builtin functions create empty dae =#, clOpt::Option{<:SCode.Element} #= if not present, looked up by name in environment =#, printErrorMsg::Bool #= if true, prints an error message if the function could not be instantiated =#) ::Tuple{FCore.Cache, Util.Status}
              local status::Util.Status
              local outCache::FCore.Cache

              (outCache, status) = instantiateDaeFunction2(inCache, env, name, builtin, clOpt, printErrorMsg, NORMAL_FUNCTION_INST())
          (outCache, status)
        end

         #= Help function to elabCallArgs. Instantiates the function as a DAE and adds it
           to the functiontree of a newly created DAE. =#
        function instantiateDaeFunctionFromTypes(inCache::FCore.Cache, env::FCore.Graph, tys::List{<:DAE.Type}, builtin::Bool #= builtin functions create empty dae =#, clOpt::Option{<:SCode.Element} #= if not present, looked up by name in environment =#, printErrorMsg::Bool #= if true, prints an error message if the function could not be instantiated =#, acc::Util.Status) ::Tuple{FCore.Cache, Util.Status}
              local status::Util.Status
              local outCache::FCore.Cache

              (outCache, status) = begin
                  local name::Absyn.Path
                  local rest::List{DAE.Type}
                  local status1::Util.Status
                  local status2::Util.Status
                @match (tys, acc) begin
                  (DAE.T_FUNCTION(path = name) <| rest, Util.SUCCESS(__))  => begin
                      (outCache, status) = instantiateDaeFunction(inCache, env, name, builtin, clOpt, printErrorMsg)
                    instantiateDaeFunctionFromTypes(inCache, env, rest, builtin, clOpt, printErrorMsg, status)
                  end

                  _  => begin
                      (inCache, acc)
                  end
                end
              end
          (outCache, status)
        end

         #= Help function to elabCallArgs. Instantiates the function as a DAE and adds it
           to the functiontree of a newly created DAE. =#
        function instantiateDaeFunctionForceInst(inCache::FCore.Cache, env::FCore.Graph, name::Absyn.Path, builtin::Bool #= builtin functions create empty dae =#, clOpt::Option{<:SCode.Element} #= if not present, looked up by name in environment =#, printErrorMsg::Bool #= if true, prints an error message if the function could not be instantiated =#) ::Tuple{FCore.Cache, Util.Status}
              local status::Util.Status
              local outCache::FCore.Cache

              (outCache, status) = instantiateDaeFunction2(inCache, env, name, builtin, clOpt, printErrorMsg, FORCE_FUNCTION_INST())
          (outCache, status)
        end

         #= Help function to elabCallArgs. Instantiates the function as a DAE and adds it
           to the functiontree of a newly created DAE. =#
        function instantiateDaeFunction2(inCache::FCore.Cache, inEnv::FCore.Graph, inName::Absyn.Path, builtin::Bool #= builtin functions create empty dae =#, clOpt::Option{<:SCode.Element} #= if not present, looked up by name in environment =#, printErrorMsg::Bool #= if true, prints an error message if the function could not be instantiated =#, forceFunctionInst::ForceFunctionInst) ::Tuple{FCore.Cache, Util.Status}
              local status::Util.Status
              local outCache::FCore.Cache

              local numError::ModelicaInteger = Error.getNumErrorMessages()
              local instOnlyForcedFunctions::Bool = isSome(getGlobalRoot(Global.instOnlyForcedFunctions))

              (outCache, status) = begin
                  local env::FCore.Graph
                  local cl::SCode.Element
                  local pathStr::String
                  local envStr::String
                  local cref::DAE.ComponentRef
                  local name::Absyn.Path
                  local ty::DAE.Type
                   #=  Skip function instantiation if we set those flags
                   =#
                @matchcontinue (builtin, clOpt, instOnlyForcedFunctions, forceFunctionInst) begin
                  (_, _, true, NORMAL_FUNCTION_INST(__))  => begin
                       #=  Don't skip builtin functions or functions in the same package; they are useful to inline
                       =#
                      @match false = AbsynUtil.pathIsIdent(inName)
                       #=  print(\"Skipping: \" + AbsynUtil.pathString(name) + \"\\n\");
                       =#
                    (inCache, Util.SUCCESS())
                  end

                  (true, _, _, _)  => begin
                    (inCache, Util.SUCCESS())
                  end

                  (_, _, _, NORMAL_FUNCTION_INST(__))  => begin
                       #=  Builtin functions skipped
                       =#
                       #=  External object functions skipped
                       =#
                      @match (_, true) = isExternalObjectFunction(inCache, inEnv, inName)
                    (inCache, Util.SUCCESS())
                  end

                  (_, NONE(), _, _)  => begin
                       #=  Recursive calls (by looking at environment) skipped
                       =#
                      @match false = FGraphUtil.isTopScope(inEnv)
                      @match true = AbsynUtil.pathSuffixOf(inName, FGraphUtil.getGraphName(inEnv))
                    (inCache, Util.SUCCESS())
                  end

                  (_, _, _, _)  => begin
                       #=  Recursive calls (by looking in cache) skipped
                       =#
                      (outCache, _, _, name) = lookupAndFullyQualify(inCache, inEnv, inName)
                      FCoreUtil.checkCachedInstFuncGuard(outCache, name)
                    (outCache, Util.SUCCESS())
                  end

                  (_, NONE(), _, _)  => begin
                       #=  class must be looked up
                       =#
                      (outCache, env, cl, name) = lookupAndFullyQualify(inCache, inEnv, inName)
                      outCache = FCoreUtil.addCachedInstFuncGuard(outCache, name)
                      outCache = InstFunction.implicitFunctionInstantiation(outCache, env, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), cl, nil)
                    (outCache, Util.SUCCESS())
                  end

                  (_, SOME(cl), _, _)  => begin
                       #=  class already available
                       =#
                      (outCache, _) = Inst.makeFullyQualified(inCache, inEnv, inName)
                      outCache = InstFunction.implicitFunctionInstantiation(outCache, inEnv, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), cl, nil)
                    (outCache, Util.SUCCESS())
                  end

                  (_, NONE(), _, _)  => begin
                       #=  call to function reference variable
                       =#
                      cref = ComponentReference.pathToCref(inName)
                      (outCache, _, ty) = Lookup.lookupVar(inCache, inEnv, cref)
                      @match DAE.T_FUNCTION() = ty
                    (outCache, Util.SUCCESS())
                  end

                  (_, _, true, _)  => begin
                      @match true = Error.getNumErrorMessages() == numError
                      envStr = FGraphUtil.printGraphPathStr(inEnv)
                      pathStr = AbsynUtil.pathString(inName)
                      Error.addMessage(Error.GENERIC_INST_FUNCTION, list(pathStr, envStr))
                    fail()
                  end

                  _  => begin
                      (inCache, Util.FAILURE())
                  end
                end
              end
          (outCache, status)
        end

        function lookupAndFullyQualify(inCache::FCore.Cache, inEnv::FCore.Graph, inFunctionName::Absyn.Path) ::Tuple{FCore.Cache, FCore.Graph, SCode.Element, Absyn.Path}
              local outFunctionName::Absyn.Path
              local outClass::SCode.Element
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              if Lookup.isFunctionCallViaComponent(inCache, inEnv, inFunctionName)
                (_, outClass, outEnv) = Lookup.lookupClass(inCache, inEnv, inFunctionName)
                outFunctionName = FGraphUtil.joinScopePath(outEnv, AbsynUtil.makeIdentPathFromString(SCodeUtil.elementName(outClass)))
                outCache = inCache
              else
                (outCache, outClass, outEnv) = Lookup.lookupClass(inCache, inEnv, inFunctionName)
                outFunctionName = AbsynUtil.makeFullyQualified(FGraphUtil.joinScopePath(outEnv, AbsynUtil.makeIdentPathFromString(SCodeUtil.elementName(outClass))))
              end
               #=  do NOT qualify function calls via component instance!
               =#
               #=  qualify everything else
               =#
          (outCache, outEnv, outClass, outFunctionName)
        end

         #= Given a list of arguments to a function, this function checks if any of the
          arguments are component references to a record instance, and instantiates the
          record constructors for those components. These are implicit record
          constructors, because they are not explicitly called, but are needed when code
          is generated for record instances as function input arguments. =#
        function instantiateImplicitRecordConstructors(inCache::FCore.Cache, inEnv::FCore.Graph, args::List{<:DAE.Exp}) ::FCore.Cache
              local outCache::FCore.Cache

              outCache = begin
                  local rest_args::List{DAE.Exp}
                  local record_name::Absyn.Path
                  local cache::FCore.Cache
                   #=  case (_, SOME(_)) then inCache;  TODO: Should this just return now? We always have symbol table!
                   =#
                @matchcontinue args begin
                   nil()  => begin
                    inCache
                  end

                  DAE.CREF(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = record_name))) <| rest_args  => begin
                      @match (cache, Util.SUCCESS()) = instantiateDaeFunction(inCache, inEnv, record_name, false, NONE(), false)
                    instantiateImplicitRecordConstructors(cache, inEnv, rest_args)
                  end

                  _ <| rest_args  => begin
                    instantiateImplicitRecordConstructors(inCache, inEnv, rest_args)
                  end
                end
              end
          outCache
        end

         #= Adds default values to a list of function slots. =#
        function addDefaultArgs(inSlots::List{<:Slot}, inInfo::SourceInfo) ::Tuple{List{DAE.Exp}, List{Slot}}
              local outSlots::List{Slot}
              local outArgs::List{DAE.Exp}

              (outArgs, outSlots) = ListUtil.map2_2(inSlots, fillDefaultSlot, listArray(inSlots), inInfo)
          (outArgs, outSlots)
        end

         #= Fills a function slot with it's default value if it hasn't already been filled. =#
        function fillDefaultSlot(inSlot::Slot, inSlotArray::Array{<:Slot}, inInfo::SourceInfo) ::Tuple{DAE.Exp, Slot}
              local outSlot::Slot
              local outArg::DAE.Exp

              (outArg, outSlot) = begin
                  local arg::DAE.Exp
                  local id::String
                  local idx::ModelicaInteger
                   #=  Slot already filled by function argument.
                   =#
                @match inSlot begin
                  SLOT(slotFilled = true, arg = SOME(arg))  => begin
                    (arg, inSlot)
                  end

                  SLOT(slotFilled = false, defaultArg = DAE.FUNCARG(defaultBinding = SOME(_)), idx = idx)  => begin
                    fillDefaultSlot2(inSlotArray[idx], inSlotArray, inInfo)
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = id))  => begin
                      Error.addSourceMessage(Error.UNFILLED_SLOT, list(id), inInfo)
                    fail()
                  end
                end
              end
               #=  Slot not filled by function argument, but has default value.
               =#
               #=  Slot not filled, and has no default value => error.
               =#
          (outArg, outSlot)
        end

        function fillDefaultSlot2(inSlot::Slot, inSlotArray::Array{<:Slot}, inInfo::SourceInfo) ::Tuple{DAE.Exp, Slot}
              local outSlot::Slot = inSlot
              local outArg::DAE.Exp

              (outArg, outSlot) = begin
                  local slot::Slot
                  local exp::DAE.Exp
                  local id::String
                  local da::DAE.FuncArg
                  local dims::DAE.Dimensions
                  local idx::ModelicaInteger
                  local slots::List{Tuple{Slot, ModelicaInteger}}
                  local cyclic_slots::List{String}
                   #=  An already evaluated slot, return its binding.
                   =#
                @match outSlot begin
                  SLOT(arg = SOME(exp), evalStatus = 2)  => begin
                    (exp, inSlot)
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = id), evalStatus = 1)  => begin
                       #=  A slot in the process of being evaluated => cyclic bindings.
                       =#
                      Error.addSourceMessage(Error.CYCLIC_DEFAULT_VALUE, list(id), inInfo)
                    fail()
                  end

                  SLOT(defaultArg = DAE.FUNCARG(defaultBinding = SOME(exp)), idx = idx, evalStatus = 0)  => begin
                       #=  A slot with an unevaluated binding, evaluate the binding and return it.
                       =#
                      outSlot.evalStatus = SLOT_EVALUATING
                      arrayUpdate(inSlotArray, idx, outSlot)
                      exp = evaluateSlotExp(exp, inSlotArray, inInfo)
                      outSlot.arg = SOME(exp)
                      outSlot.slotFilled = true
                      outSlot.evalStatus = SLOT_EVALUATED
                      arrayUpdate(inSlotArray, idx, outSlot)
                    (exp, outSlot)
                  end
                end
              end
          (outArg, outSlot)
        end

         #= Evaluates a slot's binding by recursively replacing references to other slots
           with their bindings. =#
        function evaluateSlotExp(inExp::DAE.Exp, inSlotArray::Array{<:Slot}, inInfo::SourceInfo) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = Expression.traverseExpBottomUp(inExp, evaluateSlotExp_traverser, (inSlotArray, inInfo))
          outExp
        end

        function evaluateSlotExp_traverser(inExp::DAE.Exp, inTuple::Tuple{<:Array{<:Slot}, SourceInfo}) ::Tuple{DAE.Exp, Tuple{Array{Slot}, SourceInfo}}
              local outTuple::Tuple{Array{Slot}, SourceInfo}
              local outExp::DAE.Exp

              (outExp, outTuple) = begin
                  local id::String
                  local slots::Array{Slot}
                  local slot::Option{Slot}
                  local exp::DAE.Exp
                  local orig_exp::DAE.Exp
                  local info::SourceInfo
                   #=  Only simple identifiers can be slot names.
                   =#
                @match (inExp, inTuple) begin
                  (orig_exp && DAE.CREF(componentRef = DAE.CREF_IDENT(ident = id)), (slots, info))  => begin
                      slot = lookupSlotInArray(id, slots)
                      exp = getOptSlotDefaultExp(slot, slots, info, orig_exp)
                    (exp, (slots, info))
                  end

                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
          (outExp, outTuple)
        end

         #= Looks up the given name in an array of slots, and returns either SOME(slot)
           if a slot with that name was found, or NONE() if a slot couldn't be found. =#
        function lookupSlotInArray(inSlotName::String, inSlots::Array{<:Slot}) ::Option{Slot}
              local outSlot::Option{Slot}

              local slot::Slot

              try
                slot = ArrayUtil.getMemberOnTrue(inSlotName, inSlots, isSlotNamed)
                outSlot = SOME(slot)
              catch
                outSlot = NONE()
              end
          outSlot
        end

        function isSlotNamed(inName::String, inSlot::Slot) ::Bool
              local outIsNamed::Bool

              local id::String

              @match SLOT(defaultArg = DAE.FUNCARG(name = id)) = inSlot
              outIsNamed = stringEq(id, inName)
          outIsNamed
        end

         #= Takes an optional slot and tries to evaluate the slot's binding if it's SOME,
           otherwise returns the original expression if it's NONE. =#
        function getOptSlotDefaultExp(inSlot::Option{<:Slot}, inSlots::Array{<:Slot}, inInfo::SourceInfo, inOrigExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local slot::Slot
                  local exp::DAE.Exp
                   #=  Got a slot, evaluate its binding and return it.
                   =#
                @match inSlot begin
                  SOME(slot)  => begin
                      exp = fillDefaultSlot(slot, inSlots, inInfo)
                    exp
                  end

                  NONE()  => begin
                    inOrigExp
                  end
                end
              end
               #=  No slot, return the original expression.
               =#
          outExp
        end

         #= For the special functions constructor and destructor, in external object, the
           constantness is always variable, even if arguments are constant, because they
           should be called during runtime and not during compiletime. =#
        function determineConstSpecialFunc(inCache::FCore.Cache, inEnv::FCore.Graph, inConst::DAE.Const, inFuncName::Absyn.Path) ::Tuple{FCore.Cache, DAE.Const}
              local outConst::DAE.Const
              local outCache::FCore.Cache

              local is_ext::Bool

              (outCache, is_ext) = isExternalObjectFunction(inCache, inEnv, inFuncName)
              outConst = if is_ext
                    DAE.C_VAR()
                  else
                    inConst
                  end
          (outCache, outConst)
        end

        function isExternalObjectFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path) ::Tuple{FCore.Cache, Bool}
              local outIsExt::Bool
              local outCache::FCore.Cache

              local els::List{SCode.Element}
              local last_id::String

              try
                @match (outCache, SCode.CLASS(classDef = SCode.PARTS(elementLst = els)), _) = Lookup.lookupClass(inCache, inEnv, inPath)
                @match true = SCodeUtil.isExternalObject(els)
                outIsExt = true
              catch
                last_id = AbsynUtil.pathLastIdent(inPath)
                outCache = inCache
                outIsExt = last_id == "constructor" || last_id == "destructor"
              end
          (outCache, outIsExt)
        end

         const vectorizeArg = "vectorizeArg"::String

         #= author: PA
          Takes an expression and a list of array dimensions and the Slot list.
          It will vectorize the expression over the dimension given as array dim
          for the slots which have that dimension.
          For example foo:(Real,Real[:])=> Real
          foo(1:2,{1,2;3,4}) vectorizes with arraydim [2] to
          {foo(1,{1,2}),foo(2,{3,4})} =#
        function vectorizeCall(inExp::DAE.Exp, inDims::DAE.Dimensions, inSlots::List{<:Slot}, inProperties::DAE.Properties, info::SourceInfo) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProperties) = begin
                  local e::DAE.Exp
                  local vect_exp::DAE.Exp
                  local vect_exp_1::DAE.Exp
                  local dimexp::DAE.Exp
                  local tp::DAE.Type
                  local tp0::DAE.Type
                  local prop::DAE.Properties
                  local exp_type::DAE.Type
                  local etp::DAE.Type
                  local c::DAE.Const
                  local fn::Absyn.Path
                  local expl::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local scalar::Bool
                  local int_dim::ModelicaInteger
                  local dim::DAE.Dimension
                  local ad::DAE.Dimensions
                  local slots::List{Slot}
                  local str::String
                  local attr::DAE.CallAttributes
                  local rinfo::DAE.ReductionInfo
                  local riter::DAE.ReductionIterator
                  local foldName::String
                  local resultName::String
                  local riters::List{DAE.ReductionIterator}
                  local iterType::Absyn.ReductionIterType
                @matchcontinue (inExp, inDims, inProperties) begin
                  (e,  nil(), prop)  => begin
                    (e, prop)
                  end

                  (e, DAE.DIM_UNKNOWN(__) <| ad, prop) where (Flags.getConfigBool(Flags.CHECK_MODEL))  => begin
                    vectorizeCall(e, _cons(DAE.DIM_INTEGER(1), ad), inSlots, prop, info)
                  end

                  (e && DAE.CALL(__), dim <| ad, DAE.PROP(tp, c))  => begin
                       #=  If the dimension is not defined we can't vectorize the call. If we are running
                       =#
                       #=  checkModel this should succeed anyway, since we might be checking a function
                       =#
                       #=  that takes a vector of unknown size. So pretend that the dimension is 1.
                       =#
                       #= /* Scalar expression, i.e function call */ =#
                      int_dim = Expression.dimensionSize(dim)
                      exp_type = Types.simplifyType(Types.liftArray(tp, dim)) #= pass type of vectorized result expr =#
                      vect_exp = vectorizeCallScalar(e, exp_type, int_dim, inSlots)
                      tp = Types.liftArray(tp, dim)
                    vectorizeCall(vect_exp, ad, inSlots, DAE.PROP(tp, c), info)
                  end

                  (DAE.ARRAY(__), dim <| ad, DAE.PROP(tp, c))  => begin
                       #= /* array expression of function calls */ =#
                      int_dim = Expression.dimensionSize(dim)
                       #=  _ = Types.simplifyType(Types.liftArray(tp, dim));
                       =#
                      vect_exp = vectorizeCallArray(inExp, int_dim, inSlots)
                      tp = Types.liftArrayRight(tp, dim)
                    vectorizeCall(vect_exp, ad, inSlots, DAE.PROP(tp, c), info)
                  end

                  (DAE.CALL(fn, es, attr), dim <| ad, prop && DAE.PROP(tp, c))  => begin
                       #= /* Multiple dimensions are possible to change to a reduction, like:
                           * f(arr1,arr2) => array(f(x,y) thread for x in arr1, y in arr2)
                           * f(mat1,mat2) => array(array(f(x,y) thread for x in arr1, y in arr2) thread for arr1 in mat1, arr2 in mat2
                           */ =#
                      (es, riters) = vectorizeCallUnknownDimension(es, inSlots, info)
                      tp = Types.liftArrayRight(tp, dim)
                      prop = DAE.PROP(tp, c)
                      e = DAE.CALL(fn, es, attr)
                      (e, prop) = vectorizeCall(e, ad, inSlots, prop, info)
                       #=  Recurse...
                       =#
                      foldName = Util.getTempVariableIndex()
                      resultName = Util.getTempVariableIndex()
                      iterType = if listLength(riters) > 1
                            Absyn.THREAD()
                          else
                            Absyn.COMBINE()
                          end
                      rinfo = DAE.REDUCTIONINFO(Absyn.IDENT("array"), iterType, tp, SOME(Values.ARRAY(nil, list(0))), foldName, resultName, NONE())
                    (DAE.REDUCTION(rinfo, e, riters), prop)
                  end

                  (DAE.CALL(__), DAE.DIM_EXP(__) <| _, DAE.PROP(__))  => begin
                       #= /* Scalar expression, non-constant but known dimensions */ =#
                      str = "Cannot vectorize call with dimensions [" + ExpressionDump.dimensionsString(inDims) + "]"
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), info)
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        str = ExpressionDump.dimensionString(listHead(inDims))
                        Debug.traceln("- Static.vectorizeCall failed: " + str)
                      fail()
                  end
                end
              end
          (outExp, outProperties)
        end

         #= Returns the new call arguments and a reduction iterator argument =#
        function vectorizeCallUnknownDimension(inEs::List{<:DAE.Exp}, inSlots::List{<:Slot}, info::SourceInfo) ::Tuple{List{DAE.Exp}, List{DAE.ReductionIterator}}
              local ofound::List{DAE.ReductionIterator} = nil
              local oes::List{DAE.Exp} = nil

              local rest_slots::List{Slot} = inSlots
              local dims::List{DAE.Dimension}
              local ty::DAE.Type
              local tp::DAE.Type
              local name::String

              for e in inEs
                @match SLOT(dims = dims, defaultArg = DAE.FUNCARG(ty = ty)) <| rest_slots = rest_slots
                if listEmpty(dims)
                  oes = _cons(e, oes)
                else
                  name = Util.getTempVariableIndex()
                  tp = Types.expTypetoTypesType(Expression.typeOf(e))
                  ofound = _cons(DAE.REDUCTIONITER(name, e, NONE(), tp), ofound)
                  oes = _cons(DAE.CREF(DAE.CREF_IDENT(name, ty, nil), ty), oes)
                end
              end
               #=  Maybe raise the type from the SLOT instead?
               =#
              if listEmpty(ofound)
                Error.addSourceMessageAndFail(Error.INTERNAL_ERROR, list("Static.vectorizeCallUnknownDimension could not find any slot to vectorize"), info)
              end
              oes = listReverse(oes)
              ofound = listReverse(ofound)
          (oes, ofound)
        end

         #= Helper function to vectorizeCall, vectorizes an ARRAY expression to an array
           of array expressions. =#
        function vectorizeCallArray(inExp::DAE.Exp, inDim::ModelicaInteger, inSlots::List{<:Slot}) ::DAE.Exp
              local outExp::DAE.Exp

              local ty::DAE.Type
              local expl::List{DAE.Exp}
              local sc::Bool

              @match DAE.ARRAY(ty = ty, array = expl) = inExp
              expl = vectorizeCallArray2(expl, ty, inDim, inSlots)
              sc = Expression.typeBuiltin(ty)
              ty = Expression.liftArrayRight(ty, DAE.DIM_INTEGER(inDim))
              outExp = DAE.ARRAY(ty, sc, expl)
          outExp
        end

         #= Helper function to vectorizeCallArray =#
        function vectorizeCallArray2(inExpl::List{<:DAE.Exp}, inType::DAE.Type, inDim::ModelicaInteger, inSlots::List{<:Slot}) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp}

              outExpl = list(begin
                @match e begin
                  DAE.CALL(__)  => begin
                    vectorizeCallScalar(e, inType, inDim, inSlots)
                  end

                  DAE.ARRAY(__)  => begin
                    vectorizeCallArray(e, inDim, inSlots)
                  end
                end
              end for e in inExpl)
          outExpl
        end

         #= author: PA
          Helper function to vectorizeCall, vectorizes CALL expressions to
          array expressions. =#
        function vectorizeCallScalar(exp::DAE.Exp #= e.g. abs(v) =#, ty::DAE.Type #=  e.g. Real[3], result of vectorized call =#, dim::ModelicaInteger, slots::List{<:Slot}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local expl::List{DAE.Exp}
                  local args::List{DAE.Exp}
                  local scalar::Bool
                  local new_exp::DAE.Exp
                  local e_type::DAE.Type
                  local arr_type::DAE.Type
                @matchcontinue exp begin
                  DAE.CALL(__)  => begin
                      expl = vectorizeCallScalar2(exp.path, exp.expLst, exp.attr, slots, dim)
                      e_type = Expression.unliftArray(ty)
                      scalar = Expression.typeBuiltin(e_type) #=  unlift vectorized dimension to find element type =#
                      arr_type = DAE.T_ARRAY(e_type, list(DAE.DIM_INTEGER(dim)))
                      new_exp = DAE.ARRAY(arr_type, scalar, expl)
                    new_exp
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("-Static.vectorizeCallScalar failed\\n")
                      fail()
                  end
                end
              end
          outExp
        end

         #= Iterates through vectorized dimension an creates argument list according to vectorized dimension in corresponding slot. =#
        function vectorizeCallScalar2(fn::Absyn.Path, exps::List{<:DAE.Exp}, attr::DAE.CallAttributes, slots::List{<:Slot}, dim::ModelicaInteger) ::List{DAE.Exp}
              local res::List{DAE.Exp} = nil

              local callargs::List{DAE.Exp}

              for cur_dim in dim:(-1):1
                callargs = vectorizeCallScalar3(exps, slots, cur_dim)
                res = _cons(DAE.CALL(fn, callargs, attr), res)
              end
          res
        end

         #= author: PA
          Helper function to vectorizeCallScalar2 =#
        function vectorizeCallScalar3(inExpl::List{<:DAE.Exp}, inSlots::List{<:Slot}, inIndex::ModelicaInteger) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp} = nil

              local rest_slots::List{Slot} = inSlots
              local dims::List{DAE.Dimension}

              for e in inExpl
                @match SLOT(dims = dims) <| rest_slots = rest_slots
                if ! listEmpty(dims)
                  e = Expression.makeASUB(e, list(DAE.ICONST(inIndex)))
                  (e, _) = ExpressionSimplify.simplify1(e)
                end
                outExpl = _cons(e, outExpl)
              end
               #=  Foreach argument.
               =#
              outExpl = listReverse(outExpl)
          outExpl
        end

         #= This function is used to deoverload function calls. It investigates the
          type of the function to see if it has the optional functionname set. If
          so this is returned. Otherwise return input. =#
        function deoverloadFuncname(inPath::Absyn.Path, inType::DAE.Type, inEnv::FCore.Graph) ::Tuple{Absyn.Path, DAE.Type}
              local outType::DAE.Type
              local outPath::Absyn.Path

              (outPath, outType) = begin
                  local fn::Absyn.Path
                  local name::String
                  local tty::DAE.Type
                @match inType begin
                  tty && DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isBuiltin = DAE.FUNCTION_BUILTIN(SOME(name))))  => begin
                      @set tty.path = Absyn.IDENT(name)
                    (tty.path, tty)
                  end

                  DAE.T_FUNCTION(path = fn)  => begin
                    (fn, inType)
                  end

                  _  => begin
                      (inPath, inType)
                  end
                end
              end
          (outPath, outType)
        end

         #= Elaborate input parameters to a function and select matching function type
           from a list of types. =#
        function elabTypes(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inTypes::List{<:DAE.Type}, inOnlyOneFunction::Bool #= if true, we can report errors as soon as possible =#, inCheckTypes::Bool #= if true, checks types =#, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Exp}, List{DAE.Const}, DAE.Type, DAE.Type, DAE.Dimensions, List{Slot}}
              local outSlots::List{Slot}
              local outDimensions::DAE.Dimensions
              local outFunctionType::DAE.Type
              local outResultType::DAE.Type
              local outConsts::List{DAE.Const}
              local outArgs::List{DAE.Exp}
              local outCache::FCore.Cache

              local params::List{DAE.FuncArg}
              local res_ty::DAE.Type
              local func_ty::DAE.Type
              local func_attr::DAE.FunctionAttributes
              local slots::List{Slot}
              local pb::InstTypes.PolymorphicBindings
              local path::Absyn.Path
              local success::Bool = false
              local rest_tys::List{DAE.Type} = inTypes
              local tys::List{DAE.Type}
              local name::String
              local arg::DAE.Exp
              local numArgs::ModelicaInteger
              local funcarg::DAE.FuncArg
              local debug::Bool = false

              if listLength(rest_tys) > 1
                numArgs = listLength(inPosArgs) + listLength(inNamedArgs)
                tys = list(ty for ty in rest_tys if begin
                   @match ty begin
                     DAE.T_FUNCTION(__)  => begin
                       numArgs <= listLength(ty.funcArg) && numArgs >= sum(if Util.isNone(argument.defaultBinding)
                             1
                           else
                             0
                           end for argument in ty.funcArg)
                     end
                   end
                 end)
                if ! listEmpty(tys)
                  rest_tys = tys
                end
              end
               #=  Filter out some interesting candidates first; this makes us not
               =#
               #=  look at overloaded functions with the wrong number of arguments (getting weird error-messages)
               =#
              while ! success
                @match func_ty <| rest_tys = rest_tys
                @match DAE.T_FUNCTION(funcArg = params, funcResultType = res_ty, functionAttributes = func_attr, path = path) = func_ty
                if debug
                  print("elabTypes, try: " + Types.unparseType(func_ty) + "\\n")
                end
                try
                  slots = makeEmptySlots(params)
                  (outCache, outArgs, outSlots, outConsts, pb) = elabInputArgs(inCache, inEnv, inPosArgs, inNamedArgs, slots, inOnlyOneFunction, inCheckTypes, inImplicit, inPrefix, inInfo, func_ty, path)
                  pb = Types.solvePolymorphicBindings(pb, inInfo, path)
                  res_ty = Types.fixPolymorphicRestype(res_ty, pb, inInfo)
                  (outArgs, outSlots, params, res_ty) = begin
                    @match func_attr.isBuiltin begin
                      DAE.FUNCTION_BUILTIN(unboxArgs = true)  => begin
                        (ListUtil.map(outArgs, Expression.unboxExp), list(begin
                          @match slot begin
                            SLOT(arg = SOME(arg))  => begin
                                @set slot.arg = SOME(Expression.unboxExp(arg))
                              slot
                            end

                            _  => begin
                                slot
                            end
                          end
                        end for slot in outSlots), list(begin
                          @match p begin
                            funcarg  => begin
                                @set funcarg.ty = Types.unboxedType(Types.fixPolymorphicRestype(p.ty, pb, inInfo))
                              funcarg
                            end
                          end
                        end for p in params), Types.unboxedType(res_ty))
                      end

                      _  => begin
                          (outArgs, outSlots, params, res_ty)
                      end
                    end
                  end
                  (params, res_ty) = applyArgTypesToFuncType(outSlots, params, res_ty, inEnv, inCheckTypes, inInfo)
                  outDimensions = slotsVectorizable(outSlots, inInfo)
                  outResultType = res_ty
                  outFunctionType = DAE.T_FUNCTION(params, outResultType, func_attr, path)
                  outFunctionType = Types.fixPolymorphicRestype(outFunctionType, pb, inInfo)
                  outFunctionType = createActualFunctype(outFunctionType, outSlots, inCheckTypes)
                  success = true
                  if debug
                    print("elabTypes success for " + Types.unparseType(func_ty) + ": " + Types.unparseType(outFunctionType) + "=>" + Types.unparseType(outResultType) + "\\n")
                  end
                catch
                end
              end
               #=  Fix the types of the inputs (needed for slots evaluation)
               =#
               #=  Check the sanity of function parameters whose types are dependent on other parameters.
               =#
               #=  e.g. input Integer i; input Integer a[i];  type of 'a' depends on the value 'i'.
               =#
               #=  Only created when not checking types for error msg.
               =#
               #=  The type didn't match, try next function type.
               =#
          (outCache, outArgs, outConsts, outResultType, outFunctionType, outDimensions, outSlots)
        end

         #= This function is yet another hack trying to handle function parameters with
           unknown dimensions. It uses the input arguments to try and figure out the
           actual dimensions of the dimensions. =#
        function applyArgTypesToFuncType(inSlots::List{<:Slot}, inParameters::List{<:DAE.FuncArg}, inResultType::DAE.Type, inEnv::FCore.Graph, checkTypes::Bool, inInfo::SourceInfo) ::Tuple{List{DAE.FuncArg}, DAE.Type}
              local outResultType::DAE.Type
              local outParameters::List{DAE.FuncArg}

              local tys::List{DAE.Type}
              local dims::List{DAE.Dimension}
              local used_args::List{String}
              local used_slots::List{Slot}
              local cache::FCore.Cache
              local env::FCore.Graph
              local vars::List{DAE.Var}
              local dummy_var::SCode.Element
              local res_ty::DAE.Type

               #=  If not checking types or no function parameters there is nothing to be done here.
               =#
               #=  Even if dims don't match we need the function as candidate for error messages.
               =#
              if ! checkTypes || listEmpty(inParameters)
                outParameters = inParameters
                outResultType = inResultType
                return (outParameters, outResultType)
              end
               #=  Get all the dims, bind the actual params to the formal params.
               =#
               #=  Build a new env frame with these bindings and evaluate dimensions.
               =#
               #=  Extract all dimensions from the parameters.
               =#
              tys = list(Types.funcArgType(param) for param in inParameters)
              dims = getAllOutputDimensions(inResultType)
              dims = listAppend(ListUtil.mapFlat(tys, Types.getDimensions), dims)
               #=  Use the dimensions to figure out which parameters are referenced by other
               =#
               #=  parameters' dimensions. This is done to minimize the things we need to
               =#
               #=  constant evaluate, a.k.a. 'things that go wrong'.
               =#
              used_args = extractNamesFromDims(dims)
              used_slots = list(s for s in inSlots if isSlotUsed(s, used_args))
               #=  Create DAE.Vars from the slots.
               =#
              cache = FCoreUtil.noCache()
              vars = list(makeVarFromSlot(s, inEnv, cache) for s in used_slots)
               #=  Use a dummy SCode.Element, because we're only interested in the DAE.Vars.
               =#
              dummy_var = SCode.COMPONENT("dummy", SCode.defaultPrefixes, SCode.defaultVarAttr, Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)
               #=  Create a new implicit scope with the needed parameters on top of the
               =#
               #=  current env so we can find the bindings if needed. We need an implicit
               =#
               #=  scope so comp1.comp2 can be looked up without package constant restriction.
               =#
              env = FGraphUtil.openScope(inEnv, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE())
               #=  Add variables to the environment.
               =#
              env = makeDummyFuncEnv(env, vars, dummy_var)
               #=  Evaluate the dimensions in the types.
               =#
              # outParameters = list(@do_threaded_for evaluateFuncParamDimAndMatchTypes(s, p, @nospecialize(env), cache, inInfo) (s, p) (inSlots, inParameters))

              outParameters = nil
              for (s, p) in zip(inSlots, inParameters)
                local x::DAE.FuncArg
                x = evaluateFuncParamDimAndMatchTypes(s, p, env, cache, inInfo)
                outParameters = _cons(x, outParameters)
             end
             outParameters = listReverse(outParameters)

              outResultType = evaluateFuncArgTypeDims(inResultType, env, cache)
          (outParameters, outResultType)
        end

         #= Return the dimensions of an output type. =#
        function getAllOutputDimensions(inOutputType::DAE.Type) ::List{DAE.Dimension}
              local outDimensions::List{DAE.Dimension}

              outDimensions = begin
                  local tys::List{DAE.Type}
                   #=  A tuple, get the dimensions of all the types.
                   =#
                @match inOutputType begin
                  DAE.T_TUPLE(types = tys)  => begin
                    ListUtil.mapFlat(tys, Types.getDimensions)
                  end

                  _  => begin
                      Types.getDimensions(inOutputType)
                  end
                end
              end
          outDimensions
        end

         #= Extracts a list of unique names referenced by the given list of dimensions. =#
        function extractNamesFromDims(inDimensions::List{<:DAE.Dimension}, inAccumNames::List{<:String} = nil) ::List{String}
              local outNames::List{String}

              outNames = begin
                  local exp::DAE.Exp
                  local rest_dims::List{DAE.Dimension}
                  local crefs::List{DAE.ComponentRef}
                  local names::List{String}
                @match inDimensions begin
                  DAE.DIM_EXP(exp = exp) <| rest_dims  => begin
                      crefs = Expression.extractCrefsFromExp(exp)
                      names = ListUtil.fold(crefs, extractNamesFromDims2, inAccumNames)
                    extractNamesFromDims(rest_dims, names)
                  end

                  _ <| rest_dims  => begin
                    extractNamesFromDims(rest_dims, inAccumNames)
                  end

                   nil()  => begin
                    inAccumNames
                  end
                end
              end
          outNames
        end

        function extractNamesFromDims2(inCref::DAE.ComponentRef, inAccumNames::List{<:String}) ::List{String}
              local outNames::List{String}

              outNames = begin
                  local name::String
                   #=  Only interested in simple identifier, since that's all we can handle
                   =#
                   #=  anyway.
                   =#
                @match (inCref, inAccumNames) begin
                  (DAE.CREF_IDENT(ident = name), _)  => begin
                       #=  Make sure we haven't added this name yet.
                       =#
                      outNames = if ListUtil.isMemberOnTrue(name, inAccumNames, stringEq)
                            inAccumNames
                          else
                            _cons(name, inAccumNames)
                          end
                    outNames
                  end

                  _  => begin
                      inAccumNames
                  end
                end
              end
          outNames
        end

         #= Checks if a slot is used, in the sense that it's referenced by a function
           parameter dimension. =#
        function isSlotUsed(inSlot::Slot, inUsedNames::List{<:String}) ::Bool
              local outIsUsed::Bool

              local slot_name::String

              @match SLOT(defaultArg = DAE.FUNCARG(name = slot_name)) = inSlot
              outIsUsed = ListUtil.isMemberOnTrue(slot_name, inUsedNames, stringEq)
          outIsUsed
        end

         #= Converts a Slot to a DAE.Var. =#
        function makeVarFromSlot(inSlot::Slot, inEnv::FCore.Graph, inCache::FCore.Cache) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local name::DAE.Ident
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local binding::DAE.Binding
                  local val::Values.Value
                  local defaultArg::DAE.FuncArg
                  local slotFilled::Bool
                  local dims::DAE.Dimensions
                  local idx::ModelicaInteger
                  local var::DAE.Var
                   #=  If the argument expression already has known dimensions, no need to
                   =#
                   #=  constant evaluate it.
                   =#
                @matchcontinue inSlot begin
                  SLOT(defaultArg = DAE.FUNCARG(name = name), arg = SOME(exp))  => begin
                      @match false = Expression.expHasCref(exp, ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil))
                      ty = Expression.typeOf(exp)
                      @match true = Types.dimensionsKnown(ty)
                      binding = DAE.EQBOUND(exp, NONE(), DAE.C_CONST(), DAE.BINDING_FROM_DEFAULT_VALUE())
                    DAE.TYPES_VAR(name, DAE.dummyAttrParam, ty, binding, NONE())
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = name), arg = SOME(exp))  => begin
                       #=  Otherwise, try to constant evaluate the expression.
                       =#
                       #=  Constant evaluate the bound expression.
                       =#
                      (_, val) = Ceval.ceval(inCache, inEnv, exp, false, Absyn.NO_MSG(), 0)
                      exp = ValuesUtil.valueExp(val)
                      ty = Expression.typeOf(exp)
                       #=  Create a binding from the evaluated expression.
                       =#
                      binding = DAE.EQBOUND(exp, SOME(val), DAE.C_CONST(), DAE.BINDING_FROM_DEFAULT_VALUE())
                    DAE.TYPES_VAR(name, DAE.dummyAttrParam, ty, binding, NONE())
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = name, ty = ty))  => begin
                    DAE.TYPES_VAR(name, DAE.dummyAttrParam, ty, DAE.UNBOUND(), NONE())
                  end
                end
              end
          outVar
        end

        function evaluateStructuralSlots2(inCache::FCore.Cache, inEnv::FCore.Graph, inSlots::List{<:Slot}, usedSlots::List{<:String}, acc::List{<:Slot}) ::Tuple{FCore.Cache, List{Slot}}
              local slots::List{Slot}
              local cache::FCore.Cache

              (cache, slots) = begin
                  local name::String
                  local slotFilled::Bool
                  local exp::DAE.Exp
                  local slot::Slot
                  local rest::List{Slot}
                  local defaultArg::DAE.FuncArg
                  local dims::List{DAE.Dimension}
                  local idx::ModelicaInteger
                  local val::Values.Value
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local ses::ModelicaInteger
                @matchcontinue inSlots begin
                   nil()  => begin
                    (inCache, listReverse(acc))
                  end

                  slot <| rest  => begin
                      @match false = isSlotUsed(slot, usedSlots)
                      (cache, slots) = evaluateStructuralSlots2(inCache, inEnv, rest, usedSlots, _cons(slot, acc))
                    (cache, slots)
                  end

                  SLOT(defaultArg && DAE.FUNCARG(__), _, SOME(exp), dims, idx, ses) <| rest  => begin
                       #=  If we are suggested the argument is structural, evaluate it
                       =#
                       #=  Constant evaluate the bound expression.
                       =#
                      (cache, val) = Ceval.ceval(inCache, inEnv, exp, false, Absyn.NO_MSG(), 0)
                      exp = ValuesUtil.valueExp(val)
                       #=  Create a binding from the evaluated expression.
                       =#
                      slot = SLOT(defaultArg, true, SOME(exp), dims, idx, ses)
                      (cache, slots) = evaluateStructuralSlots2(cache, inEnv, rest, usedSlots, _cons(slot, acc))
                    (cache, slots)
                  end

                  slot <| rest  => begin
                      (cache, slots) = evaluateStructuralSlots2(inCache, inEnv, rest, usedSlots, _cons(slot, acc))
                    (cache, slots)
                  end
                end
              end
          (cache, slots)
        end

        function evaluateStructuralSlots(inCache::FCore.Cache, inEnv::FCore.Graph, inSlots::List{<:Slot}, funcType::DAE.Type) ::Tuple{FCore.Cache, List{Slot}}
              local slots::List{Slot}
              local cache::FCore.Cache

              (cache, slots) = begin
                  local tys::List{DAE.Type}
                  local dims::List{DAE.Dimension}
                  local used_args::List{String}
                  local funcArg::List{DAE.FuncArg}
                  local funcResultType::DAE.Type
                @match funcType begin
                  DAE.T_FUNCTION(funcArg = funcArg, funcResultType = funcResultType)  => begin
                      tys = list(Types.funcArgType(arg) for arg in funcArg)
                      dims = getAllOutputDimensions(funcResultType)
                      dims = listAppend(ListUtil.mapFlat(tys, Types.getDimensions), dims)
                       #=  Use the dimensions to figure out which parameters are referenced by
                       =#
                       #=  other parameters' dimensions. This is done to minimize the things we
                       =#
                       #=  need to constant evaluate, a.k.a. 'things that go wrong'.
                       =#
                      used_args = extractNamesFromDims(dims)
                      (cache, slots) = evaluateStructuralSlots2(inCache, inEnv, inSlots, used_args, nil)
                    (cache, slots)
                  end

                  _  => begin
                      (inCache, inSlots)
                  end
                end
              end
               #=  T_METARECORD, T_NOTYPE etc for builtins
               =#
          (cache, slots)
        end

         #= Helper function to applyArgTypesToFuncType, creates a dummy function
           environment. =#
        function makeDummyFuncEnv(inEnv::FCore.Graph, inVars::List{<:DAE.Var}, inDummyVar::SCode.Element) ::FCore.Graph
              local outEnv::FCore.Graph = inEnv

              local dummy_var::SCode.Element

              for var in inVars
                dummy_var = SCodeUtil.setComponentName(inDummyVar, DAEUtil.typeVarIdent(var))
                outEnv = FGraphUtil.mkComponentNode(outEnv, var, dummy_var, DAE.NOMOD(), FCore.VAR_TYPED(), FCore.emptyGraph)
              end
          outEnv
        end

         #= Constant evaluates the dimensions of a FuncArg and then makes
          sure the type matches with the expected type in the slot. =#
        function evaluateFuncParamDimAndMatchTypes(inSlot::Slot, inParam::DAE.FuncArg, inEnv::FCore.Graph, inCache::FCore.Cache, inInfo::SourceInfo) ::DAE.FuncArg
              local outParam::DAE.FuncArg

              outParam = begin
                  local ident::DAE.Ident
                  local pty::DAE.Type
                  local sty::DAE.Type
                  local c::DAE.Const
                  local p::DAE.VarParallelism
                  local oexp::Option{DAE.Exp}
                  local dims1::DAE.Dimensions
                  local dims2::DAE.Dimensions
                  local t_str1::String
                  local t_str2::String
                  local vdims::DAE.Dimensions
                  local b::Bool
                   #=  If we have a code exp argument we can't check dims...
                   =#
                   #=  There are all kinds of scripting function that complicate things.
                   =#
                @match (inSlot, inParam) begin
                  (_, DAE.FUNCARG(ty = DAE.T_CODE(__)))  => begin
                    inParam
                  end

                  (SLOT(arg = SOME(DAE.ARRAY(ty = sty)), dims = vdims), _)  => begin
                       #=  If we have an array constant-evaluate the dimensions and make sure
                       =#
                       #=  They add up
                       =#
                      @match DAE.FUNCARG(ty = pty) = inParam
                       #=  evaluate the dimesions
                       =#
                      pty = evaluateFuncArgTypeDims(pty, inEnv, inCache)
                       #=  append the vectorization dim if argument is vectorized.
                       =#
                      dims1 = Types.getDimensions(pty)
                      dims1 = listAppend(vdims, dims1)
                      dims2 = Types.getDimensions(sty)
                      @match true = Expression.dimsEqual(dims1, dims2)
                      outParam = Types.setFuncArgType(inParam, pty)
                    outParam
                  end

                  (SLOT(arg = SOME(DAE.MATRIX(ty = sty)), dims = vdims), _)  => begin
                      @match DAE.FUNCARG(ty = pty) = inParam
                       #=  evaluate the dimesions
                       =#
                      pty = evaluateFuncArgTypeDims(pty, inEnv, inCache)
                       #=  append the vectorization dim if argument is vectorized.
                       =#
                      dims1 = Types.getDimensions(pty)
                      vdims = listAppend(dims1, vdims)
                      dims2 = Types.getDimensions(sty)
                      @match true = Expression.dimsEqual(vdims, dims2)
                      outParam = Types.setFuncArgType(inParam, pty)
                    outParam
                  end

                  _  => begin
                        @match DAE.FUNCARG(ty = pty) = inParam
                        pty = evaluateFuncArgTypeDims(pty, inEnv, inCache)
                        outParam = Types.setFuncArgType(inParam, pty)
                      outParam
                  end
                end
              end
          outParam
        end

         #= Constant evaluates the dimensions of a type. =#
        function evaluateFuncArgTypeDims(inType::DAE.Type, inEnv::FCore.Graph, inCache::FCore.Cache) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                  local n::ModelicaInteger
                  local dim::DAE.Dimension
                  local tys::List{DAE.Type}
                  local env::FCore.Graph
                   #=  Array type, evaluate the dimension.
                   =#
                @matchcontinue inType begin
                  DAE.T_ARRAY(ty, dim <|  nil())  => begin
                      @match (_, Values.INTEGER(n)) = Ceval.cevalDimension(inCache, inEnv, dim, false, Absyn.NO_MSG(), 0)
                      ty = evaluateFuncArgTypeDims(ty, inEnv, inCache)
                    DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(n)))
                  end

                  DAE.T_ARRAY(ty, dim <|  nil())  => begin
                       #=  Previous case failed, keep the dimension but evaluate the rest of the type.
                       =#
                      ty = evaluateFuncArgTypeDims(ty, inEnv, inCache)
                    DAE.T_ARRAY(ty, list(dim))
                  end

                  ty && DAE.T_TUPLE(__)  => begin
                      ty.types = ListUtil.map2(ty.types, evaluateFuncArgTypeDims, inEnv, inCache)
                    ty
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= Creates the actual function type of a CALL expression, used for error messages.
         This type is only created if checkTypes is false. =#
        function createActualFunctype(tp::DAE.Type, slots::List{<:Slot}, checkTypes::Bool) ::DAE.Type
              local outTp::DAE.Type = tp

              outTp = begin
                  local slotParams::List{DAE.FuncArg}
                  local params::List{DAE.FuncArg}
                  local restype::DAE.Type
                  local functionAttributes::DAE.FunctionAttributes
                @match (outTp, checkTypes) begin
                  (_, true)  => begin
                    tp
                  end

                  (DAE.T_FUNCTION(__), _)  => begin
                       #=  When not checking types, create function type by looking at the filled slots
                       =#
                      outTp.funcArg = funcArgsFromSlots(slots)
                    outTp
                  end
                end
              end
          outTp
        end

         #= author: PA
          This function checks all vectorized array dimensions in the slots and
          confirms that they all are of same dimension,or no dimension, i.e. not
          vectorized. The uniform vectorized array dimension is returned. =#
        function slotsVectorizable(inSlots::List{<:Slot}, info::SourceInfo) ::DAE.Dimensions
              local outDims::DAE.Dimensions

              outDims = begin
                  local ad::DAE.Dimensions
                  local rest::List{Slot}
                  local exp::DAE.Exp
                  local name::String
                @matchcontinue inSlots begin
                   nil()  => begin
                    nil
                  end

                  SLOT(defaultArg = DAE.FUNCARG(name = name), arg = SOME(exp), dims = ad && _ <| _) <| rest  => begin
                      sameSlotsVectorizable(rest, ad, name, exp, info)
                    ad
                  end

                  SLOT(dims =  nil()) <| rest  => begin
                    slotsVectorizable(rest, info)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("-slots_vectorizable failed\\n")
                      fail()
                  end
                end
              end
          outDims
        end

         #= author: PA
          This function succeds if all slots in the list either has the array
          dimension as given by the second argument or no array dimension at all.
          The array dimension must match both in dimension size and number of
          dimensions. =#
        function sameSlotsVectorizable(inSlots::List{<:Slot}, inDims::DAE.Dimensions, name::String, exp::DAE.Exp, info::SourceInfo)
              _ = begin
                  local slot_ad::DAE.Dimensions
                  local rest::List{Slot}
                  local exp2::DAE.Exp
                  local name2::String
                   #=  Array dims must match.
                   =#
                @match inSlots begin
                  SLOT(defaultArg = DAE.FUNCARG(name = name2), arg = SOME(exp2), dims = slot_ad && _ <| _) <| rest  => begin
                      sameArraydimLst(inDims, name, exp, slot_ad, name2, exp2, info)
                      sameSlotsVectorizable(rest, inDims, name, exp, info)
                    ()
                  end

                  SLOT(dims =  nil()) <| rest  => begin
                       #=  Empty array dims matches too.
                       =#
                      sameSlotsVectorizable(rest, inDims, name, exp, info)
                    ()
                  end

                   nil()  => begin
                    ()
                  end
                end
              end
        end

         #= author: PA
          Helper function to sameSlotsVectorizable.  =#
        function sameArraydimLst(inDims1::DAE.Dimensions, name1::String, exp1::DAE.Exp, inDims2::DAE.Dimensions, name2::String, exp2::DAE.Exp, info::SourceInfo)
              _ = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local ads1::DAE.Dimensions
                  local ads2::DAE.Dimensions
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local ad1::DAE.Dimension
                  local ad2::DAE.Dimension
                  local str1::String
                  local str2::String
                  local str3::String
                  local str4::String
                  local str::String
                @matchcontinue (inDims2, inDims2) begin
                  (DAE.DIM_INTEGER(integer = i1) <| ads1, DAE.DIM_INTEGER(integer = i2) <| ads2)  => begin
                      @match true = intEq(i1, i2)
                      sameArraydimLst(ads1, name1, exp1, ads2, name2, exp2, info)
                    ()
                  end

                  (DAE.DIM_UNKNOWN(__) <| ads1, DAE.DIM_UNKNOWN(__) <| ads2)  => begin
                      sameArraydimLst(ads1, name1, exp1, ads2, name2, exp2, info)
                    ()
                  end

                  (DAE.DIM_EXP(e1) <| ads1, DAE.DIM_EXP(e2) <| ads2)  => begin
                      @match true = Expression.expEqual(e1, e2)
                      sameArraydimLst(ads1, name1, exp1, ads2, name2, exp2, info)
                    ()
                  end

                  ( nil(),  nil())  => begin
                    ()
                  end

                  (ad1 <| _, ad2 <| _)  => begin
                      str1 = ExpressionDump.printExpStr(exp1)
                      str2 = ExpressionDump.printExpStr(exp2)
                      str3 = ExpressionDump.dimensionString(ad1)
                      str4 = ExpressionDump.dimensionString(ad2)
                      Error.addSourceMessage(Error.VECTORIZE_CALL_DIM_MISMATCH, list(name1, str1, name2, str2, str3, str4), info)
                    fail()
                  end
                end
              end
        end

         #= This function creates a Properties object from a DAE.Type and a
          DAE.TupleConst value. =#
        function getProperties(inType::DAE.Type, inTupleConst::DAE.TupleConst) ::DAE.Properties
              local outProperties::DAE.Properties

              outProperties = begin
                  local tt::DAE.Type
                  local t::DAE.Type
                  local ty::DAE.Type
                  local constType::DAE.TupleConst
                  local b::DAE.Const
                  local tystr::String
                  local conststr::String
                   #=  At least two elements in the type list, this is a tuple. LS: Tuples are fixed before here
                   =#
                @match (inType, inTupleConst) begin
                  (tt && DAE.T_TUPLE(__), constType)  => begin
                    DAE.PROP_TUPLE(tt, constType)
                  end

                  (t, DAE.TUPLE_CONST(tupleConstLst = DAE.SINGLE_CONST(constType = b) <|  nil()))  => begin
                    DAE.PROP(t, b)
                  end

                  (t, DAE.TUPLE_CONST(tupleConstLst = DAE.SINGLE_CONST(constType = b) <|  nil()))  => begin
                    DAE.PROP(t, b)
                  end

                  (t, DAE.SINGLE_CONST(constType = b))  => begin
                    DAE.PROP(t, b)
                  end

                  (ty, constType)  => begin
                       #=  One type, this is a tuple with one element. The resulting properties is then identical to that of a single expression.
                       =#
                       #=  failure
                       =#
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Static.getProperties failed: ")
                      tystr = Types.unparseType(ty)
                      conststr = Types.printTupleConstStr(constType)
                      Debug.trace(tystr)
                      Debug.trace(", ")
                      Debug.traceln(conststr)
                    fail()
                  end
                end
              end
          outProperties
        end

         #= author: PR
          This just splits the properties list into a type list and a const list.
          LS: Changed to take a Type, which is the functions return type.
          LS: Update: const is derived from the input arguments and sent here. =#
        function elabConsts(inType::DAE.Type, inConst::DAE.Const) ::DAE.TupleConst
              local outTupleConst::DAE.TupleConst

              outTupleConst = begin
                  local consts::List{DAE.TupleConst}
                  local tys::List{DAE.Type}
                  local c::DAE.Const
                  local ty::DAE.Type
                @match (inType, inConst) begin
                  (DAE.T_TUPLE(types = tys), c)  => begin
                      consts = checkConsts(tys, c)
                    DAE.TUPLE_CONST(consts)
                  end

                  (ty, c)  => begin
                      consts = checkConsts(list(ty), c)
                    DAE.TUPLE_CONST(consts)
                  end
                end
              end
               #=  LS: If not a tuple then one normal type, T_INTEGER etc, but we make a list of types
               =#
               #=  with one element and call the same check_consts, so that we always have DAE.TUPLE_CONST as result
               =#
          outTupleConst
        end

         #= LS: Changed to take a Type list, which is the functions return type. Only
           for functions returning a tuple
          LS: Update: const is derived from the input arguments and sent here  =#
        function checkConsts(inTypes::List{<:DAE.Type}, inConst::DAE.Const) ::List{DAE.TupleConst}
              local outTupleConsts::List{DAE.TupleConst}

              outTupleConsts = list(checkConst(ty, inConst) for ty in inTypes)
          outTupleConsts
        end

         #= author: PR
           At the moment this make all outputs non cons.
          All ouputs should be checked in the function body for constness.
          LS: but it says true?
          LS: Adapted to check one type instead of funcarg, since it just checks
          return type
          LS: Update: const is derived from the input arguments and sent here =#
        function checkConst(inType::DAE.Type, c::DAE.Const) ::DAE.TupleConst
              local outTupleConst::DAE.TupleConst

              outTupleConst = begin
                @match inType begin
                  DAE.T_TUPLE(__)  => begin
                      Error.addInternalError("No support for tuples built by tuples", sourceInfo())
                    fail()
                  end

                  _  => begin
                      DAE.SINGLE_CONST(c)
                  end
                end
              end
          outTupleConst
        end

         #= Splits the properties list into the separated types list and const list. =#
        function splitProps(inProperties::List{<:DAE.Properties}) ::Tuple{List{DAE.Type}, List{DAE.TupleConst}}
              local outConsts::List{DAE.TupleConst} = nil
              local outTypes::List{DAE.Type} = nil

              local ty::DAE.Type
              local c::DAE.Const
              local tc::DAE.TupleConst

              for prop in listReverse(inProperties)
                tc = begin
                  @match prop begin
                    DAE.PROP(type_ = ty, constFlag = c)  => begin
                      DAE.SINGLE_CONST(c)
                    end

                    DAE.PROP_TUPLE(type_ = ty, tupleConst = tc)  => begin
                      tc
                    end
                  end
                end
                outTypes = _cons(ty, outTypes)
                outConsts = _cons(tc, outConsts)
              end
          (outTypes, outConsts)
        end

         #= This function returns the types of a DAE.FuncArg list. =#
        function getTypes(farg::List{<:DAE.FuncArg}) ::List{DAE.Type}
              local outTypes::List{DAE.Type}

              outTypes = list(Types.funcArgType(arg) for arg in farg)
          outTypes
        end

         #= This function_ elaborates on a number of expressions and_ matches them to a
           number of `DAE.Var\\' objects, applying type_ conversions on the expressions
           when necessary to match the type_ of the DAE.Var.

           Positional arguments and named arguments are filled in the argument slots as:
             1. Positional arguments fill the first slots according to their position.
             2. Named arguments fill slots with the same name as the named argument.
             3. Unfilled slots are checked so that they have default values, otherwise error. =#
        function elabInputArgs(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inSlots::List{<:Slot}, inOnlyOneFunction::Bool, inCheckTypes::Bool #= if true, check types =#, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inFuncType::DAE.Type #= Used to determine which arguments are structural. We will evaluate them later to figure if they are used in dimensions. So we evaluate them here to get a more optimised DAE =#, inPath::Absyn.Path, isGraphicsExp::Bool = false) ::Tuple{FCore.Cache, List{DAE.Exp}, List{Slot}, List{DAE.Const}, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings = nil
              local outConsts::List{DAE.Const}
              local outSlots::List{Slot} = inSlots
              local outExps::List{DAE.Exp}
              local outCache::FCore.Cache = inCache

              local fargs::List{DAE.FuncArg}
              local consts1::List{DAE.Const}
              local consts2::List{DAE.Const}

               #=  Empty function call, e.g. foo(), is always constant.
               =#
               #=  adrpo 2010-11-09: TODO! FIXME! This is not always true, RecordCall() can
               =#
               #=  contain DEFAULT bindings that are param.
               =#
              if listEmpty(inPosArgs) && listEmpty(inNamedArgs)
                outConsts = list(DAE.C_CONST())
              else
                fargs = funcArgsFromSlots(inSlots)
                (outCache, outSlots, consts1, outPolymorphicBindings) = elabPositionalInputArgs(outCache, inEnv, inPosArgs, fargs, outSlots, inOnlyOneFunction, inCheckTypes, inImplicit, outPolymorphicBindings, inPrefix, inInfo, inPath, isGraphicsExp)
                (outCache, outSlots, consts2, outPolymorphicBindings) = elabNamedInputArgs(outCache, inEnv, inNamedArgs, fargs, outSlots, inOnlyOneFunction, inCheckTypes, inImplicit, outPolymorphicBindings, inPrefix, inInfo, inPath, isGraphicsExp)
                outConsts = listAppend(consts1, consts2)
              end
               #=  Elaborate positional arguments.
               =#
               #=  Elaborate named arguments.
               =#
              (outCache, outSlots) = evaluateStructuralSlots(outCache, inEnv, outSlots, inFuncType)
              outExps = slotListArgs(outSlots)
          (outCache, outExps, outSlots, outConsts, outPolymorphicBindings)
        end

         #= Creates a list of empty slots given a list of function parameters. =#
        function makeEmptySlots(inArgs::List{<:DAE.FuncArg}) ::List{Slot}
              local outSlots::List{Slot}

              (outSlots, _) = ListUtil.mapFold(inArgs, makeEmptySlot, 1, Slot)
          outSlots
        end

        function makeEmptySlot(inArg::DAE.FuncArg, inIndex::ModelicaInteger) ::Tuple{Slot, ModelicaInteger}
              local outIndex::ModelicaInteger
              local outSlot::Slot

              outSlot = SLOT(inArg, false, NONE(), nil, inIndex, SLOT_NOT_EVALUATED)
              outIndex = inIndex + 1
          (outSlot, outIndex)
        end

         #= Converts a list of Slot to a list of FuncArg. =#
        function funcArgsFromSlots(inSlots::List{<:Slot}) ::List{DAE.FuncArg}
              local outFuncArgs::List{DAE.FuncArg}

              outFuncArgs = list(funcArgFromSlot(slot) for slot in inSlots)
          outFuncArgs
        end

        function funcArgFromSlot(inSlot::Slot) ::DAE.FuncArg
              local outFuncArg::DAE.FuncArg

              @match SLOT(defaultArg = outFuncArg) = inSlot
          outFuncArg
        end

         #= Creates an DAE.T_COMPLEX type from a list of slots.
           Used to create type of record constructors  =#
        function complexTypeFromSlots(inSlots::List{<:Slot}, complexClassType::ClassInf.SMNode) ::DAE.Type
              local outType::DAE.Type

              local id::String
              local ty::DAE.Type
              local vars::List{DAE.Var} = nil

              for slot in inSlots
                @match SLOT(defaultArg = DAE.FUNCARG(name = id, ty = ty)) = slot
                vars = _cons(Expression.makeVar(id, Types.simplifyType(ty)), vars)
              end
              vars = listReverse(vars)
              outType = DAE.T_COMPLEX(complexClassType, vars, NONE())
          outType
        end

         #= Gets the argument expressions from a list of slots. =#
        function slotListArgs(inSlots::List{<:Slot}) ::List{DAE.Exp}
              local outArgs::List{DAE.Exp}

              outArgs = ListUtil.filterMap(inSlots, slotArg)
          outArgs
        end

         #= Gets the argument from a slot. =#
        function slotArg(inSlot::Slot) ::DAE.Exp
              local outArg::DAE.Exp

              @match SLOT(arg = SOME(outArg)) = inSlot
          outArg
        end

         #= This function takes a slot list and a class definition of a function
          and fills  default values into slots which have not been filled.

          Special case for graphics exps =#
        function fillGraphicsDefaultSlots(inCache::FCore.Cache, inSlots::List{<:Slot}, inClass::SCode.Element, inEnv::FCore.Graph, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{Slot}, List{DAE.Const}, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings = nil
              local outConsts::List{DAE.Const} = nil
              local outSlots::List{Slot} = nil
              local outCache::FCore.Cache = inCache

              local filled::Bool
              local e::Absyn.Exp
              local exp::DAE.Exp
              local id::String
              local defarg::DAE.FuncArg
              local ty::DAE.Type
              local c::DAE.Const

              for slot in inSlots
                @match SLOT(slotFilled = filled) = slot
                if ! filled
                  slot = begin
                    @matchcontinue slot begin
                      SLOT(defaultArg = defarg && DAE.FUNCARG(__))  => begin
                           #=  Try to fill the slot if it's not yet filled.
                           =#
                          @match SCode.COMPONENT(modifications = SCode.MOD(binding = SOME(e))) = SCodeUtil.getElementNamed(defarg.name, inClass)
                          @match (outCache, exp, DAE.PROP(ty, c)) = elabExpInExpression(outCache, inEnv, e, inImplicit, true, inPrefix, inInfo)
                          (exp, _, outPolymorphicBindings) = Types.matchTypePolymorphic(exp, ty, defarg.ty, FGraphUtil.getGraphPathNoImplicitScope(inEnv), outPolymorphicBindings, false)
                          @match true = Types.constEqualOrHigher(c, defarg.constType)
                          outConsts = _cons(c, outConsts)
                          slot.slotFilled = true
                          slot.arg = SOME(exp)
                        slot
                      end

                      _  => begin
                          slot
                      end
                    end
                  end
                end
                outSlots = _cons(slot, outSlots)
              end
              outSlots = listReverse(outSlots)
              outConsts = listReverse(outConsts)
          (outCache, outSlots, outConsts, outPolymorphicBindings)
        end

         #= prints the slots to a string =#
        function printSlotsStr(inSlots::List{<:Slot}) ::String
              local outString::String

              outString = begin
                  local filled::Bool
                  local farg_str::String
                  local filledStr::String
                  local str::String
                  local s::String
                  local s1::String
                  local s2::String
                  local res::String
                  local str_lst::List{String}
                  local farg::DAE.FuncArg
                  local exp::Option{DAE.Exp}
                  local ds::DAE.Dimensions
                  local xs::List{Slot}
                @match inSlots begin
                  SLOT(defaultArg = farg, slotFilled = filled, arg = exp, dims = ds) <| xs  => begin
                      farg_str = Types.printFargStr(farg)
                      filledStr = if filled
                            "filled"
                          else
                            "not filled"
                          end
                      str = Dump.getOptionStr(exp, ExpressionDump.printExpStr)
                      str_lst = ListUtil.map(ds, ExpressionDump.dimensionString)
                      s = stringDelimitList(str_lst, ", ")
                      s1 = stringAppendList(list("SLOT(", farg_str, ", ", filledStr, ", ", str, ", [", s, "])\\n"))
                      s2 = printSlotsStr(xs)
                      res = stringAppend(s1, s2)
                    res
                  end

                   nil()  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Checks if inExp is a an expression of free parameters. =#
        function isFreeParameterExp(inExp::DAE.Exp, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{Bool, FCore.Cache}
              local outCache::FCore.Cache
              local isFree::Bool

              outCache = inCache
              isFree = begin
                  local cr::DAE.ComponentRef
                  local binding::DAE.Binding
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local exps::List{DAE.Exp}
                  local mat::List{List{DAE.Exp}}
                  local isFree2::Bool
                @match inExp begin
                  DAE.ICONST(__)  => begin
                    true
                  end

                  DAE.RCONST(__)  => begin
                    true
                  end

                  DAE.SCONST(__)  => begin
                    true
                  end

                  DAE.BCONST(__)  => begin
                    true
                  end

                  DAE.CREF(componentRef = cr)  => begin
                      (outCache, _, _, binding, _, _, _, _, _) = Lookup.lookupVar(inCache, inEnv, cr)
                    begin
                      @match binding begin
                        DAE.VALBOUND(__)  => begin
                          true
                        end

                        DAE.EQBOUND(exp = exp1) where (Expression.isConst(exp1))  => begin
                          true
                        end

                        _  => begin
                            false
                        end
                      end
                    end
                  end

                  DAE.BINARY(exp1 = exp1, exp2 = exp2)  => begin
                      (isFree, outCache) = isFreeParameterExp(exp1, inCache, inEnv)
                      (isFree2, outCache) = isFreeParameterExp(exp2, outCache, inEnv)
                    isFree && isFree2
                  end

                  DAE.UNARY(exp = exp1)  => begin
                      (isFree, outCache) = isFreeParameterExp(exp1, inCache, inEnv)
                    isFree
                  end

                  DAE.LBINARY(exp1 = exp1, exp2 = exp2)  => begin
                      (isFree, outCache) = isFreeParameterExp(exp1, inCache, inEnv)
                      (isFree2, outCache) = isFreeParameterExp(exp2, outCache, inEnv)
                    isFree && isFree2
                  end

                  DAE.LUNARY(exp = exp1)  => begin
                      (isFree, outCache) = isFreeParameterExp(exp1, inCache, inEnv)
                    isFree
                  end

                  DAE.CALL(expLst = exps)  => begin
                      outCache = inCache
                      isFree = true
                      for exp in exps
                        (isFree2, outCache) = isFreeParameterExp(exp, outCache, inEnv)
                        isFree = isFree && isFree2
                      end
                    isFree
                  end

                  DAE.ARRAY(array = exps)  => begin
                      outCache = inCache
                      isFree = true
                      for exp in exps
                        (isFree2, outCache) = isFreeParameterExp(exp, outCache, inEnv)
                        isFree = isFree && isFree2
                      end
                    isFree
                  end

                  DAE.MATRIX(matrix = mat)  => begin
                      outCache = inCache
                      isFree = true
                      for row in mat
                        for exp in row
                          (isFree2, outCache) = isFreeParameterExp(exp, outCache, inEnv)
                          isFree = isFree && isFree2
                        end
                      end
                    isFree
                  end

                  DAE.CAST(exp = exp1)  => begin
                      (isFree, outCache) = isFreeParameterExp(exp1, inCache, inEnv)
                    isFree
                  end

                  _  => begin
                      false
                  end
                end
              end
          (isFree, outCache)
        end

         #= This function elaborates the positional input arguments of a function.
          A list of slots is filled from the beginning with types of each
          positional argument. =#
        function elabPositionalInputArgs(inCache::FCore.Cache, inEnv::FCore.Graph, inPosArgs::List{<:Absyn.Exp}, inFuncArgs::List{<:DAE.FuncArg}, inSlots::List{<:Slot}, inOnlyOneFunction::Bool, inCheckTypes::Bool #= if true, check types =#, inImplicit::Bool, inPolymorphicBindings::InstTypes.PolymorphicBindings, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inPath::Absyn.Path, isGraphicsExp::Bool) ::Tuple{FCore.Cache, List{Slot}, List{DAE.Const}, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings = inPolymorphicBindings
              local outConsts::List{DAE.Const} = nil
              local outSlots::List{Slot} = inSlots
              local outCache::FCore.Cache = inCache

              local farg::DAE.FuncArg
              local farg_rest::List{DAE.FuncArg} = inFuncArgs
              local c::DAE.Const
              local position::ModelicaInteger = 1

              for arg in inPosArgs
                @match farg <| farg_rest = farg_rest
                (outCache, outSlots, c, outPolymorphicBindings) = elabPositionalInputArg(outCache, inEnv, arg, farg, position, outSlots, inOnlyOneFunction, inCheckTypes, inImplicit, outPolymorphicBindings, inPrefix, inInfo, inPath, isGraphicsExp)
                position = position + 1
                outConsts = _cons(c, outConsts)
              end
              outConsts = listReverse(outConsts)
          (outCache, outSlots, outConsts, outPolymorphicBindings)
        end

         #= This function elaborates the positional input arguments of a function.
          A list of slots is filled from the beginning with types of each
          positional argument. =#
        function elabPositionalInputArg(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, farg::DAE.FuncArg, position::ModelicaInteger, inSlotLst::List{<:Slot}, onlyOneFunction::Bool, checkTypes::Bool #= if true, check types =#, impl::Bool, inPolymorphicBindings::InstTypes.PolymorphicBindings, inPrefix::Prefix.PrefixType, info::SourceInfo, path::Absyn.Path, isGraphicsExp::Bool) ::Tuple{FCore.Cache, List{Slot}, DAE.Const, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings
              local outConst::DAE.Const
              local outSlotLst::List{Slot}
              local outCache::FCore.Cache

              local numErrors::ModelicaInteger = Error.getNumErrorMessages()

              (outCache, outSlotLst, outConst, outPolymorphicBindings) = begin
                  local slots::List{Slot}
                  local slots_1::List{Slot}
                  local newslots::List{Slot}
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local t::DAE.Type
                  local vt::DAE.Type
                  local c1::DAE.Const
                  local c2::DAE.Const
                  local pr::DAE.VarParallelism
                  local prop::DAE.Properties
                  local clist::List{DAE.Const}
                  local env::FCore.Graph
                  local e::Absyn.Exp
                  local es::List{Absyn.Exp}
                  local vs::List{DAE.FuncArg}
                  local ds::DAE.Dimensions
                  local cache::FCore.Cache
                  local id::String
                  local props::DAE.Properties
                  local pre::Prefix.PrefixType
                  local ct::DAE.CodeType
                  local polymorphicBindings::InstTypes.PolymorphicBindings
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local s5::String
                @matchcontinue (inCache, inEnv, inExp, farg, position, inSlotLst, onlyOneFunction, checkTypes, impl, inPolymorphicBindings, inPrefix) begin
                  (cache, env, e, DAE.FUNCARG(name = id, ty = vt && DAE.T_CODE(ct), par = pr), _, slots, _, true, _, polymorphicBindings, pre)  => begin
                      e_1 = elabCodeExp(e, cache, env, ct, info)
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, DAE.C_VAR(), pr, NONE()), e_1, nil, slots, pre, info, path)
                    (cache, slots_1, DAE.C_VAR(), polymorphicBindings)
                  end

                  (cache, env, e, DAE.FUNCARG(name = id, ty = vt, par = pr), _, slots, _, true, _, polymorphicBindings, pre)  => begin
                      (cache, e_1, props) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      t = Types.getPropType(props)
                      (vt, _) = Types.traverseType(vt, -1, Types.makeExpDimensionsUnknown)
                      c1 = Types.propAllConst(props)
                      (e_2, _, polymorphicBindings) = Types.matchTypePolymorphic(e_1, t, vt, FGraphUtil.getGraphPathNoImplicitScope(env), polymorphicBindings, false)
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, c1, pr, NONE()), e_2, nil, slots, pre, info, path) #= no vectorized dim =#
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, env, e, DAE.FUNCARG(name = id, ty = vt, par = pr), _, slots, _, true, _, polymorphicBindings, pre)  => begin
                      (cache, e_1, props) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      t = Types.getPropType(props)
                      (vt, _) = Types.traverseType(vt, -1, Types.makeExpDimensionsUnknown)
                      c1 = Types.propAllConst(props)
                      (e_2, _, ds, polymorphicBindings) = Types.vectorizableType(e_1, t, vt, FGraphUtil.getGraphPathNoImplicitScope(env))
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, c1, pr, NONE()), e_2, ds, slots, pre, info, path)
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, env, e, DAE.FUNCARG(name = id, par = pr), _, slots, _, false, _, polymorphicBindings, pre)  => begin
                      (cache, e_1, props) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      t = Types.getPropType(props)
                      c1 = Types.propAllConst(props)
                      slots_1 = fillSlot(DAE.FUNCARG(id, t, c1, pr, NONE()), e_1, nil, slots, pre, info, path)
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, env, e, DAE.FUNCARG(name = id, ty = vt), _, _, true, true, _, _, pre)  => begin
                      @match true = Error.getNumErrorMessages() == numErrors
                      (cache, e_1, prop) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      s1 = intString(position)
                      s2 = AbsynUtil.pathStringNoQual(path)
                      s3 = ExpressionDump.printExpStr(e_1)
                      s4 = Types.unparseTypeNoAttr(Types.getPropType(prop))
                      s5 = Types.unparseTypeNoAttr(vt)
                      Error.addSourceMessage(Error.ARG_TYPE_MISMATCH, list(s1, s2, id, s3, s4, s5), info)
                    fail()
                  end
                end
              end
               #=  exact match
               =#
               #=  check if vectorized argument
               =#
               #=  not checking types
               =#
               #= /* fill slot with actual type for error message*/ =#
               #=  check types and display error
               =#
               #= /* 1 function */ =#
               #= /* checkTypes */ =#
          (outCache, outSlotLst, outConst, outPolymorphicBindings)
        end

         #= This function takes an Env, a NamedArg list, a DAE.FuncArg list and a
          Slot list.
          It builds up a new slot list and a list of elaborated expressions.
          If a slot is filled twice the function fails. If a slot is not filled at
          all and the
          value is not a parameter or a constant the function also fails. =#
        function elabNamedInputArgs(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynNamedArgLst::List{<:Absyn.NamedArg}, inTypesFuncArgLst::List{<:DAE.FuncArg}, inSlotLst::List{<:Slot}, onlyOneFunction::Bool, checkTypes::Bool #= if true, check types =#, impl::Bool, inPolymorphicBindings::InstTypes.PolymorphicBindings, inPrefix::Prefix.PrefixType, info::SourceInfo, path::Absyn.Path, isGraphicsExp::Bool) ::Tuple{FCore.Cache, List{Slot}, List{DAE.Const}, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings
              local outTypesConstLst::List{DAE.Const}
              local outSlotLst::List{Slot}
              local outCache::FCore.Cache

              (outCache, outSlotLst, outTypesConstLst, outPolymorphicBindings) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local t::DAE.Type
                  local vt::DAE.Type
                  local c1::DAE.Const
                  local pr::DAE.VarParallelism
                  local slots_1::List{Slot}
                  local newslots::List{Slot}
                  local slots::List{Slot}
                  local clist::List{DAE.Const}
                  local env::FCore.Graph
                  local id::String
                  local pre_str::String
                  local e::Absyn.Exp
                  local na::Absyn.NamedArg
                  local nas::List{Absyn.NamedArg}
                  local narg::List{Absyn.NamedArg}
                  local farg::List{DAE.FuncArg}
                  local ct::DAE.CodeType
                  local cache::FCore.Cache
                  local ds::DAE.Dimensions
                  local pre::Prefix.PrefixType
                  local polymorphicBindings::InstTypes.PolymorphicBindings
                   #=  the empty case
                   =#
                @match (inCache, inEnv, inAbsynNamedArgLst, inTypesFuncArgLst, inSlotLst, inPolymorphicBindings) begin
                  (cache, _,  nil(), _, slots, _)  => begin
                    (cache, slots, nil, inPolymorphicBindings)
                  end

                  (cache, env, na <| nas, farg, slots, polymorphicBindings)  => begin
                      (cache, slots, c1, polymorphicBindings) = elabNamedInputArg(cache, env, na, farg, slots, onlyOneFunction, checkTypes, impl, polymorphicBindings, inPrefix, info, path, Error.getNumErrorMessages(), isGraphicsExp)
                      (cache, slots, clist, polymorphicBindings) = elabNamedInputArgs(cache, env, nas, farg, slots, onlyOneFunction, checkTypes, impl, polymorphicBindings, inPrefix, info, path, isGraphicsExp)
                    (cache, slots, _cons(c1, clist), polymorphicBindings)
                  end
                end
              end
          (outCache, outSlotLst, outTypesConstLst, outPolymorphicBindings)
        end

         #= This function takes an Env, a NamedArg list, a DAE.FuncArg list and a
          Slot list.
          It builds up a new slot list and a list of elaborated expressions.
          If a slot is filled twice the function fails. If a slot is not filled at
          all and the
          value is not a parameter or a constant the function also fails. =#
        function elabNamedInputArg(inCache::FCore.Cache, inEnv::FCore.Graph, inNamedArg::Absyn.NamedArg, inTypesFuncArgLst::List{<:DAE.FuncArg}, inSlotLst::List{<:Slot}, onlyOneFunction::Bool, checkTypes::Bool #= if true, check types =#, impl::Bool, inPolymorphicBindings::InstTypes.PolymorphicBindings, inPrefix::Prefix.PrefixType, info::SourceInfo, path::Absyn.Path, numErrors::ModelicaInteger, isGraphicsExp::Bool) ::Tuple{FCore.Cache, List{Slot}, DAE.Const, InstTypes.PolymorphicBindings}
              local outPolymorphicBindings::InstTypes.PolymorphicBindings
              local outTypesConstLst::DAE.Const
              local outSlotLst::List{Slot}
              local outCache::FCore.Cache

              (outCache, outSlotLst, outTypesConstLst, outPolymorphicBindings) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local t::DAE.Type
                  local vt::DAE.Type
                  local c1::DAE.Const
                  local pr::DAE.VarParallelism
                  local slots_1::List{Slot}
                  local newslots::List{Slot}
                  local slots::List{Slot}
                  local clist::List{DAE.Const}
                  local env::FCore.Graph
                  local id::String
                  local pre_str::String
                  local str::String
                  local e::Absyn.Exp
                  local nas::List{Absyn.NamedArg}
                  local narg::List{Absyn.NamedArg}
                  local farg::List{DAE.FuncArg}
                  local ct::DAE.CodeType
                  local cache::FCore.Cache
                  local ds::DAE.Dimensions
                  local pre::Prefix.PrefixType
                  local polymorphicBindings::InstTypes.PolymorphicBindings
                  local prop::DAE.Properties
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                @matchcontinue (inCache, inEnv, inNamedArg, inTypesFuncArgLst, inSlotLst, onlyOneFunction, checkTypes, impl, inPolymorphicBindings, inPrefix) begin
                  (cache, env, Absyn.NAMEDARG(argName = id, argValue = e), farg, slots, _, true, _, polymorphicBindings, pre)  => begin
                      @match (vt && DAE.T_CODE(ty = ct)) = findNamedArgType(id, farg)
                      pr = findNamedArgParallelism(id, farg)
                      e_1 = elabCodeExp(e, cache, env, ct, info)
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, DAE.C_VAR(), pr, NONE()), e_1, nil, slots, pre, info, path)
                    (cache, slots_1, DAE.C_VAR(), polymorphicBindings)
                  end

                  (cache, env, Absyn.NAMEDARG(argName = id, argValue = e), farg, slots, _, true, _, polymorphicBindings, pre)  => begin
                      vt = findNamedArgType(id, farg)
                      pr = findNamedArgParallelism(id, farg)
                      @match (cache, e_1, DAE.PROP(t, c1)) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      (e_2, _, polymorphicBindings) = Types.matchTypePolymorphic(e_1, t, vt, FGraphUtil.getGraphPathNoImplicitScope(env), polymorphicBindings, false)
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, c1, pr, NONE()), e_2, nil, slots, pre, info, path)
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, env, Absyn.NAMEDARG(argName = id, argValue = e), farg, slots, _, true, _, polymorphicBindings, pre)  => begin
                      vt = findNamedArgType(id, farg)
                      pr = findNamedArgParallelism(id, farg)
                      @match (cache, e_1, DAE.PROP(t, c1)) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      (e_2, _, ds, polymorphicBindings) = Types.vectorizableType(e_1, t, vt, FGraphUtil.getGraphPathNoImplicitScope(env))
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, c1, pr, NONE()), e_2, ds, slots, pre, info, path)
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, env, Absyn.NAMEDARG(argName = id, argValue = e), farg, slots, _, false, _, polymorphicBindings, pre)  => begin
                      vt = findNamedArgType(id, farg)
                      pr = findNamedArgParallelism(id, farg)
                      @match (cache, e_1, DAE.PROP(_, c1)) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      slots_1 = fillSlot(DAE.FUNCARG(id, vt, c1, pr, NONE()), e_1, nil, slots, pre, info, path)
                    (cache, slots_1, c1, polymorphicBindings)
                  end

                  (cache, _, Absyn.NAMEDARG(argName = id), farg, slots, true, _, _, polymorphicBindings, _)  => begin
                      @shouldFail _ = findNamedArgType(id, farg)
                      s1 = AbsynUtil.pathStringNoQual(path)
                      Error.addSourceMessage(Error.NO_SUCH_PARAMETER, list(s1, id), info)
                      @match true = isGraphicsExp
                    (cache, slots, DAE.C_CONST(), polymorphicBindings)
                  end

                  (cache, env, Absyn.NAMEDARG(argName = id, argValue = e), farg, _, true, true, _, _, pre)  => begin
                      @match true = Error.getNumErrorMessages() == numErrors
                      vt = findNamedArgType(id, farg)
                      (cache, e_1, prop) = elabExpInExpression(cache, env, e, impl, true, pre, info)
                      s1 = AbsynUtil.pathStringNoQual(path)
                      s2 = ExpressionDump.printExpStr(e_1)
                      s3 = Types.unparseTypeNoAttr(Types.getPropType(prop))
                      s4 = Types.unparseTypeNoAttr(vt)
                      Error.addSourceMessage(Error.NAMED_ARG_TYPE_MISMATCH, list(s1, id, s2, s3, s4), info)
                    fail()
                  end
                end
              end
               #=  check types exact match
               =#
               #=  check types vectorized argument
               =#
               #=  do not check types
               =#
               #= /* only 1 function */ =#
               #=  failure
               =#
               #= /* 1 function */ =#
               #= /* checkTypes */ =#
          (outCache, outSlotLst, outTypesConstLst, outPolymorphicBindings)
        end

        function findNamedArg(inIdent::String, inArgs::List{<:DAE.FuncArg}) ::DAE.FuncArg
              local outArg::DAE.FuncArg

              local id::String
              local haveMM::Bool = Config.acceptMetaModelicaGrammar()
              local inIdent2::String = if haveMM
                    "in_" + inIdent
                  else
                    ""
                  end

              for arg in inArgs
                @match DAE.FUNCARG(name = id) = arg
                if id == inIdent || haveMM && id == inIdent2
                  outArg = arg
                  return outArg
                end
              end
              fail()
          outArg
        end

         #= This function takes an Ident and a FuncArg list, and returns the FuncArg
           which has  that identifier.
           Used for instance when looking up named arguments from the function type. =#
        function findNamedArgType(inIdent::String, inArgs::List{<:DAE.FuncArg}) ::DAE.Type
              local outType::DAE.Type

              @match DAE.FUNCARG(ty = outType) = findNamedArg(inIdent, inArgs)
          outType
        end

         #= This function takes an Ident and a FuncArg list, and returns the
           parallelism of the FuncArg which has  that identifier. =#
        function findNamedArgParallelism(inIdent::String, inArgs::List{<:DAE.FuncArg}) ::DAE.VarParallelism
              local outParallelism::DAE.VarParallelism

              @match DAE.FUNCARG(par = outParallelism) = findNamedArg(inIdent, inArgs)
          outParallelism
        end

         #= This function takses a `FuncArg\\' and an DAE.Exp and a Slot list and fills
          the slot holding the FuncArg, by setting the boolean value of the slot
          and setting the expression. The function fails if the slot is allready set. =#
        function fillSlot(inFuncArg::DAE.FuncArg, inExp::DAE.Exp, inDims::DAE.Dimensions, inSlotLst::List{<:Slot}, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, fn::Absyn.Path) ::List{Slot}
              local outSlotLst::List{Slot} = nil

              local fa1::String
              local fa2::String
              local exp_str::String
              local c_str::String
              local pre_str::String
              local ty1::DAE.Type
              local ty2::DAE.Type
              local c1::DAE.Const
              local c2::DAE.Const
              local prl::DAE.VarParallelism
              local binding::Option{DAE.Exp}
              local filled::Bool
              local idx::ModelicaInteger
              local ses::ModelicaInteger
              local slot::Slot
              local rest_slots::List{Slot} = inSlotLst

              @match DAE.FUNCARG(name = fa1, ty = ty1, constType = c1) = inFuncArg
              while ! listEmpty(rest_slots)
                @match slot <| rest_slots = rest_slots
                @match SLOT(defaultArg = DAE.FUNCARG(name = fa2)) = slot
                if stringEq(fa1, fa2) || stringEq("in_" + fa1, fa2)
                  @match SLOT(defaultArg = DAE.FUNCARG(constType = c2, par = prl, defaultBinding = binding), slotFilled = filled, idx = idx, evalStatus = ses) = slot
                  if filled
                    pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                    Error.addSourceMessageAndFail(Error.FUNCTION_SLOT_ALREADY_FILLED, list(fa2, pre_str), inInfo)
                  end
                  if ! Types.constEqualOrHigher(c1, c2)
                    exp_str = ExpressionDump.printExpStr(inExp)
                    c_str = Types.unparseConst(c2)
                    Error.addSourceMessageAndFail(Error.FUNCTION_SLOT_VARIABILITY, list(fa1, exp_str, AbsynUtil.pathStringNoQual(fn), Types.unparseConst(c1), c_str), inInfo)
                  end
                  slot = SLOT(DAE.FUNCARG(fa2, ty1, c2, prl, binding), true, SOME(inExp), inDims, idx, ses)
                  outSlotLst = ListUtil.append_reverse(outSlotLst, _cons(slot, rest_slots))
                  return outSlotLst
                end
                outSlotLst = _cons(slot, outSlotLst)
              end
               #=  Check if this slot has the same name as the one we're looking for.
               =#
               #= /* OM extension input output arguments */ =#
               #=  Fail if the slot is already filled.
               =#
               #=  Fail if the variability is wrong.
               =#
               #=  Found a valid slot, fill it and reconstruct the slot list.
               =#
              Error.addSourceMessageAndFail(Error.NO_SUCH_PARAMETER, list("", fa1), inInfo)
          outSlotLst
        end

         #=
        function: elabCref
          Elaborate on a component reference.  Check the type of the
          component referred to, and check if the environment contains
          either a constant binding for that variable, or if it contains an
          equation binding with a constant expression. =#
        function elabCref(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, inImplicit::Bool #= implicit instantiation =#, performVectorization::Bool #= true => generates vectorized expressions, {v[1],v[2],...} =#, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, Option{Tuple{DAE.Exp, DAE.Properties, DAE.Attributes}}}
              local res::Option{Tuple{DAE.Exp, DAE.Properties, DAE.Attributes}}
              local outCache::FCore.Cache

              (outCache, res) = elabCref1(inCache, inEnv, inComponentRef, inImplicit, performVectorization, inPrefix, true, info)
          (outCache, res)
        end

         #=
          Some functions expect a DAE.ComponentRef back and use this instead of elabCref :) =#
        function elabCrefNoEval(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, inImplicit::Bool #= implicit instantiation =#, performVectorization::Bool #= true => generates vectorized expressions, {v[1],v[2],...} =#, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties, DAE.Attributes}
              local outAttributes::DAE.Attributes
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              @match (outCache, SOME((outExp, outProperties, outAttributes))) = elabCref1(inCache, inEnv, inComponentRef, inImplicit, performVectorization, inPrefix, false, info)
          (outCache, outExp, outProperties, outAttributes)
        end

         #=
        function: elabCref
          Elaborate on a component reference.  Check the type of the
          component referred to, and check if the environment contains
          either a constant binding for that variable, or if it contains an
          equation binding with a constant expression. =#
        function elabCref1(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, inImplicit::Bool #= implicit instantiation =#, performVectorization::Bool #= true => generates vectorized expressions, {v[1],v[2],...} =#, inPrefix::Prefix.PrefixType, evalCref::Bool, info::SourceInfo) ::Tuple{FCore.Cache, Option{Tuple{DAE.Exp, DAE.Properties, DAE.Attributes}}}
              local res::Option{Tuple{DAE.Exp, DAE.Properties, DAE.Attributes}}
              local outCache::FCore.Cache

              (outCache, res) = begin
                  local c_1::DAE.ComponentRef
                  local constType::DAE.Const
                  local const1::DAE.Const
                  local const2::DAE.Const
                  local constCref::DAE.Const
                  local constSubs::DAE.Const
                  local t::DAE.Type
                  local origt::DAE.Type
                  local sub_ty::DAE.Type
                  local tt::DAE.Type
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local crefExp::DAE.Exp
                  local expASUB::DAE.Exp
                  local env::FCore.Graph
                  local c::Absyn.ComponentRef
                  local cache::FCore.Cache
                  local impl::Bool
                  local doVect::Bool
                  local isBuiltinFn::Bool
                  local isBuiltinFnOrInlineBuiltin::Bool
                  local hasZeroSizeDim::Bool
                  local et::DAE.Type
                  local s::String
                  local scope::String
                  local splicedExpData::InstTypes.SplicedExpData
                  local path::Absyn.Path
                  local fpath::Absyn.Path
                  local enum_lit_strs::List{String}
                  local typeStr::String
                  local id::String
                  local expCref::DAE.ComponentRef
                  local forIteratorConstOpt::Option{DAE.Const}
                  local pre::Prefix.PrefixType
                  local e::Absyn.Exp
                  local cl::SCode.Element
                  local isBuiltin::DAE.FunctionBuiltin
                  local attr::DAE.Attributes
                  local binding::DAE.Binding #= equation modification =#
                   #=  wildcard
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, inImplicit, inPrefix) begin
                  (cache, _, Absyn.WILD(__), _, _)  => begin
                      t = DAE.T_ANYTYPE_DEFAULT
                      et = Types.simplifyType(t)
                      crefExp = Expression.makeCrefExp(DAE.WILD(), et)
                    (cache, SOME((crefExp, DAE.PROP(t, DAE.C_VAR()), DAE.dummyAttrVar)))
                  end

                  (cache, _, Absyn.CREF_IDENT(name = "Boolean"), _, _)  => begin
                      exp = Expression.makeScalarArray(list(DAE.BCONST(false), DAE.BCONST(true)), DAE.T_BOOL_DEFAULT)
                      t = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(2)))
                    (cache, SOME((exp, DAE.PROP(t, DAE.C_CONST()), DAE.dummyAttrConst)))
                  end

                  (_, _, Absyn.CREF_IDENT(name = "time"), _, _)  => begin
                       #=  Boolean => {false, true}
                       =#
                      res = if isValidTimeScope(inEnv, info)
                            BUILTIN_TIME
                          else
                            NONE()
                          end
                    (inCache, res)
                  end

                  (cache, env, Absyn.CREF_IDENT(name = id, subscripts = Absyn.SUBSCRIPT(e) <|  nil()), impl, pre)  => begin
                       #=  MetaModelica arrays are only used in function context as IDENT, and at most one subscript
                       =#
                       #=  No vectorization is performed
                       =#
                      @match true = Config.acceptMetaModelicaGrammar()
                       #=  Elaborate the cref without the subscript.
                       =#
                      @match (cache, SOME((exp1, DAE.PROP(t, const1), attr))) = elabCref1(cache, env, Absyn.CREF_IDENT(id, nil), false, false, pre, evalCref, info)
                       #=  Check that the type is a MetaModelica array, and get the element type.
                       =#
                      t = Types.metaArrayElementType(t)
                       #=  Elaborate the subscript.
                       =#
                      @match (cache, exp2, DAE.PROP(sub_ty, const2)) = elabExpInExpression(cache, env, e, impl, false, pre, info)
                       #=  Unbox the subscript if it's boxed, since it will be converted to an
                       =#
                       #=  arrayGet/arrayUpdate in code generation.
                       =#
                      if Types.isMetaBoxedType(sub_ty)
                        sub_ty = Types.unboxedType(sub_ty)
                        exp2 = DAE.UNBOX(exp2, sub_ty)
                      end
                      @match true = Types.isScalarInteger(sub_ty)
                      constType = Types.constAnd(const1, const2)
                      exp = Expression.makeASUB(exp1, list(exp2))
                    (cache, SOME((exp, DAE.PROP(t, constType), attr)))
                  end

                  (cache, env, c, impl, pre)  => begin
                       #=  a normal cref
                       =#
                      c = replaceEnd(c)
                      env = if AbsynUtil.crefIsFullyQualified(inComponentRef)
                            FGraphUtil.topScope(inEnv)
                          else
                            inEnv
                          end
                      (cache, c_1, constSubs, hasZeroSizeDim) = elabCrefSubs(cache, env, inEnv, c, pre, Prefix.NOPRE(), impl, false, info)
                      (cache, attr, t, binding, forIteratorConstOpt, splicedExpData) = Lookup.lookupVar(cache, env, c_1)
                       #=  get the binding if is a constant
                       =#
                      (cache, exp, constType, attr) = elabCref2(cache, env, c_1, attr, constSubs, forIteratorConstOpt, t, binding, performVectorization, splicedExpData, pre, evalCref, info)
                      t = fixEnumerationType(t)
                      (exp, constType) = evaluateEmptyVariable(hasZeroSizeDim && evalCref, exp, t, constType)
                    (cache, SOME((exp, DAE.PROP(t, constType), attr)))
                  end

                  (cache, env, c, _, _)  => begin
                      c = replaceEnd(c)
                      path = AbsynUtil.crefToPath(c)
                      @match (cache, (@match SCode.CLASS(restriction = SCode.R_ENUMERATION()) = cl), env) = Lookup.lookupClass(cache, env, path)
                      typeStr = AbsynUtil.pathLastIdent(path)
                      path = FGraphUtil.joinScopePath(env, Absyn.IDENT(typeStr))
                      enum_lit_strs = SCodeUtil.componentNames(cl)
                      (exp, t) = makeEnumerationArray(path, enum_lit_strs)
                    (cache, SOME((exp, DAE.PROP(t, DAE.C_CONST()), DAE.dummyAttrConst)))
                  end

                  (cache, env, c, _, _)  => begin
                       #=  An enumeration type => array of enumeration literals.
                       =#
                       #= /* RO */ =#
                       #=  MetaModelica Partial Function
                       =#
                       #=  true = Flags.isSet(Flags.FNPTR) or Config.acceptMetaModelicaGrammar();
                       =#
                      path = AbsynUtil.crefToPath(c)
                       #=  call the lookup function that removes errors when it fails!
                       =#
                      @match (cache, list(t)) = lookupFunctionsInEnvNoError(cache, env, path, info)
                      (isBuiltin, isBuiltinFn, path) = isBuiltinFunc(path, t)
                      isBuiltinFnOrInlineBuiltin = ! valueEq(DAE.FUNCTION_NOT_BUILTIN(), isBuiltin)
                       #=  some builtin functions store {} there
                       =#
                      fpath = begin
                        @match t begin
                          DAE.T_FUNCTION(__)  => begin
                            t.path
                          end
                        end
                      end
                      origt = t
                      t = Types.makeFunctionPolymorphicReference(t)
                      c = AbsynUtil.pathToCref(fpath)
                      expCref = ComponentReference.toExpCref(c)
                      exp = Expression.makeCrefExp(expCref, DAE.T_FUNCTION_REFERENCE_FUNC(isBuiltinFnOrInlineBuiltin, origt))
                       #=  This is not done by lookup - only elabCall. So we should do it here.
                       =#
                      @match (cache, Util.SUCCESS()) = instantiateDaeFunction(cache, env, path, isBuiltinFn, NONE(), true)
                    (cache, SOME((exp, DAE.PROP(t, DAE.C_VAR()), DAE.dummyAttrConst)))
                  end

                  (cache, _, Absyn.CREF_IDENT("NONE",  nil()), _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      Error.addSourceMessage(Error.META_NONE_CREF, nil, info)
                    (cache, NONE())
                  end

                  (_, env, c, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Static.elabCref failed: " + Dump.printComponentRefStr(c) + " in env: " + FGraphUtil.printGraphPathStr(env))
                    fail()
                  end

                  (cache, env, c, impl, pre)  => begin
                      @shouldFail (_, _, _, _) = elabCrefSubs(cache, env, env, c, pre, Prefix.NOPRE(), impl, false, info)
                      s = Dump.printComponentRefStr(c)
                      scope = FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.LOOKUP_VARIABLE_ERROR, list(s, scope), info)
                    (cache, NONE())
                  end
                end
              end
               #= /* RO */ =#
               #=  MetaModelica extension
               =#
               #=  enabled with -d=failtrace
               =#
               #=  Debug.traceln(\"ENVIRONMENT:\\n\" + FGraphUtil.printGraphStr(env));
               =#
               #= /*
                   maybe we do have it but without a binding, so maybe we can actually type it!
                  case (cache,env,c,impl,doVect,pre,info)
                    equation
                      failure((_,_,_) = elabCrefSubs(cache,env, c, pre, Prefix.NOPRE(),impl,info));
                      id = AbsynUtil.crefFirstIdent(c);
                      (cache,DAE.TYPES_VAR(name, attributes, visibility, ty, binding, constOfForIteratorRange),
                             SOME((cl as SCode.COMPONENT(n, pref, SCode.ATTR(arrayDims = ad), Absyn.TPATH(tpath, _),m,comment,cond,info),cmod)),instStatus,_)
                        = Lookup.lookupIdent(cache, env, id);
                      print(\"Static: cref:\" + AbsynUtil.printComponentRefStr(c) + \" component first ident:\\n\" + SCodeDump.unparseElementStr(cl) + \"\\n\");
                      (cache, cl, env) = Lookup.lookupClass(cache, env, tpath);
                      print(\"Static: cref:\" + AbsynUtil.printComponentRefStr(c) + \" class component first ident:\\n\" + SCodeDump.unparseElementStr(cl) + \"\\n\");
                    then
                      (cache,NONE());*/ =#
               #=  No need to add prefix info since problem only depends on the scope?
               =#
          (outCache, res)
        end

         #= Checks if time is allowed to be used in the current scope. =#
        function isValidTimeScope(inEnv::FCore.Graph, inInfo::SourceInfo) ::Bool
              local outIsValid::Bool

              local res::SCode.Restriction

              try
                res = FGraphUtil.lastScopeRestriction(inEnv)
              catch
                outIsValid = true
                return outIsValid
              end
              outIsValid = begin
                @match res begin
                  SCode.R_CLASS(__)  => begin
                    true
                  end

                  SCode.R_OPTIMIZATION(__)  => begin
                    true
                  end

                  SCode.R_MODEL(__)  => begin
                    true
                  end

                  SCode.R_BLOCK(__)  => begin
                    true
                  end

                  _  => begin
                        Error.addSourceMessage(Error.INVALID_TIME_SCOPE, nil, inInfo)
                      false
                  end
                end
              end
          outIsValid
        end

        function lookupFunctionsInEnvNoError(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outTypesTypeLst::List{DAE.Type}
              local outCache::FCore.Cache

              (outCache, outTypesTypeLst) = begin
                @matchcontinue (inCache, inEnv, inPath, inInfo) begin
                  (_, _, _, _)  => begin
                      ErrorExt.setCheckpoint("Static.lookupFunctionsInEnvNoError")
                      (outCache, outTypesTypeLst) = Lookup.lookupFunctionsInEnv(inCache, inEnv, inPath, inInfo)
                      ErrorExt.rollBack("Static.lookupFunctionsInEnvNoError")
                    (outCache, outTypesTypeLst)
                  end

                  _  => begin
                        ErrorExt.rollBack("Static.lookupFunctionsInEnvNoError")
                      fail()
                  end
                end
              end
               #=  rollback lookup errors!
               =#
               #=  rollback lookup errors!
               =#
          (outCache, outTypesTypeLst)
        end

         #= A variable with a 0-length dimension can be evaluated.
          This is good to do because otherwise the C-code contains references to non-existing variables =#
        function evaluateEmptyVariable(hasZeroSizeDim::Bool, inExp::DAE.Exp, ty::DAE.Type, c::DAE.Const) ::Tuple{DAE.Exp, DAE.Const}
              local oc::DAE.Const
              local oexp::DAE.Exp

              (oexp, oc) = begin
                  local sc::Bool
                  local a::Bool
                  local et::DAE.Type
                  local ss::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local sub::List{DAE.Exp}
                  local exp::DAE.Exp
                @matchcontinue (hasZeroSizeDim, inExp, ty, c) begin
                  (true, DAE.ASUB(sub = sub), _, _)  => begin
                      a = Types.isArray(ty)
                      sc = boolNot(a)
                      et = Types.simplifyType(ty)
                      exp = DAE.ARRAY(et, sc, nil)
                      exp = Expression.makeASUB(exp, sub)
                    (exp, c)
                  end

                  (true, DAE.CREF(componentRef = cr), _, _)  => begin
                      a = Types.isArray(ty)
                      sc = boolNot(a)
                      et = Types.simplifyType(ty)
                      @match nil = ComponentReference.crefLastSubs(cr)
                      exp = DAE.ARRAY(et, sc, nil)
                    (exp, c)
                  end

                  (true, DAE.CREF(componentRef = cr), _, _)  => begin
                      a = Types.isArray(ty)
                      sc = boolNot(a)
                      et = Types.simplifyType(ty)
                      @match (ss && _ <| _) = ComponentReference.crefLastSubs(cr)
                      exp = DAE.ARRAY(et, sc, nil)
                      exp = Expression.makeASUB(exp, ListUtil.map(ss, Expression.getSubscriptExp))
                    (exp, c)
                  end

                  _  => begin
                      (inExp, c)
                  end
                end
              end
               #=  TODO: Use a DAE.ERROR() or something if this has subscripts?
               =#
               #=  TODO: Use a DAE.ERROR() or something if this has subscripts?
               =#
          (oexp, oc)
        end

         #= Removes the index from an enumeration type. =#
        function fixEnumerationType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local p::Absyn.Path
                  local n::List{String}
                  local v::List{DAE.Var}
                  local al::List{DAE.Var}
                @matchcontinue inType begin
                  DAE.T_ENUMERATION(index = SOME(_), path = p, names = n, literalVarLst = v, attributeLst = al)  => begin
                    DAE.T_ENUMERATION(NONE(), p, n, v, al)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= Takes the variability of a variable and the constness of it's subscripts and
          determines if the varibility of the variable should be raised. I.e.:
            parameter with variable subscripts => variable
            constant with variable subscripts => variable
            constant with parameter subscripts => parameter =#
        function applySubscriptsVariability(inVariability::SCode.Variability, inSubsConst::DAE.Const) ::SCode.Variability
              local outVariability::SCode.Variability

              outVariability = begin
                @match (inVariability, inSubsConst) begin
                  (SCode.PARAM(__), DAE.C_VAR(__))  => begin
                    SCode.VAR()
                  end

                  (SCode.CONST(__), DAE.C_VAR(__))  => begin
                    SCode.VAR()
                  end

                  (SCode.CONST(__), DAE.C_PARAM(__))  => begin
                    SCode.PARAM()
                  end

                  _  => begin
                      inVariability
                  end
                end
              end
          outVariability
        end

         #= Expands an enumeration type to an array of it's enumeration literals. =#
        function makeEnumerationArray(enumTypeName::Absyn.Path, enumLiterals::List{<:String}) ::Tuple{DAE.Exp, DAE.Type}
              local enumArrayType::DAE.Type
              local enumArray::DAE.Exp

              local enum_lit_expl::List{DAE.Exp}
              local sz::ModelicaInteger
              local ety::DAE.Type

              enum_lit_expl = Expression.makeEnumLiterals(enumTypeName, enumLiterals)
              sz = listLength(enumLiterals)
              ety = DAE.T_ARRAY(DAE.T_ENUMERATION(NONE(), enumTypeName, enumLiterals, nil, nil), list(DAE.DIM_ENUM(enumTypeName, enumLiterals, sz)))
              enumArray = DAE.ARRAY(ety, true, enum_lit_expl)
              enumArrayType = ety
          (enumArray, enumArrayType)
        end

         #= This is a helper function to elab_cref2.
          It investigates a DAE.Type in order to fill the subscript lists of a
          component reference. For instance, the name a.b with the type array of
          one dimension will become a.b[:]. =#
        function fillCrefSubscripts(inComponentRef::DAE.ComponentRef, inType::DAE.Type) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                   #= /*,slicedExp*/ =#
                  local e::DAE.ComponentRef
                  local cref_1::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                  local t::DAE.Type
                  local subs_1::List{DAE.Subscript}
                  local subs::List{DAE.Subscript}
                  local id::String
                  local ty2::DAE.Type
                   #=  no subscripts
                   =#
                @matchcontinue (inComponentRef, inType) begin
                  (e && DAE.CREF_IDENT(subscriptLst =  nil()), _)  => begin
                    e
                  end

                  (DAE.CREF_IDENT(ident = id, identType = ty2, subscriptLst = subs), t)  => begin
                      subs_1 = fillSubscripts(subs, t)
                    ComponentReference.makeCrefIdent(id, ty2, subs_1)
                  end

                  (DAE.CREF_QUAL(ident = id, subscriptLst = subs, componentRef = cref, identType = ty2), t)  => begin
                      subs = fillSubscripts(subs, ty2)
                      t = stripPrefixType(t, ty2)
                      cref_1 = fillCrefSubscripts(cref, t)
                    ComponentReference.makeCrefQual(id, ty2, subs, cref_1)
                  end
                end
              end
               #=  simple ident with non-empty subscripts
               =#
               #=  qualified ident with non-empty subscrips
               =#
          outComponentRef
        end

        function stripPrefixType(inType::DAE.Type, inPrefixType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::DAE.Type
                  local pt::DAE.Type
                @match (inType, inPrefixType) begin
                  (DAE.T_ARRAY(ty = t), DAE.T_ARRAY(ty = pt))  => begin
                    stripPrefixType(t, pt)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= Helper function to fillCrefSubscripts. =#
        function fillSubscripts(inExpSubscriptLst::List{<:DAE.Subscript}, inType::DAE.Type) ::List{DAE.Subscript}
              local outExpSubscriptLst::List{DAE.Subscript}

              outExpSubscriptLst = begin
                  local subs::List{DAE.Subscript}
                  local dims::DAE.Dimensions
                   #=  an array
                   =#
                @matchcontinue (inExpSubscriptLst, inType) begin
                  (_, DAE.T_ARRAY(__))  => begin
                      subs = ListUtil.fill(DAE.WHOLEDIM(), listLength(Types.getDimensions(inType)))
                      subs = ListUtil.stripN(subs, listLength(inExpSubscriptLst))
                      subs = listAppend(inExpSubscriptLst, subs)
                    subs
                  end

                  _  => begin
                      inExpSubscriptLst
                  end
                end
              end
               #=  not an array type!
               =#
          outExpSubscriptLst
        end

         #= This function does some more processing of crefs, like replacing a constant
           with its value and vectorizing a non-constant. =#
        function elabCref2(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::DAE.ComponentRef, inAttributes::DAE.Attributes, constSubs::DAE.Const, inIteratorConst::Option{<:DAE.Const}, inType::DAE.Type, inBinding::DAE.Binding, inVectorize::Bool #= true => vectorized expressions =#, splicedExpData::InstTypes.SplicedExpData, inPrefix::Prefix.PrefixType, evalCref::Bool, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Const, DAE.Attributes}
              local outAttributes::DAE.Attributes
              local outConst::DAE.Const
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local var::SCode.Variability = DAEUtil.getAttrVariability(inAttributes)

              (outExp, outConst, outAttributes) = begin
                  local ty::DAE.Type
                  local expTy::DAE.Type
                  local idTy::DAE.Type
                  local expIdTy::DAE.Type
                  local cr::DAE.ComponentRef
                  local subCr1::DAE.ComponentRef
                  local subCr2::DAE.ComponentRef
                  local e::DAE.Exp
                  local index::DAE.Exp
                  local sexp::Option{DAE.Exp}
                  local v::Values.Value
                  local env::FCore.Graph
                  local constType::DAE.Const
                  local s::String
                  local str::String
                  local scope::String
                  local pre_str::String
                  local binding::DAE.Binding
                  local i::ModelicaInteger
                  local p::Absyn.Path
                  local attr::DAE.Attributes
                  local subsc::List{DAE.Subscript}
                  local slice::DAE.Subscript
                   #=  If type not yet determined, component must be referencing itself.
                   =#
                   #=  Use the variability as the constness.
                   =#
                @matchcontinue (var, inType, inBinding, splicedExpData) begin
                  (_, DAE.T_UNKNOWN(__), _, _)  => begin
                      expTy = Types.simplifyType(inType)
                      constType = Types.variabilityToConst(var)
                    (DAE.CREF(inCref, expTy), constType, inAttributes)
                  end

                  (SCode.PARAM(__), _, DAE.EQBOUND(source = DAE.BINDING_FROM_START_VALUE(__)), _)  => begin
                       #=  adrpo: report a warning if the binding came from a start value!
                       =#
                       #=  lochel: I moved the warning to the back end for now
                       =#
                      @match true = Types.getFixedVarAttributeParameterOrConstant(inType)
                       #=  s := ComponentReference.printComponentRefStr(inCref);
                       =#
                       #=  pre_str := PrefixUtil.printPrefixStr2(inPrefix);
                       =#
                       #=  s := pre_str + s;
                       =#
                       #=  str := DAEUtil.printBindingExpStr(inBinding);
                       =#
                       #=  Error.addSourceMessage(Error.UNBOUND_PARAMETER_WITH_START_VALUE_WARNING, {s,str}, info);  Don't add source info here... Many models give multiple errors that are not filtered out
                       =#
                      binding = DAEUtil.setBindingSource(inBinding, DAE.BINDING_FROM_DEFAULT_VALUE())
                      (outCache, e, constType, attr) = elabCref2(outCache, inEnv, inCref, inAttributes, constSubs, inIteratorConst, inType, binding, inVectorize, splicedExpData, inPrefix, evalCref, info)
                    (e, constType, attr)
                  end

                  (SCode.CONST(__), DAE.T_ENUMERATION(index = SOME(i), path = p), _, _) where (evalCref)  => begin
                       #=  an enumeration literal -> simplify to a literal expression
                       =#
                      p = AbsynUtil.joinPaths(p, ComponentReference.crefLastPath(inCref))
                    (DAE.ENUM_LITERAL(p, i), DAE.C_CONST(), inAttributes)
                  end

                  (SCode.CONST(__), _, _, _) where (! evalCref)  => begin
                       #=  Don't evaluate constants if evalCref is false.
                       =#
                      expTy = Types.simplifyType(inType)
                    (Expression.makeCrefExp(inCref, expTy), DAE.C_CONST(), inAttributes)
                  end

                  (SCode.CONST(__), _, _, InstTypes.SPLICEDEXPDATA(__)) where (Types.isVar(constSubs))  => begin
                       #=  a constant with variable subscript
                       =#
                      cr = ComponentReference.crefStripLastSubs(inCref)
                      subsc = ComponentReference.crefLastSubs(inCref)
                      (outCache, v) = Ceval.cevalCref(outCache, inEnv, cr, false, Absyn.MSG(info), 0)
                      e = ValuesUtil.valueExp(v)
                      e = Expression.makeASUB(e, list(Expression.getSubscriptExp(sub) for sub in subsc))
                    (e, DAE.C_VAR(), inAttributes)
                  end

                  (SCode.CONST(__), _, binding, InstTypes.SPLICEDEXPDATA(_, idTy))  => begin
                       #=  a constant -> evaluate binding
                       =#
                      @match true = Types.equivtypes(inType, idTy)
                      try
                        (outCache, v) = Ceval.cevalCrefBinding(outCache, inEnv, inCref, binding, false, Absyn.MSG(info), 0)
                        e = ValuesUtil.valueExp(v)
                      catch
                        @match SOME(e) = DAEUtil.bindingExp(binding)
                        e = Expression.makeASUB(e, list(Expression.getSubscriptExp(sub) for sub in ComponentReference.crefLastSubs(inCref)))
                      end
                       #=  Couldn't evaluate binding, replace the cref with the unevaluated binding.
                       =#
                      constType = DAE.C_CONST()
                       #= Types.constAnd(DAE.C_CONST(), constSubs);
                       =#
                    (e, constType, inAttributes)
                  end

                  (SCode.CONST(__), _, _, _) where (isSome(inIteratorConst))  => begin
                       #=  a constant with some for iterator constness -> don't constant evaluate
                       =#
                      expTy = Types.simplifyType(inType)
                    (Expression.makeCrefExp(inCref, expTy), DAE.C_CONST(), inAttributes)
                  end

                  (SCode.CONST(__), _, DAE.EQBOUND(constant_ = DAE.C_CONST(__)), InstTypes.SPLICEDEXPDATA(sexp, idTy))  => begin
                       #=  a constant with a binding
                       =#
                      expTy = Types.simplifyType(inType) #= Constants with equal bindings should be constant, i.e. true
                                                          but const is passed on, allowing constants to have wrong bindings
                                                          This must be caught later on. =#
                      expIdTy = Types.simplifyType(idTy)
                      cr = fillCrefSubscripts(inCref, inType)
                      e = Expression.makeCrefExp(cr, expTy)
                      e = crefVectorize(inVectorize, e, inType, sexp, expIdTy)
                      (outCache, v) = Ceval.ceval(outCache, inEnv, e, false, Absyn.MSG(info), 0)
                      e = ValuesUtil.valueExp(v)
                    (e, DAE.C_CONST(), inAttributes)
                  end

                  (SCode.PARAM(__), _, _, InstTypes.SPLICEDEXPDATA(sexp, idTy)) where (DAEUtil.isBound(inBinding))  => begin
                       #=  evaluate parameters only if \"evalparam\" or Config.getEvaluateParametersInAnnotations() is set
                       =#
                       #=  TODO! also ceval if annotation Evaluate := true.
                       =#
                      @match true = Flags.isSet(Flags.EVAL_PARAM) || Config.getEvaluateParametersInAnnotations()
                       #=  make it a constant if evalparam is used
                       =#
                      attr = DAEUtil.setAttrVariability(inAttributes, SCode.CONST())
                      expTy = Types.simplifyType(inType) #= Constants with equal bindings should be constant, i.e. true
                                                          but const is passed on, allowing constants to have wrong bindings
                                                          This must be caught later on. =#
                      expIdTy = Types.simplifyType(idTy)
                      cr = fillCrefSubscripts(inCref, inType)
                      e = crefVectorize(inVectorize, Expression.makeCrefExp(cr, expTy), inType, sexp, expIdTy)
                      (outCache, v) = Ceval.ceval(outCache, inEnv, e, false, Absyn.MSG(info), 0)
                      e = ValuesUtil.valueExp(v)
                    (e, DAE.C_PARAM(), attr)
                  end

                  (SCode.CONST(__), _, DAE.EQBOUND(evaluatedExp = SOME(v), constant_ = DAE.C_CONST(__)), InstTypes.SPLICEDEXPDATA(SOME(DAE.CREF(componentRef = cr)), _))  => begin
                       #=  a constant array indexed by a for iterator -> transform into an array of values. HACK! HACK! UGLY! TODO! FIXME!
                       =#
                       #=  handles things like fcall(data[i]) in 1:X where data is a package constant of the form:
                       =#
                       #=  data:={Common.SingleGasesData.N2,Common.SingleGasesData.H2,Common.SingleGasesData.CO,Common.SingleGasesData.O2,Common.SingleGasesData.H2O, Common.SingleGasesData.CO2}
                       =#
                      @match list(DAE.INDEX(DAE.CREF(componentRef = subCr2)), DAE.SLICE(exp = e)) = ComponentReference.crefLastSubs(cr)
                      @match list(DAE.INDEX((@match DAE.CREF(componentRef = subCr1) = index))) = ComponentReference.crefLastSubs(inCref)
                      @match true = ComponentReference.crefEqual(subCr1, subCr2)
                      @match true = Expression.isArray(e) || Expression.isRange(e)
                      e = ValuesUtil.valueExp(v)
                      e = DAE.ASUB(e, list(index))
                    (e, DAE.C_CONST(), inAttributes)
                  end

                  (SCode.CONST(__), _, DAE.UNBOUND(__), _) where (isNone(inIteratorConst))  => begin
                       #=  constants without value should not produce error if they are not in a simulation model!
                       =#
                      if Flags.isSet(Flags.STATIC)
                        s = ComponentReference.printComponentRefStr(inCref)
                        scope = FGraphUtil.printGraphPathStr(inEnv)
                        pre_str = PrefixUtil.printPrefixStr2(inPrefix)
                        s = pre_str + s
                        Debug.traceln("- Static.elabCref2 failed on: " + pre_str + s + " with no constant binding in scope: " + scope)
                      end
                      expTy = Types.simplifyType(inType)
                      cr = fillCrefSubscripts(inCref, inType)
                      e = Expression.makeCrefExp(cr, expTy)
                    (e, DAE.C_CONST(), inAttributes)
                  end

                  (_, _, _, InstTypes.SPLICEDEXPDATA(sexp, idTy))  => begin
                       #=  Everything else, vectorize the cref.
                       =#
                      expTy = Types.simplifyType(inType)
                      expIdTy = Types.simplifyType(idTy)
                      cr = fillCrefSubscripts(inCref, inType)
                      e = crefVectorize(inVectorize, Expression.makeCrefExp(cr, expTy), inType, sexp, expIdTy)
                      constType = Types.variabilityToConst(var)
                    (e, constType, inAttributes)
                  end

                  _  => begin
                         #=  failure!
                         =#
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        pre_str = PrefixUtil.printPrefixStr2(inPrefix)
                        Debug.traceln("- Static.elabCref2 failed for: " + pre_str + ComponentReference.printComponentRefStr(inCref) + "\\n env:" + FGraphUtil.printGraphStr(inEnv))
                      fail()
                  end
                end
              end
          (outCache, outExp, outConst, outAttributes)
        end

         #= This function takes a DAE.Exp and a DAE.Type and if the expression
          is a ComponentRef and the type is an array it returns an array of
          component references with subscripts for each index.
          For instance, parameter Real x[3];
          gives cref_vectorize('x', <arraytype>) => '{x[1],x[2],x[3]}
          This is needed since the DAE does not know what the variable 'x' is,
          it only knows the variables 'x[1]', 'x[2]' and 'x[3]'.
          NOTE: Currently only works for one and two dimensions. =#
        function crefVectorize(performVectorization::Bool #= if false, return input =#, inExp::DAE.Exp, inType::DAE.Type, splicedExp::Option{<:DAE.Exp}, crefIdType::DAE.Type #= the type of the last cref ident, without considering subscripts. picked up from splicedExpData and used for crefs in vectorized exp =#) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local b1::Bool
                  local b2::Bool
                  local exptp::DAE.Type
                  local e::DAE.Exp
                  local cr::DAE.ComponentRef
                  local t::DAE.Type
                  local d1::DAE.Dimension
                  local d2::DAE.Dimension
                  local ds::ModelicaInteger
                  local ds2::ModelicaInteger
                   #=  no vectorization
                   =#
                @matchcontinue (performVectorization, inExp, inType, splicedExp, crefIdType) begin
                  (false, e, _, _, _)  => begin
                    e
                  end

                  (_, e, DAE.T_SUBTYPE_BASIC(complexType = t), _, _)  => begin
                      e = crefVectorize(true, e, t, NONE(), crefIdType)
                    e
                  end

                  (_, _, DAE.T_ARRAY(dims = d1 <|  nil(), ty = DAE.T_ARRAY(dims = d2 <|  nil())), SOME(DAE.CREF(componentRef = cr)), _)  => begin
                      b1 = Expression.dimensionSize(d1) < Config.vectorizationLimit()
                      b2 = Expression.dimensionSize(d2) < Config.vectorizationLimit()
                      @match true = boolAnd(b1, b2) || Config.vectorizationLimit() == 0
                      e = elabCrefSlice(cr, crefIdType)
                      e = elabMatrixToMatrixExp(e)
                    e
                  end

                  (_, _, DAE.T_ARRAY(dims = d1 <|  nil(), ty = t), SOME(DAE.CREF(componentRef = cr)), _)  => begin
                      @match false = Types.isArray(t)
                      @match true = Expression.dimensionSize(d1) < Config.vectorizationLimit() || Config.vectorizationLimit() == 0
                      e = elabCrefSlice(cr, crefIdType)
                    e
                  end

                  (_, DAE.CREF(componentRef = cr, ty = exptp), DAE.T_ARRAY(dims = d1 <|  nil(), ty = t && DAE.T_ARRAY(dims = d2 <|  nil())), _, _)  => begin
                      ds = Expression.dimensionSize(d1)
                      ds2 = Expression.dimensionSize(d2)
                      b1 = ds < Config.vectorizationLimit()
                      b2 = ds2 < Config.vectorizationLimit()
                      @match true = boolAnd(b1, b2) || Config.vectorizationLimit() == 0
                      @match true = listEmpty(ComponentReference.crefLastSubs(cr))
                      e = createCrefArray2d(cr, 1, ds, ds2, exptp, t, crefIdType)
                    e
                  end

                  (_, DAE.CREF(componentRef = cr, ty = exptp), DAE.T_ARRAY(dims = d1 <|  nil(), ty = t), _, _)  => begin
                      @match false = Types.isArray(t)
                      ds = Expression.dimensionSize(d1)
                      @match true = ds < Config.vectorizationLimit() || Config.vectorizationLimit() == 0
                      e = createCrefArray(cr, 1, ds, exptp, t, crefIdType)
                    e
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #=  types extending basictype
               =#
               #=  component reference and an array type with dimensions less than vectorization limit
               =#
               #=  matrix sizes > vectorization limit is not vectorized
               =#
               #=  vectorsizes > vectorization limit is not vectorized
               =#
          outExp
        end

         #= A function for extracting the type-dimension of the child to *me* to dimension *my* array-size.
          Also returns wheter the array is a scalar or not. =#
        function extractDimensionOfChild(inExp::DAE.Exp) ::Tuple{DAE.Dimensions, Bool}
              local isScalar::Bool
              local outExp::DAE.Dimensions

              (outExp, isScalar) = begin
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local ety::DAE.Type
                  local ety2::DAE.Type
                  local tl::DAE.Dimensions
                  local x::ModelicaInteger
                  local sc::Bool
                @matchcontinue inExp begin
                  DAE.ARRAY(ty = DAE.T_ARRAY(dims = tl), scalar = sc)  => begin
                    (tl, sc)
                  end

                  DAE.ARRAY(array = expl1 && exp2 && DAE.ARRAY(_, _, _) <| _)  => begin
                      (tl, _) = extractDimensionOfChild(exp2)
                      x = listLength(expl1)
                    (_cons(DAE.DIM_INTEGER(x), tl), false)
                  end

                  DAE.ARRAY(array = expl1)  => begin
                      x = listLength(expl1)
                    (list(DAE.DIM_INTEGER(x)), true)
                  end

                  DAE.CREF(_, _)  => begin
                    (nil, true)
                  end
                end
              end
          (outExp, isScalar)
        end

         #= Bjozac, 2007-05-29  Main function from now for vectorizing output.
          the subscriptlist should contain either 'done slices' or numbers representing
         dimension entries.
        Example:
        1) a is a real[2,3] with no subscripts, the input here should be
        CREF_IDENT('a',{DAE.SLICE(DAE.ARRAY(_,_,{1,2})), DAE.SLICE(DAE.ARRAY(_,_,{1,2,3}))})>
           ==> {{a[1,1],a[1,2],a[1,3]},{a[2,1],a[2,2],a[2,3]}}
        2) a is a real[3,3] with subscripts {1,2},{1,3}, the input should be
        CREF_IDENT('a',{DAE.SLICE(DAE.ARRAY(_,_,{DAE.INDEX(1),DAE.INDEX(2)})),
                        DAE.SLICE(DAE.ARRAY(_,_,{DAE.INDEX(1),DAE.INDEX(3)}))})
           ==> {{a[1,1],a[1,3]},{a[2,1],a[2,3]}} =#
        function elabCrefSlice(inCref::DAE.ComponentRef, inType::DAE.Type) ::DAE.Exp
              local outCref::DAE.Exp

              outCref = begin
                  local ssl::List{DAE.Subscript}
                  local id::String
                  local child::DAE.ComponentRef
                  local exp1::DAE.Exp
                  local childExp::DAE.Exp
                  local ety::DAE.Type
                  local prety::DAE.Type
                @match (inCref, inType) begin
                  (DAE.CREF_IDENT(ident = id, subscriptLst = ssl), ety)  => begin
                      exp1 = flattenSubscript(ssl, id, ety)
                    exp1
                  end

                  (DAE.CREF_QUAL(ident = id, identType = prety, subscriptLst = ssl, componentRef = child), ety)  => begin
                      childExp = elabCrefSlice(child, ety)
                      exp1 = flattenSubscript(ssl, id, prety)
                      exp1 = myMergeQualWithRest(exp1, childExp, ety)
                    exp1
                  end
                end
              end
          outCref
        end

         #= Incase we have a qual with child references, this function myMerges them.
          The input should be an array, or just one CREF_QUAL, of arrays...of arrays
          of CREF_QUALS and the same goes for 'rest'. Also the flat type as input. =#
        function myMergeQualWithRest(qual::DAE.Exp, rest::DAE.Exp, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local ety::DAE.Type
                  local iLst::DAE.Dimensions
                  local scalar::Bool
                   #=  a component reference
                   =#
                @match (qual, rest, inType) begin
                  (exp1 && DAE.CREF(_, _), exp2, _)  => begin
                    myMergeQualWithRest2(exp2, exp1)
                  end

                  (DAE.ARRAY(_, _, expl1), exp2, ety)  => begin
                      expl1 = ListUtil.map2(expl1, myMergeQualWithRest, exp2, ety)
                      exp2 = DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, expl1)
                      (iLst, scalar) = extractDimensionOfChild(exp2)
                      ety = Expression.arrayEltType(ety)
                      exp2 = DAE.ARRAY(DAE.T_ARRAY(ety, iLst), scalar, expl1)
                    exp2
                  end
                end
              end
               #=  an array
               =#
          outExp
        end

         #= Helper to myMergeQualWithRest, handles the case
          when the child-qual is arrays of arrays. =#
        function myMergeQualWithRest2(rest::DAE.Exp, qual::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local ssl::List{DAE.Subscript}
                  local cref::DAE.ComponentRef
                  local cref_2::DAE.ComponentRef
                  local id::String
                  local ety::DAE.Type
                  local ty2::DAE.Type
                  local iLst::DAE.Dimensions
                  local scalar::Bool
                   #=  a component reference
                   =#
                @match (rest, qual) begin
                  (DAE.CREF(cref, ety), DAE.CREF(DAE.CREF_IDENT(id, ty2, ssl), _))  => begin
                      cref_2 = ComponentReference.makeCrefQual(id, ty2, ssl, cref)
                    Expression.makeCrefExp(cref_2, ety)
                  end

                  (exp1 && DAE.ARRAY(ety, _, expl1), exp2 && DAE.CREF(DAE.CREF_IDENT(_, _, _), _))  => begin
                      expl1 = ListUtil.map1(expl1, myMergeQualWithRest2, exp2)
                      exp1 = DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, expl1)
                      (_, scalar) = extractDimensionOfChild(exp1)
                    DAE.ARRAY(ety, scalar, expl1)
                  end
                end
              end
               #=  an array
               =#
          outExp
        end

         #= to catch subscript free CREF's. =#
        function flattenSubscript(inSubs::List{<:DAE.Subscript}, name::String, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local id::String
                  local subs1::List{DAE.Subscript}
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local ety::DAE.Type
                  local cref_::DAE.ComponentRef
                   #=  empty list
                   =#
                @matchcontinue (inSubs, name, inType) begin
                  ( nil(), id, ety)  => begin
                      cref_ = ComponentReference.makeCrefIdent(id, ety, nil)
                      exp1 = Expression.makeCrefExp(cref_, ety)
                    exp1
                  end

                  (subs1, id, ety)  => begin
                      exp2 = flattenSubscript2(subs1, id, ety)
                    exp2
                  end
                end
              end
               #=  some subscripts present
               =#
               #=  {1,2,3}
               =#
          outExp
        end

         #=  BZ(2010-01-29): Changed to public to be able to vectorize crefs from other places
         =#

         #= This function takes the created 'invalid' subscripts
          and the name of the CREF and returning the CREFS
          Example: flattenSubscript2({SLICE({1,2}},SLICE({1}),\\\"a\\\",tp) ==> {{a[1,1]},{a[2,1]}}.

          This is done in several function calls, this specific
          function extracts the numbers ( 1,2 and 1 ).
           =#
        function flattenSubscript2(inSubs::List{<:DAE.Subscript}, name::String, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local id::String
                  local sub1::DAE.Subscript
                  local subs1::List{DAE.Subscript}
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local exp3::DAE.Exp
                  local ety::DAE.Type
                  local iLst::DAE.Dimensions
                  local scalar::Bool
                   #=  empty subscript
                   =#
                @matchcontinue (inSubs, name, inType) begin
                  ( nil(), _, _)  => begin
                    DAE.ARRAY(DAE.T_UNKNOWN_DEFAULT, false, nil)
                  end

                  (DAE.INDEX(exp = exp1 && DAE.ICONST(_)) <| subs1, id, ety)  => begin
                      exp2 = flattenSubscript2(subs1, id, ety)
                      exp2 = applySubscript(exp1, exp2, id, Expression.unliftArray(ety))
                    exp2
                  end

                  (DAE.SLICE(DAE.ARRAY(_, _, expl1 && DAE.ICONST(0) <|  nil())) <| subs1, id, ety)  => begin
                      exp2 = flattenSubscript2(subs1, id, ety)
                      expl2 = ListUtil.map3(expl1, applySubscript, exp2, id, ety)
                      exp3 = listHead(expl2)
                    exp3
                  end

                  (DAE.SLICE(DAE.ARRAY(_, _, expl1)) <| subs1, id, ety)  => begin
                      exp2 = flattenSubscript2(subs1, id, ety)
                    flattenSubscript3(expl1, id, ety, exp2)
                  end

                  (sub1 && DAE.SLICE(exp = DAE.RANGE(__)) <| subs1, id, ety)  => begin
                       #=  first subscript integer, ety
                       =#
                       #= print(\"1. flattened rest into \"+ExpressionDump.dumpExpStr(exp2,0)+\"\\n\");
                       =#
                       #= print(\"1. applied this subscript into \"+ExpressionDump.dumpExpStr(exp2,0)+\"\\n\");
                       =#
                       #=  special case for zero dimension...
                       =#
                       #=  {1,2,3}
                       =#
                       #= exp3 = removeDoubleEmptyArrays(exp3);
                       =#
                       #=  normal case;
                       =#
                       #=  {1,2,3}
                       =#
                      expl1 = Expression.expandRange(sub1.exp)
                      exp2 = flattenSubscript2(subs1, id, ety)
                    flattenSubscript3(expl1, id, ety, exp2)
                  end
                end
              end
          outExp
        end

        function flattenSubscript3(inSubscripts::List{<:DAE.Exp}, inName::String, inType::DAE.Type, inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local expl::List{DAE.Exp}
              local dims::List{DAE.Dimension}
              local scalar::Bool
              local ty::DAE.Type

              expl = list(applySubscript(e, inExp, inName, inType) for e in inSubscripts)
              outExp = DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, expl)
              (dims, scalar) = extractDimensionOfChild(outExp)
              ty = Expression.arrayEltType(inType)
              outExp = DAE.ARRAY(DAE.T_ARRAY(ty, dims), scalar, expl)
          outExp
        end

         #=  A help function, to prevent the {{}} look of empty arrays. =#
        function removeDoubleEmptyArrays(inArr::DAE.Exp) ::DAE.Exp
              local outArr::DAE.Exp

              outArr = begin
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local expl3::List{DAE.Exp}
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local sc::Bool
                @matchcontinue inArr begin
                  DAE.ARRAY(array = exp2 && DAE.ARRAY(array =  nil()) <|  nil())  => begin
                    exp2
                  end

                  DAE.ARRAY(ty = ty1, scalar = sc, array = expl1 && DAE.ARRAY(__) <| expl3)  => begin
                      expl3 = ListUtil.map(expl1, removeDoubleEmptyArrays)
                      exp1 = DAE.ARRAY(ty1, sc, expl3)
                    exp1
                  end

                  exp1  => begin
                    exp1
                  end

                  exp1  => begin
                      print("- Static.removeDoubleEmptyArrays failure for: " + ExpressionDump.printExpStr(exp1) + "\\n")
                    fail()
                  end
                end
              end
          outArr
        end

         #= here we apply the subscripts to the IDENTS of the CREF's.
          Special case for adressing INDEX[0], make an empty array.
          If we have an array of subscript, we call applySubscript2 =#
        function applySubscript(inSub::DAE.Exp #= dim n  =#, inSubs::DAE.Exp #= dim >n =#, name::String, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local id::String
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local ety::DAE.Type
                  local crty::DAE.Type
                  local arrDim::DAE.Dimensions
                  local cref_::DAE.ComponentRef
                @matchcontinue (inSub, inSubs, name, inType) begin
                  (_, exp1 && DAE.ARRAY(DAE.T_ARRAY(dims = arrDim), _,  nil()), _, _)  => begin
                      @match true = Expression.arrayContainZeroDimension(arrDim)
                    exp1
                  end

                  (DAE.ICONST(integer = 0), DAE.ARRAY(DAE.T_ARRAY(dims = arrDim), _, _), _, ety)  => begin
                      ety = Expression.arrayEltType(ety)
                    DAE.ARRAY(DAE.T_ARRAY(ety, _cons(DAE.DIM_INTEGER(0), arrDim)), true, nil)
                  end

                  (DAE.ICONST(integer = 0), _, _, ety)  => begin
                      ety = Expression.arrayEltType(ety)
                    DAE.ARRAY(DAE.T_ARRAY(ety, list(DAE.DIM_INTEGER(0))), true, nil)
                  end

                  (exp1, DAE.ARRAY(_, _,  nil()), id, ety)  => begin
                      @match true = Expression.isValidSubscript(exp1)
                      crty = Expression.unliftArray(ety) #= only subscripting one dimension, unlifting once  =#
                      cref_ = ComponentReference.makeCrefIdent(id, ety, list(DAE.INDEX(exp1)))
                    Expression.makeCrefExp(cref_, crty)
                  end

                  (exp1, exp2, _, ety)  => begin
                      @match true = Expression.isValidSubscript(exp1)
                    applySubscript2(exp1, exp2, ety)
                  end
                end
              end
               #= /* add dimensions */ =#
          outExp
        end

         #= Handles multiple subscripts for the expression.
          If it is an array, we listmap applySubscript3 =#
        function applySubscript2(inSub::DAE.Exp #= The subs to add =#, inSubs::DAE.Exp #= The already created subs =#, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local id::String
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local subs::List{DAE.Subscript}
                  local ety::DAE.Type
                  local ty2::DAE.Type
                  local crty::DAE.Type
                  local iLst::DAE.Dimensions
                  local scalar::Bool
                  local cref_::DAE.ComponentRef
                @match (inSub, inSubs, inType) begin
                  (exp1, DAE.CREF(DAE.CREF_IDENT(id, ty2, subs), _), _)  => begin
                      crty = Expression.unliftArrayTypeWithSubs(_cons(DAE.INDEX(exp1), subs), ty2)
                      cref_ = ComponentReference.makeCrefIdent(id, ty2, _cons(DAE.INDEX(exp1), subs))
                      exp2 = Expression.makeCrefExp(cref_, crty)
                    exp2
                  end

                  (exp1, DAE.ARRAY(_, _, expl1), ety)  => begin
                      expl1 = ListUtil.map2(expl1, applySubscript3, exp1, ety)
                      exp2 = DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, expl1)
                      (iLst, scalar) = extractDimensionOfChild(exp2)
                      ety = Expression.arrayEltType(ety)
                      exp2 = DAE.ARRAY(DAE.T_ARRAY(ety, iLst), scalar, expl1)
                    exp2
                  end
                end
              end
          outExp
        end

         #= Final applySubscript function, here we call ourself
          recursive until we have the CREFS we are looking for. =#
        function applySubscript3(inSubs::DAE.Exp #= The already created subs =#, inSub::DAE.Exp #= The subs to add =#, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local id::String
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local subs::List{DAE.Subscript}
                  local ety::DAE.Type
                  local ty2::DAE.Type
                  local crty::DAE.Type
                  local iLst::DAE.Dimensions
                  local scalar::Bool
                  local cref_::DAE.ComponentRef
                @match (inSubs, inSub, inType) begin
                  (DAE.CREF(DAE.CREF_IDENT(id, ty2, subs), _), exp1, _)  => begin
                      crty = Expression.unliftArrayTypeWithSubs(_cons(DAE.INDEX(exp1), subs), ty2)
                      cref_ = ComponentReference.makeCrefIdent(id, ty2, _cons(DAE.INDEX(exp1), subs))
                      exp2 = Expression.makeCrefExp(cref_, crty)
                    exp2
                  end

                  (DAE.ARRAY(_, _, expl1), exp1, ety)  => begin
                      expl1 = ListUtil.map2(expl1, applySubscript3, exp1, ety)
                      exp2 = DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, expl1)
                      (iLst, scalar) = extractDimensionOfChild(exp2)
                      ety = Expression.arrayEltType(ety)
                      exp2 = DAE.ARRAY(DAE.T_ARRAY(ety, iLst), scalar, expl1)
                    exp2
                  end
                end
              end
          outExp
        end

         #= author: PA

          Takes an expression that is a function call and an expresion list
          and maps the call to each expression in the list.
          For instance, call_vectorize(DAE.CALL(XX(\\\"der\\\",),...),{1,2,3}))
          => {DAE.CALL(XX(\\\"der\\\"),{1}), DAE.CALL(XX(\\\"der\\\"),{2}),DAE.CALL(XX(\\\"der\\\",{3}))}
          NOTE: the vectorized expression is inserted first in the argument list
         of the call, so if extra arguments should be passed these can be given as
         input to the call expression. =#
        function callVectorize(inExp::DAE.Exp, inExpExpLst::List{<:DAE.Exp}) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = begin
                  local e::DAE.Exp
                  local callexp::DAE.Exp
                  local es_1::List{DAE.Exp}
                  local args::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local fn::Absyn.Path
                  local tuple_::Bool
                  local builtin::Bool
                  local inl::DAE.InlineType
                  local tp::DAE.Type
                  local attr::DAE.CallAttributes
                   #=  empty list
                   =#
                @matchcontinue (inExp, inExpExpLst) begin
                  (_,  nil())  => begin
                    nil
                  end

                  (callexp && DAE.CALL(fn, args, attr), e <| es)  => begin
                      es_1 = callVectorize(callexp, es)
                    _cons(DAE.CALL(fn, _cons(e, args), attr), es_1)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Static.callVectorize failed\\n")
                      fail()
                  end
                end
              end
               #=  vectorize call
               =#
          outExpExpLst
        end

         #= helper function to crefVectorize, creates each individual cref,
          e.g. {x{1},x{2}, ...} from x. =#
        function createCrefArray(inComponentRef1::DAE.ComponentRef, inInteger2::ModelicaInteger, inInteger3::ModelicaInteger, inType4::DAE.Type, inType5::DAE.Type, crefIdType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local indx::ModelicaInteger
                  local ds::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local et::DAE.Type
                  local elt_tp::DAE.Type
                  local t::DAE.Type
                  local expl::List{DAE.Exp}
                  local e_1::DAE.Exp
                   #=  index iterator dimension size
                   =#
                @matchcontinue (inComponentRef1, inInteger2, inInteger3, inType4, inType5, crefIdType) begin
                  (_, indx, ds, et, _, _)  => begin
                      if ! indx > ds
                        fail()
                      end
                    DAE.ARRAY(et, true, nil)
                  end

                  (cr, indx, ds, et, t, _)  => begin
                      indx_1 = indx + 1
                      cr_1 = ComponentReference.replaceWholeDimSubscript(cr, indx)
                      @match DAE.ARRAY(_, _, expl) = createCrefArray(cr, indx_1, ds, et, t, crefIdType)
                      elt_tp = Expression.unliftArray(et)
                      e_1 = crefVectorize(true, Expression.makeCrefExp(cr_1, elt_tp), t, NONE(), crefIdType)
                    DAE.ARRAY(et, true, _cons(e_1, expl))
                  end

                  (cr, indx, ds, et, t, _)  => begin
                      indx_1 = indx + 1
                      @match DAE.ARRAY(_, _, expl) = createCrefArray(cr, indx_1, ds, et, t, crefIdType)
                      e_1 = Expression.makeASUB(Expression.makeCrefExp(cr, et), list(DAE.ICONST(indx)))
                      (e_1, _) = ExpressionSimplify.simplify(e_1)
                      e_1 = crefVectorize(true, e_1, t, NONE(), crefIdType)
                    DAE.ARRAY(et, true, _cons(e_1, expl))
                  end

                  (cr, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("createCrefArray failed on:" + ComponentReference.printComponentRefStr(cr))
                    fail()
                  end
                end
              end
               #=  index
               =#
               #= /*
                  case (cr,indx,ds,et,t,crefIdType)
                    equation
                      (DAE.INDEX(e_1) :: ss) = ComponentReference.crefLastSubs(cr);
                      cr_1 = ComponentReference.crefStripLastSubs(cr);
                      cr_1 = ComponentReference.subscriptCref(cr_1,ss);
                      DAE.ARRAY(_,_,expl) = createCrefArray(cr_1, indx, ds, et, t,crefIdType);
                      expl = List.map1(expl,Expression.prependSubscriptExp,DAE.INDEX(e_1));
                    then
                      DAE.ARRAY(et,true,expl);
                  */ =#
               #=  for crefs with wholedim
               =#
               #=  no subscript
               =#
               #=  {} = ComponentReference.crefLastSubs(cr);
               =#
               #=  failure
               =#
          outExp
        end

         #= helper function to cref_vectorize, creates each
          individual cref, e.g. {x{1,1},x{2,1}, ...} from x. =#
        function createCrefArray2d(inCref::DAE.ComponentRef, inIndex::ModelicaInteger, inDim1::ModelicaInteger, inDim2::ModelicaInteger, inType5::DAE.Type, inType6::DAE.Type, crefIdType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local indx::ModelicaInteger
                  local ds::ModelicaInteger
                  local ds2::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local et::DAE.Type
                  local tp::DAE.Type
                  local elt_tp::DAE.Type
                  local t::DAE.Type
                  local ms::List{List{DAE.Exp}}
                  local expl::List{DAE.Exp}
                   #=  index iterator dimension size 1 dimension size 2
                   =#
                @matchcontinue (inCref, inIndex, inDim1, inDim2, inType5, inType6, crefIdType) begin
                  (_, indx, ds, _, et, _, _)  => begin
                      if ! indx > ds
                        fail()
                      end
                    DAE.MATRIX(et, 0, nil)
                  end

                  (cr, indx, ds, ds2, et, t, _)  => begin
                      indx_1 = indx + 1
                      @match DAE.MATRIX(matrix = ms) = createCrefArray2d(cr, indx_1, ds, ds2, et, t, crefIdType)
                      cr_1 = ComponentReference.subscriptCref(cr, list(DAE.INDEX(DAE.ICONST(indx))))
                      elt_tp = Expression.unliftArray(et)
                      @match DAE.ARRAY(_, true, expl) = crefVectorize(true, Expression.makeCrefExp(cr_1, elt_tp), t, NONE(), crefIdType)
                    DAE.MATRIX(et, ds, _cons(expl, ms))
                  end

                  (cr, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Static.createCrefArray2d failed on: " + ComponentReference.printComponentRefStr(cr))
                    fail()
                  end
                end
              end
               #=  increase the index dimension
               =#
               #=
               =#
          outExp
        end

         #= This function converts an absyn cref to a component reference =#
        function absynCrefToComponentReference(inComponentRef::Absyn.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local i::String
                  local b::Bool
                  local c::Absyn.ComponentRef
                  local cref::DAE.ComponentRef
                @match inComponentRef begin
                  Absyn.CREF_IDENT(name = i, subscripts =  nil())  => begin
                      cref = ComponentReference.makeCrefIdent(i, DAE.T_UNKNOWN_DEFAULT, nil)
                    cref
                  end

                  Absyn.CREF_QUAL(name = i, subscripts =  nil(), componentRef = c)  => begin
                      cref = absynCrefToComponentReference(c)
                      cref = ComponentReference.makeCrefQual(i, DAE.T_UNKNOWN_DEFAULT, nil, cref)
                    cref
                  end

                  Absyn.CREF_FULLYQUALIFIED(componentRef = c)  => begin
                      cref = absynCrefToComponentReference(c)
                    cref
                  end
                end
              end
          outComponentRef
        end

         #= This function elaborates on all subscripts in a component reference. =#
        function elabCrefSubs(inCache::FCore.Cache, inCrefEnv::FCore.Graph #= search for the cref in this environment =#, inSubsEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, inTopPrefix::Prefix.PrefixType #= the top prefix, i.e. the one send down by elabCref1, needed to prefix expressions in subscript types! =#, inCrefPrefix::Prefix.PrefixType #= the accumulated cref, required for lookup =#, inBoolean::Bool, inHasZeroSizeDim::Bool, info::SourceInfo) ::Tuple{FCore.Cache, DAE.ComponentRef, DAE.Const, Bool}
              local outHasZeroSizeDim::Bool
              local outConst::DAE.Const #= The constness of the subscripts. Note: This is not the same as
                the constness of a cref with subscripts! (just becase x[1,2] has a constant subscript list does
                not mean that the variable x[1,2] is constant) =#
              local outComponentRef::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outComponentRef, outConst, outHasZeroSizeDim) = begin
                  local t::DAE.Type
                  local sl::DAE.Dimensions
                  local constType::DAE.Const
                  local const1::DAE.Const
                  local const2::DAE.Const
                  local crefEnv::FCore.Graph
                  local crefSubs::FCore.Graph
                  local id::String
                  local ss::List{Absyn.Subscript}
                  local impl::Bool
                  local hasZeroSizeDim::Bool
                  local cr::DAE.ComponentRef
                  local absynCr::Absyn.ComponentRef
                  local ty::DAE.Type
                  local id_ty::DAE.Type
                  local ss_1::List{DAE.Subscript}
                  local restCref::Absyn.ComponentRef
                  local absynCref::Absyn.ComponentRef
                  local cache::FCore.Cache
                  local vt::SCode.Variability
                  local crefPrefix::Prefix.PrefixType
                  local topPrefix::Prefix.PrefixType
                   #=  IDENT
                   =#
                @matchcontinue (inCache, inCrefEnv, inSubsEnv, inComponentRef, inTopPrefix, inCrefPrefix, inBoolean, inHasZeroSizeDim, info) begin
                  (cache, crefEnv, crefSubs, Absyn.CREF_IDENT(name = id, subscripts = ss), topPrefix, crefPrefix, impl, hasZeroSizeDim, _)  => begin
                      (cache, cr) = PrefixUtil.prefixCref(cache, crefEnv, InnerOuterTypes.emptyInstHierarchy, crefPrefix, ComponentReference.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil))
                      @match (cache, _, _, _, _, InstTypes.SPLICEDEXPDATA(identType = id_ty), _, _, _) = Lookup.lookupVar(cache, crefEnv, cr)
                      id_ty = Types.simplifyType(id_ty)
                      hasZeroSizeDim = Types.isZeroLengthArray(id_ty)
                      sl = Types.getDimensions(id_ty)
                      (cache, ss_1, constType) = elabSubscriptsDims(cache, crefSubs, ss, sl, impl, topPrefix, inComponentRef, info)
                    (cache, ComponentReference.makeCrefIdent(id, id_ty, ss_1), constType, hasZeroSizeDim)
                  end

                  (cache, crefEnv, crefSubs, Absyn.CREF_QUAL(name = id, subscripts =  nil(), componentRef = restCref), topPrefix, crefPrefix, impl, hasZeroSizeDim, _)  => begin
                      (cache, cr) = PrefixUtil.prefixCref(cache, crefEnv, InnerOuterTypes.emptyInstHierarchy, crefPrefix, ComponentReference.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil))
                      (cache, _, t, _, _, _, _, _, _) = Lookup.lookupVar(cache, crefEnv, cr)
                      ty = Types.simplifyType(t)
                      sl = Types.getDimensions(ty)
                      crefPrefix = PrefixUtil.prefixAdd(id, sl, nil, crefPrefix, SCode.VAR(), ClassInf.UNKNOWN(Absyn.IDENT("")), info)
                      (cache, cr, constType, hasZeroSizeDim) = elabCrefSubs(cache, crefEnv, crefSubs, restCref, topPrefix, crefPrefix, impl, hasZeroSizeDim, info)
                    (cache, ComponentReference.makeCrefQual(id, ty, nil, cr), constType, hasZeroSizeDim)
                  end

                  (cache, crefEnv, crefSubs, Absyn.CREF_QUAL(name = id, subscripts =  nil(), componentRef = restCref), topPrefix, crefPrefix, impl, hasZeroSizeDim, _)  => begin
                      crefPrefix = PrefixUtil.prefixAdd(id, nil, nil, crefPrefix, SCode.VAR(), ClassInf.UNKNOWN(Absyn.IDENT("")), info)
                      (cache, cr, constType, hasZeroSizeDim) = elabCrefSubs(cache, crefEnv, crefSubs, restCref, topPrefix, crefPrefix, impl, hasZeroSizeDim, info)
                    (cache, ComponentReference.makeCrefQual(id, DAE.T_COMPLEX_DEFAULT, nil, cr), constType, hasZeroSizeDim)
                  end

                  (cache, crefEnv, crefSubs, Absyn.CREF_QUAL(name = id, subscripts = ss && _ <| _, componentRef = restCref), topPrefix, crefPrefix, impl, hasZeroSizeDim, _)  => begin
                      (cache, cr) = PrefixUtil.prefixCref(cache, crefEnv, InnerOuterTypes.emptyInstHierarchy, crefPrefix, ComponentReference.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil))
                      @match (cache, DAE.ATTR(variability = vt), t, _, _, InstTypes.SPLICEDEXPDATA(identType = id_ty), _, _, _) = Lookup.lookupVar(cache, crefEnv, cr)
                      ty = Types.simplifyType(t)
                      id_ty = Types.simplifyType(id_ty)
                      sl = Types.getDimensions(id_ty)
                      (cache, ss_1, const1) = elabSubscriptsDims(cache, crefSubs, ss, sl, impl, topPrefix, inComponentRef, info)
                      crefPrefix = PrefixUtil.prefixAdd(id, sl, ss_1, crefPrefix, vt, ClassInf.UNKNOWN(Absyn.IDENT("")), info)
                      (cache, cr, const2, hasZeroSizeDim) = elabCrefSubs(cache, crefEnv, crefSubs, restCref, topPrefix, crefPrefix, impl, hasZeroSizeDim, info)
                      constType = Types.constAnd(const1, const2)
                    (cache, ComponentReference.makeCrefQual(id, ty, ss_1, cr), constType, hasZeroSizeDim)
                  end

                  (cache, crefEnv, crefSubs, Absyn.CREF_FULLYQUALIFIED(componentRef = absynCr), topPrefix, crefPrefix, impl, hasZeroSizeDim, _)  => begin
                      crefEnv = FGraphUtil.topScope(crefEnv)
                      (cache, cr, const1, hasZeroSizeDim) = elabCrefSubs(cache, crefEnv, crefSubs, absynCr, topPrefix, crefPrefix, impl, hasZeroSizeDim, info)
                    (cache, cr, const1, hasZeroSizeDim)
                  end

                  (_, crefEnv, _, absynCref, topPrefix, crefPrefix, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Static.elabCrefSubs failed on: " + "[top:" + PrefixUtil.printPrefixStr(topPrefix) + "]." + PrefixUtil.printPrefixStr(crefPrefix) + "." + Dump.printComponentRefStr(absynCref) + " env: " + FGraphUtil.printGraphPathStr(crefEnv))
                    fail()
                  end
                end
              end
               #=  Debug.traceln(\"Try elabSucscriptsDims \" + id);
               =#
               #=  false = Types.isUnknownType(t);
               =#
               #=  print(\"elabCrefSubs type of: \" + id + \" is \" + Types.printTypeStr(t) + \"\\n\");
               =#
               #=  Debug.traceln(\"    elabSucscriptsDims \" + id + \" got var\");
               =#
               #=  _ = Types.simplifyType(t);
               =#
               #=  Constant evaluate subscripts on form x[1,p,q] where p,q are constants or parameters
               =#
               #=  QUAL,with no subscripts => looking for var in the top env!
               =#
               #= print(\"env:\");print(FGraphUtil.printGraphStr(env));print(\"\\n\");
               =#
               #=  variability doesn't matter
               =#
               #=  QUAL,with no subscripts second case => look for class
               =#
               #=  variability doesn't matter
               =#
               #=  QUAL,with constant subscripts
               =#
               #=  failure
               =#
               #=  FAILTRACE REMOVE
               =#
          (outCache, outComponentRef, outConst #= The constness of the subscripts. Note: This is not the same as
            the constness of a cref with subscripts! (just becase x[1,2] has a constant subscript list does
            not mean that the variable x[1,2] is constant) =#, outHasZeroSizeDim)
        end

         #= This function converts a list of Absyn.Subscript to a list of
          DAE.Subscript, and checks if all subscripts are constant.
          HJ: not checking for constant, returning if constant or not =#
        function elabSubscripts(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynSubscriptLst::List{<:Absyn.Subscript}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Subscript}, DAE.Const}
              local outConst::DAE.Const
              local outExpSubscriptLst::List{DAE.Subscript}
              local outCache::FCore.Cache

              (outCache, outExpSubscriptLst, outConst) = begin
                  local sub_1::DAE.Subscript
                  local const1::DAE.Const
                  local const2::DAE.Const
                  local constType::DAE.Const
                  local subs_1::List{DAE.Subscript}
                  local env::FCore.Graph
                  local sub::Absyn.Subscript
                  local subs::List{Absyn.Subscript}
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                   #=  empty list
                   =#
                @match (inCache, inEnv, inAbsynSubscriptLst, inBoolean, inPrefix, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil, DAE.C_CONST())
                  end

                  (cache, env, sub <| subs, impl, pre, _)  => begin
                      (cache, sub_1, const1, _) = elabSubscript(cache, env, sub, impl, pre, info)
                      (cache, subs_1, const2) = elabSubscripts(cache, env, subs, impl, pre, info)
                      constType = Types.constAnd(const1, const2)
                    (cache, _cons(sub_1, subs_1), constType)
                  end
                end
              end
               #=  elab a subscript then recurse
               =#
          (outCache, outExpSubscriptLst, outConst)
        end

         #= Elaborates a list of subscripts and checks that they are valid for the given dimensions. =#
        function elabSubscriptsDims(inCache::FCore.Cache, inEnv::FCore.Graph, inSubscripts::List{<:Absyn.Subscript}, inDimensions::List{<:DAE.Dimension}, inImpl::Bool, inPrefix::Prefix.PrefixType, inCref::Absyn.ComponentRef, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Subscript}, DAE.Const}
              local outConst::DAE.Const = DAE.C_CONST()
              local outSubs::List{DAE.Subscript} = nil
              local outCache::FCore.Cache = inCache

              local rest_dims::List{DAE.Dimension} = inDimensions
              local dim::DAE.Dimension
              local dsub::DAE.Subscript
              local constType::DAE.Const
              local prop::Option{DAE.Properties}
              local subl_str::String
              local diml_str::String
              local cref_str::String
              local nrdims::ModelicaInteger
              local nrsubs::ModelicaInteger

              for asub in inSubscripts
                if listEmpty(rest_dims)
                  cref_str = Dump.printComponentRefStr(inCref)
                  subl_str = intString(listLength(inSubscripts))
                  diml_str = intString(listLength(inDimensions))
                  Error.addSourceMessageAndFail(Error.WRONG_NUMBER_OF_SUBSCRIPTS, list(cref_str, subl_str, diml_str), inInfo)
                else
                  @match dim <| rest_dims = rest_dims
                end
                (outCache, dsub, constType, prop) = elabSubscript(outCache, inEnv, asub, inImpl, inPrefix, inInfo)
                outConst = Types.constAnd(constType, outConst)
                (outCache, dsub) = elabSubscriptsDims2(outCache, inEnv, dsub, dim, outConst, prop, inImpl, inCref, inInfo)
                outSubs = _cons(dsub, outSubs)
              end
               #=  Check that we don't have more subscripts than there are dimensions.
               =#
              nrsubs = listLength(outSubs)
               #=  If there are subs and the number of subs is less than dims
               =#
               #=  then fill in whole dims for the missing subs. i.e. We have a slice.
               =#
               #=  If there are no subs then it is a whole array so we do nothing.
               =#
              if nrsubs > 0
                nrdims = listLength(inDimensions)
                while nrsubs < nrdims
                  outSubs = _cons(DAE.WHOLEDIM(), outSubs)
                  nrsubs = nrsubs + 1
                end
              end
              outSubs = listReverse(outSubs)
          (outCache, outSubs, outConst)
        end

         #= Helper function to elabSubscriptsDims. =#
        function elabSubscriptsDims2(inCache::FCore.Cache, inEnv::FCore.Graph, inSubscript::DAE.Subscript, inDimension::DAE.Dimension, inConst::DAE.Const, inProperties::Option{<:DAE.Properties}, inImpl::Bool, inCref::Absyn.ComponentRef, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Subscript}
              local outSubscript::DAE.Subscript
              local outCache::FCore.Cache

              (outCache, outSubscript) = begin
                  local cache::FCore.Cache
                  local sub::DAE.Subscript
                  local int_dim::ModelicaInteger
                  local prop::DAE.Properties
                  local ty::DAE.Type
                  local e::DAE.Exp
                  local sub_str::String
                  local dim_str::String
                  local cref_str::String
                   #=  If in for iterator loop scope the subscript should never be evaluated to
                   =#
                   #=  a value (since the parameter/const value of iterator variables are not
                   =#
                   #=  available until expansion, which happens later on)
                   =#
                   #=  Note that for loops are expanded 'on the fly' and should therefore not be
                   =#
                   #=  treated in this way.
                   =#
                @matchcontinue (inDimension, inProperties) begin
                  (_, _)  => begin
                      @match true = FGraphUtil.inForOrParforIterLoopScope(inEnv)
                      @match true = Expression.dimensionKnown(inDimension)
                    (inCache, inSubscript)
                  end

                  (_, SOME(prop))  => begin
                      @match true = Types.isParameter(inConst)
                      ty = Types.getPropType(prop)
                      @match false = Types.getFixedVarAttributeParameterOrConstant(ty)
                    (inCache, inSubscript)
                  end

                  (_, _)  => begin
                      int_dim = Expression.dimensionSize(inDimension)
                      @match true = Types.isParameterOrConstant(inConst)
                      (cache, sub) = Ceval.cevalSubscript(inCache, inEnv, inSubscript, int_dim, inImpl, Absyn.MSG(inInfo), 0)
                    (cache, sub)
                  end

                  (DAE.DIM_EXP(exp = e), _)  => begin
                      @match true = Types.isParameterOrConstant(inConst)
                      @match (_, Values.INTEGER(integer = int_dim)) = Ceval.ceval(inCache, inEnv, e, true, Absyn.MSG(inInfo), 0)
                      (cache, sub) = Ceval.cevalSubscript(inCache, inEnv, inSubscript, int_dim, inImpl, Absyn.MSG(inInfo), 0)
                    (cache, sub)
                  end

                  (_, _)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      @match true = Types.isParameterOrConstant(inConst)
                    (inCache, inSubscript)
                  end

                  (_, _)  => begin
                      @match true = Expression.dimensionKnown(inDimension)
                      @match false = Types.isConstant(inConst) || Types.isParameter(inConst) && ! FGraphUtil.inForLoopScope(inEnv)
                    (inCache, inSubscript)
                  end

                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    (inCache, inSubscript)
                  end

                  (DAE.DIM_EXP(_), _)  => begin
                    (inCache, inSubscript)
                  end

                  _  => begin
                        sub_str = ExpressionDump.printSubscriptStr(inSubscript)
                        dim_str = ExpressionDump.dimensionString(inDimension)
                        cref_str = Dump.printComponentRefStr(inCref)
                        Error.addSourceMessage(Error.ILLEGAL_SUBSCRIPT, list(sub_str, dim_str, cref_str), inInfo)
                      fail()
                  end
                end
              end
               #=  Keep non-fixed parameters.
               =#
               #= /*/ Keep parameters as they are:
                   adrpo 2012-12-02 this does not work as we need to evaluate final parameters!
                                    and we have now way yet of knowing which ones those are
                  case (_, _, _, _, _, _, _, _, _)
                    equation
                      true = Types.isParameter(inConst);
                    then
                      (inCache, inSubscript);*/ =#
               #=  If the subscript contains a const then it should be evaluated to
               =#
               #=  the value.
               =#
               #=  If the previous case failed and we're just checking the model, try again
               =#
               #=  but skip the constant evaluation.
               =#
               #=  Keep variables and parameters inside of for-loops as they are.
               =#
               #=  For unknown dimensions, ':', keep as is.
               =#
          (outCache, outSubscript)
        end

         #= This function converts an Absyn.Subscript to an
          DAE.Subscript. =#
        function elabSubscript(inCache::FCore.Cache, inEnv::FCore.Graph, inSubscript::Absyn.Subscript, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Subscript, DAE.Const, Option{DAE.Properties}}
              local outProperties::Option{DAE.Properties}
              local outConst::DAE.Const
              local outSubscript::DAE.Subscript
              local outCache::FCore.Cache

              (outCache, outSubscript, outConst, outProperties) = begin
                  local impl::Bool
                  local sub_1::DAE.Exp
                  local ty::DAE.Type
                  local constType::DAE.Const
                  local sub_2::DAE.Subscript
                  local env::FCore.Graph
                  local sub::Absyn.Exp
                  local cache::FCore.Cache
                  local prop::DAE.Properties
                  local pre::Prefix.PrefixType
                   #=  no subscript
                   =#
                @matchcontinue (inCache, inEnv, inSubscript, inBoolean, inPrefix) begin
                  (cache, _, Absyn.NOSUB(__), _, _)  => begin
                    (cache, DAE.WHOLEDIM(), DAE.C_CONST(), NONE())
                  end

                  (cache, env, Absyn.SUBSCRIPT(subscript = sub), impl, pre)  => begin
                      @match (cache, sub_1, (@match DAE.PROP(constFlag = constType) = prop)) = elabExpInExpression(cache, env, sub, impl, true, pre, info)
                      @match (cache, sub_1, (@match DAE.PROP(type_ = ty) = prop)) = Ceval.cevalIfConstant(cache, env, sub_1, prop, impl, info)
                      sub_2 = elabSubscriptType(ty, sub, sub_1, info)
                    (cache, sub_2, constType, SOME(prop))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Static.elabSubscript failed on " + Dump.printSubscriptStr(inSubscript) + " in env: " + FGraphUtil.printGraphPathStr(inEnv))
                      fail()
                  end
                end
              end
               #=  some subscript, try to elaborate it
               =#
               #=  failtrace
               =#
          (outCache, outSubscript, outConst, outProperties)
        end

         #= This function is used to find the correct constructor for DAE.Subscript to
           use for an indexing expression.  If a scalar is given as index, DAE.INDEX()
           is used, and if an array is given, DAE.SLICE() is used. =#
        function elabSubscriptType(inType::DAE.Type, inAbsynExp::Absyn.Exp, inDaeExp::DAE.Exp, inInfo::SourceInfo) ::DAE.Subscript
              local outSubscript::DAE.Subscript

              outSubscript = begin
                  local sub::DAE.Exp
                  local e_str::String
                  local t_str::String
                  local p_str::String
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.INDEX(inDaeExp)
                  end

                  DAE.T_ENUMERATION(__)  => begin
                    DAE.INDEX(inDaeExp)
                  end

                  DAE.T_BOOL(__)  => begin
                    DAE.INDEX(inDaeExp)
                  end

                  DAE.T_ARRAY(ty = DAE.T_INTEGER(__))  => begin
                    DAE.SLICE(inDaeExp)
                  end

                  DAE.T_ARRAY(ty = DAE.T_ENUMERATION(__))  => begin
                    DAE.SLICE(inDaeExp)
                  end

                  DAE.T_ARRAY(ty = DAE.T_BOOL(__))  => begin
                    DAE.SLICE(inDaeExp)
                  end

                  DAE.T_METABOXED(__)  => begin
                    elabSubscriptType(inType.ty, inAbsynExp, inDaeExp, inInfo)
                  end

                  _  => begin
                        e_str = Dump.printExpStr(inAbsynExp)
                        t_str = Types.unparseType(inType)
                        Error.addSourceMessage(Error.WRONG_DIMENSION_TYPE, list(e_str, t_str), inInfo)
                      fail()
                  end
                end
              end
          outSubscript
        end

         #= If a component of an array type is subscripted, the type of the
          component reference is of lower dimensionality than the
          component.  This function shows the function between the component
          type and the component reference expression type.

          This function might actually not be needed.
         =#
        function subscriptCrefType(inExp::DAE.Exp, inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t_1::DAE.Type
                  local t::DAE.Type
                  local c::DAE.ComponentRef
                  local e::DAE.Exp
                @matchcontinue (inExp, inType) begin
                  (DAE.CREF(componentRef = c), t)  => begin
                      t_1 = subscriptCrefType2(c, t)
                    t_1
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

        function subscriptCrefType2(inComponentRef::DAE.ComponentRef, inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::DAE.Type
                  local t_1::DAE.Type
                  local subs::List{DAE.Subscript}
                  local c::DAE.ComponentRef
                @match (inComponentRef, inType) begin
                  (DAE.CREF_IDENT(subscriptLst =  nil()), t)  => begin
                    t
                  end

                  (DAE.CREF_IDENT(subscriptLst = subs), t)  => begin
                      t_1 = subscriptType(t, subs)
                    t_1
                  end

                  (DAE.CREF_QUAL(componentRef = c), t)  => begin
                      t_1 = subscriptCrefType2(c, t)
                    t_1
                  end
                end
              end
          outType
        end

         #= Given an array dimensionality and a list of subscripts, this
          function reduces the dimensionality.
          This does not handle slices or check that subscripts are not out
          of bounds. =#
        function subscriptType(inType::DAE.Type, inExpSubscriptLst::List{<:DAE.Subscript}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::DAE.Type
                  local t_1::DAE.Type
                  local subs::List{DAE.Subscript}
                  local dim::DAE.Dimension
                @matchcontinue (inType, inExpSubscriptLst) begin
                  (t,  nil())  => begin
                    t
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_INTEGER(__) <|  nil(), ty = t), DAE.INDEX(__) <| subs)  => begin
                      t_1 = subscriptType(t, subs)
                    t_1
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.SLICE(__) <| subs)  => begin
                      t_1 = subscriptType(t, subs)
                    DAE.T_ARRAY(t_1, list(dim))
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.WHOLEDIM(__) <| subs)  => begin
                      t_1 = subscriptType(t, subs)
                    DAE.T_ARRAY(t_1, list(dim))
                  end

                  (t, _)  => begin
                      Print.printBuf("- subscript_type failed (")
                      Print.printBuf(Types.printTypeStr(t))
                      Print.printBuf(" , [...])\\n")
                    fail()
                  end
                end
              end
          outType
        end

        function makeIfExp(inCache::FCore.Cache, inEnv::FCore.Graph, inCondition::DAE.Exp, inCondProp::DAE.Properties, inTrueBranch::DAE.Exp, inTrueProp::DAE.Properties, inFalseBranch::DAE.Exp, inFalseProp::DAE.Properties, inImplicit::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache = inCache

              local ty_match::Bool
              local cond::Bool
              local cond_ty::DAE.Type
              local true_ty::DAE.Type
              local false_ty::DAE.Type
              local true_ty2::DAE.Type
              local false_ty2::DAE.Type
              local exp_ty::DAE.Type
              local cond_c::DAE.Const
              local true_c::DAE.Const
              local false_c::DAE.Const
              local exp_c::DAE.Const
              local cond_str::String
              local cond_ty_str::String
              local e1_str::String
              local e2_str::String
              local ty1_str::String
              local ty2_str::String
              local pre_str::String
              local cond_exp::DAE.Exp
              local true_exp::DAE.Exp
              local false_exp::DAE.Exp

               #=  Check that the condition is a boolean expression.
               =#
              @match DAE.PROP(type_ = cond_ty, constFlag = cond_c) = inCondProp
              (cond_exp, _, ty_match) = Types.matchTypeNoFail(inCondition, cond_ty, DAE.T_BOOL_DEFAULT)
               #=  Print an error message and fail if the condition is not a boolean expression.
               =#
              if ! ty_match
                cond_str = ExpressionDump.printExpStr(inCondition)
                cond_ty_str = Types.unparseTypeNoAttr(cond_ty)
                Error.addSourceMessageAndFail(Error.IF_CONDITION_TYPE_ERROR, list(cond_str, cond_ty_str), inInfo)
              end
               #=  Check that both branches are type compatible.
               =#
              @match DAE.PROP(type_ = true_ty, constFlag = true_c) = inTrueProp
              @match DAE.PROP(type_ = false_ty, constFlag = false_c) = inFalseProp
              (true_exp, false_exp, exp_ty, ty_match) = Types.checkTypeCompat(inTrueBranch, true_ty, inFalseBranch, false_ty)
               #=  If the compatible type is an array with some unknown dimensions, and we're
               =#
               #=  not in a function, then we need to choose one of the branches.
               =#
              if Types.arrayHasUnknownDims(exp_ty) && ! FGraphUtil.inFunctionScope(inEnv)
                if Types.isParameterOrConstant(cond_c)
                  cond_c = DAE.C_CONST()
                else
                  ty_match = false
                end
              end
               #=  Check if the condition is reasonably constant, so we can evaluate it.
               =#
               #=  Otherwise it's a type error.
               =#
               #=  If the types are not matching, print an error and fail.
               =#
              if ! ty_match && ! Config.getGraphicsExpMode()
                e1_str = ExpressionDump.printExpStr(inTrueBranch)
                e2_str = ExpressionDump.printExpStr(inFalseBranch)
                ty1_str = Types.unparseTypeNoAttr(true_ty)
                ty2_str = Types.unparseTypeNoAttr(false_ty)
                pre_str = PrefixUtil.printPrefixStr3(inPrefix)
                Error.addSourceMessageAndFail(Error.TYPE_MISMATCH_IF_EXP, list(pre_str, e1_str, ty1_str, e2_str, ty2_str), inInfo)
              end
              if Types.isConstant(cond_c)
                try
                  @match (outCache, Values.BOOL(cond)) = Ceval.ceval(inCache, inEnv, cond_exp, inImplicit, Absyn.NO_MSG(), 0)
                  if cond
                    outExp = true_exp
                    outProperties = inTrueProp
                  else
                    outExp = false_exp
                    outProperties = inFalseProp
                  end
                  return (outCache, outExp, outProperties)
                catch
                end
              end
               #=  If the condition is constant, try to evaluate it and choose a branch.
               =#
               #=  Evaluation succeeded, return the chosen branch.
               =#
               #=  If the condition is not constant or ceval failed, create an if-expression.
               =#
              exp_c = Types.constAnd(Types.constAnd(cond_c, false_c), true_c)
              outExp = DAE.IFEXP(cond_exp, true_exp, false_exp)
              outProperties = DAE.PROP(exp_ty, exp_c)
          (outCache, outExp, outProperties)
        end

         #= This function relates a DAE.ComponentRef to its canonical form,
          which is when all subscripts are evaluated to constant values.
          If Such an evaluation is not possible, there is no canonical
          form and this function fails. =#
        function canonCref2(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inPrefixCref::DAE.ComponentRef, inBoolean::Bool) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outComponentRef::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outComponentRef) = begin
                  local ss_1::List{DAE.Subscript}
                  local ss::List{DAE.Subscript}
                  local env::FCore.Graph
                  local n::String
                  local impl::Bool
                  local cache::FCore.Cache
                  local prefixCr::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local sl::List{ModelicaInteger}
                  local t::DAE.Type
                  local ty2::DAE.Type
                @match (inCache, inEnv, inComponentRef, inPrefixCref, inBoolean) begin
                  (cache, env, DAE.CREF_IDENT(ident = n, identType = ty2, subscriptLst = ss), prefixCr, impl)  => begin
                      cr = ComponentReference.crefPrependIdent(prefixCr, n, nil, ty2)
                      (cache, _, t) = Lookup.lookupVar(cache, env, cr)
                      sl = Types.getDimensionSizes(t)
                      (cache, ss_1) = Ceval.cevalSubscripts(cache, env, ss, sl, impl, Absyn.NO_MSG(), 0)
                    (cache, ComponentReference.makeCrefIdent(n, ty2, ss_1))
                  end
                end
              end
               #= /* impl */ =#
          (outCache, outComponentRef)
        end

         #= Transform expression to canonical form
          by constant evaluating all subscripts. =#
        function canonCref(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inBoolean::Bool) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outComponentRef::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outComponentRef) = begin
                  local t::DAE.Type
                  local sl::List{ModelicaInteger}
                  local ss_1::List{DAE.Subscript}
                  local ss::List{DAE.Subscript}
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local n::String
                  local impl::Bool
                  local c_1::DAE.ComponentRef
                  local c::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local cache::FCore.Cache
                  local ty2::DAE.Type
                   #=  handle wild _
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, inBoolean) begin
                  (cache, _, DAE.WILD(__), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    (cache, DAE.WILD())
                  end

                  (cache, env, DAE.CREF_IDENT(ident = n, subscriptLst = ss), impl)  => begin
                      (cache, _, t, _, _, _, _, _, _) = Lookup.lookupVarIdent(cache, env, n)
                      sl = Types.getDimensionSizes(t)
                      (cache, ss_1) = Ceval.cevalSubscripts(cache, env, ss, sl, impl, Absyn.NO_MSG(), 0)
                      ty2 = Types.simplifyType(t)
                    (cache, ComponentReference.makeCrefIdent(n, ty2, ss_1))
                  end

                  (cache, env, DAE.CREF_QUAL(ident = n, subscriptLst = ss, componentRef = c), impl)  => begin
                      (cache, _, t, _, _, _, _, componentEnv, _) = Lookup.lookupVarIdent(cache, env, n)
                      ty2 = Types.simplifyType(t)
                      sl = Types.getDimensionSizes(t)
                      (cache, ss_1) = Ceval.cevalSubscripts(cache, env, ss, sl, impl, Absyn.NO_MSG(), 0)
                      (cache, c_1) = canonCref(cache, componentEnv, c, impl)
                    (cache, ComponentReference.makeCrefQual(n, ty2, ss_1, c_1))
                  end

                  (_, _, cr, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Static.canonCref failed, cr: ")
                      Debug.traceln(ComponentReference.printComponentRefStr(cr))
                    fail()
                  end
                end
              end
               #=  an unqualified component reference
               =#
               #= /* impl */ =#
               #=  a qualified component reference
               =#
               #= (cache,c_1) = canonCref2(cache, env, c, ComponentReference.makeCrefIdent(n,ty2,ss), impl);
               =#
               #=  failtrace
               =#
          (outCache, outComponentRef)
        end

         #= In a function we might have input arguments with unknown dimensions, and in
          that case we can't expand calls such as fill. A function call is therefore
          created with variable variability. This function checks that we're inside a
          function and returns DAE.C_VAR(), or fails if we're not inside a function.

          The exception is if checkModel is used, in which case we don't know what the
          variability would have been had all parameters received a binding. We can't
          set the variability to variable or parameter because then we might get
          bindings with higher variability than the component, and we can't set it to
          constant because that would cause the compiler to try and constant evaluate
          the call. So we set it to DAE.C_UNKNOWN() instead. =#
        function unevaluatedFunctionVariability(inEnv::FCore.Graph) ::DAE.Const
              local outConst::DAE.Const

              if FGraphUtil.inFunctionScope(inEnv)
                outConst = DAE.C_VAR()
              elseif Flags.getConfigBool(Flags.CHECK_MODEL) || Config.splitArrays()
                outConst = DAE.C_UNKNOWN()
              else
                fail()
              end
               #=  bug #2113, seems that there is nothing in the specs
               =#
               #=  that requires that fill arguments are of parameter/constant
               =#
               #=  variability, so allow it.
               =#
          outConst
        end

         #= Use with listFold to check if all slots have been filled =#
        function slotAnd(s::Slot, b::Bool) ::Bool
              local res::Bool

              @match SLOT(slotFilled = res) = s
              res = b && res
          res
        end

        function elabCodeExp(exp::Absyn.Exp, cache::FCore.Cache, env::FCore.Graph, ct::DAE.CodeType, info::SourceInfo) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local s1::String
                  local s2::String
                  local cr::Absyn.ComponentRef
                  local path::Absyn.Path
                  local es_1::List{DAE.Exp}
                  local es::List{Absyn.Exp}
                  local et::DAE.Type
                  local i::ModelicaInteger
                  local dexp::DAE.Exp
                  local prop::DAE.Properties
                  local ty::DAE.Type
                  local ct2::DAE.CodeType
                  local cn::Absyn.CodeNode
                   #=  first; try to elaborate the exp (maybe there is a binding in the environment that says v is a VariableName
                   =#
                @matchcontinue (exp, ct) begin
                  (_, _)  => begin
                      dexp = elabCodeExp_dispatch(exp, cache, env, ct, info)
                    dexp
                  end

                  (Absyn.CODE(code = Absyn.C_MODIFICATION(__)), DAE.C_EXPRESSION_OR_MODIFICATION(__))  => begin
                    DAE.CODE(exp.code, DAE.T_UNKNOWN_DEFAULT)
                  end

                  (Absyn.CODE(code = Absyn.C_EXPRESSION(__)), DAE.C_EXPRESSION(__))  => begin
                    DAE.CODE(exp.code, DAE.T_UNKNOWN_DEFAULT)
                  end

                  (_, DAE.C_EXPRESSION(__))  => begin
                    DAE.CODE(Absyn.C_EXPRESSION(exp), DAE.T_UNKNOWN_DEFAULT)
                  end

                  (_, DAE.C_EXPRESSION_OR_MODIFICATION(__))  => begin
                    DAE.CODE(Absyn.C_EXPRESSION(exp), DAE.T_UNKNOWN_DEFAULT)
                  end

                  (Absyn.CREF(componentRef = cr), DAE.C_TYPENAME(__))  => begin
                      path = AbsynUtil.crefToPath(cr)
                    DAE.CODE(Absyn.C_TYPENAME(path), DAE.T_UNKNOWN_DEFAULT)
                  end

                  (Absyn.ARRAY(es), DAE.C_VARIABLENAMES(__))  => begin
                      es_1 = ListUtil.map4(es, elabCodeExp, cache, env, DAE.C_VARIABLENAME(), info)
                      i = listLength(es)
                      et = DAE.T_ARRAY(DAE.T_UNKNOWN_DEFAULT, list(DAE.DIM_INTEGER(i)))
                    DAE.ARRAY(et, false, es_1)
                  end

                  (_, DAE.C_VARIABLENAMES(__))  => begin
                      et = DAE.T_ARRAY(DAE.T_UNKNOWN_DEFAULT, list(DAE.DIM_INTEGER(1)))
                      dexp = elabCodeExp(exp, cache, env, DAE.C_VARIABLENAME(), info)
                    DAE.ARRAY(et, false, list(dexp))
                  end

                  (Absyn.CREF(componentRef = cr), DAE.C_VARIABLENAME(__))  => begin
                    DAE.CODE(Absyn.C_VARIABLENAME(cr), DAE.T_UNKNOWN_DEFAULT)
                  end

                  (Absyn.CALL(Absyn.CREF_IDENT("der",  nil()), Absyn.FUNCTIONARGS(args = Absyn.CREF(__) <|  nil(), argNames =  nil())), DAE.C_VARIABLENAME(__))  => begin
                    DAE.CODE(Absyn.C_EXPRESSION(exp), DAE.T_UNKNOWN_DEFAULT)
                  end

                  _  => begin
                        @shouldFail @match DAE.C_VARIABLENAMES() = ct
                        s1 = Dump.printExpStr(exp)
                        s2 = Types.printCodeTypeStr(ct)
                        Error.addSourceMessage(Error.ELAB_CODE_EXP_FAILED, list(s1, s2), info)
                      fail()
                  end
                end
              end
               #=  adrpo: be very careful with this as it can take quite a long time, for example a call to:
               =#
               #=         getDerivedClassModifierValue(Modelica.Fluid.Vessels.BaseClasses.PartialLumpedVessel.Medium.MassFlowRate,unit);
               =#
               #=         will instantiate Modelica.Fluid.Vessels.BaseClasses.PartialLumpedVessel.Medium.MassFlowRate
               =#
               #=         if we're not careful
               =#
               #=  Expression
               =#
               #=  Type Name
               =#
               #=  Variable Names
               =#
               #=  Variable Name
               =#
               #=  failure
               =#
          outExp
        end

         #= @author: adrpo
         evaluate a code expression.
         be careful how much you lookup =#
        function elabCodeExp_dispatch(exp::Absyn.Exp, cache::FCore.Cache, env::FCore.Graph, ct::DAE.CodeType, info::Absyn.Info) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local s1::String
                  local s2::String
                  local cr::Absyn.ComponentRef
                  local path::Absyn.Path
                  local es_1::List{DAE.Exp}
                  local es::List{Absyn.Exp}
                  local et::DAE.Type
                  local i::ModelicaInteger
                  local dexp::DAE.Exp
                  local prop::DAE.Properties
                  local ty::DAE.Type
                  local ct2::DAE.CodeType
                  local id::Absyn.Ident
                   #=  for a component reference make sure the first ident is either \"OpenModelica\" or not a class
                   =#
                @matchcontinue exp begin
                  Absyn.CREF(componentRef = cr)  => begin
                      ErrorExt.setCheckpoint("elabCodeExp_dispatch1")
                      id = AbsynUtil.crefFirstIdent(cr)
                      _ = begin
                        @matchcontinue () begin
                          ()  => begin
                              @match true = id == "OpenModelica"
                              (_, dexp, prop) = elabExpInExpression(cache, env, exp, false, false, Prefix.NOPRE(), info)
                            ()
                          end

                          ()  => begin
                              @shouldFail (_, _, _) = Lookup.lookupClassIdent(cache, env, id)
                              (_, dexp, prop) = elabExpInExpression(cache, env, exp, false, false, Prefix.NOPRE(), info)
                            ()
                          end

                          _  => begin
                              fail()
                          end
                        end
                      end
                      @match DAE.T_CODE(ty = ct2) = Types.getPropType(prop)
                      @match true = valueEq(ct, ct2)
                      ErrorExt.delCheckpoint("elabCodeExp_dispatch1")
                    dexp
                  end

                  Absyn.CREF(__)  => begin
                      ErrorExt.rollBack("elabCodeExp_dispatch1")
                    fail()
                  end

                  _  => begin
                      @match false = AbsynUtil.isCref(exp)
                      ErrorExt.setCheckpoint("elabCodeExp_dispatch")
                      (_, dexp, prop) = elabExpInExpression(cache, env, exp, false, false, Prefix.NOPRE(), info)
                      @match DAE.T_CODE(ty = ct2) = Types.getPropType(prop)
                      @match true = valueEq(ct, ct2)
                      ErrorExt.delCheckpoint("elabCodeExp_dispatch")
                    dexp
                  end

                  _  => begin
                        @match false = AbsynUtil.isCref(exp)
                        ErrorExt.rollBack("elabCodeExp_dispatch")
                      fail()
                  end
                end
              end
               #=  if the first one is OpenModelica, search
               =#
               #=  not a class or OpenModelica, continue
               =#
               #=  a class which is not OpenModelica, fail
               =#
               #=  print(ExpressionDump.printExpStr(dexp) + \" \" + Types.unparseType(ty) + \"\\n\");
               =#
               #=  print(ExpressionDump.printExpStr(dexp) + \" \" + Types.unparseType(ty) + \"\\n\");
               =#
          outExp
        end

         #= Elaborates a list of array dimensions. =#
        function elabArrayDims(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, inDimensions::List{<:Absyn.Subscript}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensions::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensions) = elabArrayDims2(inCache, inEnv, inComponentRef, inDimensions, inImplicit, inDoVect, inPrefix, inInfo, nil)
          (outCache, outDimensions)
        end

         #= Helper function to elabArrayDims. Needed because of tail recursion. =#
        function elabArrayDims2(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, inDimensions::List{<:Absyn.Subscript}, inImplicit::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inElaboratedDims::DAE.Dimensions) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensions::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensions) = begin
                  local cache::FCore.Cache
                  local dim::Absyn.Subscript
                  local rest_dims::List{Absyn.Subscript}
                  local elab_dim::DAE.Dimension
                  local elab_dims::DAE.Dimensions
                @match inDimensions begin
                   nil()  => begin
                    (inCache, listReverse(inElaboratedDims))
                  end

                  dim <| rest_dims  => begin
                      (cache, elab_dim) = elabArrayDim(inCache, inEnv, inCref, dim, inImplicit, inDoVect, inPrefix, inInfo)
                      elab_dims = _cons(elab_dim, inElaboratedDims)
                      (cache, elab_dims) = elabArrayDims2(cache, inEnv, inCref, rest_dims, inImplicit, inDoVect, inPrefix, inInfo, elab_dims)
                    (cache, elab_dims)
                  end
                end
              end
          (outCache, outDimensions)
        end

         #= Elaborates a single array dimension. =#
        function elabArrayDim(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, inDimension::Absyn.Subscript, inImpl::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Dimension}
              local outDimension::DAE.Dimension
              local outCache::FCore.Cache

              (outCache, outDimension) = begin
                  local cr::Absyn.ComponentRef
                  local dim::DAE.Dimension
                  local cache::FCore.Cache
                  local cenv::FCore.Graph
                  local cls::SCode.Element
                  local type_path::Absyn.Path
                  local enum_type_name::Absyn.Path
                  local name::String
                  local enum_literals::List{String}
                  local enum_size::ModelicaInteger
                  local el::List{SCode.Element}
                  local sub::Absyn.Exp
                  local cr_exp::Absyn.Exp
                  local e::DAE.Exp
                  local dim_exp::DAE.Exp
                  local prop::DAE.Properties
                  local enum_lst::List{SCode.Enum}
                  local size_arg::Absyn.Exp
                  local t::DAE.Type
                   #=  The : operator results in an unknown dimension.
                   =#
                @matchcontinue (inCache, inEnv, inCref, inDimension, inImpl) begin
                  (_, _, _, Absyn.NOSUB(__), _)  => begin
                    (inCache, DAE.DIM_UNKNOWN())
                  end

                  (_, _, _, Absyn.SUBSCRIPT(subscript = Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "size"), functionArgs = Absyn.FUNCTIONARGS(args = cr_exp && Absyn.CREF(componentRef = cr) <| size_arg <|  nil()))), _)  => begin
                      @match true = AbsynUtil.crefEqual(inCref, cr)
                      (cache, e, _) = elabExpInExpression(inCache, inEnv, cr_exp, inImpl, inDoVect, inPrefix, inInfo)
                      (cache, dim_exp, _) = elabExpInExpression(cache, inEnv, size_arg, inImpl, inDoVect, inPrefix, inInfo)
                      dim = DAE.DIM_EXP(DAE.SIZE(e, SOME(dim_exp)))
                    (inCache, dim)
                  end

                  (_, _, _, Absyn.SUBSCRIPT(subscript = Absyn.CREF(componentRef = Absyn.CREF_IDENT(name = "Boolean"))), _)  => begin
                    (inCache, DAE.DIM_BOOLEAN())
                  end

                  (cache, _, _, Absyn.SUBSCRIPT(subscript = Absyn.CREF(cr)), _)  => begin
                      type_path = AbsynUtil.crefToPath(cr)
                      cache = Lookup.lookupClass(cache, inEnv, type_path)
                      (cache, t) = Lookup.lookupType(cache, inEnv, type_path, NONE())
                      dim = begin
                        @match t begin
                          DAE.T_ENUMERATION(index = NONE())  => begin
                            DAE.DIM_ENUM(t.path, t.names, listLength(t.names))
                          end

                          DAE.T_BOOL(__)  => begin
                            DAE.DIM_BOOLEAN()
                          end
                        end
                      end
                    (cache, dim)
                  end

                  (_, _, _, Absyn.SUBSCRIPT(subscript = sub), _)  => begin
                      (cache, e, prop) = elabExpInExpression(inCache, inEnv, sub, inImpl, inDoVect, inPrefix, inInfo)
                      @match (cache, SOME(dim)) = elabArrayDim2(cache, inEnv, inCref, e, prop, inImpl, inDoVect, inPrefix, inInfo)
                    (cache, dim)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Static.elabArrayDim failed on: " + AbsynUtil.printComponentRefStr(inCref) + Dump.printArraydimStr(list(inDimension)))
                      fail()
                  end
                end
              end
               #=  Size expression that refers to the array itself, such as
               =#
               #=  Real x(:, size(x, 1)).
               =#
               #= dim = DAE.DIM_UNKNOWN();
               =#
               #=  Array dimension from a Boolean or enumeration.
               =#
               #=  For all other cases we need to elaborate the subscript expression, so the
               =#
               #=  expression is elaborated and passed on to elabArrayDim2 to avoid doing
               =#
               #=  the elaboration several times.
               =#
          (outCache, outDimension)
        end

         #= Helper function to elabArrayDim. Continues the work from the last case in
          elabArrayDim to avoid unnecessary elaboration. =#
        function elabArrayDim2(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, inExp::DAE.Exp, inProperties::DAE.Properties, inImpl::Bool, inDoVect::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, Option{DAE.Dimension}}
              local outDimension::Option{DAE.Dimension}
              local outCache::FCore.Cache

              (outCache, outDimension) = begin
                  local cnst::DAE.Const
                  local cache::FCore.Cache
                  local e::DAE.Exp
                  local ty::DAE.Type
                  local e_str::String
                  local t_str::String
                  local a_str::String
                  local i::ModelicaInteger
                   #=  Constant dimension creates DIM_INTEGER.
                   =#
                @matchcontinue (inCache, inEnv, inCref, inExp, inProperties, inImpl) begin
                  (_, _, _, _, DAE.PROP(DAE.T_INTEGER(__), cnst), _)  => begin
                      @match true = Types.isParameterOrConstant(cnst)
                      @match (cache, Values.INTEGER(i)) = Ceval.ceval(inCache, inEnv, inExp, inImpl)
                    (cache, SOME(DAE.DIM_INTEGER(i)))
                  end

                  (_, _, _, _, DAE.PROP(DAE.T_INTEGER(__), DAE.C_PARAM(__)), _)  => begin
                      @match false = Config.splitArrays()
                    (inCache, SOME(DAE.DIM_EXP(inExp)))
                  end

                  (_, _, _, _, DAE.PROP(DAE.T_INTEGER(__), DAE.C_VAR(__)), false)  => begin
                      e_str = ExpressionDump.printExpStr(inExp)
                      Error.addSourceMessage(Error.DIMENSION_NOT_KNOWN, list(e_str), inInfo)
                    (inCache, NONE())
                  end

                  (_, _, _, _, DAE.PROP(DAE.T_INTEGER(__), _), true)  => begin
                      (cache, e, _) = Ceval.cevalIfConstant(inCache, inEnv, inExp, inProperties, inImpl, inInfo)
                    (cache, SOME(DAE.DIM_EXP(e)))
                  end

                  (_, _, _, _, _, _)  => begin
                      @match (cache, (@match DAE.SIZE(_, _) = e), _) = Ceval.cevalIfConstant(inCache, inEnv, inExp, inProperties, inImpl, inInfo)
                    (cache, SOME(DAE.DIM_EXP(e)))
                  end

                  (_, _, _, _, _, _)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                    (inCache, SOME(DAE.DIM_UNKNOWN()))
                  end

                  (_, _, _, _, DAE.PROP(DAE.T_INTEGER(__), cnst), _)  => begin
                      @match true = Types.isParameterOrConstant(cnst)
                      e_str = ExpressionDump.printExpStr(inExp)
                      a_str = Dump.printComponentRefStr(inCref) + "[" + e_str + "]"
                      Error.addSourceMessage(Error.STRUCTURAL_PARAMETER_OR_CONSTANT_WITH_NO_BINDING, list(e_str, a_str), inInfo)
                    (inCache, NONE())
                  end

                  (_, _, _, _, DAE.PROP(ty, _), _)  => begin
                      e_str = ExpressionDump.printExpStr(inExp)
                      t_str = Types.unparseType(ty)
                      Types.typeErrorSanityCheck(t_str, "Integer", inInfo)
                      Error.addSourceMessage(Error.ARRAY_DIMENSION_INTEGER, list(e_str, t_str), inInfo)
                    (inCache, NONE())
                  end
                end
              end
               #=  When arrays are non-expanded, non-constant parametric dimensions are allowed.
               =#
               #=  When not implicit instantiation, array dimension must be constant.
               =#
               #=  Non-constant dimension creates DIM_EXP.
               =#
               #=  an integer parameter with no binding
               =#
               #= (_, _) = elabArrayDim2(inCache, inEnv, inCref, inExp, inProperties, inImpl, inDoVect, inPrefix, inInfo);
               =#
          (outCache, outDimension)
        end

        function consStrippedCref(e::Absyn.Exp, es::List{<:Absyn.Exp}) ::List{Absyn.Exp}
              local oes::List{Absyn.Exp}

              oes = begin
                  local cr::Absyn.ComponentRef
                @match (e, es) begin
                  (Absyn.CREF(cr), _)  => begin
                      cr = AbsynUtil.crefStripLastSubs(cr)
                    _cons(Absyn.CREF(cr), es)
                  end

                  _  => begin
                      es
                  end
                end
              end
          oes
        end

         #= Replaces end-expressions in a cref with the appropriate size-expressions. =#
        function replaceEnd(inCref::Absyn.ComponentRef) ::Absyn.ComponentRef
              local outCref::Absyn.ComponentRef

              local cr_parts::List{Absyn.ComponentRef}
              local cr::Absyn.ComponentRef
              local cr_no_subs::Absyn.ComponentRef

               #= print(\"Before replace: \" + Dump.printComponentRefStr(inCref) + \"\\n\");
               =#
              @match outCref <| cr_parts = AbsynUtil.crefExplode(inCref)
              if ! AbsynUtil.crefIsIdent(outCref)
                outCref = inCref
                return outCref
              end
              if AbsynUtil.crefIsFullyQualified(inCref)
                outCref = AbsynUtil.crefMakeFullyQualified(outCref)
              end
              outCref = replaceEndInSubs(AbsynUtil.crefStripLastSubs(outCref), AbsynUtil.crefLastSubs(outCref))
              for cr in cr_parts
                cr_no_subs = AbsynUtil.crefStripLastSubs(cr)
                outCref = AbsynUtil.joinCrefs(outCref, cr_no_subs)
                outCref = replaceEndInSubs(outCref, AbsynUtil.crefLastSubs(cr))
              end
               #= print(\"After replace: \" + Dump.printComponentRefStr(outCref) + \"\\n\");
               =#
          outCref
        end

        function replaceEndInSubs(inCref::Absyn.ComponentRef, inSubscripts::List{<:Absyn.Subscript}) ::Absyn.ComponentRef
              local outCref::Absyn.ComponentRef = inCref

              local subs::List{Absyn.Subscript} = nil
              local new_sub::Absyn.Subscript
              local i::ModelicaInteger = 1

              if listEmpty(inSubscripts)
                return outCref
              end
              for sub in inSubscripts
                new_sub = replaceEndInSub(sub, i, inCref)
                subs = _cons(new_sub, subs)
                i = i + 1
              end
              outCref = AbsynUtil.crefSetLastSubs(outCref, listReverse(subs))
          outCref
        end

        function replaceEndInSub(inSubscript::Absyn.Subscript, inDimIndex::ModelicaInteger, inCref::Absyn.ComponentRef) ::Absyn.Subscript
              local outSubscript::Absyn.Subscript

              outSubscript = begin
                @match inSubscript begin
                  Absyn.SUBSCRIPT(__)  => begin
                    Absyn.SUBSCRIPT(replaceEndTraverser(inSubscript.subscript, (inCref, inDimIndex)))
                  end

                  _  => begin
                      inSubscript
                  end
                end
              end
          outSubscript
        end

        function replaceEndTraverser(inExp::Absyn.Exp, inTuple::Tuple{<:Absyn.ComponentRef, ModelicaInteger}) ::Absyn.Exp
              local outExp::Absyn.Exp

              outExp = begin
                  local cr::Absyn.ComponentRef
                  local i::ModelicaInteger
                @match inExp begin
                  Absyn.END(__)  => begin
                      (cr, i) = inTuple
                    Absyn.CALL(Absyn.CREF_IDENT("size", nil), Absyn.FUNCTIONARGS(list(Absyn.CREF(cr), Absyn.INTEGER(i)), nil))
                  end

                  Absyn.CREF(__)  => begin
                    Absyn.CREF(replaceEnd(inExp.componentRef))
                  end

                  _  => begin
                      AbsynUtil.traverseExpShallow(inExp, inTuple, replaceEndTraverser)
                  end
                end
              end
          outExp
        end

        function fixTupleMetaModelica(exps::List{<:DAE.Exp}, types::List{<:DAE.Type}, consts::List{<:DAE.TupleConst}) ::Tuple{DAE.Exp, DAE.Properties}
              local prop::DAE.Properties
              local exp::DAE.Exp

              local c::DAE.Const
              local tys2::List{DAE.Type}
              local exps2::List{DAE.Exp}

              if Config.acceptMetaModelicaGrammar()
                c = Types.tupleConstListToConst(consts)
                tys2 = list(Types.boxIfUnboxedType(ty) for ty in types)
                (exps2, tys2) = Types.matchTypeTuple(exps, types, tys2, false)
                exp = DAE.META_TUPLE(exps2)
                prop = DAE.PROP(DAE.T_METATUPLE(tys2), c)
              else
                exp = DAE.TUPLE(exps)
                prop = DAE.PROP_TUPLE(DAE.T_TUPLE(types, NONE()), DAE.TUPLE_CONST(consts))
              end
          (exp, prop)
        end

        function checkBuiltinCallArgs(inPosArgs::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inExpectedArgs::ModelicaInteger, inFnName::String, inInfo::Absyn.Info)
              local args_str::String
              local msg_str::String
              local pos_args::List{String}
              local named_args::List{String}

              if listLength(inPosArgs) != inExpectedArgs || ! listEmpty(inNamedArgs)
                Error.addSourceMessageAndFail(Error.WRONG_NO_OF_ARGS, list(inFnName), inInfo)
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  module InstUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

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
        import AbsynUtil
        import ClassInf
        import DAE
        import FCore
        import InnerOuter
        import InstTypes
        import Mod
        import Prefix
        import SCode
        import UnitAbsyn
        import Values
        import HashTable
        import HashTable5
        import AvlSetCR

        import DoubleEnded
        import ListUtil
        import BaseHashTable
        import Expression
        import Error
        import Util
        import ComponentReference
        import Patternm
        import DAEUtil
        import DAEDump
        import Types
        import Debug
        import PrefixUtil
        import ElementSource
        import ExpressionDump
        import Flags
        import FGraph
        import FNode
        import SCodeDump
        import SCodeUtil
        import Lookup
        import ValuesUtil
        import Static
        import Ceval
        import Dump
        import Config
        import Inst
        import InstFunction
        import System
        import ErrorExt
        import InstExtends
        import Graph
        import UnitAbsynBuilder
        import UnitChecker
        # import NFSCodeFlatten
        import HashSet
        import BaseHashSet
        import MetaModelica.Dangerous.listReverseInPlace

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

        InstDims = List

         #= This function creates a new, unique identifer.
          The same name is never returned twice. =#
        function newIdent() ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              local i::ModelicaInteger
              local is::String
              local s::String

              i = tick()
              is = intString(i)
              s = stringAppend("__TMP__", is)
              outComponentRef = ComponentReference.makeCrefIdent(s, DAE.T_UNKNOWN_DEFAULT, nil)
          outComponentRef
        end

         #= This function returns true if the Class is not a function. =#
        function isNotFunction(cls::SCode.Element) ::Bool
              local res::Bool

              res = SCodeUtil.isFunction(cls)
              res = boolNot(res)
          res
        end

        function scodeFlatten(inProgram::SCode.Program, inPath::Absyn.Path) ::SCode.Program
              local outProgram::SCode.Program

              outProgram = inProgram
          outProgram
        end

        function scodeFlattenProgram(inProgram::SCode.Program) ::SCode.Program
              local outProgram::SCode.Program

              outProgram = begin
                @matchcontinue inProgram begin
                  _  => begin
                      ErrorExt.setCheckpoint("scodeFlattenProgram")
                      outProgram = inProgram # NFSCodeFlatten.flattenCompleteProgram(inProgram)
                      ErrorExt.delCheckpoint("scodeFlattenProgram")
                    outProgram
                  end

                  _  => begin
                        ErrorExt.rollBack("scodeFlattenProgram")
                      inProgram
                  end
                end
              end
          outProgram
        end

         #=
        Author BZ
        This is a backpatch to fix the case of 'connection.isRoot' in initial if equations.
        After the class is instantiated a second sweep is done to check the initial if equations conditions.
        If all conditions are constant, we return only the 'correct' branch equations. =#
        function reEvaluateInitialIfEqns(cache::FCore.Cache, env::FCore.Graph, dae::DAE.DAElist, isTopCall::Bool) ::DAE.DAElist
              local odae::DAE.DAElist

              odae = begin
                  local elems::List{DAE.Element}
                @match (cache, env, dae, isTopCall) begin
                  (_, _, DAE.DAE(elementLst = elems), true)  => begin
                      elems = listReverse(ListUtil.fold2r(elems, reEvaluateInitialIfEqns2, cache, env, nil))
                    DAE.DAE(elems)
                  end

                  (_, _, _, false)  => begin
                    dae
                  end
                end
              end
          odae
        end

         #=  =#
        function reEvaluateInitialIfEqns2(acc::List{<:DAE.Element}, elem::DAE.Element, inCache::FCore.Cache, env::FCore.Graph) ::List{DAE.Element}
              local oelems::List{DAE.Element}

              oelems = begin
                  local conds::List{DAE.Exp}
                  local valList::List{Values.Value}
                  local tbs::List{List{DAE.Element}}
                  local fb::List{DAE.Element}
                  local selectedBranch::List{DAE.Element}
                  local source::DAE.ElementSource
                  local blist::List{Bool}
                  local cache::FCore.Cache
                @matchcontinue (acc, elem, inCache, env) begin
                  (_, DAE.INITIAL_IF_EQUATION(condition1 = conds, equations2 = tbs, equations3 = fb), cache, _)  => begin
                      (_, valList) = Ceval.cevalList(cache, env, conds, true, Absyn.NO_MSG(), 0)
                      blist = ListUtil.map(valList, ValuesUtil.valueBool)
                      selectedBranch = ListUtil.findBoolList(blist, tbs, fb)
                      selectedBranch = makeDAEElementInitial(selectedBranch)
                    listAppend(selectedBranch, acc)
                  end

                  _  => begin
                      _cons(elem, acc)
                  end
                end
              end
               #= print(\" (Initial if)To ceval: \" + stringDelimitList(List.map(conds,ExpressionDump.printExpStr),\", \") + \"\\n\");
               =#
               #= print(\" Ceval res: (\"+stringDelimitList(List.map(valList,ValuesUtil.printValStr),\",\")+\")\\n\");
               =#
          oelems
        end

         #=
        Author BZ
        Helper function for reEvaluateInitialIfEqns, makes the contenst of an initial if equation initial. =#
        function makeDAEElementInitial(inElems::List{<:DAE.Element}) ::List{DAE.Element}
              local outElems::List{DAE.Element}

              outElems = begin
                  local elem::DAE.Element
                  local cr::DAE.ComponentRef
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local s::DAE.ElementSource
                  local expl::List{DAE.Exp}
                  local tbs::List{List{DAE.Element}}
                  local fb::List{DAE.Element}
                  local al::DAE.Algorithm
                  local dims::DAE.Dimensions
                  local elems::List{DAE.Element}
                @match inElems begin
                   nil()  => begin
                    nil
                  end

                  DAE.DEFINE(cr, e1, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIALDEFINE(cr, e1, s), outElems)
                  end

                  DAE.ARRAY_EQUATION(dims, e1, e2, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIAL_ARRAY_EQUATION(dims, e1, e2, s), outElems)
                  end

                  DAE.EQUATION(e1, e2, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIALEQUATION(e1, e2, s), outElems)
                  end

                  DAE.IF_EQUATION(expl, tbs, fb, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIAL_IF_EQUATION(expl, tbs, fb, s), outElems)
                  end

                  DAE.ALGORITHM(al, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIALALGORITHM(al, s), outElems)
                  end

                  DAE.COMPLEX_EQUATION(e1, e2, s) <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(DAE.INITIAL_COMPLEX_EQUATION(e1, e2, s), outElems)
                  end

                  elem <| elems  => begin
                      outElems = makeDAEElementInitial(elems)
                    _cons(elem, outElems)
                  end
                end
              end
               #=  safe \"last case\" since we can not fail in cases above.
               =#
          outElems
        end

         #= Looks up a top level class with the given name. =#
        function lookupTopLevelClass(inName::String, inProgram::SCode.Program, inPrintError::Bool) ::SCode.Element
              local outClass::SCode.Element

              outClass = begin
                  local cls::SCode.Element
                @matchcontinue (inName, inProgram, inPrintError) begin
                  (_, _, _)  => begin
                      cls = ListUtil.getMemberOnTrue(inName, inProgram, SCodeUtil.isClassNamed)
                    cls
                  end

                  (_, _, true)  => begin
                      Error.addMessage(Error.LOAD_MODEL_ERROR, list(inName))
                    fail()
                  end
                end
              end
          outClass
        end

         #= Fixes the type of a class if it is uniontype or function reference.
          These are MetaModelica extensions. =#
        function fixInstClassType(ty::DAE.Type, isPartialFn::Bool) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local name::String
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                @matchcontinue (ty, isPartialFn) begin
                  (DAE.T_COMPLEX(complexClassType = ClassInf.SMNode.TYPE(path = path1)), _)  => begin
                      name = AbsynUtil.pathLastIdent(path1)
                      path2 = AbsynUtil.stripLast(path1)
                      @match "Code" = AbsynUtil.pathLastIdent(path2)
                      path2 = AbsynUtil.stripLast(path2)
                      @match "OpenModelica" = AbsynUtil.pathLastIdent(path2)
                    Util.assoc(name, list(("Expression", DAE.T_CODE(DAE.C_EXPRESSION())), ("ExpressionOrModification", DAE.T_CODE(DAE.C_EXPRESSION_OR_MODIFICATION())), ("TypeName", DAE.T_CODE(DAE.C_TYPENAME())), ("VariableName", DAE.T_CODE(DAE.C_VARIABLENAME())), ("VariableNames", DAE.T_CODE(DAE.C_VARIABLENAMES()))))
                  end

                  (_, false)  => begin
                    ty
                  end

                  (_, true)  => begin
                    Types.makeFunctionPolymorphicReference(ty)
                  end
                end
              end
          outType
        end

        function updateEnumerationEnvironment(inCache::FCore.Cache, inEnv::FCore.Graph, inType::DAE.Type, inClass::SCode.Element, inCi_State::ClassInf.SMNode) ::Tuple{FCore.Cache, FCore.Graph}
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local ty::DAE.Type
                  local c::SCode.Element
                  local names::List{String}
                  local vars::List{DAE.Var}
                  local p::Absyn.Path
                  local pname::Absyn.Path
                @matchcontinue (inCache, inEnv, inType, inClass, inCi_State) begin
                  (cache, env, DAE.T_ENUMERATION(names = names, literalVarLst = vars, path = p), _, ClassInf.ENUMERATION(pname))  => begin
                      (cache, env_1) = updateEnumerationEnvironment1(cache, env, AbsynUtil.pathString(pname), names, vars, p)
                    (cache, env_1)
                  end

                  (cache, env, _, _, _)  => begin
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= update enumeration value in environment =#
        function updateEnumerationEnvironment1(inCache::FCore.Cache, inEnv::FCore.Graph, inName::Absyn.Ident, inNames::List{<:String}, inVars::List{<:DAE.Var}, inPath::Absyn.Path) ::Tuple{FCore.Cache, FCore.Graph}
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local compenv::FCore.Graph
                  local name::String
                  local nn::String
                  local names::List{String}
                  local vars::List{DAE.Var}
                  local var::DAE.Var
                  local new_var::DAE.Var
                  local ty::DAE.Type
                  local instStatus::FCore.Status
                  local p::Absyn.Path
                  local attributes::DAE.Attributes
                  local binding::DAE.Binding
                  local cnstOpt::Option{DAE.Const}
                @match (inCache, inEnv, inName, inNames, inVars, inPath) begin
                  (cache, env, _, nn <| names, DAE.TYPES_VAR(ty = ty) <| vars, p)  => begin
                      @match (cache, DAE.TYPES_VAR(name, attributes, _, binding, cnstOpt), _, _, _, compenv) = Lookup.lookupIdentLocal(cache, env, nn)
                      new_var = DAE.TYPES_VAR(name, attributes, ty, binding, cnstOpt)
                      env_1 = FGraph.updateComp(env, new_var, FCore.VAR_DAE(), compenv)
                      (cache, env_2) = updateEnumerationEnvironment1(cache, env_1, name, names, vars, p)
                    (cache, env_2)
                  end

                  (cache, env, _,  nil(), _, _)  => begin
                    (cache, env)
                  end
                end
              end
               #=  get Var
               =#
               #=  print(\"updateEnumerationEnvironment1 -> component: \" + name + \" ty: \" + Types.printTypeStr(ty) + \"\\n\");
               =#
               #=  change type
               =#
               #=  update
               =#
               #=  next
               =#
          (outCache, outEnv)
        end

         #= updates the deduced units in each DAE.VAR =#
        function updateDeducedUnits(callScope::Bool, store::UnitAbsyn.InstStore, dae::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local ht::HashTable.HashTableType
                  local vec::Array{Option{UnitAbsyn.Unit}}
                  local elts::List{DAE.Element}
                   #= /* Only traverse on top scope */ =#
                @match (callScope, store, dae) begin
                  (true, UnitAbsyn.INSTSTORE(UnitAbsyn.STORE(vec, _), ht, _), DAE.DAE(elts))  => begin
                      elts = ListUtil.map2(elts, updateDeducedUnits2, vec, ht)
                    DAE.DAE(elts)
                  end

                  _  => begin
                      dae
                  end
                end
              end
          outDae
        end

         #= updates the deduced units in each DAE.VAR =#
        function updateDeducedUnits2(elt::DAE.Element, vec::Array{<:Option{<:UnitAbsyn.Unit}}, ht::HashTable.HashTableType) ::DAE.Element
              local oelt::DAE.Element

              oelt = begin
                  local indx::ModelicaInteger
                  local unitStr::String
                  local unit::UnitAbsyn.Unit
                  local varOpt::Option{DAE.VariableAttributes}
                  local cr::DAE.ComponentRef
                   #= /* Only traverse on top scope */ =#
                @matchcontinue (elt, vec, ht) begin
                  (DAE.VAR(componentRef = cr, variableAttributesOption = varOpt && SOME(DAE.VAR_ATTR_REAL(unit = NONE()))), _, _)  => begin
                      indx = BaseHashTable.get(cr, ht)
                      @match SOME(unit) = vec[indx]
                      unitStr = UnitAbsynBuilder.unit2str(unit)
                      varOpt = DAEUtil.setUnitAttr(varOpt, DAE.SCONST(unitStr))
                    DAEUtil.setVariableAttributes(elt, varOpt)
                  end

                  _  => begin
                      elt
                  end
                end
              end
          oelt
        end

         #= reports CONSISTENT or INCOMPLETE error message depending on content of store =#
        function reportUnitConsistency(topScope::Bool, store::UnitAbsyn.InstStore)
              _ = begin
                  local complete::Bool
                  local st::UnitAbsyn.Store
                @matchcontinue (topScope, store) begin
                  (_, _)  => begin
                      @match false = Flags.getConfigBool(Flags.UNIT_CHECKING)
                    ()
                  end

                  (true, UnitAbsyn.INSTSTORE(st, _, SOME(UnitAbsyn.CONSISTENT(__))))  => begin
                      (complete, _) = UnitChecker.isComplete(st)
                      Error.addMessage(if complete
                            Error.CONSISTENT_UNITS
                          else
                            Error.INCOMPLETE_UNITS
                          end, nil)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Author: BZ, 2009-09
         Extract the part before the conector ex: a.b.c.connector_d.e would return a.b.c =#
        function extractConnectorPrefix(connectorRef::DAE.ComponentRef) ::DAE.ComponentRef
              local prefixCon::DAE.ComponentRef

              prefixCon = begin
                  local child::DAE.ComponentRef
                  local name::String
                  local subs::List{DAE.Subscript}
                  local ty::DAE.Type
                   #=  If the bottom var is a connector, then it is not an outside connector. (spec 0.1.2)
                   =#
                @matchcontinue connectorRef begin
                  DAE.CREF_IDENT(_, _, _)  => begin
                    fail()
                  end

                  DAE.CREF_QUAL(name, ty && DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _)), subs, _)  => begin
                    ComponentReference.makeCrefIdent(name, ty, subs)
                  end

                  DAE.CREF_QUAL(name, ty, subs, child)  => begin
                      child = extractConnectorPrefix(child)
                    ComponentReference.makeCrefQual(name, ty, subs, child)
                  end
                end
              end
               #=  print(name + \" is not a outside connector \\n\");
               =#
          prefixCon
        end

         #=
        Author: BZ, 2009-09
        Helper function for updateTypesInUnconnectedConnectors2 =#
        function updateCrefTypesWithConnectorPrefix(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local name::String
                  local name2::String
                  local child::DAE.ComponentRef
                  local child2::DAE.ComponentRef
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                @matchcontinue (cr1, cr2) begin
                  (DAE.CREF_IDENT(name, ty, subs), DAE.CREF_QUAL(name2, _, _, child2))  => begin
                      @match true = stringEq(name, name2)
                    ComponentReference.makeCrefQual(name, ty, subs, child2)
                  end

                  (DAE.CREF_QUAL(name, ty, subs, child), DAE.CREF_QUAL(name2, _, _, child2))  => begin
                      @match true = stringEq(name, name2)
                      outCref = updateCrefTypesWithConnectorPrefix(child, child2)
                    ComponentReference.makeCrefQual(name, ty, subs, outCref)
                  end

                  _  => begin
                        print(" ***** FAILURE with " + ComponentReference.printComponentRefStr(cr1) + " _and_ " + ComponentReference.printComponentRefStr(cr2) + "\\n")
                      fail()
                  end
                end
              end
          outCref
        end

        function checkClassEqual(c1::SCode.Element, c2::SCode.Element) ::Bool
              local areEqual::Bool

              areEqual = begin
                  local r::SCode.Restriction
                  local normalAlgorithmLst1::List{SCode.AlgorithmSection}
                  local normalAlgorithmLst2::List{SCode.AlgorithmSection}
                  local initialAlgorithmLst1::List{SCode.AlgorithmSection}
                  local initialAlgorithmLst2::List{SCode.AlgorithmSection}
                  local cd1::SCode.ClassDef
                  local cd2::SCode.ClassDef
                   #=  when -g=MetaModelica, check class equality!
                   =#
                @matchcontinue (c1, c2) begin
                  (_, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @shouldFail equality(c1, c2)
                    false
                  end

                  (SCode.CLASS(restriction = SCode.R_TYPE(__)), _)  => begin
                      @shouldFail equality(c1, c2)
                    false
                  end

                  (SCode.CLASS(restriction = r), _)  => begin
                      @match false = SCodeUtil.isFunctionRestriction(r)
                    true
                  end

                  (SCode.CLASS(classDef = SCode.PARTS(normalAlgorithmLst = normalAlgorithmLst1, initialAlgorithmLst = initialAlgorithmLst1)), SCode.CLASS(classDef = SCode.PARTS(normalAlgorithmLst = normalAlgorithmLst2, initialAlgorithmLst = initialAlgorithmLst2)))  => begin
                      @match true = intEq(listLength(normalAlgorithmLst1), listLength(normalAlgorithmLst2))
                      @match true = intEq(listLength(initialAlgorithmLst1), listLength(initialAlgorithmLst2))
                    true
                  end

                  (SCode.CLASS(classDef = cd1 && SCode.DERIVED(__)), SCode.CLASS(classDef = cd2 && SCode.DERIVED(__)))  => begin
                      equality(cd1, cd2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  check the types for equality!
               =#
               #=  anything else but functions, do not check equality
               =#
               #=  check the class equality only for functions, made of parts
               =#
               #=  only check if algorithm list lengths are the same!
               =#
               #=  check the class equality only for functions, made of derived
               =#
               #=  only check class definitions are the same!
               =#
               #=  anything else, false!
               =#
          areEqual
        end

         #= Checks if two prefixes are equal, unless the class is a
         basic type, i.e. all reals, integers, enumerations with
         the same name, etc. are equal. =#
        function prefixEqualUnlessBasicType(pre1::Prefix.PrefixType, pre2::Prefix.PrefixType, cls::SCode.Element)
              _ = begin
                  local idn::String
                   #=  adrpo: TODO! FIXME!, I think here we should have pre1 = Prefix.CLASSPRE(variability1) == pre2 = Prefix.CLASSPRE(variability2)
                   =#
                   #=  don't care about prefix for:
                   =#
                   #=  - enumerations
                   =#
                   #=  - types as they cannot have components
                   =#
                   #=  - predefined types as they cannot have components
                   =#
                @matchcontinue (pre1, pre2, cls) begin
                  (_, _, SCode.CLASS(restriction = SCode.R_ENUMERATION(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_ENUMERATION(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_INTEGER(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_REAL(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_STRING(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_BOOLEAN(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(restriction = SCode.R_PREDEFINED_CLOCK(__)))  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(name = idn)) where (idn == "Real" || idn == "Integer" || idn == "String" || idn == "Boolean")  => begin
                    ()
                  end

                  (_, _, SCode.CLASS(name = "Clock"))  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    ()
                  end

                  _  => begin
                        equality(pre1, pre2)
                      ()
                  end
                end
              end
               #=  case (_, _, SCode.CLASS(restriction = SCode.R_TYPE())) then ();
               =#
               #=  BTH
               =#
               #=  don't care about prefix for:
               =#
               #=  - Real, String, Integer, Boolean
               =#
               #=  BTH
               =#
               #=  anything else, check for equality!
               =#
        end

         #=
        Author: BZ, this function identifies built in classes. =#
        function isBuiltInClass(className::String) ::Bool
              local b::Bool

              b = begin
                @match className begin
                  "Real"  => begin
                    true
                  end

                  "Integer"  => begin
                    true
                  end

                  "String"  => begin
                    true
                  end

                  "Boolean"  => begin
                    true
                  end

                  "Clock"  => begin
                    Config.synchronousFeaturesAllowed()
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
          b
        end

        function equalityConstraintOutputDimension(inElements::List{<:SCode.Element}) ::ModelicaInteger
              local outDimension::ModelicaInteger

              outDimension = begin
                  local tail::List{SCode.Element}
                  local dim::ModelicaInteger
                @match inElements begin
                   nil()  => begin
                    0
                  end

                  SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.OUTPUT(__), arrayDims = Absyn.SUBSCRIPT(Absyn.INTEGER(dim)) <|  nil())) <| _  => begin
                    dim
                  end

                  _ <| tail  => begin
                      dim = equalityConstraintOutputDimension(tail)
                    dim
                  end
                end
              end
          outDimension
        end

         #=   Tests if the given elements contain equalityConstraint function and returns
            corresponding DAE.EqualityConstraint. =#
        function equalityConstraint(inEnv::FCore.Graph, inCdefelts::List{<:SCode.Element}, info::SourceInfo) ::DAE.EqualityConstraint
              local outResult::DAE.EqualityConstraint = NONE()

              local els::List{SCode.Element}
              local path::Absyn.Path
              local dimension::ModelicaInteger
              local inlineType::DAE.InlineType

              try
                @match SOME(path) = FGraph.getScopePath(inEnv)
                path = AbsynUtil.joinPaths(path, Absyn.IDENT("equalityConstraint"))
                path = AbsynUtil.makeFullyQualified(path)
              catch
                return outResult
              end
              for el in inCdefelts
                try
                  @match SCode.CLASS(name = "equalityConstraint", restriction = SCode.R_FUNCTION(), classDef = SCode.PARTS(elementLst = els)) = el
                  dimension = equalityConstraintOutputDimension(els)
                  inlineType = classIsInlineFunc(el)
                  outResult = SOME((path, dimension, inlineType))
                  return outResult
                catch
                end
              end
          outResult
        end

         #= @author: adrpo
         do this unit checking ONLY if we have the flag! =#
        function handleUnitChecking(cache::FCore.Cache, env::FCore.Graph, inStore::UnitAbsyn.InstStore, pre::Prefix.PrefixType, compDAE::DAE.DAElist, daes::List{<:DAE.DAElist}, className::String #= for debugging =#) ::Tuple{FCore.Cache, FCore.Graph, UnitAbsyn.InstStore}
              local outStore::UnitAbsyn.InstStore
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outStore) = begin
                  local daetemp::DAE.DAElist
                  local ut::UnitAbsyn.UnitTerms
                  local store::UnitAbsyn.InstStore
                   #=  do nothing if we don't have to do unit checking
                   =#
                @match (cache, env, inStore, pre, compDAE, daes, className) begin
                  (_, _, store, _, _, _, _) where (! Flags.getConfigBool(Flags.UNIT_CHECKING))  => begin
                    (cache, env, store)
                  end

                  (_, _, store, _, _, _, _)  => begin
                      daetemp = DAEUtil.joinDaeLst(daes)
                      (store, ut) = UnitAbsynBuilder.instBuildUnitTerms(env, daetemp, compDAE, store)
                      UnitAbsynBuilder.registerUnitWeights(cache, env, compDAE)
                      store = UnitChecker.check(ut, store)
                    (cache, env, store)
                  end
                end
              end
               #=  Perform unit checking/dimensional analysis
               =#
               #= (daetemp,_) = ConnectUtil.equations(csets,pre,false,ConnectionGraph.EMPTY);  ToDO. calculation of connect eqns done twice. remove in future.
               =#
               #=  equations from components (dae1) not considered, they are checked in resp recursive call
               =#
               #=  but bindings on scalar variables must be considered, therefore passing dae1 separately
               =#
               #= daetemp = DAEUtil.joinDaeLst(daetemp::daes);
               =#
               #= print(\"built store for \"+className+\"\\n\");
               =#
               #= UnitAbsynBuilder.printInstStore(store);
               =#
               #= print(\"terms for \"+className+\"\\n\");
               =#
               #= UnitAbsynBuilder.printTerms(ut);
               =#
               #=  perform the check
               =#
               #= print(\"store for \"+className+\"\\n\");
               =#
               #= UnitAbsynBuilder.printInstStore(store);
               =#
               #= print(\"dae1=\"+DAEDump.dumpDebugDAE(DAE.DAE(dae1))+\"\\n\");
               =#
          (outCache, outEnv, outStore)
        end

         #= see Modelica Specfification 3.1, 7.1.3 Restrictions on the Kind of Base Class =#
        function checkExtendsRestrictionMatch(r1::SCode.Restriction, r2::SCode.Restriction)
              _ = begin
                @match (r1, r2) begin
                  (SCode.R_PACKAGE(__), SCode.R_PACKAGE(__))  => begin
                    ()
                  end

                  (SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)), SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)))  => begin
                    ()
                  end

                  (SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(_)), SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)))  => begin
                    ()
                  end

                  (SCode.R_FUNCTION(SCode.FR_OPERATOR_FUNCTION(__)), SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)))  => begin
                    ()
                  end

                  (SCode.R_FUNCTION(SCode.FR_OPERATOR_FUNCTION(__)), SCode.R_FUNCTION(SCode.FR_OPERATOR_FUNCTION(__)))  => begin
                    ()
                  end

                  (SCode.R_TYPE(__), SCode.R_TYPE(__))  => begin
                    ()
                  end

                  (SCode.R_RECORD(_), SCode.R_RECORD(_))  => begin
                    ()
                  end

                  (SCode.R_CONNECTOR(_), SCode.R_TYPE(__))  => begin
                    ()
                  end

                  (SCode.R_CONNECTOR(_), SCode.R_RECORD(_))  => begin
                    ()
                  end

                  (SCode.R_CONNECTOR(_), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end

                  (SCode.R_BLOCK(__), SCode.R_RECORD(false))  => begin
                    ()
                  end

                  (SCode.R_BLOCK(__), SCode.R_BLOCK(__))  => begin
                    ()
                  end

                  (SCode.R_MODEL(__), SCode.R_RECORD(false))  => begin
                    ()
                  end

                  (SCode.R_MODEL(__), SCode.R_BLOCK(__))  => begin
                    ()
                  end

                  (SCode.R_MODEL(__), SCode.R_MODEL(__))  => begin
                    ()
                  end

                  (SCode.R_MODEL(__), SCode.R_CLASS(__))  => begin
                    ()
                  end

                  (SCode.R_CLASS(__), SCode.R_MODEL(__))  => begin
                    ()
                  end

                  (SCode.R_CLASS(__), SCode.R_RECORD(_))  => begin
                    ()
                  end

                  (SCode.R_CLASS(__), SCode.R_BLOCK(__))  => begin
                    ()
                  end

                  (SCode.R_CLASS(__), SCode.R_CLASS(__))  => begin
                    ()
                  end

                  (SCode.R_OPERATOR(__), SCode.R_OPERATOR(__))  => begin
                    ()
                  end
                end
              end
               #=  package can be extendended by package
               =#
               #=  normal function -> normal function
               =#
               #=  external function -> normal function
               =#
               #=  operator function -> normal function
               =#
               #=  operator function -> operator function
               =#
               #=  type -> type
               =#
               #=  record -> record
               =#
               #=  connector -> type
               =#
               #=  connector -> record
               =#
               #=  connector -> connector
               =#
               #=  block -> record
               =#
               #=  block -> block
               =#
               #=  model -> record
               =#
               #=  model -> block
               =#
               #=  model -> model
               =#
               #=  class??? same restrictions as model?
               =#
               #=  model -> class
               =#
               #=  class -> model
               =#
               #=  class -> record
               =#
               #=  class -> block
               =#
               #=  class -> class
               =#
               #=  operator -> operator
               =#
        end

         #= @author: adrpo
          This function will check extends for Modelica 3.1 restrictions =#
        function checkExtendsForTypeRestiction(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inRestriction::SCode.Restriction, inSCodeElementLst::List{<:SCode.Element})
              _ = begin
                  local p::Absyn.Path
                  local r1::SCode.Restriction
                  local r2::SCode.Restriction
                  local r::SCode.Restriction
                  local id::String
                   #=  check the basics ....
                   =#
                   #=  type or connector can be extended by a type
                   =#
                @matchcontinue (inCache, inEnv, inIH, inRestriction, inSCodeElementLst) begin
                  (_, _, _, r, SCode.EXTENDS(baseClassPath = Absyn.IDENT(id)) <|  nil())  => begin
                      @match true = listMember(r, list(SCode.R_TYPE(), SCode.R_CONNECTOR(false), SCode.R_CONNECTOR(true)))
                      @match true = listMember(id, list("Real", "Integer", "Boolean", "String"))
                    ()
                  end

                  (_, _, _, r, SCode.EXTENDS(baseClassPath = Absyn.IDENT(id)) <|  nil())  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                      @match true = listMember(r, list(SCode.R_TYPE(), SCode.R_CONNECTOR(false), SCode.R_CONNECTOR(true)))
                      @match true = listMember(id, list("Real", "Integer", "Boolean", "String", "Clock"))
                    ()
                  end

                  (_, _, _, _, SCode.EXTENDS(baseClassPath = p) <|  nil())  => begin
                      @shouldFail (_, _, _) = Lookup.lookupClass(inCache, inEnv, p)
                    ()
                  end

                  (_, _, _, r1, SCode.EXTENDS(baseClassPath = p) <|  nil())  => begin
                      @match (_, SCode.CLASS(restriction = r2), _) = Lookup.lookupClass(inCache, inEnv, p)
                      checkExtendsRestrictionMatch(r1, r2)
                    ()
                  end

                  (_, _, _, r1, SCode.EXTENDS(baseClassPath = p) <|  nil())  => begin
                      @match (_, SCode.CLASS(restriction = r2), _) = Lookup.lookupClass(inCache, inEnv, p)
                      print("Error!: " + SCodeDump.restrString(r1) + " " + FGraph.printGraphPathStr(inEnv) + " cannot be extended by " + SCodeDump.restrString(r2) + " " + AbsynUtil.pathString(p) + " due to derived/base class restrictions.\\n")
                    fail()
                  end
                end
              end
               #= BTH same as above but extended with Clock type if Flags.SYNCHRONOUS_FEATURES == true
               =#
               #=  we haven't found the class, do nothing
               =#
               #=  we found te class, check the restriction
               =#
               #=  make some waves that this is not correct
               =#
        end

        function checkDerivedRestriction(parentRestriction::SCode.Restriction, childRestriction::SCode.Restriction, childName::SCode.Ident) ::Bool
              local b::Bool

              local b1::Bool
              local b2::Bool
              local b3::Bool
              local b4::Bool
              local strLst::List{String}
              local rstLst::List{SCode.Restriction}

               #=  BTH add Clock type to both lists if Flags.SYNCHRONOUS_FEATURES == true
               =#
              strLst = if Config.synchronousFeaturesAllowed()
                    list("Real", "Integer", "String", "Boolean", "Clock")
                  else
                    list("Real", "Integer", "String", "Boolean")
                  end
              b1 = listMember(childName, strLst)
              rstLst = if Config.synchronousFeaturesAllowed()
                    list(SCode.R_TYPE(), SCode.R_PREDEFINED_INTEGER(), SCode.R_PREDEFINED_REAL(), SCode.R_PREDEFINED_STRING(), SCode.R_PREDEFINED_BOOLEAN(), SCode.R_PREDEFINED_CLOCK())
                  else
                    list(SCode.R_TYPE(), SCode.R_PREDEFINED_INTEGER(), SCode.R_PREDEFINED_REAL(), SCode.R_PREDEFINED_STRING(), SCode.R_PREDEFINED_BOOLEAN())
                  end
              b2 = listMember(childRestriction, rstLst)
              b3 = valueEq(parentRestriction, SCode.R_TYPE())
               #= b2 := listMember(childRestriction, {SCode.R_TYPE(), SCode.R_ENUMERATION(), SCode.R_PREDEFINED_INTEGER(), SCode.R_PREDEFINED_REAL(), SCode.R_PREDEFINED_STRING(), SCode.R_PREDEFINED_BOOLEAN(), SCode.R_PREDEFINED_ENUMERATION()});
               =#
               #= b3 := boolOr(valueEq(parentRestriction, SCode.R_TYPE()), valueEq(parentRestriction, SCode.R_ENUMERATION()));
               =#
              b4 = valueEq(parentRestriction, SCode.R_CONNECTOR(false)) || valueEq(parentRestriction, SCode.R_CONNECTOR(true))
               #=  basically if child or parent is a type or basic type or parent is a connector and child is a type
               =#
              b = boolOr(b1, boolOr(b2, boolOr(b3, boolAnd(boolOr(b1, b2), b4))))
          b
        end

         #=
        Author: BZ, 2009-05
        This function is called from instClassDef, recursivly remove modifers on each component.
        What ever is left in modifier is printed as a warning. That means that we have modifiers on a component that does not exist. =#
        function matchModificationToComponents(inElems::List{<:SCode.Element}, inmod::DAE.Mod, callingScope::String)
              _ = begin
                  local elem::SCode.Element
                  local cn::String
                  local s1::String
                  local s2::String
                  local elems::List{SCode.Element}
                  local mod::DAE.Mod
                @match (inElems, inmod, callingScope) begin
                  (_, DAE.NOMOD(__), _)  => begin
                    ()
                  end

                  (_, DAE.MOD(subModLst =  nil()), _)  => begin
                    ()
                  end

                  ( nil(), _, _)  => begin
                      s1 = Mod.prettyPrintMod(inmod, 0)
                      s2 = s1 + " not found in <" + callingScope + ">"
                      Error.addMessage(Error.UNUSED_MODIFIER, list(s2))
                    fail()
                  end

                  (SCode.COMPONENT(name = cn) <| elems, mod, _)  => begin
                      mod = Mod.removeMod(mod, cn)
                      matchModificationToComponents(elems, mod, callingScope)
                    ()
                  end

                  (SCode.EXTENDS(__) <| elems, _, _)  => begin
                      matchModificationToComponents(elems, inmod, callingScope)
                    ()
                  end

                  (SCode.CLASS(name = cn, prefixes = SCode.PREFIXES(__)) <| elems, mod, _)  => begin
                      mod = Mod.removeMod(mod, cn)
                      matchModificationToComponents(elems, mod, callingScope)
                    ()
                  end

                  (SCode.IMPORT(__) <| elems, _, _)  => begin
                      matchModificationToComponents(elems, inmod, callingScope)
                    ()
                  end

                  (SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.NOT_REPLACEABLE(__))) <| elems, _, _)  => begin
                      matchModificationToComponents(elems, inmod, callingScope)
                    ()
                  end
                end
              end
               #=  Line below can be used for testing test-suite for dangling modifiers when getErrorString() is not called.
               =#
               #= print(\" *** ERROR Unused modifer...: \" + s2 + \"\\n\");
               =#
               #= TODO: only remove modifiers on replaceable classes, make special case for redeclaration of local classes
               =#
        end

         #= Returns true if the given element is in the list =#
        function elementNameMember(inElement::Tuple{<:SCode.Element, DAE.Mod}, els::List{<:SCode.Element}) ::Bool
              local isNamed::Bool

              isNamed = listMember(Util.tuple21(inElement), els)
          isNamed
        end

         #=
        Author: adrpo, see extractConstantPlusDeps for comments =#
        function extractConstantPlusDepsTpl(inComps::List{<:Tuple{<:SCode.Element, DAE.Mod}}, ocr::Option{<:DAE.ComponentRef}, allComps::List{<:SCode.Element}, className::String, ieql::List{<:SCode.Equation}, iieql::List{<:SCode.Equation}, ialgs::List{<:SCode.AlgorithmSection}, iialgs::List{<:SCode.AlgorithmSection}) ::Tuple{List{Tuple{SCode.Element, DAE.Mod}}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}}
              local oialgs::List{SCode.AlgorithmSection}
              local oalgs::List{SCode.AlgorithmSection}
              local oieql::List{SCode.Equation}
              local oeql::List{SCode.Equation}
              local oel::List{Tuple{SCode.Element, DAE.Mod}}

              (oel, oeql, oieql, oalgs, oialgs) = begin
                  local cr::DAE.ComponentRef
                  local all::List{SCode.Element}
                  local lst::List{SCode.Element}
                   #=  handle empty!
                   =#
                @matchcontinue (inComps, ocr, allComps, className, ieql, iieql, ialgs, iialgs) begin
                  ( nil(), _, _, _, _, _, _, _)  => begin
                    (nil, ieql, iieql, ialgs, iialgs)
                  end

                  (_, NONE(), _, _, _, _, _, _)  => begin
                    (inComps, ieql, iieql, ialgs, iialgs)
                  end

                  (_, SOME(_), _, _, _, _, _, _)  => begin
                      lst = ListUtil.map(inComps, Util.tuple21)
                      lst = extractConstantPlusDeps2(lst, ocr, allComps, className, nil)
                      @match false = listEmpty(lst)
                      lst = listReverse(lst)
                      oel = ListUtil.filter1OnTrue(inComps, elementNameMember, lst)
                    (oel, nil, nil, nil, nil)
                  end

                  (_, SOME(cr), _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- InstUtil.extractConstantPlusDeps failure to find " + ComponentReference.printComponentRefStr(cr) + ", returning \\n")
                      Debug.trace("- InstUtil.extractConstantPlusDeps elements to instantiate:" + intString(listLength(inComps)) + "\\n")
                    fail()
                  end
                end
              end
               #=  handle none
               =#
               #=  handle some
               =#
               #=  TODO: This used to return the input only if failtrace was set; should it always succeed?
               =#
          (oel, oeql, oieql, oalgs, oialgs)
        end

         #=
        Author: BZ, 2009-04
        This function filters the list of elements to instantiate depending on optional(DAE.ComponentRef), the
        optional argument is set in Lookup.lookupVarInPackages.
        If it is set, we are only looking for one variable in current scope hence we are not interested in
        instantiating more then nescessary.

        The actuall action of this function is to compare components to the DAE.ComponentRef name
        if it is found return that component and any dependant components(modifiers), this is done by calling the function recursivly.

        If the component specified in argument 2 is not found, we return all extend and import statements.
        TODO: search import and extends statements for specified variable.
              this includes to check class definitions to so that we do not need to instantiate local class definitions while looking for a constant. =#
        function extractConstantPlusDeps(inComps::List{<:SCode.Element}, ocr::Option{<:DAE.ComponentRef}, allComps::List{<:SCode.Element}, className::String) ::List{SCode.Element}
              local outComps::List{SCode.Element}

              outComps = begin
                  local cr::DAE.ComponentRef
                   #=  handle empty!
                   =#
                   #=  case({}, _, allComps, className) then {};
                   =#
                   #=  handle none
                   =#
                @matchcontinue (inComps, ocr, allComps, className) begin
                  (_, NONE(), _, _)  => begin
                    inComps
                  end

                  (_, SOME(_), _, _)  => begin
                      outComps = extractConstantPlusDeps2(inComps, ocr, allComps, className, nil)
                      @match false = listEmpty(outComps)
                      outComps = listReverse(outComps)
                    outComps
                  end

                  (_, SOME(cr), _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- InstUtil.extractConstantPlusDeps failure to find " + ComponentReference.printComponentRefStr(cr) + ", returning \\n")
                      Debug.trace("- InstUtil.extractConstantPlusDeps elements to instantiate:" + intString(listLength(inComps)) + "\\n")
                    fail()
                  end
                end
              end
               #=  handle StateSelect as we will NEVER find it!
               =#
               #=  case(inComps, SOME(DAE.CREF_QUAL(ident=\"StateSelect\")), allComps, className) then inComps;
               =#
               #=  handle some
               =#
               #=  TODO: This used to return the input only if failtrace was set; should it always succeed?
               =#
          outComps
        end

         #=
        Author: BZ, 2009-04
        Helper function for extractConstantPlusDeps =#
        function extractConstantPlusDeps2(inComps::List{<:SCode.Element}, ocr::Option{<:DAE.ComponentRef}, inAllComps::List{<:SCode.Element}, className::String, inExisting::List{<:String}) ::List{SCode.Element}
              local outComps::List{SCode.Element}

              outComps = begin
                  local compMod::SCode.Element
                  local recDeps::List{SCode.Element}
                  local selem::SCode.Element
                  local name::String
                  local name2::String
                  local scmod::SCode.Mod
                  local cr::DAE.ComponentRef
                  local crefs::List{Absyn.ComponentRef}
                  local p::Absyn.Path
                  local comps::List{SCode.Element}
                  local allComps::List{SCode.Element}
                  local existing::List{String}
                @matchcontinue (inComps, ocr, inAllComps, className, inExisting) begin
                  ( nil(), SOME(_), _, _, _)  => begin
                    nil
                  end

                  ( nil(), _, _, _, _)  => begin
                    fail()
                  end

                  (_, NONE(), _, _, _)  => begin
                    inComps
                  end

                  (selem && SCode.CLASS(name = name2) <| comps, SOME(DAE.CREF_IDENT(__)), allComps, _, existing)  => begin
                      allComps = _cons(selem, allComps)
                      existing = _cons(name2, existing)
                      outComps = extractConstantPlusDeps2(comps, ocr, allComps, className, existing)
                    _cons(selem, outComps)
                  end

                  (selem && SCode.COMPONENT(name = name2, modifications = scmod) <| comps, SOME(DAE.CREF_IDENT(ident = name)), allComps, _, existing)  => begin
                      @match true = stringEq(name, name2)
                      crefs = getCrefFromMod(scmod)
                      allComps = listAppend(comps, allComps)
                      existing = _cons(name2, existing)
                      recDeps = extractConstantPlusDeps3(crefs, allComps, className, existing)
                    _cons(selem, recDeps)
                  end

                  (selem && SCode.COMPONENT(name = name2) <| comps, SOME(DAE.CREF_IDENT(ident = name)), allComps, _, existing)  => begin
                      @match false = stringEq(name, name2)
                      allComps = _cons(selem, allComps)
                    extractConstantPlusDeps2(comps, ocr, allComps, className, existing)
                  end

                  (compMod && SCode.EXTENDS(__) <| comps, SOME(DAE.CREF_IDENT(__)), allComps, _, existing)  => begin
                      allComps = _cons(compMod, allComps)
                      recDeps = extractConstantPlusDeps2(comps, ocr, allComps, className, existing)
                    _cons(compMod, recDeps)
                  end

                  (compMod && SCode.IMPORT(__) <| comps, SOME(DAE.CREF_IDENT(__)), allComps, _, existing)  => begin
                      allComps = _cons(compMod, allComps)
                      recDeps = extractConstantPlusDeps2(comps, ocr, allComps, className, existing)
                    _cons(compMod, recDeps)
                  end

                  (compMod && SCode.DEFINEUNIT(__) <| comps, SOME(DAE.CREF_IDENT(__)), allComps, _, existing)  => begin
                      allComps = _cons(compMod, allComps)
                      recDeps = extractConstantPlusDeps2(comps, ocr, allComps, className, existing)
                    _cons(compMod, recDeps)
                  end

                  _  => begin
                        print(" failure in get_Constant_PlusDeps \\n")
                      fail()
                  end
                end
              end
               #= print(\" failure to find: \" + ComponentReference.printComponentRefStr(cr) + \" in scope: \" + className + \"\\n\");
               =#
               #= /*
                  case( (selem as SCode.CLASS(name=name2))::comps,SOME(DAE.CREF_IDENT(ident=name)),allComps,className,existing)
                    equation
                      true = stringEq(name,name2);
                      outComps = extractConstantPlusDeps2(comps,ocr,allComps,className,existing);
                    then
                      selem::outComps;
                      */ =#
               #= false = stringEq(name,name2);
               =#
               #= extractConstantPlusDeps2(comps,ocr,allComps,className,existing);
               =#
               #= debug_print(\"all\",  (inComps, ocr, allComps, className, existing));
               =#
          outComps
        end

         #=
        Author: BZ, 2009-04
        Helper function for extractConstantPlusDeps =#
        function extractConstantPlusDeps3(inAcrefs::List{<:Absyn.ComponentRef}, remainingComps::List{<:SCode.Element}, className::String, inExisting::List{<:String}) ::List{SCode.Element}
              local outComps::List{SCode.Element}

              outComps = begin
                  local s1::String
                  local s2::String
                  local acr::Absyn.ComponentRef
                  local localComps::List{SCode.Element}
                  local names::List{String}
                  local cref_::DAE.ComponentRef
                  local acrefs::List{Absyn.ComponentRef}
                  local existing::List{String}
                @matchcontinue (inAcrefs, remainingComps, className, inExisting) begin
                  ( nil(), _, _, _)  => begin
                    nil
                  end

                  (Absyn.CREF_FULLYQUALIFIED(acr) <| acrefs, _, _, existing)  => begin
                    extractConstantPlusDeps3(_cons(acr, acrefs), remainingComps, className, existing)
                  end

                  (Absyn.CREF_QUAL(s1, _, acr && Absyn.CREF_IDENT(_, _)) <| acrefs, _, _, existing) where (stringEq(className, s1))  => begin
                    extractConstantPlusDeps3(_cons(acr, acrefs), remainingComps, className, existing)
                  end

                  (Absyn.CREF_QUAL(_, _, _) <| acrefs, _, _, existing)  => begin
                      outComps = extractConstantPlusDeps3(acrefs, remainingComps, className, existing)
                    outComps
                  end

                  (Absyn.CREF_IDENT(s1, _) <| acrefs, _, _, existing) where (ListUtil.isMemberOnTrue(s1, existing, stringEq))  => begin
                    extractConstantPlusDeps3(acrefs, remainingComps, className, existing)
                  end

                  (Absyn.CREF_IDENT(s1, _) <| acrefs, _, _, existing)  => begin
                      cref_ = ComponentReference.makeCrefIdent(s1, DAE.T_UNKNOWN_DEFAULT, nil)
                      localComps = extractConstantPlusDeps2(remainingComps, SOME(cref_), nil, className, existing)
                      names = SCodeUtil.componentNamesFromElts(localComps)
                      existing = listAppend(names, existing)
                      outComps = extractConstantPlusDeps3(acrefs, remainingComps, className, existing)
                      outComps = listAppend(localComps, outComps)
                    outComps
                  end
                end
              end
               #=  in same scope look up.
               =#
               #=  false = stringEq(className,s1);
               =#
               #=  modifer dep already added
               =#
          outComps
        end

         #= @author adrpo
         Removes self reference from a path if it exists.
         Examples:
           removeSelfReference('Icons', 'Icons.BaseLibrary') => 'BaseLibrary'
           removeSelfReference('Icons', 'BlaBla.BaseLibrary') => 'BlaBla.BaseLibrary' =#
        function removeSelfReference(className::String, path::Absyn.Path) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = if stringEq(className, AbsynUtil.pathFirstIdent(path))
                    AbsynUtil.removePrefix(Absyn.IDENT(className), path)
                  else
                    path
                  end
          outPath
        end

         #= prints the tuple of elements and modifiers to stdout =#
        function printExtcomps(inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}})
              _ = begin
                  local s::String
                  local el::SCode.Element
                  local mod::DAE.Mod
                  local els::List{Tuple{SCode.Element, DAE.Mod}}
                @match inElements begin
                   nil()  => begin
                    ()
                  end

                  (el, mod) <| els  => begin
                      s = SCodeDump.unparseElementStr(el, SCodeDump.defaultOptions)
                      print(s)
                      print(", ")
                      print(Mod.printModStr(mod))
                      print("\\n")
                      printExtcomps(els)
                    ()
                  end
                end
              end
        end

         #= Returns only elements that are constants or have annotation(Evaluate = true)!
         author: PA & adrpo
         Used buy partialInstClassdef to instantiate constants in packages. =#
        function constantEls(elements::List{<:SCode.Element}) ::List{SCode.Element}
              local outElements::List{SCode.Element}

              local attr::SCode.Attributes

              outElements = list(el for el in elements if begin
                 @match el begin
                   SCode.COMPONENT(attributes = attr)  => begin
                     SCodeUtil.isConstant(SCodeUtil.attrVariability(attr))
                   end

                   _  => begin
                       false
                   end
                 end
               end)
          outElements
        end

         #= Returns only elements that are constants.
         author: @adrpo
         Used by partialInstClassdef to instantiate constants and parameters in packages. =#
        function constantAndParameterEls(elements::List{<:SCode.Element}) ::List{SCode.Element}
              local outElements::List{SCode.Element}

              local attr::SCode.Attributes

              outElements = list(el for el in elements if begin
                 @match el begin
                   SCode.COMPONENT(attributes = attr)  => begin
                     SCodeUtil.isParameterOrConst(SCodeUtil.attrVariability(attr))
                   end

                   _  => begin
                       false
                   end
                 end
               end)
          outElements
        end

         #= remove bindings for all elements if we do partial instantiation =#
        function removeBindings(elements::List{<:SCode.Element}) ::List{SCode.Element}
              local outElements::List{SCode.Element}

              outElements = begin
                  local el::SCode.Element
                  local els::List{SCode.Element}
                  local els1::List{SCode.Element}
                  local name::SCode.Ident #= the component name =#
                  local prefixes::SCode.Prefixes #= the common class or component prefixes =#
                  local attributes::SCode.Attributes #= the component attributes =#
                  local typeSpec::Absyn.TypeSpec #= the type specification =#
                  local modifications::SCode.Mod #= the modifications to be applied to the component =#
                  local comment::SCode.Comment #= this if for extraction of comments and annotations from Absyn =#
                  local condition::Option{Absyn.Exp} #= the conditional declaration of a component =#
                  local info::SourceInfo #= this is for line and column numbers, also file name. =#
                @match elements begin
                   nil()  => begin
                    nil
                  end

                  SCode.COMPONENT(name, prefixes, attributes, typeSpec, _, comment, condition, info) <| els  => begin
                      els1 = removeBindings(els)
                    _cons(SCode.COMPONENT(name, prefixes, attributes, typeSpec, SCode.NOMOD(), comment, condition, info), els1)
                  end

                  el <| els  => begin
                      els1 = removeBindings(els)
                    _cons(el, els1)
                  end
                end
              end
          outElements
        end

         #= remove bindings for all elements if we do partial instantiation =#
        function removeExtBindings(elements::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outElements::List{Tuple{SCode.Element, DAE.Mod}}

              outElements = begin
                  local el::Tuple{SCode.Element, DAE.Mod}
                  local els::List{Tuple{SCode.Element, DAE.Mod}}
                  local els1::List{Tuple{SCode.Element, DAE.Mod}}
                  local name::SCode.Ident #= the component name =#
                  local prefixes::SCode.Prefixes #= the common class or component prefixes =#
                  local attributes::SCode.Attributes #= the component attributes =#
                  local typeSpec::Absyn.TypeSpec #= the type specification =#
                  local modifications::SCode.Mod #= the modifications to be applied to the component =#
                  local comment::SCode.Comment #= this if for extraction of comments and annotations from Absyn =#
                  local condition::Option{Absyn.Exp} #= the conditional declaration of a component =#
                  local info::SourceInfo #= this is for line and column numbers, also file name. =#
                @match elements begin
                   nil()  => begin
                    nil
                  end

                  (SCode.COMPONENT(name, prefixes, attributes, typeSpec, _, comment, condition, info), _) <| els  => begin
                      els1 = removeExtBindings(els)
                    _cons((SCode.COMPONENT(name, prefixes, attributes, typeSpec, SCode.NOMOD(), comment, condition, info), DAE.NOMOD()), els1)
                  end

                  el <| els  => begin
                      els1 = removeExtBindings(els)
                    _cons(el, els1)
                  end
                end
              end
          outElements
        end

         #=
        Author: BZ, 2009-08
        Extract modifer for dependent variables(dep). =#
        function getModsForDep(inDepCref::Absyn.ComponentRef, inElems::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::DAE.Mod
              local omods::DAE.Mod

              omods = begin
                  local name1::String
                  local name2::String
                  local cmod::DAE.Mod
                  local tpl::Tuple{SCode.Element, DAE.Mod}
                  local dep::Absyn.ComponentRef
                  local elems::List{Tuple{SCode.Element, DAE.Mod}}
                @matchcontinue (inDepCref, inElems) begin
                  (_,  nil())  => begin
                    DAE.NOMOD()
                  end

                  (dep, (SCode.COMPONENT(__), DAE.NOMOD(__)) <| elems)  => begin
                    getModsForDep(dep, elems)
                  end

                  (dep, (SCode.COMPONENT(name = name1), cmod) <| _)  => begin
                      name2 = AbsynUtil.printComponentRefStr(dep)
                      @match true = stringEq(name2, name1)
                      cmod = DAE.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), list(DAE.NAMEMOD(name2, cmod)), NONE(), AbsynUtil.dummyInfo)
                    cmod
                  end

                  (dep, _ <| elems)  => begin
                      cmod = getModsForDep(dep, elems)
                    cmod
                  end
                end
              end
          omods
        end

         #= Return the Arraydim of an optional arradim.
          Empty list returned if no arraydim present. =#
        function getOptionArraydim(inAbsynArrayDimOption::Option{<:Absyn.ArrayDim}) ::Absyn.ArrayDim
              local outArrayDim::Absyn.ArrayDim

              outArrayDim = begin
                  local dim::List{Absyn.Subscript}
                @match inAbsynArrayDimOption begin
                  SOME(dim)  => begin
                    dim
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outArrayDim
        end

         #= This function takes an SCode.Element list and tranforms it into a
          (SCode.Element Mod) list by inserting DAE.NOMOD() for each element.
          Used to transform elements into a uniform list combined from inherited
          elements and ordinary elements. =#
        function addNomod(inElements::List{<:SCode.Element}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outElements::List{Tuple{SCode.Element, DAE.Mod}}

              outElements = list((x, DAE.NOMOD()) for x in inElements)
          outElements
        end

        Element = Tuple{SCode.Element, DAE.Mod}

         #= Sorts constants and parameters by dependencies, so that they are instantiated
          before they are used. =#
        function sortElementList(inElements::List{<:Element}, inEnv::FCore.Graph, isFunctionScope::Bool) ::List{Element}


              local outE::List{Element}
              local outEls::List{Element}
              local cycleElts::List{Element}
              local cycles::List{Tuple{Element, List{Element}}}
              local g::List{Tuple{Element, List{Element}}}

               #=  no sorting for meta-modelica!
               =#
              if ! Config.acceptMetaModelicaGrammar()
                g = Graph.buildGraph(inElements, getElementDependencies, (inElements, isFunctionScope))
                (outE, cycles) = Graph.topologicalSort(g, isElementEqual)
                outEls = listAppend(outE, ListUtil.map(cycles, Util.tuple21))
                checkCyclicalComponents(cycles, inEnv)
              end
               #=  sort the elements according to the dependencies
               =#
               #=  printGraph(inEnv, g, outE, cycles);
               =#
               #=  append the elements in the cycles as they might not actually be cycles, but they depend on elements not in the list (i.e. package constants, etc)!
               =#
          outEls
        end

        function printGraph(env::FGraph.Graph, g::List{<:Tuple{<:Element, List{<:Element}}}, order::List{<:Element}, cycles::List{<:Tuple{<:Element, List{<:Element}}})
              _ = begin
                @matchcontinue (env, g, order, cycles) begin
                  (_,  nil(), _, _)  => begin
                    ()
                  end

                  (_, _, _, _)  => begin
                      print("Graph for env: " + FGraph.printGraphPathStr(env) + "\\n" + Graph.printGraph(g, elementName) + "\\n")
                      print("Element order:\\n\\t" + stringDelimitList(ListUtil.map(order, elementName), "\\n\\t") + "\\n")
                      print("Cycles:\\n" + Graph.printGraph(cycles, elementName) + "\\n")
                    ()
                  end
                end
              end
               #=  nothing for empty graph
               =#
               #=  show me something!
               =#
        end

        function getDepsFromExps(inExps::List{<:Absyn.Exp}, inAllElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inDependencies::List{<:Tuple{<:SCode.Element, DAE.Mod}}, isFunction::Bool) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outDependencies::List{Tuple{SCode.Element, DAE.Mod}}

              outDependencies = begin
                  local rest::List{Absyn.Exp}
                  local e::Absyn.Exp
                  local deps::List{Tuple{SCode.Element, DAE.Mod}}
                   #=  handle the empty case
                   =#
                @match (inExps, inDependencies) begin
                  ( nil(), _)  => begin
                    inDependencies
                  end

                  (e <| rest, deps)  => begin
                      (_, (_, _, deps, _)) = AbsynUtil.traverseExpBidir(e, getElementDependenciesTraverserEnter, getElementDependenciesTraverserExit, (inAllElements, nil, deps, isFunction))
                      deps = getDepsFromExps(rest, inAllElements, deps, isFunction)
                    deps
                  end
                end
              end
               #=  handle the normal case
               =#
               #= (_, (_, _, (els, deps))) = AbsynUtil.traverseExpBidir(e, (getElementDependenciesTraverserEnter, getElementDependenciesTraverserExit, (inAllElements, deps)));
               =#
               #= deps = getDepsFromExps(rest, els, deps);
               =#
          outDependencies
        end

         #= @author: adrpo
         removes the name from deps (Real A[size(A,1)] dependency) =#
        function removeCurrentElementFromArrayDimDeps(name::String, inDependencies::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outDependencies::List{Tuple{SCode.Element, DAE.Mod}}

              outDependencies = list(dep for dep in inDependencies if ! stringEq(name, SCodeUtil.elementName(Util.tuple21(dep))))
          outDependencies
        end

        function getExpsFromConstrainClass(inRP::SCode.Replaceable) ::Tuple{List{Absyn.Exp}, List{Absyn.Exp}}
              local outSubsExps::List{Absyn.Exp} #= the expressions from subs =#
              local outBindingExp::List{Absyn.Exp} #= the bind exp if any =#

              (outBindingExp, outSubsExps) = begin
                  local l1::List{Absyn.Exp}
                  local l2::List{Absyn.Exp}
                  local m::SCode.Mod
                @match inRP begin
                  SCode.NOT_REPLACEABLE(__)  => begin
                    (nil, nil)
                  end

                  SCode.REPLACEABLE(NONE())  => begin
                    (nil, nil)
                  end

                  SCode.REPLACEABLE(SOME(SCode.CONSTRAINCLASS(modifier = m)))  => begin
                      (l1, l2) = getExpsFromMod(m)
                    (l1, l2)
                  end
                end
              end
               #=  no cc
               =#
               #=  yeha, we have a ccccc :)
               =#
          (outBindingExp #= the bind exp if any =#, outSubsExps #= the expressions from subs =#)
        end

        function getExpsFromSubMods(inSubMods::List{<:SCode.SubMod} #= the component sub modifiers =#) ::List{Absyn.Exp}
              local outSubsExps::List{Absyn.Exp} #= the expressions from subs =#

              outSubsExps = begin
                  local mod::SCode.Mod
                  local rest::List{SCode.SubMod}
                  local e::List{Absyn.Exp}
                  local exps::List{Absyn.Exp}
                  local sm::List{Absyn.Exp}
                   #=  handle empty
                   =#
                @match inSubMods begin
                   nil()  => begin
                    nil
                  end

                  SCode.NAMEMOD(mod = mod) <| rest  => begin
                      (e, sm) = getExpsFromMod(mod)
                      exps = getExpsFromSubMods(rest)
                      exps = listAppend(e, listAppend(sm, exps))
                    exps
                  end
                end
              end
               #=  handle namemod
               =#
          outSubsExps #= the expressions from subs =#
        end

        function getCrefFromMod(inMod::SCode.Mod #= the component modifier =#) ::List{Absyn.ComponentRef}
              local outCrefs::List{Absyn.ComponentRef}

              outCrefs = begin
                  local l1::List{Absyn.Exp}
                  local l2::List{Absyn.Exp}
                @matchcontinue inMod begin
                  _  => begin
                      (l1, l2) = getExpsFromMod(inMod)
                      outCrefs = ListUtil.flatten(ListUtil.map2(listAppend(l1, l2), AbsynUtil.getCrefFromExp, true, true))
                    outCrefs
                  end

                  _  => begin
                        print(getInstanceName() + ": could not retrieve crefs from SCode.Mod: " + SCodeDump.printModStr(inMod, SCodeDump.defaultOptions) + "\\n")
                      fail()
                  end
                end
              end
          outCrefs
        end

        function getExpsFromMod(inMod::SCode.Mod #= the component modifier =#) ::Tuple{List{Absyn.Exp}, List{Absyn.Exp}}
              local outSubsExps::List{Absyn.Exp} #= the expressions from subs =#
              local outBindingExp::List{Absyn.Exp} #= the bind exp if any =#

              (outBindingExp, outSubsExps) = begin
                  local se::List{Absyn.Exp}
                  local l1::List{Absyn.Exp}
                  local l2::List{Absyn.Exp}
                  local l3::List{Absyn.Exp}
                  local l4::List{Absyn.Exp}
                  local e::Absyn.Exp
                  local subs::List{SCode.SubMod}
                  local el::SCode.Element
                  local ado::Option{Absyn.ArrayDim}
                  local m::SCode.Mod
                  local ad::Absyn.ArrayDim
                  local rp::SCode.Replaceable
                   #=  no mods!
                   =#
                @match inMod begin
                  SCode.NOMOD(__)  => begin
                    (nil, nil)
                  end

                  SCode.MOD(subModLst =  nil(), binding = NONE())  => begin
                    (nil, nil)
                  end

                  SCode.MOD(subModLst = subs, binding = SOME(e))  => begin
                      se = getExpsFromSubMods(subs)
                    (list(e), se)
                  end

                  SCode.MOD(subModLst = subs, binding = NONE())  => begin
                      se = getExpsFromSubMods(subs)
                    (nil, se)
                  end

                  SCode.REDECL(element = SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = rp), classDef = SCode.DERIVED(Absyn.TPATH(_, ado), m, _)))  => begin
                      (l1, l2) = getExpsFromConstrainClass(rp)
                      (_, se) = AbsynUtil.getExpsFromArrayDimOpt(ado)
                      (l3, l4) = getExpsFromMod(m)
                      l1 = listAppend(se, listAppend(l1, l3))
                      l4 = listAppend(l2, l4)
                    (l1, l4)
                  end

                  SCode.REDECL(element = SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = rp), classDef = SCode.CLASS_EXTENDS(modifications = m)))  => begin
                      (l1, l2) = getExpsFromConstrainClass(rp)
                      (l3, l4) = getExpsFromMod(m)
                      l3 = listAppend(l1, l3)
                      l4 = listAppend(l2, l4)
                    (l3, l4)
                  end

                  SCode.REDECL(element = SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = rp)))  => begin
                      (l1, l2) = getExpsFromConstrainClass(rp)
                    (l1, l2)
                  end

                  SCode.REDECL(element = SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = rp), modifications = m, attributes = SCode.ATTR(arrayDims = ad)))  => begin
                      (l1, l2) = getExpsFromConstrainClass(rp)
                      (_, se) = AbsynUtil.getExpsFromArrayDim(ad)
                      (l3, l4) = getExpsFromMod(m)
                      l1 = listAppend(se, listAppend(l1, l3))
                      l4 = listAppend(l2, l4)
                    (l1, l4)
                  end
                end
              end
               #=  the special kind of crappy mods
               =#
               #=  mods with binding
               =#
               #=  mods without binding
               =#
               #=  redeclare short class, investigate cc mods and own mods/array dims
               =#
               #=  redeclare long class extends class, investigate cc and mods
               =#
               #=  redeclare long class, investigate cc
               =#
               #=  redeclare component, investigate cc mods and own mods/array dims
               =#
          (outBindingExp #= the bind exp if any =#, outSubsExps #= the expressions from subs =#)
        end

         #= author: PA
          Similar to getCrefFromMod, but investigates
          array dimensionalitites instead. =#
        function getCrefFromDim(inArrayDim::Absyn.ArrayDim) ::List{Absyn.ComponentRef}
              local outAbsynComponentRefLst::List{Absyn.ComponentRef}

              outAbsynComponentRefLst = begin
                  local l1::List{Absyn.ComponentRef}
                  local l2::List{Absyn.ComponentRef}
                  local res::List{Absyn.ComponentRef}
                  local exp::Absyn.Exp
                  local rest::List{Absyn.Subscript}
                @matchcontinue inArrayDim begin
                  Absyn.SUBSCRIPT(subscript = exp) <| rest  => begin
                      l1 = getCrefFromDim(rest)
                      l2 = AbsynUtil.getCrefFromExp(exp, true, true)
                      res = ListUtil.union(l1, l2)
                    res
                  end

                  Absyn.NOSUB(__) <| rest  => begin
                      res = getCrefFromDim(rest)
                    res
                  end

                   nil()  => begin
                    nil
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstUtil.getCrefFromDim failed\\n")
                      fail()
                  end
                end
              end
          outAbsynComponentRefLst
        end

         #= Returns the dependencies given an element. =#
        function getElementDependencies(inElement::Tuple{<:SCode.Element, DAE.Mod}, inAllElementsAndIsFunctionScope::Tuple{<:List{<:Tuple{<:SCode.Element, DAE.Mod}}, Bool}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outDependencies::List{Tuple{SCode.Element, DAE.Mod}}

              outDependencies = begin
                  local var::SCode.Variability
                  local cExpOpt::Option{Absyn.Exp}
                  local deps::List{Tuple{SCode.Element, DAE.Mod}}
                  local daeMod::DAE.Mod
                  local ad::Absyn.ArrayDim
                  local exps::List{Absyn.Exp}
                  local sexps::List{Absyn.Exp}
                  local bexps::List{Absyn.Exp}
                  local mod::SCode.Mod
                  local name::String
                  local hasUnknownDims::Bool
                  local isFunctionScope::Bool
                  local direction::Absyn.Direction
                  local inAllElements::List{Tuple{SCode.Element, DAE.Mod}}
                  local rp::SCode.Replaceable
                  local els::List{SCode.Element}
                  local externalDecl::Option{SCode.ExternalDecl}
                  local isFunction::Bool
                   #=  For constants and parameters we check the component conditional, array dimensions, modifiers and binding
                   =#
                @matchcontinue (inElement, inAllElementsAndIsFunctionScope) begin
                  ((SCode.COMPONENT(name = name, condition = cExpOpt, prefixes = SCode.PREFIXES(replaceablePrefix = rp), attributes = SCode.ATTR(arrayDims = ad, variability = var), modifications = mod), daeMod), (inAllElements, isFunction))  => begin
                      @match true = SCodeUtil.isParameterOrConst(var)
                      (_, exps) = AbsynUtil.getExpsFromArrayDim(ad)
                      (bexps, sexps) = getExpsFromMod(mod)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      (bexps, sexps) = getExpsFromConstrainClass(rp)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      (bexps, sexps) = getExpsFromMod(Mod.unelabMod(daeMod))
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      deps = getDepsFromExps(exps, inAllElements, nil, isFunction)
                      deps = removeCurrentElementFromArrayDimDeps(name, deps)
                      deps = getDepsFromExps(Util.optionList(cExpOpt), inAllElements, deps, isFunction)
                      deps = ListUtil.union(deps, nil)
                    deps
                  end

                  ((SCode.COMPONENT(attributes = SCode.ATTR(direction = direction)), _), (_, true))  => begin
                      @match true = AbsynUtil.isInputOrOutput(direction)
                    nil
                  end

                  ((SCode.COMPONENT(name = name, condition = cExpOpt, prefixes = SCode.PREFIXES(replaceablePrefix = rp), attributes = SCode.ATTR(arrayDims = ad), modifications = mod), daeMod), (inAllElements, isFunction))  => begin
                      (_, exps) = AbsynUtil.getExpsFromArrayDim(ad)
                      (bexps, sexps) = getExpsFromMod(mod)
                      exps = listAppend(sexps, exps)
                      exps = listAppend(bexps, exps)
                      (bexps, sexps) = getExpsFromConstrainClass(rp)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      (bexps, sexps) = getExpsFromMod(Mod.unelabMod(daeMod))
                      exps = listAppend(sexps, exps)
                      exps = listAppend(bexps, exps)
                      deps = getDepsFromExps(exps, inAllElements, nil, isFunction)
                      deps = removeCurrentElementFromArrayDimDeps(name, deps)
                      deps = getDepsFromExps(Util.optionList(cExpOpt), inAllElements, deps, isFunction)
                      deps = ListUtil.union(deps, nil)
                    deps
                  end

                  ((SCode.CLASS(name = name, prefixes = SCode.PREFIXES(replaceablePrefix = rp), classDef = SCode.DERIVED(modifications = mod, attributes = SCode.ATTR(arrayDims = ad))), daeMod), (inAllElements, isFunction))  => begin
                      (_, exps) = AbsynUtil.getExpsFromArrayDim(ad)
                      (_, sexps) = getExpsFromMod(mod)
                      exps = listAppend(sexps, exps)
                      (bexps, sexps) = getExpsFromConstrainClass(rp)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      (_, sexps) = getExpsFromMod(Mod.unelabMod(daeMod))
                      exps = listAppend(sexps, exps)
                      deps = getDepsFromExps(exps, inAllElements, nil, isFunction)
                      deps = removeCurrentElementFromArrayDimDeps(name, deps)
                      deps = ListUtil.union(deps, nil)
                    deps
                  end

                  ((SCode.CLASS(name = name, prefixes = SCode.PREFIXES(__), classDef = SCode.PARTS(externalDecl = externalDecl)), _), (inAllElements, isFunction))  => begin
                      exps = getExpsFromExternalDecl(externalDecl)
                      deps = getDepsFromExps(exps, inAllElements, nil, isFunction)
                      deps = removeCurrentElementFromArrayDimDeps(name, deps)
                      deps = ListUtil.union(deps, nil)
                    deps
                  end

                  _  => begin
                      nil
                  end
                end
              end
               #=  remove the current element from the deps as it is usally Real A[size(A,1)]; or self reference FlowModel fm(... blah = fcall(fm.x));
               =#
               #=  print(name + \" deps \" + stringDelimitList(list(SCodeUtil.elementName(Util.tuple21(e)) for e in deps),\",\") + \"\\n\");
               =#
               #=  For input and output variables in function scope return no dependencies so they stay in order!
               =#
               #=  For other variables we check the condition, since they might be conditional on a constant or parameter.
               =#
               #=  DO *NOT* ignore the bindings in function scope. We do not want to keep the order!
               =#
               #=  exps = if_(hasUnknownDims, listAppend(bexps, exps), exps);
               =#
               #=  DO *NOT* ignore the bindings in function scope so we keep the order!
               =#
               #=  exps = if_(hasUnknownDims, listAppend(bexps, exps), exps);
               =#
               #=  remove the current element from the deps as it is usally Real A[size(A,1)];
               =#
               #=  print(name + \" deps \" + stringDelimitList(list(SCodeUtil.elementName(Util.tuple21(e)) for e in deps),\",\") + \"\\n\");
               =#
               #=  We might actually get packages here, check the modifiers and the array dimensions
               =#
               #=  We might have functions here and their input/output elements can have bindings from the list
               =#
               #=  see reference_X in PartialMedium
               =#
               #=  see ExternalMedia.Media.ExternalTwoPhaseMedium.FluidConstants
               =#
               #=      which depends on function calls which depend on package constants inside external decl
               =#
               #= /*
                      exps = getExpsFromDefaults(els, exps);
                      (bexps, sexps) = getExpsFromConstrainClass(rp);
                      exps = listAppend(bexps, listAppend(sexps, exps));
                      (bexps, sexps) = getExpsFromMod(Mod.unelabMod(daeMod));
                      exps = listAppend(bexps, listAppend(sexps, exps));
                      */ =#
          outDependencies
        end

         #= get dependencies from external declarations =#
        function getExpsFromExternalDecl(inExternalDecl::Option{<:SCode.ExternalDecl}) ::List{Absyn.Exp}
              local outExps::List{Absyn.Exp}

              outExps = begin
                  local exps::List{Absyn.Exp}
                @match inExternalDecl begin
                  NONE()  => begin
                    nil
                  end

                  SOME(SCode.EXTERNALDECL(args = exps))  => begin
                    exps
                  end
                end
              end
          outExps
        end

        function getExpsFromDefaults(inEls::SCode.Program, inAcc::List{<:Absyn.Exp}) ::List{Absyn.Exp}
              local outExps::List{Absyn.Exp}

              outExps = begin
                  local rest::SCode.Program
                  local exps::List{Absyn.Exp}
                  local sexps::List{Absyn.Exp}
                  local bexps::List{Absyn.Exp}
                  local acc::List{Absyn.Exp}
                  local m::SCode.Mod
                  local rp::SCode.Replaceable
                @matchcontinue (inEls, inAcc) begin
                  ( nil(), _)  => begin
                    inAcc
                  end

                  (SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = rp), modifications = m) <| rest, _)  => begin
                      exps = inAcc
                      (bexps, sexps) = getExpsFromConstrainClass(rp)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      (bexps, sexps) = getExpsFromMod(m)
                      exps = listAppend(bexps, listAppend(sexps, exps))
                      exps = getExpsFromDefaults(rest, exps)
                    exps
                  end

                  (_ <| rest, _)  => begin
                      exps = getExpsFromDefaults(rest, inAcc)
                    exps
                  end
                end
              end
          outExps
        end

        ElementList = List{Element}

         #= Traverse function used by getElementDependencies to collect all dependencies
          for an element. The first ElementList in the input argument is a list of all
          elements, and the second is a list of accumulated dependencies. =#
        function getElementDependenciesTraverserEnter(inExp::Absyn.Exp, inTuple::Tuple{<:ElementList, List{<:ElementList}, ElementList, Bool}) ::Tuple{Absyn.Exp, Tuple{ElementList, List{ElementList}, ElementList, Bool}}
              local outTuple::Tuple{ElementList, List{ElementList}, ElementList, Bool}
              local outExp::Absyn.Exp

              (outExp, outTuple) = begin
                  local exp::Absyn.Exp
                  local id::String
                  local all_el::ElementList
                  local accum_el::ElementList
                  local stack::List{ElementList}
                  local e::Tuple{SCode.Element, DAE.Mod}
                  local cref::Absyn.ComponentRef
                  local b::Bool
                @matchcontinue (inExp, inTuple) begin
                  (exp && Absyn.CREF(componentRef = cref), (all_el, stack, accum_el, b))  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      e = ListUtil.find1(all_el, isElementNamed, id)
                    (exp, (all_el, stack, _cons(e, accum_el), b))
                  end

                  (exp && Absyn.CALL(function_ = cref), (all_el, stack, accum_el, b))  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      e = ListUtil.find1(all_el, isElementNamed, id)
                    (exp, (all_el, stack, _cons(e, accum_el), b))
                  end

                  (exp && Absyn.IFEXP(__), (all_el, stack, accum_el, false))  => begin
                    (exp, (all_el, _cons(accum_el, stack), nil, false))
                  end

                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
               #=  The condition expression is always used
               =#
          (outExp, outTuple)
        end

         #= Dummy traversal function used by getElementDependencies. =#
        function getElementDependenciesTraverserExit(inExp::Absyn.Exp, inTuple::Tuple{<:ElementList, List{<:ElementList}, ElementList, Bool}) ::Tuple{Absyn.Exp, Tuple{ElementList, List{ElementList}, ElementList, Bool}}
              local outTuple::Tuple{ElementList, List{ElementList}, ElementList, Bool}
              local outExp::Absyn.Exp

              (outExp, outTuple) = begin
                  local all_el::ElementList
                  local accum_el::ElementList
                  local stack_el::ElementList
                  local deps::ElementList
                  local rest_stack::List{ElementList}
                  local exp::Absyn.Exp
                  local ifExp::Absyn.Exp
                  local b::Bool
                   #=  If a binding contains an if-equation we don't really have any idea which
                   =#
                   #=  branch will be used, which causes some problems with Fluid. So we just
                   =#
                   #=  reset everything up to this point and pray that we didn't miss anything
                   =#
                   #=  important.
                   =#
                @matchcontinue (inExp, inTuple) begin
                  (exp && Absyn.IFEXP(ifExp = ifExp), (all_el, stack_el <| rest_stack, _, false))  => begin
                      (_, (_, _, deps, _)) = AbsynUtil.traverseExpBidir(ifExp, getElementDependenciesTraverserEnter, getElementDependenciesTraverserExit, (all_el, nil, nil, false))
                    (exp, (all_el, rest_stack, listAppend(deps, stack_el), false))
                  end

                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
          (outExp, outTuple)
        end

         #= Returns true if the given element has the same name as the given string,
          otherwise false. =#
        function isElementNamed(inElement::Tuple{<:SCode.Element, DAE.Mod}, inName::String) ::Bool
              local isNamed::Bool

              isNamed = begin
                  local name::String
                @match inElement begin
                  (SCode.COMPONENT(name = name), _)  => begin
                    name == inName
                  end

                  (SCode.CLASS(name = name), _)  => begin
                    name == inName
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNamed
        end

         #= Checks that two elements are equal, i.e. has the same name. =#
        function isElementEqual(inElement1::Tuple{<:SCode.Element, DAE.Mod}, inElement2::Tuple{<:SCode.Element, DAE.Mod}) ::Bool
              local isEqual::Bool

              isEqual = begin
                  local id1::String
                  local id2::String
                @match (inElement1, inElement2) begin
                  ((SCode.COMPONENT(name = id1), _), (SCode.COMPONENT(name = id2), _))  => begin
                    stringEqual(id1, id2)
                  end

                  ((SCode.CLASS(name = id1), _), (SCode.CLASS(name = id2), _))  => begin
                    stringEqual(id1, id2)
                  end

                  _  => begin
                      stringEq(elementName(inElement1), elementName(inElement2))
                  end
                end
              end
               #=  we can also have packages!
               =#
          isEqual
        end

         #= Checks the return value from Graph.topologicalSort. If the list of cycles is
          not empty, print an error message and fail, since it's not allowed for
          constants or parameters to have cyclic dependencies. =#
        function checkCyclicalComponents(inCycles::List{<:Tuple{<:Element, List{<:Element}}}, inEnv::FCore.Graph)
              () = begin
                  local cycles::List{List{Element}}
                  local names::List{List{String}}
                  local cycles_strs::List{String}
                  local cycles_str::String
                  local scope_str::String
                  local graph::List{Tuple{Element, List{Element}}}
                @matchcontinue inCycles begin
                   nil()  => begin
                    ()
                  end

                  _  => begin
                      graph = Graph.filterGraph(inCycles, isElementParamOrConst)
                      @match nil = Graph.findCycles(graph, isElementEqual)
                    ()
                  end

                  _  => begin
                        cycles = Graph.findCycles(inCycles, isElementEqual)
                        names = ListUtil.mapList(cycles, elementName)
                        cycles_strs = ListUtil.map1(names, stringDelimitList, ",")
                        cycles_str = stringDelimitList(cycles_strs, "}, {")
                        cycles_str = "{" + cycles_str + "}"
                        scope_str = FGraph.printGraphPathStr(inEnv)
                        Error.addMessage(Error.CIRCULAR_COMPONENTS, list(scope_str, cycles_str))
                        if ! Flags.isSet(Flags.IGNORE_CYCLES)
                          fail()
                        end
                      ()
                  end
                end
              end
        end

        function isElementParamOrConst(inElement::Tuple{<:SCode.Element, DAE.Mod}) ::Bool
              local outIsParamOrConst::Bool

              outIsParamOrConst = begin
                  local var::SCode.Variability
                @match inElement begin
                  (SCode.COMPONENT(attributes = SCode.ATTR(variability = var)), _)  => begin
                    SCodeUtil.isParameterOrConst(var)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsParamOrConst
        end

         #= Returns the name of the given element. =#
        function elementName(inElement::Tuple{<:SCode.Element, DAE.Mod}) ::String
              local outName::String

              local elem::SCode.Element

              outName = begin
                  local str::String
                @matchcontinue inElement begin
                  _  => begin
                      (elem, _) = inElement
                      outName = SCodeUtil.elementName(elem)
                    outName
                  end

                  _  => begin
                      str = SCodeDump.shortElementStr(Util.tuple21(inElement))
                    str
                  end
                end
              end
          outName
        end

         #= author: PA
          This function filters out the class definitions (ElementMod) list. =#
        function classdefElts2(inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, partialPrefix::SCode.Partial) ::Tuple{List{SCode.Element}, List{Tuple{SCode.Element, DAE.Mod}}}
              local outConstEls::List{Tuple{SCode.Element, DAE.Mod}}
              local outClassDefs::List{SCode.Element}

              (outClassDefs, outConstEls) = begin
                  local cdefs::List{SCode.Element}
                  local cdef::SCode.Element
                  local el::Tuple{SCode.Element, DAE.Mod}
                  local xs::List{Tuple{SCode.Element, DAE.Mod}}
                  local els::List{Tuple{SCode.Element, DAE.Mod}}
                  local attr::SCode.Attributes
                @matchcontinue (inElements, partialPrefix) begin
                  ( nil(), _)  => begin
                    (nil, nil)
                  end

                  ((cdef && SCode.CLASS(restriction = SCode.R_PACKAGE(__)), _) <| xs, SCode.PARTIAL(__))  => begin
                      (cdefs, els) = classdefElts2(xs, partialPrefix)
                    (_cons(cdef, cdefs), els)
                  end

                  ((cdef && SCode.CLASS(__), _) <| xs, SCode.NOT_PARTIAL(__))  => begin
                      (cdefs, els) = classdefElts2(xs, partialPrefix)
                    (_cons(cdef, cdefs), els)
                  end

                  (el && (SCode.COMPONENT(attributes = attr), _) <| xs, SCode.NOT_PARTIAL(__))  => begin
                      @match SCode.CONST() = SCodeUtil.attrVariability(attr)
                      (cdefs, els) = classdefElts2(xs, partialPrefix)
                    (cdefs, _cons(el, els))
                  end

                  (_ <| xs, _)  => begin
                      (cdefs, els) = classdefElts2(xs, partialPrefix)
                    (cdefs, els)
                  end
                end
              end
          (outClassDefs, outConstEls)
        end

         #= author: PA
          This function filters out the class definitions
          and import statements of an Element list. =#
        function classdefAndImpElts(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}}
              local restElts::List{SCode.Element}
              local cdefElts::List{SCode.Element}

              (cdefElts, restElts) = begin
                  local res::List{SCode.Element}
                  local xs::List{SCode.Element}
                  local cdef::SCode.Element
                  local imp::SCode.Element
                  local e::SCode.Element
                @match elts begin
                   nil()  => begin
                    (nil, nil)
                  end

                  cdef && SCode.CLASS(__) <| xs  => begin
                      (_, restElts) = classdefAndImpElts(xs)
                    (_cons(cdef, restElts), restElts)
                  end

                  imp && SCode.IMPORT(__) <| xs  => begin
                      (cdefElts, restElts) = classdefAndImpElts(xs)
                    (_cons(imp, cdefElts), restElts)
                  end

                  e <| xs  => begin
                      (cdefElts, restElts) = classdefAndImpElts(xs)
                    (cdefElts, _cons(e, restElts))
                  end
                end
              end
          (cdefElts, restElts)
        end

         #= /*
        protected function extendsElts
        \"author: PA
          This function filters out the extends Element in an Element list\"
          input list<SCode.Element> inSCodeElementLst;
          output list<SCode.Element> outSCodeElementLst;
        algorithm
          outSCodeElementLst := match (inSCodeElementLst)
            local
              list<SCode.Element> res,xs;
              SCode.Element cdef;
            case ({}) then {};
            case (((cdef as SCode.EXTENDS(baseClassPath = _)) :: xs))
              equation
                res = extendsElts(xs);
              then
                (cdef :: res);
            case ((_ :: xs))
              equation
                res = extendsElts(xs);
              then
                res;
          end match;
        end extendsElts;
        */ =#

         #= author: PA
          This function filters out the component Element in an Element list =#
        function componentElts(inSCodeElementLst::List{<:SCode.Element}) ::List{SCode.Element}
              local outSCodeElementLst::List{SCode.Element}

              outSCodeElementLst = begin
                  local res::List{SCode.Element}
                  local xs::List{SCode.Element}
                  local cdef::SCode.Element
                @match inSCodeElementLst begin
                   nil()  => begin
                    nil
                  end

                  cdef && SCode.COMPONENT(__) <| xs  => begin
                      res = componentElts(xs)
                    _cons(cdef, res)
                  end

                  _ <| xs  => begin
                      res = componentElts(xs)
                    res
                  end
                end
              end
          outSCodeElementLst
        end

         #= This function adds class definitions and import statements to the environment. =#
        function addClassdefsToEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inClasses::List{<:SCode.Element}, inImpl::Bool, inRedeclareMod::Option{<:DAE.Mod}, checkDuplicates::Bool = false) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              for c in inClasses
                (outCache, outEnv, outIH) = addClassdefToEnv(outCache, outEnv, outIH, inPrefix, c, inImpl, inRedeclareMod, checkDuplicates)
              end
          (outCache, outEnv, outIH)
        end

         #= author: PA
          Helper relation to addClassdefsToEnv =#
        function addClassdefToEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSCodeElement::SCode.Element, inBoolean::Bool, redeclareMod::Option{<:DAE.Mod}, checkDuplicates::Bool = false) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local cl2::SCode.Element
                  local enumclass::SCode.Element
                  local imp::SCode.Element
                  local sel1::SCode.Element
                  local elt::SCode.Element
                  local enumLst::List{SCode.Enum}
                  local impl::Bool
                  local ih::InstanceHierarchy
                  local info::SourceInfo
                  local pre::Prefix.PrefixType
                  local s::String
                  local cmt::SCode.Comment
                  local rpp::SCode.Replaceable
                  local m::DAE.Mod
                   #=  we do have a redeclaration of class.
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inSCodeElement, redeclareMod) begin
                  (cache, env, ih, pre, sel1 && SCode.CLASS(__), SOME(m))  => begin
                      m = Mod.lookupCompModification(m, sel1.name)
                      @match false = valueEq(m, DAE.NOMOD())
                      env_1 = FGraph.mkClassNode(env, sel1, pre, m)
                      (cache, env_1, ih, cl2) = addClassdefsToEnv3(cache, env_1, ih, pre, redeclareMod, sel1)
                      ih = InnerOuter.addClassIfInner(cl2, pre, env_1, ih)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, pre, sel1 && SCode.CLASS(__), _)  => begin
                      env_1 = FGraph.mkClassNode(env, sel1, pre, DAE.NOMOD(), checkDuplicates)
                      ih = InnerOuter.addClassIfInner(sel1, pre, env_1, ih)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, _, imp && SCode.IMPORT(__), _)  => begin
                      env_1 = FGraph.mkImportNode(env, imp)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, _, elt && SCode.DEFINEUNIT(__), _)  => begin
                      env_1 = FGraph.mkDefunitNode(env, elt)
                    (cache, env_1, ih)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstUtil.addClassdefToEnv2 failed\\n")
                      fail()
                  end
                end
              end
               #=  call to redeclareType which calls updateComponents in env wich updates the class frame
               =#
               #=  otherwise, extend frame with in class.
               =#
               #=  Debug.traceln(\"Extend frame \" + FGraph.printGraphPathStr(env) + \" with \" + SCodeUtil.className(cl));
               =#
               #=  adrpo: we should have no imports after SCodeFlatten!
               =#
               #=  unfortunately we do because of the way we evaluate
               =#
               #=  programs for interactive evaluation
               =#
          (outCache, outEnv, outIH)
        end

         #= fails if the comp env path is NOT a prefix of comp type path =#
        function checkCompEnvPathVsCompTypePath(inCompEnvPath::Option{<:Absyn.Path}, inCompTypePath::Absyn.Path)
              _ = begin
                  local ep::Absyn.Path
                  local tp::Absyn.Path
                   #=  if the type path is just an ident, we have a problem!
                   =#
                @match (inCompEnvPath, inCompTypePath) begin
                  (_, Absyn.IDENT(_))  => begin
                    ()
                  end

                  (SOME(ep), tp)  => begin
                      tp = AbsynUtil.stripLast(tp)
                      @match true = AbsynUtil.pathPrefixOf(tp, ep)
                    ()
                  end
                end
              end
               #=  if env path where the component C resides A.B.P.Z
               =#
               #=  has as prefix the component C type path C say A.B.P.C
               =#
               #=  it means that when we search for component A.B.P.Z.C
               =#
               #=  we might find the type: A.B.P.C instead.
               =#
        end

         #= author: PA
          Since Modelica has removed the declare before use limitation, all
          components are intially added untyped to the environment, i.e. the
          SCode.Element is added. This is performed by this function. Later,
          during the second pass of the instantiation of components, the components
          are updated  in the environment. This is done by the function
          update_components_in_env. This function is also responsible for
          changing parameters into structural  parameters if they are affecting
          the number of variables or equations. This is needed because Modelica has
          no language construct for structural parameters, i.e. they must be
          detected by the compiler.

          Structural parameters are identified by investigating array dimension
          sizes of components and by investigating if-equations. If an if-equation
          has a boolean expression controlled by parameter(s), these are structural
          parameters. =#
        function addComponentsToEnv(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuter.InstHierarchy, mod::DAE.Mod, prefix::Prefix.PrefixType, state::ClassInf.SMNode, components::List{<:Tuple{<:SCode.Element, DAE.Mod}}, impl::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}




              local comp::SCode.Element
              local comp2::SCode.Element
              local cmod::DAE.Mod
              local local_mod::DAE.Mod
              local comp_mod::DAE.Mod
              local mod2::DAE.Mod
              local ty_path::Absyn.Path
              local prefs::SCode.Prefixes
              local attr::SCode.Attributes
              local dattr::DAE.Attributes
              local error::Bool = false
              local err_msg::String

              for compmod in components
                (comp, cmod) = compmod
                error = begin
                  @matchcontinue comp begin
                    SCode.COMPONENT(typeSpec = Absyn.TPATH(path = ty_path)) where (comp.name == AbsynUtil.pathLastIdent(ty_path))  => begin
                         #=  name is equal with the last ident from type path.
                         =#
                         #=  this is only a problem if the environment in which the component
                         =#
                         #=  resides has as prefix the type path (without the last ident)
                         =#
                         #=  as this would mean that we might find the type instead of the
                         =#
                         #=  component when we do lookup
                         =#
                        checkCompEnvPathVsCompTypePath(FGraph.getScopePath(env), ty_path)
                        err_msg = comp.name + " in env: " + FGraph.printGraphPathStr(env)
                        Error.addSourceMessage(Error.COMPONENT_NAME_SAME_AS_TYPE_NAME, list(err_msg, AbsynUtil.pathString(ty_path)), comp.info)
                      true
                    end

                    SCode.COMPONENT(prefixes = prefs && SCode.PREFIXES(__), attributes = attr && SCode.ATTR(__))  => begin
                        ty_path = AbsynUtil.typeSpecPath(comp.typeSpec)
                        local_mod = Mod.lookupModificationP(mod, ty_path)
                        if SCodeUtil.finalBool(SCodeUtil.prefixesFinal(prefs))
                          comp.modifications = traverseModAddFinal(comp.modifications)
                        end
                        (cache, env, ih, comp2, mod2) = Inst.redeclareType(cache, env, ih, local_mod, comp, prefix, state, impl, cmod)
                        comp_mod = Mod.lookupCompModification(mod, comp.name)
                        cmod = Mod.merge(comp_mod, cmod)
                        dattr = DAEUtil.translateSCodeAttrToDAEAttr(attr, prefs)
                        env = FGraph.mkComponentNode(env, DAE.TYPES_VAR(comp.name, dattr, DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE()), comp, cmod, FCore.VAR_UNTYPED(), FGraph.empty())
                      false
                    end

                    SCode.COMPONENT(__)  => begin
                      true
                    end

                    _  => begin
                        false
                    end
                  end
                end
                if error
                  fail()
                end
              end
               #=  Something went wrong.
               =#
               #=  Skip non-components.
               =#
          (cache, env, ih)
        end

         #= author: PA
          This function collects all variables from the dimensionalities of
          component elements. These variables are candidates for structural
          parameters. =#
        function getCrefsFromCompdims(inComponents::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{Absyn.ComponentRef}
              local outCrefs::List{Absyn.ComponentRef}

              outCrefs = begin
                  local crefs1::List{Absyn.ComponentRef}
                  local crefs2::List{Absyn.ComponentRef}
                  local crefs::List{Absyn.ComponentRef}
                  local arraydim::List{Absyn.Subscript}
                  local xs::List{Tuple{SCode.Element, DAE.Mod}}
                @matchcontinue inComponents begin
                   nil()  => begin
                    nil
                  end

                  (SCode.COMPONENT(attributes = SCode.ATTR(arrayDims = arraydim)), _) <| xs  => begin
                      crefs1 = getCrefFromDim(arraydim)
                      crefs2 = getCrefsFromCompdims(xs)
                      crefs = listAppend(crefs1, crefs2)
                    crefs
                  end

                  _ <| xs  => begin
                      crefs = getCrefsFromCompdims(xs)
                    crefs
                  end
                end
              end
          outCrefs
        end

         #= author: PA
          This function checks if a componentreferece is a member of
          a list of component references, disregarding subscripts. =#
        function memberCrefs(inComponentRef::Absyn.ComponentRef, inComponentRefs::List{<:Absyn.ComponentRef}) ::Bool
              local outIsMember::Bool

              outIsMember = ListUtil.isMemberOnTrue(inComponentRef, inComponentRefs, AbsynUtil.crefEqualNoSubs)
          outIsMember
        end

         #=
         if we have an outer modification: redeclare X = Y
         and a component modification redeclare X = Z
         update the component modification to redeclare X = Y =#
        function chainRedeclares(inModOuter::DAE.Mod #= the outer mod which should overwrite the inner mod =#, inModInner::SCode.Mod #= the inner mod =#) ::SCode.Mod
              local outMod::SCode.Mod

              local b::Bool

              outMod = begin
                @match (inModOuter, inModInner) begin
                  (_, _)  => begin
                      (outMod, b) = chainRedeclare_dispatch(inModOuter, inModInner)
                    if b
                          outMod
                        else
                          inModInner
                        end
                  end
                end
              end
               #= /*
                    case(_, _)
                      equation
                        outMod = chainRedeclare_dispatch(inModOuter,inModInner);
                        false = SCodeUtil.modEqual(inModInner, outMod);
                        print(\"Chain:\\nO:\" + Mod.printModStr(inModOuter) + \"\\nI:\" + SCodeDump.printModStr(inModInner, SCodeDump.defaultOptions) + \"\\nR:\" + SCodeDump.printModStr(outMod, SCodeDump.defaultOptions) + \"\\n\");
                      then
                        outMod;
                    */ =#
          outMod
        end

         #=
         if we have an outer modification: redeclare X = Y
         and a component modification redeclare X = Z
         update the component modification to redeclare X = Y =#
        function chainRedeclare_dispatch(inModOuter::DAE.Mod #= the outer mod which should overwrite the inner mod =#, inModInner::SCode.Mod #= the inner mod =#) ::Tuple{SCode.Mod, Bool}
              local change::Bool
              local outMod::SCode.Mod

              (outMod, change) = begin
                  local f::SCode.Final
                  local e::SCode.Each
                  local cls::SCode.Element
                  local name::String
                  local nInner::String
                  local nDerivedInner::String
                  local rest::List{SCode.SubMod}
                  local subs::List{SCode.SubMod}
                  local b::Option{Absyn.Exp}
                  local m::SCode.Mod
                  local m2::SCode.Mod
                  local sm::SCode.SubMod
                  local info::SourceInfo
                   #=  outer B(redeclare X = Y), inner B(redeclare Y = Z) -> B(redeclare X = Z)
                   =#
                @matchcontinue (inModOuter, inModInner) begin
                  (_, SCode.REDECL(f, e, SCode.CLASS(name = nInner, classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(nDerivedInner))))))  => begin
                      @match DAE.REDECL(element = cls) = Mod.lookupCompModification(inModOuter, nDerivedInner)
                      cls = SCodeUtil.setClassName(nInner, cls)
                    (SCode.REDECL(f, e, cls), true)
                  end

                  (_, SCode.REDECL(f, e, SCode.CLASS(name = nInner, classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(_))))))  => begin
                      @match DAE.REDECL(element = cls) = Mod.lookupCompModification(inModOuter, nInner)
                    (SCode.REDECL(f, e, cls), true)
                  end

                  (_, SCode.MOD(f, e, SCode.NAMEMOD(name, m && SCode.REDECL(__)) <| rest, b, info))  => begin
                      m2 = chainRedeclare_dispatch(inModOuter, m)
                      @match (SCode.MOD(subModLst = subs), _) = chainRedeclare_dispatch(inModOuter, SCode.MOD(f, e, rest, b, info))
                    (SCode.MOD(f, e, _cons(SCode.NAMEMOD(name, m2), subs), b, info), true)
                  end

                  (_, SCode.MOD(f, e, sm <| rest, b, info))  => begin
                      @match (SCode.MOD(subModLst = subs), change) = chainRedeclare_dispatch(inModOuter, SCode.MOD(f, e, rest, b, info))
                    (SCode.MOD(f, e, _cons(sm, subs), b, info), change)
                  end

                  _  => begin
                      (inModInner, false)
                  end
                end
              end
               #=  lookup the class mod in the outer
               =#
               #=  outer B(redeclare X = Y), inner B(redeclare X = Z) -> B(redeclare X = Z)
               =#
               #=  lookup the class mod in the outer
               =#
               #=  a mod with a name mod
               =#
               #=  lookup the class mod in the outer
               =#
               #=  something else, move along!
               =#
          (outMod, change)
        end

         #= @author: adrpo
         add the record constructor to the cache if we have
         it as the type of an input component to a function =#
        function addRecordConstructorsToTheCache(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inDirection::Absyn.Direction, inClass::SCode.Element, inInstDims::List{<:List{<:DAE.Dimension}}) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InstanceHierarchy
                  local name::String
                  local path::Absyn.Path
                   #=  add it to the cache if we have a input record component
                   =#
                @matchcontinue (inCache, inEnv, inIH, inMod, inPrefix, inState, inDirection, inClass, inInstDims) begin
                  (_, _, _, _, _, ClassInf.FUNCTION(path = path), _, SCode.CLASS(name = name, restriction = SCode.R_RECORD(_)), _)  => begin
                      print("Depreciated record constructor used: Inst.addRecordConstructorsToTheCache")
                      @match true = AbsynUtil.isInputOrOutput(inDirection)
                      @match false = stringEq(AbsynUtil.pathLastIdent(path), name)
                      (cache, env, ih) = InstFunction.implicitFunctionInstantiation(inCache, inEnv, inIH, inMod, inPrefix, inClass, inInstDims)
                    (cache, env, ih)
                  end

                  _  => begin
                      (inCache, inEnv, inIH)
                  end
                end
              end
               #=  false = Config.acceptMetaModelicaGrammar();
               =#
               #=  TODO, add the env path to the check!
               =#
               #=  print(\"InstFunction.implicitFunctionInstantiation: \" + name + \" in f:\" + AbsynUtil.pathString(path) + \" in s:\" + FGraph.printGraphPathStr(inEnv) + \" m: \" + Mod.printModStr(inMod) + \"\\n\");
               =#
               #=  do nothing otherwise!
               =#
          (outCache, outEnv, outIH)
        end

         #= Check if variable is multiply declared and
         that all declarations are identical if so. =#
        function checkMultiplyDeclared(cache::FCore.Cache, env::FCore.Graph, mod::DAE.Mod, prefix::Prefix.PrefixType, ciState::ClassInf.SMNode, compTuple::Tuple{<:SCode.Element, DAE.Mod}, instDims::List{<:List{<:DAE.Dimension}}, impl::Bool) ::Bool
              local alreadyDeclared::Bool

              alreadyDeclared = begin
                  local n::String
                  local n2::String
                  local oldElt::SCode.Element
                  local oldMod::DAE.Mod
                  local newComp::Tuple{SCode.Element, DAE.Mod}
                  local instStatus::FCore.Status
                  local oldClass::SCode.Element
                  local newClass::SCode.Element
                @matchcontinue (cache, env, mod, prefix, ciState, compTuple, instDims, impl) begin
                  (_, _, _, _, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("checkMultiplyDeclared")
                    fail()
                  end

                  (_, _, _, _, _, (SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_))), _), _, _)  => begin
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, (SCode.COMPONENT(__), DAE.REDECL(_, _, _)), _, _)  => begin
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, newComp && (SCode.COMPONENT(name = n), _), _, _)  => begin
                      (_, _, oldElt, oldMod, instStatus, _) = Lookup.lookupIdentLocal(cache, env, n)
                      checkMultipleElementsIdentical(cache, env, (oldElt, oldMod), newComp)
                      alreadyDeclared = instStatusToBool(instStatus)
                      ErrorExt.delCheckpoint("checkMultiplyDeclared")
                    alreadyDeclared
                  end

                  (_, _, _, _, _, (SCode.COMPONENT(name = n), _), _, _)  => begin
                      @shouldFail (_, _, _, _, _, _) = Lookup.lookupIdentLocal(cache, env, n)
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, (SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_))), _), _, _)  => begin
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, (SCode.CLASS(__), DAE.REDECL(_, _, _)), _, _)  => begin
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, (SCode.CLASS(name = n, classDef = SCode.PARTS(elementLst = SCode.EXTENDS(baseClassPath = Absyn.IDENT(n2)) <| _)), _), _, _)  => begin
                      n = "parent" + "." + n
                      @match 0 = System.stringFind(n, n2)
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  (_, _, _, _, _, (newClass && SCode.CLASS(name = n), _), _, _)  => begin
                      (oldClass, _) = Lookup.lookupClassLocal(env, n)
                      checkMultipleClassesEquivalent(oldClass, newClass)
                      ErrorExt.delCheckpoint("checkMultiplyDeclared")
                    true
                  end

                  (_, _, _, _, _, (SCode.CLASS(name = n), _), _, _)  => begin
                      @shouldFail (_, _) = Lookup.lookupClassLocal(env, n)
                      ErrorExt.rollBack("checkMultiplyDeclared")
                    false
                  end

                  _  => begin
                        ErrorExt.delCheckpoint("checkMultiplyDeclared")
                        if Flags.isSet(Flags.FAILTRACE)
                          Debug.trace("-Inst.checkMultiplyDeclared failed\\n")
                        end
                      fail()
                  end
                end
              end
          alreadyDeclared
        end

         #= Translates InstStatus to a boolean indicating if component is allready declared. =#
        function instStatusToBool(instStatus::FCore.Status) ::Bool
              local alreadyDeclared::Bool

              alreadyDeclared = begin
                @match instStatus begin
                  FCore.VAR_DAE(__)  => begin
                    true
                  end

                  FCore.VAR_UNTYPED(__)  => begin
                    false
                  end

                  FCore.VAR_TYPED(__)  => begin
                    false
                  end
                end
              end
          alreadyDeclared
        end

         #= Checks that the old declaration is identical
         to the new one. If not, give error message =#
        function checkMultipleElementsIdentical(inCache::FCore.Cache, inEnv::FCore.Graph, oldComponent::Tuple{<:SCode.Element, DAE.Mod}, newComponent::Tuple{<:SCode.Element, DAE.Mod})
              _ = begin
                  local oldElt::SCode.Element
                  local newElt::SCode.Element
                  local oldMod::DAE.Mod
                  local newMod::DAE.Mod
                  local s1::String
                  local s2::String
                  local s::String
                  local smod1::SCode.Mod
                  local smod2::SCode.Mod
                  local env::FCore.Graph
                  local env1::FCore.Graph
                  local env2::FCore.Graph
                  local cache::FCore.Cache
                  local c1::SCode.Element
                  local c2::SCode.Element
                  local tpath1::Absyn.Path
                  local tpath2::Absyn.Path
                  local old_info::SourceInfo
                  local new_info::SourceInfo
                  local prefixes1::SCode.Prefixes
                  local prefixes2::SCode.Prefixes
                  local attr1::SCode.Attributes
                  local attr2::SCode.Attributes
                  local tp1::Absyn.TypeSpec
                  local tp2::Absyn.TypeSpec
                  local n1::String
                  local n2::String
                  local ad1::Option{Absyn.ArrayDim}
                  local ad2::Option{Absyn.ArrayDim}
                  local cond1::Option{Absyn.Exp}
                  local cond2::Option{Absyn.Exp}
                   #=  try equality first!
                   =#
                @matchcontinue (inCache, inEnv, oldComponent, newComponent) begin
                  (_, _, (oldElt, _), (newElt, _))  => begin
                      @match true = SCodeUtil.elementEqual(oldElt, newElt)
                    ()
                  end

                  (cache, env, (SCode.COMPONENT(n1, prefixes1, attr1, Absyn.TPATH(tpath1, ad1), smod1, _, cond1, _), _), (SCode.COMPONENT(n2, prefixes2, attr2, Absyn.TPATH(tpath2, ad2), smod2, _, cond2, _), _))  => begin
                      @match true = stringEq(n1, n2)
                      @match true = SCodeUtil.prefixesEqual(prefixes1, prefixes2)
                      @match true = SCodeUtil.attributesEqual(attr1, attr2)
                      @match true = SCodeUtil.modEqual(smod1, smod2)
                      equality(ad1, ad2)
                      equality(cond1, cond2)
                      (_, c1, env1) = Lookup.lookupClass(cache, env, tpath1)
                      (_, c2, env2) = Lookup.lookupClass(cache, env, tpath2)
                      @match true = stringEq(FGraph.printGraphPathStr(env1), FGraph.printGraphPathStr(env2))
                      @match true = SCodeUtil.elementEqual(c1, c2)
                    ()
                  end

                  (cache, env, (oldElt && SCode.COMPONENT(n1, prefixes1, attr1, Absyn.TPATH(tpath1, ad1), smod1, _, cond1, old_info), _), (newElt && SCode.COMPONENT(n2, prefixes2, attr2, Absyn.TPATH(tpath2, ad2), smod2, _, cond2, new_info), _))  => begin
                      @match true = stringEq(n1, n2)
                      @match true = stringEq(n1, "m_flow")
                      @match true = SCodeUtil.prefixesEqual(prefixes1, prefixes2)
                      @match true = SCodeUtil.attributesEqual(attr1, attr2)
                      @match false = SCodeUtil.modEqual(smod1, smod2)
                      equality(ad1, ad2)
                      equality(cond1, cond2)
                      (_, c1, env1) = Lookup.lookupClass(cache, env, tpath1)
                      (_, c2, env2) = Lookup.lookupClass(cache, env, tpath2)
                      @match true = stringEq(FGraph.printGraphPathStr(env1), FGraph.printGraphPathStr(env2))
                      @match true = SCodeUtil.elementEqual(c1, c2)
                      s1 = SCodeDump.unparseElementStr(oldElt, SCodeDump.defaultOptions)
                      s2 = SCodeDump.unparseElementStr(newElt, SCodeDump.defaultOptions)
                      s = "Inherited elements are not identical: bug: https://trac.modelica.org/Modelica/ticket/627\\n\\tfirst:  " + s1 + "\\n\\tsecond: " + s2 + "\\nContinue ...."
                      Error.addMultiSourceMessage(Error.COMPILER_WARNING, list(s), list(old_info, new_info))
                    ()
                  end

                  (_, _, (oldElt && SCode.COMPONENT(info = old_info), _), (newElt && SCode.COMPONENT(info = new_info), _))  => begin
                      s1 = SCodeDump.unparseElementStr(oldElt, SCodeDump.defaultOptions)
                      s2 = SCodeDump.unparseElementStr(newElt, SCodeDump.defaultOptions)
                      Error.addMultiSourceMessage(Error.DUPLICATE_ELEMENTS_NOT_IDENTICAL, list(s1, s2), list(old_info, new_info))
                    fail()
                  end
                end
              end
               #=  NOTE: Should be type identical instead? see spec.
               =#
               #=  p.23, check of flattening. \"Check that duplicate elements are identical\".
               =#
               #=  adrpo: see if they are not syntactically equivalent, but semantically equivalent!
               =#
               #=         see Modelica Spec. 3.1, page 66.
               =#
               #=  COMPONENT
               =#
               #=  see if the most stuff is the same!
               =#
               #=  if we lookup tpath1 and tpath2 and reach the same class, we're fine!
               =#
               #=  the class has the same environment
               =#
               #=  the classes are the same!
               =#
               #= /*
                       add a warning and let it continue!
                      s1 = SCodeDump.unparseElementStr(oldElt);
                      s2 = SCodeDump.unparseElementStr(newElt);
                      Error.addMultiSourceMessage(Error.DUPLICATE_ELEMENTS_NOT_SYNTACTICALLY_IDENTICAL, {s1, s2}, {old_info, new_info});
                      */ =#
               #=  adrpo: handle bug: https:trac.modelica.org/Modelica/ticket/627
               =#
               #=         TODO! FIXME! REMOVE! remove when the bug is fixed!
               =#
               #=  see if the most stuff is the same!
               =#
               #=  if we lookup tpath1 and tpath2 and reach the same class, we're fine!
               =#
               #=  the class has the same environment
               =#
               #=  the classes are the same!
               =#
               #=  add a warning and let it continue!
               =#
               #=  fail baby and add a source message!
               =#
        end

         #= Checks that the old class definition is equivalent
         to the new one. If not, give error message =#
        function checkMultipleClassesEquivalent(oldClass::SCode.Element, newClass::SCode.Element)
              _ = begin
                  local oldCl::SCode.Element
                  local newCl::SCode.Element
                  local s1::String
                  local s2::String
                  local sl1::List{String}
                  local sl2::List{String}
                  local enumLst::List{SCode.Enum}
                  local elementLst::List{SCode.Element}
                  local info1::SourceInfo
                  local info2::SourceInfo
                   #=    Special cases for checking enumerations which can be represented differently
                   =#
                @matchcontinue (oldClass, newClass) begin
                  (SCode.CLASS(classDef = SCode.ENUMERATION(enumLst = enumLst)), SCode.CLASS(restriction = SCode.R_ENUMERATION(__), classDef = SCode.PARTS(elementLst = elementLst)))  => begin
                      sl1 = ListUtil.map(enumLst, SCodeUtil.enumName)
                      sl2 = ListUtil.map(elementLst, SCodeUtil.elementName)
                      ListUtil.threadMapAllValue(sl1, sl2, stringEq, true)
                    ()
                  end

                  (SCode.CLASS(restriction = SCode.R_ENUMERATION(__), classDef = SCode.PARTS(elementLst = elementLst)), SCode.CLASS(classDef = SCode.ENUMERATION(enumLst = enumLst)))  => begin
                      sl1 = ListUtil.map(enumLst, SCodeUtil.enumName)
                      sl2 = ListUtil.map(elementLst, SCodeUtil.elementName)
                      ListUtil.threadMapAllValue(sl1, sl2, stringEq, true)
                    ()
                  end

                  (oldCl, newCl)  => begin
                      @match true = SCodeUtil.elementEqual(oldCl, newCl)
                    ()
                  end

                  (oldCl, newCl)  => begin
                      s1 = SCodeDump.unparseElementStr(oldCl, SCodeDump.defaultOptions)
                      s2 = SCodeDump.unparseElementStr(newCl, SCodeDump.defaultOptions)
                      info1 = SCodeUtil.elementInfo(oldCl)
                      info2 = SCodeUtil.elementInfo(newCl)
                      Error.addMultiSourceMessage(Error.DUPLICATE_CLASSES_NOT_EQUIVALENT, list(s1, s2), list(info1, info2))
                    fail()
                  end
                end
              end
               #=  try equality first!
               =#
               #= print(\" *** error message added *** \\n\");
               =#
        end

        function removeOptCrefFromCrefs(inCrefs::List{<:Absyn.ComponentRef}, inCref::Option{<:Absyn.ComponentRef}) ::List{Absyn.ComponentRef}
              local outCrefs::List{Absyn.ComponentRef}

              outCrefs = begin
                  local cref::Absyn.ComponentRef
                @match (inCrefs, inCref) begin
                  (_, SOME(cref))  => begin
                    removeCrefFromCrefs(inCrefs, cref)
                  end

                  _  => begin
                      inCrefs
                  end
                end
              end
          outCrefs
        end

         #= Removes a variable from a variable list =#
        function removeCrefFromCrefs(inAbsynComponentRefLst::List{<:Absyn.ComponentRef}, inComponentRef::Absyn.ComponentRef) ::List{Absyn.ComponentRef}
              local outAbsynComponentRefLst::List{Absyn.ComponentRef}

              outAbsynComponentRefLst = begin
                  local n1::String
                  local n2::String
                  local rest_1::List{Absyn.ComponentRef}
                  local rest::List{Absyn.ComponentRef}
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                @match (inAbsynComponentRefLst, inComponentRef) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (Absyn.CREF_IDENT(name = n1, subscripts =  nil()) <| rest, cr2 && Absyn.CREF_IDENT(name = n2, subscripts =  nil())) where (stringEq(n1, n2))  => begin
                      rest_1 = removeCrefFromCrefs(rest, cr2)
                    rest_1
                  end

                  (Absyn.CREF_QUAL(name = n1) <| rest, cr2 && Absyn.CREF_IDENT(name = n2)) where (stringEq(n1, n2))  => begin
                      rest_1 = removeCrefFromCrefs(rest, cr2)
                    rest_1
                  end

                  (cr1 <| rest, cr2)  => begin
                      rest_1 = removeCrefFromCrefs(rest, cr2)
                    _cons(cr1, rest_1)
                  end
                end
              end
               #=  If modifier like on comp like: T t(x=t.y) => t.y must be removed
               =#
          outAbsynComponentRefLst
        end

         #= Author: BZ, 2009-07
         A function for filtering out the modifications on the constraining type class. =#
        function keepConstrainingTypeModifersOnly(inMod::DAE.Mod, elems::List{<:SCode.Element}) ::DAE.Mod
              local filteredMod::DAE.Mod

              filteredMod = begin
                  local f::SCode.Final
                  local e::SCode.Each
                  local oe::Option{DAE.EqMod}
                  local subs::List{DAE.SubMod}
                  local compNames::List{String}
                  local info::SourceInfo
                @match (inMod, elems) begin
                  (_,  nil())  => begin
                    inMod
                  end

                  (DAE.NOMOD(__), _)  => begin
                    DAE.NOMOD()
                  end

                  (DAE.REDECL(_, _, _), _)  => begin
                    inMod
                  end

                  (DAE.MOD(f, e, subs, oe, info), _)  => begin
                      compNames = ListUtil.map(elems, SCodeUtil.elementName)
                      subs = keepConstrainingTypeModifersOnly2(subs, compNames)
                    DAE.MOD(f, e, subs, oe, info)
                  end
                end
              end
          filteredMod
        end

         #=
        Author BZ
        Helper function for keepConstrainingTypeModifersOnly =#
        function keepConstrainingTypeModifersOnly2(isubs::List{<:DAE.SubMod}, elems::List{<:String}) ::List{DAE.SubMod}
              local osubs::List{DAE.SubMod}

              osubs = begin
                  local sub::DAE.SubMod
                  local mod::DAE.Mod
                  local n::String
                  local osubs2::List{DAE.SubMod}
                  local subs::List{DAE.SubMod}
                  local b::Bool
                @match (isubs, elems) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (subs,  nil())  => begin
                    subs
                  end

                  (sub && DAE.NAMEMOD(ident = n) <| subs, _) where (ListUtil.isMemberOnTrue(n, elems, stringEq))  => begin
                    _cons(sub, keepConstrainingTypeModifersOnly2(subs, elems))
                  end

                  (_ <| subs, _)  => begin
                    keepConstrainingTypeModifersOnly2(subs, elems)
                  end
                end
              end
          osubs
        end

         #= Author: BZ, 2009-07
         This function examines a optional Absyn.ConstrainClass argument.
         If there is a constraining class, lookup the class and return its elements. =#
        function extractConstrainingComps(cc::Option{<:SCode.ConstrainClass}, env::FCore.Graph, pre::Prefix.PrefixType) ::List{SCode.Element}
              local elems::List{SCode.Element}

              elems = begin
                  local path::Absyn.Path
                  local cl::SCode.Element
                  local name::String
                  local selems::List{SCode.Element}
                  local extendselts::List{SCode.Element}
                  local compelts::List{SCode.Element}
                  local extcompelts::List{SCode.Element}
                  local classextendselts::List{SCode.Element}
                  local classes::List{SCode.Element}
                  local extcomps::List{Tuple{SCode.Element, DAE.Mod}}
                  local mod::SCode.Mod
                  local cmt::SCode.Comment
                @matchcontinue (cc, env, pre) begin
                  (NONE(), _, _)  => begin
                    nil
                  end

                  (SOME(SCode.CONSTRAINCLASS(constrainingClass = path)), _, _)  => begin
                      @match (_, SCode.CLASS(name = name, classDef = SCode.PARTS(elementLst = selems)), _) = Lookup.lookupClass(FCoreUtil.emptyCache(), env, path)
                      (classes, classextendselts, extendselts, compelts) = splitElts(selems)
                      (_, _, _, _, extcomps, _, _, _, _) = InstExtends.instExtendsAndClassExtendsList(FCoreUtil.emptyCache(), env, InnerOuter.emptyInstHierarchy, DAE.NOMOD(), pre, extendselts, classextendselts, selems, ClassInf.UNKNOWN(Absyn.IDENT("")), name, true, false)
                      extcompelts = ListUtil.map(extcomps, Util.tuple21)
                      compelts = listAppend(classes, listAppend(compelts, extcompelts))
                    compelts
                  end

                  (SOME(SCode.CONSTRAINCLASS(path, mod, cmt)), _, _)  => begin
                      @match (_, SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = path))), _) = Lookup.lookupClass(FCoreUtil.emptyCache(), env, path)
                      compelts = extractConstrainingComps(SOME(SCode.CONSTRAINCLASS(path, mod, cmt)), env, pre)
                    compelts
                  end
                end
              end
          elems
        end

         #= This function takes two DAElists, the first with equations generated by
           InstBinding.instModEquation and the second the variables that bindings
           belonged to. The function moves the equations back as bindings for the
           variables, used for fixing record bindings. =#
        function moveBindings(inEquations::DAE.DAElist, inVariables::DAE.DAElist) ::DAE.DAElist
              local outVariables::DAE.DAElist

              local eqs::List{DAE.Element}
              local vars::List{DAE.Element}

              if Config.getGraphicsExpMode()
                outVariables = inVariables
                return outVariables
              end
              @match DAE.DAE(elementLst = eqs) = inEquations
              @match DAE.DAE(elementLst = vars) = inVariables
              Error.assertion(intEq(listLength(eqs), listLength(vars)), "- InstUtil.moveBindings: Mismatched number of equations and variables.", AbsynUtil.dummyInfo)
              vars = ListUtil.threadMap(eqs, vars, moveBindings2)
              outVariables = DAE.DAE(vars)
          outVariables
        end

        function moveBindings2(inEquation::DAE.Element, inVariable::DAE.Element) ::DAE.Element
              local outVariable::DAE.Element

              outVariable = begin
                  local cref::DAE.ComponentRef
                  local kind::DAE.VarKind
                  local dir::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local vis::DAE.VarVisibility
                  local ty::DAE.Type
                  local dims::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local src::DAE.ElementSource
                  local attr::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local io::Absyn.InnerOuter
                  local bind_exp::DAE.Exp
                @matchcontinue (inEquation, inVariable) begin
                  (_, DAE.VAR(cref, kind, dir, prl, vis, ty, _, dims, ct, src, attr, cmt, io))  => begin
                      bind_exp = moveBindings3(inEquation)
                    DAE.VAR(cref, kind, dir, prl, vis, ty, SOME(bind_exp), dims, ct, src, attr, cmt, io)
                  end

                  (_, DAE.VAR(componentRef = cref))  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- InstUtil.moveBindings failed on " + ComponentReference.printComponentRefStr(cref))
                    fail()
                  end
                end
              end
          outVariable
        end

        function moveBindings3(inEquation::DAE.Element) ::DAE.Exp
              local outBinding::DAE.Exp

              outBinding = begin
                  local bind_exp::DAE.Exp
                @match inEquation begin
                  DAE.EQUATION(scalar = bind_exp)  => begin
                    bind_exp
                  end

                  DAE.DEFINE(exp = bind_exp)  => begin
                    bind_exp
                  end
                end
              end
          outBinding
        end

        function checkModificationOnOuter(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inName::String, inCref::DAE.ComponentRef, inMod::DAE.Mod, inVariability::SCode.Variability, inInnerOuter::Absyn.InnerOuter, inImpl::Bool, inInfo::SourceInfo)
              _ = begin
                  local sm::HashSet.HashSetType
                  local cref::DAE.ComponentRef
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inName, inCref, inMod, inVariability, inInnerOuter, inImpl, inInfo) begin
                  (_, _, _, _, _, _, _, SCode.CONST(__), _, _, _)  => begin
                    ()
                  end

                  (_, _, _, _, _, _, _, SCode.PARAM(__), _, _, _)  => begin
                    ()
                  end

                  (_, _, InnerOuter.TOP_INSTANCE(sm = sm) <| _, _, _, _, DAE.MOD(__), _, Absyn.OUTER(__), _, _)  => begin
                      cref = PrefixUtil.prefixToCref(inPrefix)
                      @match true = BaseHashSet.has(cref, sm)
                    ()
                  end

                  _  => begin
                        @match false = InnerOuter.modificationOnOuter(inCache, inEnv, inIH, inPrefix, inName, inCref, inMod, inInnerOuter, inImpl, inInfo)
                      ()
                  end
                end
              end
               #=  BTH: we check if the outer variable is in an instance that is
               =#
               #=       part of a Modelica state machine. In that case we have added
               =#
               #=       an equation modification, binding the inner variable to
               =#
               #=       the outer variable (instead of replacing the outer variable
               =#
               #=       by the inner variable). See InstVar.instVar(..).
               =#
               #=       Hence, such a modification should not throw an error.
               =#
               #=  adrpo: we cannot check this here as:
               =#
               #=         we might have modifications on inner that we copy here
               =#
               #=         Dymola doesn't report modifications on outer as error!
               =#
               #=         instead we check here if the modification is not the same
               =#
               #=         as the one on inner
               =#
        end

         #= Checks that a function variable is valid. =#
        function checkFunctionVar(inName::String, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inInfo::SourceInfo)
              _ = begin
                @match (inName, inAttributes, inPrefixes, inInfo) begin
                  (_, SCode.ATTR(direction = Absyn.BIDIR(__)), SCode.PREFIXES(visibility = SCode.PUBLIC(__)), _)  => begin
                      Error.addSourceMessage(Error.NON_FORMAL_PUBLIC_FUNCTION_VAR, list(inName), inInfo)
                    ()
                  end

                  (_, SCode.ATTR(direction = Absyn.BIDIR(__)), SCode.PREFIXES(visibility = SCode.PROTECTED(__)), _)  => begin
                    ()
                  end

                  (_, SCode.ATTR(__), SCode.PREFIXES(visibility = SCode.PROTECTED(__)), _)  => begin
                      Error.addSourceMessage(Error.PROTECTED_FORMAL_FUNCTION_VAR, list(inName), inInfo)
                    fail()
                  end

                  _  => begin
                      ()
                  end
                end
              end
               #=  Public non-formal parameters are not allowed, but since they're used in
               =#
               #=  the MSL we just issue a warning for now.
               =#
               #=  Protected non-formal parameters are ok.
               =#
               #=  Protected formal parameters are not allowed.
               =#
               #=  Everything else, i.e. public formal parameters, are ok.
               =#
        end

        function checkFunctionVarType(inType::DAE.Type, inState::ClassInf.SMNode, inVarName::String, inInfo::SourceInfo)
              _ = begin
                  local ty_str::String
                @matchcontinue (inType, inState, inVarName, inInfo) begin
                  (_, _, _, _)  => begin
                      @match true = Types.isValidFunctionVarType(inType)
                    ()
                  end

                  _  => begin
                        ty_str = Types.getTypeName(inType)
                        Error.addSourceMessage(Error.INVALID_FUNCTION_VAR_TYPE, list(ty_str, inVarName), inInfo)
                      fail()
                  end
                end
              end
        end

         #= Helper functin to instVar2. All array variables should be
         given array types, by lifting the type given a dimensionality.
         An exception are types extending builtin types, since they already
         have array types. This relation performs the lifting for alltypes
         except types extending basic types. =#
        function liftNonBasicTypes(tp::DAE.Type, dimt::DAE.Dimension) ::DAE.Type
              local outTp::DAE.Type

              outTp = begin
                  local ty::DAE.Type
                @matchcontinue (tp, dimt) begin
                  (DAE.T_SUBTYPE_BASIC(complexType = ty), _)  => begin
                      @match false = listEmpty(Types.getDimensions(ty))
                    tp
                  end

                  _  => begin
                      Types.liftArray(tp, dimt)
                  end
                end
              end
          outTp
        end

         #= If the binding expression has higher variability that the component, generates an error.
        Helper to makeVariableBinding. Author -- alleb =#
        function checkHigherVariability(compConst::DAE.Const, bindConst::DAE.Const, pre::Prefix.PrefixType, name::String, binding::DAE.Exp, info::SourceInfo)
              _ = begin
                  local c::DAE.Const
                  local c1::DAE.Const
                  local n::Ident
                  local sc::String
                  local sc1::String
                  local se::String
                  local sn::String
                  local e::DAE.Exp
                @matchcontinue (compConst, bindConst, pre, name, binding, info) begin
                  (c, c1, _, _, _, _)  => begin
                      equality(c, c1)
                    ()
                  end

                  (DAE.C_PARAM(__), DAE.C_UNKNOWN(__), _, _, _, _)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                    ()
                  end

                  (c, c1, _, n, e, _)  => begin
                      sn = PrefixUtil.printPrefixStr2(pre) + n
                      sc = DAEUtil.constStr(c)
                      sc1 = DAEUtil.constStr(c1)
                      se = ExpressionDump.printExpStr(e)
                      Error.addSourceMessage(Error.HIGHER_VARIABILITY_BINDING, list(sn, sc, se, sc1), info)
                    fail()
                  end
                end
              end
               #=  When doing checkModel we might have parameters with variable bindings,
               =#
               #=  for example when the binding depends on the dimensions on an array with
               =#
               #=  unknown dimensions.
               =#
               #=  Since c1 is generated by Types.matchProp, it can not be lower that c, so no need to check that it is higher
               =#
        end

         #= Creates an array type from the element type
          given as argument and a list of dimensional sizes. =#
        function makeArrayType(inDimensionLst::DAE.Dimensions, inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                  local ty_1::DAE.Type
                  local i::ModelicaInteger
                  local xs::DAE.Dimensions
                  local tty::DAE.Type
                  local dim::DAE.Dimension
                @matchcontinue (inDimensionLst, inType) begin
                  ( nil(), ty)  => begin
                    ty
                  end

                  (dim <| xs, tty)  => begin
                      ty_1 = makeArrayType(xs, tty)
                    DAE.T_ARRAY(ty_1, list(dim))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstUtil.makeArrayType failed\\n")
                      fail()
                  end
                end
              end
          outType
        end

         #= Retrieves the dimensions of a usertype and the innermost class type to instantiate,
          and also any modifications from the base classes of the usertype.
          The builtin types have no dimension, whereas a user defined type might
          have dimensions. For instance, type Point = Real[3];
          has one dimension of size 3 and the class to instantiate is Real =#
        function getUsertypeDimensions(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inClass::SCode.Element, inInstDims::List{<:List{<:DAE.Dimension}}, inBoolean::Bool) ::Tuple{FCore.Cache, DAE.Dimensions, SCode.Element, DAE.Mod}
              local outMods::DAE.Mod #= modifications from base classes =#
              local classToInstantiate::SCode.Element
              local outDimensionLst::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensionLst, classToInstantiate, outMods) = begin
                  local cl::SCode.Element
                  local cenv::FCore.Graph
                  local env::FCore.Graph
                  local owncref::Absyn.ComponentRef
                  local ad_1::List{Absyn.Subscript}
                  local mod_1::DAE.Mod
                  local type_mods::DAE.Mod
                  local eq::Option{DAE.EqMod}
                  local dim1::DAE.Dimensions
                  local dim2::DAE.Dimensions
                  local res::DAE.Dimensions
                  local pre::Prefix.PrefixType
                  local id::String
                  local cn::Absyn.Path
                  local ad::Option{List{Absyn.Subscript}}
                  local mod::SCode.Mod
                  local dims::InstDims
                  local impl::Bool
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local info::SourceInfo
                  local els::List{SCode.Element}
                  local path::SCode.Path
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inClass, inInstDims, inBoolean) begin
                  (cache, _, _, _, cl && SCode.CLASS(name = id), _, _) where (id == "Real" || id == "Integer" || id == "String" || id == "Boolean")  => begin
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (cache, _, _, _, cl && SCode.CLASS(name = "Clock"), _, _)  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (cache, _, _, _, cl && SCode.CLASS(restriction = SCode.R_RECORD(_), classDef = SCode.PARTS(__)), _, _)  => begin
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (cache, env, _, pre, cl && SCode.CLASS(name = id, info = info, classDef = SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(path = Absyn.IDENT(__), arrayDim = ad))), dims, impl)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      owncref = Absyn.CREF_IDENT(id, nil)
                      ad_1 = getOptionArraydim(ad)
                      (cache, dim1) = elabArraydim(cache, env, owncref, Absyn.IDENT("Integer"), ad_1, NONE(), impl, true, false, pre, info, dims)
                    (cache, dim1, cl, DAE.NOMOD())
                  end

                  (cache, _, _, _, cl && SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)), partialPrefix = SCode.PARTIAL(__)), _, _)  => begin
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (_, _, _, _, SCode.CLASS(name = id, info = info, restriction = SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(_)), partialPrefix = SCode.NOT_PARTIAL(__)), _, _)  => begin
                      Error.addSourceMessage(Error.META_FUNCTION_TYPE_NO_PARTIAL_PREFIX, list(id), info)
                    fail()
                  end

                  (cache, _, _, _, cl && SCode.CLASS(restriction = SCode.R_UNIONTYPE(__)), _, _)  => begin
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (cache, env, ih, pre, SCode.CLASS(name = id, restriction = SCode.R_TYPE(__), info = info, classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn, arrayDim = ad), modifications = mod)), dims, impl)  => begin
                      (cache, cl, cenv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      owncref = Absyn.CREF_IDENT(id, nil)
                      ad_1 = getOptionArraydim(ad)
                      env = addEnumerationLiteralsToEnv(env, cl)
                      (cache, mod_1) = Mod.elabMod(cache, env, ih, pre, mod, impl, Mod.DERIVED(cn), info)
                      eq = Mod.modEquation(mod_1)
                      (cache, dim1, cl, type_mods) = getUsertypeDimensions(cache, cenv, ih, pre, cl, dims, impl)
                      (cache, dim2) = elabArraydim(cache, env, owncref, cn, ad_1, eq, impl, true, false, pre, info, dims)
                      type_mods = Mod.addEachIfNeeded(type_mods, dim2)
                      type_mods = Mod.merge(mod_1, type_mods)
                      res = listAppend(dim2, dim1)
                    (cache, res, cl, type_mods)
                  end

                  (cache, env, ih, pre, SCode.CLASS(classDef = SCode.PARTS(elementLst = els, normalEquationLst =  nil(), initialEquationLst =  nil(), normalAlgorithmLst =  nil(), initialAlgorithmLst =  nil())), _, impl)  => begin
                      @match (_, _, list(SCode.EXTENDS(path, _, mod, _, info)), nil) = splitElts(els)
                      (cache, mod_1) = Mod.elabModForBasicType(cache, env, ih, pre, mod, impl, Mod.EXTENDS(path), info)
                      (cache, cl, _) = Lookup.lookupClass(cache, env, path)
                      (cache, res, cl, type_mods) = getUsertypeDimensions(cache, env, ih, pre, cl, nil, impl)
                      type_mods = Mod.merge(mod_1, type_mods)
                    (cache, res, cl, type_mods)
                  end

                  (cache, _, _, _, cl && SCode.CLASS(__), _, _)  => begin
                    (cache, nil, cl, DAE.NOMOD())
                  end

                  (_, _, _, _, SCode.CLASS(__), _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      id = SCodeDump.unparseElementStr(inClass, SCodeDump.defaultOptions)
                      Debug.traceln("InstUtil.getUsertypeDimensions failed: " + id)
                    fail()
                  end
                end
              end
               #=  BTH
               =#
               #= ------------------------
               =#
               #=  MetaModelica extension
               =#
               #=  Absyn.IDENT(\"Integer\") used as a dummie
               =#
               #=  Partial function definitions with no output - stefan
               =#
               #=  MetaModelica Uniontype. Added 2009-05-11 sjoelund
               =#
               #= /*----------------------*/ =#
               #=  Derived classes with restriction type, e.g. type Point = Real[3];
               =#
               #=  do not add each to mod_1, it should have it already!
               =#
               #=  mod_1 = Mod.addEachIfNeeded(mod_1, dim2);
               =#
               #=  extended classes type Y = Real[3]; class X extends Y;
               =#
               #=  ONLY ONE extends!
               =#
               #=  type_mods = Mod.addEachIfNeeded(type_mods, res);
               =#
          (outCache, outDimensionLst, classToInstantiate, outMods #= modifications from base classes =#)
        end

         #= If the input SCode.Element is an enumeration, this function adds all of it's
           enumeration literals to the environment. This is used in getUsertypeDimensions
           so that the modifiers on an enumeration can be elaborated when the literals
           are used, for example like this:
             type enum1 = enumeration(val1, val2);
             type enum2 = enum1(start = val1);  val1 needs to be in the environment here. =#
        function addEnumerationLiteralsToEnv(inEnv::FCore.Graph, inClass::SCode.Element) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                  local enums::List{SCode.Element}
                  local env::FCore.Graph
                @matchcontinue (inEnv, inClass) begin
                  (_, SCode.CLASS(restriction = SCode.R_ENUMERATION(__), classDef = SCode.PARTS(elementLst = enums)))  => begin
                      env = ListUtil.fold(enums, addEnumerationLiteralToEnv, inEnv)
                    env
                  end

                  _  => begin
                      inEnv
                  end
                end
              end
               #=  Not an enumeration, no need to do anything.
               =#
          outEnv
        end

        function addEnumerationLiteralToEnv(inEnum::SCode.Element, inEnv::FCore.Graph) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                  local lit::SCode.Ident
                  local env::FCore.Graph
                @matchcontinue (inEnum, inEnv) begin
                  (SCode.COMPONENT(name = lit), _)  => begin
                      env = FGraph.mkComponentNode(inEnv, DAE.TYPES_VAR(lit, DAE.dummyAttrVar, DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE()), inEnum, DAE.NOMOD(), FCore.VAR_UNTYPED(), FGraph.empty())
                    env
                  end

                  _  => begin
                        print("InstUtil.addEnumerationLiteralToEnv: Unknown enumeration type!\\n")
                      fail()
                  end
                end
              end
          outEnv
        end

        function updateClassInfState(inCache::FCore.Cache, inNewEnv::FCore.Graph, inOldEnv::FCore.Graph, inCIState::ClassInf.SMNode) ::ClassInf.SMNode
              local outCIState::ClassInf.SMNode

              outCIState = begin
                  local ci_state::ClassInf.SMNode
                  local rest::FCore.Graph
                  local id::Absyn.Ident
                  local cls::SCode.Element
                   #=  top env, return the same ci_state
                   =#
                @matchcontinue (inCache, inNewEnv, inOldEnv, inCIState) begin
                  (_, _, _, ci_state)  => begin
                      @match true = FGraph.isTopScope(inNewEnv)
                    ci_state
                  end

                  (_, _, _, ci_state)  => begin
                      @match true = stringEq(FGraph.getGraphNameStr(inNewEnv), FGraph.getGraphNameStr(inOldEnv))
                    ci_state
                  end

                  (_, _, _, _)  => begin
                      @match false = FGraph.isTopScope(inNewEnv)
                      id = FNode.refName(FGraph.lastScopeRef(inNewEnv))
                      (rest, _) = FGraph.stripLastScopeRef(inNewEnv)
                      (_, cls, _) = Lookup.lookupClassIdent(inCache, rest, id)
                      ci_state = ClassInf.start(SCodeUtil.getClassRestriction(cls), FGraph.getGraphName(inNewEnv))
                    ci_state
                  end

                  _  => begin
                      inCIState
                  end
                end
              end
               #=  same environment, return the same ci_state
               =#
               #=  not the same environment, try to
               =#
               #=  make a ci state from the new env
               =#
               #=  not top scope
               =#
          outCIState
        end

         #= function: instDAE.Dimension
          instantiates one dimension expression, See also instDimExpLst. =#
        function evalEnumAndBoolDim(inDimension::DAE.Dimension) ::DAE.Dimension
              local outDimension::DAE.Dimension

              outDimension = begin
                  local i::ModelicaInteger
                   #=  case (DAE.DIM_ENUM(size = i)) then DAE.DIM_INTEGER(i);
                   =#
                @match inDimension begin
                  DAE.DIM_BOOLEAN(__)  => begin
                    DAE.DIM_INTEGER(2)
                  end

                  _  => begin
                      inDimension
                  end
                end
              end
          outDimension
        end

         #= /*TODO: mahge: Remove me*/ =#

         #= the vesrion of instDimExp for the case of non-expanded arrays =#
        function instDimExpNonSplit(inDimension::DAE.Dimension, inBoolean::Bool) ::DAE.Subscript
              local outSubscript::DAE.Subscript

              outSubscript = begin
                  local e::DAE.Exp
                  local i::ModelicaInteger
                @match (inDimension, inBoolean) begin
                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    DAE.WHOLEDIM()
                  end

                  (DAE.DIM_INTEGER(integer = i), _)  => begin
                    DAE.WHOLE_NONEXP(DAE.ICONST(i))
                  end

                  (DAE.DIM_ENUM(size = i), _)  => begin
                    DAE.WHOLE_NONEXP(DAE.ICONST(i))
                  end

                  (DAE.DIM_BOOLEAN(__), _)  => begin
                    DAE.WHOLE_NONEXP(DAE.ICONST(2))
                  end

                  (DAE.DIM_EXP(exp = e), _)  => begin
                    DAE.WHOLE_NONEXP(e)
                  end
                end
              end
               #= case (DAE.DIM_EXP(exp = e as DAE.RANGE(exp = _)), _) then DAE.INDEX(e);
               =#
          outSubscript
        end

         #= Tries to determine the size of a WHOLEDIM dimension by looking at a variables
          modifier. =#
        function instWholeDimFromMod(dimensionExp::DAE.Dimension, modifier::DAE.Mod, inVarName::String, inInfo::SourceInfo) ::DAE.Dimension
              local outDimension::DAE.Dimension

              outDimension = begin
                  local d::DAE.Dimension
                  local sub::DAE.Subscript
                  local exp::DAE.Exp
                  local exp_str::String
                @matchcontinue (dimensionExp, modifier, inVarName, inInfo) begin
                  (DAE.DIM_UNKNOWN(__), DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = exp))), _, _)  => begin
                      @match _cons(d, _) = Expression.expDimensions(exp)
                    d
                  end

                  (DAE.DIM_UNKNOWN(__), DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = exp))), _, _)  => begin
                      exp_str = ExpressionDump.printExpStr(exp)
                      Error.addSourceMessage(Error.FAILURE_TO_DEDUCE_DIMS_FROM_MOD, list(inVarName, exp_str), inInfo)
                    fail()
                  end

                  (DAE.DIM_UNKNOWN(__), _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- InstUtil.instWholeDimFromMod failed\\n")
                    fail()
                  end
                end
              end
               #=  TODO: We should print an error if we fail to deduce the dimensions from
               =#
               #=  the modifier, but we do not yet handle some cases (such as
               =#
               #=  Modelica.Blocks.Sources.KinematicPTP), so just print a warning for now.
               =#
          outDimension
        end

         #= Propagates attributes (flow, stream, discrete, parameter, constant, input,
          output) to elements in a structured component. =#
        function propagateAttributes(inDae::DAE.DAElist, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inInfo::SourceInfo) ::DAE.DAElist
              local outDae::DAE.DAElist

              local elts::List{DAE.Element}

              @match DAE.DAE(elementLst = elts) = inDae
              elts = ListUtil.map3(elts, propagateAllAttributes, inAttributes, inPrefixes, inInfo)
              outDae = DAE.DAE(elts)
          outDae
        end

         #= Helper function to propagateAttributes. Propagates all attributes if needed. =#
        function propagateAllAttributes(inElement::DAE.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inInfo::SourceInfo) ::DAE.Element
              local outElement::DAE.Element

              outElement = begin
                  local cr::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local vdir::DAE.VarDirection
                  local vprl::DAE.VarParallelism
                  local vvis::DAE.VarVisibility
                  local ty::DAE.Type
                  local binding::Option{DAE.Exp}
                  local dims::DAE.InstDims
                  local ct1::SCode.ConnectorType
                  local ct2::DAE.ConnectorType
                  local source::DAE.ElementSource
                  local var_attrs::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local sprl::SCode.Parallelism
                  local var::SCode.Variability
                  local dir::Absyn.Direction
                  local fp::SCode.Final
                  local ident::SCode.Ident
                  local el::List{DAE.Element}
                  local vis::SCode.Visibility
                   #=  Just return the element if nothing needs to be changed.
                   =#
                @match (inElement, inAttributes, inPrefixes, inInfo) begin
                  (_, SCode.ATTR(connectorType = SCode.POTENTIAL(__), parallelism = SCode.NON_PARALLEL(__), variability = SCode.VAR(__), direction = Absyn.BIDIR(__)), SCode.PREFIXES(visibility = SCode.PUBLIC(__), finalPrefix = SCode.NOT_FINAL(__), innerOuter = Absyn.NOT_INNER_OUTER(__)), _)  => begin
                    inElement
                  end

                  (DAE.VAR(componentRef = cr, kind = vk, direction = vdir, parallelism = vprl, protection = vvis, ty = ty, binding = binding, dims = dims, connectorType = ct2, source = source, variableAttributesOption = var_attrs, comment = cmt, innerOuter = io2), SCode.ATTR(connectorType = ct1, parallelism = sprl, variability = var, direction = dir), SCode.PREFIXES(visibility = vis, finalPrefix = fp, innerOuter = io1), _)  => begin
                      vdir = propagateDirection(vdir, dir, cr, inInfo)
                      vk = propagateVariability(vk, var)
                      vprl = propagateParallelism(vprl, sprl, cr, inInfo)
                      vvis = propagateVisibility(vvis, vis)
                      var_attrs = propagateFinal(var_attrs, fp)
                      io2 = propagateInnerOuter(io2, io1)
                      ct2 = propagateConnectorType(ct2, ct1, cr, inInfo)
                    DAE.VAR(cr, vk, vdir, vprl, vvis, ty, binding, dims, ct2, source, var_attrs, cmt, io2)
                  end

                  (DAE.COMP(ident = ident, dAElist = el, source = source, comment = cmt), _, _, _)  => begin
                      el = ListUtil.map3(el, propagateAllAttributes, inAttributes, inPrefixes, inInfo)
                    DAE.COMP(ident, el, source, cmt)
                  end

                  _  => begin
                      inElement
                  end
                end
              end
               #=  Normal variable.
               =#
               #=  Structured component.
               =#
               #=  Everything else.
               =#
          outElement
        end

         #= Helper function to propagateAttributes. Propagates the input/output
          attribute to variables of a structured component. =#
        function propagateDirection(inVarDirection::DAE.VarDirection, inDirection::Absyn.Direction, inCref::DAE.ComponentRef, inInfo::SourceInfo) ::DAE.VarDirection
              local outVarDirection::DAE.VarDirection

              outVarDirection = begin
                  local s1::String
                  local s2::String
                  local s3::String
                   #=  Component that is bidirectional does not change direction on subcomponents.
                   =#
                @match (inVarDirection, inDirection, inCref, inInfo) begin
                  (_, Absyn.BIDIR(__), _, _)  => begin
                    inVarDirection
                  end

                  (DAE.BIDIR(__), _, _, _)  => begin
                    absynDirToDaeDir(inDirection)
                  end

                  _  => begin
                        s1 = Dump.directionSymbol(inDirection)
                        s2 = ComponentReference.printComponentRefStr(inCref)
                        s3 = DAEDump.dumpDirectionStr(inVarDirection)
                        Error.addSourceMessage(Error.COMPONENT_INPUT_OUTPUT_MISMATCH, list(s1, s2, s3), inInfo)
                      fail()
                  end
                end
              end
               #=  Bidirectional variables are changed to input or output if component has
               =#
               #=  such prefix.
               =#
               #=  Error when component declared as input or output if the variable already
               =#
               #=  has such a prefix.
               =#
          outVarDirection
        end

         #= Helper function to propagateAttributes. Propagates the input/output
          attribute to variables of a structured component. =#
        function propagateParallelism(inVarParallelism::DAE.VarParallelism, inParallelism::SCode.Parallelism, inCref::DAE.ComponentRef, inInfo::SourceInfo) ::DAE.VarParallelism
              local outVarParallelism::DAE.VarParallelism

              outVarParallelism = begin
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local daeprl1::DAE.VarParallelism
                  local daeprl2::DAE.VarParallelism
                  local sprl::SCode.Parallelism
                   #=  Component that is non parallel does not change Parallelism on subcomponents.
                   =#
                @matchcontinue (inVarParallelism, inParallelism, inCref, inInfo) begin
                  (_, SCode.NON_PARALLEL(__), _, _)  => begin
                    inVarParallelism
                  end

                  (DAE.NON_PARALLEL(__), _, _, _)  => begin
                    DAEUtil.scodePrlToDaePrl(inParallelism)
                  end

                  (daeprl1, _, _, _)  => begin
                      daeprl2 = DAEUtil.scodePrlToDaePrl(inParallelism)
                      @match true = DAEUtil.daeParallelismEqual(daeprl1, daeprl2)
                    daeprl1
                  end

                  _  => begin
                        daeprl2 = DAEUtil.scodePrlToDaePrl(inParallelism)
                        s1 = DAEDump.dumpVarParallelismStr(daeprl2)
                        s2 = ComponentReference.printComponentRefStr(inCref)
                        s3 = DAEDump.dumpVarParallelismStr(inVarParallelism)
                        s4 = "\\n" + "- Component declared as '" + s1 + "' when having the variable '" + s2 + "' declared as '" + s3 + "' : Subcomponent parallelism modified to." + s1
                        Error.addSourceMessage(Error.PARMODELICA_WARNING, list(s4), inInfo)
                      daeprl2
                  end
                end
              end
               #=  non_parallel variables are changed to parlocal or parglobal
               =#
               #=  depending on the component
               =#
               #=  if the two parallelisms are equal then it is OK
               =#
               #=  Reaches here If the component is declared as parlocal or parglobal
               =#
               #=  and the subcomponent is declared as parglobal or parlocal, respectively.
               =#
               #=  Print a warning and override the subcomponent's parallelism.
               =#
          outVarParallelism
        end

         #= Helper function to propagateAttributes. Propagates the visibility (public or
           protected) attribute to variables of a structured component. =#
        function propagateVisibility(inVarVisibility::DAE.VarVisibility, inVisibility::SCode.Visibility) ::DAE.VarVisibility
              local outVarVisibility::DAE.VarVisibility

              outVarVisibility = begin
                @match (inVarVisibility, inVisibility) begin
                  (_, SCode.PROTECTED(__))  => begin
                    DAE.PROTECTED()
                  end

                  _  => begin
                      inVarVisibility
                  end
                end
              end
          outVarVisibility
        end

         #= Helper function to propagateAttributes. Propagates the variability (parameter
          or constant) attribute to variables of a structured component. =#
        function propagateVariability(inVarKind::DAE.VarKind, inVariability::SCode.Variability) ::DAE.VarKind
              local outVarKind::DAE.VarKind

              outVarKind = begin
                @match (inVarKind, inVariability) begin
                  (_, SCode.VAR(__))  => begin
                    inVarKind
                  end

                  (DAE.DISCRETE(__), _)  => begin
                    inVarKind
                  end

                  (_, SCode.DISCRETE(__))  => begin
                    DAE.DISCRETE()
                  end

                  (DAE.CONST(__), _)  => begin
                    inVarKind
                  end

                  (_, SCode.CONST(__))  => begin
                    DAE.CONST()
                  end

                  (DAE.PARAM(__), _)  => begin
                    inVarKind
                  end

                  (_, SCode.PARAM(__))  => begin
                    DAE.PARAM()
                  end

                  _  => begin
                      inVarKind
                  end
                end
              end
               #=  Component that is VAR does not change variability of subcomponents.
               =#
               #=  Most restrictive variability is preserved.
               =#
          outVarKind
        end

         #= Helper function to propagateAttributes. Propagates the final attribute to
          variables of a structured component. =#
        function propagateFinal(inVarAttributes::Option{<:DAE.VariableAttributes}, inFinal::SCode.Final) ::Option{DAE.VariableAttributes}
              local outVarAttributes::Option{DAE.VariableAttributes}

              outVarAttributes = begin
                @match (inVarAttributes, inFinal) begin
                  (_, SCode.FINAL(__))  => begin
                    DAEUtil.setFinalAttr(inVarAttributes, SCodeUtil.finalBool(inFinal))
                  end

                  _  => begin
                      inVarAttributes
                  end
                end
              end
          outVarAttributes
        end

         #= Helper function to propagateAttributes. Propagates the inner/outer attribute
          to variables of a structured component. =#
        function propagateInnerOuter(inVarInnerOuter::Absyn.InnerOuter, inInnerOuter::Absyn.InnerOuter) ::Absyn.InnerOuter
              local outVarInnerOuter::Absyn.InnerOuter

              outVarInnerOuter = begin
                @match (inVarInnerOuter, inInnerOuter) begin
                  (_, Absyn.NOT_INNER_OUTER(__))  => begin
                    inVarInnerOuter
                  end

                  (Absyn.NOT_INNER_OUTER(__), _)  => begin
                    inInnerOuter
                  end

                  _  => begin
                      inVarInnerOuter
                  end
                end
              end
               #=  Component that is unspecified does not change inner/outer on subcomponents.
               =#
               #=  Unspecified variables are changed to the same inner/outer prefix as the
               =#
               #=  component.
               =#
               #=  If variable already have inner/outer, keep it.
               =#
          outVarInnerOuter
        end

         #= Helper function to propagateAttributes. Propagates the flow/stream attribute
           to variables of a structured component. =#
        function propagateConnectorType(inVarConnectorType::DAE.ConnectorType, inConnectorType::SCode.ConnectorType, inCref::DAE.ComponentRef, inInfo::SourceInfo) ::DAE.ConnectorType
              local outVarConnectorType::DAE.ConnectorType

              outVarConnectorType = begin
                  local s1::String
                  local s2::String
                  local s3::String
                @match (inVarConnectorType, inConnectorType, inCref, inInfo) begin
                  (_, SCode.POTENTIAL(__), _, _)  => begin
                    inVarConnectorType
                  end

                  (DAE.POTENTIAL(__), SCode.FLOW(__), _, _)  => begin
                    DAE.FLOW()
                  end

                  (DAE.NON_CONNECTOR(__), SCode.FLOW(__), _, _)  => begin
                    DAE.FLOW()
                  end

                  (DAE.POTENTIAL(__), SCode.STREAM(__), _, _)  => begin
                    DAE.STREAM(NONE())
                  end

                  (DAE.NON_CONNECTOR(__), SCode.STREAM(__), _, _)  => begin
                    DAE.STREAM(NONE())
                  end

                  _  => begin
                        s1 = SCodeDump.connectorTypeStr(inConnectorType)
                        s2 = ComponentReference.printComponentRefStr(inCref)
                        s3 = DAEDump.dumpConnectorType(inVarConnectorType)
                        Error.addSourceMessage(Error.INVALID_TYPE_PREFIX, list(s1, "variable", s2, s3), inInfo)
                      fail()
                  end
                end
              end
               #=  Error if the component tries to overwrite the prefix of a subcomponent.
               =#
          outVarConnectorType
        end

         #= Translates Absyn.Direction to DAE.VarDirection.
          Needed so that input, output is transferred to DAE. =#
        function absynDirToDaeDir(inDirection::Absyn.Direction) ::DAE.VarDirection
              local outVarDirection::DAE.VarDirection

              outVarDirection = begin
                @match inDirection begin
                  Absyn.INPUT(__)  => begin
                    DAE.INPUT()
                  end

                  Absyn.OUTPUT(__)  => begin
                    DAE.OUTPUT()
                  end

                  Absyn.BIDIR(__)  => begin
                    DAE.BIDIR()
                  end
                end
              end
          outVarDirection
        end

         #= Returns true if attributes contain PARAM =#
        function attrIsParam(inAttributes::SCode.Attributes) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inAttributes begin
                  SCode.ATTR(variability = SCode.PARAM(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= author: PA
          Lookup uninstantiated component in env, elaborate its modifiers to
          find arraydimensions and return as DAE.Dimension list.
          Used when components have submodifiers (on e.g. attributes) using
          size to find dimensions of component. =#
        function elabComponentArraydimFromEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensionLst::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensionLst) = begin
                  local id::String
                  local ad::List{Absyn.Subscript}
                  local m::SCode.Mod
                  local m_1::SCode.Mod
                  local cmod::DAE.Mod
                  local cmod_1::DAE.Mod
                  local m_2::DAE.Mod
                  local mod_2::DAE.Mod
                  local eq::DAE.EqMod
                  local dims::DAE.Dimensions
                  local env::FCore.Graph
                  local cref::DAE.ComponentRef
                  local cache::FCore.Cache
                  local subs::List{DAE.Subscript}
                @matchcontinue (inCache, inEnv, inComponentRef, info) begin
                  (cache, env, DAE.CREF_IDENT(ident = id), _)  => begin
                      @match (cache, _, SCode.COMPONENT(modifications = m), cmod, _, _) = Lookup.lookupIdent(cache, env, id)
                      cmod_1 = Mod.stripSubmod(cmod)
                      m_1 = SCodeUtil.stripSubmod(m)
                      (cache, m_2) = Mod.elabMod(cache, env, InnerOuter.emptyInstHierarchy, Prefix.NOPRE(), m_1, false, Mod.COMPONENT(id), info)
                      mod_2 = Mod.merge(cmod_1, m_2)
                      @match SOME(eq) = Mod.modEquation(mod_2)
                      (cache, dims) = elabComponentArraydimFromEnv2(cache, eq, env)
                    (cache, dims)
                  end

                  (cache, env, DAE.CREF_IDENT(ident = id), _)  => begin
                      @match (cache, _, SCode.COMPONENT(attributes = SCode.ATTR(arrayDims = ad)), _, _, _) = Lookup.lookupIdent(cache, env, id)
                      (cache, subs) = Static.elabSubscripts(cache, env, ad, true, Prefix.NOPRE(), info)
                      dims = Expression.subscriptDimensions(subs)
                    (cache, dims)
                  end

                  (_, _, cref, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- InstUtil.elabComponentArraydimFromEnv failed: " + ComponentReference.printComponentRefStr(cref))
                    fail()
                  end
                end
              end
          (outCache, outDimensionLst)
        end

         #= author: PA
          Helper function to elabComponentArraydimFromEnv.
          This function is similar to elabArraydim, but it will only
          investigate binding (DAE.EqMod) and not the component declaration. =#
        function elabComponentArraydimFromEnv2(inCache::FCore.Cache, inEqMod::DAE.EqMod, inEnv::FCore.Graph) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensionLst::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensionLst) = begin
                  local lst::List{ModelicaInteger}
                  local lst_1::DAE.Dimensions
                  local e::DAE.Exp
                  local t::DAE.Type
                  local env::FCore.Graph
                  local cache::FCore.Cache
                @match (inCache, inEqMod, inEnv) begin
                  (cache, DAE.TYPED(properties = DAE.PROP(type_ = t)), _)  => begin
                      lst = Types.getDimensionSizes(t)
                      lst_1 = ListUtil.map(lst, Expression.intDimension)
                    (cache, lst_1)
                  end
                end
              end
          (outCache, outDimensionLst)
        end

         #= Same functionality as elabArraydim, but takes an optional arraydim.
          In case of NONE(), empty DAE.Dimension list is returned. =#
        function elabArraydimOpt(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, path::Absyn.Path #= Class of declaration =#, inAbsynArrayDimOption::Option{<:Absyn.ArrayDim}, inTypesEqModOption::Option{<:DAE.EqMod}, inBoolean::Bool, performVectorization::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo, inInstDims::List{<:List{<:DAE.Dimension}}) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensionLst::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensionLst) = begin
                  local res::DAE.Dimensions
                  local env::FCore.Graph
                  local owncref::Absyn.ComponentRef
                  local ad::List{Absyn.Subscript}
                  local eq::Option{DAE.EqMod}
                  local impl::Bool
                  local cache::FCore.Cache
                  local doVect::Bool
                  local pre::Prefix.PrefixType
                  local inst_dims::InstDims
                @match (inCache, inEnv, inComponentRef, path, inAbsynArrayDimOption, inTypesEqModOption, inBoolean, performVectorization, inPrefix, info, inInstDims) begin
                  (cache, env, owncref, _, SOME(ad), eq, impl, doVect, pre, _, inst_dims)  => begin
                      (cache, res) = elabArraydim(cache, env, owncref, path, ad, eq, impl, doVect, false, pre, info, inst_dims)
                    (cache, res)
                  end

                  (cache, _, _, _, NONE(), _, _, _, _, _, _)  => begin
                    (cache, nil)
                  end
                end
              end
          (outCache, outDimensionLst)
        end

         #= This functions examines both an `Absyn.ArrayDim\\' and an `DAE.EqMod
          option\\' argument to find out the dimensions af a component.  If
          no equation modifications is given, only the declared dimension is
          used.

          When the size of a dimension in the type is undefined, the
          corresponding size in the type of the modification is used.

          All this is accomplished by examining the two arguments separately
          and then using `complete_arraydime\\' or `compatible_arraydim\\' to
          check that that the dimension sizes are compatible and complete. =#
        function elabArraydim(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::Absyn.ComponentRef, path::Absyn.Path #= Class of declaration =#, inArrayDim::Absyn.ArrayDim, inTypesEqModOption::Option{<:DAE.EqMod}, inBoolean::Bool, performVectorization::Bool, isFunctionInput::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo, inInstDims::List{<:List{<:DAE.Dimension}}) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDimensionLst::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDimensionLst) = begin
                  local dim::DAE.Dimensions
                  local dim1::DAE.Dimensions
                  local dim2::DAE.Dimensions
                  local dim3::DAE.Dimensions
                  local env::FCore.Graph
                  local cref::Absyn.ComponentRef
                  local ad::List{Absyn.Subscript}
                  local impl::Bool
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local t::DAE.Type
                  local e_str::String
                  local t_str::String
                  local dim_str::String
                  local cache::FCore.Cache
                  local doVect::Bool
                  local prop::DAE.Properties
                  local pre::Prefix.PrefixType
                  local aexp::Absyn.Exp
                  local eq::Option{DAE.EqMod}
                  local inst_dims::InstDims
                  local info::SourceInfo
                  local info2::SourceInfo
                   #=  The size of function input arguments should not be set here, since they
                   =#
                   #=  may vary depending on the inputs. So we ignore any modifications on input
                   =#
                   #=  variables here.
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, path, inArrayDim, inTypesEqModOption, inBoolean, performVectorization, isFunctionInput, inPrefix, inInfo, inInstDims) begin
                  (cache, env, cref, _, ad, _, _, doVect, true, pre, info, _)  => begin
                      (cache, dim) = Static.elabArrayDims(cache, env, cref, ad, true, doVect, pre, info)
                    (cache, dim)
                  end

                  (cache, _, _, _,  nil(), _, _, _, _, _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, cref, _, ad, NONE(), impl, doVect, _, pre, info, _)  => begin
                      (cache, dim) = Static.elabArrayDims(cache, env, cref, ad, impl, doVect, pre, info)
                    (cache, dim)
                  end

                  (cache, env, cref, _, ad, SOME(DAE.TYPED(e, _, prop, _)), impl, doVect, _, pre, info, inst_dims)  => begin
                      t = Types.getPropType(prop)
                      (cache, dim1) = Static.elabArrayDims(cache, env, cref, ad, impl, doVect, pre, info)
                      dim2 = elabArraydimType(t, ad, e, path, pre, cref, info, inst_dims)
                      dim3 = ListUtil.threadMap(dim1, dim2, compatibleArraydim)
                    (cache, dim3)
                  end

                  (cache, env, cref, _, ad, SOME(DAE.UNTYPED(aexp)), impl, doVect, _, pre, info, inst_dims)  => begin
                      (cache, e_1, prop) = Static.elabExp(cache, env, aexp, impl, doVect, pre, info)
                      (cache, e_1, prop) = Ceval.cevalIfConstant(cache, env, e_1, prop, impl, info)
                      t = Types.getPropType(prop)
                      (cache, dim1) = Static.elabArrayDims(cache, env, cref, ad, impl, doVect, pre, info)
                      dim2 = elabArraydimType(t, ad, e_1, path, pre, cref, info, inst_dims)
                      dim3 = ListUtil.threadMap(dim1, dim2, compatibleArraydim)
                    (cache, dim3)
                  end

                  (cache, env, cref, _, ad, SOME(DAE.TYPED(e, _, DAE.PROP(t, _), _, info2)), impl, doVect, _, pre, info, inst_dims)  => begin
                      @match false = Flags.getConfigBool(Flags.CHECK_MODEL)
                      (_, dim1) = Static.elabArrayDims(cache, env, cref, ad, impl, doVect, pre, info)
                      dim2 = elabArraydimType(t, ad, e, path, pre, cref, info, inst_dims)
                      @shouldFail _ = ListUtil.threadMap(dim1, dim2, compatibleArraydim)
                      e_str = ExpressionDump.printExpStr(e)
                      t_str = Types.unparseType(t)
                      dim_str = printDimStr(dim1)
                      Error.addMultiSourceMessage(Error.ARRAY_DIMENSION_MISMATCH, list(e_str, t_str, dim_str), _cons(info2, _cons(info, nil)))
                    fail()
                  end

                  (_, _, cref, _, ad, eq, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- InstUtil.elabArraydim failed on: \\n\\tcref:")
                      Debug.trace(AbsynUtil.pathString(path) + " " + Dump.printComponentRefStr(cref))
                      Debug.traceln(Dump.printArraydimStr(ad) + " = " + Types.unparseOptionEqMod(eq))
                    fail()
                  end
                end
              end
               #= /* impl */ =#
               #= /* Untyped expressions must be elaborated. */ =#
               #= Debug.traceln(\"TYPED: \" + ExpressionDump.printExpStr(e) + \" s: \" + FGraph.printGraphPathStr(env));
               =#
               #= Debug.traceln(\"UNTYPED\");
               =#
               #=  adrpo: do not display error when running checkModel
               =#
               #=         TODO! FIXME! check if this doesn't actually get rid of useful error messages
               =#
               #=  print some failures
               =#
               #=  only display when the failtrace flag is on
               =#
          (outCache, outDimensionLst)
        end

         #= This function prints array dimensions.
          The code is not included in the report. =#
        function printDimStr(inDimensionLst::DAE.Dimensions) ::String
              local outString::String

              local dim_strings::List{String}

              dim_strings = ListUtil.map(inDimensionLst, ExpressionDump.dimensionString)
              outString = stringDelimitList(dim_strings, ",")
          outString
        end

         #= Given two, possibly incomplete, array dimension size specifications, this
          function checks whether they are compatible. Being compatible means that they
          have the same number of dimensions, and for every dimension at least one of
          the lists specifies it's size. If both lists specify a dimension size, they
          have to specify the same size. =#
        function compatibleArraydim(inDimension1::DAE.Dimension, inDimension2::DAE.Dimension) ::DAE.Dimension
              local outDimension::DAE.Dimension

              outDimension = begin
                  local x::DAE.Dimension
                  local y::DAE.Dimension
                @match (inDimension1, inDimension2) begin
                  (DAE.DIM_UNKNOWN(__), DAE.DIM_UNKNOWN(__))  => begin
                    DAE.DIM_UNKNOWN()
                  end

                  (_, DAE.DIM_UNKNOWN(__))  => begin
                    inDimension1
                  end

                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    inDimension2
                  end

                  (_, DAE.DIM_EXP(__))  => begin
                    inDimension1
                  end

                  (DAE.DIM_EXP(__), _)  => begin
                    inDimension2
                  end

                  (_, _)  => begin
                      @match true = intEq(Expression.dimensionSize(inDimension1), Expression.dimensionSize(inDimension2))
                    inDimension1
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstUtil.compatibleArraydim failed\\n")
                      fail()
                  end
                end
              end
          outDimension
        end

         #= Find out the dimension sizes of a type. The second argument is used to know
           how many dimensions should be extracted from the type. =#
        function elabArraydimType(inType::DAE.Type, inArrayDim::Absyn.ArrayDim, inExp::DAE.Exp #= User for error messages. =#, inPath::Absyn.Path #= Class of declaration, used for error messages. =#, inPrefix::Prefix.PrefixType, inCref::Absyn.ComponentRef, inInfo::SourceInfo, inInstDims::List{<:List{<:DAE.Dimension}}) ::DAE.Dimensions
              local outDimensions::DAE.Dimensions

              local flat_id::List{DAE.Dimension}
              local ad_str::String
              local ty_str::String
              local exp_str::String
              local name_str::String

              flat_id = if Config.splitArrays()
                    nil
                  else
                    ListUtil.flatten(inInstDims)
                  end
              try
                @match true = Types.numberOfDimensions(inType) >= listLength(inArrayDim) + listLength(flat_id)
                outDimensions = elabArraydimType2(inType, inArrayDim, flat_id)
              catch
                ad_str = AbsynUtil.pathString(inPath) + Dump.printArraydimStr(inArrayDim)
                ty_str = Types.unparseTypeNoAttr(inType)
                exp_str = ExpressionDump.printExpStr(inExp)
                name_str = PrefixUtil.printPrefixStrIgnoreNoPre(inPrefix) + AbsynUtil.printComponentRefStr(inCref)
                Error.addSourceMessageAndFail(Error.MODIFIER_DECLARATION_TYPE_MISMATCH_ERROR, list(name_str, ad_str, exp_str, ty_str), inInfo)
              end
          outDimensions
        end

         #= Help function to elabArraydimType. =#
        function elabArraydimType2(inType::DAE.Type, inArrayDim::Absyn.ArrayDim, inDims::List{<:DAE.Dimension}) ::DAE.Dimensions
              local outDimensions::DAE.Dimensions

              outDimensions = begin
                  local d::DAE.Dimension
                  local dim::DAE.Dimension
                  local rest_dims::List{DAE.Dimension}
                  local t::DAE.Type
                @matchcontinue (inType, inArrayDim, inDims) begin
                  (DAE.T_ARRAY(dims = d <|  nil(), ty = t), _, dim <| rest_dims)  => begin
                      compatibleArraydim(d, dim)
                    elabArraydimType2(t, inArrayDim, rest_dims)
                  end

                  (DAE.T_ARRAY(dims = d <|  nil(), ty = t), _,  nil())  => begin
                    _cons(d, elabArraydimType2(t, listRest(inArrayDim), nil))
                  end

                  (_,  nil(),  nil())  => begin
                    nil
                  end

                  (_, _ <| _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("Undefined! The type detected: ")
                      Debug.traceln(Types.printTypeStr(inType))
                    fail()
                  end
                end
              end
               #= /* PR, for debugging */ =#
          outDimensions
        end

         #= @author: adrpo
         we might need to intantiate partial functions, but we should NOT add them to the DAE! =#
        function addFunctionsToDAE(inCache::FCore.Cache, funcs::List{<:DAE.Function} #= fully qualified function name =#, inPartialPrefix::SCode.Partial) ::FCore.Cache
              local outCache::FCore.Cache

              outCache = begin
                  local cache::FCore.Cache
                  local pPrefix::SCode.Partial
                   #= /*/ if not meta-modelica and we have a partial function, DO NOT ADD IT TO THE DAE!
                      case (cache, funcs, pPrefix as SCode.PARTIAL())
                        equation
                          false = Config.acceptMetaModelicaGrammar();
                          true = System.getPartialInstantiation();
                           if all the functions are complete, add them, otherwise, NO
                          fLst = List.select(funcs, DAEUtil.isNotCompleteFunction);
                          fLst = if_(listEmpty(fLst), funcs, {});
                          cache = FCore.addDaeFunction(cache, fLst);
                        then
                          cache;*/ =#
                   #=  otherwise add it to the DAE!
                   =#
                @match (inCache, funcs, inPartialPrefix) begin
                  (cache, _, _)  => begin
                      cache = FCore.addDaeFunction(cache, funcs)
                    cache
                  end
                end
              end
          outCache
        end

        function addNameToDerivativeMapping(inElts::List{<:DAE.Function}, path::Absyn.Path) ::List{DAE.Function}
              local outElts::List{DAE.Function}

              outElts = list(begin
                @match fn begin
                  DAE.FUNCTION(__)  => begin
                      fn.functions = addNameToDerivativeMappingFunctionDefs(fn.functions, path)
                    fn
                  end

                  _  => begin
                      fn
                  end
                end
              end for fn in inElts)
          outElts
        end

         #=  help function to addNameToDerivativeMapping =#
        function addNameToDerivativeMappingFunctionDefs(inFuncs::List{<:DAE.FunctionDefinition}, path::Absyn.Path) ::List{DAE.FunctionDefinition}
              local outFuncs::List{DAE.FunctionDefinition}

              outFuncs = list(begin
                @match fn begin
                  DAE.FUNCTION_DER_MAPPER(__)  => begin
                      fn.lowerOrderDerivatives = _cons(path, fn.lowerOrderDerivatives)
                    fn
                  end

                  _  => begin
                      fn
                  end
                end
              end for fn in inFuncs)
          outFuncs
        end

         #=
        Authot BZ
        helper function for InstFunction.implicitFunctionInstantiation, returns derivative of function, if any. =#
        function getDeriveAnnotation(cd::SCode.ClassDef, cmt::SCode.Comment, baseFunc::Absyn.Path, inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, info::SourceInfo) ::List{DAE.FunctionDefinition}
              local element::List{DAE.FunctionDefinition}

              element = begin
                  local elemDecl::List{SCode.Element}
                  local ann::SCode.Annotation
                @matchcontinue (cd, cmt, baseFunc, inCache, inEnv, inIH, inPrefix, info) begin
                  (SCode.PARTS(elementLst = elemDecl, externalDecl = SOME(SCode.EXTERNALDECL(annotation_ = SOME(ann)))), _, _, _, _, _, _, _)  => begin
                    getDeriveAnnotation2(ann, elemDecl, baseFunc, inCache, inEnv, inIH, inPrefix, info)
                  end

                  (SCode.PARTS(elementLst = elemDecl), SCode.COMMENT(annotation_ = SOME(ann)), _, _, _, _, _, _)  => begin
                    getDeriveAnnotation2(ann, elemDecl, baseFunc, inCache, inEnv, inIH, inPrefix, info)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          element
        end

         #=
        helper function for getDeriveAnnotation =#
        function getDeriveAnnotation2(ann::SCode.Annotation, elemDecl::List{<:SCode.Element}, baseFunc::Absyn.Path, inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, info::SourceInfo) ::List{DAE.FunctionDefinition}
              local element::List{DAE.FunctionDefinition}

              element = begin
                  local smlst::List{SCode.SubMod}
                  local anns::List{SCode.Annotation}
                @match (ann, elemDecl, baseFunc, inCache, inEnv, inIH, inPrefix, info) begin
                  (SCode.ANNOTATION(SCode.MOD(subModLst = smlst)), _, _, _, _, _, _, _)  => begin
                    getDeriveAnnotation3(smlst, elemDecl, baseFunc, inCache, inEnv, inIH, inPrefix, info)
                  end
                end
              end
          element
        end

         #=
        Author: bjozac
          helper function to getDeriveAnnotation2 =#
        function getDeriveAnnotation3(inSubs::List{<:SCode.SubMod}, elemDecl::List{<:SCode.Element}, baseFunc::Absyn.Path, inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, info::SourceInfo) ::List{DAE.FunctionDefinition}
              local element::List{DAE.FunctionDefinition}

              element = begin
                  local ae::Absyn.Exp
                  local acr::Absyn.ComponentRef
                  local deriveFunc::Absyn.Path
                  local defaultDerivative::Option{Absyn.Path}
                  local m::SCode.Mod
                  local subs2::List{SCode.SubMod}
                  local order::ModelicaInteger
                  local conditionRefs::List{Tuple{ModelicaInteger, DAE.derivativeCond}}
                  local mapper::DAE.FunctionDefinition
                  local subs::List{SCode.SubMod}
                @matchcontinue inSubs begin
                   nil()  => begin
                    fail()
                  end

                  SCode.NAMEMOD("derivative", SCode.MOD(subModLst = subs2, binding = SOME(Absyn.CREF(acr)))) <| subs  => begin
                      deriveFunc = AbsynUtil.crefToPath(acr)
                      (_, deriveFunc) = Inst.makeFullyQualified(inCache, inEnv, deriveFunc)
                      order = getDerivativeOrder(subs2)
                      ErrorExt.setCheckpoint("getDeriveAnnotation3") #= don't report errors on modifers in functions =#
                      conditionRefs = getDeriveCondition(subs2, elemDecl, inCache, inEnv, inIH, inPrefix, info)
                      ErrorExt.rollBack("getDeriveAnnotation3")
                      conditionRefs = ListUtil.sort(conditionRefs, DAEUtil.derivativeOrder)
                      defaultDerivative = getDerivativeSubModsOptDefault(subs, inCache, inEnv, inPrefix)
                      mapper = DAE.FUNCTION_DER_MAPPER(baseFunc, deriveFunc, order, conditionRefs, defaultDerivative, nil)
                    list(mapper)
                  end

                  _ <| subs  => begin
                    getDeriveAnnotation3(subs, elemDecl, baseFunc, inCache, inEnv, inIH, inPrefix, info)
                  end
                end
              end
               #= /*print(\"\\n adding conditions on derivative count: \" + intString(listLength(conditionRefs)) + \"\\n\");
                      dbgString = AbsynUtil.optPathString(defaultDerivative);
                      dbgString = if_(stringEq(dbgString,\"\"),\"\", \"**** Default Derivative: \" + dbgString + \"\\n\");
                      print(\"**** Function derived: \" + AbsynUtil.pathString(baseFunc) + \" \\n\");
                      print(\"**** Deriving function: \" + AbsynUtil.pathString(deriveFunc) + \"\\n\");
                      print(\"**** Conditions: \" + stringDelimitList(DAEDump.dumpDerivativeCond(conditionRefs),\", \") + \"\\n\");
                      print(\"**** Order: \" + intString(order) + \"\\n\");
                      print(dbgString);*/ =#
          element
        end

         #=
        helper function for getDeriveAnnotation
        Extracts conditions for derivative. =#
        function getDeriveCondition(inSubs::List{<:SCode.SubMod}, elemDecl::List{<:SCode.Element}, inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, info::SourceInfo) ::List{Tuple{ModelicaInteger, DAE.derivativeCond}}
              local outconds::List{Tuple{ModelicaInteger, DAE.derivativeCond}}

              outconds = begin
                  local m::SCode.Mod
                  local elabedMod::DAE.Mod
                  local sub::DAE.SubMod
                  local name::String
                  local cond::DAE.derivativeCond
                  local acr::Absyn.ComponentRef
                  local varPos::ModelicaInteger
                  local subs::List{SCode.SubMod}
                  local cache::FCore.Cache
                @matchcontinue (inSubs, elemDecl, inCache, inEnv, inIH, inPrefix, info) begin
                  ( nil(), _, _, _, _, _, _)  => begin
                    nil
                  end

                  (SCode.NAMEMOD("noDerivative", SCode.MOD(binding = SOME(Absyn.CREF(acr)))) <| subs, _, _, _, _, _, _)  => begin
                      name = AbsynUtil.printComponentRefStr(acr)
                      outconds = getDeriveCondition(subs, elemDecl, inCache, inEnv, inIH, inPrefix, info)
                      varPos = setFunctionInputIndex(elemDecl, name, 1)
                    _cons((varPos, DAE.NO_DERIVATIVE(DAE.ICONST(99))), outconds)
                  end

                  (SCode.NAMEMOD("zeroDerivative", SCode.MOD(binding = SOME(Absyn.CREF(acr)))) <| subs, _, _, _, _, _, _)  => begin
                      name = AbsynUtil.printComponentRefStr(acr)
                      outconds = getDeriveCondition(subs, elemDecl, inCache, inEnv, inIH, inPrefix, info)
                      varPos = setFunctionInputIndex(elemDecl, name, 1)
                    _cons((varPos, DAE.ZERO_DERIVATIVE()), outconds)
                  end

                  (SCode.NAMEMOD("noDerivative", m && SCode.MOD(__)) <| subs, _, _, _, _, _, _)  => begin
                      @match (cache, DAE.MOD(subModLst = list(sub))) = Mod.elabMod(inCache, inEnv, inIH, inPrefix, m, false, Mod.COMPONENT("noDerivative"), info)
                      (name, cond) = extractNameAndExp(sub)
                      outconds = getDeriveCondition(subs, elemDecl, cache, inEnv, inIH, inPrefix, info)
                      varPos = setFunctionInputIndex(elemDecl, name, 1)
                    _cons((varPos, cond), outconds)
                  end

                  (_ <| subs, _, _, _, _, _, _)  => begin
                    getDeriveCondition(subs, elemDecl, inCache, inEnv, inIH, inPrefix, info)
                  end
                end
              end
          outconds
        end

         #=
        Author BZ =#
        function setFunctionInputIndex(inElemDecl::List{<:SCode.Element}, str::String, currPos::ModelicaInteger) ::ModelicaInteger
              local index::ModelicaInteger

              index = begin
                  local str2::String
                  local elemDecl::List{SCode.Element}
                @matchcontinue (inElemDecl, str, currPos) begin
                  ( nil(), _, _)  => begin
                      print(" failure in setFunctionInputIndex, didn't find any index for: " + str + "\\n")
                    fail()
                  end

                  (SCode.COMPONENT(name = str2, attributes = SCode.ATTR(direction = Absyn.INPUT(__))) <| _, _, _)  => begin
                      @match true = stringEq(str2, str)
                    currPos
                  end

                  (SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.INPUT(__))) <| elemDecl, _, _)  => begin
                    setFunctionInputIndex(elemDecl, str, currPos + 1)
                  end

                  (_ <| elemDecl, _, _)  => begin
                    setFunctionInputIndex(elemDecl, str, currPos)
                  end
                end
              end
               #= /* found matching input*/ =#
               #= /* Non-matching input, increase inputarg pos*/ =#
               #= /* Other element, do not increaese inputarg pos*/ =#
          index
        end

         #=
        Author BZ
        could be used by getDeriveCondition, depending on interpretation of spec compared to constructed libraries.
        helper function for getDeriveAnnotation =#
        function extractNameAndExp(m::DAE.SubMod) ::Tuple{String, DAE.derivativeCond}
              local cond::DAE.derivativeCond
              local inputVar::String

              (inputVar, cond) = begin
                  local e::DAE.Exp
                @match m begin
                  DAE.NAMEMOD(ident = inputVar, mod = DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = e))))  => begin
                    (inputVar, DAE.NO_DERIVATIVE(e))
                  end

                  DAE.NAMEMOD(ident = inputVar, mod = DAE.MOD(binding = NONE()))  => begin
                    (inputVar, DAE.NO_DERIVATIVE(DAE.ICONST(1)))
                  end

                  DAE.NAMEMOD(ident = inputVar, mod = DAE.MOD(binding = NONE()))  => begin
                    (inputVar, DAE.ZERO_DERIVATIVE())
                  end

                  _  => begin
                      ("", DAE.ZERO_DERIVATIVE())
                  end
                end
              end
               #=  zeroderivative
               =#
          (inputVar, cond)
        end

         #=
        helper function for getDeriveAnnotation =#
        function getDerivativeSubModsOptDefault(inSubs::List{<:SCode.SubMod}, inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType) ::Option{Absyn.Path}
              local defaultDerivative::Option{Absyn.Path}

              defaultDerivative = begin
                  local acr::Absyn.ComponentRef
                  local p::Absyn.Path
                  local ae::Absyn.Exp
                  local m::SCode.Mod
                  local subs::List{SCode.SubMod}
                @matchcontinue (inSubs, inCache, inEnv, inPrefix) begin
                  ( nil(), _, _, _)  => begin
                    NONE()
                  end

                  (SCode.NAMEMOD("derivative", SCode.MOD(binding = SOME(Absyn.CREF(acr)))) <| _, _, _, _)  => begin
                      p = AbsynUtil.crefToPath(acr)
                      (_, p) = Inst.makeFullyQualified(inCache, inEnv, p)
                    SOME(p)
                  end

                  (_ <| subs, _, _, _)  => begin
                    getDerivativeSubModsOptDefault(subs, inCache, inEnv, inPrefix)
                  end
                end
              end
          defaultDerivative
        end

         #=
        helper function for getDeriveAnnotation
        Get current derive order =#
        function getDerivativeOrder(inSubs::List{<:SCode.SubMod}) ::ModelicaInteger
              local order::ModelicaInteger

              order = begin
                  local ae::Absyn.Exp
                  local m::SCode.Mod
                  local subs::List{SCode.SubMod}
                @match inSubs begin
                   nil()  => begin
                    1
                  end

                  SCode.NAMEMOD("order", SCode.MOD(binding = SOME(Absyn.INTEGER(order)))) <| _  => begin
                    order
                  end

                  _ <| subs  => begin
                    getDerivativeOrder(subs)
                  end
                end
              end
          order
        end

         #= This function sets the FQ path given as argument in types that have optional path set.
         (The optional path points to the class the type is built from) =#
        function setFullyQualifiedTypename(inType::DAE.Type, path::Absyn.Path) ::DAE.Type
              local resType::DAE.Type

              resType = begin
                  local newPath::Absyn.Path
                  local tp::DAE.Type
                @match inType begin
                  resType && DAE.T_FUNCTION(__)  => begin
                      resType.path = path
                    resType
                  end

                  _  => begin
                      inType
                  end
                end
              end
          resType
        end

        function classIsInlineFunc(elt::SCode.Element) ::DAE.InlineType
              local outInlineType::DAE.InlineType

              outInlineType = begin
                @match elt begin
                  SCode.CLASS(__)  => begin
                    commentIsInlineFunc(elt.cmt)
                  end

                  _  => begin
                      DAE.DEFAULT_INLINE()
                  end
                end
              end
          outInlineType
        end

        function commentIsInlineFunc(cmt::SCode.Comment) ::DAE.InlineType
              local outInlineType::DAE.InlineType

              outInlineType = begin
                  local smlst::List{SCode.SubMod}
                @matchcontinue cmt begin
                  SCode.COMMENT(annotation_ = SOME(SCode.ANNOTATION(SCode.MOD(subModLst = smlst))))  => begin
                    isInlineFunc2(smlst)
                  end

                  _  => begin
                      DAE.DEFAULT_INLINE()
                  end
                end
              end
          outInlineType
        end

        function isInlineFunc2(inSubModList::List{<:SCode.SubMod}) ::DAE.InlineType
              local res::DAE.InlineType

              local stop::Bool = false

              res = DAE.DEFAULT_INLINE()
              for tp in inSubModList
                stop = begin
                  @match tp begin
                    SCode.NAMEMOD("Inline", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.NORM_INLINE()
                      false
                    end

                    SCode.NAMEMOD("Inline", SCode.MOD(binding = SOME(Absyn.BOOL(false))))  => begin
                        res = DAE.NO_INLINE()
                      false
                    end

                    SCode.NAMEMOD("LateInline", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.AFTER_INDEX_RED_INLINE()
                      true
                    end

                    SCode.NAMEMOD("__MathCore_InlineAfterIndexReduction", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.AFTER_INDEX_RED_INLINE()
                      true
                    end

                    SCode.NAMEMOD("__Dymola_InlineAfterIndexReduction", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.AFTER_INDEX_RED_INLINE()
                      true
                    end

                    SCode.NAMEMOD("InlineAfterIndexReduction", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.AFTER_INDEX_RED_INLINE()
                      true
                    end

                    SCode.NAMEMOD("__OpenModelica_EarlyInline", SCode.MOD(binding = SOME(Absyn.BOOL(true))))  => begin
                        res = DAE.EARLY_INLINE()
                      true
                    end

                    _  => begin
                        false
                    end
                  end
                end
                if stop
                  break
                end
              end
          res
        end

         #= strips the assignment modification of the component declared as output =#
        function stripFuncOutputsMod(elem::SCode.Element) ::SCode.Element
              local stripped_elem::SCode.Element

              stripped_elem = begin
                  local id::SCode.Ident
                  local inOut::Absyn.InnerOuter
                  local finPre::SCode.Final
                  local repPre::SCode.Replaceable
                  local vis::SCode.Visibility
                  local redecl::SCode.Redeclare
                  local attr::SCode.Attributes
                  local typeSpc::Absyn.TypeSpec
                  local comm::SCode.Comment
                  local cond::Option{Absyn.Exp}
                  local info::SourceInfo
                  local modFinPre::SCode.Final
                  local modEachPre::SCode.Each
                  local modSubML::List{SCode.SubMod}
                  local e::SCode.Element
                  local modBla::SCode.Mod
                  local mod_info::SourceInfo
                @matchcontinue elem begin
                  SCode.COMPONENT(name = id, prefixes = SCode.PREFIXES(visibility = vis, redeclarePrefix = redecl, finalPrefix = finPre, innerOuter = inOut, replaceablePrefix = repPre), attributes = attr && SCode.ATTR(direction = Absyn.OUTPUT(__)), typeSpec = typeSpc, modifications = SCode.MOD(finalPrefix = modFinPre, eachPrefix = modEachPre, subModLst = modSubML, binding = SOME(_), info = mod_info), comment = comm, condition = cond, info = info)  => begin
                      modBla = SCode.MOD(modFinPre, modEachPre, modSubML, NONE(), mod_info)
                    SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, finPre, inOut, repPre), attr, typeSpc, modBla, comm, cond, info)
                  end

                  e  => begin
                    e
                  end
                end
              end
          stripped_elem
        end

         #=
          * All in-/outputs are referenced
          * There must be no algorithm section (checked earlier)
           =#
        function checkExternalFunction(els::List{<:DAE.Element}, decl::DAE.ExternalDecl, name::String)
              local i::ModelicaInteger

              if decl.language == "builtin"
                return
              end
              ListUtil.map2_0(els, checkExternalFunctionOutputAssigned, decl, name)
              checkFunctionInputUsed(els, SOME(decl), name)
        end

        function checkFunctionInputUsed(elts::List{<:DAE.Element}, decl::Option{<:DAE.ExternalDecl}, name::String)
              local invars::List{DAE.Element}
              local vars::List{DAE.Element}
              local algs::List{DAE.Element}

              (vars, _, _, _, algs, _, _, _, _) = DAEUtil.splitElements(elts)
              invars = ListUtil.filterOnTrue(vars, DAEUtil.isInputVar)
              invars = ListUtil.select(invars, checkInputUsedAnnotation)
              invars = checkExternalDeclInputUsed(invars, decl)
              invars = ListUtil.select1(invars, checkVarBindingsInputUsed, vars)
              (_, (_, invars)) = DAEUtil.traverseDAEElementList(algs, Expression.traverseSubexpressionsHelper, (checkExpInputUsed, invars))
              ListUtil.map1_0(invars, warnUnusedFunctionVar, name)
        end

         #=
          True if __OpenModelica_UnusedVariable does not exist in the element.
         =#
        function checkInputUsedAnnotation(inElement::DAE.Element) ::Bool
              local result::Bool

              result = begin
                  local cmt::Option{SCode.Comment}
                  local cr::DAE.ComponentRef
                @match inElement begin
                  DAE.VAR(comment = cmt)  => begin
                      result = SCodeUtil.optCommentHasBooleanNamedAnnotation(cmt, "__OpenModelica_UnusedVariable")
                    ! result
                  end

                  _  => begin
                      true
                  end
                end
              end
          result
        end

        function warnUnusedFunctionVar(v::DAE.Element, name::String)
              local cr::DAE.ComponentRef
              local source::DAE.ElementSource
              local str::String

              @match DAE.VAR(componentRef = cr, source = source) = v
              str = ComponentReference.printComponentRefStr(cr)
              Error.addSourceMessage(Error.FUNCTION_UNUSED_INPUT, list(str, name), ElementSource.getElementSourceFileInfo(source))
        end

        function checkExternalDeclInputUsed(inames::List{<:DAE.Element}, decl::Option{<:DAE.ExternalDecl}) ::List{DAE.Element}
              local onames::List{DAE.Element}

              onames = begin
                  local args::List{DAE.ExtArg}
                  local arg::DAE.ExtArg
                  local names::List{DAE.Element}
                @match (inames, decl) begin
                  (names, NONE())  => begin
                    names
                  end

                  ( nil(), _)  => begin
                    nil
                  end

                  (names, SOME(DAE.EXTERNALDECL(returnArg = arg, args = args)))  => begin
                      names = ListUtil.select1(names, checkExternalDeclArgs, _cons(arg, args))
                    names
                  end
                end
              end
          onames
        end

        function checkExpInputUsed(inExp::DAE.Exp, inEls::List{<:DAE.Element}) ::Tuple{DAE.Exp, List{DAE.Element}}
              local els::List{DAE.Element}
              local exp::DAE.Exp

              (exp, els) = begin
                  local cr::DAE.ComponentRef
                  local path::Absyn.Path
                @matchcontinue (inExp, inEls) begin
                  (exp && DAE.CREF(componentRef = cr), els)  => begin
                      els = ListUtil.select1(els, checkExpInputUsed3, cr)
                    (exp, els)
                  end

                  (exp && DAE.CALL(path = path), els)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      cr = ComponentReference.pathToCref(path)
                      els = ListUtil.select1(els, checkExpInputUsed3, cr)
                    (exp, els)
                  end

                  _  => begin
                      (inExp, inEls)
                  end
                end
              end
          (exp, els)
        end

        function checkExpInputUsed3(el::DAE.Element, cr2::DAE.ComponentRef) ::Bool
              local noteq::Bool

              local cr1::DAE.ComponentRef

              @match DAE.VAR(componentRef = cr1) = el
              noteq = ! ComponentReference.crefEqualNoStringCompare(cr1, cr2)
          noteq
        end

        function checkVarBindingsInputUsed(v::DAE.Element, els::List{<:DAE.Element}) ::Bool
              local notfound::Bool

              notfound = ! ListUtil.isMemberOnTrue(v, els, checkVarBindingInputUsed)
          notfound
        end

        function checkVarBindingInputUsed(v::DAE.Element, el::DAE.Element) ::Bool
              local found::Bool

              found = begin
                  local exp::DAE.Exp
                  local cr::DAE.ComponentRef
                @match (v, el) begin
                  (DAE.VAR(__), DAE.VAR(direction = DAE.INPUT(__)))  => begin
                    false
                  end

                  (DAE.VAR(componentRef = cr), DAE.VAR(binding = SOME(exp)))  => begin
                    Expression.expHasCref(exp, cr)
                  end

                  _  => begin
                      false
                  end
                end
              end
          found
        end

        function checkExternalDeclArgs(v::DAE.Element, args::List{<:DAE.ExtArg}) ::Bool
              local notfound::Bool

              notfound = ! ListUtil.isMemberOnTrue(v, args, extArgCrefEq)
          notfound
        end

         #= All outputs must either have a default binding or be used in the external function
        declaration as there is no way to make assignments in external functions. =#
        function checkExternalFunctionOutputAssigned(v::DAE.Element, decl::DAE.ExternalDecl, name::String)
              _ = begin
                  local arg::DAE.ExtArg
                  local args::List{DAE.ExtArg}
                  local b::Bool
                  local binding::Option{DAE.Exp}
                  local str::String
                  local cr::DAE.ComponentRef
                  local source::DAE.ElementSource
                @match (v, decl, name) begin
                  (DAE.VAR(direction = DAE.OUTPUT(__), componentRef = cr, binding = binding, source = source), DAE.EXTERNALDECL(returnArg = arg, args = args), _)  => begin
                      if ! (ListUtil.isMemberOnTrue(v, _cons(arg, args), extArgCrefEq) || isSome(binding))
                        str = ComponentReference.printComponentRefStr(cr)
                        Error.addSourceMessage(Error.EXTERNAL_NOT_SINGLE_RESULT, list(str, name), ElementSource.getElementSourceFileInfo(source))
                        fail()
                      end
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= See if an external argument matches a cref =#
        function extArgCrefEq(v::DAE.Element, arg::DAE.ExtArg) ::Bool
              local b::Bool

              b = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local exp::DAE.Exp
                @match (v, arg) begin
                  (DAE.VAR(componentRef = cr1), DAE.EXTARG(componentRef = cr2))  => begin
                      cr2 = ComponentReference.crefFirstCref(cr2)
                    ComponentReference.crefEqualNoStringCompare(cr1, cr2)
                  end

                  (DAE.VAR(direction = DAE.OUTPUT(__)), _)  => begin
                    false
                  end

                  (DAE.VAR(componentRef = cr1), DAE.EXTARGSIZE(componentRef = cr2))  => begin
                      cr2 = ComponentReference.crefFirstCref(cr2)
                    ComponentReference.crefEqualNoStringCompare(cr1, cr2)
                  end

                  (DAE.VAR(componentRef = cr1), DAE.EXTARGEXP(exp = exp))  => begin
                    Expression.expHasCref(exp, cr1)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  If the external argument refers to a record member, i.e. a qualified
               =#
               #=  cref, consider the whole record to be used.
               =#
          b
        end

         #= If the external function id is present, then a function call must
          exist, i.e. explicit call was written in the external clause. =#
        function isExtExplicitCall(inExternalDecl::SCode.ExternalDecl) ::Bool
              local isExplicit::Bool

              isExplicit = begin
                @match inExternalDecl begin
                  SCode.EXTERNALDECL(funcName = SOME(_))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isExplicit
        end

         #= Succeds for Elements that are input or output components =#
        function isInoutVar(inElement::SCode.Element) ::Bool
              local b::Bool

              b = isOutputVar(inElement) || isInputVar(inElement)
          b
        end

         #= Succeds for element that is output component =#
        function isOutputVar(inElement::SCode.Element) ::Bool
              local b::Bool

              b = begin
                @match inElement begin
                  SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.OUTPUT(__)))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Succeds for element that is input component =#
        function isInputVar(inElement::SCode.Element) ::Bool
              local b::Bool

              b = begin
                @match inElement begin
                  SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.INPUT(__)))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns the function name of the externally defined function. =#
        function instExtGetFname(inExternalDecl::SCode.ExternalDecl, inIdent::String) ::String
              local outIdent::String

              outIdent = begin
                  local id::String
                  local fid::String
                @match (inExternalDecl, inIdent) begin
                  (SCode.EXTERNALDECL(funcName = SOME(id)), _)  => begin
                    id
                  end

                  (SCode.EXTERNALDECL(funcName = NONE()), fid)  => begin
                    fid
                  end
                end
              end
          outIdent
        end

         #= author: PA
          Return the annotation associated with an external function declaration.
          If no annotation is found, check the classpart annotations. =#
        function instExtGetAnnotation(inExternalDecl::SCode.ExternalDecl) ::Option{SCode.Annotation}
              local outAnnotation::Option{SCode.Annotation}

              outAnnotation = begin
                  local ann::Option{SCode.Annotation}
                @match inExternalDecl begin
                  SCode.EXTERNALDECL(annotation_ = ann)  => begin
                    ann
                  end
                end
              end
          outAnnotation
        end

         #= Return the implementation language of the external function declaration.
          Defaults to \\\"C\\\" if no language specified. =#
        function instExtGetLang(inExternalDecl::SCode.ExternalDecl) ::String
              local outString::String

              outString = begin
                  local lang::String
                @match inExternalDecl begin
                  SCode.EXTERNALDECL(lang = SOME(lang))  => begin
                    lang
                  end

                  SCode.EXTERNALDECL(lang = NONE())  => begin
                    "C"
                  end
                end
              end
          outString
        end

         #= Special elabExp for explicit external calls.
          This special function calls elabExpExt which handles size builtin
          calls specially, and uses the ordinary Static.elab_exp for other
          expressions. =#
        function elabExpListExt(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Exp}, List{DAE.Properties}}
              local outTypesPropertiesLst::List{DAE.Properties}
              local outExpExpLst::List{DAE.Exp}
              local outCache::FCore.Cache

              (outCache, outExpExpLst, outTypesPropertiesLst) = begin
                  local impl::Bool
                  local exp::DAE.Exp
                  local p::DAE.Properties
                  local exps::List{DAE.Exp}
                  local props::List{DAE.Properties}
                  local env::FCore.Graph
                  local e::Absyn.Exp
                  local rest::List{Absyn.Exp}
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local cr::DAE.ComponentRef
                @match (inCache, inEnv, inAbsynExpLst, inBoolean, inPrefix, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil, nil)
                  end

                  (cache, env, e <| rest, impl, pre, _)  => begin
                      (cache, exp, p) = elabExpExt(cache, env, e, impl, pre, info)
                      (cache, exps, props) = elabExpListExt(cache, env, rest, impl, pre, info)
                    (cache, _cons(exp, exps), _cons(p, props))
                  end
                end
              end
          (outCache, outExpExpLst, outTypesPropertiesLst)
        end

         #= author: LS
          special elabExp for explicit external calls.
          This special function calls elabExpExt which handles size builtin calls
          specially, and uses the ordinary Static.elab_exp for other expressions. =#
        function elabExpExt(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = begin
                  local dimp::DAE.Exp
                  local arraycrefe::DAE.Exp
                  local exp::DAE.Exp
                  local e::DAE.Exp
                  local dimty::DAE.Type
                  local arraycrprop::DAE.Properties
                  local prop::DAE.Properties
                  local env::FCore.Graph
                  local call::Absyn.Exp
                  local arraycr::Absyn.Exp
                  local dim::Absyn.Exp
                  local args::List{Absyn.Exp}
                  local nargs::List{Absyn.NamedArg}
                  local impl::Bool
                  local cache::FCore.Cache
                  local absynExp::Absyn.Exp
                  local pre::Prefix.PrefixType
                   #=  special case for  size
                   =#
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inPrefix, info) begin
                  (cache, env, Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "size"), functionArgs = Absyn.FUNCTIONARGS(args = arraycr <| dim <|  nil())), impl, pre, _)  => begin
                      @match (cache, dimp, (@match DAE.PROP(_, _) = prop)) = Static.elabExp(cache, env, dim, impl, false, pre, info)
                      (cache, dimp, prop) = Ceval.cevalIfConstant(cache, env, dimp, prop, impl, info)
                      (cache, arraycrefe, arraycrprop) = Static.elabExp(cache, env, arraycr, impl, false, pre, info)
                      (cache, arraycrefe, arraycrprop) = Ceval.cevalIfConstant(cache, env, arraycrefe, arraycrprop, impl, info)
                      exp = DAE.SIZE(arraycrefe, SOME(dimp))
                    (cache, exp, DAE.PROP(DAE.T_INTEGER_DEFAULT, DAE.C_VAR()))
                  end

                  (cache, env, absynExp, impl, pre, _)  => begin
                      (cache, e, prop) = Static.elabExp(cache, env, absynExp, impl, false, pre, info)
                      (cache, e, prop) = Ceval.cevalIfConstant(cache, env, e, prop, impl, info)
                    (cache, e, prop)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("-Inst.elabExpExt failed")
                      fail()
                  end
                end
              end
               #=  For all other expressions, use normal elaboration
               =#
          (outCache, outExp, outProperties)
        end

         #= author: LS
          instantiates function arguments, i.e. actual parameters, in external declaration. =#
        function instExtGetFargs(inCache::FCore.Cache, inEnv::FCore.Graph, inExternalDecl::SCode.ExternalDecl, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.ExtArg}}
              local outDAEExtArgLst::List{DAE.ExtArg}
              local outCache::FCore.Cache

              (outCache, outDAEExtArgLst) = begin
                  local exps::List{DAE.Exp}
                  local props::List{DAE.Properties}
                  local extargs::List{DAE.ExtArg}
                  local env::FCore.Graph
                  local id::Option{String}
                  local lang::Option{String}
                  local retcr::Option{Absyn.ComponentRef}
                  local absexps::List{Absyn.Exp}
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                @matchcontinue (inCache, inEnv, inExternalDecl, inBoolean, inPrefix, info) begin
                  (cache, env, SCode.EXTERNALDECL(lang = lang, args = absexps), impl, pre, _)  => begin
                      (cache, exps, props) = elabExpListExt(cache, env, absexps, impl, pre, info)
                      (cache, extargs) = instExtGetFargs2(cache, env, absexps, exps, props, lang, info)
                    (cache, extargs)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- InstUtil.instExtGetFargs failed")
                      fail()
                  end
                end
              end
          (outCache, outDAEExtArgLst)
        end

         #= author: LS
          Helper function to instExtGetFargs =#
        function instExtGetFargs2(inCache::FCore.Cache, inEnv::FCore.Graph, absynExps::List{<:Absyn.Exp}, inExpExpLst::List{<:DAE.Exp}, inTypesPropertiesLst::List{<:DAE.Properties}, lang::Option{<:String}, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.ExtArg}}
              local outDAEExtArgLst::List{DAE.ExtArg}
              local outCache::FCore.Cache

              (outCache, outDAEExtArgLst) = begin
                  local extargs::List{DAE.ExtArg}
                  local extarg::DAE.ExtArg
                  local env::FCore.Graph
                  local e::DAE.Exp
                  local exps::List{DAE.Exp}
                  local p::DAE.Properties
                  local props::List{DAE.Properties}
                  local cache::FCore.Cache
                  local ae::Absyn.Exp
                  local aes::List{Absyn.Exp}
                @match (inCache, inEnv, absynExps, inExpExpLst, inTypesPropertiesLst, lang, info) begin
                  (cache, _, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, ae <| aes, e <| exps, p <| props, _, _)  => begin
                      @match (cache, SOME(extarg)) = instExtGetFargsSingle(cache, env, ae, e, p, lang, info)
                      (cache, extargs) = instExtGetFargs2(cache, env, aes, exps, props, lang, info)
                    (cache, _cons(extarg, extargs))
                  end
                end
              end
          (outCache, outDAEExtArgLst)
        end

         #= author: LS
          Helper function to instExtGetFargs2, does the work for one argument. =#
        function instExtGetFargsSingle(inCache::FCore.Cache, inEnv::FCore.Graph, absynExp::Absyn.Exp, inExp::DAE.Exp, inProperties::DAE.Properties, lang::Option{<:String}, info::SourceInfo) ::Tuple{FCore.Cache, Option{DAE.ExtArg}}
              local outExtArg::Option{DAE.ExtArg}
              local outCache::FCore.Cache

              (outCache, outExtArg) = begin
                  local attr::DAE.Attributes
                  local fattr::DAE.Attributes
                  local ty::DAE.Type
                  local varty::DAE.Type
                  local bnd::DAE.Binding
                  local env::FCore.Graph
                  local cref::DAE.ComponentRef
                  local fcr::DAE.ComponentRef
                  local crty::DAE.Type
                  local cnst::DAE.Const
                  local crefstr::String
                  local scope::String
                  local dim::DAE.Exp
                  local exp::DAE.Exp
                  local prop::DAE.Properties
                  local cache::FCore.Cache
                  local variability::SCode.Variability
                  local val::Values.Value
                  local str::String
                @matchcontinue (inCache, inEnv, absynExp, inExp, inProperties, lang, info) begin
                  (_, _, _, DAE.CREF(componentRef = cref && DAE.CREF_QUAL(__)), DAE.PROP(constFlag = DAE.C_VAR(__)), _, _)  => begin
                      (cache, _, ty, _, _, _, _, _, _) = Lookup.lookupVarLocal(inCache, inEnv, cref)
                      fcr = ComponentReference.crefFirstCref(cref)
                      (cache, fattr, _, _, _, _, _, _, _) = Lookup.lookupVarLocal(cache, inEnv, fcr)
                    (cache, SOME(DAE.EXTARG(cref, DAEUtil.getAttrDirection(fattr), ty)))
                  end

                  (_, _, _, DAE.CREF(componentRef = cref && DAE.CREF_IDENT(__)), DAE.PROP(constFlag = DAE.C_VAR(__)), _, _)  => begin
                      (cache, attr, ty, _, _, _, _, _, _) = Lookup.lookupVarLocal(inCache, inEnv, cref)
                    (cache, SOME(DAE.EXTARG(cref, DAEUtil.getAttrDirection(attr), ty)))
                  end

                  (cache, env, _, DAE.CREF(componentRef = cref), DAE.PROP(__), _, _)  => begin
                      @shouldFail (_, _, _, _, _, _, _, _, _) = Lookup.lookupVarLocal(cache, env, cref)
                      crefstr = ComponentReference.printComponentRefStr(cref)
                      scope = FGraph.printGraphPathStr(env)
                      Error.addMessage(Error.LOOKUP_VARIABLE_ERROR, list(crefstr, scope))
                    (cache, NONE())
                  end

                  (cache, env, _, DAE.SIZE(exp = DAE.CREF(componentRef = cref), sz = SOME(dim)), DAE.PROP(__), _, _)  => begin
                      (cache, _, varty, _, _, _, _, _, _) = Lookup.lookupVarLocal(cache, env, cref)
                    (cache, SOME(DAE.EXTARGSIZE(cref, varty, dim)))
                  end

                  (cache, env, _, _, DAE.PROP(type_ = ty, constFlag = DAE.C_CONST(__)), _, _)  => begin
                      (cache, exp) = Ceval.cevalIfConstant(cache, env, inExp, inProperties, false, info)
                      @match true = Expression.isScalarConst(exp)
                    (cache, SOME(DAE.EXTARGEXP(exp, ty)))
                  end

                  (cache, _, _, _, DAE.PROP(type_ = ty), SOME("builtin"), _)  => begin
                    (cache, SOME(DAE.EXTARGEXP(inExp, ty)))
                  end

                  (cache, _, _, DAE.CALL(attr = DAE.CALL_ATTR(builtin = true)), DAE.PROP(type_ = ty), _, _)  => begin
                    (cache, SOME(DAE.EXTARGEXP(inExp, ty)))
                  end

                  (cache, _, Absyn.CREF(_), _, DAE.PROP(type_ = ty), _, _)  => begin
                    (cache, SOME(DAE.EXTARGEXP(inExp, ty)))
                  end

                  (cache, _, _, exp, DAE.PROP(__), _, _)  => begin
                      str = ExpressionDump.printExpStr(exp)
                      Error.addSourceMessage(Error.EXTERNAL_ARG_WRONG_EXP, list(str), info)
                    (cache, NONE())
                  end
                end
              end
               #=  For qualified crefs, copy input/output from the first part of the
               =#
               #=  cref. This is done so that the correct code can be generated when
               =#
               #=  using qualified crefs in external function definitions.
               =#
               #=  adrpo: these can be non-local if they are constants or parameters!
               =#
          (outCache, outExtArg)
        end

         #= author: LS
          Instantiates the return type of an external declaration. =#
        function instExtGetRettype(inCache::FCore.Cache, inEnv::FCore.Graph, inExternalDecl::SCode.ExternalDecl, inBoolean::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.ExtArg}
              local outExtArg::DAE.ExtArg
              local outCache::FCore.Cache

              (outCache, outExtArg) = begin
                  local exp::DAE.Exp
                  local prop::DAE.Properties
                  local extarg::DAE.ExtArg
                  local env::FCore.Graph
                  local n::Option{String}
                  local lang::Option{String}
                  local cref::Absyn.ComponentRef
                  local args::List{Absyn.Exp}
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local attr::DAE.Attributes
                @matchcontinue (inCache, inEnv, inExternalDecl, inBoolean, inPrefix, info) begin
                  (cache, _, SCode.EXTERNALDECL(output_ = NONE()), _, _, _)  => begin
                    (cache, DAE.NOEXTARG())
                  end

                  (cache, env, SCode.EXTERNALDECL(lang = lang, output_ = SOME(cref)), impl, pre, _)  => begin
                      @match (cache, SOME((exp, prop, _))) = Static.elabCref(cache, env, cref, impl, false, pre, info)
                      @match (cache, SOME(extarg)) = instExtGetFargsSingle(cache, env, Absyn.CREF(cref), exp, prop, lang, info)
                      assertExtArgOutputIsCrefVariable(lang, extarg, Types.getPropType(prop), Types.propAllConst(prop), info)
                    (cache, extarg)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- InstUtil.instExtRettype failed")
                      fail()
                  end
                end
              end
               #= /* impl */ =#
               #= /* Do NOT vectorize arrays; we require a CREF */ =#
          (outCache, outExtArg)
        end

        function assertExtArgOutputIsCrefVariable(lang::Option{<:String}, arg::DAE.ExtArg, ty::DAE.Type, c::DAE.Const, info::SourceInfo)
              _ = begin
                  local str::String
                @match (lang, arg, ty, c, info) begin
                  (SOME("builtin"), _, _, _, _)  => begin
                    ()
                  end

                  (_, _, DAE.T_ARRAY(__), _, _)  => begin
                      str = Types.unparseType(ty)
                      Error.addSourceMessage(Error.EXTERNAL_FUNCTION_RESULT_ARRAY_TYPE, list(str), info)
                    fail()
                  end

                  (_, DAE.EXTARG(__), _, DAE.C_VAR(__), _)  => begin
                    ()
                  end

                  (_, _, _, DAE.C_VAR(__), _)  => begin
                      str = DAEDump.dumpExtArgStr(arg)
                      Error.addSourceMessage(Error.EXTERNAL_FUNCTION_RESULT_NOT_CREF, list(str), info)
                    fail()
                  end

                  _  => begin
                        Error.addSourceMessage(Error.EXTERNAL_FUNCTION_RESULT_NOT_VAR, nil, info)
                      fail()
                  end
                end
              end
        end

         #= Creates a DAE.VarVisibility from a SCode.Visibility =#
        function makeDaeProt(visibility::SCode.Visibility) ::DAE.VarVisibility
              local res::DAE.VarVisibility

              res = begin
                @match visibility begin
                  SCode.PROTECTED(__)  => begin
                    DAE.PROTECTED()
                  end

                  SCode.PUBLIC(__)  => begin
                    DAE.PUBLIC()
                  end
                end
              end
          res
        end

        function makeDaeVariability(inVariability::SCode.Variability) ::DAE.VarKind
              local outVariability::DAE.VarKind

              outVariability = begin
                @match inVariability begin
                  SCode.VAR(__)  => begin
                    DAE.VARIABLE()
                  end

                  SCode.PARAM(__)  => begin
                    DAE.PARAM()
                  end

                  SCode.CONST(__)  => begin
                    DAE.CONST()
                  end

                  SCode.DISCRETE(__)  => begin
                    DAE.DISCRETE()
                  end
                end
              end
          outVariability
        end

        function makeDaeDirection(inDirection::Absyn.Direction) ::DAE.VarDirection
              local outDirection::DAE.VarDirection

              outDirection = begin
                @match inDirection begin
                  Absyn.INPUT(__)  => begin
                    DAE.INPUT()
                  end

                  Absyn.OUTPUT(__)  => begin
                    DAE.OUTPUT()
                  end

                  Absyn.BIDIR(__)  => begin
                    DAE.BIDIR()
                  end
                end
              end
          outDirection
        end

         #= From a class typename, its inference state, and a list of subcomponents,
          this function returns DAE.Type.  If the class inference state
          indicates that the type should be a built-in type, one of the
          built-in type constructors is used.  Otherwise, a T_COMPLEX is
          built. =#
        function mktype(inPath::Absyn.Path, inState::ClassInf.SMNode, inTypesVarLst::List{<:DAE.Var}, inTypesTypeOption::Option{<:DAE.Type}, inEqualityConstraint::DAE.EqualityConstraint, inClass::SCode.Element, inheritedComment::SCode.Comment) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local somep::Option{Absyn.Path}
                  local p::Absyn.Path
                  local v::List{DAE.Var}
                  local vl::List{DAE.Var}
                  local l::List{DAE.Var}
                  local bc2::DAE.Type
                  local functype::DAE.Type
                  local enumtype::DAE.Type
                  local st::ClassInf.SMNode
                  local bc::DAE.Type
                  local cl::SCode.Element
                  local arrayType::DAE.Type
                  local resType::DAE.Type
                  local classState::ClassInf.SMNode
                  local equalityConstraint::DAE.EqualityConstraint
                  local funcattr::DAE.FunctionAttributes
                  local pstr::String
                  local info::SourceInfo
                @matchcontinue (inPath, inState, inTypesVarLst, inTypesTypeOption, inEqualityConstraint, inClass) begin
                  (_, ClassInf.TYPE_INTEGER(__), v, _, _, _)  => begin
                    DAE.T_INTEGER(v)
                  end

                  (_, ClassInf.TYPE_REAL(__), v, _, _, _)  => begin
                    DAE.T_REAL(v)
                  end

                  (_, ClassInf.TYPE_STRING(__), v, _, _, _)  => begin
                    DAE.T_STRING(v)
                  end

                  (_, ClassInf.TYPE_BOOL(__), v, _, _, _)  => begin
                    DAE.T_BOOL(v)
                  end

                  (_, ClassInf.TYPE_CLOCK(__), v, _, _, _)  => begin
                    DAE.T_CLOCK(v)
                  end

                  (p, ClassInf.TYPE_ENUM(__), _, _, _, _)  => begin
                    DAE.T_ENUMERATION(NONE(), p, nil, nil, nil)
                  end

                  (p, ClassInf.FUNCTION(__), vl, _, _, cl)  => begin
                      funcattr = getFunctionAttributes(cl, vl, inheritedComment)
                      functype = Types.makeFunctionType(p, vl, funcattr)
                    functype
                  end

                  (_, ClassInf.ENUMERATION(path = p), _, SOME(enumtype), _, _)  => begin
                      enumtype = Types.makeEnumerationType(p, enumtype)
                    enumtype
                  end

                  (_, ClassInf.TYPE(__), _, SOME(DAE.T_ARRAY(ty = arrayType)), NONE(), _)  => begin
                      classState = arrayTTypeToClassInfState(arrayType)
                      resType = mktype(inPath, classState, inTypesVarLst, inTypesTypeOption, inEqualityConstraint, inClass, inheritedComment)
                    resType
                  end

                  (_, ClassInf.TYPE(__), _, SOME(DAE.T_ARRAY(ty = arrayType)), SOME(_), _)  => begin
                      classState = arrayTTypeToClassInfState(arrayType)
                      resType = mktype(inPath, classState, inTypesVarLst, inTypesTypeOption, inEqualityConstraint, inClass, inheritedComment)
                      resType = DAE.T_SUBTYPE_BASIC(inState, nil, resType, inEqualityConstraint)
                    resType
                  end

                  (_, ClassInf.META_TUPLE(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (_, ClassInf.META_OPTION(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (_, ClassInf.META_LIST(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (_, ClassInf.META_POLYMORPHIC(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (_, ClassInf.META_ARRAY(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (_, ClassInf.META_UNIONTYPE(_), _, SOME(bc2), _, _)  => begin
                    bc2
                  end

                  (p, ClassInf.META_UNIONTYPE(_), _, _, _, _)  => begin
                      pstr = AbsynUtil.pathString(p)
                      info = SCodeUtil.elementInfo(inClass)
                      Error.addSourceMessage(Error.META_UNIONTYPE_ALIAS_MODS, list(pstr), info)
                    fail()
                  end

                  (_, st, l, NONE(), equalityConstraint, _)  => begin
                      @shouldFail @match ClassInf.META_UNIONTYPE(_) = st
                    DAE.T_COMPLEX(st, l, equalityConstraint)
                  end

                  (_, st, l, SOME(bc), equalityConstraint, _)  => begin
                      @shouldFail @match ClassInf.META_UNIONTYPE(_) = st
                    DAE.T_SUBTYPE_BASIC(st, l, bc, equalityConstraint)
                  end
                end
              end
               #=  BTH
               =#
               #=  Insert function type construction here after checking input/output arguments? see Types.mo T_FUNCTION
               =#
               #=  Array of type extending from base type, adrpo: WITH NO EQUALITY CONSTRAINT, otherwise we loose it!
               =#
               #=  Array of type extending from base type, adrpo: WITH EQUALITY CONSTRAINT, build a T_SUBTYPE_BASIC
               =#
               #= /* MetaModelica extension */ =#
               #= /*------------------------*/ =#
               #=  not extending
               =#
               #=  extending
               =#
          outType
        end

        function arrayTTypeToClassInfState(arrayType::DAE.Type) ::ClassInf.SMNode
              local classInfState::ClassInf.SMNode

              classInfState = begin
                  local t::DAE.Type
                  local cs::ClassInf.SMNode
                @match arrayType begin
                  DAE.T_INTEGER(__)  => begin
                    ClassInf.TYPE_INTEGER(Absyn.IDENT(""))
                  end

                  DAE.T_REAL(__)  => begin
                    ClassInf.TYPE_REAL(Absyn.IDENT(""))
                  end

                  DAE.T_STRING(__)  => begin
                    ClassInf.TYPE_STRING(Absyn.IDENT(""))
                  end

                  DAE.T_BOOL(__)  => begin
                    ClassInf.TYPE_BOOL(Absyn.IDENT(""))
                  end

                  DAE.T_CLOCK(__)  => begin
                    ClassInf.TYPE_CLOCK(Absyn.IDENT(""))
                  end

                  DAE.T_ARRAY(ty = t)  => begin
                      cs = arrayTTypeToClassInfState(t)
                    cs
                  end
                end
              end
               #=  BTH FIXME Dont understand for what this function is good to. Just adding clock anyway
               =#
          classInfState
        end

         #= author: PA
          This function is similar to mktype with the exception
          that it will create array types based on the last argument,
          which indicates wheter the class extends from a basictype.
          It is used only in the inst_class_basictype function. =#
        function mktypeWithArrays(inPath::Absyn.Path, inState::ClassInf.SMNode, inTypesVarLst::List{<:DAE.Var}, inTypesTypeOption::Option{<:DAE.Type}, inClass::SCode.Element, inheritedComment::SCode.Comment) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local p::Absyn.Path
                  local ci::ClassInf.SMNode
                  local st::ClassInf.SMNode
                  local vs::List{DAE.Var}
                  local v::List{DAE.Var}
                  local vl::List{DAE.Var}
                  local l::List{DAE.Var}
                  local tp::DAE.Type
                  local functype::DAE.Type
                  local enumtype::DAE.Type
                  local somep::Option{Absyn.Path}
                  local cl::SCode.Element
                  local bc::DAE.Type
                  local funcattr::DAE.FunctionAttributes
                @matchcontinue (inPath, inState, inTypesVarLst, inTypesTypeOption, inClass) begin
                  (_, ci, _, SOME(tp), _)  => begin
                      @match true = Types.isArray(tp)
                      @shouldFail ClassInf.isConnector(ci)
                    tp
                  end

                  (p, ClassInf.TYPE_INTEGER(__), v, _, _)  => begin
                      _ = getOptPath(p)
                    DAE.T_INTEGER(v)
                  end

                  (_, ClassInf.TYPE_REAL(__), v, _, _)  => begin
                    DAE.T_REAL(v)
                  end

                  (_, ClassInf.TYPE_STRING(__), v, _, _)  => begin
                    DAE.T_STRING(v)
                  end

                  (_, ClassInf.TYPE_BOOL(__), v, _, _)  => begin
                    DAE.T_BOOL(v)
                  end

                  (_, ClassInf.TYPE_CLOCK(__), v, _, _)  => begin
                    DAE.T_CLOCK(v)
                  end

                  (p, ClassInf.TYPE_ENUM(__), _, _, _)  => begin
                    DAE.T_ENUMERATION(NONE(), p, nil, nil, nil)
                  end

                  (p, ClassInf.FUNCTION(__), vl, _, cl)  => begin
                      funcattr = getFunctionAttributes(cl, vl, inheritedComment)
                      functype = Types.makeFunctionType(p, vl, funcattr)
                    functype
                  end

                  (p, ClassInf.ENUMERATION(__), _, SOME(enumtype), _)  => begin
                      enumtype = Types.makeEnumerationType(p, enumtype)
                    enumtype
                  end

                  (_, st, l, NONE(), _)  => begin
                    DAE.T_COMPLEX(st, l, NONE())
                  end

                  (_, st, l, SOME(bc), _)  => begin
                    DAE.T_SUBTYPE_BASIC(st, l, bc, NONE())
                  end

                  _  => begin
                        print("InstUtil.mktypeWithArrays failed\\n")
                      fail()
                  end
                end
              end
               #=  BTH
               =#
               #=  Insert function type construction here after checking input/output arguments? see Types.mo T_FUNCTION
               =#
               #=  not extending basic type!
               =#
               #=  adrpo: TODO! check equalityConstraint!
               =#
          outType
        end

         #= Helper function to mktype
          Transforms a Path into a Path option. =#
        function getOptPath(inPath::Absyn.Path) ::Option{Absyn.Path}
              local outAbsynPathOption::Option{Absyn.Path}

              outAbsynPathOption = begin
                  local p::Absyn.Path
                @match inPath begin
                  Absyn.IDENT(name = "")  => begin
                    NONE()
                  end

                  p  => begin
                    SOME(p)
                  end
                end
              end
          outAbsynPathOption
        end

         #= This function is used to check that a
          protected element is not modified. =#
        function checkProt(inVisibility::SCode.Visibility, inMod::DAE.Mod, inComponentRef::DAE.ComponentRef, info::SourceInfo)
              _ = begin
                  local cref::DAE.ComponentRef
                  local str1::String
                  local str2::String
                @match (inVisibility, inMod, inComponentRef, info) begin
                  (SCode.PUBLIC(__), _, _, _)  => begin
                    ()
                  end

                  (_, DAE.NOMOD(__), _, _)  => begin
                    ()
                  end

                  (_, DAE.MOD(_, _,  nil(), NONE()), _, _)  => begin
                    ()
                  end

                  (SCode.PROTECTED(__), _, cref, _)  => begin
                      str1 = ComponentReference.printComponentRefStr(cref)
                      str2 = Mod.prettyPrintMod(inMod, 0)
                      Error.addSourceMessage(Error.MODIFY_PROTECTED, list(str1, str2), info)
                    ()
                  end
                end
              end
        end

         #= author: LP
          Retrieves the stateSelect value, as defined in DAE,  from an Expression option. =#
        function getStateSelectFromExpOption(inExpExpOption::Option{<:DAE.Exp}) ::Option{DAE.StateSelect}
              local outDAEStateSelectOption::Option{DAE.StateSelect}

              outDAEStateSelectOption = begin
                @match inExpExpOption begin
                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT("never"))))  => begin
                    SOME(DAE.NEVER())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT("avoid"))))  => begin
                    SOME(DAE.AVOID())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT("default"))))  => begin
                    SOME(DAE.DEFAULT())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT("prefer"))))  => begin
                    SOME(DAE.PREFER())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT("always"))))  => begin
                    SOME(DAE.ALWAYS())
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          outDAEStateSelectOption
        end

         #= Returns true if the given submod is a namemod with the same name as the given
          name, otherwise false. =#
        function isSubModNamed(inName::String, inSubMod::DAE.SubMod) ::Bool
              local isNamed::Bool

              isNamed = begin
                  local submod_name::String
                @match (inName, inSubMod) begin
                  (_, DAE.NAMEMOD(ident = submod_name))  => begin
                    stringEqual(inName, submod_name)
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNamed
        end

         #= If the type is an array type this function creates an array of the given
          record, otherwise it just returns the input arguments. =#
        function liftRecordBinding(inType::DAE.Type, inExp::DAE.Exp, inValue::Values.Value) ::Tuple{DAE.Exp, Values.Value}
              local outValue::Values.Value
              local outExp::DAE.Exp

              (outExp, outValue) = begin
                  local dim::DAE.Dimension
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local val::Values.Value
                  local ety::DAE.Type
                  local int_dim::ModelicaInteger
                  local expl::List{DAE.Exp}
                  local vals::List{Values.Value}
                @matchcontinue (inType, inExp, inValue) begin
                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = ty), _, _)  => begin
                      int_dim = Expression.dimensionSize(dim)
                      (exp, val) = liftRecordBinding(ty, inExp, inValue)
                      ety = Types.simplifyType(inType)
                      expl = ListUtil.fill(exp, int_dim)
                      vals = ListUtil.fill(val, int_dim)
                      exp = DAE.ARRAY(ety, true, expl)
                      val = Values.ARRAY(vals, list(int_dim))
                    (exp, val)
                  end

                  _  => begin
                        @match false = Types.isArray(inType)
                      (inExp, inValue)
                  end
                end
              end
          (outExp, outValue)
        end

         #= author: PA
          The topmost instantiation call is treated specially with for instance unconnected connectors.
          This function returns true if the CallingScope indicates the top call. =#
        function isTopCall(inCallingScope::InstTypes.CallingScope) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inCallingScope begin
                  InstTypes.TOP_CALL(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #=  Extracts SCode.Element name. =#
        function extractCurrentName(sele::SCode.Element) ::Tuple{String, SourceInfo}
              local oinfo::SourceInfo
              local ostring::String

              (ostring, oinfo) = begin
                  local path::Absyn.Path
                  local name::String
                  local ret::String
                  local imp::Absyn.Import
                  local info::SourceInfo
                @match sele begin
                  SCode.CLASS(name = name, info = info)  => begin
                    (name, info)
                  end

                  SCode.COMPONENT(name = name, info = info)  => begin
                    (name, info)
                  end

                  SCode.EXTENDS(baseClassPath = path, info = info)  => begin
                      ret = AbsynUtil.pathString(path)
                    (ret, info)
                  end

                  SCode.IMPORT(imp = imp, info = info)  => begin
                      name = AbsynUtil.printImportString(imp)
                    (name, info)
                  end
                end
              end
          (ostring, oinfo)
        end

         #= @author: adrpo
          Reorder the connect equations to have non-expandable connect first:
            connect(non_expandable, non_expandable);
            connect(non_expandable, expandable);
            connect(expandable, non_expandable);
            connect(expandable, expandable); =#
        function reorderConnectEquationsExpandable(cache::FCore.Cache, env::FCore.Graph, inEquations::List{<:SCode.Equation}) ::Tuple{FCore.Cache, List{SCode.Equation}}
              local outEquations::List{SCode.Equation}


              local delst::DoubleEnded.MutableList{SCode.Equation}
              local expandableEqs::List{SCode.Equation}
              local crefLeft::Absyn.ComponentRef
              local crefRight::Absyn.ComponentRef
              local ty1::DAE.Type
              local ty2::DAE.Type

              if if listEmpty(inEquations)
                    true
                  else
                    ! System.getHasExpandableConnectors()
                  end
                outEquations = inEquations
                return (cache, outEquations)
              end
              ErrorExt.setCheckpoint("expandableConnectorsOrder")
              delst = DoubleEnded.fromList(nil)
              expandableEqs = list(eq for eq in inEquations if begin
                 @matchcontinue eq begin
                   SCode.EQUATION(SCode.EQ_CONNECT(crefLeft = crefLeft, crefRight = crefRight))  => begin
                       (_, ty1, _) = Lookup.lookupConnectorVar(env, ComponentReference.toExpCref(crefLeft))
                        #=  type of left var is an expandable connector!
                        =#
                       @match true = Types.isExpandableConnector(ty1)
                       (_, ty2, _) = Lookup.lookupConnectorVar(env, ComponentReference.toExpCref(crefRight))
                        #=  type of right left var is an expandable connector!
                        =#
                       @match true = Types.isExpandableConnector(ty2)
                     true
                   end

                   _  => begin
                         DoubleEnded.push_back(delst, eq)
                       false
                   end
                 end
               end)
              if listEmpty(expandableEqs)
                ErrorExt.delCheckpoint("expandableConnectorsOrder")
                outEquations = inEquations
                return (cache, outEquations)
              end
               #=  Just to preserve referenceEq; does not really matter
               =#
              ErrorExt.rollBack("expandableConnectorsOrder")
               #=  Reorder the connect equations to have non-expandable connect first:
               =#
               #=    connect(non_expandable, non_expandable);
               =#
               #=    connect(non_expandable, expandable);
               =#
               #=    connect(expandable, non_expandable);
               =#
               #=    connect(expandable, expandable);
               =#
               #=  put expandable at the begining
               =#
              DoubleEnded.push_list_front(delst, expandableEqs)
               #=  put expandable at the end
               =#
              DoubleEnded.push_list_back(delst, expandableEqs)
               #=  duplicate expandable to get the union
               =#
              _ = begin
                @match expandableEqs begin
                  _ <| _ <| _  => begin
                      DoubleEnded.push_list_back(delst, expandableEqs)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
               #=  > length 1
               =#
              outEquations = DoubleEnded.toListAndClear(delst)
          (cache, outEquations)
        end

         #= @author: adrpo
          This function will move all the *inner*
          elements first in the given list of elements =#
        function sortInnerFirstTplLstElementMod(inTplLstElementMod::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outTplLstElementMod::List{Tuple{SCode.Element, DAE.Mod}}

              outTplLstElementMod = begin
                  local innerElts::List{Tuple{SCode.Element, DAE.Mod}}
                  local innerouterElts::List{Tuple{SCode.Element, DAE.Mod}}
                  local otherElts::List{Tuple{SCode.Element, DAE.Mod}}
                  local sorted::List{Tuple{SCode.Element, DAE.Mod}}
                  local innerModelicaServices::List{Tuple{SCode.Element, DAE.Mod}}
                  local innerModelica::List{Tuple{SCode.Element, DAE.Mod}}
                  local innerOthers::List{Tuple{SCode.Element, DAE.Mod}}
                   #=  no sorting if we don't have any inner/outer in the model
                   =#
                @matchcontinue inTplLstElementMod begin
                  _  => begin
                      @match false = System.getHasInnerOuterDefinitions()
                    inTplLstElementMod
                  end

                  _  => begin
                      (innerElts, innerouterElts, otherElts) = splitInnerAndOtherTplLstElementMod(inTplLstElementMod)
                      (innerModelicaServices, innerModelica, innerOthers) = splitInners(innerElts, nil, nil, nil)
                      sorted = listAppend(innerModelicaServices, listAppend(innerModelica, listAppend(innerOthers, listAppend(innerouterElts, otherElts))))
                    sorted
                  end
                end
              end
               #=  do sorting only if we have inner-outer
               =#
               #=  split into inner, inner outer and other elements
               =#
               #=  sort the inners to put Modelica types first!
               =#
               #=  put the inner elements first
               =#
               #=  put the innerouter elements second
               =#
          outTplLstElementMod
        end

         #= @author: adrpo
          This function will sort inner into 3 lists:
          *inner* ModelicaServices.*
          *inner* Modelica.*
          *inner* Other.* =#
        function splitInners(inTplLstElementMod::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inAcc1::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inAcc2::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inAcc3::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::Tuple{List{Tuple{SCode.Element, DAE.Mod}}, List{Tuple{SCode.Element, DAE.Mod}}, List{Tuple{SCode.Element, DAE.Mod}}}
              local outOthers::List{Tuple{SCode.Element, DAE.Mod}}
              local outModelica::List{Tuple{SCode.Element, DAE.Mod}}
              local outModelicaServices::List{Tuple{SCode.Element, DAE.Mod}}

              (outModelicaServices, outModelica, outOthers) = begin
                  local rest::List{Tuple{SCode.Element, DAE.Mod}}
                  local acc1::List{Tuple{SCode.Element, DAE.Mod}}
                  local acc2::List{Tuple{SCode.Element, DAE.Mod}}
                  local acc3::List{Tuple{SCode.Element, DAE.Mod}}
                  local e::SCode.Element
                  local m::DAE.Mod
                  local em::Tuple{SCode.Element, DAE.Mod}
                  local p::Absyn.Path
                @matchcontinue (inTplLstElementMod, inAcc1, inAcc2, inAcc3) begin
                  ( nil(), _, _, _)  => begin
                    (listReverse(inAcc1), listReverse(inAcc2), listReverse(inAcc3))
                  end

                  (em <| rest, _, _, _)  => begin
                      e = Util.tuple21(em)
                      @match Absyn.TPATH(p, _) = SCodeUtil.getComponentTypeSpec(e)
                      @match true = stringEq("ModelicaServices", AbsynUtil.pathFirstIdent(p))
                      (acc1, acc2, acc3) = splitInners(rest, _cons(em, inAcc1), inAcc2, inAcc3)
                    (acc1, acc2, acc3)
                  end

                  (em <| rest, _, _, _)  => begin
                      e = Util.tuple21(em)
                      @match Absyn.TPATH(p, _) = SCodeUtil.getComponentTypeSpec(e)
                      @match true = stringEq("Modelica", AbsynUtil.pathFirstIdent(p))
                      (acc1, acc2, acc3) = splitInners(rest, inAcc1, _cons(em, inAcc2), inAcc3)
                    (acc1, acc2, acc3)
                  end

                  (em && (_, _) <| rest, _, _, _)  => begin
                      (acc1, acc2, acc3) = splitInners(rest, inAcc1, inAcc2, _cons(em, inAcc3))
                    (acc1, acc2, acc3)
                  end
                end
              end
          (outModelicaServices, outModelica, outOthers)
        end

         #= @author: adrpo
          Split the elements into inner, inner outer and others =#
        function splitInnerAndOtherTplLstElementMod(inTplLstElementMod::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::Tuple{List{Tuple{SCode.Element, DAE.Mod}}, List{Tuple{SCode.Element, DAE.Mod}}, List{Tuple{SCode.Element, DAE.Mod}}}
              local outOtherTplLstElementMod::List{Tuple{SCode.Element, DAE.Mod}} = nil
              local outInnerOuterTplLstElementMod::List{Tuple{SCode.Element, DAE.Mod}} = nil
              local outInnerTplLstElementMod::List{Tuple{SCode.Element, DAE.Mod}} = nil

              local comp::SCode.Element
              local io::Absyn.InnerOuter

              for e in listReverse(inTplLstElementMod)
                (comp, _) = e
                () = begin
                  @match comp begin
                    SCode.COMPONENT(prefixes = SCode.PREFIXES(innerOuter = io)) where (AbsynUtil.isInner(io))  => begin
                        if AbsynUtil.isOuter(io)
                          outInnerOuterTplLstElementMod = _cons(e, outInnerOuterTplLstElementMod)
                        else
                          outInnerTplLstElementMod = _cons(e, outInnerTplLstElementMod)
                        end
                         #=  inner outer components.
                         =#
                         #=  inner components.
                         =#
                      ()
                    end

                    _  => begin
                           #=  any other components.
                           =#
                          outOtherTplLstElementMod = _cons(e, outOtherTplLstElementMod)
                        ()
                    end
                  end
                end
              end
          (outInnerTplLstElementMod, outInnerOuterTplLstElementMod, outOtherTplLstElementMod)
        end

         #=
        This function splits the Element list into four lists
        1. Class definitions , imports and defineunits
        2. Class-extends class definitions
        3. Extends elements
        4. Components which are ordered by inner/outer, inner first =#
        function splitEltsOrderInnerOuter(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}, List{SCode.Element}, List{SCode.Element}}
              local compElts::List{SCode.Element}
              local extElts::List{SCode.Element}
              local classextendsElts::List{SCode.Element}
              local cdefImpElts::List{SCode.Element}

              (cdefImpElts, classextendsElts, extElts, compElts) = begin
                  local innerComps::List{SCode.Element}
                  local otherComps::List{SCode.Element}
                  local comps::List{SCode.Element}
                  local cdef::SCode.Element
                  local imp::SCode.Element
                  local ext::SCode.Element
                  local io::Absyn.InnerOuter
                @match elts begin
                  _  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(elts)
                      comps = listAppend(innerComps, otherComps)
                    (cdefImpElts, classextendsElts, extElts, comps)
                  end
                end
              end
               #=  put inner elements first in the list of
               =#
               #=  elements so they are instantiated first!
               =#
          (cdefImpElts, classextendsElts, extElts, compElts)
        end

         #=
        This function splits the Element list into four lists
        1. Class definitions , imports and defineunits
        2. Class-extends class definitions
        3. Extends elements
        4. Components =#
        function splitElts(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}, List{SCode.Element}, List{SCode.Element}}
              local compElts::List{SCode.Element} = nil
              local extElts::List{SCode.Element} = nil
              local classextendsElts::List{SCode.Element} = nil
              local cdefImpElts::List{SCode.Element} = nil

              for elt in elts
                _ = begin
                  @match elt begin
                    SCode.CLASS(__)  => begin
                        if begin
                          @match elt.classDef begin
                            SCode.CLASS_EXTENDS(__)  => begin
                              true
                            end

                            _  => begin
                                false
                            end
                          end
                        end
                          classextendsElts = _cons(elt, classextendsElts)
                        else
                          cdefImpElts = _cons(elt, cdefImpElts)
                        end
                         #=  class definitions with class extends
                         =#
                         #=  class definitions without class extends
                         =#
                      ()
                    end

                    SCode.IMPORT(__)  => begin
                         #=  imports
                         =#
                        cdefImpElts = _cons(elt, cdefImpElts)
                      ()
                    end

                    SCode.DEFINEUNIT(__)  => begin
                         #=  units
                         =#
                        cdefImpElts = _cons(elt, cdefImpElts)
                      ()
                    end

                    SCode.EXTENDS(__)  => begin
                         #=  extends elements
                         =#
                        extElts = _cons(elt, extElts)
                      ()
                    end

                    SCode.COMPONENT(__)  => begin
                         #=  components
                         =#
                        compElts = _cons(elt, compElts)
                      ()
                    end
                  end
                end
              end
              cdefImpElts = listReverseInPlace(cdefImpElts)
              classextendsElts = listReverseInPlace(classextendsElts)
              extElts = listReverseInPlace(extElts)
              compElts = listReverseInPlace(compElts)
          (cdefImpElts, classextendsElts, extElts, compElts)
        end

         #=
        This function splits the Element list into these categories:
        1. Imports
        2. Define units and class definitions
        3. Class-extends class definitions
        4. Filtered class extends and imports =#
        function splitEltsNoComponents(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}, List{SCode.Element}, List{SCode.Element}}
              local filtered::List{SCode.Element}
              local classextendsElts::List{SCode.Element}
              local defElts::List{SCode.Element}
              local impElts::List{SCode.Element}

              (impElts, defElts, classextendsElts, filtered) = begin
                  local xs::List{SCode.Element}
                  local elt::SCode.Element
                   #=  empty case
                   =#
                @match elts begin
                   nil()  => begin
                    (nil, nil, nil, nil)
                  end

                  elt && SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)) <| xs  => begin
                      (impElts, defElts, classextendsElts, filtered) = splitEltsNoComponents(xs)
                    (impElts, defElts, _cons(elt, classextendsElts), filtered)
                  end

                  elt && SCode.CLASS(__) <| xs  => begin
                      (impElts, defElts, classextendsElts, filtered) = splitEltsNoComponents(xs)
                    (impElts, _cons(elt, defElts), classextendsElts, _cons(elt, filtered))
                  end

                  elt && SCode.IMPORT(__) <| xs  => begin
                      (impElts, defElts, classextendsElts, filtered) = splitEltsNoComponents(xs)
                    (_cons(elt, impElts), defElts, classextendsElts, filtered)
                  end

                  elt && SCode.DEFINEUNIT(__) <| xs  => begin
                      (impElts, defElts, classextendsElts, filtered) = splitEltsNoComponents(xs)
                    (impElts, _cons(elt, defElts), classextendsElts, _cons(elt, filtered))
                  end

                  elt <| xs  => begin
                      (impElts, defElts, classextendsElts, filtered) = splitEltsNoComponents(xs)
                    (impElts, defElts, classextendsElts, _cons(elt, filtered))
                  end
                end
              end
               #=  class definitions with class extends
               =#
               #=  class definitions without class extends
               =#
               #=  imports
               =#
               #=  units
               =#
               #=  extends and components elements
               =#
          (impElts, defElts, classextendsElts, filtered)
        end

         #=
         @author: adrpo
          Splits elements into these categories:
          1. Class definitions, imports and defineunits
          2. Class-extends class definitions
          3. Extends elements
          4. Inner Components
          5. Any Other Components =#
        function splitEltsInnerAndOther(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}, List{SCode.Element}, List{SCode.Element}, List{SCode.Element}}
              local otherCompElts::List{SCode.Element}
              local innerCompElts::List{SCode.Element}
              local extElts::List{SCode.Element}
              local classextendsElts::List{SCode.Element}
              local cdefImpElts::List{SCode.Element}

              (cdefImpElts, classextendsElts, extElts, innerCompElts, otherCompElts) = begin
                  local res::List{SCode.Element}
                  local xs::List{SCode.Element}
                  local innerComps::List{SCode.Element}
                  local otherComps::List{SCode.Element}
                  local cdef::SCode.Element
                  local imp::SCode.Element
                  local ext::SCode.Element
                  local comp::SCode.Element
                  local io::Absyn.InnerOuter
                   #=  empty case
                   =#
                @match elts begin
                   nil()  => begin
                    (nil, nil, nil, nil, nil)
                  end

                  cdef && SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (cdefImpElts, _cons(cdef, classextendsElts), extElts, innerComps, otherComps)
                  end

                  cdef && SCode.CLASS(__) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (_cons(cdef, cdefImpElts), classextendsElts, extElts, innerComps, otherComps)
                  end

                  imp && SCode.IMPORT(__) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (_cons(imp, cdefImpElts), classextendsElts, extElts, innerComps, otherComps)
                  end

                  imp && SCode.DEFINEUNIT(__) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (_cons(imp, cdefImpElts), classextendsElts, extElts, innerComps, otherComps)
                  end

                  ext && SCode.EXTENDS(__) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (cdefImpElts, classextendsElts, _cons(ext, extElts), innerComps, otherComps)
                  end

                  comp && SCode.COMPONENT(prefixes = SCode.PREFIXES(innerOuter = io)) <| xs  => begin
                      @match true = AbsynUtil.isInner(io)
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (cdefImpElts, classextendsElts, extElts, _cons(comp, innerComps), otherComps)
                  end

                  comp && SCode.COMPONENT(__) <| xs  => begin
                      (cdefImpElts, classextendsElts, extElts, innerComps, otherComps) = splitEltsInnerAndOther(xs)
                    (cdefImpElts, classextendsElts, extElts, innerComps, _cons(comp, otherComps))
                  end
                end
              end
               #=  class definitions with class extends
               =#
               #=  class definitions without class extends
               =#
               #=  imports
               =#
               #=  units
               =#
               #=  extends elements
               =#
               #=  inner components
               =#
               #=  any other components
               =#
          (cdefImpElts, classextendsElts, extElts, innerCompElts, otherCompElts)
        end

         #= @author: adrpo
         this functions puts the component in front of the list if
         is inner or innerouter and at the end of the list otherwise =#
        function orderComponents(inComp::SCode.Element, inCompElts::List{<:SCode.Element}) ::List{SCode.Element}
              local outCompElts::List{SCode.Element}

              outCompElts = begin
                  local compElts::List{SCode.Element}
                   #=  input/output come first!
                   =#
                @match (inComp, inCompElts) begin
                  (SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.INPUT(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(attributes = SCode.ATTR(direction = Absyn.OUTPUT(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(prefixes = SCode.PREFIXES(innerOuter = Absyn.INNER(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(prefixes = SCode.PREFIXES(innerOuter = Absyn.INNER_OUTER(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(attributes = SCode.ATTR(variability = SCode.CONST(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(attributes = SCode.ATTR(variability = SCode.PARAM(__))), _)  => begin
                    _cons(inComp, inCompElts)
                  end

                  (SCode.COMPONENT(__), _)  => begin
                      compElts = listAppend(inCompElts, list(inComp))
                    compElts
                  end
                end
              end
               #=  put inner/outer in front.
               =#
               #=  put constants in front
               =#
               #=  put parameters in front
               =#
               #=  all other append to the end.
               =#
          outCompElts
        end

         #= This function splits the Element list into two lists
        1. Class-extends class definitions
        2. Any other element =#
        function splitClassExtendsElts(elts::List{<:SCode.Element}) ::Tuple{List{SCode.Element}, List{SCode.Element}}
              local outElts::List{SCode.Element}
              local classextendsElts::List{SCode.Element}

              (classextendsElts, outElts) = begin
                  local res::List{SCode.Element}
                  local xs::List{SCode.Element}
                  local cdef::SCode.Element
                @match elts begin
                   nil()  => begin
                    (nil, nil)
                  end

                  cdef && SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)) <| xs  => begin
                      (classextendsElts, res) = splitClassExtendsElts(xs)
                    (_cons(cdef, classextendsElts), res)
                  end

                  cdef <| xs  => begin
                      (classextendsElts, res) = splitClassExtendsElts(xs)
                    (classextendsElts, _cons(cdef, res))
                  end
                end
              end
          (classextendsElts, outElts)
        end

         #= function: addClassdefsToEnv3  =#
        function addClassdefsToEnv3(inCache::FCore.Cache, env::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inMod::Option{<:DAE.Mod}, sele::SCode.Element) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, SCode.Element}
              local osele::SCode.Element
              local outIH::InnerOuter.InstHierarchy
              local oenv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, oenv, outIH, osele) = begin
                  local mo::DAE.Mod
                  local mo2::DAE.Mod
                  local sele2::SCode.Element
                  local cache::FCore.Cache
                  local env2::FCore.Graph
                  local str::String
                  local ih::InstanceHierarchy
                  local lsm::List{DAE.SubMod}
                  local lsm2::List{DAE.SubMod}
                  local pre::Prefix.PrefixType
                @match (inCache, env, inIH, inPrefix, inMod, sele) begin
                  (_, _, _, _, NONE(), _)  => begin
                    fail()
                  end

                  (cache, _, ih, pre, SOME(DAE.MOD(subModLst = lsm)), SCode.CLASS(name = str))  => begin
                      (mo2, _) = extractCorrectClassMod2(lsm, str, nil)
                      @match (cache, env2, ih, (@match SCode.CLASS() = sele2), _) = Inst.redeclareType(cache, env, ih, mo2, sele, pre, ClassInf.MODEL(Absyn.IDENT(str)), true, DAE.NOMOD())
                    (cache, env2, ih, sele2)
                  end
                end
              end
               #=  fprintln(Flags.INST_TRACE, \"Mods in addClassdefsToEnv3: \" + Mod.printModStr(mo) + \" class name: \" + str);
               =#
               #=  fprintln(Flags.INST_TRACE, \"Mods in addClassdefsToEnv3 after extractCorrectClassMod2: \" + Mod.printModStr(mo2) + \" class name: \" + str);
               =#
               #=  TODO: classinf below should be FQ
               =#
          (outCache, oenv, outIH, osele)
        end

         #=  This function extracts a modifier on a specific component.
         Referenced by the name. =#
        function extractCorrectClassMod2(smod::List{<:DAE.SubMod}, name::String, premod::List{<:DAE.SubMod}) ::Tuple{DAE.Mod, List{DAE.SubMod}}
              local restmods::List{DAE.SubMod}
              local omod::DAE.Mod

              (omod, restmods) = begin
                  local mod::DAE.Mod
                  local sub::DAE.SubMod
                  local id::String
                  local rest::List{DAE.SubMod}
                  local rest2::List{DAE.SubMod}
                @match (smod, name, premod) begin
                  ( nil(), _, _)  => begin
                    (DAE.NOMOD(), premod)
                  end

                  (DAE.NAMEMOD(id, mod) <| rest, _, _) where (stringEq(id, name))  => begin
                      rest2 = listAppend(premod, rest)
                    (mod, rest2)
                  end

                  (sub <| rest, _, _)  => begin
                      (mod, rest2) = extractCorrectClassMod2(rest, name, premod)
                    (mod, _cons(sub, rest2))
                  end
                end
              end
          (omod, restmods)
        end

         #= Helper function for traverseModAddFinal =#
        function traverseModAddFinal(mod::SCode.Mod) ::SCode.Mod


              mod = begin
                  local element1::SCode.Element
                  local element2::SCode.Element
                  local each_::SCode.Each
                  local subs1::List{SCode.SubMod}
                  local subs2::List{SCode.SubMod}
                  local eq::Option{Absyn.Exp}
                  local info::SourceInfo
                  local f::SCode.Final
                @matchcontinue mod begin
                  SCode.NOMOD(__)  => begin
                    mod
                  end

                  SCode.REDECL(eachPrefix = each_, element = element1)  => begin
                      element2 = traverseModAddFinal3(element1)
                    if referenceEq(element1, element2)
                          mod
                        else
                          SCode.REDECL(SCode.FINAL(), each_, element2)
                        end
                  end

                  SCode.MOD(f, each_, subs1, eq, info)  => begin
                      subs2 = ListUtil.mapCheckReferenceEq(subs1, traverseModAddFinal4)
                    if valueEq(SCode.FINAL(), f) && referenceEq(subs1, subs2)
                          mod
                        else
                          SCode.MOD(SCode.FINAL(), each_, subs2, eq, info)
                        end
                  end

                  _  => begin
                        Error.addInternalError(getInstanceName(), sourceInfo())
                      fail()
                  end
                end
              end
          mod
        end

         #= Helper function for traverseModAddFinal2 =#
        function traverseModAddFinal3(inElement::SCode.Element) ::SCode.Element
              local outElement::SCode.Element

              outElement = begin
                  local attr::SCode.Attributes
                  local tySpec::Absyn.TypeSpec
                  local mod::SCode.Mod
                  local oldmod::SCode.Mod
                  local name::Ident
                  local vis::SCode.Visibility
                  local prefixes::SCode.Prefixes
                  local cmt::SCode.Comment
                  local cond::Option{Absyn.Exp}
                  local p::Absyn.Path
                  local ann::Option{SCode.Annotation}
                  local info::SourceInfo
                @matchcontinue inElement begin
                  SCode.COMPONENT(name, prefixes, attr, tySpec, oldmod, cmt, cond, info)  => begin
                      mod = traverseModAddFinal(oldmod)
                    if referenceEq(oldmod, mod)
                          inElement
                        else
                          SCode.COMPONENT(name, prefixes, attr, tySpec, mod, cmt, cond, info)
                        end
                  end

                  SCode.IMPORT(__)  => begin
                    inElement
                  end

                  SCode.CLASS(__)  => begin
                    inElement
                  end

                  SCode.EXTENDS(p, vis, oldmod, ann, info)  => begin
                      mod = traverseModAddFinal(oldmod)
                    if referenceEq(oldmod, mod)
                          inElement
                        else
                          SCode.EXTENDS(p, vis, mod, ann, info)
                        end
                  end

                  _  => begin
                        print(" we failed with traverseModAddFinal3\\n")
                      fail()
                  end
                end
              end
          outElement
        end

         #= Helper function for traverseModAddFinal2 =#
        function traverseModAddFinal4(sub::SCode.SubMod) ::SCode.SubMod


              local mod::SCode.Mod

              mod = traverseModAddFinal(sub.mod)
              if ! referenceEq(sub.mod, mod)
                sub.mod = mod
              end
          sub
        end

         #= The function used to modify modifications for non-expanded arrays =#
        function traverseModAddDims(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inMod::SCode.Mod, inInstDims::List{<:List{<:DAE.Dimension}}) ::SCode.Mod
              local outMod::SCode.Mod

              outMod = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local mod::SCode.Mod
                  local mod2::SCode.Mod
                  local inst_dims::InstDims
                  local decDims::List{Absyn.Subscript}
                  local exps::List{List{DAE.Exp}}
                  local aexps::List{List{Absyn.Exp}}
                  local adims::List{Option{Absyn.Exp}}
                @matchcontinue (inCache, inEnv, inPrefix, inMod, inInstDims) begin
                  (_, _, _, mod, _)  => begin
                      @match true = Config.splitArrays()
                    mod
                  end

                  (_, _, _, _,  nil())  => begin
                    inMod
                  end

                  (cache, env, pre, mod, inst_dims)  => begin
                      exps = ListUtil.map(inst_dims, Expression.dimensionsToExps)
                      aexps = ListUtil.mapList(exps, Expression.unelabExp)
                      mod2 = traverseModAddDims4(cache, env, pre, mod, aexps, true)
                    mod2
                  end
                end
              end
               #= If arrays are expanded, no action is needed
               =#
          outMod
        end

         #= Helper function  for traverseModAddDims =#
        function traverseModAddDims4(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inMod::SCode.Mod, inExps::List{<:List{<:Absyn.Exp}}, inIsTop::Bool) ::SCode.Mod
              local outMod::SCode.Mod

              outMod = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local mod::SCode.Mod
                  local f::SCode.Final
                  local submods::List{SCode.SubMod}
                  local submods2::List{SCode.SubMod}
                  local binding::Option{Absyn.Exp}
                  local exps::List{List{Absyn.Exp}}
                  local expOpts::List{Option{Absyn.Exp}}
                  local info::SourceInfo
                @match (inCache, inEnv, inPrefix, inMod, inExps, inIsTop) begin
                  (_, _, _, SCode.NOMOD(__), _, _)  => begin
                    inMod
                  end

                  (_, _, _, SCode.REDECL(__), _, _)  => begin
                    inMod
                  end

                  (cache, env, pre, SCode.MOD(f, SCode.NOT_EACH(__), submods, binding, info), exps, _)  => begin
                      submods2 = traverseModAddDims5(cache, env, pre, submods, exps)
                      binding = insertSubsInBinding(binding, exps)
                    SCode.MOD(f, SCode.NOT_EACH(), submods2, binding, info)
                  end
                end
              end
               #=  Though redeclarations may need some processing as well
               =#
          outMod
        end

         #= Helper function  for traverseModAddDims2 =#
        function traverseModAddDims5(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inMods::List{<:SCode.SubMod}, inExps::List{<:List{<:Absyn.Exp}}) ::List{SCode.SubMod}
              local outMods::List{SCode.SubMod}

              outMods = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local mod::SCode.Mod
                  local mod2::SCode.Mod
                  local smods::List{SCode.SubMod}
                  local smods2::List{SCode.SubMod}
                  local n::Ident
                @match (inCache, inEnv, inPrefix, inMods, inExps) begin
                  (_, _, _,  nil(), _)  => begin
                    nil
                  end

                  (cache, env, pre, SCode.NAMEMOD(n, mod) <| smods, _)  => begin
                      mod2 = traverseModAddDims4(cache, env, pre, mod, inExps, false)
                      smods2 = traverseModAddDims5(cache, env, pre, smods, inExps)
                    _cons(SCode.NAMEMOD(n, mod2), smods2)
                  end
                end
              end
          outMods
        end

        function insertSubsInBinding(inOpt::Option{<:Absyn.Exp}, inExps::List{<:List{<:Absyn.Exp}}) ::Option{Absyn.Exp}
              local outOpt::Option{Absyn.Exp}

              outOpt = begin
                  local exps::List{List{Absyn.Exp}}
                  local e::Absyn.Exp
                  local e2::Absyn.Exp
                  local subs::List{List{Absyn.Subscript}}
                  local vars::List{List{Absyn.Ident}}
                @match (inOpt, inExps) begin
                  (NONE(), _)  => begin
                    NONE()
                  end

                  (SOME(e), exps)  => begin
                      vars = generateUnusedNamesLstCall(e, exps)
                      subs = ListUtil.mapList(vars, stringSub)
                      (e2, _) = AbsynUtil.traverseExp(e, AbsynUtil.crefInsertSubscriptLstLst, subs)
                      e2 = wrapIntoForLst(e2, vars, exps)
                    SOME(e2)
                  end
                end
              end
          outOpt
        end

         #= Generates a list of variable names which are not used in any of expressions.
        The number of variables is the same as the length of input list.
        TODO: Write the REAL function! =#
        function generateUnusedNames(inExp::Absyn.Exp, inList::List{<:Absyn.Exp}) ::List{String}
              local outNames::List{String}

              (outNames, _) = generateUnusedNames2(inList, 1)
          outNames
        end

        function generateUnusedNames2(inList::List{<:Absyn.Exp}, inInt::ModelicaInteger) ::Tuple{List{String}, ModelicaInteger}
              local outInt::ModelicaInteger
              local outNames::List{String}

              (outNames, outInt) = begin
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local s::String
                  local names::List{String}
                  local exps::List{Absyn.Exp}
                @match (inList, inInt) begin
                  ( nil(), i)  => begin
                    (nil, i)
                  end

                  (_ <| exps, i)  => begin
                      s = intString(i)
                      s = "i" + s
                      i1 = i + 1
                      (names, i2) = generateUnusedNames2(exps, i1)
                    (_cons(s, names), i2)
                  end
                end
              end
          (outNames, outInt)
        end

        function generateUnusedNamesLst(inList::List{<:List{<:Absyn.Exp}}, inInt::ModelicaInteger) ::Tuple{List{List{String}}, ModelicaInteger}
              local outInt::ModelicaInteger
              local outNames::List{List{String}}

              (outNames, outInt) = begin
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local names::List{List{String}}
                  local ns::List{String}
                  local exps::List{List{Absyn.Exp}}
                  local e0::List{Absyn.Exp}
                @match (inList, inInt) begin
                  ( nil(), i)  => begin
                    (nil, i)
                  end

                  (e0 <| exps, i)  => begin
                      (ns, i1) = generateUnusedNames2(e0, i)
                      (names, i2) = generateUnusedNamesLst(exps, i1)
                    (_cons(ns, names), i2)
                  end
                end
              end
          (outNames, outInt)
        end

         #= Generates a list of lists of variable names which are not used in any of expressions.
        The structure of lsis of lists is the same as of input list of lists.
        TODO: Write the REAL function! =#
        function generateUnusedNamesLstCall(inExp::Absyn.Exp, inList::List{<:List{<:Absyn.Exp}}) ::List{List{String}}
              local outNames::List{List{String}}

              (outNames, _) = generateUnusedNamesLst(inList, 1)
          outNames
        end

        function stringsSubs(inNames::List{<:String}) ::List{Absyn.Subscript}
              local outSubs::List{Absyn.Subscript}

              outSubs = begin
                  local n::String
                  local names::List{String}
                  local subs::List{Absyn.Subscript}
                @match inNames begin
                   nil()  => begin
                    nil
                  end

                  n <| names  => begin
                      subs = stringsSubs(names)
                    _cons(Absyn.SUBSCRIPT(Absyn.CREF(Absyn.CREF_IDENT(n, nil))), subs)
                  end
                end
              end
          outSubs
        end

        function stringSub(inName::String) ::Absyn.Subscript
              local outSub::Absyn.Subscript

              outSub = begin
                  local n::String
                @match inName begin
                  n  => begin
                    Absyn.SUBSCRIPT(Absyn.CREF(Absyn.CREF_IDENT(n, nil)))
                  end
                end
              end
          outSub
        end

        function wrapIntoFor(inExp::Absyn.Exp, inNames::List{<:String}, inRanges::List{<:Absyn.Exp}) ::Absyn.Exp
              local outExp::Absyn.Exp

              outExp = begin
                  local e::Absyn.Exp
                  local e2::Absyn.Exp
                  local r::Absyn.Exp
                  local n::String
                  local names::List{String}
                  local ranges::List{Absyn.Exp}
                @match (inExp, inNames, inRanges) begin
                  (e,  nil(),  nil())  => begin
                    e
                  end

                  (e, n <| names, r <| ranges)  => begin
                      e2 = wrapIntoFor(e, names, ranges)
                    Absyn.CALL(Absyn.CREF_IDENT("array", nil), Absyn.FOR_ITER_FARG(e2, Absyn.COMBINE(), list(Absyn.ITERATOR(n, NONE(), SOME(Absyn.RANGE(Absyn.INTEGER(1), NONE(), r))))))
                  end
                end
              end
          outExp
        end

        function wrapIntoForLst(inExp::Absyn.Exp, inNames::List{<:List{<:String}}, inRanges::List{<:List{<:Absyn.Exp}}) ::Absyn.Exp
              local outExp::Absyn.Exp

              outExp = begin
                  local e::Absyn.Exp
                  local e2::Absyn.Exp
                  local e3::Absyn.Exp
                  local n::List{String}
                  local names::List{List{String}}
                  local r::List{Absyn.Exp}
                  local ranges::List{List{Absyn.Exp}}
                @match (inExp, inNames, inRanges) begin
                  (e,  nil(),  nil())  => begin
                    e
                  end

                  (e, n <| names, r <| ranges)  => begin
                      e2 = wrapIntoForLst(e, names, ranges)
                      e3 = wrapIntoFor(e2, n, r)
                    e3
                  end
                end
              end
          outExp
        end

        function componentHasCondition(component::Tuple{<:SCode.Element, DAE.Mod}) ::Bool
              local hasCondition::Bool

              hasCondition = begin
                @match component begin
                  (SCode.COMPONENT(condition = SOME(_)), _)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          hasCondition
        end

        function instElementCondExp(inCache::FCore.Cache, inEnv::FCore.Graph, component::SCode.Element, prefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{Option{Bool}, FCore.Cache}
              local outCache::FCore.Cache
              local outCondValue::Option{Bool}

              (outCondValue, outCache) = begin
                  local name::String
                  local cond_exp::Absyn.Exp
                  local cond_val::Bool
                  local cache::FCore.Cache
                @matchcontinue component begin
                  SCode.COMPONENT(condition = SOME(cond_exp))  => begin
                      (cond_val, cache) = instConditionalDeclaration(inCache, inEnv, cond_exp, prefix, info)
                    (SOME(cond_val), cache)
                  end

                  SCode.COMPONENT(condition = SOME(_))  => begin
                    (NONE(), inCache)
                  end

                  _  => begin
                      (SOME(true), inCache)
                  end
                end
              end
          (outCondValue, outCache)
        end

        function instConditionalDeclaration(inCache::FCore.Cache, inEnv::FCore.Graph, inCondition::Absyn.Exp, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{Bool, FCore.Cache}
              local outCache::FCore.Cache
              local outIsConditional::Bool

              local cache::FCore.Cache
              local e::DAE.Exp
              local t::DAE.Type
              local c::DAE.Const
              local is_bool::Bool
              local is_param::Bool
              local b::Bool
              local val::Values.Value

               #=  Elaborate the conditional expression.
               =#
              @match (outCache, e, DAE.PROP(type_ = t, constFlag = c)) = Static.elabExp(inCache, inEnv, inCondition, false, false, inPrefix, inInfo)
               #=  The expression must be of boolean type.
               =#
              if ! Types.isBoolean(t)
                Error.addSourceMessageAndFail(Error.IF_CONDITION_TYPE_ERROR, list(Dump.printExpStr(inCondition), Types.unparseTypeNoAttr(t)), inInfo)
              end
               #=  The expression must be a parameter expression that can be evaluated at compile-time.
               =#
              if ! Types.isParameterOrConstant(c)
                Error.addSourceMessageAndFail(Error.COMPONENT_CONDITION_VARIABILITY, list(Dump.printExpStr(inCondition)), inInfo)
              end
               #=  If it is a boolean parameter expression, try to evaluate it.
               =#
              (outCache, val) = Ceval.ceval(outCache, inEnv, e, false, Absyn.MSG(inInfo), 0)
              outIsConditional = begin
                @match val begin
                  Values.BOOL(b)  => begin
                    b
                  end

                  Values.EMPTY(__)  => begin
                      if ! Config.getGraphicsExpMode()
                        Error.addSourceMessage(Error.CONDITIONAL_EXP_WITHOUT_VALUE, list(Dump.printExpStr(inCondition)), inInfo)
                        fail()
                      end
                    true
                  end

                  _  => begin
                        Error.addInternalError("InstUtil.instConditionalDeclaration got unexpected value " + ValuesUtil.valString(val), sourceInfo())
                      fail()
                  end
                end
              end
               #=  Randomly pick a default for graphics mode...
               =#
          (outIsConditional, outCache)
        end

         #= Propagate ClassPrefix, i.e. variability to a component.
         This is needed to make sure that e.g. a parameter does
         not generate an equation but a binding. =#
        function propagateClassPrefix(attr::SCode.Attributes, pre::Prefix.PrefixType) ::SCode.Attributes
              local outAttr::SCode.Attributes

              outAttr = begin
                  local ad::Absyn.ArrayDim
                  local ct::SCode.ConnectorType
                  local dir::Absyn.Direction
                  local prl::SCode.Parallelism
                  local vt::SCode.Variability
                  local isf::Absyn.IsField
                   #=  if classprefix is variable, keep component variability
                   =#
                @match (attr, pre) begin
                  (_, Prefix.PREFIX(_, Prefix.CLASSPRE(SCode.VAR(__))))  => begin
                    attr
                  end

                  (SCode.ATTR(variability = SCode.CONST(__)), _)  => begin
                    attr
                  end

                  (SCode.ATTR(ad, ct, prl, _, dir, isf), Prefix.PREFIX(_, Prefix.CLASSPRE(vt)))  => begin
                    SCode.ATTR(ad, ct, prl, vt, dir, isf)
                  end

                  _  => begin
                      attr
                  end
                end
              end
               #=  if variability is constant, do not override it!
               =#
               #=  if classprefix is parameter or constant, override component variability
               =#
               #=  anything else
               =#
          outAttr
        end

         #= help function to instBinding.
         If first arg is true, it returns the constant expression found in Value option.
         This is used to ensure that e.g. stateSelect attribute gets a constant value
         and not a parameter expression. =#
        function checkUseConstValue(useConstValue::Bool, ie::DAE.Exp, v::Option{<:Values.Value}) ::DAE.Exp
              local outE::DAE.Exp

              outE = begin
                  local val::Values.Value
                  local e::DAE.Exp
                @matchcontinue (useConstValue, ie, v) begin
                  (false, e, _)  => begin
                    e
                  end

                  (true, _, SOME(val))  => begin
                      e = ValuesUtil.valueExp(val)
                    e
                  end

                  (_, e, _)  => begin
                    e
                  end
                end
              end
          outE
        end

        function propagateAbSCDirection(inVariability::SCode.Variability, inAttributes::SCode.Attributes, inClassAttributes::Option{<:SCode.Attributes}, inInfo::SourceInfo) ::SCode.Attributes
              local outAttributes::SCode.Attributes

              outAttributes = begin
                  local dir::Absyn.Direction
                @match (inVariability, inAttributes, inClassAttributes, inInfo) begin
                  (SCode.CONST(__), _, _, _)  => begin
                    inAttributes
                  end

                  (SCode.PARAM(__), _, _, _)  => begin
                    inAttributes
                  end

                  _  => begin
                        @match SCode.ATTR(direction = dir) = inAttributes
                        dir = propagateAbSCDirection2(dir, inClassAttributes, inInfo)
                      SCodeUtil.setAttributesDirection(inAttributes, dir)
                  end
                end
              end
          outAttributes
        end

         #=
        Author BZ 2008-05
        This function merged derived SCode.Attributes with the current input SCode.Attributes. =#
        function propagateAbSCDirection2(v1::Absyn.Direction, optDerAttr::Option{<:SCode.Attributes}, inInfo::SourceInfo) ::Absyn.Direction
              local v3::Absyn.Direction

              v3 = begin
                  local v2::Absyn.Direction
                @match (v1, optDerAttr, inInfo) begin
                  (_, NONE(), _)  => begin
                    v1
                  end

                  (Absyn.BIDIR(__), SOME(SCode.ATTR(direction = v2)), _)  => begin
                    v2
                  end

                  (_, SOME(SCode.ATTR(direction = Absyn.BIDIR(__))), _)  => begin
                    v1
                  end

                  (_, SOME(SCode.ATTR(direction = v2)), _)  => begin
                      equality(v1, v2)
                    v1
                  end

                  _  => begin
                        print(" failure in propagateAbSCDirection2, Absyn.DIRECTION mismatch")
                        Error.addSourceMessage(Error.COMPONENT_INPUT_OUTPUT_MISMATCH, list("", ""), inInfo)
                      fail()
                  end
                end
              end
          v3
        end

        function makeCrefBaseType(inBaseType::DAE.Type, inDimensions::List{<:List{<:DAE.Dimension}}) ::DAE.Type
              local outType::DAE.Type

              outType = Types.simplifyType(makeCrefBaseType2(inBaseType, inDimensions))
          outType
        end

        function makeCrefBaseType2(inBaseType::DAE.Type, inDimensions::List{<:List{<:DAE.Dimension}}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                   #=  Types extending basic type has dimensions already added
                   =#
                   #=  adrpo: not true, see PowerSystems library for example
                   =#
                   #=  type ReferenceAngle extends .Modelica.SIunits.Angle; some equalityConstraint function end ReferenceAngle;
                   =#
                   #=  used like: ReferenceAngle[x] theta in a connector
                   =#
                @matchcontinue (inBaseType, inDimensions) begin
                  (DAE.T_SUBTYPE_BASIC(complexType = ty), _)  => begin
                      @match false = listEmpty(Types.getDimensions(ty))
                    ty
                  end

                  (_,  nil())  => begin
                    inBaseType
                  end

                  _  => begin
                        dims = ListUtil.last(inDimensions)
                        ty = Expression.liftArrayLeftList(inBaseType, dims)
                      ty
                  end
                end
              end
               #=  check if it has any dimensions
               =#
          outType
        end

         #= Author: BZ, 2009-07
          Get Absyn.ComponentRefs from dimension in SCode.COMPONENT =#
        function getCrefFromCompDim(inEle::SCode.Element) ::List{Absyn.ComponentRef}
              local cref::List{Absyn.ComponentRef}

              cref = begin
                  local ads::List{Absyn.Subscript}
                @matchcontinue inEle begin
                  SCode.COMPONENT(attributes = SCode.ATTR(arrayDims = ads))  => begin
                    AbsynUtil.getCrefsFromSubs(ads, true, true)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          cref
        end

         #=
          author: PA
          Return all variables in a conditional component clause.
          Done to instantiate components referenced in other components, See also getCrefFromMod and
          updateComponentsInEnv. =#
        function getCrefFromCond(cond::Option{<:Absyn.Exp}) ::List{Absyn.ComponentRef}
              local crefs::List{Absyn.ComponentRef}

              crefs = begin
                  local e::Absyn.Exp
                @match cond begin
                  NONE()  => begin
                    nil
                  end

                  SOME(e)  => begin
                    AbsynUtil.getCrefFromExp(e, true, true)
                  end
                end
              end
          crefs
        end

         #=
        For components that already have been visited by updateComponentsInEnv, they must be instantiated without
        modifiers to prevent infinite recursion. However, parameters and constants may not have recursive definitions.
        So we print errors for those instead. =#
        function checkVariabilityOfUpdatedComponent(variability::SCode.Variability, cref::Absyn.ComponentRef)
              _ = begin
                @match (variability, cref) begin
                  (SCode.VAR(__), _)  => begin
                    ()
                  end

                  (SCode.DISCRETE(__), _)  => begin
                    ()
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #= /* Doesn't work anyway right away
                      crefStr = AbsynUtil.printComponentRefStr(cref);
                      varStr = SCodeDump.variabilityString(variability);
                      Error.addMessage(Error.CIRCULAR_PARAM,{crefStr,varStr});*/ =#
        end

         #=
        This function modifies equations into bindings for parameters =#
        function propagateBinding(inVarsDae::DAE.DAElist, inEquationsDae::DAE.DAElist #= Note: functions from here are not considered =#) ::DAE.DAElist
              local outVarsDae::DAE.DAElist

              local vars::List{DAE.Element}
              local vars1::List{DAE.Element}
              local equations::List{DAE.Element}
              local equations1::List{DAE.Element}
              local v1::DAE.Element
              local i::ModelicaInteger
              local is::List{ModelicaInteger}
              local e::DAE.Exp
              local cr::DAE.ComponentRef
              local path::Absyn.Path

              @match DAE.DAE(vars) = inVarsDae
              @match DAE.DAE(equations) = inEquationsDae
              if listEmpty(vars) || listEmpty(equations)
                outVarsDae = inVarsDae
                return outVarsDae
              end
              vars1 = nil
              is = nil
              for v in vars
                v1 = begin
                  @matchcontinue v begin
                    v1 && DAE.VAR(__)  => begin
                        (e, i) = findCorrespondingBinding(v1.componentRef, equations)
                        v1.binding = SOME(e)
                        is = _cons(i, is)
                      v1
                    end

                    _  => begin
                        v
                    end
                  end
                end
                vars1 = _cons(v1, vars1)
              end
              vars1 = listReverse(vars1)
              equations1 = ListUtil.deletePositions(equations, is)
              equations1 = list(DAEUtil.moveElementToInitialSection(eq) for eq in equations)
              i = 0
              for eq in equations1
                _ = begin
                  @match eq begin
                    DAE.INITIALEQUATION(exp1 = DAE.CREF(ty = DAE.T_COMPLEX(__)), exp2 = DAE.CALL(path = path)) where (AbsynUtil.pathLastIdent(path) == "constructor")  => begin
                         #=  Don't duplicate constructor calls
                         =#
                        is = _cons(i, is)
                      ()
                    end

                    DAE.INITIAL_COMPLEX_EQUATION(lhs = DAE.CREF(componentRef = cr))  => begin
                        vars1 = list(begin
                          @match v begin
                            DAE.VAR(binding = SOME(_)) where (ComponentReference.crefPrefixOf(cr, v.componentRef))  => begin
                                is = _cons(i, is)
                              v
                            end

                            DAE.VAR(binding = NONE()) where (ComponentReference.crefPrefixOf(cr, v.componentRef))  => begin
                                 #=  Moving parameter bindings into initial equation section means we need to force fixed=false...
                                 =#
                                v.variableAttributesOption = DAEUtil.setFixedAttr(v.variableAttributesOption, SOME(DAE.BCONST(false)))
                                Error.addSourceMessage(Error.MOVING_PARAMETER_BINDING_TO_INITIAL_EQ_SECTION, list(ComponentReference.printComponentRefStr(v.componentRef)), eq.source.info)
                              v
                            end

                            _  => begin
                                v
                            end
                          end
                        end for v in vars1)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
                i = i + 1
              end
               #= /* algorithm print(anyString(eq)); */ =#
              equations1 = ListUtil.deletePositions(equations1, is)
              outVarsDae = DAE.DAE(listAppend(equations1, vars1))
          outVarsDae
        end

         #=
        Helper function for propagateBinding =#
        function findCorrespondingBinding(inCref::DAE.ComponentRef, inEquations::List{<:DAE.Element}, i::ModelicaInteger = 0) ::Tuple{DAE.Exp, ModelicaInteger}

              local outExp::DAE.Exp

              outExp = begin
                  local cref::DAE.ComponentRef
                  local cref2::DAE.ComponentRef
                  local cref3::DAE.ComponentRef
                  local e::DAE.Exp
                  local equations::List{DAE.Element}
                @match (inCref, inEquations) begin
                  (cref, DAE.DEFINE(componentRef = cref2, exp = e) <| _) where (ComponentReference.crefEqual(cref, cref2))  => begin
                    e
                  end

                  (cref, DAE.EQUATION(exp = DAE.CREF(cref2, _), scalar = e) <| _) where (ComponentReference.crefEqual(cref, cref2))  => begin
                    e
                  end

                  (cref, DAE.EQUEQUATION(cr1 = cref2, cr2 = cref3) <| _) where (ComponentReference.crefEqual(cref, cref2))  => begin
                    Expression.crefExp(cref3)
                  end

                  (cref, DAE.COMPLEX_EQUATION(lhs = DAE.CREF(cref2, _), rhs = e) <| _) where (ComponentReference.crefEqual(cref, cref2))  => begin
                    e
                  end

                  (cref, _ <| equations)  => begin
                      (outExp, i) = findCorrespondingBinding(cref, equations, i + 1)
                    outExp
                  end
                end
              end
          (outExp, i)
        end

        function isPartial(partialPrefix::SCode.Partial, mods::DAE.Mod) ::SCode.Partial
              local outPartial::SCode.Partial

              outPartial = begin
                @match (partialPrefix, mods) begin
                  (SCode.PARTIAL(__), DAE.NOMOD(__))  => begin
                    SCode.PARTIAL()
                  end

                  _  => begin
                      SCode.NOT_PARTIAL()
                  end
                end
              end
          outPartial
        end

        function isFunctionInput(classState::ClassInf.SMNode, direction::Absyn.Direction) ::Bool
              local functionInput::Bool

              functionInput = begin
                @match (classState, direction) begin
                  (ClassInf.FUNCTION(__), Absyn.INPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          functionInput
        end

         #= This function extracts the comment section from a list of elements. =#
        function extractComment(elts::List{<:DAE.Element}) ::SCode.Comment
              local cmt::SCode.Comment = SCode.COMMENT(NONE(), NONE())

              for elt in elts
                _ = begin
                  @match elt begin
                    DAE.COMMENT(cmt = cmt)  => begin
                        return
                      fail()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
          cmt
        end

         #= This function merges two comments together. The rule is that the string
          comment is taken from the first comment, and the annotations from both
          comments are merged. =#
        function mergeClassComments(comment1::SCode.Comment, comment2::SCode.Comment) ::SCode.Comment
              local outComment::SCode.Comment

              outComment = begin
                  local ann1::Option{SCode.Annotation}
                  local ann2::Option{SCode.Annotation}
                  local ann::Option{SCode.Annotation}
                  local str1::Option{String}
                  local str2::Option{String}
                  local str::Option{String}
                  local cmt::Option{SCode.Comment}
                  local mods1::List{SCode.SubMod}
                  local mods2::List{SCode.SubMod}
                  local mods::List{SCode.SubMod}
                  local info::SourceInfo
                @matchcontinue (comment1, comment2) begin
                  (SCode.COMMENT(SOME(SCode.ANNOTATION(SCode.MOD(subModLst = mods1, info = info))), str1), SCode.COMMENT(SOME(SCode.ANNOTATION(SCode.MOD(subModLst = mods2))), str2))  => begin
                      str = if isSome(str1)
                            str1
                          else
                            str2
                          end
                      mods = listAppend(mods1, mods2)
                    SCode.COMMENT(SOME(SCode.ANNOTATION(SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), mods, NONE(), info))), str)
                  end

                  (SCode.COMMENT(ann1, str1), SCode.COMMENT(ann2, str2))  => begin
                      str = if isSome(str1)
                            str1
                          else
                            str2
                          end
                      ann = if isSome(ann1)
                            ann1
                          else
                            ann2
                          end
                    SCode.COMMENT(ann, str)
                  end
                end
              end
          outComment
        end

        function makeNonExpSubscript(inSubscript::DAE.Subscript) ::DAE.Subscript
              local outSubscript::DAE.Subscript

              outSubscript = begin
                  local e::DAE.Exp
                  local subscript::DAE.Subscript
                @match inSubscript begin
                  DAE.INDEX(e)  => begin
                    DAE.WHOLE_NONEXP(e)
                  end

                  subscript && DAE.WHOLE_NONEXP(_)  => begin
                    subscript
                  end
                end
              end
          outSubscript
        end

         #= Looks at the annotations of an SCode.Element to create the function attributes,
        i.e. Inline and Purity =#
        function getFunctionAttributes(cl::SCode.Element, vl::List{<:DAE.Var}, inheritedComment::SCode.Comment) ::DAE.FunctionAttributes
              local attr::DAE.FunctionAttributes

              attr = begin
                  local restriction::SCode.Restriction
                  local isOpenModelicaPure::Bool
                  local isImpure::Bool
                  local hasOutVars::Bool
                  local unboxArgs::Bool
                  local isBuiltin::DAE.FunctionBuiltin
                  local inlineType::DAE.InlineType
                  local name::String
                  local inVars::List{DAE.Var}
                  local outVars::List{DAE.Var}
                @matchcontinue cl begin
                  SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(isImpure)))  => begin
                      inVars = ListUtil.select(vl, Types.isInputVar)
                      outVars = ListUtil.select(vl, Types.isOutputVar)
                      name = SCodeUtil.isBuiltinFunction(cl, ListUtil.map(inVars, Types.varName), ListUtil.map(outVars, Types.varName))
                      inlineType = commentIsInlineFunc(inheritedComment)
                      isOpenModelicaPure = ! SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_Impure")
                      isImpure = if isImpure
                            true
                          else
                            SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__ModelicaAssociation_Impure")
                          end
                      unboxArgs = SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_UnboxArguments")
                    DAE.FUNCTION_ATTRIBUTES(inlineType, isOpenModelicaPure, isImpure, false, DAE.FUNCTION_BUILTIN(SOME(name), unboxArgs), DAE.FP_NON_PARALLEL())
                  end

                  SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_PARALLEL_FUNCTION(__)))  => begin
                      inVars = ListUtil.select(vl, Types.isInputVar)
                      outVars = ListUtil.select(vl, Types.isOutputVar)
                      name = SCodeUtil.isBuiltinFunction(cl, ListUtil.map(inVars, Types.varName), ListUtil.map(outVars, Types.varName))
                      inlineType = commentIsInlineFunc(inheritedComment)
                      isOpenModelicaPure = ! SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_Impure")
                      unboxArgs = SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_UnboxArguments")
                    DAE.FUNCTION_ATTRIBUTES(inlineType, isOpenModelicaPure, false, false, DAE.FUNCTION_BUILTIN(SOME(name), unboxArgs), DAE.FP_PARALLEL_FUNCTION())
                  end

                  SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_PARALLEL_FUNCTION(__)))  => begin
                      inlineType = commentIsInlineFunc(inheritedComment)
                      isBuiltin = if SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_BuiltinPtr")
                            DAE.FUNCTION_BUILTIN_PTR()
                          else
                            DAE.FUNCTION_NOT_BUILTIN()
                          end
                      isOpenModelicaPure = ! SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_Impure")
                    DAE.FUNCTION_ATTRIBUTES(inlineType, isOpenModelicaPure, false, false, isBuiltin, DAE.FP_PARALLEL_FUNCTION())
                  end

                  SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_KERNEL_FUNCTION(__)))  => begin
                    DAE.FUNCTION_ATTRIBUTES(DAE.NO_INLINE(), true, false, false, DAE.FUNCTION_NOT_BUILTIN(), DAE.FP_KERNEL_FUNCTION())
                  end

                  SCode.CLASS(restriction = restriction)  => begin
                      inlineType = commentIsInlineFunc(inheritedComment)
                      hasOutVars = ListUtil.exist(vl, Types.isOutputVar)
                      isBuiltin = if SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_BuiltinPtr")
                            DAE.FUNCTION_BUILTIN_PTR()
                          else
                            DAE.FUNCTION_NOT_BUILTIN()
                          end
                      isOpenModelicaPure = ! SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__OpenModelica_Impure")
                      isImpure = SCodeUtil.commentHasBooleanNamedAnnotation(inheritedComment, "__ModelicaAssociation_Impure") || SCodeUtil.isRestrictionImpure(restriction, hasOutVars || Config.languageStandardAtLeast(Config.LanguageStandard.S3_3))
                    DAE.FUNCTION_ATTRIBUTES(inlineType, isOpenModelicaPure, isImpure, false, isBuiltin, DAE.FP_NON_PARALLEL())
                  end
                end
              end
               #= parallel functions: There are some builtin functions.
               =#
               #= parallel functions: non-builtin
               =#
               #= kernel functions: never builtin and never inlined.
               =#
               #=  In Modelica 3.2 and before, external functions with side-effects are not marked
               =#
          attr
        end

         #= Verifies that an element of a function is correct, i.e.
        public input/output, protected variable/parameter/constant or algorithm section =#
        function checkFunctionElement(elt::DAE.Element, isExternal::Bool, info::SourceInfo)
              _ = begin
                  local str::String
                   #=  Variables have already been checked in checkFunctionVar.
                   =#
                @match (elt, isExternal, info) begin
                  (DAE.VAR(__), _, _)  => begin
                    ()
                  end

                  (DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(DAE.STMT_ASSIGN(exp = DAE.METARECORDCALL(__)) <|  nil())), _, _)  => begin
                    ()
                  end

                  (DAE.ALGORITHM(__), false, _)  => begin
                    ()
                  end

                  (DAE.COMMENT(__), _, _)  => begin
                    ()
                  end

                  _  => begin
                        str = DAEDump.dumpElementsStr(list(elt))
                        Error.addSourceMessage(Error.FUNCTION_ELEMENT_WRONG_KIND, list(str), info)
                      fail()
                  end
                end
              end
               #=  We need to know the inlineType to make a good notification
               =#
               #=  Error.addSourceMessage(true,Error.COMPILER_NOTIFICATION, {\"metarecordcall\"}, info);
               =#
        end

        function printElementAndModList(inLstElAndMod::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::String
              local outStr::String

              outStr = begin
                  local e::SCode.Element
                  local m::DAE.Mod
                  local rest::List{Tuple{SCode.Element, DAE.Mod}}
                  local s1::String
                  local s2::String
                  local s3::String
                  local s::String
                @match inLstElAndMod begin
                   nil()  => begin
                    ""
                  end

                  (e, m) <| rest  => begin
                      s1 = SCodeDump.unparseElementStr(e, SCodeDump.defaultOptions)
                      s2 = Mod.printModStr(m)
                      s3 = printElementAndModList(rest)
                      s = "Element:\\n" + s1 + "\\nModifier: " + s2 + "\\n" + s3
                    s
                  end
                end
              end
          outStr
        end

        function splitClassDefsAndComponents(inLstElAndMod::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::Tuple{List{Tuple{SCode.Element, DAE.Mod}}, List{Tuple{SCode.Element, DAE.Mod}}}
              local outComponentDefs::List{Tuple{SCode.Element, DAE.Mod}}
              local outClassDefs::List{Tuple{SCode.Element, DAE.Mod}}

              (outClassDefs, outComponentDefs) = begin
                  local e::SCode.Element
                  local m::DAE.Mod
                  local rest::List{Tuple{SCode.Element, DAE.Mod}}
                  local clsdefs::List{Tuple{SCode.Element, DAE.Mod}}
                  local compdefs::List{Tuple{SCode.Element, DAE.Mod}}
                  local s1::String
                  local s2::String
                  local s3::String
                  local s::String
                @match inLstElAndMod begin
                   nil()  => begin
                    (nil, nil)
                  end

                  (e && SCode.COMPONENT(__), m) <| rest  => begin
                      (clsdefs, compdefs) = splitClassDefsAndComponents(rest)
                    (clsdefs, _cons((e, m), compdefs))
                  end

                  (e, m) <| rest  => begin
                      (clsdefs, compdefs) = splitClassDefsAndComponents(rest)
                    (_cons((e, m), clsdefs), compdefs)
                  end
                end
              end
               #=  components
               =#
               #=  classes and others
               =#
          (outClassDefs, outComponentDefs)
        end

         #= this function selects the correct modifiers for class/binding
         i.e.
         fromMerging: redeclare constant Boolean standardOrderComponents = tru
         fromRedeclareType: = true
         take binding to be the second and the other one you make NOMOD
         as it doesn't belong in the Boolean class.
         Weird Modelica.Media stuff =#
        function selectModifiers(fromMerging::DAE.Mod, fromRedeclareType::DAE.Mod, typePath::Absyn.Path) ::Tuple{DAE.Mod, DAE.Mod}
              local classMod::DAE.Mod
              local bindingMod::DAE.Mod

              (bindingMod, classMod) = begin
                  local mod::DAE.Mod
                   #=  if the thing we got from merging is a redeclare
                   =#
                   #=  for a component of a basic type, skip it!
                   =#
                @matchcontinue (fromMerging, fromRedeclareType, typePath) begin
                  (_, _, _)  => begin
                      @match true = redeclareBasicType(fromMerging)
                    (fromRedeclareType, fromRedeclareType)
                  end

                  _  => begin
                      (fromMerging, fromRedeclareType)
                  end
                end
              end
               #=  any other is fine!
               =#
          (bindingMod, classMod)
        end

        function redeclareBasicType(mod::DAE.Mod) ::Bool
              local isRedeclareOfBasicType::Bool

              isRedeclareOfBasicType = begin
                  local name::String
                  local path::Absyn.Path
                   #=  you cannot redeclare a basic type, only the properties and the binding, i.e.
                   =#
                   #=  redeclare constant Boolean standardOrderComponents = true
                   =#
                @matchcontinue mod begin
                  DAE.REDECL(element = SCode.COMPONENT(typeSpec = Absyn.TPATH(path = path)))  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                      name = AbsynUtil.pathFirstIdent(path)
                      @match true = listMember(name, list("Real", "Integer", "Boolean", "String", "Clock"))
                    true
                  end

                  DAE.REDECL(element = SCode.COMPONENT(typeSpec = Absyn.TPATH(path = path)))  => begin
                      @match false = Config.synchronousFeaturesAllowed()
                      name = AbsynUtil.pathFirstIdent(path)
                      @match true = listMember(name, list("Real", "Integer", "Boolean", "String"))
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
               #=  BTH
               =#
          isRedeclareOfBasicType
        end

         #= * Does tail recursion optimization =#
        function optimizeFunctionCheckForLocals(path::Absyn.Path, inElts::List{<:DAE.Element}, oalg::Option{<:DAE.Element}, acc::List{<:DAE.Element}, invars::List{<:String}, outvars::List{<:String}) ::List{DAE.Element}
              local outElts::List{DAE.Element}

              outElts = begin
                  local stmts::List{DAE.Statement}
                  local elt::DAE.Element
                  local elt1::DAE.Element
                  local elt2::DAE.Element
                  local source::DAE.ElementSource
                  local str::String
                  local name::String
                  local elts::List{DAE.Element}
                   #=  No algorithm section; allowed
                   =#
                @match (path, inElts, oalg, acc, invars, outvars) begin
                  (_,  nil(), NONE(), _, _, _)  => begin
                    listReverse(acc)
                  end

                  (_,  nil(), SOME(DAE.ALGORITHM(DAE.ALGORITHM_STMTS(stmts), source)), _, _, _)  => begin
                      stmts = optimizeLastStatementTail(path, stmts, listReverse(invars), listReverse(outvars), nil)
                    listReverse(_cons(DAE.ALGORITHM(DAE.ALGORITHM_STMTS(stmts), source), acc))
                  end

                  (_, DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS( nil())) <| elts, _, _, _, _)  => begin
                    optimizeFunctionCheckForLocals(path, elts, oalg, acc, invars, outvars)
                  end

                  (_, elt1 && DAE.ALGORITHM(source = source) <| elts, SOME(elt2), _, _, _)  => begin
                      str = AbsynUtil.pathString(path)
                      if ! Config.acceptMetaModelicaGrammar()
                        Error.addSourceMessage(Error.FUNCTION_MULTIPLE_ALGORITHM, list(str), ElementSource.getElementSourceFileInfo(source))
                      end
                    optimizeFunctionCheckForLocals(path, elts, SOME(elt1), _cons(elt2, acc), invars, outvars)
                  end

                  (_, elt && DAE.ALGORITHM(__) <| elts, NONE(), _, _, _)  => begin
                    optimizeFunctionCheckForLocals(path, elts, SOME(elt), acc, invars, outvars)
                  end

                  (_, elt && DAE.VAR(componentRef = DAE.CREF_IDENT(ident = name), direction = DAE.OUTPUT(__)) <| elts, _, _, _, _)  => begin
                    optimizeFunctionCheckForLocals(path, elts, oalg, _cons(elt, acc), invars, _cons(name, outvars))
                  end

                  (_, elt && DAE.VAR(componentRef = DAE.CREF_IDENT(ident = name), direction = DAE.INPUT(__)) <| elts, _, _, _, _)  => begin
                    optimizeFunctionCheckForLocals(path, elts, oalg, _cons(elt, acc), _cons(name, invars), outvars)
                  end

                  (_, elt <| elts, _, _, _, _)  => begin
                    optimizeFunctionCheckForLocals(path, elts, oalg, _cons(elt, acc), invars, outvars)
                  end
                end
              end
          outElts
        end

        function optimizeLastStatementTail(path::Absyn.Path, inStmts::List{<:DAE.Statement}, invars::List{<:String}, outvars::List{<:String}, acc::List{<:DAE.Statement}) ::List{DAE.Statement}
              local ostmts::List{DAE.Statement}

              ostmts = begin
                  local stmt::DAE.Statement
                  local stmts::List{DAE.Statement}
                @match (path, inStmts, invars, outvars, acc) begin
                  (_, stmt <|  nil(), _, _, _)  => begin
                      stmt = optimizeStatementTail(path, stmt, invars, outvars)
                    listReverse(_cons(stmt, acc))
                  end

                  (_, stmt <| stmts, _, _, _)  => begin
                    optimizeLastStatementTail(path, stmts, invars, outvars, _cons(stmt, acc))
                  end
                end
              end
          ostmts
        end

        function optimizeStatementTail(path::Absyn.Path, inStmt::DAE.Statement, invars::List{<:String}, outvars::List{<:String}) ::DAE.Statement
              local ostmt::DAE.Statement

              ostmt = begin
                  local tp::DAE.Type
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local cond::DAE.Exp
                  local lhsLst::List{DAE.Exp}
                  local name::String
                  local lhsNames::List{String}
                  local stmts::List{DAE.Statement}
                  local source::DAE.ElementSource
                  local stmt::DAE.Statement
                  local else_::DAE.Else
                @matchcontinue (path, inStmt, invars, outvars) begin
                  (_, DAE.STMT_ASSIGN(tp, lhs, rhs, source), _, _)  => begin
                      name = Expression.simpleCrefName(lhs)
                      rhs = optimizeStatementTail2(path, rhs, list(name), invars, outvars, source)
                      stmt = if Expression.isTailCall(rhs)
                            DAE.STMT_NORETCALL(rhs, source)
                          else
                            DAE.STMT_ASSIGN(tp, lhs, rhs, source)
                          end
                    stmt
                  end

                  (_, DAE.STMT_TUPLE_ASSIGN(tp, lhsLst, rhs, source), _, _)  => begin
                      lhsNames = ListUtil.map(lhsLst, Expression.simpleCrefName)
                      rhs = optimizeStatementTail2(path, rhs, lhsNames, invars, outvars, source)
                      stmt = if Expression.isTailCall(rhs)
                            DAE.STMT_NORETCALL(rhs, source)
                          else
                            DAE.STMT_TUPLE_ASSIGN(tp, lhsLst, rhs, source)
                          end
                    stmt
                  end

                  (_, DAE.STMT_IF(cond, stmts, else_, source), _, _)  => begin
                      stmts = optimizeLastStatementTail(path, stmts, invars, outvars, nil)
                      else_ = optimizeElseTail(path, else_, invars, outvars)
                    DAE.STMT_IF(cond, stmts, else_, source)
                  end

                  (_, DAE.STMT_NORETCALL(rhs, source), _,  nil())  => begin
                      rhs = optimizeStatementTail2(path, rhs, nil, invars, nil, source)
                      stmt = DAE.STMT_NORETCALL(rhs, source)
                    stmt
                  end

                  _  => begin
                      inStmt
                  end
                end
              end
          ostmt
        end

        function optimizeElseTail(path::Absyn.Path, inElse::DAE.Else, invars::List{<:String}, outvars::List{<:String}) ::DAE.Else
              local outElse::DAE.Else

              outElse = begin
                  local cond::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local else_::DAE.Else
                @matchcontinue (path, inElse, invars, outvars) begin
                  (_, DAE.ELSEIF(cond, stmts, else_), _, _)  => begin
                      stmts = optimizeLastStatementTail(path, stmts, invars, outvars, nil)
                      else_ = optimizeElseTail(path, else_, invars, outvars)
                    DAE.ELSEIF(cond, stmts, else_)
                  end

                  (_, DAE.ELSE(stmts), _, _)  => begin
                      stmts = optimizeLastStatementTail(path, stmts, invars, outvars, nil)
                    DAE.ELSE(stmts)
                  end

                  _  => begin
                      inElse
                  end
                end
              end
          outElse
        end

        function optimizeStatementTail2(path::Absyn.Path, rhs::DAE.Exp, lhsVars::List{<:String}, invars::List{<:String}, outvars::List{<:String}, source::DAE.ElementSource) ::DAE.Exp
              local orhs::DAE.Exp

              @match true = valueEq(lhsVars, outvars)
              @match (orhs, true) = optimizeStatementTail3(path, rhs, invars, lhsVars, source)
          orhs
        end

        function optimizeStatementTail3(path::Absyn.Path, rhs::DAE.Exp, vars::List{<:String}, lhsVars::List{<:String}, source::DAE.ElementSource) ::Tuple{DAE.Exp, Bool}
              local isTailRecursive::Bool
              local orhs::DAE.Exp

              (orhs, isTailRecursive) = begin
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local str::String
                  local i::DAE.InlineType
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local b4::Bool
                  local tp::DAE.Type
                  local et::DAE.Type
                  local es::List{DAE.Exp}
                  local inputs::List{DAE.Exp}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local localDecls::List{DAE.Element}
                  local matchType::DAE.MatchType
                  local cases::List{DAE.MatchCase}
                  local aliases::List{List{String}}
                  local attr::DAE.CallAttributes
                  local call::DAE.Exp
                @matchcontinue (path, rhs, vars, source) begin
                  (path1, call && DAE.CALL(path = path2, attr = attr && DAE.CALL_ATTR(tailCall = DAE.NO_TAIL(__))), _, _)  => begin
                      @match true = AbsynUtil.pathEqual(path1, path2)
                      str = "Tail recursion of: " + ExpressionDump.printExpStr(rhs) + " with input vars: " + stringDelimitList(vars, ",")
                      if Flags.isSet(Flags.TAIL)
                        Error.addSourceMessage(Error.COMPILER_NOTIFICATION, list(str), ElementSource.getElementSourceFileInfo(source))
                      end
                      attr.tailCall = DAE.TAIL(vars, lhsVars)
                      call.attr = attr
                    (call, true)
                  end

                  (_, DAE.IFEXP(e1, e2, e3), _, _)  => begin
                      (e2, b1) = optimizeStatementTail3(path, e2, vars, lhsVars, source)
                      (e3, b2) = optimizeStatementTail3(path, e3, vars, lhsVars, source)
                      @match true = b1 || b2
                    (DAE.IFEXP(e1, e2, e3), true)
                  end

                  (_, DAE.MATCHEXPRESSION(matchType && DAE.MATCH(_), inputs, aliases, localDecls, cases, et), _, _)  => begin
                      cases = optimizeStatementTailMatchCases(path, cases, false, nil, vars, lhsVars, source)
                    (DAE.MATCHEXPRESSION(matchType, inputs, aliases, localDecls, cases, et), true)
                  end

                  _  => begin
                      (rhs, false)
                  end
                end
              end
               #= /*TODO:matchcontinue*/ =#
          (orhs, isTailRecursive)
        end

        function optimizeStatementTailMatchCases(path::Absyn.Path, inCases::List{<:DAE.MatchCase}, changed::Bool, inAcc::List{<:DAE.MatchCase}, vars::List{<:String}, lhsVars::List{<:String}, source::DAE.ElementSource) ::List{DAE.MatchCase}
              local ocases::List{DAE.MatchCase}

              ocases = begin
                  local patterns::List{DAE.Pattern}
                  local localDecls::List{DAE.Element}
                  local body::List{DAE.Statement}
                  local patternGuard::Option{DAE.Exp}
                  local resultInfo::SourceInfo
                  local info::SourceInfo
                  local jump::ModelicaInteger
                  local case_::DAE.MatchCase
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local cases::List{DAE.MatchCase}
                  local acc::List{DAE.MatchCase}
                  local sourceStmt::DAE.ElementSource
                @matchcontinue (path, inCases, changed, inAcc, vars, source) begin
                  (_,  nil(), true, acc, _, _)  => begin
                    listReverse(acc)
                  end

                  (_, DAE.CASE(patterns, patternGuard, localDecls, body, SOME(exp), resultInfo, jump, info) <| cases, _, acc, _, _)  => begin
                      @match (exp, true) = optimizeStatementTail3(path, exp, vars, lhsVars, source)
                      case_ = DAE.CASE(patterns, patternGuard, localDecls, body, SOME(exp), resultInfo, jump, info)
                    optimizeStatementTailMatchCases(path, cases, true, _cons(case_, acc), vars, lhsVars, source)
                  end

                  (_, DAE.CASE(patterns, patternGuard, localDecls, body, SOME(DAE.TUPLE( nil())), resultInfo, jump, info) <| cases, _, acc, _, _)  => begin
                      @match DAE.STMT_NORETCALL(exp, sourceStmt) = ListUtil.last(body)
                      @match (exp, true) = optimizeStatementTail3(path, exp, vars, lhsVars, source)
                      body = ListUtil.set(body, listLength(body), DAE.STMT_NORETCALL(exp, sourceStmt))
                      case_ = DAE.CASE(patterns, patternGuard, localDecls, body, SOME(DAE.TUPLE(nil)), resultInfo, jump, info)
                    optimizeStatementTailMatchCases(path, cases, true, _cons(case_, acc), vars, lhsVars, source)
                  end

                  (_, case_ <| cases, _, acc, _, _)  => begin
                    optimizeStatementTailMatchCases(path, cases, changed, _cons(case_, acc), vars, lhsVars, source)
                  end
                end
              end
          ocases
        end

         #= Cannot be part of Env due to RML issues =#
        function pushStructuralParameters(cache::FCore.Cache) ::FCore.Cache
              local ocache::FCore.Cache

              ocache = begin
                  local ie::Option{FCore.Graph}
                  local f::MutableType #= {DAE.FunctionTree} =#
                  local ht::AvlSetCR.Tree
                  local crs::List{List{DAE.ComponentRef}}
                  local p::Absyn.Path
                @match cache begin
                  FCore.CACHE(ie, f, (ht, crs), p)  => begin
                    FCore.CACHE(ie, f, (ht, _cons(nil, crs)), p)
                  end

                  _  => begin
                      cache
                  end
                end
              end
          ocache
        end

         #= Cannot be part of Env due to RML issues =#
        function popStructuralParameters(cache::FCore.Cache, pre::Prefix.PrefixType) ::FCore.Cache
              local ocache::FCore.Cache

              ocache = begin
                  local ie::Option{FCore.Graph}
                  local f::MutableType #= {DAE.FunctionTree} =#
                  local ht::AvlSetCR.Tree
                  local crs::List{DAE.ComponentRef}
                  local crss::List{List{DAE.ComponentRef}}
                  local p::Absyn.Path
                  local program::Absyn.Program
                @match (cache, pre) begin
                  (FCore.CACHE(ie, f, (ht, crs <| crss), p), _)  => begin
                      ht = prefixAndAddCrefsToHt(cache, ht, pre, crs)
                    FCore.CACHE(ie, f, (ht, crss), p)
                  end

                  (FCore.CACHE(_, _, (_,  nil()), _), _)  => begin
                    cache
                  end

                  (FCore.NO_CACHE(__), _)  => begin
                    cache
                  end
                end
              end
          ocache
        end

         #= Cannot be part of Env due to RML issues =#
        function prefixAndAddCrefsToHt(cache::FCore.Cache, set::AvlSetCR.Tree, pre::Prefix.PrefixType, icrs::List{<:DAE.ComponentRef}) ::AvlSetCR.Tree


              for cr in icrs
                (_, cr) = PrefixUtil.prefixCref(cache, FGraph.empty(), InnerOuter.emptyInstHierarchy, pre, cr)
                set = AvlSetCR.add(set, cr)
              end
          set
        end

        function numStructuralParameterScopes(cache::FCore.Cache) ::ModelicaInteger
              local i::ModelicaInteger

              local lst::List{List{DAE.ComponentRef}}

              @match FCore.CACHE(evaluatedParams = (_, lst)) = cache
              i = listLength(lst)
          i
        end

         #= Finds any variable that might be used without first being defined =#
        function checkFunctionDefUse(elts::List{<:DAE.Element}, info::SourceInfo)
              _ = begin
                @matchcontinue (elts, info) begin
                  (_, _)  => begin
                      _ = checkFunctionDefUse2(elts, NONE(), nil, nil, info)
                    ()
                  end

                  _  => begin
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list("InstUtil.checkFunctionDefUse failed"), info)
                      ()
                  end
                end
              end
        end

         #= Finds any variable that might be used without first being defined =#
        function checkFunctionDefUse2(elts::List{<:DAE.Element}, alg::Option{<:List{<:DAE.Statement}} #= NONE() in first iteration =#, inUnbound::List{<:String} #= {} in first iteration =#, inOutputs::List{<:String} #= List of variables that are also used, when returning =#, inInfo::SourceInfo) ::List{String}
              local outUnbound::List{String}

              outUnbound = begin
                  local rest::List{DAE.Element}
                  local stmts::List{DAE.Statement}
                  local unbound::List{String}
                  local outputs::List{String}
                  local names::List{String}
                  local outNames::List{String}
                  local name::String
                  local dims::DAE.InstDims
                  local dir::DAE.VarDirection
                  local vars::List{DAE.Var}
                @match (elts, alg, inUnbound, inOutputs, inInfo) begin
                  ( nil(), NONE(), _, _, _)  => begin
                    inUnbound
                  end

                  ( nil(), SOME(stmts), unbound, outputs, _)  => begin
                      (_, _, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, false, (false, false, unbound))
                      unbound = ListUtil.fold1(outputs, checkOutputDefUse, inInfo, unbound)
                    unbound
                  end

                  (DAE.VAR(direction = DAE.INPUT(__)) <| rest, _, unbound, _, _)  => begin
                      unbound = checkFunctionDefUse2(rest, alg, unbound, inOutputs, inInfo)
                    unbound
                  end

                  (DAE.VAR(direction = dir, componentRef = DAE.CREF_IDENT(ident = name), ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_), varLst = vars), dims = dims, binding = NONE()) <| rest, _, unbound, _, _)  => begin
                      vars = ListUtil.filterOnTrue(vars, Types.varIsVariable)
                      names = ListUtil.map1r(ListUtil.map(vars, Types.varName), stringAppend, name + ".")
                      outNames = if DAEUtil.varDirectionEqual(dir, DAE.OUTPUT())
                            names
                          else
                            nil
                          end
                      names = if Expression.dimensionsKnownAndNonZero(dims)
                            names
                          else
                            nil
                          end
                      unbound = listAppend(names, unbound)
                      outputs = listAppend(outNames, inOutputs)
                      unbound = checkFunctionDefUse2(rest, alg, unbound, outputs, inInfo)
                    unbound
                  end

                  (DAE.VAR(direction = dir, componentRef = DAE.CREF_IDENT(ident = name), dims = dims, binding = NONE()) <| rest, _, unbound, _, _)  => begin
                      unbound = ListUtil.consOnTrue(Expression.dimensionsKnownAndNonZero(dims), name, unbound)
                      outputs = ListUtil.consOnTrue(DAEUtil.varDirectionEqual(dir, DAE.OUTPUT()), name, inOutputs)
                      unbound = checkFunctionDefUse2(rest, alg, unbound, outputs, inInfo)
                    unbound
                  end

                  (DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(stmts)) <| rest, NONE(), unbound, _, _)  => begin
                      unbound = checkFunctionDefUse2(rest, SOME(stmts), unbound, inOutputs, inInfo)
                    unbound
                  end

                  (_ <| rest, _, unbound, _, _)  => begin
                      unbound = checkFunctionDefUse2(rest, alg, unbound, inOutputs, inInfo)
                    unbound
                  end
                end
              end
               #=  This would run also for partial function inst... So let's skip it
               =#
               #=  equation
               =#
               #=   unbound = List.fold1(outputs, checkOutputDefUse, inInfo, unbound);
               =#
               #=  TODO: We filter out parameters at the moment. I'm unsure if this is correct. Might be that this is an automatic error...
               =#
               #=  print(\"for record: \" + stringDelimitList(names,\",\") + \"\\n\");
               =#
               #=  Arrays with unknown bounds (size(cr,1), etc) are treated as initialized because they may have 0 dimensions checked for in the code
               =#
               #=  Arrays with unknown bounds (size(cr,1), etc) are treated as initialized because they may have 0 dimensions checked for in the code
               =#
          outUnbound
        end

        function checkOutputDefUse(name::String, info::SourceInfo, inUnbound::List{<:String}) ::List{String}
              local outUnbound::List{String}

              local b::Bool

              b = listMember(name, inUnbound)
              Error.assertionOrAddSourceMessage(! b, Error.WARNING_DEF_USE, list(name), info)
              outUnbound = ListUtil.filter1OnTrue(inUnbound, Util.stringNotEqual, name)
          outUnbound
        end

         #= Find any variable that might be used in the statement without prior definition. Any defined variables are removed from undefined. =#
        function checkFunctionDefUseStmt(inStmt::DAE.Statement, inLoop::Bool, inUnbound::Tuple{<:Bool, Bool, List{<:String}} #= Return or Break ; Returned for sure ; Unbound =#) ::Tuple{Bool, Bool, List{String}}
              local outUnbound::Tuple{Bool, Bool, List{String}} #=  =#

              outUnbound = begin
                  local source::DAE.ElementSource
                  local str::String
                  local iter::String
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local lhss::List{DAE.Exp}
                  local unbound::List{String}
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local else_::DAE.Else
                  local stmts::List{DAE.Statement}
                  local info::SourceInfo
                @match (inStmt, inLoop, inUnbound) begin
                  (_, _, (true, _, _))  => begin
                    inUnbound
                  end

                  (_, _, (false, true, _))  => begin
                      info = ElementSource.getElementSourceFileInfo(ElementSource.getStatementSource(inStmt))
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list("InstUtil.checkFunctionDefUseStmt failed"), info)
                    fail()
                  end

                  (DAE.STMT_ASSIGN(exp1 = lhs, exp = rhs, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(rhs, findUnboundVariableUse, (unbound, info))
                      unbound = traverseCrefSubs(lhs, info, unbound)
                      unbound = crefFiltering(lhs, unbound)
                    (false, false, unbound)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(expExpLst = lhss, exp = rhs, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(rhs, findUnboundVariableUse, (unbound, info))
                      unbound = ListUtil.fold1(lhss, traverseCrefSubs, info, unbound)
                      unbound = ListUtil.fold(lhss, crefFiltering, unbound)
                    (false, false, unbound)
                  end

                  (DAE.STMT_ASSIGN_ARR(lhs = lhs, exp = rhs, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(rhs, findUnboundVariableUse, (unbound, info))
                      unbound = traverseCrefSubs(lhs, info, unbound)
                      unbound = crefFiltering(lhs, unbound)
                    (false, false, unbound)
                  end

                  (DAE.STMT_IF(exp, stmts, else_, source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (b1, b2, unbound) = checkFunctionDefUseElse(DAE.ELSEIF(exp, stmts, else_), unbound, inLoop, info)
                    (b1, b2, unbound)
                  end

                  (DAE.STMT_FOR(iter = iter, range = exp, statementLst = stmts, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, iter) #= TODO: This is not needed if all references are tagged CREF_ITER =#
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                      (_, b, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, true, (false, false, unbound))
                    (b, b, unbound)
                  end

                  (DAE.STMT_PARFOR(iter = iter, range = exp, statementLst = stmts, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, iter) #= TODO: This is not needed if all references are tagged CREF_ITER =#
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                      (_, b, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, true, (false, false, unbound))
                    (b, b, unbound)
                  end

                  (DAE.STMT_WHILE(exp = exp, statementLst = stmts, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                      (_, b, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, true, (false, false, unbound))
                    (b, b, unbound)
                  end

                  (DAE.STMT_ASSERT(cond = DAE.BCONST(false)), _, (_, _, _))  => begin
                    (true, true, nil)
                  end

                  (DAE.STMT_ASSERT(cond = exp1, msg = exp2, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp1, findUnboundVariableUse, (unbound, info))
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp2, findUnboundVariableUse, (unbound, info))
                    (false, false, unbound)
                  end

                  (DAE.STMT_TERMINATE(msg = exp, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                    (true, true, unbound)
                  end

                  (DAE.STMT_NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("fail"), expLst =  nil())), _, (_, _, _))  => begin
                    (true, true, nil)
                  end

                  (DAE.STMT_NORETCALL(exp = exp, source = source), _, (_, _, unbound))  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                    (false, false, unbound)
                  end

                  (DAE.STMT_BREAK(__), _, (_, _, unbound))  => begin
                    (true, false, unbound)
                  end

                  (DAE.STMT_RETURN(__), _, (_, _, unbound))  => begin
                    (true, true, unbound)
                  end

                  (DAE.STMT_CONTINUE(__), _, (_, _, unbound))  => begin
                    (false, false, unbound)
                  end

                  (DAE.STMT_ARRAY_INIT(__), _, _)  => begin
                    inUnbound
                  end

                  (DAE.STMT_FAILURE(body = stmts), _, (_, _, unbound))  => begin
                      (_, b, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, inLoop, (false, false, unbound))
                    (b, b, unbound)
                  end

                  _  => begin
                        str = DAEDump.ppStatementStr(inStmt)
                        str = "InstUtil.checkFunctionDefUseStmt failed: " + str
                        info = ElementSource.getElementSourceFileInfo(ElementSource.getStatementSource(inStmt))
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), info)
                      fail()
                  end
                end
              end
               #=  Traverse subs too! arr[x] := ..., x unbound
               =#
               #=  Traverse subs too! arr[x] := ..., x unbound
               =#
               #=  Traverse subs too! arr[x] := ..., x unbound
               =#
               #=  TODO: Re-write these earlier from assert(false,msg) to terminate(msg)
               =#
               #=  STMT_WHEN not in functions
               =#
               #=  STMT_REINIT not in functions
               =#
          outUnbound #=  =#
        end

        function checkFunctionDefUseElse(inElse::DAE.Else, inUnbound::List{<:String}, inLoop::Bool, info::SourceInfo) ::Tuple{Bool, Bool, List{String}}
              local outUnbound::Tuple{Bool, Bool, List{String}}

              outUnbound = begin
                  local exp::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local else_::DAE.Else
                  local unbound::List{String}
                  local unboundBranch::List{String}
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local b4::Bool
                  local iloop::Bool
                @match (inElse, inUnbound, inLoop, info) begin
                  (DAE.NOELSE(__), _, _, _)  => begin
                    (false, false, inUnbound)
                  end

                  (DAE.ELSEIF(exp, stmts, else_), unbound, iloop, _)  => begin
                      (_, (unbound, _)) = Expression.traverseExpTopDown(exp, findUnboundVariableUse, (unbound, info))
                      (b1, b2, unboundBranch) = checkFunctionDefUseElse(else_, unbound, inLoop, info)
                      (b3, b4, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, inLoop, (false, false, unbound))
                      iloop = true #= We find a few false positives if we are too conservative, so let's do it non-exact =#
                      unbound = if iloop
                            ListUtil.intersectionOnTrue(unboundBranch, unbound, stringEq)
                          else
                            unbound
                          end
                      unbound = if ! (iloop || b1)
                            ListUtil.union(unboundBranch, unbound)
                          else
                            unbound
                          end
                      b1 = b1 && b3
                      b2 = b2 && b4
                    (b1, b2, unbound)
                  end

                  (DAE.ELSE(stmts), unbound, _, _)  => begin
                      (b1, b2, unbound) = ListUtil.fold1(stmts, checkFunctionDefUseStmt, inLoop, (false, false, unbound))
                    (b1, b2, unbound)
                  end
                end
              end
               #= /* Merge the state of the two branches. Either they can break/return or not */ =#
          outUnbound
        end

         #= If the expression is a cref, remove it from the unbound variables =#
        function crefFiltering(inExp::DAE.Exp, inUnbound::List{<:String}) ::List{String}
              local outUnbound::List{String}

              outUnbound = begin
                  local unbound::List{String}
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                  local pattern::DAE.Pattern
                  local id1::String
                  local id2::String
                @match (inExp, inUnbound) begin
                  (DAE.CREF(componentRef = DAE.WILD(__)), _)  => begin
                    inUnbound
                  end

                  (DAE.CREF(componentRef = DAE.CREF_QUAL(ident = id1, componentRef = DAE.CREF_IDENT(ident = id2))), unbound)  => begin
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, id1 + "." + id2)
                    unbound
                  end

                  (DAE.CREF(componentRef = DAE.CREF_IDENT(ident = id1), ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_))), unbound)  => begin
                      id1 = id1 + "."
                      unbound = ListUtil.filter2OnTrue(unbound, Util.notStrncmp, id1, stringLength(id1))
                    unbound
                  end

                  (DAE.CREF(componentRef = cr), unbound)  => begin
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, ComponentReference.crefFirstIdent(cr))
                    unbound
                  end

                  (DAE.ASUB(exp = exp), unbound)  => begin
                    crefFiltering(exp, unbound)
                  end

                  (DAE.PATTERN(pattern = pattern), unbound)  => begin
                      (_, unbound) = Patternm.traversePattern(pattern, patternFiltering, unbound)
                    unbound
                  end

                  _  => begin
                      inUnbound
                  end
                end
              end
               #=  Assignment to part of a record
               =#
               #=  Assignment to the whole record - filter out everything it is prefix of
               =#
          outUnbound
        end

        function patternFiltering(inPat::DAE.Pattern, inLst::List{<:String}) ::Tuple{DAE.Pattern, List{String}}
              local unbound::List{String} = inLst
              local outPat::DAE.Pattern = inPat

              unbound = begin
                @match inPat begin
                  DAE.PAT_AS(__)  => begin
                    ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, inPat.id)
                  end

                  DAE.PAT_AS_FUNC_PTR(__)  => begin
                    ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, inPat.id)
                  end

                  _  => begin
                      unbound
                  end
                end
              end
          (outPat, unbound)
        end

        function traverseCrefSubs(exp::DAE.Exp, info::SourceInfo, inUnbound::List{<:String}) ::List{String}
              local outUnbound::List{String}

              outUnbound = begin
                  local unbound::List{String}
                  local cr::DAE.ComponentRef
                @match (exp, info, inUnbound) begin
                  (DAE.CREF(componentRef = cr), _, unbound)  => begin
                      (_, (unbound, _)) = Expression.traverseExpTopDownCrefHelper(cr, findUnboundVariableUse, (unbound, info))
                    unbound
                  end

                  _  => begin
                      inUnbound
                  end
                end
              end
          outUnbound
        end

         #= Check if the expression is used before it is defined =#
        function findUnboundVariableUse(inExp::DAE.Exp, inTpl::Tuple{<:List{<:String}, SourceInfo}) ::Tuple{DAE.Exp, Bool, Tuple{List{String}, SourceInfo}}
              local outTpl::Tuple{List{String}, SourceInfo}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local exp::DAE.Exp
                  local unbound::List{String}
                  local unboundLocal::List{String}
                  local info::SourceInfo
                  local str::String
                  local name::String
                  local cr::DAE.ComponentRef
                  local b::Bool
                  local arg::Tuple{List{String}, SourceInfo}
                  local inputs::List{DAE.Exp}
                  local localDecls::List{DAE.Element}
                  local cases::List{DAE.MatchCase}
                  local unbounds::List{List{String}}
                @match (inExp, inTpl) begin
                  (exp && DAE.SIZE(__), arg)  => begin
                    (exp, false, arg)
                  end

                  (exp && DAE.CALL(path = Absyn.IDENT("isPresent"), attr = DAE.CALL_ATTR(builtin = true)), arg)  => begin
                    (exp, false, arg)
                  end

                  (DAE.CREF(componentRef = DAE.WILD(__)), (_, info))  => begin
                       #=  _ shouldn't be allowed to be used like a variable, but until that's
                       =#
                       #=  enforced just give an error message here instead of just failing.
                       =#
                      Error.addSourceMessage(Error.WARNING_DEF_USE, list("_"), info)
                    (inExp, true, inTpl)
                  end

                  (exp && DAE.CREF(componentRef = cr), (unbound, info))  => begin
                      b = listMember(ComponentReference.crefFirstIdent(cr), unbound)
                      str = ComponentReference.crefFirstIdent(cr)
                      Error.assertionOrAddSourceMessage(! b, Error.WARNING_DEF_USE, list(str), info)
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, str)
                    (exp, true, (unbound, info))
                  end

                  (exp && DAE.CALL(path = Absyn.IDENT(name)), (unbound, info))  => begin
                      b = listMember(name, unbound)
                      Error.assertionOrAddSourceMessage(! b, Error.WARNING_DEF_USE, list(name), info)
                      unbound = ListUtil.filter1OnTrue(unbound, Util.stringNotEqual, name)
                    (exp, true, (unbound, info))
                  end

                  (exp && DAE.MATCHEXPRESSION(inputs = inputs, localDecls = localDecls, cases = cases), (unbound, info))  => begin
                      (_, (unbound, _)) = Expression.traverseExpTopDown(DAE.LIST(inputs), findUnboundVariableUse, (unbound, info))
                      unboundLocal = checkFunctionDefUse2(localDecls, NONE(), unbound, nil, info)
                      unbounds = ListUtil.map1(cases, findUnboundVariableUseInCase, unboundLocal)
                      unbound = ListUtil.fold1r(unbounds, ListUtil.intersectionOnTrue, stringEq, unbound)
                    (exp, false, (unbound, info))
                  end

                  (exp, arg)  => begin
                    (exp, true, arg)
                  end
                end
              end
               #=  Find variables assigned in a case, like: _ = match () case () equation o = 1.5; then ();
               =#
          (outExp, cont, outTpl)
        end

         #= Check if the expression is used before it is defined =#
        function findUnboundVariableUseInCase(case_::DAE.MatchCase, inUnbound::List{<:String}) ::List{String}
              local unbound::List{String}

              unbound = begin
                  local info::SourceInfo
                  local resultInfo::SourceInfo
                  local patternGuard::Option{DAE.Exp}
                  local result::Option{DAE.Exp}
                  local patterns::List{DAE.Pattern}
                  local body::List{DAE.Statement}
                @match (case_, inUnbound) begin
                  (DAE.CASE(patterns = patterns, patternGuard = patternGuard, body = body, result = result, info = info, resultInfo = resultInfo), unbound)  => begin
                      (_, unbound) = Patternm.traversePatternList(patterns, patternFiltering, unbound)
                      (_, (unbound, _)) = Expression.traverseExpTopDown(DAE.META_OPTION(patternGuard), findUnboundVariableUse, (unbound, info))
                      (_, _, unbound) = ListUtil.fold1(body, checkFunctionDefUseStmt, true, (false, false, unbound))
                      (_, (unbound, _)) = Expression.traverseExpTopDown(DAE.META_OPTION(result), findUnboundVariableUse, (unbound, resultInfo))
                    unbound
                  end
                end
              end
          unbound
        end

        function checkParallelismWRTEnv(inEnv::FCore.Graph, inName::String, inAttr::SCode.Attributes, inInfo::SourceInfo) ::Bool
              local isValid::Bool

              isValid = begin
                  local errorString::String
                  local scopeName::String
                  local dir::Absyn.Direction
                  local prl::SCode.Parallelism
                  local isparglobal::Bool
                  local hasnodir::Bool
                  local r::FCore.MMRef
                @matchcontinue (inEnv, inName, inAttr, inInfo) begin
                  (_, _, SCode.ATTR(parallelism = prl, direction = dir), _)  => begin
                      r = FGraph.lastScopeRef(inEnv)
                      @match false = FNode.isRefTop(r)
                      scopeName = FNode.refName(r)
                      @match true = FGraph.checkScopeType(list(r), SOME(FCore.PARALLEL_SCOPE()))
                      isparglobal = SCodeUtil.parallelismEqual(prl, SCode.PARGLOBAL())
                      hasnodir = ! AbsynUtil.isInputOrOutput(dir)
                      @match true = isparglobal && hasnodir
                      errorString = "\\n" + "- local parglobal component '" + inName + "' is declared in parallel/parkernel function '" + scopeName + "'. \\n" + "- parglobal variables can be declared only in normal functions. \\n"
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), inInfo)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          isValid
        end

        function instDimsHasZeroDims(inInstDims::List{<:List{<:DAE.Dimension}}) ::Bool
              local outHasZeroDims::Bool

              outHasZeroDims = begin
                  local dims::List{DAE.Dimension}
                  local rest_dims::InstDims
                @matchcontinue inInstDims begin
                  dims <| _  => begin
                      @match true = ListUtil.exist(dims, Expression.dimensionIsZero)
                    true
                  end

                  _ <| rest_dims  => begin
                    instDimsHasZeroDims(rest_dims)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outHasZeroDims
        end

         #= help function for updateComponentInEnv,
        For components that already have been visited by updateComponentsInEnv, they must be instantiated without
        modifiers to prevent infinite recursion =#
        function noModForUpdatedComponents(variability::SCode.Variability, updatedComps::HashTable5.HashTable, cref::Absyn.ComponentRef, mods::DAE.Mod, cmod::DAE.Mod, m::SCode.Mod) ::Tuple{DAE.Mod, DAE.Mod, SCode.Mod}
              local outM::SCode.Mod
              local outCmod::DAE.Mod
              local outMods::DAE.Mod

              (outMods, outCmod, outM) = begin
                @matchcontinue (variability, updatedComps, cref, mods, cmod, m) begin
                  (_, _, _, _, _, _) where (BaseHashTable.hasKey(cref, updatedComps))  => begin
                      checkVariabilityOfUpdatedComponent(variability, cref)
                    (DAE.NOMOD(), DAE.NOMOD(), SCode.NOMOD())
                  end

                  _  => begin
                      (mods, cmod, m)
                  end
                end
              end
          (outMods, outCmod, outM)
        end

         #= Takes a component's modifier and final attribute, and return FINAL if either
           of them is final, otherwise NOT_FINAL. =#
        function propagateModFinal(inMod::DAE.Mod, inFinal::SCode.Final) ::SCode.Final
              local outFinal::SCode.Final

              outFinal = begin
                  local fp::SCode.Final
                   #=  If the component is already final, keep it.
                   =#
                @match (inMod, inFinal) begin
                  (_, SCode.FINAL(__))  => begin
                    inFinal
                  end

                  (DAE.MOD(finalPrefix = fp), _)  => begin
                    fp
                  end

                  _  => begin
                      inFinal
                  end
                end
              end
               #=  If we got a modifier, use its final prefix instead.
               =#
               #=  Otherwise, do nothing.
               =#
          outFinal
        end

         #= ------------------------------
         =#
         #= ------  PDE extension:  ------
         =#
         #= ------------------------------
         =#

        DomainFieldOpt = Option

        DomainFieldsLst = List

        function addGhostCells(inCompelts::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inEqs::List{<:SCode.Equation}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outCompelts::List{Tuple{SCode.Element, DAE.Mod}}

              local fieldNamesP::List{Absyn.Ident}

              local ghostCompelts::List{Tuple{SCode.Element, DAE.Mod}}

              fieldNamesP = ListUtil.fold(inEqs, fieldsInPderEq, nil)
              ghostCompelts = ListUtil.fold1(inCompelts, addGhostCells2, fieldNamesP, nil)
              outCompelts = listAppend(inCompelts, ghostCompelts)
          outCompelts
        end

        function fieldsInPderEq(eq::SCode.Equation, inFieldNames::List{<:Absyn.Ident}) ::List{Absyn.Ident}
              local outFieldNames::List{Absyn.Ident}

              outFieldNames = begin
                  local fieldNames1::List{Absyn.Ident}
                  local lhs_exp::Absyn.Exp
                  local rhs_exp::Absyn.Exp
                @match eq begin
                  SCode.EQUATION(SCode.EQ_PDE(expLeft = lhs_exp, expRight = rhs_exp))  => begin
                       #= /*,domain = domainCr as Absyn.CREF_IDENT(), comment = comment, info = info))*/ =#
                      (_, fieldNames1) = AbsynUtil.traverseExpTopDown(lhs_exp, fieldInPderExp, inFieldNames)
                      (_, fieldNames1) = AbsynUtil.traverseExpTopDown(rhs_exp, fieldInPderExp, fieldNames1)
                    listAppend(inFieldNames, fieldNames1)
                  end

                  _  => begin
                      inFieldNames
                  end
                end
              end
          outFieldNames
        end

        function fieldInPderExp(inExp::Absyn.Exp, inFieldNames::List{<:Absyn.Ident}) ::Tuple{Absyn.Exp, List{Absyn.Ident}}
              local outFieldNames::List{Absyn.Ident}
              local outExp::Absyn.Exp

              outFieldNames = begin
                  local newFieldName::Absyn.Ident
                @match inExp begin
                  Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "pder"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(Absyn.CREF_IDENT(name = newFieldName)) <| _ <|  nil()))  => begin
                    ListUtil.unionElt(newFieldName, inFieldNames)
                  end

                  Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "pder"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(Absyn.CREF_IDENT(name = newFieldName)) <| _ <| _ <|  nil()))  => begin
                    ListUtil.unionElt(newFieldName, inFieldNames)
                  end

                  _  => begin
                      inFieldNames
                  end
                end
              end
              outExp = inExp
          (outExp, outFieldNames)
        end

        function addGhostCells2(inCompelt::Tuple{<:SCode.Element, DAE.Mod}, fieldNamesP::List{<:Absyn.Ident}, inGhosts::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{Tuple{SCode.Element, DAE.Mod}}
              local outGhosts::List{Tuple{SCode.Element, DAE.Mod}}

              outGhosts = begin
                  local name::SCode.Ident
                  local prefixes::SCode.Prefixes
                  local attributes::SCode.Attributes
                  local typeSpec::Absyn.TypeSpec
                  local modifications::SCode.Mod
                  local comment::SCode.Comment
                  local condition::Option{Absyn.Exp}
                  local info::SCode.SourceInfo
                  local arrayDims::Absyn.ArrayDim
                  local connectorType::SCode.ConnectorType
                  local parallelism::SCode.Parallelism
                  local variability::SCode.Variability
                  local direction::Absyn.Direction
                  local finalPrefix::SCode.Final #= final prefix =#
                  local eachPrefix::SCode.Each #= each prefix =#
                  local subModLst::List{SCode.SubMod}
                  local binding::Option{Absyn.Exp}
                  local info2::SCode.SourceInfo
                  local daeMod::DAE.Mod
                  local ghostL::Tuple{SCode.Element, DAE.Mod}
                  local ghostR::Tuple{SCode.Element, DAE.Mod}
                @matchcontinue inCompelt begin
                  (SCode.COMPONENT(name, prefixes, SCode.ATTR(arrayDims, connectorType, parallelism, variability, direction, Absyn.FIELD(__)), typeSpec, SCode.MOD(finalPrefix, eachPrefix, subModLst, binding, info2), comment, condition, info), daeMod)  => begin
                      if ! listMember(name, fieldNamesP)
                        fail()
                      end
                      subModLst = ListUtil.filterOnFalse(subModLst, isSubModDomainOrStart)
                      ghostL = (SCode.COMPONENT(stringAppend(name, "ghostL"), prefixes, SCode.ATTR(arrayDims, connectorType, parallelism, variability, direction, Absyn.NONFIELD()), typeSpec, SCode.MOD(finalPrefix, eachPrefix, subModLst, binding, info2), comment, condition, info), daeMod)
                      ghostR = (SCode.COMPONENT(stringAppend(name, "ghostR"), prefixes, SCode.ATTR(arrayDims, connectorType, parallelism, variability, direction, Absyn.NONFIELD()), typeSpec, SCode.MOD(finalPrefix, eachPrefix, subModLst, binding, info2), comment, condition, info), daeMod)
                    _cons(ghostL, _cons(ghostR, inGhosts))
                  end

                  _  => begin
                      inGhosts
                  end
                end
              end
               #= /*modifications*/ =#
               #= remove domain from the subModLst:
               =#
          outGhosts
        end

        function isSubModDomainOrStart(subMod::SCode.SubMod) ::Bool
              local isNotDomain::Bool

              isNotDomain = begin
                  local idn::String
                @match subMod begin
                  SCode.NAMEMOD(ident = idn) where (idn == "domain" || idn == "start")  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNotDomain
        end

        function elabField(inCache::FCore.Cache, inEnv::FCore.Graph, name::String, attr::SCode.Attributes, inDims::DAE.Dimensions, inMod::DAE.Mod, inInfo::SourceInfo) ::Tuple{DAE.Dimensions, DAE.Mod, DomainFieldOpt}
              local outFieldDomOpt::DomainFieldOpt
              local outMod::DAE.Mod
              local outDims::DAE.Dimensions

              (outDims, outMod, outFieldDomOpt) = begin
                  local dim_f::DAE.Dimension
                  local finalPrefix::SCode.Final
                  local eachPrefix::SCode.Each
                  local subModLst::List{DAE.SubMod}
                  local binding::Option{DAE.EqMod}
                  local info::DAE.SourceInfo
                  local N::ModelicaInteger = -1
                  local dcr::DAE.ComponentRef
                  local domainSubMod::DAE.SubMod
                @match (attr, inMod) begin
                  (SCode.ATTR(isField = Absyn.NONFIELD(__)), _)  => begin
                    (inDims, inMod, NONE())
                  end

                  (SCode.ATTR(isField = Absyn.FIELD(__)), DAE.MOD(finalPrefix = finalPrefix, eachPrefix = eachPrefix, subModLst = subModLst, binding = binding, info = info))  => begin
                      (domainSubMod, subModLst) = ListUtil.findAndRemove(subModLst, findDomainSubMod)
                      dcr = getQualDcr(domainSubMod, inInfo)
                      (N, dcr) = getNDcr(dcr)
                      if N == (-1)
                        Error.addSourceMessageAndFail(Error.PDEModelica_ERROR, list("Domain of the field variable '" + name + "' not found."), inInfo)
                      end
                      subModLst = listReverse(subModLst)
                      subModLst = ListUtil.map(subModLst, addEach)
                      outMod = DAE.MOD(finalPrefix, eachPrefix, subModLst, binding, info)
                      dim_f = DAE.DIM_INTEGER(N)
                    (_cons(dim_f, inDims), outMod, SOME((Absyn.CREF_IDENT(name, nil), dcr)))
                  end

                  (_, DAE.NOMOD(__))  => begin
                      Error.addSourceMessageAndFail(Error.PDEModelica_ERROR, list("Field variable '" + name + "' has no domain modifier."), inInfo)
                    (inDims, inMod, NONE())
                  end
                end
              end
          (outDims, outMod, outFieldDomOpt)
        end

        function findDomainSubMod(subMod::DAE.SubMod) ::Bool
              local isDomain::Bool

              isDomain = begin
                @match subMod begin
                  DAE.NAMEMOD(ident = "domain")  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isDomain
        end

        function getQualDcr(domainSubMod::DAE.SubMod, inInfo::SourceInfo) ::DAE.ComponentRef
              local dcr::DAE.ComponentRef

              dcr = begin
                  local cr::DAE.ComponentRef
                @match domainSubMod begin
                  DAE.NAMEMOD(ident = "domain", mod = DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = DAE.CREF(componentRef = cr, ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = Absyn.FULLYQUALIFIED(path = Absyn.IDENT(name = "DomainLineSegment1D")))))))))  => begin
                    cr
                  end

                  _  => begin
                      Error.addSourceMessageAndFail(Error.PDEModelica_ERROR, list("The domain type is wrong.\\n"), inInfo)
                    fail()
                  end
                end
              end
          dcr
        end

        function getNDcr(dcr::DAE.ComponentRef) ::Tuple{ModelicaInteger, DAE.ComponentRef}
              local outCrOpt::DAE.ComponentRef
              local outN::ModelicaInteger

              (outN, outCrOpt) = begin
                  local cr1::DAE.ComponentRef
                  local varLst::List{DAE.Var}
                  local N::ModelicaInteger
                @match dcr begin
                  DAE.CREF_QUAL(componentRef = cr1)  => begin
                    getNDcr(cr1)
                  end

                  DAE.CREF_IDENT(identType = DAE.T_COMPLEX(varLst = varLst))  => begin
                      N = ListUtil.findSome(varLst, findN)
                    (N, dcr)
                  end
                end
              end
          (outN, outCrOpt)
        end

         #= a map function to find N in domain class modifiers =#
        function findN(inVar::DAE.Var) ::Option{ModelicaInteger}
              local optN::Option{ModelicaInteger}

              optN = begin
                  local N::ModelicaInteger
                @match inVar begin
                  DAE.TYPES_VAR(name = "N", binding = DAE.EQBOUND(evaluatedExp = SOME(Values.INTEGER(N))))  => begin
                    SOME(N)
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          optN
        end

         #= map function that adds each prefix to given modifier =#
        function addEach(inSubMod::DAE.SubMod) ::DAE.SubMod
              local outSubMod::DAE.SubMod

              local ident::DAE.Ident

              local finalPrefix::SCode.Final

              local eachPrefix::SCode.Each

              local subModLst::List{DAE.SubMod}

              local binding::Option{DAE.EqMod}

              local info::DAE.SourceInfo
               #= /*  equation
                  DAE.NAMEMOD(ident, DAE.MOD(finalPrefix, _, subModLst, eqModOption)) = inSubMod;
                  outSubMod = DAE.NAMEMOD(ident, DAE.MOD(finalPrefix, SCode.EACH(), subModLst, eqModOption));*/ =#

              outSubMod = begin
                @match inSubMod begin
                  DAE.NAMEMOD(ident, DAE.MOD(finalPrefix, _, subModLst, binding, info))  => begin
                    DAE.NAMEMOD(ident, DAE.MOD(finalPrefix, SCode.EACH(), subModLst, binding, info))
                  end
                end
              end
          outSubMod
        end

         #= ----end elabField and sub funs
         =#

        function optAppendField(inDomFieldsLst::DomainFieldsLst, fieldDomOpt::DomainFieldOpt) ::DomainFieldsLst
              local outDomFieldsLst::DomainFieldsLst

              outDomFieldsLst = begin
                  local fieldCr::Absyn.ComponentRef
                  local domainCr::DAE.ComponentRef
                  local found::Bool
                @match fieldDomOpt begin
                  NONE()  => begin
                    inDomFieldsLst
                  end

                  SOME((fieldCr, domainCr))  => begin
                      (outDomFieldsLst, found) = ListUtil.map2Fold(inDomFieldsLst, optAppendFieldMapFun, domainCr, fieldCr, false)
                      if ! found
                        outDomFieldsLst = _cons((domainCr, list(fieldCr)), inDomFieldsLst)
                      end
                    outDomFieldsLst
                  end
                end
              end
          outDomFieldsLst
        end

        function optAppendFieldMapFun(inDomainFields::Tuple{<:DAE.ComponentRef, List{<:Absyn.ComponentRef}}, domainCrToAdd::DAE.ComponentRef, fieldCrToAdd::Absyn.ComponentRef, inFound::Bool) ::Tuple{Tuple{DAE.ComponentRef, List{Absyn.ComponentRef}}, Bool}
              local outFound::Bool
              local outDomainFields::Tuple{DAE.ComponentRef, List{Absyn.ComponentRef}}

              (outDomainFields, outFound) = begin
                  local domainCr::DAE.ComponentRef
                  local fieldCrLst::List{Absyn.ComponentRef}
                @matchcontinue (inDomainFields, inFound) begin
                  ((domainCr, fieldCrLst), false)  => begin
                      @match true = ComponentReference.crefEqual(domainCr, domainCrToAdd)
                    ((domainCr, _cons(fieldCrToAdd, fieldCrLst)), true)
                  end

                  _  => begin
                      (inDomainFields, inFound)
                  end
                end
              end
          (outDomainFields, outFound)
        end

         #= ----end optAppendField and sub funs
         =#

        function discretizePDE(inEQ::SCode.Equation, inDomFieldLst::DomainFieldsLst, inDiscretizedEQs::List{<:SCode.Equation}) ::List{SCode.Equation}
              local outDiscretizedEQs::List{SCode.Equation}

              local newDiscretizedEQs::List{SCode.Equation}

              newDiscretizedEQs = begin
                  local lhs_exp::Absyn.Exp
                  local rhs_exp::Absyn.Exp
                  local domainCr::Absyn.ComponentRef
                  local domainCr1::Absyn.ComponentRef
                  local fieldCr::Absyn.ComponentRef
                  local comment::SCode.Comment
                  local info::SCode.SourceInfo
                  local N::ModelicaInteger
                  local fieldLst::List{Absyn.ComponentRef}
                  local name::Absyn.Ident
                  local subscripts::List{Absyn.Subscript}
                   #= PDE with domain specified, allow for field variables:
                   =#
                @match inEQ begin
                  SCode.EQUATION(SCode.EQ_PDE(expLeft = lhs_exp, expRight = rhs_exp, domain = domainCr && Absyn.CREF_IDENT(__), comment = comment, info = info))  => begin
                      (N, fieldLst) = getDomNFields(inDomFieldLst, domainCr, info)
                    creatFieldEqs(lhs_exp, rhs_exp, domainCr, N, fieldLst, comment, info)
                  end

                  SCode.EQUATION(SCode.EQ_PDE(expLeft = lhs_exp, expRight = rhs_exp, domain = domainCr && Absyn.CREF_QUAL(name, subscripts, Absyn.CREF_IDENT(name = "interior")), comment = comment, info = info))  => begin
                      domainCr1 = Absyn.CREF_IDENT(name, subscripts)
                      (N, fieldLst) = getDomNFields(inDomFieldLst, domainCr1, info)
                    creatFieldEqs(lhs_exp, rhs_exp, domainCr, N, fieldLst, comment, info)
                  end

                  SCode.EQUATION(SCode.EQ_PDE(expLeft = lhs_exp, expRight = rhs_exp, domain = Absyn.CREF_QUAL(name, subscripts, Absyn.CREF_IDENT(name = "left")), comment = comment, info = info))  => begin
                      domainCr1 = Absyn.CREF_IDENT(name, subscripts)
                      (N, fieldLst) = getDomNFields(inDomFieldLst, domainCr1, info)
                      (lhs_exp, _) = AbsynUtil.traverseExp(lhs_exp, extrapFieldTraverseFun, 1)
                      (rhs_exp, _) = AbsynUtil.traverseExp(rhs_exp, extrapFieldTraverseFun, 1)
                    list(newEQFun(1, lhs_exp, rhs_exp, domainCr1, N, true, fieldLst, comment, info))
                  end

                  SCode.EQUATION(SCode.EQ_PDE(expLeft = lhs_exp, expRight = rhs_exp, domain = Absyn.CREF_QUAL(name, subscripts, Absyn.CREF_IDENT(name = "right")), comment = comment, info = info))  => begin
                      domainCr1 = Absyn.CREF_IDENT(name, subscripts)
                      (N, fieldLst) = getDomNFields(inDomFieldLst, domainCr1, info)
                      (lhs_exp, _) = AbsynUtil.traverseExp(lhs_exp, extrapFieldTraverseFun, N)
                      (rhs_exp, _) = AbsynUtil.traverseExp(rhs_exp, extrapFieldTraverseFun, N)
                    list(newEQFun(N, lhs_exp, rhs_exp, domainCr1, N, true, fieldLst, comment, info))
                  end

                  SCode.EQUATION(SCode.EQ_PDE(__))  => begin
                      print("Unhandled type of EQ_PDE in discretizePDE\\n")
                      fail()
                    nil
                  end

                  _  => begin
                      list(inEQ)
                  end
                end
              end
               #= same as previous but with \".interior\"
               =#
               #= left boundary condition or extrapolation
               =#
               #= right boundary condition or extrapolation
               =#
               #= Unhandled pde
               =#
               #= Other than EQ_PDE:
               =#
              outDiscretizedEQs = listAppend(inDiscretizedEQs, newDiscretizedEQs)
          outDiscretizedEQs
        end

        function extrapFieldTraverseFun(inExp::Absyn.Exp, inN::ModelicaInteger #= If N = 1 then left extrapolation, right extrapolation otherwise =#) ::Tuple{Absyn.Exp, ModelicaInteger}
              local outN::ModelicaInteger = inN
              local outExp::Absyn.Exp

              outExp = begin
                  local name::Absyn.Ident
                  local subscripts::List{Absyn.Subscript}
                  local i::ModelicaInteger
                @match inExp begin
                  Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "extrapolateField", subscripts =  nil()), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(Absyn.CREF_IDENT(name, subscripts)) <|  nil()))  => begin
                      if inN == 1
                        i = 1
                      else
                        i = -1
                      end
                    Absyn.BINARY(Absyn.BINARY(Absyn.INTEGER(2), Absyn.MUL(), Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(inN)), subscripts)))), Absyn.SUB(), Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(inN + i)), subscripts))))
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #= TODO: add check wheter the field in extrapolateField arg is in given domain.
               =#
          (outExp, outN)
        end

        function getDomNFields(inDomFieldLst::DomainFieldsLst, inDomainCr::Absyn.ComponentRef, info::SCode.SourceInfo) ::Tuple{ModelicaInteger, List{Absyn.ComponentRef}}
              local outFieldLst::List{Absyn.ComponentRef} = nil
              local outN::ModelicaInteger = 0

              try
                (outN, outFieldLst) = ListUtil.findSome1(inDomFieldLst, domNFieldsFindFun, inDomainCr)
              catch
                Error.addSourceMessageAndFail(Error.COMPILER_ERROR, list("There are no fields defined within the domain of this equation."), info)
              end
          (outN, outFieldLst)
        end

        function domNFieldsFindFun(inDomFields::Tuple{<:DAE.ComponentRef, List{<:Absyn.ComponentRef}}, inDomainCr::Absyn.ComponentRef) ::Option{Tuple{ModelicaInteger, List{Absyn.ComponentRef}}}
              local outOptNFields::Option{Tuple{ModelicaInteger, List{Absyn.ComponentRef}}}

              outOptNFields = begin
                  local domainCr::DAE.ComponentRef
                  local fieldCrLst::List{Absyn.ComponentRef}
                  local varLst::List{DAE.Var}
                  local N::ModelicaInteger
                @matchcontinue inDomFields begin
                  (domainCr, fieldCrLst)  => begin
                      @match true = absynDAECrefEqualName(inDomainCr, domainCr)
                      @match DAE.CREF_IDENT(identType = DAE.T_COMPLEX(varLst = varLst)) = domainCr
                      N = ListUtil.findSome(varLst, findN)
                    SOME((N, fieldCrLst))
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          outOptNFields
        end

        function absynDAECrefEqualName(domainCr1::Absyn.ComponentRef, domainCr2::DAE.ComponentRef) ::Bool
              local equal::Bool

              local name1::String
              local name2::String

               #= TODO: implement
               =#
              equal = begin
                @match (domainCr1, domainCr2) begin
                  (Absyn.CREF_IDENT(name = name1), DAE.CREF_IDENT(ident = name2)) where (stringEqual(name1, name2))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          equal
        end

        function extrapolateFieldEq(isRight::Bool, fieldCr::Absyn.ComponentRef, domainCr::Absyn.ComponentRef, N::ModelicaInteger, comment::SCode.Comment, info::SCode.SourceInfo, fieldLst::List{<:Absyn.ComponentRef}) ::SCode.Equation
              local outEQ::SCode.Equation

              local name::Absyn.Ident

              local subscripts::List{Absyn.Subscript}

              local i1::ModelicaInteger = 1
              local i2::ModelicaInteger = 2
              local i3::ModelicaInteger = 3

              if ListUtil.isMemberOnTrue(fieldCr, fieldLst, AbsynUtil.crefEqual)
                (name, subscripts) = begin
                  @match fieldCr begin
                    Absyn.CREF_IDENT(name = name, subscripts = subscripts)  => begin
                      (name, subscripts)
                    end
                  end
                end
                if isRight
                  i1 = N
                  i2 = N - 1
                  i3 = N - 2
                end
                outEQ = SCode.EQUATION(SCode.EQ_EQUALS(Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i1)), subscripts))), Absyn.BINARY(Absyn.BINARY(Absyn.INTEGER(2), Absyn.MUL(), Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i2)), subscripts)))), Absyn.SUB(), Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i3)), subscripts)))), comment, info))
              else
                fail()
              end
               #= left eq:   u_1 = 2*u_2 - u_3
               =#
               #= right eq:  u_N = 2*u_{N-1} - u_{N-2}
               =#
          outEQ
        end

         #= creates list of equations for fields. If the equation contains pder it spans 2:N-1, otherwise 1:N =#
        function creatFieldEqs(lhs_exp::Absyn.Exp, rhs_exp::Absyn.Exp, domainCr::Absyn.ComponentRef, N::ModelicaInteger, fieldLst::List{<:Absyn.ComponentRef}, comment::SCode.Comment, info::SCode.SourceInfo) ::List{SCode.Equation}
              local outDiscretizedEQs::List{SCode.Equation}

              local bl::Bool
              local br::Bool

              (_, bl) = AbsynUtil.traverseExp(lhs_exp, hasPderTraverseFun, false)
              (_, br) = AbsynUtil.traverseExp(rhs_exp, hasPderTraverseFun, false)
               #= outDiscretizedEQs := match (AbsynUtil.traverseExp(lhs_exp, hasPderTraverseFun, false),Absyn.traverseExp(rhs_exp, hasPderTraverseFun, false))
               =#
              outDiscretizedEQs = begin
                @match (bl, br) begin
                  (false, false)  => begin
                    list(newEQFun(i, lhs_exp, rhs_exp, domainCr, N, false, fieldLst, comment, info) for i in 1:N)
                  end

                  _  => begin
                      list(newEQFun(i, lhs_exp, rhs_exp, domainCr, N, false, fieldLst, comment, info) for i in 1:N)
                  end
                end
              end
               #= case ((_,false),(_,false)) no pder()
               =#
               #= no pder()
               =#
               #= TODO: both branches are the same now, when using ghost cells, simplify!
               =#
               #= contains some pder()
               =#
          outDiscretizedEQs
        end

        function hasPderTraverseFun(inExp::Absyn.Exp, inHasPder::Bool) ::Tuple{Absyn.Exp, Bool}
              local outHasPder::Bool
              local outExp::Absyn.Exp = inExp

              outHasPder = begin
                @match (inExp, inHasPder) begin
                  (_, true)  => begin
                    true
                  end

                  (Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "pder")), _)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          (outExp, outHasPder)
        end

        function newEQFun(i::ModelicaInteger, inLhs_exp::Absyn.Exp, inRhs_exp::Absyn.Exp, domainCr::Absyn.ComponentRef, N::ModelicaInteger, isBC::Bool, fieldLst::List{<:Absyn.ComponentRef}, comment::SCode.Comment, info::SCode.SourceInfo) ::SCode.Equation
              local outEQ::SCode.Equation

              local outLhs_exp::Absyn.Exp
              local outRhs_exp::Absyn.Exp

              (outLhs_exp, _) = AbsynUtil.traverseExpTopDown(inLhs_exp, discretizeTraverseFun, (i, fieldLst, domainCr, info, false, N, isBC))
              (outRhs_exp, _) = AbsynUtil.traverseExpTopDown(inRhs_exp, discretizeTraverseFun, (i, fieldLst, domainCr, info, false, N, isBC))
              outEQ = SCode.EQUATION(SCode.EQ_EQUALS(outLhs_exp, outRhs_exp, comment, info))
          outEQ
        end

        function discretizeTraverseFun(inExp::Absyn.Exp, inTup::Tuple{<:ModelicaInteger, List{<:Absyn.ComponentRef}, Absyn.ComponentRef, SCode.SourceInfo, Bool, ModelicaInteger, Bool}) ::Tuple{Absyn.Exp, Tuple{ModelicaInteger, List{Absyn.ComponentRef}, Absyn.ComponentRef, SCode.SourceInfo, Bool, ModelicaInteger, Bool}}
              local outTup::Tuple{ModelicaInteger, List{Absyn.ComponentRef}, Absyn.ComponentRef, SCode.SourceInfo, Bool, ModelicaInteger, Bool}
              local outExp::Absyn.Exp

              local i::ModelicaInteger
              local N::ModelicaInteger
               #=    protected String eqDomainName;
               =#

              local fieldLst::List{Absyn.ComponentRef}

              local info::SCode.SourceInfo

              local skip::Bool
              local failVar::Bool
              local isBC::Bool

              local domainCr::Absyn.ComponentRef

              local domName::Absyn.Ident

              failVar = false
              (i, fieldLst, domainCr, info, skip, N, isBC) = inTup
              @match Absyn.CREF_IDENT(name = domName) = domainCr
              if skip
                outExp = inExp
                outTup = inTup
                return (outExp, outTup)
              end
              outExp = begin
                  local name::Absyn.Ident
                  local fieldDomainName::Absyn.Ident
                  local subscripts::List{Absyn.Subscript}
                  local fieldCr::Absyn.ComponentRef
                  local exp::Absyn.Exp
                  local leftVar::Absyn.Exp
                  local actualVar::Absyn.Exp
                  local rightVar::Absyn.Exp
                @matchcontinue inExp begin
                  Absyn.CREF(Absyn.CREF_QUAL(name = domName, subscripts =  nil(), componentRef = Absyn.CREF_IDENT(name = "x", subscripts =  nil())))  => begin
                    Absyn.CREF(Absyn.CREF_QUAL(name = domName, subscripts = nil, componentRef = Absyn.CREF_IDENT(name = "x", subscripts = list(Absyn.SUBSCRIPT(Absyn.INTEGER(i))))))
                  end

                  Absyn.CREF(fieldCr && Absyn.CREF_IDENT(name, subscripts))  => begin
                      @match true = ListUtil.isMemberOnTrue(fieldCr, fieldLst, AbsynUtil.crefEqual)
                      exp = if isBC && i == 1
                            Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostL"), subscripts))
                          elseif (isBC && i == N)
                                Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostR"), subscripts))
                          else
                            Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i)), subscripts)))
                          end
                    exp
                  end

                  Absyn.CALL(Absyn.CREF_IDENT("pder",  nil()), Absyn.FUNCTIONARGS(Absyn.CREF(fieldCr && Absyn.CREF_IDENT(name, subscripts)) <| Absyn.CREF(Absyn.CREF_IDENT(name = "x")) <|  nil(), _))  => begin
                      if ! ListUtil.isMemberOnTrue(fieldCr, fieldLst, AbsynUtil.crefEqual)
                        failVar = true
                        Error.addSourceMessageAndFail(Error.COMPILER_ERROR, list("Field variable '" + name + "' has different domain than the equation or is not a field."), info)
                      end
                      leftVar = if i == 1
                            Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostL"), subscripts))
                          else
                            Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i - 1)), subscripts)))
                          end
                      rightVar = if i == N
                            Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostR"), subscripts))
                          else
                            Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i + 1)), subscripts)))
                          end
                    Absyn.BINARY(Absyn.BINARY(rightVar, Absyn.SUB(), leftVar), Absyn.DIV(), Absyn.BINARY(Absyn.INTEGER(2), Absyn.MUL(), Absyn.CREF(Absyn.CREF_QUAL(domName, nil, Absyn.CREF_IDENT("dx", nil)))))
                  end

                  Absyn.CALL(Absyn.CREF_IDENT("pder",  nil()), Absyn.FUNCTIONARGS(Absyn.CREF(fieldCr && Absyn.CREF_IDENT(name, subscripts)) <| Absyn.CREF(Absyn.CREF_IDENT(name = "x")) <| Absyn.CREF(Absyn.CREF_IDENT(name = "x")) <|  nil(), _))  => begin
                      if ! ListUtil.isMemberOnTrue(fieldCr, fieldLst, AbsynUtil.crefEqual)
                        failVar = true
                        Error.addSourceMessageAndFail(Error.COMPILER_ERROR, list("Field variable '" + name + "' has different domain than the equation or is not a field."), info)
                      end
                      leftVar = if i == 1
                            Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostL"), subscripts))
                          else
                            Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i - 1)), subscripts)))
                          end
                      actualVar = Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i)), subscripts)))
                      rightVar = if i == N
                            Absyn.CREF(Absyn.CREF_IDENT(stringAppend(name, "ghostR"), subscripts))
                          else
                            Absyn.CREF(Absyn.CREF_IDENT(name, _cons(Absyn.SUBSCRIPT(Absyn.INTEGER(i + 1)), subscripts)))
                          end
                    Absyn.BINARY(Absyn.BINARY(Absyn.BINARY(leftVar, Absyn.SUB(), Absyn.BINARY(Absyn.INTEGER(2), Absyn.MUL(), actualVar)), Absyn.ADD(), rightVar), Absyn.DIV(), Absyn.BINARY(Absyn.CREF(Absyn.CREF_QUAL(domName, nil, Absyn.CREF_IDENT("dx", nil))), Absyn.POW(), Absyn.INTEGER(2)))
                  end

                  Absyn.CALL(Absyn.CREF_IDENT("pder",  nil()), Absyn.FUNCTIONARGS(Absyn.CREF(_) <| _ <|  nil(), _))  => begin
                      Error.addSourceMessageAndFail(Error.COMPILER_ERROR, list("You are differentiating with respect to variable that is not a coordinate."), info)
                    inExp
                  end

                  Absyn.CALL(Absyn.CREF_IDENT("pder",  nil()), Absyn.FUNCTIONARGS(_ <| _ <|  nil(), _))  => begin
                      Error.addSourceMessageAndFail(Error.COMPILER_ERROR, list("Unsupported partial derivative."), info)
                    inExp
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #= skip = true
               =#
               #= pder with differentiating wrt wrong variable
               =#
              if failVar
                fail()
              end
              outTup = (i, fieldLst, domainCr, info, skip, N, isBC)
          (outExp, outTup)
        end

        function findDomF(inTup::Tuple{String, T}, name::String)  where {T}
              local found::Bool

              found = begin
                  local nameLoc::String
                @match inTup begin
                  (nameLoc, _) where (stringEqual(nameLoc, name))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          found
        end

         #= /*
        public function findDomains
          input SCode.Element el;
          input list<tuple<String,Integer>> domainLstIn;
          output list<tuple<String,Integer>> domainLstOut;
        algorithm
        TODO: rewrite to use instantiated domain elements
          domainLstOut := match el
            local
              String name;
              list<SCode.SubMod> subModLst;
              Integer N;
            case SCode.COMPONENT(typeSpec=Absyn.TPATH(path=Absyn.IDENT(name=\"DomainLineSegment1D\")), name = name,
              modifications = SCode.MOD(subModLst = subModLst))
              then
                (name,findDomains1(subModLst))::domainLstIn;
              else
              domainLstIn;
          end match;
        end findDomains;


        protected function findDomains1
          input list<SCode.SubMod> subModLst;
          output Integer N;
        algorithm
          try
            N := match List.find(subModLst,findDomains2)
            local
              Integer n;
            case SCode.NAMEMOD(\"N\",SCode.MOD(binding = SOME(Absyn.INTEGER(n))))
            then
              n;
            end match;
          else
            print(\"\\nError: Variable N not found in the domain.\\n\");
            fail();
          end try;
        end findDomains1;

        protected function findDomains2
          input SCode.SubMod subMod;
          output Boolean found;
        algorithm
          found := match subMod
            case SCode.NAMEMOD(ident = \"N\")
              then
                true;
              else
                false;
          end match;
        end findDomains2;
        */ =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

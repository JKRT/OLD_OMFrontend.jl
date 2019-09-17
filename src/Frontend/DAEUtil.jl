  module DAEUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    FuncTypeElementTo = Function

    FuncTypeElementTo = Function

    CondFunc = Function

    CondFunc = Function

    FuncTypeElementTo = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function
    @UniontypeDecl TraverseStatementsOptions

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

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

        import SCode

        import Values

        import ValuesUtil

        import HashTable

        import HashTable2

        import Algorithm
        import BaseHashTable
        import Ceval
        import DAE.AvlTreePathFunction
        import ComponentReference
        import Config
        import ConnectUtil
        import DAEDump
        import Debug
        import DoubleEnded
        import ElementSource
        import Error
        import Expression
        import ExpressionDump
        import ExpressionSimplify
        import Flags
        import ListUtil
        import SCodeUtil
        import System
        import Types
        import Util
        import StateMachineFlatten
        import VarTransform

         #= return the DAE.Const as a string. (VAR|PARAM|CONST)
        Used for debugging. =#
        function constStr(constExpr::DAE.ConstExpr) ::String
              local str::String

              str = begin
                @match constExpr begin
                  DAE.C_VAR(__)  => begin
                    "VAR"
                  end

                  DAE.C_PARAM(__)  => begin
                    "PARAM"
                  end

                  DAE.C_CONST(__)  => begin
                    "CONST"
                  end
                end
              end
          str
        end

         #= return the DAE.Const as a friendly string. Used for debugging. =#
        function constStrFriendly(constExpr::DAE.ConstExpr) ::String
              local str::String

              str = begin
                @match constExpr begin
                  DAE.C_VAR(__)  => begin
                    ""
                  end

                  DAE.C_PARAM(__)  => begin
                    "parameter "
                  end

                  DAE.C_CONST(__)  => begin
                    "constant "
                  end
                end
              end
          str
        end

        function const2VarKind(constExpr::DAE.Const) ::DAE.VarKind
              local kind::DAE.VarKind

              kind = begin
                @match constExpr begin
                  DAE.C_VAR(__)  => begin
                    DAE.VARIABLE()
                  end

                  DAE.C_PARAM(__)  => begin
                    DAE.PARAM()
                  end

                  DAE.C_CONST(__)  => begin
                    DAE.CONST()
                  end
                end
              end
          kind
        end

         #= Dump VarParallelism to a string =#
        function dumpVarParallelismStr(inVarParallelism::DAE.VarParallelism) ::String
              local outString::String

              outString = begin
                @match inVarParallelism begin
                  DAE.NON_PARALLEL(__)  => begin
                    ""
                  end

                  DAE.PARGLOBAL(__)  => begin
                    "parglobal "
                  end

                  DAE.PARLOCAL(__)  => begin
                    "parlocal "
                  end
                end
              end
          outString
        end

         #= author: PA
          if variable is input declared at the top level of the model,
          or if it is an input in a connector instance at top level return true. =#
        function topLevelInput(inComponentRef::DAE.ComponentRef, inVarDirection::DAE.VarDirection, inConnectorType::DAE.ConnectorType) ::Bool
              local isTopLevel::Bool

              isTopLevel = begin
                @match (inVarDirection, inComponentRef) begin
                  (DAE.INPUT(__), DAE.CREF_IDENT(__))  => begin
                    true
                  end

                  (DAE.INPUT(__), _) where (ConnectUtil.faceEqual(ConnectUtil.componentFaceType(inComponentRef), Connect.OUTSIDE()))  => begin
                    topLevelConnectorType(inConnectorType)
                  end

                  _  => begin
                      false
                  end
                end
              end
          isTopLevel
        end

         #= author: PA
          if variable is output declared at the top level of the model,
          or if it is an output in a connector instance at top level return true. =#
        function topLevelOutput(inComponentRef::DAE.ComponentRef, inVarDirection::DAE.VarDirection, inConnectorType::DAE.ConnectorType) ::Bool
              local isTopLevel::Bool

              isTopLevel = begin
                @match (inVarDirection, inComponentRef) begin
                  (DAE.OUTPUT(__), DAE.CREF_IDENT(__))  => begin
                    true
                  end

                  (DAE.OUTPUT(__), _) where (ConnectUtil.faceEqual(ConnectUtil.componentFaceType(inComponentRef), Connect.OUTSIDE()))  => begin
                    topLevelConnectorType(inConnectorType)
                  end

                  _  => begin
                      false
                  end
                end
              end
          isTopLevel
        end

        function topLevelConnectorType(inConnectorType::DAE.ConnectorType) ::Bool
              local isTopLevel::Bool

              isTopLevel = begin
                @match inConnectorType begin
                  DAE.FLOW(__)  => begin
                    true
                  end

                  DAE.POTENTIAL(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isTopLevel
        end

         #= returns true if type is simple type =#
        function expTypeSimple(tp::DAE.Type) ::Bool
              local isSimple::Bool

              isSimple = begin
                @match tp begin
                  DAE.T_REAL(__)  => begin
                    true
                  end

                  DAE.T_INTEGER(__)  => begin
                    true
                  end

                  DAE.T_STRING(__)  => begin
                    true
                  end

                  DAE.T_BOOL(__)  => begin
                    true
                  end

                  DAE.T_CLOCK(__)  => begin
                    true
                  end

                  DAE.T_ENUMERATION(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
          isSimple
        end

         #= returns the element type of an array =#
        function expTypeElementType(tp::DAE.Type) ::DAE.Type
              local eltTp::DAE.Type

              eltTp = begin
                  local ty::DAE.Type
                @match tp begin
                  DAE.T_ARRAY(ty = ty)  => begin
                    expTypeElementType(ty)
                  end

                  _  => begin
                      tp
                  end
                end
              end
          eltTp
        end

         #= returns true if type is complex type =#
        function expTypeComplex(tp::DAE.Type) ::Bool
              local isComplex::Bool

              isComplex = begin
                @match tp begin
                  DAE.T_COMPLEX(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isComplex
        end

         #= returns true if type is array type
        Alternative names: isArrayType, isExpTypeArray =#
        function expTypeArray(tp::DAE.Type) ::Bool
              local isArray::Bool

              isArray = begin
                @match tp begin
                  DAE.T_ARRAY(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isArray
        end

         #= returns true if type is tuple type. =#
        function expTypeTuple(tp::DAE.Type) ::Bool
              local isTuple::Bool

              isTuple = begin
                @match tp begin
                  DAE.T_TUPLE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isTuple
        end

         #= returns the array dimensions of an ExpType =#
        function expTypeArrayDimensions(tp::DAE.Type) ::List{ModelicaInteger}
              local dims::List{ModelicaInteger}

              dims = begin
                  local array_dims::DAE.Dimensions
                @match tp begin
                  DAE.T_ARRAY(dims = array_dims)  => begin
                      dims = ListUtil.map(array_dims, Expression.dimensionSize)
                    dims
                  end
                end
              end
          dims
        end

         #= Converts a dimension to an expression, covering constants and paramters. =#
        function dimExp(dim::DAE.Dimension) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local iconst::ModelicaInteger
                @match dim begin
                  DAE.DIM_INTEGER(iconst)  => begin
                    DAE.ICONST(iconst)
                  end

                  DAE.DIM_EXP(exp)  => begin
                    exp
                  end

                  _  => begin
                        Error.addMessage(Error.DIMENSION_NOT_KNOWN, list(anyString(dim)))
                      fail()
                  end
                end
              end
          exp
        end

         #=
        Function to sort derivatives.
        Used for Util.sort =#
        function derivativeOrder(e1::Tuple{<:ModelicaInteger, DAE.derivativeCond}, e2::Tuple{<:ModelicaInteger, DAE.derivativeCond}) ::Bool
              local b::Bool

              local i1::ModelicaInteger
              local i2::ModelicaInteger

              b = begin
                @match (e1, e2) begin
                  ((i1, _), (i2, _))  => begin
                    Util.isIntGreater(i1, i2)
                  end
                end
              end
          b
        end

         #=  collects all paths representing derivative functions for a list of FunctionDefinition's =#
        function getDerivativePaths(inFuncDefs::List{<:DAE.FunctionDefinition}) ::List{Absyn.Path}
              local paths::List{Absyn.Path}

              paths = begin
                  local pLst1::List{Absyn.Path}
                  local pLst2::List{Absyn.Path}
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local funcDefs::List{DAE.FunctionDefinition}
                @matchcontinue inFuncDefs begin
                   nil()  => begin
                    nil
                  end

                  DAE.FUNCTION_DER_MAPPER(derivativeFunction = p1, defaultDerivative = SOME(p2), lowerOrderDerivatives = pLst1) <| funcDefs  => begin
                      pLst2 = getDerivativePaths(funcDefs)
                      paths = ListUtil.union(_cons(p1, _cons(p2, pLst1)), pLst2)
                    paths
                  end

                  DAE.FUNCTION_DER_MAPPER(derivativeFunction = p1, defaultDerivative = NONE(), lowerOrderDerivatives = pLst1) <| funcDefs  => begin
                      pLst2 = getDerivativePaths(funcDefs)
                      paths = ListUtil.union(_cons(p1, pLst1), pLst2)
                    paths
                  end

                  _ <| funcDefs  => begin
                    getDerivativePaths(funcDefs)
                  end
                end
              end
          paths
        end

         #=
        Set the optional equationBound value =#
        function addEquationBoundString(bindExp::DAE.Exp, attr::Option{<:DAE.VariableAttributes}) ::Option{DAE.VariableAttributes}
              local oattr::Option{DAE.VariableAttributes}

              oattr = begin
                  local e1::Option{DAE.Exp}
                  local e2::Option{DAE.Exp}
                  local e3::Option{DAE.Exp}
                  local e4::Option{DAE.Exp}
                  local e5::Option{DAE.Exp}
                  local e6::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local sSelectOption::Option{DAE.StateSelect}
                  local sSelectOption2::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOption::Option{DAE.Distribution}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                  local s::String
                @match (bindExp, attr) begin
                  (_, SOME(DAE.VAR_ATTR_REAL(e1, e2, e3, min, max, e4, e5, e6, sSelectOption, unc, distOption, _, ip, fn, so)))  => begin
                    SOME(DAE.VAR_ATTR_REAL(e1, e2, e3, min, max, e4, e5, e6, sSelectOption, unc, distOption, SOME(bindExp), ip, fn, so))
                  end

                  (_, SOME(DAE.VAR_ATTR_INT(e1, min, max, e2, e3, unc, distOption, _, ip, fn, so)))  => begin
                    SOME(DAE.VAR_ATTR_INT(e1, min, max, e2, e3, unc, distOption, SOME(bindExp), ip, fn, so))
                  end

                  (_, SOME(DAE.VAR_ATTR_BOOL(e1, e2, e3, _, ip, fn, so)))  => begin
                    SOME(DAE.VAR_ATTR_BOOL(e1, e2, e3, SOME(bindExp), ip, fn, so))
                  end

                  (_, SOME(DAE.VAR_ATTR_STRING(e1, e2, e3, _, ip, fn, so)))  => begin
                    SOME(DAE.VAR_ATTR_STRING(e1, e2, e3, SOME(bindExp), ip, fn, so))
                  end

                  (_, SOME(DAE.VAR_ATTR_ENUMERATION(e1, min, max, e2, e3, _, ip, fn, so)))  => begin
                    SOME(DAE.VAR_ATTR_ENUMERATION(e1, min, max, e2, e3, SOME(bindExp), ip, fn, so))
                  end

                  _  => begin
                        print("-failure in DAEUtil.addEquationBoundString\\n")
                      fail()
                  end
                end
              end
          oattr
        end

         #= get list of classes from Var =#
        function getClassList(v::DAE.Element) ::List{Absyn.Path}
              local lst::List{Absyn.Path}

              lst = begin
                @match v begin
                  DAE.VAR(source = DAE.SOURCE(typeLst = lst))  => begin
                    lst
                  end

                  _  => begin
                      nil
                  end
                end
              end
          lst
        end

         #=
        Returned bound equation =#
        function getBoundStartEquation(attr::DAE.VariableAttributes) ::DAE.Exp
              local oe::DAE.Exp

              oe = begin
                  local beq::DAE.Exp
                @match attr begin
                  DAE.VAR_ATTR_REAL(equationBound = SOME(beq))  => begin
                    beq
                  end

                  DAE.VAR_ATTR_INT(equationBound = SOME(beq))  => begin
                    beq
                  end

                  DAE.VAR_ATTR_BOOL(equationBound = SOME(beq))  => begin
                    beq
                  end

                  DAE.VAR_ATTR_ENUMERATION(equationBound = SOME(beq))  => begin
                    beq
                  end
                end
              end
          oe
        end

         #= Splits the DAE into one with vars and no equations and algorithms
         and another one which has all the equations and algorithms but no variables.
         Note: the functions are copied to both dae's.
          =#
        function splitDAEIntoVarsAndEquations(inDae::DAE.DAElist) ::Tuple{DAE.DAElist, DAE.DAElist}
              local allEqs::DAE.DAElist
              local allVars::DAE.DAElist

              local rest::List{DAE.Element}
              local vars::DoubleEnded.MutableList{DAE.Element}
              local eqs::DoubleEnded.MutableList{DAE.Element}

              @match DAE.DAE(rest) = inDae
              vars = DoubleEnded.fromList(nil)
              eqs = DoubleEnded.fromList(nil)
              for elt in rest
                _ = begin
                    local v::DAE.Element
                    local e::DAE.Element
                    local elts::List{DAE.Element}
                    local elts2::List{DAE.Element}
                    local elts22::List{DAE.Element}
                    local elts1::List{DAE.Element}
                    local elts11::List{DAE.Element}
                    local elts3::List{DAE.Element}
                    local elts33::List{DAE.Element}
                    local id::String
                    local source::DAE.ElementSource #= the origin of the element =#
                    local cmt::Option{SCode.Comment}
                  @match elt begin
                    DAE.VAR(__)  => begin
                        DoubleEnded.push_back(vars, elt)
                      ()
                    end

                    DAE.COMP(id, elts1, source, cmt)  => begin
                         #=  adrpo: TODO! FIXME! a DAE.COMP SHOULD NOT EVER BE HERE!
                         =#
                        @match (DAE.DAE(elts11), DAE.DAE(elts3)) = splitDAEIntoVarsAndEquations(DAE.DAE(elts1))
                        DoubleEnded.push_back(vars, DAE.COMP(id, elts11, source, cmt))
                        DoubleEnded.push_list_back(eqs, elts3)
                      ()
                    end

                    DAE.EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.EQUEQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIALEQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.ARRAY_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_ARRAY_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.COMPLEX_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_COMPLEX_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIALDEFINE(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.DEFINE(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.WHEN_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.FOR_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.IF_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_IF_EQUATION(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.ALGORITHM(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIALALGORITHM(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.EXTOBJECTCLASS(__)  => begin
                         #=  adrpo: TODO! FIXME! why are external object constructor calls added to the non-equations DAE??
                         =#
                         #=  PA: are these external object constructor CALLS? Do not think so. But they should anyway be in funcs..
                         =#
                        DoubleEnded.push_back(vars, elt)
                      ()
                    end

                    DAE.ASSERT(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_ASSERT(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.TERMINATE(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_TERMINATE(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.REINIT(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.NORETCALL(__)  => begin
                         #=  handle also NORETCALL! Connections.root(...)
                         =#
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    DAE.INITIAL_NORETCALL(__)  => begin
                        DoubleEnded.push_back(eqs, elt)
                      ()
                    end

                    _  => begin
                          Error.addInternalError(getInstanceName() + " failed for " + DAEDump.dumpDAEElementsStr(DAE.DAE(list(elt))), sourceInfo())
                        fail()
                    end
                  end
                end
              end
              allVars = DAE.DAE(DoubleEnded.toListAndClear(vars))
              allEqs = DAE.DAE(DoubleEnded.toListAndClear(eqs))
          (allVars, allEqs)
        end

         #= Remove the variables in the list from the DAE =#
        function removeVariables(dae::DAE.DAElist, vars::List{<:DAE.ComponentRef}) ::DAE.DAElist
              local outDae::DAE.DAElist

               #=  adrpo: TODO! FIXME! rather expensive function!
               =#
               #=         implement this by walking dae once and check element with each var in the list
               =#
               #=         instead of walking the dae once for each var.
               =#
               #=  outDae := List.fold(vars,removeVariable,dae);
               =#
              outDae = begin
                  local elements::List{DAE.Element}
                @match (dae, vars) begin
                  (_,  nil())  => begin
                    dae
                  end

                  (DAE.DAE(elements), _)  => begin
                      elements = removeVariablesFromElements(elements, vars)
                    DAE.DAE(elements)
                  end
                end
              end
          outDae
        end

         #= @author: adrpo
          remove the variables that match for the element list =#
        function removeVariablesFromElements(inElements::List{<:DAE.Element}, variableNames::List{<:DAE.ComponentRef}) ::List{DAE.Element}
              local outElements::List{DAE.Element} = nil

              if listEmpty(variableNames)
                outElements = inElements
                return outElements
              end
              for el in inElements
                _ = begin
                    local cr::DAE.ComponentRef
                    local elist::List{DAE.Element}
                    local v::DAE.Element
                    local id::String
                    local source::DAE.ElementSource #= the origin of the element =#
                    local cmt::Option{SCode.Comment}
                    local isEmpty::Bool
                  @match el begin
                    v && DAE.VAR(componentRef = cr)  => begin
                        if listEmpty(ListUtil.select1(variableNames, ComponentReference.crefEqual, cr))
                          outElements = _cons(v, outElements)
                        end
                      ()
                    end

                    DAE.COMP(id, elist, source, cmt)  => begin
                        elist = removeVariablesFromElements(elist, variableNames)
                        outElements = _cons(DAE.COMP(id, elist, source, cmt), outElements)
                      ()
                    end

                    _  => begin
                          outElements = _cons(el, outElements)
                        ()
                    end
                  end
                end
              end
               #=  handle components
               =#
               #=  anything else, just keep it
               =#
              outElements = MetaModelica.Dangerous.listReverseInPlace(outElements)
          outElements
        end

         #= Remove the variable from the DAE, UNUSED =#
        function removeVariable(var::DAE.ComponentRef, dae::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local cr::DAE.ComponentRef
                  local elist::List{DAE.Element}
                  local elist2::List{DAE.Element}
                  local e::DAE.Element
                  local v::DAE.Element
                  local id::String
                  local source::DAE.ElementSource #= the origin of the element =#
                  local cmt::Option{SCode.Comment}
                @matchcontinue (var, dae) begin
                  (_, DAE.DAE( nil()))  => begin
                    DAE.DAE(nil)
                  end

                  (_, DAE.DAE(DAE.VAR(componentRef = cr) <| elist))  => begin
                      @match true = ComponentReference.crefEqualNoStringCompare(var, cr)
                    DAE.DAE(elist)
                  end

                  (_, DAE.DAE(DAE.COMP(id, elist, source, cmt) <| elist2))  => begin
                      @match DAE.DAE(elist) = removeVariable(var, DAE.DAE(elist))
                      @match DAE.DAE(elist2) = removeVariable(var, DAE.DAE(elist2))
                    DAE.DAE(_cons(DAE.COMP(id, elist, source, cmt), elist2))
                  end

                  (_, DAE.DAE(e <| elist))  => begin
                      @match DAE.DAE(elist) = removeVariable(var, DAE.DAE(elist))
                    DAE.DAE(_cons(e, elist))
                  end
                end
              end
          outDae
        end

         #= Remove the inner attribute of all vars in list =#
        function removeInnerAttrs(dae::DAE.DAElist, vars::List{<:DAE.ComponentRef}) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = ListUtil.fold(vars, removeInnerAttr, dae)
          outDae
        end

         #= Remove the inner attribute from variable in the DAE =#
        function removeInnerAttr(var::DAE.ComponentRef, dae::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local cr::DAE.ComponentRef
                  local oldVar::DAE.ComponentRef
                  local newVar::DAE.ComponentRef
                  local elist::List{DAE.Element}
                  local elist2::List{DAE.Element}
                  local e::DAE.Element
                  local v::DAE.Element
                  local u::DAE.Element
                  local o::DAE.Element
                  local id::String
                  local kind::DAE.VarKind
                  local prl::DAE.VarParallelism
                  local dir::DAE.VarDirection
                  local tp::DAE.Type
                  local bind::Option{DAE.Exp}
                  local dim::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local cls::List{Absyn.Path}
                  local attr::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local io::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local prot::DAE.VarVisibility
                  local source::DAE.ElementSource #= the origin of the element =#
                @match (var, dae) begin
                  (_, DAE.DAE( nil()))  => begin
                    DAE.DAE(nil)
                  end

                  (_, DAE.DAE(DAE.VAR(oldVar, kind, dir, prl, prot, tp, bind, dim, ct, source, attr, cmt, Absyn.INNER_OUTER(__)) <| elist)) where (compareUniquedVarWithNonUnique(var, oldVar))  => begin
                      newVar = nameInnerouterUniqueCref(oldVar)
                      o = DAE.VAR(oldVar, kind, dir, prl, prot, tp, NONE(), dim, ct, source, attr, cmt, Absyn.OUTER()) #= intact =#
                      u = DAE.VAR(newVar, kind, dir, prl, prot, tp, bind, dim, ct, source, attr, cmt, Absyn.NOT_INNER_OUTER()) #=  unique'ified =#
                      elist = _cons(u, _cons(o, elist))
                    DAE.DAE(elist)
                  end

                  (_, DAE.DAE(DAE.VAR(cr, kind, dir, prl, prot, tp, bind, dim, ct, source, attr, cmt, io) <| elist)) where (ComponentReference.crefEqualNoStringCompare(var, cr))  => begin
                      io2 = removeInnerAttribute(io)
                    DAE.DAE(_cons(DAE.VAR(cr, kind, dir, prl, prot, tp, bind, dim, ct, source, attr, cmt, io2), elist))
                  end

                  (_, DAE.DAE(DAE.COMP(id, elist, source, cmt) <| elist2))  => begin
                      @match DAE.DAE(elist) = removeInnerAttr(var, DAE.DAE(elist))
                      @match DAE.DAE(elist2) = removeInnerAttr(var, DAE.DAE(elist2))
                    DAE.DAE(_cons(DAE.COMP(id, elist, source, cmt), elist2))
                  end

                  (_, DAE.DAE(e <| elist))  => begin
                      @match DAE.DAE(elist) = removeInnerAttr(var, DAE.DAE(elist))
                    DAE.DAE(_cons(e, elist))
                  end
                end
              end
               #= /* When having an inner outer, we declare two variables on the same line.
                      Since we can not handle this with current instantiation procedure, we create temporary variables in the dae.
                      These are named uniqly and renamed later in \"instClass\"
                   */ =#
          outDae
        end

         #=
        Author: BZ, workaround to get innerouter elements to work.
        This function strips the 'unique identifer' from the cref and compares.
         =#
        function compareUniquedVarWithNonUnique(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local equal::Bool

              local s1::String
              local s2::String
              local s3::String

              s1 = ComponentReference.printComponentRefStr(cr1)
              s2 = ComponentReference.printComponentRefStr(cr2)
              s1 = System.stringReplace(s1, DAE.UNIQUEIO, "")
              s2 = System.stringReplace(s2, DAE.UNIQUEIO, "")
              equal = stringEq(s1, s2)
          equal
        end

         #=
        Author: BZ, 2008-11
        Renames a var to unique name =#
        function nameInnerouterUniqueCref(inCr::DAE.ComponentRef) ::DAE.ComponentRef
              local outCr::DAE.ComponentRef

              outCr = begin
                  local newChild::DAE.ComponentRef
                  local child::DAE.ComponentRef
                  local id::String
                  local idt::DAE.Type
                  local subs::List{DAE.Subscript}
                @match inCr begin
                  DAE.CREF_IDENT(id, idt, subs)  => begin
                      id = DAE.UNIQUEIO + id
                    ComponentReference.makeCrefIdent(id, idt, subs)
                  end

                  DAE.CREF_QUAL(id, idt, subs, child)  => begin
                      newChild = nameInnerouterUniqueCref(child)
                    ComponentReference.makeCrefQual(id, idt, subs, newChild)
                  end
                end
              end
          outCr
        end

         #=
        Function for stripping a cref of its uniqified part.
        Remove 'removalString' from the cref if found
         =#
        function unNameInnerouterUniqueCref(cr::DAE.ComponentRef, removalString::String) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              ocr = begin
                  local str::String
                  local str2::String
                  local ty::DAE.Type
                  local child::DAE.ComponentRef
                  local child_2::DAE.ComponentRef
                  local subs::List{DAE.Subscript}
                @matchcontinue (cr, removalString) begin
                  (DAE.CREF_IDENT(str, ty, subs), _)  => begin
                      str2 = System.stringReplace(str, removalString, "")
                    ComponentReference.makeCrefIdent(str2, ty, subs)
                  end

                  (DAE.CREF_QUAL(str, ty, subs, child), _)  => begin
                      child_2 = unNameInnerouterUniqueCref(child, removalString)
                      str2 = System.stringReplace(str, removalString, "")
                    ComponentReference.makeCrefQual(str2, ty, subs, child_2)
                  end

                  (DAE.WILD(__), _)  => begin
                    DAE.WILD()
                  end

                  (child, _)  => begin
                      print(" failure unNameInnerouterUniqueCref: ")
                      print(ComponentReference.printComponentRefStr(child) + "\\n")
                    fail()
                  end
                end
              end
          ocr
        end

         #= Help function to removeInnerAttr =#
        function removeInnerAttribute(io::Absyn.InnerOuter) ::Absyn.InnerOuter
              local ioOut::Absyn.InnerOuter

              ioOut = begin
                @match io begin
                  Absyn.INNER(__)  => begin
                    Absyn.NOT_INNER_OUTER()
                  end

                  Absyn.INNER_OUTER(__)  => begin
                    Absyn.OUTER()
                  end

                  _  => begin
                      io
                  end
                end
              end
          ioOut
        end

         #=  returns the component reference of a variable =#
        function varCref(elt::DAE.Element) ::DAE.ComponentRef
              local cr::DAE.ComponentRef

              @match DAE.VAR(componentRef = cr) = elt
          cr
        end

         #=  gets the attributes of a DAE.Element that is VAR =#
        function getVariableAttributes(elt::DAE.Element) ::Option{DAE.VariableAttributes}
              local variableAttributesOption::Option{DAE.VariableAttributes}

              @match DAE.VAR(variableAttributesOption = variableAttributesOption) = elt
          variableAttributesOption
        end

         #=
          Return the unit attribute =#
        function getUnitAttr(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local start::DAE.Exp

              start = begin
                  local u::DAE.Exp
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(unit = SOME(u)))  => begin
                    u
                  end

                  _  => begin
                      DAE.SCONST("")
                  end
                end
              end
          start
        end

         #=
          Return the start attribute. =#
        function getStartAttrEmpty(inVariableAttributesOption::Option{<:DAE.VariableAttributes}, optExp::DAE.Exp) ::DAE.Exp
              local start::DAE.Exp

              start = begin
                  local r::DAE.Exp
                @match (inVariableAttributesOption, optExp) begin
                  (SOME(DAE.VAR_ATTR_REAL(start = SOME(r))), _)  => begin
                    r
                  end

                  (SOME(DAE.VAR_ATTR_INT(start = SOME(r))), _)  => begin
                    r
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(start = SOME(r))), _)  => begin
                    r
                  end

                  (SOME(DAE.VAR_ATTR_STRING(start = SOME(r))), _)  => begin
                    r
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(start = SOME(r))), _)  => begin
                    r
                  end

                  _  => begin
                      optExp
                  end
                end
              end
          start
        end

         #=
        Author: BZ, returns a list of optional exp, {opt<Min> opt<Max}  =#
        function getMinMax(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::List{Option{DAE.Exp}}
              local oExps::List{Option{DAE.Exp}}

              oExps = begin
                  local e1::Option{DAE.Exp}
                  local e2::Option{DAE.Exp}
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_ENUMERATION(min = e1, max = e2))  => begin
                    list(e1, e2)
                  end

                  SOME(DAE.VAR_ATTR_INT(min = e1, max = e2))  => begin
                    list(e1, e2)
                  end

                  SOME(DAE.VAR_ATTR_REAL(min = e1, max = e2))  => begin
                    list(e1, e2)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          oExps
        end

        function getMinMaxValues(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::Tuple{Option{DAE.Exp}, Option{DAE.Exp}}
              local outMaxValue::Option{DAE.Exp}
              local outMinValue::Option{DAE.Exp}

              (outMinValue, outMaxValue) = begin
                  local minValue::Option{DAE.Exp}
                  local maxValue::Option{DAE.Exp}
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_ENUMERATION(min = minValue, max = maxValue))  => begin
                    (minValue, maxValue)
                  end

                  SOME(DAE.VAR_ATTR_INT(min = minValue, max = maxValue))  => begin
                    (minValue, maxValue)
                  end

                  SOME(DAE.VAR_ATTR_REAL(min = minValue, max = maxValue))  => begin
                    (minValue, maxValue)
                  end

                  _  => begin
                      (NONE(), NONE())
                  end
                end
              end
          (outMinValue, outMaxValue)
        end

         #= Sets the min and max attributes. If inAttr is NONE(), assumes Real attributes. =#
        function setMinMax(inAttr::Option{<:DAE.VariableAttributes}, inMin::Option{<:DAE.Exp}, inMax::Option{<:DAE.Exp}) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local q::Option{DAE.Exp}
                  local u::Option{DAE.Exp}
                  local du::Option{DAE.Exp}
                  local f::Option{DAE.Exp}
                  local n::Option{DAE.Exp}
                  local i::Option{DAE.Exp}
                  local ss::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOpt::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                @match (inAttr, inMin, inMax) begin
                  (SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, i, f, n, ss, unc, distOpt, eb, ip, fn, so)), _, _)  => begin
                    if referenceEq(min, inMin) && referenceEq(max, inMax)
                          inAttr
                        else
                          SOME(DAE.VAR_ATTR_REAL(q, u, du, inMin, inMax, i, f, n, ss, unc, distOpt, eb, ip, fn, so))
                        end
                  end

                  (SOME(DAE.VAR_ATTR_INT(q, min, max, i, f, unc, distOpt, eb, ip, fn, so)), _, _)  => begin
                    if referenceEq(min, inMin) && referenceEq(max, inMax)
                          inAttr
                        else
                          SOME(DAE.VAR_ATTR_INT(q, inMin, inMax, i, f, unc, distOpt, eb, ip, fn, so))
                        end
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, du, eb, ip, fn, so)), _, _)  => begin
                    if referenceEq(min, inMin) && referenceEq(max, inMax)
                          inAttr
                        else
                          SOME(DAE.VAR_ATTR_ENUMERATION(q, inMin, inMax, u, du, eb, ip, fn, so))
                        end
                  end

                  (NONE(), _, _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), inMin, inMax, NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE()))
                  end
                end
              end
          outAttr
        end

         #=
          Return the start attribute. =#
        function getStartAttr(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local start::DAE.Exp

              start = begin
                  local r::DAE.Exp
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_INT(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_BOOL(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_STRING(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(start = SOME(r)))  => begin
                    r
                  end

                  _  => begin
                      DAE.RCONST(0.0)
                  end
                end
              end
          start
        end

         #=
          Return the startOrigin attribute =#
        function getStartOrigin(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::Option{DAE.Exp}
              local startOrigin::Option{DAE.Exp}

              startOrigin = begin
                  local so::Option{DAE.Exp}
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(startOrigin = so))  => begin
                    so
                  end

                  SOME(DAE.VAR_ATTR_INT(startOrigin = so))  => begin
                    so
                  end

                  SOME(DAE.VAR_ATTR_BOOL(startOrigin = so))  => begin
                    so
                  end

                  SOME(DAE.VAR_ATTR_STRING(startOrigin = so))  => begin
                    so
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(startOrigin = so))  => begin
                    so
                  end

                  NONE()  => begin
                    NONE()
                  end
                end
              end
          startOrigin
        end

         #=
          Return the start attribute. or fails =#
        function getStartAttrFail(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local start::DAE.Exp

              start = begin
                  local r::DAE.Exp
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_INT(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_BOOL(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_STRING(start = SOME(r)))  => begin
                    r
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(start = SOME(r)))  => begin
                    r
                  end
                end
              end
          start
        end

         #=
          Return the nominal attribute. or fails =#
        function getNominalAttrFail(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local nominal::DAE.Exp

              nominal = begin
                  local r::DAE.Exp
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(nominal = SOME(r)))  => begin
                    r
                  end
                end
              end
          nominal
        end

         #=
          Return the min attribute. or fails =#
        function getMinAttrFail(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local outMin::DAE.Exp

              @match SOME(DAE.VAR_ATTR_REAL(min = SOME(outMin))) = inVariableAttributesOption
          outMin
        end

         #=
          Return the max attribute. or fails =#
        function getMaxAttrFail(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local outMax::DAE.Exp

              @match SOME(DAE.VAR_ATTR_REAL(max = SOME(outMax))) = inVariableAttributesOption
          outMax
        end

         #= sets the attributes of a DAE.Element that is VAR =#
        function setVariableAttributes(var::DAE.Element, varOpt::Option{<:DAE.VariableAttributes}) ::DAE.Element
              local v::DAE.Element = var

              v = begin
                @match v begin
                  DAE.VAR(__)  => begin
                      v.variableAttributesOption = varOpt
                    v
                  end
                end
              end
          v
        end

         #=
          sets the stateselect attribute. If NONE(), assumes Real attributes. =#
        function setStateSelect(attr::Option{<:DAE.VariableAttributes}, s::DAE.StateSelect) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local va::DAE.VariableAttributes
                @match attr begin
                  SOME(va && DAE.VAR_ATTR_REAL(__))  => begin
                      va.stateSelectOption = SOME(s)
                    SOME(va)
                  end

                  NONE()  => begin
                    SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), SOME(s), NONE(), NONE(), NONE(), NONE(), NONE(), NONE()))
                  end
                end
              end
          outAttr
        end

         #=
          sets the start attribute. If NONE(), assumes Real attributes. =#
        function setStartAttr(attr::Option{<:DAE.VariableAttributes}, start::DAE.Exp) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = setStartAttrOption(attr, SOME(start))
          outAttr
        end

         #=
          sets the start attribute. If NONE(), assumes Real attributes. =#
        function setStartAttrOption(attr::Option{<:DAE.VariableAttributes}, start::Option{<:DAE.Exp}) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local va::DAE.VariableAttributes
                  local at::Option{DAE.VariableAttributes}
                @match attr begin
                  SOME(va && DAE.VAR_ATTR_REAL(__))  => begin
                      if valueEq(va.start, start)
                        at = attr
                      else
                        va.start = start
                        at = SOME(va)
                      end
                    at
                  end

                  SOME(va && DAE.VAR_ATTR_INT(__))  => begin
                      if valueEq(va.start, start)
                        at = attr
                      else
                        va.start = start
                        at = SOME(va)
                      end
                    at
                  end

                  SOME(va && DAE.VAR_ATTR_BOOL(__))  => begin
                      if valueEq(va.start, start)
                        at = attr
                      else
                        va.start = start
                        at = SOME(va)
                      end
                    at
                  end

                  SOME(va && DAE.VAR_ATTR_STRING(__))  => begin
                      if valueEq(va.start, start)
                        at = attr
                      else
                        va.start = start
                        at = SOME(va)
                      end
                    at
                  end

                  SOME(va && DAE.VAR_ATTR_ENUMERATION(__))  => begin
                      if valueEq(va.start, start)
                        at = attr
                      else
                        va.start = start
                        at = SOME(va)
                      end
                    at
                  end

                  NONE()  => begin
                    if isNone(start)
                          NONE()
                        else
                          SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), NONE(), NONE(), start, NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE()))
                        end
                  end
                end
              end
          outAttr
        end

         #=
          sets the startOrigin attribute. If NONE(), assumes Real attributes. =#
        function setStartOrigin(attr::Option{<:DAE.VariableAttributes}, startOrigin::Option{<:DAE.Exp}) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local va::DAE.VariableAttributes
                @match attr begin
                  SOME(va && DAE.VAR_ATTR_REAL(__))  => begin
                      va.startOrigin = startOrigin
                    SOME(va)
                  end

                  SOME(va && DAE.VAR_ATTR_INT(__))  => begin
                      va.startOrigin = startOrigin
                    SOME(va)
                  end

                  SOME(va && DAE.VAR_ATTR_BOOL(__))  => begin
                      va.startOrigin = startOrigin
                    SOME(va)
                  end

                  SOME(va && DAE.VAR_ATTR_STRING(__))  => begin
                      va.startOrigin = startOrigin
                    SOME(va)
                  end

                  SOME(va && DAE.VAR_ATTR_ENUMERATION(__))  => begin
                      va.startOrigin = startOrigin
                    SOME(va)
                  end

                  NONE()  => begin
                    if isNone(startOrigin)
                          NONE()
                        else
                          SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), startOrigin))
                        end
                  end
                end
              end
          outAttr
        end

         #=
          returns the nominal attribute. If NONE(), assumes Real attributes. =#
        function getNominalAttr(attr::Option{<:DAE.VariableAttributes}) ::DAE.Exp
              local nominal::DAE.Exp

              nominal = begin
                  local n::DAE.Exp
                @match attr begin
                  SOME(DAE.VAR_ATTR_REAL(nominal = SOME(n)))  => begin
                    n
                  end

                  _  => begin
                      DAE.RCONST(1.0)
                  end
                end
              end
          nominal
        end

         #=
          sets the nominal attribute. If NONE(), assumes Real attributes. =#
        function setNominalAttr(attr::Option{<:DAE.VariableAttributes}, nominal::DAE.Exp) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local va::DAE.VariableAttributes
                @match attr begin
                  SOME(va && DAE.VAR_ATTR_REAL(__))  => begin
                      va.nominal = SOME(nominal)
                    SOME(va)
                  end

                  NONE()  => begin
                    SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), SOME(nominal), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE()))
                  end
                end
              end
          outAttr
        end

         #=
          sets the unit attribute. =#
        function setUnitAttr(attr::Option{<:DAE.VariableAttributes}, unit::DAE.Exp) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local q::Option{DAE.Exp}
                  local u::Option{DAE.Exp}
                  local du::Option{DAE.Exp}
                  local f::Option{DAE.Exp}
                  local n::Option{DAE.Exp}
                  local s::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local ss::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOpt::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                @match (attr, unit) begin
                  (SOME(DAE.VAR_ATTR_REAL(q, _, du, min, max, s, f, n, ss, unc, distOpt, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(q, SOME(unit), du, min, max, s, f, n, ss, unc, distOpt, eb, ip, fn, so))
                  end

                  (NONE(), _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(NONE(), SOME(unit), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE()))
                  end
                end
              end
          outAttr
        end

         #=
          This function takes a VAR elemets and sets var visibility. =#
        function setElementVarVisibility(elt::DAE.Element, visibility::DAE.VarVisibility) ::DAE.Element
              local e::DAE.Element = elt

              e = begin
                @match e begin
                  DAE.VAR(__)  => begin
                      e.protection = visibility
                    e
                  end

                  _  => begin
                      e
                  end
                end
              end
          e
        end

         #=
          This function takes a VAR elemets and sets var direction. =#
        function setElementVarDirection(elt::DAE.Element, direction::DAE.VarDirection) ::DAE.Element
              local e::DAE.Element = elt

              e = begin
                @match e begin
                  DAE.VAR(__)  => begin
                      e.direction = direction
                    e
                  end

                  _  => begin
                      e
                  end
                end
              end
          e
        end

         #= Sets the binding of a VAR DAE.Element. =#
        function setElementVarBinding(elt::DAE.Element, binding::Option{<:DAE.Exp}) ::DAE.Element
              local e::DAE.Element = elt

              e = begin
                @match e begin
                  DAE.VAR(__)  => begin
                      e.binding = binding
                    e
                  end

                  _  => begin
                      e
                  end
                end
              end
          e
        end

         #=
          sets the start attribute. If NONE(), assumes Real attributes. =#
        function setProtectedAttr(attr::Option{<:DAE.VariableAttributes}, isProtected::Bool) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local q::Option{DAE.Exp}
                  local u::Option{DAE.Exp}
                  local du::Option{DAE.Exp}
                  local i::Option{DAE.Exp}
                  local f::Option{DAE.Exp}
                  local n::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local ss::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOpt::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                @match attr begin
                  SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, i, f, n, ss, unc, distOpt, eb, _, fn, so))  => begin
                    SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, i, f, n, ss, unc, distOpt, eb, SOME(isProtected), fn, so))
                  end

                  SOME(DAE.VAR_ATTR_INT(q, min, max, i, f, unc, distOpt, eb, _, fn, so))  => begin
                    SOME(DAE.VAR_ATTR_INT(q, min, max, i, f, unc, distOpt, eb, SOME(isProtected), fn, so))
                  end

                  SOME(DAE.VAR_ATTR_BOOL(q, i, f, eb, _, fn, so))  => begin
                    SOME(DAE.VAR_ATTR_BOOL(q, i, f, eb, SOME(isProtected), fn, so))
                  end

                  SOME(DAE.VAR_ATTR_STRING(q, i, f, eb, _, fn, so))  => begin
                    SOME(DAE.VAR_ATTR_STRING(q, i, f, eb, SOME(isProtected), fn, so))
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, du, eb, _, fn, so))  => begin
                    SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, du, eb, SOME(isProtected), fn, so))
                  end

                  SOME(DAE.VAR_ATTR_CLOCK(fn, _))  => begin
                    SOME(DAE.VAR_ATTR_CLOCK(fn, SOME(isProtected)))
                  end

                  NONE()  => begin
                    setProtectedAttr(SOME(DAE.emptyVarAttrReal), isProtected)
                  end
                end
              end
               #=  lochel: maybe we should let this case just fail
               =#
          outAttr
        end

         #=
          retrieves the protected attribute form VariableAttributes. =#
        function getProtectedAttr(attr::Option{<:DAE.VariableAttributes}) ::Bool
              local isProtected::Bool

              isProtected = begin
                @match attr begin
                  SOME(DAE.VAR_ATTR_REAL(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  SOME(DAE.VAR_ATTR_INT(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  SOME(DAE.VAR_ATTR_BOOL(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  SOME(DAE.VAR_ATTR_STRING(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  SOME(DAE.VAR_ATTR_CLOCK(isProtected = SOME(isProtected)))  => begin
                    isProtected
                  end

                  _  => begin
                      false
                  end
                end
              end
          isProtected
        end

         #= Function: setFixedAttr
        Sets the start attribute:fixed to inputarg =#
        function setFixedAttr(attr::Option{<:DAE.VariableAttributes}, fixed::Option{<:DAE.Exp}) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local q::Option{DAE.Exp}
                  local u::Option{DAE.Exp}
                  local du::Option{DAE.Exp}
                  local n::Option{DAE.Exp}
                  local ini::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local ss::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOpt::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                @match (attr, fixed) begin
                  (SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, ini, _, n, ss, unc, distOpt, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, ini, fixed, n, ss, unc, distOpt, eb, ip, fn, so))
                  end

                  (SOME(DAE.VAR_ATTR_INT(q, min, max, ini, _, unc, distOpt, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_INT(q, min, max, ini, fixed, unc, distOpt, eb, ip, fn, so))
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(q, ini, _, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_BOOL(q, ini, fixed, eb, ip, fn, so))
                  end

                  (SOME(DAE.VAR_ATTR_STRING(q, ini, _, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_STRING(q, ini, fixed, eb, ip, fn, so))
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, _, eb, ip, fn, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, fixed, eb, ip, fn, so))
                  end
                end
              end
          outAttr
        end

         #=
          sets the start attribute. If NONE(), assumes Real attributes. =#
        function setFinalAttr(attr::Option{<:DAE.VariableAttributes}, finalPrefix::Bool) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local q::Option{DAE.Exp}
                  local u::Option{DAE.Exp}
                  local du::Option{DAE.Exp}
                  local i::Option{DAE.Exp}
                  local f::Option{DAE.Exp}
                  local n::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local ss::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local distOpt::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                @match (attr, finalPrefix) begin
                  (SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, i, f, n, ss, unc, distOpt, eb, ip, _, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(q, u, du, min, max, i, f, n, ss, unc, distOpt, eb, ip, SOME(finalPrefix), so))
                  end

                  (SOME(DAE.VAR_ATTR_INT(q, min, max, i, f, unc, distOpt, eb, ip, _, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_INT(q, min, max, i, f, unc, distOpt, eb, ip, SOME(finalPrefix), so))
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(q, i, f, eb, ip, _, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_BOOL(q, i, f, eb, ip, SOME(finalPrefix), so))
                  end

                  (SOME(DAE.VAR_ATTR_CLOCK(ip, _)), _)  => begin
                    SOME(DAE.VAR_ATTR_CLOCK(ip, SOME(finalPrefix)))
                  end

                  (SOME(DAE.VAR_ATTR_STRING(q, i, f, eb, ip, _, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_STRING(q, i, f, eb, ip, SOME(finalPrefix), so))
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, du, eb, ip, _, so)), _)  => begin
                    SOME(DAE.VAR_ATTR_ENUMERATION(q, min, max, u, du, eb, ip, SOME(finalPrefix), so))
                  end

                  (NONE(), _)  => begin
                    SOME(DAE.VAR_ATTR_REAL(NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), SOME(finalPrefix), NONE()))
                  end
                end
              end
               #=  BTH
               =#
          outAttr
        end

         #=
          returns true if have final attr. =#
        function getFinalAttr(attr::Option{<:DAE.VariableAttributes}) ::Bool
              local finalPrefix::Bool

              finalPrefix = begin
                  local b::Bool
                @match attr begin
                  SOME(DAE.VAR_ATTR_REAL(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  SOME(DAE.VAR_ATTR_INT(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  SOME(DAE.VAR_ATTR_BOOL(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  SOME(DAE.VAR_ATTR_STRING(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  SOME(DAE.VAR_ATTR_CLOCK(finalPrefix = SOME(b)))  => begin
                    b
                  end

                  _  => begin
                      false
                  end
                end
              end
          finalPrefix
        end

         #= Function: boolVarVisibility
        Takes a DAE.varprotection and returns true/false (is_protected / not) =#
        function boolVarVisibility(vp::DAE.VarVisibility) ::Bool
              local prot::Bool

              prot = begin
                @match vp begin
                  DAE.PUBLIC(__)  => begin
                    false
                  end

                  DAE.PROTECTED(__)  => begin
                    true
                  end

                  _  => begin
                        print("- DAEUtil.boolVarVisibility failed\\n")
                      fail()
                  end
                end
              end
          prot
        end

         #=
          Returns true if variable attributes defines a start value. =#
        function hasStartAttr(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::Bool
              local hasStart::Bool

              hasStart = begin
                  local r::DAE.Exp
                @match inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(start = SOME(_)))  => begin
                    true
                  end

                  SOME(DAE.VAR_ATTR_INT(start = SOME(_)))  => begin
                    true
                  end

                  SOME(DAE.VAR_ATTR_BOOL(start = SOME(_)))  => begin
                    true
                  end

                  SOME(DAE.VAR_ATTR_STRING(start = SOME(_)))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          hasStart
        end

         #=
          Return the start attribute as a string.
         =#
        function getStartAttrString(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::String
              local outString::String

              outString = begin
                  local s::String
                  local r::DAE.Exp
                @matchcontinue inVariableAttributesOption begin
                  NONE()  => begin
                    ""
                  end

                  SOME(DAE.VAR_ATTR_REAL(start = SOME(r)))  => begin
                      s = ExpressionDump.printExpStr(r)
                    s
                  end

                  SOME(DAE.VAR_ATTR_INT(start = SOME(r)))  => begin
                      s = ExpressionDump.printExpStr(r)
                    s
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= author:  LS

          Retrive the elements for which the function given as second argument
          succeeds.
         =#
        function getMatchingElements(elist::List{<:DAE.Element}, cond::FuncTypeElementTo) ::List{DAE.Element}
              local oelist::List{DAE.Element}

              oelist = ListUtil.filterOnTrue(elist, cond)
          oelist
        end

         #= author:  PA

          Similar to getMatchingElements but traverses down in COMP elements also.
         =#
        function getAllMatchingElements(elist::List{<:DAE.Element}, cond::FuncTypeElementTo) ::List{DAE.Element}
              local outElist::List{DAE.Element}

              outElist = begin
                  local elist1::List{DAE.Element}
                  local elist2::List{DAE.Element}
                  local e::DAE.Element
                @matchcontinue (elist, cond) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.COMP(dAElist = elist1) <| elist2, _)  => begin
                      elist1 = getAllMatchingElements(elist1, cond)
                      elist2 = getAllMatchingElements(elist2, cond)
                    listAppend(elist1, elist2)
                  end

                  (e <| elist2, _)  => begin
                      cond(e)
                      elist2 = getAllMatchingElements(elist2, cond)
                    _cons(e, elist2)
                  end

                  (_ <| elist2, _)  => begin
                    getAllMatchingElements(elist2, cond)
                  end
                end
              end
          outElist
        end

         #= author:  adrpo
          Similar to getMatchingElements but gets two conditions and returns two lists. The functions are copied to both. =#
        function findAllMatchingElements(dae::DAE.DAElist, cond1::CondFunc, cond2::CondFunc) ::Tuple{DAE.DAElist, DAE.DAElist}
              local secondList::DAE.DAElist
              local firstList::DAE.DAElist

              local elements::List{DAE.Element}
              local el1::List{DAE.Element}
              local el2::List{DAE.Element}

              @match DAE.DAE(elementLst = elements) = dae
              (el1, el2) = findAllMatchingElements2(elements, cond1, cond2)
              firstList = DAE.DAE(MetaModelica.Dangerous.listReverseInPlace(el1))
              secondList = DAE.DAE(MetaModelica.Dangerous.listReverseInPlace(el2))
          (firstList, secondList)
        end

        function findAllMatchingElements2(elements::List{<:DAE.Element}, cond1::CondFunc, cond2::CondFunc, accumFirst::List{<:DAE.Element} = nil, accumSecond::List{<:DAE.Element} = nil) ::Tuple{List{DAE.Element}, List{DAE.Element}}
              local secondList::List{DAE.Element} = accumSecond
              local firstList::List{DAE.Element} = accumFirst

              for e in elements
                _ = begin
                  @match e begin
                    DAE.COMP(__)  => begin
                        (firstList, secondList) = findAllMatchingElements2(e.dAElist, cond1, cond2, firstList, secondList)
                      ()
                    end

                    _  => begin
                          if cond1(e)
                            firstList = _cons(e, firstList)
                          end
                          if cond2(e)
                            secondList = _cons(e, secondList)
                          end
                        ()
                    end
                  end
                end
              end
          (firstList, secondList)
        end

         #=
        Author BZ
         =#
        function isAfterIndexInlineFunc(inElem::DAE.Function) ::Bool
              local b::Bool

              b = begin
                @match inElem begin
                  DAE.FUNCTION(inlineType = DAE.AFTER_INDEX_RED_INLINE(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= author: LS
          True if element is parameter.
         =#
        function isParameter(inElement::DAE.Element) ::Bool
              local outB::Bool

              outB = begin
                @match inElement begin
                  DAE.VAR(kind = DAE.PARAM(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #=
          author: BZ 2008-06
          Succeeds if element is constant/parameter.
         =#
        function isParameterOrConstant(inElement::DAE.Element) ::Bool
              local b::Bool

              b = begin
                @match inElement begin
                  DAE.VAR(kind = DAE.CONST(__))  => begin
                    true
                  end

                  DAE.VAR(kind = DAE.PARAM(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isParamOrConstVar(inVar::DAE.Var) ::Bool
              local outIsParamOrConst::Bool

              local var::SCode.Variability

              @match DAE.TYPES_VAR(attributes = DAE.ATTR(variability = var)) = inVar
              outIsParamOrConst = SCodeUtil.isParameterOrConst(var)
          outIsParamOrConst
        end

        function isNotParamOrConstVar(inVar::DAE.Var) ::Bool
              local outIsNotParamOrConst::Bool

              outIsNotParamOrConst = ! isParamOrConstVar(inVar)
          outIsNotParamOrConst
        end

        function isParamConstOrComplexVar(inVar::DAE.Var) ::Bool
              local outIsParamConstComplex::Bool

              outIsParamConstComplex = isParamOrConstVar(inVar) || isComplexVar(inVar)
          outIsParamConstComplex
        end

        function isParamOrConstVarKind(inVarKind::DAE.VarKind) ::Bool
              local outIsParamOrConst::Bool

              outIsParamOrConst = begin
                @match inVarKind begin
                  DAE.PARAM(__)  => begin
                    true
                  end

                  DAE.CONST(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsParamOrConst
        end

         #= Returns true if the element is an inner variable. =#
        function isInnerVar(element::DAE.Element) ::Bool
              local isInner::Bool

              isInner = begin
                @match element begin
                  DAE.VAR(__)  => begin
                    AbsynUtil.isInner(element.innerOuter)
                  end

                  _  => begin
                      false
                  end
                end
              end
          isInner
        end

         #= Returns true if the element is an outer variable. =#
        function isOuterVar(element::DAE.Element) ::Bool
              local isOuter::Bool

              isOuter = begin
                @match element begin
                  DAE.VAR(innerOuter = Absyn.OUTER(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  FIXME? adrpo: do we need this?
               =#
               #=  case DAE.VAR(innerOuter = Absyn.INNER_OUTER()) then true;
               =#
          isOuter
        end

         #= author: LS

          Succeeds if element is component, COMP.
         =#
        function isComp(inElement::DAE.Element)
              _ = begin
                @match inElement begin
                  DAE.COMP(__)  => begin
                    ()
                  end
                end
              end
        end

         #= author: LS

          Retrieve all output variables from an Element list.
         =#
        function getOutputVars(vl::List{<:DAE.Element}) ::List{DAE.Element}
              local vl_1::List{DAE.Element}

              vl_1 = getMatchingElements(vl, isOutputVar)
          vl_1
        end

         #=
          author: PA

          Retrieve all protected variables from an Element list.
         =#
        function getProtectedVars(vl::List{<:DAE.Element}) ::List{DAE.Element}
              local vl_1::List{DAE.Element}

              vl_1 = getMatchingElements(vl, isProtectedVar)
          vl_1
        end

         #= author: LS

          Retrieve all bidirectional variables from an Element list.
         =#
        function getBidirVars(vl::List{<:DAE.Element}) ::List{DAE.Element}
              local vl_1::List{DAE.Element}

              vl_1 = getMatchingElements(vl, isBidirVar)
          vl_1
        end

         #=
          Retrieve all input variables from an Element list.
         =#
        function getInputVars(vl::List{<:DAE.Element}) ::List{DAE.Element}
              local vl_1::List{DAE.Element}

              vl_1 = getMatchingElements(vl, isInput)
          vl_1
        end

         #= Succeeds if the given variable has a flow prefix. =#
        function isFlowVar(inElement::DAE.Element)
              @match DAE.VAR(kind = DAE.VARIABLE(), connectorType = DAE.FLOW()) = inElement
        end

         #= Succeeds if the given variable has a stream prefix. =#
        function isStreamVar(inElement::DAE.Element)
              @match DAE.VAR(kind = DAE.VARIABLE(), connectorType = DAE.STREAM()) = inElement
        end

        function isFlow(inFlow::DAE.ConnectorType) ::Bool
              local outIsFlow::Bool

              outIsFlow = begin
                @match inFlow begin
                  DAE.FLOW(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsFlow
        end

        function isStream(inStream::DAE.ConnectorType) ::Bool
              local outIsStream::Bool

              outIsStream = begin
                @match inStream begin
                  DAE.STREAM(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsStream
        end

         #= Succeeds if Element is an output variable. =#
        function isOutputVar(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(kind = DAE.VARIABLE(__), direction = DAE.OUTPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #= Succeeds if Element is a protected variable. =#
        function assertProtectedVar(inElement::DAE.Element)
              _ = begin
                @match inElement begin
                  DAE.VAR(protection = DAE.PROTECTED(__))  => begin
                    ()
                  end
                end
              end
        end

         #= Succeeds if Element is a protected variable. =#
        function isProtectedVar(inElement::DAE.Element) ::Bool
              local b::Bool

              b = begin
                @match inElement begin
                  DAE.VAR(protection = DAE.PROTECTED(__))  => begin
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
          Succeeds if Element is a public variable.
         =#
        function isPublicVar(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(protection = DAE.PUBLIC(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #=
          Succeeds if Element is a bidirectional variable.
         =#
        function isBidirVar(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(kind = DAE.VARIABLE(__), direction = DAE.BIDIR(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

        function isBidirVarDirection(inVarDirection::DAE.VarDirection) ::Bool
              local outIsBidir::Bool

              outIsBidir = begin
                @match inVarDirection begin
                  DAE.BIDIR(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsBidir
        end

         #=
          Succeeds if Element is an input variable.
         =#
        function isInputVar(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(kind = DAE.VARIABLE(__), direction = DAE.INPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #=
          Succeeds if Element is an input .
         =#
        function isInput(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(direction = DAE.INPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #= Returns true if the element is not a variable, otherwise false. =#
        function isNotVar(e::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match e begin
                  DAE.VAR(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outMatch
        end

         #= Returns true if the element is a variable, otherwise false. =#
        function isVar(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.VAR(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #=
          return true if the element is a function reference variable =#
        function isFunctionRefVar(inElem::DAE.Element) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inElem begin
                  DAE.VAR(ty = DAE.T_FUNCTION(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

        function isComment(elt::DAE.Element) ::Bool
              local b::Bool

              b = begin
                @match elt begin
                  DAE.COMMENT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= author: LS
          Succeeds if Element is an algorithm. =#
        function isAlgorithm(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.ALGORITHM(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #=  outputs true if the stmt is an assert.
        author:Waurich TUD 2014-04 =#
        function isStmtAssert(stmt::DAE.Statement) ::Bool
              local b::Bool

              b = begin
                @match stmt begin
                  DAE.STMT_ASSERT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=  outputs true if the stmt is a return.
        author:Waurich TUD 2014-04 =#
        function isStmtReturn(stmt::DAE.Statement) ::Bool
              local b::Bool

              b = begin
                @match stmt begin
                  DAE.STMT_RETURN(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=  outputs true if the stmt is a reinit.
        author:Waurich TUD 2014-04 =#
        function isStmtReinit(stmt::DAE.Statement) ::Bool
              local b::Bool

              b = begin
                @match stmt begin
                  DAE.STMT_REINIT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=  outputs true if the stmt is a terminate.
        author:Waurich TUD 2014-04 =#
        function isStmtTerminate(stmt::DAE.Statement) ::Bool
              local b::Bool

              b = begin
                @match stmt begin
                  DAE.STMT_TERMINATE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= author: LS
          Succeeds if Element is an complex equation. =#
        function isComplexEquation(inElement::DAE.Element) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match inElement begin
                  DAE.COMPLEX_EQUATION(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

         #= author: PA

          Succeeds if is a function with Inline=false =#
        function isFunctionInlineFalse(inElement::DAE.Function) ::Bool
              local res::Bool

              res = begin
                @match inElement begin
                  DAE.FUNCTION(inlineType = DAE.NO_INLINE(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #=
          Search for an element for which the function passed as second
          argument succeds. If no element is found return NONE.
         =#
        function findElement(inElementLst::List{<:DAE.Element}, inFuncTypeElementTo::FuncTypeElementTo) ::Option{DAE.Element}
              local outElementOption::Option{DAE.Element}

              outElementOption = begin
                  local e::DAE.Element
                  local rest::List{DAE.Element}
                  local f::FuncTypeElementTo
                  local e_1::Option{DAE.Element}
                @match (inElementLst, inFuncTypeElementTo) begin
                  ( nil(), _)  => begin
                    NONE()
                  end

                  (e <| rest, f)  => begin
                      e_1 = begin
                        @matchcontinue () begin
                          ()  => begin
                              f(e)
                            SOME(e)
                          end

                          _  => begin
                                @shouldFail f(e)
                                e_1 = findElement(rest, f)
                              e_1
                          end
                        end
                      end
                    e_1
                  end
                end
              end
          outElementOption
        end

         #=
          This function takes a `DAE.Element\\' list and returns a comma separated
          string of variable bindings.
          E.g. model A Real x=1; Real y=2; end A; => \\\"1,2\\\"
         =#
        function getVariableBindingsStr(elts::List{<:DAE.Element}) ::String
              local str::String

              local varlst::List{DAE.Element}
              local els::List{DAE.Element}

              str = begin
                @match elts begin
                  DAE.COMP(dAElist = els) <|  nil()  => begin
                    getVariableBindingsStr(els)
                  end

                  _  => begin
                        varlst = getVariableList(elts)
                        str = getBindingsStr(varlst)
                      str
                  end
                end
              end
          str
        end

         #=
          Return all variables from an Element list.
         =#
        function getVariableList(inElementLst::List{<:DAE.Element}) ::List{DAE.Element}
              local outElementLst::List{DAE.Element}

               #= /* adrpo: filter out records! */ =#
              outElementLst = list(e for e in inElementLst if begin
                 @match e begin
                   DAE.VAR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)))  => begin
                     false
                   end

                   DAE.VAR(__)  => begin
                     true
                   end

                   _  => begin
                       false
                   end
                 end
               end)
          outElementLst
        end

         #= function: getVariableType
          Return the type of a variable, otherwise fails.
         =#
        function getVariableType(inElement::DAE.Element) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local tp::DAE.Type
                @match inElement begin
                  DAE.VAR(ty = tp)  => begin
                    tp
                  end

                  _  => begin
                      fail()
                  end
                end
              end
          outType
        end

         #=
          Retrive the bindings from a list of Elements and output to a string.
         =#
        function getBindingsStr(inElementLst::List{<:DAE.Element}) ::String
              local outString::String

              outString = begin
                  local expstr::String
                  local s3::String
                  local s4::String
                  local str::String
                  local s1::String
                  local s2::String
                  local v::DAE.Element
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local lst::List{DAE.Element}
                @match inElementLst begin
                  DAE.VAR(binding = SOME(e)) <| lst && _ <| _  => begin
                      expstr = ExpressionDump.printExpStr(e)
                      s3 = stringAppend(expstr, ",")
                      s4 = getBindingsStr(lst)
                      str = stringAppend(s3, s4)
                    str
                  end

                  DAE.VAR(binding = NONE()) <| lst && _ <| _  => begin
                      s1 = "-,"
                      s2 = getBindingsStr(lst)
                      str = stringAppend(s1, s2)
                    str
                  end

                  DAE.VAR(binding = SOME(e)) <|  nil()  => begin
                      str = ExpressionDump.printExpStr(e)
                    str
                  end

                  DAE.VAR(binding = NONE()) <|  nil()  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Author: BZ, 2008-11
        Get variable-bindings from element list.
         =#
        function getBindings(inElementLst::List{<:DAE.Element}) ::Tuple{List{DAE.ComponentRef}, List{DAE.Exp}}
              local oute::List{DAE.Exp}
              local outc::List{DAE.ComponentRef}

              (outc, oute) = begin
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local rest::List{DAE.Element}
                @matchcontinue inElementLst begin
                   nil()  => begin
                    (nil, nil)
                  end

                  DAE.VAR(componentRef = cr, binding = SOME(e)) <| rest  => begin
                      (outc, oute) = getBindings(rest)
                    (_cons(cr, outc), _cons(e, oute))
                  end

                  DAE.VAR(binding = NONE()) <| rest  => begin
                      (outc, oute) = getBindings(rest)
                    (outc, oute)
                  end

                  _  => begin
                        print(" error in getBindings \\n")
                      fail()
                  end
                end
              end
          (outc, oute)
        end

         #= Converts a SCode.ConnectorType to a DAE.ConnectorType, given a class type. =#
        function toConnectorType(inConnectorType::SCode.ConnectorType, inState::ClassInf.State) ::DAE.ConnectorType
              local outConnectorType::DAE.ConnectorType

              outConnectorType = begin
                @match (inConnectorType, inState) begin
                  (SCode.FLOW(__), _)  => begin
                    DAE.FLOW()
                  end

                  (SCode.STREAM(__), _)  => begin
                    DAE.STREAM(NONE())
                  end

                  (_, ClassInf.CONNECTOR(__))  => begin
                    DAE.POTENTIAL()
                  end

                  _  => begin
                      DAE.NON_CONNECTOR()
                  end
                end
              end
          outConnectorType
        end

        function toConnectorTypeNoState(scodeConnectorType::SCode.ConnectorType, flowName::Option{<:DAE.ComponentRef} = NONE()) ::DAE.ConnectorType
              local daeConnectorType::DAE.ConnectorType

              daeConnectorType = begin
                @match scodeConnectorType begin
                  SCode.FLOW(__)  => begin
                    DAE.FLOW()
                  end

                  SCode.STREAM(__)  => begin
                    DAE.STREAM(flowName)
                  end

                  _  => begin
                      DAE.POTENTIAL()
                  end
                end
              end
          daeConnectorType
        end

         #= Converts scode parallelsim to dae parallelism.
          Prints a warning if parallel variables are used
          in a non-function class. =#
        function toDaeParallelism(inCref::DAE.ComponentRef, inParallelism::SCode.Parallelism, inState::ClassInf.State, inInfo::SourceInfo) ::DAE.VarParallelism
              local outParallelism::DAE.VarParallelism

              outParallelism = begin
                  local str1::String
                  local path::Absyn.Path
                @matchcontinue (inCref, inParallelism, inState, inInfo) begin
                  (_, SCode.NON_PARALLEL(__), _, _)  => begin
                    DAE.NON_PARALLEL()
                  end

                  (_, SCode.PARGLOBAL(__), ClassInf.FUNCTION(_, _), _)  => begin
                    DAE.PARGLOBAL()
                  end

                  (_, SCode.PARLOCAL(__), ClassInf.FUNCTION(_, _), _)  => begin
                    DAE.PARLOCAL()
                  end

                  (_, SCode.PARGLOBAL(__), _, _)  => begin
                      path = ClassInf.getStateName(inState)
                      str1 = "\\n" + "- DAEUtil.toDaeParallelism: parglobal component '" + ComponentReference.printComponentRefStr(inCref) + "' in non-function class: " + ClassInf.printStateStr(inState) + " " + AbsynUtil.pathString(path)
                      Error.addSourceMessage(Error.PARMODELICA_WARNING, list(str1), inInfo)
                    DAE.PARGLOBAL()
                  end

                  (_, SCode.PARLOCAL(__), _, _)  => begin
                      path = ClassInf.getStateName(inState)
                      str1 = "\\n" + "- DAEUtil.toDaeParallelism: parlocal component '" + ComponentReference.printComponentRefStr(inCref) + "' in non-function class: " + ClassInf.printStateStr(inState) + " " + AbsynUtil.pathString(path)
                      Error.addSourceMessage(Error.PARMODELICA_WARNING, list(str1), inInfo)
                    DAE.PARLOCAL()
                  end
                end
              end
               #= In functions. No worries.
               =#
               #=  In other classes print warning
               =#
          outParallelism
        end

         #= Translates SCode.Parallelism to DAE.VarParallelism
          without considering if it is a function or not. =#
        function scodePrlToDaePrl(inParallelism::SCode.Parallelism) ::DAE.VarParallelism
              local outVarParallelism::DAE.VarParallelism

              outVarParallelism = begin
                @match inParallelism begin
                  SCode.NON_PARALLEL(__)  => begin
                    DAE.NON_PARALLEL()
                  end

                  SCode.PARGLOBAL(__)  => begin
                    DAE.PARGLOBAL()
                  end

                  SCode.PARLOCAL(__)  => begin
                    DAE.PARLOCAL()
                  end
                end
              end
          outVarParallelism
        end

        function daeParallelismEqual(inParallelism1::DAE.VarParallelism, inParallelism2::DAE.VarParallelism) ::Bool
              local equal::Bool

              equal = begin
                @match (inParallelism1, inParallelism2) begin
                  (DAE.NON_PARALLEL(__), DAE.NON_PARALLEL(__))  => begin
                    true
                  end

                  (DAE.PARGLOBAL(__), DAE.PARGLOBAL(__))  => begin
                    true
                  end

                  (DAE.PARLOCAL(__), DAE.PARLOCAL(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          equal
        end

         #= Retrive the flow variables of an Element list. =#
        function getFlowVariables(inElementLst::List{<:DAE.Element}) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local res::List{DAE.ComponentRef}
                  local res1::List{DAE.ComponentRef}
                  local res1_1::List{DAE.ComponentRef}
                  local res2::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                  local xs::List{DAE.Element}
                  local lst::List{DAE.Element}
                  local id::String
                @matchcontinue inElementLst begin
                   nil()  => begin
                    nil
                  end

                  DAE.VAR(componentRef = cr, connectorType = DAE.FLOW(__)) <| xs  => begin
                      res = getFlowVariables(xs)
                    _cons(cr, res)
                  end

                  DAE.COMP(ident = id, dAElist = lst) <| xs  => begin
                      res1 = getFlowVariables(lst)
                      res1_1 = getFlowVariables2(res1, id)
                      res2 = getFlowVariables(xs)
                      res = listAppend(res1_1, res2)
                    res
                  end

                  _ <| xs  => begin
                      res = getFlowVariables(xs)
                    res
                  end
                end
              end
          outExpComponentRefLst
        end

         #=
          Helper function to get_flow_variables.
         =#
        function getFlowVariables2(inExpComponentRefLst::List{<:DAE.ComponentRef}, inIdent::String) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local id::String
                  local res::List{DAE.ComponentRef}
                  local xs::List{DAE.ComponentRef}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                @match (inExpComponentRefLst, inIdent) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (cr <| xs, id)  => begin
                      res = getFlowVariables2(xs, id)
                      cr_1 = ComponentReference.makeCrefQual(id, DAE.T_UNKNOWN_DEFAULT, nil, cr)
                    _cons(cr_1, res)
                  end
                end
              end
          outExpComponentRefLst
        end

         #= Retrive the stream variables of an Element list. =#
        function getStreamVariables(inElementLst::List{<:DAE.Element}) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local res::List{DAE.ComponentRef}
                  local res1::List{DAE.ComponentRef}
                  local res1_1::List{DAE.ComponentRef}
                  local res2::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                  local xs::List{DAE.Element}
                  local lst::List{DAE.Element}
                  local id::String
                @matchcontinue inElementLst begin
                   nil()  => begin
                    nil
                  end

                  DAE.VAR(componentRef = cr, connectorType = DAE.STREAM(__)) <| xs  => begin
                      res = getStreamVariables(xs)
                    _cons(cr, res)
                  end

                  DAE.COMP(ident = id, dAElist = lst) <| xs  => begin
                      res1 = getStreamVariables(lst)
                      res1_1 = getStreamVariables2(res1, id)
                      res2 = getStreamVariables(xs)
                      res = listAppend(res1_1, res2)
                    res
                  end

                  _ <| xs  => begin
                      res = getStreamVariables(xs)
                    res
                  end
                end
              end
          outExpComponentRefLst
        end

         #=
          Helper function to get_flow_variables.
         =#
        function getStreamVariables2(inExpComponentRefLst::List{<:DAE.ComponentRef}, inIdent::String) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local id::String
                  local res::List{DAE.ComponentRef}
                  local xs::List{DAE.ComponentRef}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                @match (inExpComponentRefLst, inIdent) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (cr <| xs, id)  => begin
                      res = getStreamVariables2(xs, id)
                      cr_1 = ComponentReference.makeCrefQual(id, DAE.T_UNKNOWN_DEFAULT, nil, cr)
                    _cons(cr_1, res)
                  end
                end
              end
          outExpComponentRefLst
        end

         #= Transforms a list of elements into a record value.
          TODO: This does not work for records inside records.
          For a general approach we need to build an environment from the DAE and then
          instead investigate the variables and lookup their values from the created environment. =#
        function daeToRecordValue(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path, inElementLst::List{<:DAE.Element}, inBoolean::Bool) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local cname::Absyn.Path
                  local value::Values.Value
                  local res::Values.Value
                  local vals::List{Values.Value}
                  local names::List{String}
                  local cr_str::String
                  local str::String
                  local cr::DAE.ComponentRef
                  local rhs::DAE.Exp
                  local rest::List{DAE.Element}
                  local impl::Bool
                  local ix::ModelicaInteger
                  local el::DAE.Element
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local source::DAE.ElementSource
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inPath, inElementLst, inBoolean) begin
                  (cache, _, cname,  nil(), _)  => begin
                    (cache, Values.RECORD(cname, nil, nil, -1))
                  end

                  (cache, env, cname, DAE.VAR(componentRef = cr, binding = SOME(rhs), source = source) <| rest, impl)  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      (cache, value) = Ceval.ceval(cache, env, rhs, impl, Absyn.MSG(info), 0)
                      @match (cache, Values.RECORD(cname, vals, names, ix)) = daeToRecordValue(cache, env, cname, rest, impl)
                      cr_str = ComponentReference.printComponentRefStr(cr)
                    (cache, Values.RECORD(cname, _cons(value, vals), _cons(cr_str, names), ix))
                  end

                  (_, _, _, el <| _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      str = DAEDump.dumpDebugDAE(DAE.DAE(list(el)))
                      Debug.traceln("- DAEUtil.daeToRecordValue failed on: " + str)
                    fail()
                  end
                end
              end
               #= /* impl */ =#
               #=  fprintln(Flags.FAILTRACE, \"- DAEUtil.daeToRecordValue typeOfRHS: \" + ExpressionDump.typeOfString(rhs));
               =#
          (outCache, outValue)
        end

         #= function toModelicaForm.

          Transforms all variables from a.b.c to a_b_c, etc
         =#
        function toModelicaForm(inDAElist::DAE.DAElist) ::DAE.DAElist
              local outDAElist::DAE.DAElist

              outDAElist = begin
                  local elts_1::List{DAE.Element}
                  local elts::List{DAE.Element}
                @match inDAElist begin
                  DAE.DAE(elts)  => begin
                      elts_1 = toModelicaFormElts(elts)
                    DAE.DAE(elts_1)
                  end
                end
              end
          outDAElist
        end

         #= Helper function to toModelicaForm. =#
        function toModelicaFormElts(inElementLst::List{<:DAE.Element}) ::List{DAE.Element}
              local outElementLst::List{DAE.Element}

              outElementLst = begin
                  local str::String
                  local str_1::String
                  local id::String
                  local elts_1::List{DAE.Element}
                  local elts::List{DAE.Element}
                  local welts_1::List{DAE.Element}
                  local welts::List{DAE.Element}
                  local telts_1::List{DAE.Element}
                  local eelts_1::List{DAE.Element}
                  local telts::List{DAE.Element}
                  local eelts::List{DAE.Element}
                  local elts2::List{DAE.Element}
                  local d_1::Option{DAE.Exp}
                  local d::Option{DAE.Exp}
                  local f::Option{DAE.Exp}
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local cref_::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local ty::DAE.Type
                  local a::DAE.VarKind
                  local b::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local t::DAE.Type
                  local instDim::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local elt_1::DAE.Element
                  local elt::DAE.Element
                  local dae_1::DAE.DAElist
                  local dae::DAE.DAElist
                  local prot::DAE.VarVisibility
                  local h::List{Absyn.Path}
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local e_1::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
                  local e3::DAE.Exp
                  local e_3::DAE.Exp
                  local p::Absyn.Path
                  local io::Absyn.InnerOuter
                  local conds::List{DAE.Exp}
                  local conds_1::List{DAE.Exp}
                  local trueBranches::List{List{DAE.Element}}
                  local trueBranches_1::List{List{DAE.Element}}
                  local partialPrefix::Bool
                  local derFuncs::List{DAE.FunctionDefinition}
                  local source::DAE.ElementSource #= the element origin =#
                  local alg::DAE.Algorithm
                @match inElementLst begin
                   nil()  => begin
                    nil
                  end

                  DAE.VAR(componentRef = cr, kind = a, direction = b, parallelism = prl, protection = prot, ty = t, binding = d, dims = instDim, connectorType = ct, source = source, variableAttributesOption = dae_var_attr, comment = comment, innerOuter = io) <| elts  => begin
                      str = ComponentReference.printComponentRefStr(cr)
                      str_1 = Util.stringReplaceChar(str, ".", "_")
                      elts_1 = toModelicaFormElts(elts)
                      d_1 = toModelicaFormExpOpt(d)
                      ty = ComponentReference.crefLastType(cr)
                      cref_ = ComponentReference.makeCrefIdent(str_1, ty, nil)
                    _cons(DAE.VAR(cref_, a, b, prl, prot, t, d_1, instDim, ct, source, dae_var_attr, comment, io), elts_1)
                  end

                  DAE.DEFINE(componentRef = cr, exp = e, source = source) <| elts  => begin
                      e_1 = toModelicaFormExp(e)
                      cr_1 = toModelicaFormCref(cr)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.DEFINE(cr_1, e_1, source), elts_1)
                  end

                  DAE.INITIALDEFINE(componentRef = cr, exp = e, source = source) <| elts  => begin
                      e_1 = toModelicaFormExp(e)
                      cr_1 = toModelicaFormCref(cr)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.INITIALDEFINE(cr_1, e_1, source), elts_1)
                  end

                  DAE.EQUATION(exp = e1, scalar = e2, source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.EQUATION(e1_1, e2_1, source), elts_1)
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2, source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.COMPLEX_EQUATION(e1_1, e2_1, source), elts_1)
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2, source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.INITIAL_COMPLEX_EQUATION(e1_1, e2_1, source), elts_1)
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2, source = source) <| elts  => begin
                      @match DAE.CREF(cr1, _) = toModelicaFormExp(Expression.crefExp(cr1))
                      @match DAE.CREF(cr2, _) = toModelicaFormExp(Expression.crefExp(cr2))
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.EQUEQUATION(cr1, cr2, source), elts_1)
                  end

                  DAE.WHEN_EQUATION(condition = e1, equations = welts, elsewhen_ = SOME(elt), source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      welts_1 = toModelicaFormElts(welts)
                      @match list(elt_1) = toModelicaFormElts(list(elt))
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.WHEN_EQUATION(e1_1, welts_1, SOME(elt_1), source), elts_1)
                  end

                  DAE.WHEN_EQUATION(condition = e1, equations = welts, elsewhen_ = NONE(), source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      welts_1 = toModelicaFormElts(welts)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.WHEN_EQUATION(e1_1, welts_1, NONE(), source), elts_1)
                  end

                  DAE.IF_EQUATION(condition1 = conds, equations2 = trueBranches, equations3 = eelts, source = source) <| elts  => begin
                      conds_1 = ListUtil.map(conds, toModelicaFormExp)
                      trueBranches_1 = ListUtil.map(trueBranches, toModelicaFormElts)
                      eelts_1 = toModelicaFormElts(eelts)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.IF_EQUATION(conds_1, trueBranches_1, eelts_1, source), elts_1)
                  end

                  DAE.INITIAL_IF_EQUATION(condition1 = conds, equations2 = trueBranches, equations3 = eelts, source = source) <| elts  => begin
                      conds_1 = ListUtil.map(conds, toModelicaFormExp)
                      trueBranches_1 = ListUtil.map(trueBranches, toModelicaFormElts)
                      eelts_1 = toModelicaFormElts(eelts)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.INITIAL_IF_EQUATION(conds_1, trueBranches_1, eelts_1, source), elts_1)
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2, source = source) <| elts  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.INITIALEQUATION(e1_1, e2_1, source), elts_1)
                  end

                  DAE.ALGORITHM(algorithm_ = alg, source = source) <| elts  => begin
                      print("to_modelica_form_elts(ALGORITHM) not impl. yet\\n")
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.ALGORITHM(alg, source), elts_1)
                  end

                  DAE.INITIALALGORITHM(algorithm_ = alg, source = source) <| elts  => begin
                      print("to_modelica_form_elts(INITIALALGORITHM) not impl. yet\\n")
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.INITIALALGORITHM(alg, source), elts_1)
                  end

                  DAE.COMP(ident = id, dAElist = elts2, source = source, comment = comment) <| elts  => begin
                      elts2 = toModelicaFormElts(elts2)
                      elts_1 = toModelicaFormElts(elts)
                    _cons(DAE.COMP(id, elts2, source, comment), elts_1)
                  end

                  DAE.ASSERT(condition = e1, message = e2, level = e3, source = source) <| elts  => begin
                      elts_1 = toModelicaFormElts(elts)
                      e_1 = toModelicaFormExp(e1)
                      e_2 = toModelicaFormExp(e2)
                      e_3 = toModelicaFormExp(e3)
                    _cons(DAE.ASSERT(e_1, e_2, e_3, source), elts_1)
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2, level = e3, source = source) <| elts  => begin
                      elts_1 = toModelicaFormElts(elts)
                      e_1 = toModelicaFormExp(e1)
                      e_2 = toModelicaFormExp(e2)
                      e_3 = toModelicaFormExp(e3)
                    _cons(DAE.INITIAL_ASSERT(e_1, e_2, e_3, source), elts_1)
                  end

                  DAE.TERMINATE(message = e1, source = source) <| elts  => begin
                      elts_1 = toModelicaFormElts(elts)
                      e_1 = toModelicaFormExp(e1)
                    _cons(DAE.TERMINATE(e_1, source), elts_1)
                  end

                  DAE.INITIAL_TERMINATE(message = e1, source = source) <| elts  => begin
                      elts_1 = toModelicaFormElts(elts)
                      e_1 = toModelicaFormExp(e1)
                    _cons(DAE.INITIAL_TERMINATE(e_1, source), elts_1)
                  end
                end
              end
          outElementLst
        end

         #=
        Author BZ
         Function for updating the Component Ref of the Var =#
        function replaceCrefInVar(newCr::DAE.ComponentRef, inelem::DAE.Element) ::DAE.Element
              local outelem::DAE.Element

              outelem = begin
                  local a1::DAE.ComponentRef
                  local a2::DAE.VarKind
                  local a3::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local a4::DAE.VarVisibility
                  local a5::DAE.Type
                  local a7::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local a6::Option{DAE.Exp}
                  local source::DAE.ElementSource
                  local a11::Option{DAE.VariableAttributes}
                  local a12::Option{SCode.Comment}
                  local a13::Absyn.InnerOuter
                @match (newCr, inelem) begin
                  (_, DAE.VAR(_, a2, a3, prl, a4, a5, a6, a7, ct, source, a11, a12, a13))  => begin
                    DAE.VAR(newCr, a2, a3, prl, a4, a5, a6, a7, ct, source, a11, a12, a13)
                  end
                end
              end
          outelem
        end

         #=
        Author BZ
         Function for updating the Type of the Var =#
        function replaceTypeInVar(newType::DAE.Type, inelem::DAE.Element) ::DAE.Element
              local outelem::DAE.Element

              outelem = begin
                  local a1::DAE.ComponentRef
                  local a2::DAE.VarKind
                  local a3::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local a4::DAE.VarVisibility
                  local a5::DAE.Type
                  local a7::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local a6::Option{DAE.Exp}
                  local source::DAE.ElementSource
                  local a11::Option{DAE.VariableAttributes}
                  local a12::Option{SCode.Comment}
                  local a13::Absyn.InnerOuter
                @match (newType, inelem) begin
                  (_, DAE.VAR(a1, a2, a3, prl, a4, _, a6, a7, ct, source, a11, a12, a13))  => begin
                    DAE.VAR(a1, a2, a3, prl, a4, newType, a6, a7, ct, source, a11, a12, a13)
                  end
                end
              end
          outelem
        end

         #=
        Author BZ
         Function for updating the Component Ref and the Type of the Var =#
        function replaceCrefandTypeInVar(newCr::DAE.ComponentRef, newType::DAE.Type, inelem::DAE.Element) ::DAE.Element
              local outelem::DAE.Element

              outelem = begin
                  local a1::DAE.ComponentRef
                  local a2::DAE.VarKind
                  local a3::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local a4::DAE.VarVisibility
                  local a5::DAE.Type
                  local a7::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local a6::Option{DAE.Exp}
                  local source::DAE.ElementSource
                  local a11::Option{DAE.VariableAttributes}
                  local a12::Option{SCode.Comment}
                  local a13::Absyn.InnerOuter
                @match (newCr, newType, inelem) begin
                  (_, _, DAE.VAR(_, a2, a3, prl, a4, _, a6, a7, ct, source, a11, a12, a13))  => begin
                      outelem = DAE.VAR(newCr, a2, a3, prl, a4, newType, a6, a7, ct, source, a11, a12, a13)
                    outelem
                  end
                end
              end
          outelem
        end

         #=
        Author BZ
         Function for updating the Component Ref of the Var =#
        function replaceBindungInVar(newBindung::DAE.Exp, inelem::DAE.Element) ::DAE.Element
              local outelem::DAE.Element

              outelem = begin
                  local a1::DAE.ComponentRef
                  local a2::DAE.VarKind
                  local a3::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local a4::DAE.VarVisibility
                  local a5::DAE.Type
                  local a7::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local a6::Option{DAE.Exp}
                  local source::DAE.ElementSource
                  local a11::Option{DAE.VariableAttributes}
                  local a12::Option{SCode.Comment}
                  local a13::Absyn.InnerOuter
                @match (newBindung, inelem) begin
                  (_, DAE.VAR(a1, a2, a3, prl, a4, a5, _, a7, ct, source, a11, a12, a13))  => begin
                    DAE.VAR(a1, a2, a3, prl, a4, a5, SOME(newBindung), a7, ct, source, a11, a12, a13)
                  end
                end
              end
          outelem
        end

         #= Helper function to toMdelicaFormElts. =#
        function toModelicaFormExpOpt(inExpExpOption::Option{<:DAE.Exp}) ::Option{DAE.Exp}
              local outExpExpOption::Option{DAE.Exp}

              outExpExpOption = begin
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                @match inExpExpOption begin
                  SOME(e)  => begin
                      e_1 = toModelicaFormExp(e)
                    SOME(e_1)
                  end

                  NONE()  => begin
                    NONE()
                  end
                end
              end
          outExpExpOption
        end

         #= Helper function to toModelicaFormElts. =#
        function toModelicaFormCref(cr::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              local str::String
              local str_1::String
              local ty::DAE.Type

              str = ComponentReference.printComponentRefStr(cr)
              ty = ComponentReference.crefLastType(cr)
              str_1 = Util.stringReplaceChar(str, ".", "_")
              outComponentRef = ComponentReference.makeCrefIdent(str_1, ty, nil)
          outComponentRef
        end

         #= Helper function to toModelicaFormElts. =#
        function toModelicaFormExp(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local t::DAE.Type
                  local tp::DAE.Type
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local op::DAE.Operator
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local f::Absyn.Path
                  local b::Bool
                  local bt::Bool
                  local i::ModelicaInteger
                  local eopt_1::Option{DAE.Exp}
                  local eopt::Option{DAE.Exp}
                  local attr::DAE.CallAttributes
                  local optionExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                @matchcontinue inExp begin
                  DAE.CREF(componentRef = cr, ty = t)  => begin
                      cr_1 = toModelicaFormCref(cr)
                    Expression.makeCrefExp(cr_1, t)
                  end

                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                    DAE.BINARY(e1_1, op, e2_1)
                  end

                  DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                    DAE.LBINARY(e1_1, op, e2_1)
                  end

                  DAE.UNARY(operator = op, exp = e)  => begin
                      e_1 = toModelicaFormExp(e)
                    DAE.UNARY(op, e_1)
                  end

                  DAE.LUNARY(operator = op, exp = e)  => begin
                      e_1 = toModelicaFormExp(e)
                    DAE.LUNARY(op, e_1)
                  end

                  DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = i, optionExpisASUB = optionExpisASUB)  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                    DAE.RELATION(e1_1, op, e2_1, i, optionExpisASUB)
                  end

                  DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3)  => begin
                      e1_1 = toModelicaFormExp(e1)
                      e2_1 = toModelicaFormExp(e2)
                      e3_1 = toModelicaFormExp(e3)
                    DAE.IFEXP(e1_1, e2_1, e3_1)
                  end

                  DAE.CALL(path = f, expLst = expl, attr = attr)  => begin
                      expl_1 = ListUtil.map(expl, toModelicaFormExp)
                    DAE.CALL(f, expl_1, attr)
                  end

                  DAE.ARRAY(ty = t, scalar = b, array = expl)  => begin
                      expl_1 = ListUtil.map(expl, toModelicaFormExp)
                    DAE.ARRAY(t, b, expl_1)
                  end

                  DAE.TUPLE(PR = expl)  => begin
                      expl_1 = ListUtil.map(expl, toModelicaFormExp)
                    DAE.TUPLE(expl_1)
                  end

                  DAE.CAST(ty = t, exp = e)  => begin
                      e_1 = toModelicaFormExp(e)
                    DAE.CAST(t, e_1)
                  end

                  DAE.ASUB(exp = e, sub = expl)  => begin
                      e_1 = toModelicaFormExp(e)
                    Expression.makeASUB(e_1, expl)
                  end

                  DAE.SIZE(exp = e, sz = eopt)  => begin
                      e_1 = toModelicaFormExp(e)
                      eopt_1 = toModelicaFormExpOpt(eopt)
                    DAE.SIZE(e_1, eopt_1)
                  end

                  e  => begin
                    e
                  end
                end
              end
          outExp
        end

         #= Return the FUNCTION with the given name. Fails if not found. =#
        function getNamedFunction(path::Absyn.Path, functions::DAE.FunctionTree) ::DAE.Function
              local outElement::DAE.Function

              outElement = begin
                  local msg::String
                @matchcontinue (path, functions) begin
                  (_, _)  => begin
                    Util.getOption(DAE.AvlTreePathFunction.get(functions, path))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        msg = stringDelimitList(ListUtil.mapMap(getFunctionList(functions), functionName, AbsynUtil.pathStringDefault), "\\n  ")
                        msg = "DAEUtil.getNamedFunction failed: " + AbsynUtil.pathString(path) + "\\nThe following functions were part of the cache:\\n  " + msg
                        Debug.traceln(msg)
                      fail()
                  end
                end
              end
               #=  Error.addMessage(Error.INTERNAL_ERROR,{msg});
               =#
          outElement
        end

         #= Return the FUNCTION with the given name. Fails if not found. =#
        function getNamedFunctionWithError(path::Absyn.Path, functions::DAE.FunctionTree, info::SourceInfo) ::DAE.Function
              local outElement::DAE.Function

              outElement = begin
                  local msg::String
                @matchcontinue (path, functions, info) begin
                  (_, _, _)  => begin
                    Util.getOption(DAE.AvlTreePathFunction.get(functions, path))
                  end

                  _  => begin
                        msg = stringDelimitList(ListUtil.mapMap(getFunctionList(functions), functionName, AbsynUtil.pathStringDefault), "\\n  ")
                        msg = "DAEUtil.getNamedFunction failed: " + AbsynUtil.pathString(path) + "\\nThe following functions were part of the cache:\\n  " + msg
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list(msg), info)
                      fail()
                  end
                end
              end
          outElement
        end

         #= Is slow; PartFn.mo should be rewritten using the FunctionTree =#
        function getNamedFunctionFromList(ipath::Absyn.Path, ifns::List{<:DAE.Function}) ::DAE.Function
              local fn::DAE.Function

              fn = begin
                  local path::Absyn.Path
                  local fns::List{DAE.Function}
                @matchcontinue (ipath, ifns) begin
                  (path, fn <| _)  => begin
                      @match true = AbsynUtil.pathEqual(functionName(fn), path)
                    fn
                  end

                  (path, _ <| fns)  => begin
                    getNamedFunctionFromList(path, fns)
                  end

                  (path,  nil())  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- DAEUtil.getNamedFunctionFromList failed " + AbsynUtil.pathString(path))
                    fail()
                  end
                end
              end
          fn
        end

        function getFunctionVisibility(fn::DAE.Function) ::SCode.Visibility
              local visibility::SCode.Visibility

              visibility = begin
                @match fn begin
                  DAE.FUNCTION(visibility = visibility)  => begin
                    visibility
                  end

                  _  => begin
                      SCode.PUBLIC()
                  end
                end
              end
          visibility
        end

        function getFunctionsElements(elements::List{<:DAE.Function}) ::List{DAE.Element}
              local els::List{DAE.Element}

              local elsList::List{List{DAE.Element}}

              elsList = ListUtil.map(elements, getFunctionElements)
              els = ListUtil.flatten(elsList)
          els
        end

        function getFunctionElements(fn::DAE.Function) ::List{DAE.Element}
              local els::List{DAE.Element}

              els = begin
                  local elements::List{DAE.Element}
                @match fn begin
                  DAE.FUNCTION(functions = DAE.FUNCTION_DEF(body = elements) <| _)  => begin
                    elements
                  end

                  DAE.FUNCTION(functions = DAE.FUNCTION_EXT(body = elements) <| _)  => begin
                    elements
                  end

                  DAE.RECORD_CONSTRUCTOR(__)  => begin
                    nil
                  end
                end
              end
          els
        end

        function getFunctionType(fn::DAE.Function) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local elements::List{DAE.Element}
                @match fn begin
                  DAE.FUNCTION(type_ = outType)  => begin
                    outType
                  end

                  DAE.FUNCTION(type_ = outType)  => begin
                    outType
                  end

                  DAE.RECORD_CONSTRUCTOR(type_ = outType)  => begin
                    outType
                  end
                end
              end
          outType
        end

        function getFunctionImpureAttribute(fn::DAE.Function) ::Bool
              local outImpure::Bool

              outImpure = begin
                @match fn begin
                  DAE.FUNCTION(isImpure = outImpure)  => begin
                    outImpure
                  end
                end
              end
          outImpure
        end

        function getFunctionInlineType(fn::DAE.Function) ::DAE.InlineType
              local outInlineType::DAE.InlineType

              outInlineType = begin
                @match fn begin
                  DAE.FUNCTION(inlineType = outInlineType)  => begin
                    outInlineType
                  end
                end
              end
          outInlineType
        end

        function getFunctionInputVars(fn::DAE.Function) ::List{DAE.Element}
              local outEls::List{DAE.Element}

              local elements::List{DAE.Element}

              elements = getFunctionElements(fn)
              outEls = ListUtil.filterOnTrue(elements, isInputVar)
          outEls
        end

        function getFunctionOutputVars(fn::DAE.Function) ::List{DAE.Element}
              local outEls::List{DAE.Element}

              local elements::List{DAE.Element}

              elements = getFunctionElements(fn)
              outEls = ListUtil.filterOnTrue(elements, isOutputVar)
          outEls
        end

        function getFunctionProtectedVars(fn::DAE.Function) ::List{DAE.Element}
              local outEls::List{DAE.Element}

              local elements::List{DAE.Element}

              elements = getFunctionElements(fn)
              outEls = ListUtil.filterOnTrue(elements, isProtectedVar)
          outEls
        end

        function getFunctionAlgorithms(fn::DAE.Function) ::List{DAE.Element}
              local outEls::List{DAE.Element}

              local elements::List{DAE.Element}

              elements = getFunctionElements(fn)
              outEls = ListUtil.filterOnTrue(elements, isAlgorithm)
          outEls
        end

        function getFunctionAlgorithmStmts(fn::DAE.Function) ::List{DAE.Statement}
              local bodyStmts::List{DAE.Statement}

              local elements::List{DAE.Element}

              elements = getFunctionElements(fn)
              bodyStmts = ListUtil.mapFlat(ListUtil.filterOnTrue(elements, isAlgorithm), getStatement)
          bodyStmts
        end

        function getStatement(inElement::DAE.Element) ::List{DAE.Statement}
              local outStatements::List{DAE.Statement}

              outStatements = begin
                  local stmts::List{DAE.Statement}
                @matchcontinue inElement begin
                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts))  => begin
                    stmts
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Differentiatte.getStatement failed\\n")
                      fail()
                  end
                end
              end
          outStatements
        end

         #= gets the size of a DAE.TUPLE =#
        function getTupleSize(inExp::DAE.Exp) ::ModelicaInteger
              local size::ModelicaInteger

              size = begin
                  local exps::List{DAE.Exp}
                @match inExp begin
                  DAE.TUPLE(exps)  => begin
                      size = listLength(exps)
                    size
                  end

                  _  => begin
                      0
                  end
                end
              end
          size
        end

         #= gets the list<DAE.Exp> of a DAE.TUPLE or the list of the exp if its not a tuple =#
        function getTupleExps(inExp::DAE.Exp) ::List{DAE.Exp}
              local exps::List{DAE.Exp}

              exps = begin
                @match inExp begin
                  DAE.TUPLE(exps)  => begin
                    exps
                  end

                  _  => begin
                      list(inExp)
                  end
                end
              end
          exps
        end

         #=
          Makes an expression from a ComponentRef.
         =#
        function crefToExp(inComponentRef::DAE.ComponentRef) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = Expression.makeCrefExp(inComponentRef, DAE.T_UNKNOWN_DEFAULT)
          outExp
        end

         #=
          Perform some checks for DAE equations:
          1. Assert equations should be used only inside when equations;
          2. Bolean when equation should:
            2.1 not contain nested clocked or boolean when equations;
            2.2 not have clocked else-when parts;
            2.3 have component references on left side of its equations, and
                for each branch the set of left hand references should be same;
          3. Clocked when equation should not:
            3.1 contain nested clocked when equations;
            3.2 contain else-when parts;
            3.3 contain reinit equation(?);
          4. Initial when equation should not contain assert equation.
         =#
        function verifyEquationsDAE(dae::DAE.DAElist)
              local cond::DAE.Exp
              local dae_elts::List{DAE.Element}
              local eqs::List{DAE.Element}
              local ew::Option{DAE.Element}
              local source::DAE.ElementSource
              local el::DAE.Element
              local info::SourceInfo

              @match DAE.DAE(dae_elts) = dae
              for el in dae_elts
                () = begin
                  @match el begin
                    DAE.WHEN_EQUATION(cond, eqs, ew, source)  => begin
                        verifyWhenEquation(cond, eqs, ew, source)
                      ()
                    end

                    DAE.REINIT(__)  => begin
                        info = ElementSource.getElementSourceFileInfo(ElementSource.getElementSource(el))
                        Error.addSourceMessageAndFail(Error.REINIT_NOT_IN_WHEN, nil, info)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
        end

        function verifyWhenEquation(cond::DAE.Exp, eqs::List{<:DAE.Element}, ew::Option{<:DAE.Element}, source::DAE.ElementSource)
              if Types.isClockOrSubTypeClock(Expression.typeof(cond))
                verifyClockWhenEquation(cond, eqs, ew, source)
              else
                verifyBoolWhenEquation(cond, eqs, ew, source)
              end
        end

        function verifyClockWhenEquation(cond::DAE.Exp, eqs::List{<:DAE.Element}, ew::Option{<:DAE.Element}, source::DAE.ElementSource)
              local info::SourceInfo

              if ! isNone(ew)
                info = ElementSource.getElementSourceFileInfo(source)
                Error.addSourceMessageAndFail(Error.ELSE_WHEN_CLOCK, nil, info)
              end
              verifyClockWhenEquation1(eqs)
        end

        function verifyClockWhenEquation1(inEqs::List{<:DAE.Element})
              local el::DAE.Element

              for el in inEqs
                () = begin
                    local cond::DAE.Exp
                    local eqs::List{DAE.Element}
                    local ew::Option{DAE.Element}
                    local source::DAE.ElementSource
                    local info::SourceInfo
                  @match el begin
                    DAE.REINIT(__)  => begin
                        info = ElementSource.getElementSourceFileInfo(ElementSource.getElementSource(el))
                        Error.addSourceMessageAndFail(Error.REINIT_NOT_IN_WHEN, nil, info)
                      ()
                    end

                    DAE.WHEN_EQUATION(cond, eqs, ew, source)  => begin
                        if Types.isClockOrSubTypeClock(Expression.typeof(cond))
                          info = ElementSource.getElementSourceFileInfo(ElementSource.getElementSource(el))
                          Error.addSourceMessageAndFail(Error.NESTED_CLOCKED_WHEN, nil, info)
                        end
                        verifyBoolWhenEquation(cond, eqs, ew, source)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
        end

        function verifyBoolWhenEquation(inCond::DAE.Exp, inEqs::List{<:DAE.Element}, inElseWhen::Option{<:DAE.Element}, source::DAE.ElementSource)
              local crefs1::List{DAE.ComponentRef}
              local crefs2::List{DAE.ComponentRef}
              local whenBranches::List{Tuple{DAE.Exp, List{DAE.Element}}}
              local whenBranch::Tuple{DAE.Exp, List{DAE.Element}}
              local cond::DAE.Exp
              local eqs::List{DAE.Element}
              local info::SourceInfo

              crefs1 = verifyBoolWhenEquationBranch(inCond, inEqs)
              whenBranches = collectWhenEquationBranches(inElseWhen)
              for whenBranch in whenBranches
                (cond, eqs) = whenBranch
                if Types.isClockOrSubTypeClock(Expression.typeof(cond))
                  info = ElementSource.getElementSourceFileInfo(source)
                  Error.addSourceMessageAndFail(Error.CLOCKED_WHEN_BRANCH, nil, info)
                end
                crefs2 = verifyBoolWhenEquationBranch(cond, eqs)
                crefs2 = ListUtil.unionOnTrue(crefs1, crefs2, ComponentReference.crefEqual)
                if listLength(crefs2) != listLength(crefs1)
                  info = ElementSource.getElementSourceFileInfo(source)
                  Error.addSourceMessageAndFail(Error.DIFFERENT_VARIABLES_SOLVED_IN_ELSEWHEN, nil, info)
                end
              end
        end

        function collectWhenEquationBranches(inElseWhen::Option{<:DAE.Element}, inWhenBranches::List{<:Tuple{<:DAE.Exp, List{<:DAE.Element}}} = nil) ::List{Tuple{DAE.Exp, List{DAE.Element}}}
              local outWhenBranches::List{Tuple{DAE.Exp, List{DAE.Element}}}

              outWhenBranches = begin
                  local cond::DAE.Exp
                  local eqs::List{DAE.Element}
                  local ew::Option{DAE.Element}
                  local info::SourceInfo
                  local msg::String
                  local el::DAE.Element
                @match inElseWhen begin
                  NONE()  => begin
                    inWhenBranches
                  end

                  SOME(DAE.WHEN_EQUATION(cond, eqs, ew, _))  => begin
                    collectWhenEquationBranches(ew, _cons((cond, eqs), inWhenBranches))
                  end

                  SOME(el)  => begin
                      msg = "- DAEUtil.collectWhenEquationBranches failed on: " + DAEDump.dumpElementsStr(list(el))
                      info = ElementSource.getElementSourceFileInfo(ElementSource.getElementSource(el))
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(msg), info)
                    fail()
                  end
                end
              end
          outWhenBranches
        end

        function verifyBoolWhenEquationBranch(inCond::DAE.Exp, inEqs::List{<:DAE.Element}) ::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef}

              local initCond::Bool = Expression.containsInitialCall(inCond)

              crefs = verifyBoolWhenEquation1(inEqs, initCond)
          crefs
        end

        function verifyBoolWhenEquation1(inElems::List{<:DAE.Element}, initCond::Bool, inCrefs::List{<:DAE.ComponentRef} = nil) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              outCrefs = begin
                  local rest::List{DAE.Element}
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local exps::List{DAE.Exp}
                  local crefs::List{DAE.ComponentRef}
                  local crefsLists::List{List{DAE.ComponentRef}}
                  local source::DAE.ElementSource
                  local info::SourceInfo
                  local el::DAE.Element
                  local falseEqs::List{DAE.Element}
                  local trueEqs::List{List{DAE.Element}}
                  local b::Bool
                  local msg::String
                @match inElems begin
                   nil()  => begin
                    inCrefs
                  end

                  DAE.VAR(__) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, inCrefs)
                  end

                  DAE.DEFINE(componentRef = cr) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, _cons(cr, inCrefs))
                  end

                  DAE.EQUATION(exp = e, source = source) <| rest  => begin
                      crefs = collectWhenCrefs1(e, source, inCrefs)
                    verifyBoolWhenEquation1(rest, initCond, crefs)
                  end

                  DAE.ARRAY_EQUATION(exp = e, source = source) <| rest  => begin
                      crefs = collectWhenCrefs1(e, source, inCrefs)
                    verifyBoolWhenEquation1(rest, initCond, crefs)
                  end

                  DAE.COMPLEX_EQUATION(lhs = e, source = source) <| rest  => begin
                      crefs = collectWhenCrefs1(e, source, inCrefs)
                    verifyBoolWhenEquation1(rest, initCond, crefs)
                  end

                  DAE.EQUEQUATION(cr1 = cr) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, _cons(cr, inCrefs))
                  end

                  DAE.IF_EQUATION(equations2 = trueEqs, equations3 = falseEqs, source = source) <| rest  => begin
                      crefsLists = ListUtil.map2(trueEqs, verifyBoolWhenEquation1, initCond, nil)
                      crefs = verifyBoolWhenEquation1(falseEqs, initCond)
                      crefsLists = _cons(crefs, crefsLists)
                      (crefs, b) = compareCrefList(crefsLists)
                      if ! b
                        info = ElementSource.getElementSourceFileInfo(source)
                        msg = "All branches must write to the same variable"
                        Error.addSourceMessage(Error.WHEN_EQ_LHS, list(msg), info)
                        fail()
                      end
                    verifyBoolWhenEquation1(rest, initCond, listAppend(crefs, inCrefs))
                  end

                  DAE.ASSERT(__) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, inCrefs)
                  end

                  DAE.TERMINATE(__) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, inCrefs)
                  end

                  DAE.REINIT(source = source) <| rest  => begin
                      if initCond
                        info = ElementSource.getElementSourceFileInfo(source)
                        Error.addSourceMessage(Error.REINIT_IN_WHEN_INITIAL, nil, info)
                        fail()
                      end
                    verifyBoolWhenEquation1(rest, initCond, inCrefs)
                  end

                  DAE.NORETCALL(__) <| rest  => begin
                    verifyBoolWhenEquation1(rest, initCond, inCrefs)
                  end

                  DAE.WHEN_EQUATION(condition = e, source = source) <| _  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      if Types.isClockOrSubTypeClock(Expression.typeof(e))
                        Error.addSourceMessage(Error.CLOCKED_WHEN_IN_WHEN_EQ, nil, info)
                      else
                        Error.addSourceMessage(Error.NESTED_WHEN, nil, info)
                      end
                    fail()
                  end

                  el <| _  => begin
                      msg = "- DAEUtil.verifyWhenEquationStatements failed on: " + DAEDump.dumpElementsStr(list(el))
                      info = ElementSource.getElementSourceFileInfo(ElementSource.getElementSource(el))
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(msg), info)
                    fail()
                  end
                end
              end
          outCrefs
        end

        function collectWhenCrefs(inExps::List{<:DAE.Exp}, source::DAE.ElementSource, inCrefs::List{<:DAE.ComponentRef} = nil) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              outCrefs = ListUtil.fold1(inExps, collectWhenCrefs1, source, inCrefs)
          outCrefs
        end

        function collectWhenCrefs1(inExp::DAE.Exp, source::DAE.ElementSource, inCrefs::List{<:DAE.ComponentRef} = nil) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              local e::DAE.Exp
              local exps::List{DAE.Exp}
              local cr::DAE.ComponentRef

              outCrefs = begin
                  local msg::String
                  local info::SourceInfo
                @match inExp begin
                  DAE.CREF(cr, _)  => begin
                    _cons(cr, inCrefs)
                  end

                  DAE.TUPLE(exps)  => begin
                    collectWhenCrefs(exps, source, inCrefs)
                  end

                  _  => begin
                        msg = ExpressionDump.printExpStr(inExp)
                        info = ElementSource.getElementSourceFileInfo(source)
                        Error.addSourceMessage(Error.WHEN_EQ_LHS, list(msg), info)
                      fail()
                  end
                end
              end
          outCrefs
        end

         #=  =#
        function compareCrefList(inCrefs::List{<:List{<:DAE.ComponentRef}}) ::Tuple{List{DAE.ComponentRef}, Bool}
              local matching::Bool
              local outrefs::List{DAE.ComponentRef}

              (outrefs, matching) = begin
                  local crefs::List{DAE.ComponentRef}
                  local recRefs::List{DAE.ComponentRef}
                  local i::ModelicaInteger
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local llrefs::List{List{DAE.ComponentRef}}
                @match inCrefs begin
                   nil()  => begin
                    (nil, true)
                  end

                  crefs <|  nil()  => begin
                    (crefs, true)
                  end

                  crefs <| llrefs  => begin
                      (recRefs, b3) = compareCrefList(llrefs)
                      i = listLength(recRefs)
                      if intGt(i, 0)
                        b1 = 0 == intMod(listLength(crefs), i)
                        crefs = ListUtil.unionOnTrueList(list(recRefs, crefs), ComponentReference.crefEqual)
                        b2 = intEq(listLength(crefs), i)
                        b1 = boolAnd(b1, boolAnd(b2, b3))
                      else
                        @match true = intEq(i, 0)
                        @match true = intEq(listLength(crefs), 0)
                        b1 = true
                      end
                    (crefs, b1)
                  end
                end
              end
          (outrefs, matching)
        end

         #= lochel: This is not used.
          evaluates the annotation Evaluate =#
        function evaluateAnnotation(inCache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist) ::DAE.DAElist
              local outDAElist::DAE.DAElist

              outDAElist = begin
                  local dae::DAE.DAElist
                  local ht::HashTable2.HashTable
                  local pv::HashTable2.HashTable
                  local ht1::HashTable2.HashTable
                  local elts::List{DAE.Element}
                  local elts1::List{DAE.Element}
                  local elts2::List{DAE.Element}
                  local cache::FCore.Cache
                @matchcontinue (inCache, env, inDAElist) begin
                  (_, _, dae && DAE.DAE(elts))  => begin
                      pv = getParameterVars(dae, HashTable2.emptyHashTable())
                      @match (ht, true) = evaluateAnnotation1(dae, pv, HashTable2.emptyHashTable())
                      (_, ht1, _) = evaluateAnnotation2_loop(inCache, env, dae, ht, BaseHashTable.hashTableCurrentSize(ht))
                      (elts2, _) = traverseDAEElementList(elts, Expression.traverseSubexpressionsHelper, (evaluateAnnotationTraverse, (ht1, 0, 0)))
                    DAE.DAE(elts2)
                  end

                  _  => begin
                      inDAElist
                  end
                end
              end
          outDAElist
        end

         #= author: Frenkel TUD, 2010-12 =#
        function evaluateAnnotationTraverse(inExp::DAE.Exp, itpl::Tuple{<:HashTable2.HashTable, ModelicaInteger, ModelicaInteger}) ::Tuple{DAE.Exp, Tuple{HashTable2.HashTable, ModelicaInteger, ModelicaInteger}}
              local otpl::Tuple{HashTable2.HashTable, ModelicaInteger, ModelicaInteger}
              local outExp::DAE.Exp

              (outExp, otpl) = begin
                  local cr::DAE.ComponentRef
                  local ht::HashTable2.HashTable
                  local exp::DAE.Exp
                  local e1::DAE.Exp
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                  local k::ModelicaInteger
                  local varLst::List{DAE.Var}
                   #=  Special Case for Records
                   =#
                @matchcontinue (inExp, itpl) begin
                  (exp && DAE.CREF(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_))), (ht, i, j))  => begin
                      @match (e1, true) = Expression.extendArrExp(exp, false)
                      (e1, (ht, i, k)) = Expression.traverseExpBottomUp(e1, evaluateAnnotationTraverse, itpl)
                      @match true = intGt(k, j)
                    (e1, (ht, i, k))
                  end

                  (exp && DAE.CREF(ty = DAE.T_ARRAY(__)), (ht, i, j))  => begin
                      @match (e1, true) = Expression.extendArrExp(exp, false)
                      (e1, (ht, i, k)) = Expression.traverseExpBottomUp(e1, evaluateAnnotationTraverse, itpl)
                      @match true = intGt(k, j)
                    (e1, (ht, i, k))
                  end

                  (exp && DAE.CREF(__), (ht, i, j))  => begin
                      e1 = replaceCrefInAnnotation(exp, ht)
                      @match true = Expression.isConst(e1)
                    (e1, (ht, i, j + 1))
                  end

                  (exp && DAE.CREF(__), (ht, i, j))  => begin
                    (exp, (ht, i + 1, j))
                  end

                  _  => begin
                      (inExp, itpl)
                  end
                end
              end
               #=  Special Case for Arrays
               =#
          (outExp, otpl)
        end

         #=
          helper of evaluateAnnotationTraverse =#
        function replaceCrefInAnnotation(inExp::DAE.Exp, inTable::HashTable2.HashTable) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                @matchcontinue (inExp, inTable) begin
                  (DAE.CREF(componentRef = cr), _)  => begin
                      exp = BaseHashTable.get(cr, inTable)
                    replaceCrefInAnnotation(exp, inTable)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

        function getParameterVars(dae::DAE.DAElist, ht::HashTable2.HashTable) ::HashTable2.HashTable
              local oht::HashTable2.HashTable

              local elts::List{DAE.Element}

              @match DAE.DAE(elts) = dae
              oht = ListUtil.fold(elts, getParameterVars2, ht)
          oht
        end

        function getParameterVars2(elt::DAE.Element, ht::HashTable2.HashTable) ::HashTable2.HashTable
              local ouHt::HashTable2.HashTable

              ouHt = begin
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local elts::List{DAE.Element}
                @matchcontinue (elt, ht) begin
                  (DAE.COMP(dAElist = elts), _)  => begin
                    ListUtil.fold(elts, getParameterVars2, ht)
                  end

                  (DAE.VAR(componentRef = cr, kind = DAE.PARAM(__), binding = SOME(e)), _)  => begin
                    BaseHashTable.add((cr, e), ht)
                  end

                  (DAE.VAR(componentRef = cr, kind = DAE.PARAM(__), variableAttributesOption = dae_var_attr), _)  => begin
                      e = getStartAttrFail(dae_var_attr)
                    BaseHashTable.add((cr, e), ht)
                  end

                  _  => begin
                      ht
                  end
                end
              end
          ouHt
        end

         #= evaluates the annotation Evaluate =#
        function evaluateAnnotation1(dae::DAE.DAElist, pv::HashTable2.HashTable, ht::HashTable2.HashTable) ::Tuple{HashTable2.HashTable, Bool}
              local hasEvaluate::Bool
              local oht::HashTable2.HashTable

              local elts::List{DAE.Element}

              @match DAE.DAE(elts) = dae
              (oht, hasEvaluate) = ListUtil.fold1r(elts, evaluateAnnotation1Fold, pv, (ht, false))
          (oht, hasEvaluate)
        end

         #= evaluates the annotation Evaluate =#
        function evaluateAnnotation1Fold(tpl::Tuple{<:HashTable2.HashTable, Bool}, el::DAE.Element, inPV::HashTable2.HashTable) ::Tuple{HashTable2.HashTable, Bool}
              local otpl::Tuple{HashTable2.HashTable, Bool}

              otpl = begin
                  local rest::List{DAE.Element}
                  local sublist::List{DAE.Element}
                  local comment::SCode.Comment
                  local ht::HashTable2.HashTable
                  local ht1::HashTable2.HashTable
                  local ht2::HashTable2.HashTable
                  local pv::HashTable2.HashTable
                  local cr::DAE.ComponentRef
                  local anno::SCode.Annotation
                  local annos::List{SCode.Annotation}
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local b::Bool
                  local b1::Bool
                @matchcontinue (tpl, el, inPV) begin
                  (_, DAE.COMP(dAElist = sublist), pv)  => begin
                    ListUtil.fold1r(sublist, evaluateAnnotation1Fold, pv, tpl)
                  end

                  ((ht, _), DAE.VAR(componentRef = cr, kind = DAE.PARAM(__), binding = SOME(e), comment = SOME(comment)), pv)  => begin
                      @match SCode.COMMENT(annotation_ = SOME(anno)) = comment
                      @match true = SCodeUtil.hasBooleanNamedAnnotation(anno, "Evaluate")
                      e1 = evaluateParameter(e, pv)
                      ht1 = BaseHashTable.add((cr, e1), ht)
                    (ht1, true)
                  end

                  _  => begin
                      tpl
                  end
                end
              end
          otpl
        end

        function evaluateParameter(inExp::DAE.Exp, inPV::HashTable2.HashTable) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local pv::HashTable2.HashTable
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local i::ModelicaInteger
                @matchcontinue (inExp, inPV) begin
                  (e, _)  => begin
                      @match true = Expression.isConst(e)
                    e
                  end

                  (e, _)  => begin
                      @match false = Expression.expHasCrefs(e)
                    e
                  end

                  (e, pv)  => begin
                      (e1, (_, i, _)) = Expression.traverseExpBottomUp(e, evaluateAnnotationTraverse, (pv, 0, 0))
                      @match true = intEq(i, 0)
                      e2 = evaluateParameter(e1, pv)
                    e2
                  end
                end
              end
               #=  {} = Expression.extractCrefsFromExp(e);
               =#
          outExp
        end

        function evaluateAnnotation2_loop(cache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist, inHt::HashTable2.HashTable, sizeBefore::ModelicaInteger) ::Tuple{List{DAE.Element}, HashTable2.HashTable, FCore.Cache}
              local outCache::FCore.Cache
              local outHt::HashTable2.HashTable
              local outDAElist::List{DAE.Element}

              local newsize::ModelicaInteger

              (outDAElist, outHt, outCache) = evaluateAnnotation2(cache, env, inDAElist, inHt)
              newsize = BaseHashTable.hashTableCurrentSize(outHt)
              (outDAElist, outHt, outCache) = evaluateAnnotation2_loop1(intEq(newsize, sizeBefore), outCache, env, DAE.DAE(outDAElist), outHt, newsize)
          (outDAElist, outHt, outCache)
        end

        function evaluateAnnotation2_loop1(finish::Bool, inCache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist, inHt::HashTable2.HashTable, sizeBefore::ModelicaInteger) ::Tuple{List{DAE.Element}, HashTable2.HashTable, FCore.Cache}
              local outCache::FCore.Cache
              local outHt::HashTable2.HashTable
              local outDAElist::List{DAE.Element}

              (outDAElist, outHt, outCache) = begin
                  local ht::HashTable2.HashTable
                  local elst::List{DAE.Element}
                  local cache::FCore.Cache
                @match (finish, inCache, env, inDAElist, inHt, sizeBefore) begin
                  (true, _, _, DAE.DAE(elst), _, _)  => begin
                    (elst, inHt, inCache)
                  end

                  _  => begin
                        (elst, ht, cache) = evaluateAnnotation2_loop(inCache, env, inDAElist, inHt, sizeBefore)
                      (elst, ht, cache)
                  end
                end
              end
          (outDAElist, outHt, outCache)
        end

         #= evaluates the parameters with bindings parameters with annotation Evaluate =#
        function evaluateAnnotation2(inCache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist, inHt::HashTable2.HashTable) ::Tuple{List{DAE.Element}, HashTable2.HashTable, FCore.Cache}
              local outCache::FCore.Cache
              local outHt::HashTable2.HashTable
              local outDAElist::List{DAE.Element}

              (outDAElist, outHt, outCache) = begin
                  local elementLst::List{DAE.Element}
                  local elementLst1::List{DAE.Element}
                  local ht::HashTable2.HashTable
                  local ht1::HashTable2.HashTable
                  local cache::FCore.Cache
                @matchcontinue (inCache, env, inDAElist, inHt) begin
                  (_, _, DAE.DAE( nil()), ht)  => begin
                    (nil, ht, inCache)
                  end

                  (_, _, DAE.DAE(elementLst = elementLst), ht)  => begin
                      (elementLst1, (ht1, cache, _)) = ListUtil.mapFold(elementLst, evaluateAnnotation3, (ht, inCache, env))
                    (elementLst1, ht1, cache)
                  end
                end
              end
          (outDAElist, outHt, outCache)
        end

         #= evaluates the parameters with bindings parameters with annotation Evaluate =#
        function evaluateAnnotation3(iel::DAE.Element, inHt::Tuple{<:HashTable2.HashTable, FCore.Cache, FCore.Graph}) ::Tuple{DAE.Element, Tuple{HashTable2.HashTable, FCore.Cache, FCore.Graph}}
              local outHt::Tuple{HashTable2.HashTable, FCore.Cache, FCore.Graph}
              local oel::DAE.Element

              (oel, outHt) = begin
                  local httpl::Tuple{HashTable2.HashTable, FCore.Cache, FCore.Graph}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local rest::List{DAE.Element}
                  local sublist::List{DAE.Element}
                  local sublist1::List{DAE.Element}
                  local newlst::List{DAE.Element}
                  local ht::HashTable2.HashTable
                  local ht1::HashTable2.HashTable
                  local ht2::HashTable2.HashTable
                  local cr::DAE.ComponentRef
                  local anno::SCode.Annotation
                  local annos::List{SCode.Annotation}
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local ident::DAE.Ident
                  local source::DAE.ElementSource
                  local comment::Option{SCode.Comment}
                  local kind::DAE.VarKind
                  local kind1::DAE.VarKind
                  local direction::DAE.VarDirection
                  local parallelism::DAE.VarParallelism
                  local protection::DAE.VarVisibility
                  local ty::DAE.Type
                  local binding::Option{DAE.Exp}
                  local dims::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local variableAttributesOption::Option{DAE.VariableAttributes}
                  local absynCommentOption::Option{SCode.Comment}
                  local innerOuter::Absyn.InnerOuter
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                @matchcontinue (iel, inHt) begin
                  (DAE.COMP(ident = ident, dAElist = sublist, source = source, comment = comment), _)  => begin
                      (sublist1, httpl) = ListUtil.mapFold(sublist, evaluateAnnotation3, inHt)
                    (DAE.COMP(ident, sublist1, source, comment), httpl)
                  end

                  (DAE.VAR(componentRef = cr, kind = DAE.PARAM(__), direction = direction, parallelism = parallelism, protection = protection, ty = ty, binding = SOME(e), dims = dims, connectorType = ct, source = source, variableAttributesOption = variableAttributesOption, comment = absynCommentOption, innerOuter = innerOuter), (ht, cache, env))  => begin
                      (e1, (_, i, j)) = Expression.traverseExpBottomUp(e, evaluateAnnotationTraverse, (ht, 0, 0))
                      (e2, ht1, cache) = evaluateAnnotation4(cache, env, cr, e1, i, j, ht)
                    (DAE.VAR(cr, DAE.PARAM(), direction, parallelism, protection, ty, SOME(e2), dims, ct, source, variableAttributesOption, absynCommentOption, innerOuter), (ht1, cache, env))
                  end

                  _  => begin
                      (iel, inHt)
                  end
                end
              end
          (oel, outHt)
        end

         #= evaluates the parameters with bindings parameters with annotation Evaluate =#
        function evaluateAnnotation4(inCache::FCore.Cache, env::FCore.Graph, inCr::DAE.ComponentRef, inExp::DAE.Exp, inInteger1::ModelicaInteger, inInteger2::ModelicaInteger, inHt::HashTable2.HashTable) ::Tuple{DAE.Exp, HashTable2.HashTable, FCore.Cache}
              local outCache::FCore.Cache
              local outHt::HashTable2.HashTable
              local outExp::DAE.Exp

              (outExp, outHt, outCache) = begin
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                  local ht::HashTable2.HashTable
                  local ht1::HashTable2.HashTable
                  local cache::FCore.Cache
                  local value::Values.Value
                @matchcontinue (inCache, env, inCr, inExp, inInteger1, inInteger2, inHt) begin
                  (_, _, cr, e, i, j, ht)  => begin
                      @match true = intGt(j, 0)
                      @match true = intEq(i, 0)
                      (e1, (ht, _, _)) = Expression.traverseExpBottomUp(e, evaluateAnnotationTraverse, (ht, 0, 0))
                      (cache, value) = Ceval.ceval(inCache, env, e1, false, Absyn.NO_MSG(), 0)
                      e1 = ValuesUtil.valueExp(value)
                      ht1 = BaseHashTable.add((cr, e1), ht)
                    (e1, ht1, cache)
                  end

                  (_, _, _, e, _, _, ht)  => begin
                    (e, ht, inCache)
                  end
                end
              end
               #=  there is a paramter with evaluate=true
               =#
               #=  there are no other crefs
               =#
               #=  evalute expression
               =#
               #=  e1 = e;
               =#
          (outExp, outHt, outCache)
        end

         #= author: BZ, 2008-12
          Rename innerouter(the inner part of innerouter) variables that have been renamed to a.b.$unique$var
          Just remove the $unique$ from the var name.
          This function traverses the entire dae. =#
        function renameUniqueOuterVars(dae::DAE.DAElist) ::DAE.DAElist
              local odae::DAE.DAElist

              (odae, _, _) = traverseDAE(dae, DAE.AvlTreePathFunction.Tree.EMPTY(), Expression.traverseSubexpressionsHelper, (removeUniqieIdentifierFromCref, nil))
          odae
        end

         #= Function for Expression.traverseExpBottomUp, removes the constant 'UNIQUEIO' from any cref it might visit. =#
        function removeUniqieIdentifierFromCref(inExp::DAE.Exp, oarg::Type_a) ::Tuple{DAE.Exp, Type_a}
              local outDummy::Type_a
              local outExp::DAE.Exp

              (outExp, outDummy) = begin
                  local cr::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local ty::DAE.Type
                  local exp::DAE.Exp
                @matchcontinue (inExp, oarg) begin
                  (DAE.CREF(cr, ty), _)  => begin
                      cr2 = unNameInnerouterUniqueCref(cr, DAE.UNIQUEIO)
                      exp = Expression.makeCrefExp(cr2, ty)
                    (exp, oarg)
                  end

                  _  => begin
                      (inExp, oarg)
                  end
                end
              end
          (outExp, outDummy)
        end

         #= author: BZ, 2008-12
          Rename all variables to the form a.b.$unique$var, call
          This function traverses the entire dae. =#
        function nameUniqueOuterVars(dae::DAE.DAElist) ::DAE.DAElist
              local odae::DAE.DAElist

              (odae, _, _) = traverseDAE(dae, DAE.AvlTreePathFunction.Tree.EMPTY(), Expression.traverseSubexpressionsHelper, (addUniqueIdentifierToCref, nil))
          odae
        end

         #= author: BZ, 2008-12
          Function for Expression.traverseExpBottomUp, adds the constant 'UNIQUEIO' to the CREF_IDENT() part of the cref. =#
        function addUniqueIdentifierToCref(inExp::DAE.Exp, oarg::Type_a) ::Tuple{DAE.Exp, Type_a}
              local outDummy::Type_a
              local outExp::DAE.Exp

              (outExp, outDummy) = begin
                  local cr::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local ty::DAE.Type
                  local exp::DAE.Exp
                @matchcontinue (inExp, oarg) begin
                  (DAE.CREF(cr, ty), _)  => begin
                      cr2 = nameInnerouterUniqueCref(cr)
                      exp = Expression.makeCrefExp(cr2, ty)
                    (exp, oarg)
                  end

                  _  => begin
                      (inExp, oarg)
                  end
                end
              end
          (outExp, outDummy)
        end

         #=  helper functions for traverseDAE
         =#

         #= author: BZ, 2008-12
          Traverse an optional expression, helper function for traverseDAE =#
        function traverseDAEOptExp(oexp::Option{<:DAE.Exp}, func::FuncExpType, iextraArg::Type_a) ::Tuple{Option{DAE.Exp}, Type_a}
              local oextraArg::Type_a
              local ooexp::Option{DAE.Exp}

              (ooexp, oextraArg) = begin
                  local e::DAE.Exp
                  local extraArg::Type_a
                @match (oexp, func, iextraArg) begin
                  (NONE(), _, extraArg)  => begin
                    (NONE(), extraArg)
                  end

                  (SOME(e), _, extraArg)  => begin
                      (e, extraArg) = func(e, extraArg)
                    (SOME(e), extraArg)
                  end
                end
              end
          (ooexp, oextraArg)
        end

         #= author: BZ, 2008-12
          Traverse an list of expressions, helper function for traverseDAE =#
        function traverseDAEExpList(iexps::List{<:DAE.Exp}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Exp}, Type_a}
              local oextraArg::Type_a
              local oexps::List{DAE.Exp}

              (oexps, oextraArg) = begin
                  local e::DAE.Exp
                  local extraArg::Type_a
                  local exps::List{DAE.Exp}
                @match (iexps, func, iextraArg) begin
                  ( nil(), _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (e <| exps, _, extraArg)  => begin
                      (e, extraArg) = func(e, extraArg)
                      (oexps, extraArg) = traverseDAEExpList(exps, func, extraArg)
                    (_cons(e, oexps), extraArg)
                  end
                end
              end
          (oexps, oextraArg)
        end

         #= author: BZ, 2008-12
          Helper function for traverseDAE, traverses a list of dae element list. =#
        function traverseDAEList(idaeList::List{<:List{<:DAE.Element}}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{List{DAE.Element}}, Type_a}
              local oextraArg::Type_a
              local traversedDaeList::List{List{DAE.Element}}

              (traversedDaeList, oextraArg) = begin
                  local branch::List{DAE.Element}
                  local branch2::List{DAE.Element}
                  local recRes::List{List{DAE.Element}}
                  local daeList::List{List{DAE.Element}}
                  local extraArg::Type_a
                @match (idaeList, func, iextraArg) begin
                  ( nil(), _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (branch <| daeList, _, extraArg)  => begin
                      (branch2, extraArg) = traverseDAEElementList(branch, func, extraArg)
                      (recRes, extraArg) = traverseDAEList(daeList, func, extraArg)
                    (_cons(branch2, recRes), extraArg)
                  end
                end
              end
          (traversedDaeList, oextraArg)
        end

        function getFunctionList(ft::DAE.FunctionTree, failOnError::Bool = false) ::List{DAE.Function}
              local fns::List{DAE.Function}

              local lst::List{Tuple{DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}}
              local lstInvalid::List{Tuple{DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}}
              local str::String

              try
                fns = ListUtil.map(DAE.AvlTreePathFunction.listValues(ft), Util.getOption)
              catch
                lst = DAE.AvlTreePathFunction.toList(ft)
                lstInvalid = ListUtil.select(lst, isInvalidFunctionEntry)
                str = stringDelimitList(list(AbsynUtil.pathString(p) for p in ListUtil.map(lstInvalid, Util.tuple21)), "\\n ")
                str = "\\n " + str + "\\n"
                Error.addMessage(Error.NON_INSTANTIATED_FUNCTION, list(str))
                if failOnError
                  fail()
                end
                fns = ListUtil.mapMap(ListUtil.select(lst, isValidFunctionEntry), Util.tuple22, Util.getOption)
              end
          fns
        end

        function getFunctionNames(ft::DAE.FunctionTree) ::List{String}
              local strs::List{String}

              strs = ListUtil.mapMap(getFunctionList(ft), functionName, AbsynUtil.pathStringDefault)
          strs
        end

        function isInvalidFunctionEntry(tpl::Tuple{<:DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}) ::Bool
              local b::Bool

              b = begin
                @match tpl begin
                  (_, NONE())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isValidFunctionEntry(tpl::Tuple{<:DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}) ::Bool
              local b::Bool

              b = ! isInvalidFunctionEntry(tpl)
          b
        end

         #= This function traverses all dae exps.
           NOTE, it also traverses DAE.VAR(componenname) as an expression. =#
        function traverseDAE(dae::DAE.DAElist, functionTree::DAE.FunctionTree, func::FuncExpType, arg::ArgT)  where {ArgT}




              local el::List{DAE.Element}

              (el, arg) = traverseDAEElementList(dae.elementLst, func, arg)
              dae.elementLst = el
              (functionTree, arg) = DAE.AvlTreePathFunction.mapFold(functionTree, (func) -> traverseDAEFuncHelper(func = func), arg)
          (dae, functionTree, arg)
        end

         #= Helper function to traverseDae. Traverses the functions. =#
        function traverseDAEFuncHelper(key::DAE.AvlTreePathFunction.Key, value::DAE.AvlTreePathFunction.Value, func::FuncExpType, arg::ArgT)  where {ArgT}



              (value, arg) = begin
                  local daeFunc1::DAE.Function
                  local daeFunc2::DAE.Function
                @match value begin
                  SOME(daeFunc1)  => begin
                      (daeFunc2, arg) = traverseDAEFunc(daeFunc1, func, arg)
                    (if referenceEq(daeFunc1, daeFunc2)
                          value
                        else
                          SOME(daeFunc2)
                        end, arg)
                  end

                  NONE()  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- DAEUtil.traverseDAEFuncLst failed: " + AbsynUtil.pathString(key))
                    fail()
                  end
                end
              end
          (value, arg)
        end

         #= Traverses the functions.
           Note: Only calls the top-most expressions. If you need to also traverse the
           expression, use an extra helper function. =#
        function traverseDAEFunctions(functions::List{DAE.Function}, func::FuncExpType, arg::ArgT)  where {ArgT}



              (functions, arg) = ListUtil.mapFold(functions, (func) -> traverseDAEFunc(func = func), arg)
          (functions, arg)
        end

        function traverseDAEFunc(daeFunction::DAE.Function, func::FuncExpType, arg::ArgT)  where {ArgT}



              _ = begin
                  local fdef::DAE.FunctionDefinition
                  local rest_defs::List{DAE.FunctionDefinition}
                  local el::List{DAE.Element}
                @match daeFunction begin
                  DAE.FUNCTION(functions = fdef && DAE.FUNCTION_DEF(__) <| rest_defs)  => begin
                      (el, arg) = traverseDAEElementList(fdef.body, func, arg)
                      if ! referenceEq(fdef.body, el)
                        fdef.body = el
                        daeFunction.functions = _cons(fdef, rest_defs)
                      end
                    ()
                  end

                  DAE.FUNCTION(functions = fdef && DAE.FUNCTION_EXT(__) <| rest_defs)  => begin
                      (el, arg) = traverseDAEElementList(fdef.body, func, arg)
                      if ! referenceEq(fdef.body, el)
                        fdef.body = el
                        daeFunction.functions = _cons(fdef, rest_defs)
                      end
                    ()
                  end

                  DAE.RECORD_CONSTRUCTOR(__)  => begin
                    ()
                  end
                end
              end
          (daeFunction, arg)
        end

         #= author: BZ, 2008-12, adrpo, 2010-12
           This function traverses all dae exps.
           NOTE, it also traverses DAE.VAR(componenname) as an expression. =#
        function traverseDAEElementList(elements::List{DAE.Element}, func::FuncExpType, arg::ArgT)  where {ArgT}



              (elements, arg) = ListUtil.mapFold(elements, (func) -> traverseDAEElement(func = func), arg)
          (elements, arg)
        end

         #= author: adrpo, 2010-12
           This function is a tail recursive function that traverses all dae exps.
           NOTE, it also traverses DAE.VAR(componenname) as an expression. =#
        function traverseDAEElement(element::DAE.Element, func::FuncExpType, arg::ArgT)  where {ArgT}



              _ = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local new_e1::DAE.Exp
                  local new_e2::DAE.Exp
                  local new_e3::DAE.Exp
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local new_cr1::DAE.ComponentRef
                  local new_cr2::DAE.ComponentRef
                  local el::List{DAE.Element}
                  local new_el::List{DAE.Element}
                  local eqll::List{List{DAE.Element}}
                  local new_eqll::List{List{DAE.Element}}
                  local e::DAE.Element
                  local new_e::DAE.Element
                  local stmts::List{DAE.Statement}
                  local new_stmts::List{DAE.Statement}
                  local expl::List{DAE.Exp}
                  local new_expl::List{DAE.Exp}
                  local binding::Option{DAE.Exp}
                  local new_binding::Option{DAE.Exp}
                  local attr::Option{DAE.VariableAttributes}
                  local new_attr::Option{DAE.VariableAttributes}
                  local varLst::List{DAE.Var}
                  local daebinding::DAE.Binding
                  local new_daebinding::DAE.Binding
                  local changed::Bool
                  local new_ty::DAE.Type
                @match element begin
                  DAE.VAR(componentRef = cr1, binding = binding, variableAttributesOption = attr)  => begin
                      (e1, arg) = func(Expression.crefExp(cr1), arg)
                      if Expression.isCref(e1)
                        new_cr1 = Expression.expCref(e1)
                        if ! referenceEq(cr1, new_cr1)
                          element.componentRef = new_cr1
                        end
                      end
                      element.dims = list(begin
                        @match d begin
                          DAE.DIM_EXP(e1)  => begin
                              (new_e1, arg) = func(e1, arg)
                            if referenceEq(e1, new_e1)
                                  d
                                else
                                  DAE.DIM_EXP(new_e1)
                                end
                          end

                          _  => begin
                              d
                          end
                        end
                      end for d in element.dims)
                      new_ty = begin
                        @match (@match element.ty = ty) begin
                          DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))  => begin
                              changed = false
                              varLst = list(begin
                                @match v begin
                                  DAE.TYPES_VAR(binding = daebinding && DAE.EQBOUND(__))  => begin
                                      (e2, arg) = func(daebinding.exp, arg)
                                      if ! referenceEq(daebinding.exp, e2)
                                        daebinding = DAE.EQBOUND(e2, NONE(), daebinding.constant_, daebinding.source)
                                        v.binding = daebinding
                                        changed = true
                                      end
                                    v
                                  end

                                  DAE.TYPES_VAR(binding = daebinding && DAE.VALBOUND(__))  => begin
                                      e1 = ValuesUtil.valueExp(daebinding.valBound)
                                      (e2, arg) = func(e1, arg)
                                      if ! referenceEq(e1, e2)
                                        new_daebinding = DAE.EQBOUND(e2, NONE(), DAE.C_CONST(), daebinding.source)
                                        v.binding = new_daebinding
                                        changed = true
                                      end
                                    v
                                  end

                                  _  => begin
                                      v
                                  end
                                end
                              end for v in ty.varLst)
                              if ! referenceEq(varLst, ty.varLst)
                                ty.varLst = varLst
                              end
                            ty
                          end

                          _  => begin
                              ty
                          end
                        end
                      end
                      if ! referenceEq(element.ty, new_ty)
                        element.ty = new_ty
                      end
                      (new_binding, arg) = traverseDAEOptExp(binding, func, arg)
                      if ! referenceEq(binding, new_binding)
                        element.binding = new_binding
                      end
                      (new_attr, arg) = traverseDAEVarAttr(attr, func, arg)
                      if ! referenceEq(attr, new_attr)
                        element.variableAttributesOption = new_attr
                      end
                    ()
                  end

                  DAE.DEFINE(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(Expression.crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.INITIALDEFINE(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(Expression.crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2)  => begin
                      @match (DAE.CREF(new_cr1), arg) = func(Expression.crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.cr1 = new_cr1
                      end
                      @match (DAE.CREF(new_cr2), arg) = func(Expression.crefExp(cr2), arg)
                      if ! referenceEq(cr2, new_cr2)
                        element.cr2 = new_cr2
                      end
                    ()
                  end

                  DAE.EQUATION(exp = e1, scalar = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.scalar = new_e2
                      end
                    ()
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp1 = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.exp2 = new_e2
                      end
                    ()
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.lhs = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.rhs = new_e2
                      end
                    ()
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.lhs = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.rhs = new_e2
                      end
                    ()
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.array = new_e2
                      end
                    ()
                  end

                  DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.array = new_e2
                      end
                    ()
                  end

                  DAE.WHEN_EQUATION(condition = e1, equations = el)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations = new_el
                      end
                      if isSome(element.elsewhen_)
                        @match SOME(e) = element.elsewhen_
                        (new_e, arg) = traverseDAEElement(e, func, arg)
                        if ! referenceEq(e, new_e)
                          element.elsewhen_ = SOME(new_e)
                        end
                      end
                    ()
                  end

                  DAE.FOR_EQUATION(range = e1, equations = el)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.range = new_e1
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations = new_el
                      end
                    ()
                  end

                  DAE.COMP(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.EXTOBJECTCLASS(__)  => begin
                    ()
                  end

                  DAE.ASSERT(condition = e1, message = e2, level = e3)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.message = new_e2
                      end
                      (new_e3, arg) = func(e3, arg)
                      if ! referenceEq(e3, new_e3)
                        element.level = new_e3
                      end
                    ()
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2, level = e3)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.message = new_e2
                      end
                      (new_e3, arg) = func(e3, arg)
                      if ! referenceEq(e3, new_e3)
                        element.level = new_e3
                      end
                    ()
                  end

                  DAE.TERMINATE(message = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.message = new_e1
                      end
                    ()
                  end

                  DAE.INITIAL_TERMINATE(message = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.message = new_e1
                      end
                    ()
                  end

                  DAE.NORETCALL(exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                    ()
                  end

                  DAE.INITIAL_NORETCALL(exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                    ()
                  end

                  DAE.REINIT(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(Expression.crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(stmts))  => begin
                      (new_stmts, arg) = traverseDAEEquationsStmts(stmts, func, arg)
                      if ! referenceEq(stmts, new_stmts)
                        element.algorithm_ = DAE.ALGORITHM_STMTS(new_stmts)
                      end
                    ()
                  end

                  DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(stmts))  => begin
                      (new_stmts, arg) = traverseDAEEquationsStmts(stmts, func, arg)
                      if ! referenceEq(stmts, new_stmts)
                        element.algorithm_ = DAE.ALGORITHM_STMTS(new_stmts)
                      end
                    ()
                  end

                  DAE.CONSTRAINT(constraints = DAE.CONSTRAINT_EXPS(expl))  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.constraints = DAE.CONSTRAINT_EXPS(new_expl)
                      end
                    ()
                  end

                  DAE.CLASS_ATTRIBUTES(__)  => begin
                    ()
                  end

                  DAE.IF_EQUATION(condition1 = expl, equations2 = eqll, equations3 = el)  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.condition1 = new_expl
                      end
                      (new_eqll, arg) = traverseDAEList(eqll, func, arg)
                      if ! referenceEq(eqll, new_eqll)
                        element.equations2 = new_eqll
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations3 = new_el
                      end
                    ()
                  end

                  DAE.INITIAL_IF_EQUATION(condition1 = expl, equations2 = eqll, equations3 = el)  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.condition1 = new_expl
                      end
                      (new_eqll, arg) = traverseDAEList(eqll, func, arg)
                      if ! referenceEq(eqll, new_eqll)
                        element.equations2 = new_eqll
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations3 = new_el
                      end
                    ()
                  end

                  DAE.FLAT_SM(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.SM_COMP(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.COMMENT(__)  => begin
                    ()
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("DAEUtil.traverseDAEElement not implemented correctly for element: " + DAEDump.dumpElementsStr(list(element))))
                      fail()
                  end
                end
              end
          (element, arg)
        end

         @Uniontype TraverseStatementsOptions begin
              @Record TRAVERSE_ALL begin

              end

              @Record TRAVERSE_RHS_ONLY begin

              end
         end

         #=
          This function goes through the Algorithm structure and finds all the
          expressions and performs the function on them
         =#
        function traverseAlgorithmExps(inAlgorithm::DAE.Algorithm, func::FuncExpType, inTypeA::Type_a) ::Type_a
              local outTypeA::Type_a

              outTypeA = begin
                  local stmts::List{DAE.Statement}
                  local ext_arg_1::Type_a
                @match (inAlgorithm, func, inTypeA) begin
                  (DAE.ALGORITHM_STMTS(statementLst = stmts), _, _)  => begin
                      (_, ext_arg_1) = DAEUtil.traverseDAEEquationsStmts(stmts, func, inTypeA)
                    ext_arg_1
                  end
                end
              end
          outTypeA
        end

         #= Traversing of DAE.Statement. =#
        function traverseDAEEquationsStmts(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = traverseDAEEquationsStmtsList(inStmts, func, TRAVERSE_ALL(), iextraArg)
          (outStmts, oextraArg)
        end

         #= Traversing of DAE.Statement. Only rhs expressions are replaced, keeping lhs intact. =#
        function traverseDAEEquationsStmtsRhsOnly(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = traverseDAEEquationsStmtsList(inStmts, func, TRAVERSE_RHS_ONLY(), iextraArg)
          (outStmts, oextraArg)
        end

         #= Traversing of DAE.Statement. =#
        function traverseDAEEquationsStmtsList(inStmts::List{<:DAE.Statement}, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              local outStmtsLst::List{List{DAE.Statement}}
              local b::Bool

              (outStmtsLst, oextraArg) = ListUtil.map2Fold(inStmts, traverseDAEEquationsStmtsWork, func, opt, iextraArg)
              outStmts = ListUtil.flatten(outStmtsLst)
              b = ListUtil.allReferenceEq(inStmts, outStmts)
              outStmts = if b
                    inStmts
                  else
                    outStmts
                  end
          (outStmts, oextraArg)
        end

        function traverseStatementsOptionsEvalLhs(inExp::DAE.Exp, inA::Type_a, func::FuncExpType, opt::TraverseStatementsOptions) ::Tuple{DAE.Exp, Type_a}
              local outA::Type_a
              local outExp::DAE.Exp

              (outExp, outA) = begin
                @match (inExp, inA, func, opt) begin
                  (_, _, _, TRAVERSE_ALL(__))  => begin
                      (outExp, outA) = func(inExp, inA)
                    (outExp, outA)
                  end

                  _  => begin
                      (inExp, inA)
                  end
                end
              end
          (outExp, outA)
        end

         #= Handles the traversing of DAE.Statement. =#
        function traverseDAEEquationsStmtsWork(inStmt::DAE.Statement, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e_3::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local xs_1::List{DAE.Statement}
                  local xs::List{DAE.Statement}
                  local stmts::List{DAE.Statement}
                  local stmts1::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local tp::DAE.Type
                  local x::DAE.Statement
                  local ew::DAE.Statement
                  local ew_1::DAE.Statement
                  local b1::Bool
                  local id1::String
                  local str::String
                  local ix::ModelicaInteger
                  local source::DAE.ElementSource
                  local algElse::DAE.Else
                  local algElse1::DAE.Else
                  local extraArg::Type_a
                  local loopPrlVars::List{Tuple{DAE.ComponentRef, SourceInfo}} #= list of parallel variables used/referenced in the parfor loop =#
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                  local b::Bool
                @matchcontinue (inStmt, func, opt, iextraArg) begin
                  (DAE.STMT_ASSIGN(type_ = tp, exp1 = e, exp = e2, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = traverseStatementsOptionsEvalLhs(e, extraArg, func, opt)
                      (e_2, extraArg) = func(e2, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2)
                            inStmt
                          else
                            DAE.STMT_ASSIGN(tp, e_1, e_2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(type_ = tp, expExpLst = expl1, exp = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      @match (DAE.TUPLE(expl2), extraArg) = traverseStatementsOptionsEvalLhs(DAE.TUPLE(expl1), extraArg, func, opt)
                      x = if referenceEq(e, e_1) && referenceEq(expl1, expl2)
                            inStmt
                          else
                            DAE.STMT_TUPLE_ASSIGN(tp, expl2, e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_ASSIGN_ARR(type_ = tp, lhs = e, exp = e2, source = source), _, _, extraArg)  => begin
                      (e_2, extraArg) = func(e2, extraArg)
                      _ = begin
                        @matchcontinue () begin
                          ()  => begin
                              @match ((@match DAE.CREF(_, _) = e_1), extraArg) = traverseStatementsOptionsEvalLhs(e, extraArg, func, opt)
                              x = if referenceEq(e2, e_2) && referenceEq(e, e_1)
                                    inStmt
                                  else
                                    DAE.STMT_ASSIGN_ARR(tp, e_1, e_2, source)
                                  end
                            ()
                          end

                          _  => begin
                                @shouldFail @match (DAE.CREF(_, _), _) = func(e, extraArg)
                                x = if referenceEq(e2, e_2)
                                      inStmt
                                    else
                                      DAE.STMT_ASSIGN_ARR(tp, e, e_2, source)
                                    end
                              ()
                          end
                        end
                      end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_IF(exp = e, statementLst = stmts, else_ = algElse, source = source), _, _, extraArg)  => begin
                      (algElse1, extraArg) = traverseDAEEquationsStmtsElse(algElse, func, opt, extraArg)
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      (stmts1, b) = Algorithm.optimizeIf(e_1, stmts2, algElse1, source)
                      stmts1 = if ! b && referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(algElse, algElse1)
                            _cons(inStmt, nil)
                          else
                            stmts1
                          end
                    (stmts1, extraArg)
                  end

                  (DAE.STMT_FOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_FOR(tp, b1, id1, ix, e_1, stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_PARFOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, loopPrlVars = loopPrlVars, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_PARFOR(tp, b1, id1, ix, e_1, stmts2, loopPrlVars, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHILE(exp = e, statementLst = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHILE(e_1, stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = NONE(), source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, NONE(), source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = SOME(ew), source = source), _, _, extraArg)  => begin
                      @match (list(ew_1), extraArg) = traverseDAEEquationsStmtsList(list(ew), func, opt, extraArg)
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(ew, ew_1) && referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, SOME(ew_1), source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_ASSERT(cond = e, msg = e2, level = e3, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      (e_2, extraArg) = func(e2, extraArg)
                      (e_3, extraArg) = func(e3, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(e3, e_3)
                            inStmt
                          else
                            DAE.STMT_ASSERT(e_1, e_2, e_3, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_TERMINATE(msg = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1)
                            inStmt
                          else
                            DAE.STMT_TERMINATE(e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_REINIT(var = e, value = e2, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      (e_2, extraArg) = func(e2, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2)
                            inStmt
                          else
                            DAE.STMT_REINIT(e_1, e_2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_NORETCALL(exp = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1)
                            inStmt
                          else
                            DAE.STMT_NORETCALL(e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_RETURN(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_BREAK(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_CONTINUE(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_FAILURE(body = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      x = if referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_FAILURE(stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (x, _, _, _)  => begin
                      str = DAEDump.ppStatementStr(x)
                      str = "DAEUtil.traverseDAEEquationsStmts not implemented correctly: " + str
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #= /* We need to pass this through because simplify/etc may scalarize the cref...
                               true = Flags.isSet(Flags.FAILTRACE);
                               print(DAEDump.ppStatementStr(x));
                               print(\"Warning, not allowed to set the componentRef to a expression in DAEUtil.traverseDAEEquationsStmts\\n\");
                            */ =#
               #=  MetaModelica extension. KS
               =#
          (outStmts, oextraArg)
        end

         #= Helper function for traverseDAEEquationsStmts =#
        function traverseDAEEquationsStmtsElse(inElse::DAE.Else, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{DAE.Else, Type_a}
              local oextraArg::Type_a
              local outElse::DAE.Else

              (outElse, oextraArg) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local st::List{DAE.Statement}
                  local st_1::List{DAE.Statement}
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local extraArg::Type_a
                  local b::Bool
                @match (inElse, func, opt, iextraArg) begin
                  (DAE.NOELSE(__), _, _, extraArg)  => begin
                    (DAE.NOELSE(), extraArg)
                  end

                  (DAE.ELSEIF(e, st, el), _, _, extraArg)  => begin
                      (el_1, extraArg) = traverseDAEEquationsStmtsElse(el, func, opt, extraArg)
                      (st_1, extraArg) = traverseDAEEquationsStmtsList(st, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      outElse = Algorithm.optimizeElseIf(e_1, st_1, el_1)
                      b = referenceEq(el, el_1) && referenceEq(st, st_1) && referenceEq(e, e_1)
                      outElse = if b
                            inElse
                          else
                            outElse
                          end
                    (outElse, extraArg)
                  end

                  (DAE.ELSE(st), _, _, extraArg)  => begin
                      (st_1, extraArg) = traverseDAEEquationsStmtsList(st, func, opt, extraArg)
                      outElse = if referenceEq(st, st_1)
                            inElse
                          else
                            DAE.ELSE(st_1)
                          end
                    (outElse, extraArg)
                  end
                end
              end
          (outElse, oextraArg)
        end

         #= Author: BZ, 2008-12, wbraun 2012-09
          Traversing statemeant and provide current statement
          to FuncExptype
          Handles the traversing of DAE.Statement. =#
        function traverseDAEStmts(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e_3::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local xs_1::List{DAE.Statement}
                  local xs::List{DAE.Statement}
                  local stmts::List{DAE.Statement}
                  local stmts1::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local tp::DAE.Type
                  local x::DAE.Statement
                  local ew::DAE.Statement
                  local ew_1::DAE.Statement
                  local b1::Bool
                  local id1::String
                  local str::String
                  local ix::ModelicaInteger
                  local source::DAE.ElementSource
                  local algElse::DAE.Else
                  local extraArg::Type_a
                  local loopPrlVars::List{Tuple{DAE.ComponentRef, SourceInfo}} #= list of parallel variables used/referenced in the parfor loop =#
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                @matchcontinue (inStmts, func, iextraArg) begin
                  ( nil(), _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (x && DAE.STMT_ASSIGN(type_ = tp, exp1 = e2, exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSIGN(tp, e_2, e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_TUPLE_ASSIGN(type_ = tp, expExpLst = expl1, exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (expl2, extraArg) = traverseDAEExpListStmt(expl1, func, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(expl2, expl1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_TUPLE_ASSIGN(tp, expl2, e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_ASSIGN_ARR(type_ = tp, lhs = e, exp = e2, source = source) <| xs, _, extraArg)  => begin
                      (e_2, extraArg) = func(e2, x, extraArg)
                      try
                        @match ((@match DAE.CREF(_, _) = e_1), extraArg) = func(e, x, extraArg)
                      catch
                        e_1 = e
                      end
                       #=  We need to pass this through because simplify/etc may scalarize the cref...
                       =#
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSIGN_ARR(tp, e_1, e_2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_IF(exp = e, statementLst = stmts, else_ = algElse, source = source) <| xs, _, extraArg)  => begin
                      (algElse, extraArg) = traverseDAEStmtsElse(algElse, func, x, extraArg)
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (stmts1, _) = Algorithm.optimizeIf(e_1, stmts2, algElse, source)
                    (listAppend(stmts1, xs_1), extraArg)
                  end

                  (x && DAE.STMT_FOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_FOR(tp, b1, id1, ix, e_1, stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_PARFOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, loopPrlVars = loopPrlVars, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_PARFOR(tp, b1, id1, ix, e_1, stmts2, loopPrlVars, source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_WHILE(exp = e, statementLst = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_WHILE(e_1, stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = NONE(), source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, NONE(), source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = SOME(ew), source = source) <| xs, _, extraArg)  => begin
                      @match (list(_), extraArg) = traverseDAEStmts(list(ew), func, extraArg)
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, SOME(ew), source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_ASSERT(cond = e, msg = e2, level = e3, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (e_3, extraArg) = func(e3, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(e3, e_3) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSERT(e_1, e_2, e_3, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_TERMINATE(msg = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_TERMINATE(e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_REINIT(var = e, value = e2, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_REINIT(e_1, e_2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_NORETCALL(exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_NORETCALL(e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_RETURN(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (x && DAE.STMT_BREAK(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (x && DAE.STMT_CONTINUE(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (DAE.STMT_FAILURE(body = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_FAILURE(stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x <| _, _, _)  => begin
                      str = DAEDump.ppStatementStr(x)
                      str = "DAEUtil.traverseDAEStmts not implemented correctly: " + str
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  MetaModelica extension. KS
               =#
          (outStmts, oextraArg)
        end

         #= Helper function for traverseDAEEquationsStmts =#
        function traverseDAEStmtsElse(inElse::DAE.Else, func::FuncExpType, istmt::DAE.Statement, iextraArg::Type_a) ::Tuple{DAE.Else, Type_a}
              local oextraArg::Type_a
              local outElse::DAE.Else

              (outElse, oextraArg) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local st::List{DAE.Statement}
                  local st_1::List{DAE.Statement}
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local extraArg::Type_a
                @match (inElse, func, istmt, iextraArg) begin
                  (DAE.NOELSE(__), _, _, extraArg)  => begin
                    (DAE.NOELSE(), extraArg)
                  end

                  (DAE.ELSEIF(e, st, el), _, _, extraArg)  => begin
                      (el_1, extraArg) = traverseDAEStmtsElse(el, func, istmt, extraArg)
                      (st_1, extraArg) = traverseDAEStmts(st, func, extraArg)
                      (e_1, extraArg) = func(e, istmt, extraArg)
                    (Algorithm.optimizeElseIf(e_1, st_1, el_1), extraArg)
                  end

                  (DAE.ELSE(st), _, _, extraArg)  => begin
                      (st_1, extraArg) = traverseDAEStmts(st, func, extraArg)
                    (DAE.ELSE(st_1), extraArg)
                  end
                end
              end
          (outElse, oextraArg)
        end

         #=
        Author: BZ, 2008-12
        Traverse an list of expressions, helper function for traverseDAE =#
        function traverseDAEExpListStmt(iexps::List{<:DAE.Exp}, func::FuncExpType, istmt::DAE.Statement, iextraArg::Type_a) ::Tuple{List{DAE.Exp}, Type_a}
              local oextraArg::Type_a
              local oexps::List{DAE.Exp}

              (oexps, oextraArg) = begin
                  local e::DAE.Exp
                  local extraArg::Type_a
                  local exps::List{DAE.Exp}
                @match (iexps, func, istmt, iextraArg) begin
                  ( nil(), _, _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (e <| exps, _, _, extraArg)  => begin
                      (e, extraArg) = func(e, istmt, extraArg)
                      (oexps, extraArg) = traverseDAEExpListStmt(exps, func, istmt, extraArg)
                    (_cons(e, oexps), extraArg)
                  end
                end
              end
          (oexps, oextraArg)
        end

         #=
        Author: BZ, 2008-12
        Help function to traverseDAE
         =#
        function traverseDAEVarAttr(attr::Option{<:DAE.VariableAttributes}, func::FuncExpType, iextraArg::Type_a) ::Tuple{Option{DAE.VariableAttributes}, Type_a}
              local oextraArg::Type_a
              local traversedDaeList::Option{DAE.VariableAttributes}

              (traversedDaeList, oextraArg) = begin
                  local quantity::Option{DAE.Exp}
                  local unit::Option{DAE.Exp}
                  local displayUnit::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local start::Option{DAE.Exp}
                  local fixed::Option{DAE.Exp}
                  local nominal::Option{DAE.Exp}
                  local eb::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local stateSelect::Option{DAE.StateSelect}
                  local uncertainty::Option{DAE.Uncertainty}
                  local distribution::Option{DAE.Distribution}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                  local extraArg::Type_a
                @match (attr, func, iextraArg) begin
                  (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, start, fixed, nominal, stateSelect, uncertainty, distribution, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (unit, extraArg) = traverseDAEOptExp(unit, func, extraArg)
                      (displayUnit, extraArg) = traverseDAEOptExp(displayUnit, func, extraArg)
                      (min, extraArg) = traverseDAEOptExp(min, func, extraArg)
                      (max, extraArg) = traverseDAEOptExp(max, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                      (nominal, extraArg) = traverseDAEOptExp(nominal, func, extraArg)
                    (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, start, fixed, nominal, stateSelect, uncertainty, distribution, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_INT(quantity, min, max, start, fixed, uncertainty, distribution, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (min, extraArg) = traverseDAEOptExp(min, func, extraArg)
                      (max, extraArg) = traverseDAEOptExp(max, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_INT(quantity, min, max, start, fixed, uncertainty, distribution, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(quantity, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_BOOL(quantity, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_CLOCK(_, _)), _, extraArg)  => begin
                    (attr, extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_STRING(quantity, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_STRING(quantity, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(quantity, min, max, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                    (SOME(DAE.VAR_ATTR_ENUMERATION(quantity, min, max, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (NONE(), _, extraArg)  => begin
                    (NONE(), extraArg)
                  end
                end
              end
               #=  BTH
               =#
          (traversedDaeList, oextraArg)
        end

         #=
          See setComponentType =#
        function addComponentTypeOpt(inDae::DAE.DAElist, inPath::Option{<:Absyn.Path}) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local p::Absyn.Path
                  local dae::DAE.DAElist
                @match (inDae, inPath) begin
                  (dae, SOME(p))  => begin
                      dae = addComponentType(dae, p)
                    dae
                  end

                  (dae, NONE())  => begin
                    dae
                  end
                end
              end
          outDae
        end

         #=
          This function takes a dae element list and a type name and
          inserts the type name into each Var (variable) of the dae.
          This type name is the origin of the variable. =#
        function addComponentType(dae::DAE.DAElist, newtype::Absyn.Path) ::DAE.DAElist


              if ! (Flags.isSet(Flags.INFO_XML_OPERATIONS) || Flags.isSet(Flags.VISUAL_XML))
                return dae
              end
              dae = begin
                  local elts::List{DAE.Element}
                @match dae begin
                  DAE.DAE(elts)  => begin
                      elts = ListUtil.map1(elts, addComponentType2, newtype)
                    DAE.DAE(elts)
                  end
                end
              end
          dae
        end

         #=
          This function takes a dae element list and a type name and
          inserts the type name into each Var (variable) of the dae.
          This type name is the origin of the variable. =#
        function addComponentType2(elt::DAE.Element, inPath::Absyn.Path) ::DAE.Element


              elt = begin
                  local source::DAE.ElementSource
                @match elt begin
                  DAE.VAR(__)  => begin
                      elt.source = ElementSource.addElementSourceType(elt.source, inPath)
                    elt
                  end

                  _  => begin
                      elt
                  end
                end
              end
          elt
        end

         #= returns true if element matches an external function =#
        function isExtFunction(elt::DAE.Function) ::Bool
              local res::Bool

              res = begin
                @match elt begin
                  DAE.FUNCTION(functions = DAE.FUNCTION_EXT(__) <| _)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns the name of a FUNCTION or RECORD_CONSTRUCTOR =#
        function functionName(elt::DAE.Function) ::Absyn.Path
              local name::Absyn.Path

              name = begin
                @match elt begin
                  DAE.FUNCTION(path = name)  => begin
                    name
                  end

                  DAE.RECORD_CONSTRUCTOR(path = name)  => begin
                    name
                  end
                end
              end
          name
        end

         #=
        Author: BZ, 2009-12
        Function for converting a InlineType to a bool.
        Whether the inline takes place before or after index reduction does not mather.
        Any kind of inline will result in true.
         =#
        function convertInlineTypeToBool(it::DAE.InlineType) ::Bool
              local b::Bool

              b = begin
                @match it begin
                  DAE.NO_INLINE(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

         #= Retrieve the elements from a DAEList =#
        function daeElements(dae::DAE.DAElist) ::List{DAE.Element}
              local elts::List{DAE.Element}

              elts = begin
                @match dae begin
                  DAE.DAE(elts)  => begin
                    elts
                  end
                end
              end
          elts
        end

         #= joins two daes by appending the element lists and joining the function trees =#
        function joinDaes(dae1::DAE.DAElist, dae2::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local elts1::List{DAE.Element}
                  local elts2::List{DAE.Element}
                  local elts::List{DAE.Element}
                   #=  just append lists
                   =#
                @match (dae1, dae2) begin
                  (DAE.DAE(elts1), DAE.DAE(elts2))  => begin
                      elts = listAppend(elts1, elts2)
                    DAE.DAE(elts)
                  end
                end
              end
               #=  t1 = clock();
               =#
               #=  t2 = clock();
               =#
               #=  ti = t2 -. t1;
               =#
               #=  fprintln(Flags.INNER_OUTER, \" joinDAEs: (\" + realString(ti) + \") -> \" + intString(listLength(elts1)) + \" + \" +  intString(listLength(elts2)));
               =#
          outDae
        end

         #= joins a list of daes by using joinDaes =#
        function joinDaeLst(idaeLst::List{<:DAE.DAElist}) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local dae::DAE.DAElist
                  local dae1::DAE.DAElist
                  local daeLst::List{DAE.DAElist}
                @matchcontinue idaeLst begin
                  dae <|  nil()  => begin
                    dae
                  end

                  dae <| daeLst  => begin
                      dae1 = joinDaeLst(daeLst)
                      dae = joinDaes(dae, dae1)
                    dae
                  end
                end
              end
          outDae
        end

         #= This functions splits DAE elements into multiple groups. =#
        function splitElements(elements::List{<:DAE.Element}) ::Tuple{List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAE.Element}, List{DAEDump.compWithSplitElements}, List{SCode.Comment}}
              local comments::List{SCode.Comment} = nil
              local stateMachineComps::List{DAEDump.compWithSplitElements} = nil
              local externalObjects::List{DAE.Element} = nil
              local constraints::List{DAE.Element} = nil
              local classAttributes::List{DAE.Element} = nil
              local algorithms::List{DAE.Element} = nil
              local equations::List{DAE.Element} = nil
              local initialAlgorithms::List{DAE.Element} = nil
              local initialEquations::List{DAE.Element} = nil
              local variables::List{DAE.Element} = nil

              local split_comp::DAEDump.compWithSplitElements

              for e in elements
                _ = begin
                  @match e begin
                    DAE.VAR(__)  => begin
                        variables = _cons(e, variables)
                      ()
                    end

                    DAE.INITIALEQUATION(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_ARRAY_EQUATION(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_COMPLEX_EQUATION(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIALDEFINE(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_IF_EQUATION(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_ASSERT(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_TERMINATE(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIAL_NORETCALL(__)  => begin
                        initialEquations = _cons(e, initialEquations)
                      ()
                    end

                    DAE.INITIALALGORITHM(__)  => begin
                        initialAlgorithms = _cons(e, initialAlgorithms)
                      ()
                    end

                    DAE.EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.EQUEQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.ARRAY_EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.COMPLEX_EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.DEFINE(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.ASSERT(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.TERMINATE(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.IF_EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.FOR_EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.WHEN_EQUATION(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.REINIT(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.NORETCALL(__)  => begin
                        equations = _cons(e, equations)
                      ()
                    end

                    DAE.ALGORITHM(__)  => begin
                        algorithms = _cons(e, algorithms)
                      ()
                    end

                    DAE.CONSTRAINT(__)  => begin
                        constraints = _cons(e, constraints)
                      ()
                    end

                    DAE.CLASS_ATTRIBUTES(__)  => begin
                        classAttributes = _cons(e, classAttributes)
                      ()
                    end

                    DAE.EXTOBJECTCLASS(__)  => begin
                        externalObjects = _cons(e, externalObjects)
                      ()
                    end

                    DAE.COMP(__)  => begin
                        variables = listAppend(e.dAElist, variables)
                      ()
                    end

                    DAE.FLAT_SM(__)  => begin
                        split_comp = splitComponent(DAE.COMP(e.ident, e.dAElist, DAE.emptyElementSource, SOME(SCode.COMMENT(NONE(), SOME("stateMachine")))))
                        stateMachineComps = _cons(split_comp, stateMachineComps)
                      ()
                    end

                    DAE.SM_COMP(__)  => begin
                        split_comp = splitComponent(DAE.COMP(ComponentReference.crefStr(e.componentRef), e.dAElist, DAE.emptyElementSource, SOME(SCode.COMMENT(NONE(), SOME("state")))))
                        stateMachineComps = _cons(split_comp, stateMachineComps)
                      ()
                    end

                    DAE.COMMENT(__)  => begin
                        comments = _cons(e.cmt, comments)
                      ()
                    end

                    _  => begin
                          Error.addInternalError("DAEUtil.splitElements got unknown element.", AbsynUtil.dummyInfo)
                        fail()
                    end
                  end
                end
              end
              variables = listReverse(variables)
              initialEquations = listReverse(initialEquations)
              initialAlgorithms = listReverse(initialAlgorithms)
              equations = listReverse(equations)
              algorithms = listReverse(algorithms)
              classAttributes = listReverse(classAttributes)
              constraints = listReverse(constraints)
              externalObjects = listReverse(externalObjects)
              stateMachineComps = listReverse(stateMachineComps)
          (variables, initialEquations, initialAlgorithms, equations, algorithms, classAttributes, constraints, externalObjects, stateMachineComps, comments)
        end

         #= Transforms a DAE.COMP to a DAEDump.COMP_WITH_SPLIT. =#
        function splitComponent(component::DAE.Element) ::DAEDump.compWithSplitElements
              local splitComponent::DAEDump.compWithSplitElements

              local v::List{DAE.Element}
              local ie::List{DAE.Element}
              local ia::List{DAE.Element}
              local e::List{DAE.Element}
              local a::List{DAE.Element}
              local co::List{DAE.Element}
              local o::List{DAE.Element}
              local ca::List{DAE.Element}
              local sm::List{DAEDump.compWithSplitElements}

              local split_el::DAEDump.splitElements

              splitComponent = begin
                @match component begin
                  DAE.COMP(__)  => begin
                      (v, ie, ia, e, a, co, o, ca, sm) = splitElements(component.dAElist)
                      split_el = DAEDump.SPLIT_ELEMENTS(v, ie, ia, e, a, co, o, ca, sm)
                    DAEDump.COMP_WITH_SPLIT(component.ident, split_el, component.comment)
                  end
                end
              end
          splitComponent
        end

         #= Succeeds if Element is an if-equation.
         =#
        function isIfEquation(inElement::DAE.Element)
              _ = begin
                @match inElement begin
                  DAE.IF_EQUATION(__)  => begin
                    ()
                  end

                  DAE.INITIAL_IF_EQUATION(__)  => begin
                    ()
                  end
                end
              end
        end

         #= Used to traverse expressions and collect all local declarations =#
        function collectLocalDecls(e::DAE.Exp, inElements::List{<:DAE.Element}) ::Tuple{DAE.Exp, List{DAE.Element}}
              local outElements::List{DAE.Element}
              local outExp::DAE.Exp

              (outExp, outElements) = begin
                  local ld1::List{DAE.Element}
                  local ld2::List{DAE.Element}
                  local ld::List{DAE.Element}
                @match (e, inElements) begin
                  (DAE.MATCHEXPRESSION(localDecls = ld1), ld2)  => begin
                      ld = listAppend(ld1, ld2)
                    (e, ld)
                  end

                  _  => begin
                      (e, inElements)
                  end
                end
              end
          (outExp, outElements)
        end

         #= Traverses DAE elements to find all Uniontypes, and return the paths
        of all of their records. This list contains duplicates; handle that in
        the other function. =#
        function getUniontypePaths(funcs::List{<:DAE.Function}, els::List{<:DAE.Element}) ::List{Absyn.Path}
              local outPaths::List{Absyn.Path}

              local paths1::List{Absyn.Path}
              local paths2::List{Absyn.Path}

              outPaths = begin
                @matchcontinue (funcs, els) begin
                  (_, _)  => begin
                      @match false = Config.acceptMetaModelicaGrammar()
                    nil
                  end

                  _  => begin
                        paths1 = getUniontypePathsFunctions(funcs)
                        paths2 = getUniontypePathsElements(els, nil)
                        outPaths = listAppend(paths1, paths2)
                      outPaths
                  end
                end
              end
               #=  Use accumulators? Small gain as T_METAUNIONTYPE has lists of paths anyway?
               =#
          outPaths
        end

         #= May contain duplicates. =#
        function getUniontypePathsFunctions(elements::List{<:DAE.Function}) ::List{Absyn.Path}
              local outPaths::List{Absyn.Path}

              outPaths = begin
                  local els::List{DAE.Element}
                  local els1::List{DAE.Element}
                  local els2::List{DAE.Element}
                @match elements begin
                  _  => begin
                      (_, (_, els1)) = traverseDAEFunctions(elements, Expression.traverseSubexpressionsHelper, (collectLocalDecls, nil))
                      els2 = getFunctionsElements(elements)
                      els = listAppend(els1, els2)
                      outPaths = getUniontypePathsElements(els, nil)
                    outPaths
                  end
                end
              end
          outPaths
        end

         #= May contain duplicates. =#
        function getUniontypePathsElements(elements::List{<:DAE.Element}, acc::List{<:DAE.Type}) ::List{Absyn.Path}
              local outPaths::List{Absyn.Path}

              outPaths = begin
                  local paths1::List{Absyn.Path}
                  local rest::List{DAE.Element}
                  local tys::List{DAE.Type}
                  local ft::DAE.Type
                @match (elements, acc) begin
                  ( nil(), _)  => begin
                    ListUtil.applyAndFold(acc, listAppend, Types.getUniontypePaths, nil)
                  end

                  (DAE.VAR(ty = ft) <| rest, _)  => begin
                      tys = Types.getAllInnerTypesOfType(ft, Types.uniontypeFilter)
                    getUniontypePathsElements(rest, listAppend(tys, acc))
                  end

                  (_ <| rest, _)  => begin
                    getUniontypePathsElements(rest, acc)
                  end
                end
              end
          outPaths
        end

        function getDAEDeclsFromValueblocks(exps::List{<:DAE.Exp}) ::List{DAE.Element}
              local outEls::List{DAE.Element} = nil

              for ex in exps
                _ = begin
                    local els1::List{DAE.Element}
                  @match ex begin
                    DAE.MATCHEXPRESSION(localDecls = els1)  => begin
                        outEls = ListUtil.append_reverse(els1, outEls)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
              outEls = MetaModelica.Dangerous.listReverseInPlace(outEls)
          outEls
        end

         #=  protected function transformDerInline \"This is not used.
         =#
         #=    Simple euler inline of the equation system; only does explicit euler, and only der(cref)\"
         =#
         #=    input DAE.DAElist dae;
         =#
         #=    output DAE.DAElist d;
         =#
         #=  algorithm
         =#
         #=    d := matchcontinue (dae)
         =#
         #=      local
         =#
         #=        HashTable.HashTable ht;
         =#
         #=      case _
         =#
         #=        equation
         =#
         #=          false = Flags.isSet(Flags.FRONTEND_INLINE_EULER);
         =#
         #=        then dae;
         =#
         #=      case _
         =#
         #=        equation
         =#
         #=          ht = HashTable.emptyHashTable();
         =#
         #=          (d,_,ht) = traverseDAE(dae,DAE.AvlTreePathFunction.Tree.EMPTY(),simpleInlineDerEuler,ht);
         =#
         #=        then d;
         =#
         #=    end matchcontinue;
         =#
         #=  end transformDerInline;
         =#
         #=
         =#
         #=  protected function simpleInlineDerEuler \"This is not used.
         =#
         #=    Helper function of transformDerInline.\"
         =#
         #=    input tuple<DAE.Exp,HashTable.HashTable> itpl;
         =#
         #=    output tuple<DAE.Exp,HashTable.HashTable> otpl;
         =#
         #=  algorithm
         =#
         #=    otpl := matchcontinue (itpl)
         =#
         #=      local
         =#
         #=        DAE.ComponentRef cr,cref_1,cref_2;
         =#
         #=        HashTable.HashTable crs0,crs1;
         =#
         #=        DAE.Exp exp,e1,e2;
         =#
         #=
         =#
         #=      case ((DAE.CALL(path=Absyn.IDENT(\"der\"),expLst={exp as DAE.CREF(componentRef = cr, ty = DAE.T_REAL(varLst = _))}),crs0))
         =#
         #=        equation
         =#
         #=          cref_1 = ComponentReference.makeCrefQual(\"$old\",DAE.T_REAL_DEFAULT,{},cr);
         =#
         #=          cref_2 = ComponentReference.makeCrefIdent(\"$current_step_size\",DAE.T_REAL_DEFAULT,{});
         =#
         #=          e1 = Expression.makeCrefExp(cref_1,DAE.T_REAL_DEFAULT);
         =#
         #=          e2 = Expression.makeCrefExp(cref_2,DAE.T_REAL_DEFAULT);
         =#
         #=          exp = DAE.BINARY(
         =#
         #=                  DAE.BINARY(exp, DAE.SUB(DAE.T_REAL_DEFAULT), e1),
         =#
         #=                  DAE.DIV(DAE.T_REAL_DEFAULT),
         =#
         #=                  e2);
         =#
         #=          crs1 = BaseHashTable.add((cr,0),crs0);
         =#
         #=        then
         =#
         #=          ((exp,crs1));
         =#
         #=
         =#
         #=      case ((exp,crs0)) then ((exp,crs0));
         =#
         #=
         =#
         #=    end matchcontinue;
         =#
         #=  end simpleInlineDerEuler;
         =#

        function transformationsBeforeBackend(cache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist) ::DAE.DAElist
              local outDAElist::DAE.DAElist

              local dAElist::DAE.DAElist
              local elts::List{DAE.Element}
              local ht::AvlSetCR.Tree

               #=  Transform Modelica state machines to flat data-flow equations
               =#
              dAElist = StateMachineFlatten.stateMachineToDataFlow(cache, env, inDAElist)
              if Flags.isSet(Flags.SCODE_INST)
                @match DAE.DAE(elts) = dAElist
                outDAElist = DAE.DAE(elts)
              else
                @match DAE.DAE(elts) = dAElist
                ht = FCore.getEvaluatedParams(cache)
                elts = ListUtil.map1(elts, makeEvaluatedParamFinal, ht)
                if Flags.isSet(Flags.PRINT_STRUCTURAL)
                  transformationsBeforeBackendNotification(ht)
                end
                outDAElist = DAE.DAE(elts)
              end
               #=  This is stupid, but `outDAElist := dAElist` causes crashes for some reason. GC bug?
               =#
               #=  Don't even run the function to try and do this; it doesn't work very well
               =#
               #=  outDAElist := transformDerInline(outDAElist);
               =#
          outDAElist
        end

        function transformationsBeforeBackendNotification(ht::AvlSetCR.Tree)
              local crs::List{DAE.ComponentRef}
              local strs::List{String}
              local str::String

              crs = AvlSetCR.listKeys(ht)
              if ! listEmpty(crs)
                strs = ListUtil.map(crs, ComponentReference.printComponentRefStr)
                str = stringDelimitList(strs, ", ")
                Error.addMessage(Error.NOTIFY_FRONTEND_STRUCTURAL_PARAMETERS, list(str))
              end
        end

         #=
          This function makes all evaluated parameters final. =#
        function makeEvaluatedParamFinal(inElement::DAE.Element, ht::AvlSetCR.Tree #= evaluated parameters =#) ::DAE.Element
              local outElement::DAE.Element

              outElement = begin
                  local cr::DAE.ComponentRef
                  local varOpt::Option{DAE.VariableAttributes}
                  local id::String
                  local elts::List{DAE.Element}
                  local source::DAE.ElementSource
                  local cmt::Option{SCode.Comment}
                  local elt::DAE.Element
                @match (inElement, ht) begin
                  (DAE.VAR(componentRef = cr, kind = DAE.PARAM(__), variableAttributesOption = varOpt), _)  => begin
                      elt = if AvlSetCR.hasKey(ht, cr)
                            setVariableAttributes(inElement, setFinalAttr(varOpt, true))
                          else
                            inElement
                          end
                    elt
                  end

                  (DAE.COMP(id, elts, source, cmt), _)  => begin
                      elts = ListUtil.map1(elts, makeEvaluatedParamFinal, ht)
                    DAE.COMP(id, elts, source, cmt)
                  end

                  _  => begin
                      inElement
                  end
                end
              end
          outElement
        end

         #= author: adrpo
          This function will set the source of the binding =#
        function setBindingSource(inBinding::DAE.Binding, bindingSource::DAE.BindingSource) ::DAE.Binding
              local outBinding::DAE.Binding

              outBinding = begin
                  local exp::DAE.Exp #= exp =#
                  local evaluatedExp::Option{Values.Value} #= evaluatedExp; evaluated exp =#
                  local cnst::DAE.Const #= constant =#
                  local valBound::Values.Value
                @match (inBinding, bindingSource) begin
                  (DAE.UNBOUND(__), _)  => begin
                    inBinding
                  end

                  (DAE.EQBOUND(exp, evaluatedExp, cnst, _), _)  => begin
                    DAE.EQBOUND(exp, evaluatedExp, cnst, bindingSource)
                  end

                  (DAE.VALBOUND(valBound, _), _)  => begin
                    DAE.VALBOUND(valBound, bindingSource)
                  end
                end
              end
          outBinding
        end

         #= prints a binding =#
        function printBindingExpStr(binding::DAE.Binding) ::String
              local str::String

              str = begin
                  local e::DAE.Exp
                  local v::Values.Value
                @match binding begin
                  DAE.UNBOUND(__)  => begin
                    ""
                  end

                  DAE.EQBOUND(exp = e)  => begin
                      str = ExpressionDump.printExpStr(e)
                    str
                  end

                  DAE.VALBOUND(valBound = v)  => begin
                      str = " = " + ValuesUtil.valString(v)
                    str
                  end
                end
              end
          str
        end

         #= prints a binding source as a string =#
        function printBindingSourceStr(bindingSource::DAE.BindingSource) ::String
              local str::String

              str = begin
                @match bindingSource begin
                  DAE.BINDING_FROM_DEFAULT_VALUE(__)  => begin
                    "[DEFAULT VALUE]"
                  end

                  DAE.BINDING_FROM_START_VALUE(__)  => begin
                    "[START VALUE]"
                  end
                end
              end
          str
        end

         #= Collect the function names of variables in valueblock local sections =#
        function collectValueblockFunctionRefVars(exp::DAE.Exp, acc::List{<:Absyn.Path}) ::Tuple{DAE.Exp, List{Absyn.Path}}
              local outAcc::List{Absyn.Path}
              local outExp::DAE.Exp

              (outExp, outAcc) = begin
                  local decls::List{DAE.Element}
                @match (exp, acc) begin
                  (DAE.MATCHEXPRESSION(localDecls = decls), _)  => begin
                      outAcc = ListUtil.fold(decls, collectFunctionRefVarPaths, acc)
                    (exp, outAcc)
                  end

                  _  => begin
                      (exp, acc)
                  end
                end
              end
          (outExp, outAcc)
        end

         #= Collect the function names of declared variables =#
        function collectFunctionRefVarPaths(inElem::DAE.Element, acc::List{<:Absyn.Path}) ::List{Absyn.Path}
              local outAcc::List{Absyn.Path}

              outAcc = begin
                  local path::Absyn.Path
                @match inElem begin
                  DAE.VAR(ty = DAE.T_FUNCTION(path = path))  => begin
                    _cons(path, acc)
                  end

                  _  => begin
                      acc
                  end
                end
              end
          outAcc
        end

         #= add functions present in the element list to the function tree =#
        function addDaeFunction(functions::List{<:DAE.Function}, functionTree::DAE.FunctionTree) ::DAE.FunctionTree
              for f in functions
                functionTree = DAE.AvlTreePathFunction.add(functionTree, functionName(f), SOME(f))
              end
          functionTree
        end

         #= adds a functionDefinition to a function. can be used to add function_der_mapper to a function =#
        function addFunctionDefinition(ifunc::DAE.Function, iFuncDef::DAE.FunctionDefinition) ::DAE.Function
              local func::DAE.Function = ifunc

              _ = begin
                @match func begin
                  DAE.FUNCTION(__)  => begin
                      func.functions = ListUtil.appendElt(iFuncDef, func.functions)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
          func
        end

         #=
          add extermal functions present in the element list to the function tree
          Note: normal functions are skipped.
          See also addDaeFunction =#
        function addDaeExtFunction(ifuncs::List{<:DAE.Function}, itree::DAE.FunctionTree) ::DAE.FunctionTree
              local outTree::DAE.FunctionTree

              outTree = begin
                  local func::DAE.Function
                  local funcs::List{DAE.Function}
                  local tree::DAE.FunctionTree
                  local msg::String
                @matchcontinue (ifuncs, itree) begin
                  ( nil(), tree)  => begin
                    tree
                  end

                  (func <| funcs, tree)  => begin
                      @match true = isExtFunction(func)
                      tree = DAE.AvlTreePathFunction.add(tree, functionName(func), SOME(func))
                    addDaeExtFunction(funcs, tree)
                  end

                  (_ <| funcs, tree)  => begin
                    addDaeExtFunction(funcs, tree)
                  end
                end
              end
               #= showCacheFuncs(tree);
               =#
               #=  print(\"Add ext to cache: \" + AbsynUtil.pathString(functionName(func)) + \"\\n\");
               =#
          outTree
        end

        function getFunctionsInfo(ft::DAE.FunctionTree) ::List{String}
              local strs::List{String}

              strs = begin
                  local lst::List{Tuple{DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}}
                @match ft begin
                  _  => begin
                      lst = DAE.AvlTreePathFunction.toList(ft)
                      strs = ListUtil.map(lst, getInfo)
                      strs = ListUtil.sort(strs, Util.strcmpBool)
                    strs
                  end
                end
              end
          strs
        end

        function getInfo(tpl::Tuple{<:DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}) ::String
              local str::String

              str = begin
                  local p::Absyn.Path
                @match tpl begin
                  (p, NONE())  => begin
                      str = AbsynUtil.pathString(p) + " [invalid]"
                    str
                  end

                  (p, SOME(_))  => begin
                      str = AbsynUtil.pathString(p) + " [valid]  "
                    str
                  end
                end
              end
          str
        end

        function showCacheFuncs(tree::DAE.FunctionTree)
              _ = begin
                  local msg::String
                @match tree begin
                  _  => begin
                      msg = stringDelimitList(getFunctionsInfo(tree), "\\n  ")
                      print("Cache has: \\n  " + msg + "\\n")
                    ()
                  end
                end
              end
        end

         #=
          Sets the variability attribute in an Attributes record. =#
        function setAttrVariability(attr::DAE.Attributes, var::SCode.Variability) ::DAE.Attributes


              attr.variability = var
          attr
        end

         #=
          Get the variability attribute in an Attributes record. =#
        function getAttrVariability(attr::DAE.Attributes) ::SCode.Variability
              local var::SCode.Variability = attr.variability
          var
        end

         #= Sets the direction attribute in an Attributes record. =#
        function setAttrDirection(attr::DAE.Attributes, dir::Absyn.Direction) ::DAE.Attributes


              attr.direction = dir
          attr
        end

        function getAttrDirection(attr::DAE.Attributes) ::Absyn.Direction
              local dir::Absyn.Direction = attr.direction
          dir
        end

         #= Sets the innerOuter attribute in an Attributes record. =#
        function setAttrInnerOuter(attr::DAE.Attributes, io::Absyn.InnerOuter) ::DAE.Attributes


              attr.innerOuter = io
          attr
        end

        function getAttrInnerOuter(attr::DAE.Attributes) ::Absyn.InnerOuter
              local io::Absyn.InnerOuter = attr.innerOuter
          io
        end

        function translateSCodeAttrToDAEAttr(inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes) ::DAE.Attributes
              local outAttributes::DAE.Attributes

              local ct::SCode.ConnectorType
              local prl::SCode.Parallelism
              local var::SCode.Variability
              local dir::Absyn.Direction
              local io::Absyn.InnerOuter
              local vis::SCode.Visibility

              @match SCode.ATTR(connectorType = ct, parallelism = prl, variability = var, direction = dir) = inAttributes
              @match SCode.PREFIXES(innerOuter = io, visibility = vis) = inPrefixes
              outAttributes = DAE.ATTR(toConnectorTypeNoState(ct), prl, var, dir, io, vis)
          outAttributes
        end

        function varName(var::DAE.Element) ::String
              local name::String

              @match DAE.VAR(componentRef = DAE.CREF_IDENT(ident = name)) = var
          name
        end

        function typeVarIdent(var::DAE.Var) ::DAE.Ident
              local name::DAE.Ident

              @match DAE.TYPES_VAR(name = name) = var
          name
        end

        function typeVarIdentEqual(var::DAE.Var, name::String) ::Bool
              local b::Bool

              local name2::String

              @match DAE.TYPES_VAR(name = name2) = var
              b = stringEq(name, name2)
          b
        end

        function varType(var::DAE.Var) ::DAE.Type
              local type_::DAE.Type

              @match DAE.TYPES_VAR(ty = type_) = var
          type_
        end

         #=
          help function to instBinding, returns the expression of a binding =#
        function bindingExp(bind::DAE.Binding) ::Option{DAE.Exp}
              local exp::Option{DAE.Exp}

              exp = begin
                  local e::DAE.Exp
                  local v::Values.Value
                @match bind begin
                  DAE.UNBOUND(__)  => begin
                    NONE()
                  end

                  DAE.EQBOUND(evaluatedExp = SOME(v))  => begin
                      e = ValuesUtil.valueExp(v)
                    SOME(e)
                  end

                  DAE.EQBOUND(exp = e)  => begin
                    SOME(e)
                  end

                  DAE.VALBOUND(valBound = v)  => begin
                      e = ValuesUtil.valueExp(v)
                    SOME(e)
                  end
                end
              end
          exp
        end

        function isBound(inBinding::DAE.Binding) ::Bool
              local outIsBound::Bool

              outIsBound = begin
                @match inBinding begin
                  DAE.UNBOUND(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outIsBound
        end

         #= author: adrpo
          this function returns true if the given function is complete:
          - has inputs
          - has outputs
          - has an algorithm section
          note that record constructors are always considered complete =#
        function isCompleteFunction(f::DAE.Function) ::Bool
              local isComplete::Bool

              isComplete = begin
                  local functions::List{DAE.FunctionDefinition}
                   #=  record constructors are always complete!
                   =#
                @match f begin
                  DAE.RECORD_CONSTRUCTOR(__)  => begin
                    true
                  end

                  DAE.FUNCTION(functions = functions)  => begin
                    isCompleteFunctionBody(functions)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  functions are complete if they have inputs, outputs and algorithm section
               =#
          isComplete
        end

         #= author: adrpo
          this function returns true if the given function body is complete =#
        function isCompleteFunctionBody(functions::List{<:DAE.FunctionDefinition}) ::Bool
              local isComplete::Bool

              isComplete = begin
                  local rest::List{DAE.FunctionDefinition}
                  local els::List{DAE.Element}
                  local v::List{DAE.Element}
                  local ie::List{DAE.Element}
                  local ia::List{DAE.Element}
                  local e::List{DAE.Element}
                  local a::List{DAE.Element}
                  local o::List{DAE.Element}
                  local ca::List{DAE.Element}
                  local co::List{DAE.Element}
                @matchcontinue functions begin
                   nil()  => begin
                    false
                  end

                  DAE.FUNCTION_EXT(__) <| _  => begin
                    true
                  end

                  DAE.FUNCTION_DEF(els) <| _  => begin
                      (_, _, _, _, a, _, _, _) = splitElements(els)
                      @match false = listEmpty(a)
                    true
                  end

                  DAE.FUNCTION_DER_MAPPER(__) <| rest  => begin
                    isCompleteFunctionBody(rest)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  external are complete!
               =#
               #=  functions are complete if they have inputs, outputs and algorithm section
               =#
               #=  algs are not empty
               =#
          isComplete
        end

        function isNotCompleteFunction(f::DAE.Function) ::Bool
              local isNotComplete::Bool

              isNotComplete = ! isCompleteFunction(f)
          isNotComplete
        end

        function setAttributeDirection(inDirection::Absyn.Direction, inAttributes::DAE.Attributes) ::DAE.Attributes
              local outAttributes::DAE.Attributes

              local ct::DAE.ConnectorType
              local p::SCode.Parallelism
              local var::SCode.Variability
              local io::Absyn.InnerOuter
              local vis::SCode.Visibility

              @match DAE.ATTR(ct, p, var, _, io, vis) = inAttributes
              outAttributes = DAE.ATTR(ct, p, var, inDirection, io, vis)
          outAttributes
        end

        function varKindEqual(inVariability1::DAE.VarKind, inVariability2::DAE.VarKind) ::Bool
              local outIsEqual::Bool

              outIsEqual = begin
                @match (inVariability1, inVariability2) begin
                  (DAE.VARIABLE(__), DAE.VARIABLE(__))  => begin
                    true
                  end

                  (DAE.DISCRETE(__), DAE.DISCRETE(__))  => begin
                    true
                  end

                  (DAE.CONST(__), DAE.CONST(__))  => begin
                    true
                  end

                  (DAE.PARAM(__), DAE.PARAM(__))  => begin
                    true
                  end
                end
              end
          outIsEqual
        end

        function varDirectionEqual(inDirection1::DAE.VarDirection, inDirection2::DAE.VarDirection) ::Bool
              local outIsEqual::Bool

              outIsEqual = begin
                @match (inDirection1, inDirection2) begin
                  (DAE.BIDIR(__), DAE.BIDIR(__))  => begin
                    true
                  end

                  (DAE.INPUT(__), DAE.INPUT(__))  => begin
                    true
                  end

                  (DAE.OUTPUT(__), DAE.OUTPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsEqual
        end

        function isComplexVar(inVar::DAE.Var) ::Bool
              local outIsComplex::Bool

              local ty::DAE.Type

              @match DAE.TYPES_VAR(ty = ty) = inVar
              outIsComplex = Types.isComplexType(ty)
          outIsComplex
        end

        function getElements(inDAE::DAE.DAElist) ::List{DAE.Element}
              local outElements::List{DAE.Element}

              @match DAE.DAE(outElements) = inDAE
          outElements
        end

        function mkEmptyVar(name::String) ::DAE.Var
              local outVar::DAE.Var

              outVar = DAE.TYPES_VAR(name, DAE.dummyAttrVar, DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE())
          outVar
        end

         #= @author: adrpo
         sort the DAE back in the order they are in the file =#
        function sortDAEInModelicaCodeOrder(inShouldSort::Bool, inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inDae::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local els::List{DAE.Element}
                @match (inShouldSort, inElements, inDae) begin
                  (false, _, _)  => begin
                    inDae
                  end

                  (true,  nil(), _)  => begin
                    inDae
                  end

                  (true, _, DAE.DAE(els))  => begin
                      els = sortDAEElementsInModelicaCodeOrder(inElements, els)
                    DAE.DAE(els)
                  end
                end
              end
          outDae
        end

         #= @author: adrpo
         sort the DAE elements back in the order they are in the file =#
        function sortDAEElementsInModelicaCodeOrder(inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inDaeEls::List{<:DAE.Element}) ::List{DAE.Element}
              local outDaeEls::List{DAE.Element} = nil

              local rest::List{DAE.Element} = inDaeEls

              for e in inElements
                _ = begin
                    local named::List{DAE.Element}
                    local name::Absyn.Ident
                  @match e begin
                    (SCode.COMPONENT(name = name), _)  => begin
                        (named, rest) = splitVariableNamed(rest, name, nil, nil)
                        outDaeEls = ListUtil.append_reverse(named, outDaeEls)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
              outDaeEls = ListUtil.append_reverse(inDaeEls, outDaeEls)
              outDaeEls = MetaModelica.Dangerous.listReverseInPlace(outDaeEls)
          outDaeEls
        end

         #= @author: adrpo
          Splits into a list with all variables with the given name and the rest =#
        function splitVariableNamed(inElementLst::List{<:DAE.Element}, inName::Absyn.Ident, inAccNamed::List{<:DAE.Element}, inAccRest::List{<:DAE.Element}) ::Tuple{List{DAE.Element}, List{DAE.Element}}
              local outRest::List{DAE.Element}
              local outNamed::List{DAE.Element}

              (outNamed, outRest) = begin
                  local res::List{DAE.Element}
                  local lst::List{DAE.Element}
                  local accNamed::List{DAE.Element}
                  local accRest::List{DAE.Element}
                  local x::DAE.Element
                  local equal::Bool
                  local cr::DAE.ComponentRef
                @match (inElementLst, inName, inAccNamed, inAccRest) begin
                  ( nil(), _, _, _)  => begin
                    (listReverse(inAccNamed), listReverse(inAccRest))
                  end

                  (x && DAE.VAR(componentRef = cr) <| lst, _, accNamed, accRest)  => begin
                      equal = stringEq(ComponentReference.crefFirstIdent(cr), inName)
                      accNamed = ListUtil.consOnTrue(equal, x, accNamed)
                      accRest = ListUtil.consOnTrue(boolNot(equal), x, accRest)
                      (accNamed, accRest) = splitVariableNamed(lst, inName, accNamed, accRest)
                    (accNamed, accRest)
                  end

                  (x <| lst, _, accNamed, accRest)  => begin
                      (accNamed, accRest) = splitVariableNamed(lst, inName, accNamed, _cons(x, accRest))
                    (accNamed, accRest)
                  end
                end
              end
          (outNamed, outRest)
        end

         #= @author: adrpo
         collect all crefs from the DAE =#
        function getAllExpandableCrefsFromDAE(inDAE::DAE.DAElist) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              local elts::List{DAE.Element}

              @match DAE.DAE(elts) = inDAE
              (_, (_, outCrefs)) = traverseDAEElementList(elts, Expression.traverseSubexpressionsHelper, (collectAllExpandableCrefsInExp, nil))
          outCrefs
        end

         #= collect all crefs from expression =#
        function collectAllExpandableCrefsInExp(exp::DAE.Exp, acc::List{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, List{DAE.ComponentRef}}
              local outCrefs::List{DAE.ComponentRef}
              local outExp::DAE.Exp

              (outExp, outCrefs) = begin
                  local cr::DAE.ComponentRef
                @match (exp, acc) begin
                  (DAE.CREF(componentRef = cr), _)  => begin
                    (exp, ListUtil.consOnTrue(ConnectUtil.isExpandable(cr), cr, acc))
                  end

                  _  => begin
                      (exp, acc)
                  end
                end
              end
          (outExp, outCrefs)
        end

        function daeDescription(inDAE::DAE.DAElist) ::String
              local comment::String

              comment = begin
                @match inDAE begin
                  DAE.DAE(elementLst = DAE.COMP(comment = SOME(SCode.COMMENT(comment = SOME(comment)))) <| _)  => begin
                    comment
                  end

                  _  => begin
                      ""
                  end
                end
              end
          comment
        end

         #= replaces the type in the geiven DAE.CALL_ATTR =#
        function replaceCallAttrType(caIn::DAE.CallAttributes, typeIn::DAE.Type) ::DAE.CallAttributes
              local caOut::DAE.CallAttributes

              caOut = caIn
              caOut.ty = typeIn
              if Types.isTuple(typeIn)
                caOut.tuple_ = true
              end
          caOut
        end

        function funcIsRecord(func::DAE.Function) ::Bool
              local isRec::Bool

              isRec = begin
                @match func begin
                  DAE.RECORD_CONSTRUCTOR(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isRec
        end

         #= gets the number of flattened scalars for a FuncArg =#
        function funcArgDim(argIn::DAE.FuncArg) ::ModelicaInteger
              local dim::ModelicaInteger

              dim = begin
                  local ty::DAE.Type
                  local arrayDims::DAE.Dimensions
                  local names::List{String}
                @match argIn begin
                  DAE.FUNCARG(ty = DAE.T_ARRAY(dims = arrayDims))  => begin
                    ListUtil.applyAndFold(arrayDims, intAdd, Expression.dimensionSize, 0)
                  end

                  DAE.FUNCARG(ty = DAE.T_ENUMERATION(names = names))  => begin
                    listLength(names)
                  end

                  _  => begin
                      1
                  end
                end
              end
          dim
        end

        function toDAEInnerOuter(ioIn::Absyn.InnerOuter) ::DAE.VarInnerOuter
              local ioOut::DAE.VarInnerOuter

              ioOut = begin
                @match ioIn begin
                  Absyn.INNER(__)  => begin
                    DAE.INNER()
                  end

                  Absyn.OUTER(__)  => begin
                    DAE.OUTER()
                  end

                  Absyn.INNER_OUTER(__)  => begin
                    DAE.INNER_OUTER()
                  end

                  Absyn.NOT_INNER_OUTER(__)  => begin
                    DAE.NOT_INNER_OUTER()
                  end
                end
              end
          ioOut
        end

         #= gets the crefs of the assert condition.
        author:Waurich 2015-04 =#
        function getAssertConditionCrefs(stmt::DAE.Statement, crefsIn::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local crefsOut::List{DAE.ComponentRef}

              crefsOut = begin
                  local cond::DAE.Exp
                  local crefs::List{DAE.ComponentRef}
                @match (stmt, crefsIn) begin
                  (DAE.STMT_ASSERT(cond = cond), _)  => begin
                      crefs = Expression.extractCrefsFromExp(cond)
                    listAppend(crefsIn, crefs)
                  end

                  _  => begin
                      crefsIn
                  end
                end
              end
          crefsOut
        end

         #= author: marcusw
          Get the index of the given subscript as Integer. If the subscript is not a constant integer, the function returns -1. =#
        function getSubscriptIndex(iSubscript::DAE.Subscript) ::ModelicaInteger
              local oIndex::ModelicaInteger

              local index::ModelicaInteger
              local exp::DAE.Exp

              oIndex = begin
                @match iSubscript begin
                  DAE.INDEX(DAE.ICONST(integer = index))  => begin
                    index
                  end

                  DAE.INDEX(DAE.ENUM_LITERAL(index = index))  => begin
                    index
                  end

                  _  => begin
                      -1
                  end
                end
              end
          oIndex
        end

        function bindingValue(inBinding::DAE.Binding) ::Option{Values.Value}
              local outValue::Option{Values.Value}

              outValue = begin
                @match inBinding begin
                  DAE.EQBOUND(__)  => begin
                    inBinding.evaluatedExp
                  end

                  DAE.VALBOUND(__)  => begin
                    SOME(inBinding.valBound)
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          outValue
        end

        function statementsContainReturn(stmts::List{<:DAE.Statement}) ::Bool
              local b::Bool

              (_, b) = traverseDAEStmts(stmts, statementsContainReturn2, false)
          b
        end

        function statementsContainTryBlock(stmts::List{<:DAE.Statement}) ::Bool
              local b::Bool

              (_, b) = traverseDAEStmts(stmts, statementsContainTryBlock2, false)
          b
        end

        function statementsContainReturn2(inExp::DAE.Exp, inStmt::DAE.Statement, b::Bool) ::Tuple{DAE.Exp, Bool}
              local ob::Bool = b
              local outExp::DAE.Exp = inExp

              if ! b
                ob = begin
                  @match inStmt begin
                    DAE.STMT_RETURN(__)  => begin
                      true
                    end

                    _  => begin
                        begin
                            local cases::List{DAE.MatchCase}
                            local body::List{DAE.Statement}
                          @match inExp begin
                            DAE.MATCHEXPRESSION(cases = cases)  => begin
                                for c in cases
                                  if ! ob
                                    @match DAE.CASE(body = body) = c
                                    ob = statementsContainReturn(body)
                                  end
                                end
                              ob
                            end

                            _  => begin
                                false
                            end
                          end
                        end
                    end
                  end
                end
              end
          (outExp, ob)
        end

        function statementsContainTryBlock2(inExp::DAE.Exp, inStmt::DAE.Statement, b::Bool) ::Tuple{DAE.Exp, Bool}
              local ob::Bool = b
              local outExp::DAE.Exp = inExp

              if ! b
                ob = begin
                  @match inExp begin
                    DAE.MATCHEXPRESSION(matchType = DAE.MATCHCONTINUE(__))  => begin
                      true
                    end

                    _  => begin
                        false
                    end
                  end
                end
              end
          (outExp, ob)
        end

         #=
          Retrive the binding from a list of Elements
          that matches the given cref
         =#
        function getVarBinding(iels::List{<:DAE.Element}, icr::DAE.ComponentRef) ::Option{DAE.Exp}
              local obnd::Option{DAE.Exp}

              local cr::DAE.ComponentRef
              local e::DAE.Exp
              local lst::List{DAE.Element}

              obnd = NONE()
              for i in iels
                obnd = begin
                  @match i begin
                    DAE.VAR(componentRef = cr, binding = obnd)  => begin
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.DEFINE(componentRef = cr, exp = e)  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.INITIALDEFINE(componentRef = cr, exp = e)  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.EQUATION(exp = DAE.CREF(componentRef = cr), scalar = e)  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.EQUATION(exp = e, scalar = DAE.CREF(componentRef = cr))  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.INITIALEQUATION(exp1 = DAE.CREF(componentRef = cr), exp2 = e)  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    DAE.INITIALEQUATION(exp1 = e, exp2 = DAE.CREF(componentRef = cr))  => begin
                        obnd = SOME(e)
                        if ComponentReference.crefEqualNoStringCompare(icr, cr)
                          return
                        end
                      obnd
                    end

                    _  => begin
                        obnd
                    end
                  end
                end
              end
          obnd
        end

         #= pour man's constant evaluation =#
        function evaluateCref(icr::DAE.ComponentRef, iels::List{<:DAE.Element}) ::Option{DAE.Exp}
              local oexp::Option{DAE.Exp}

              local e::DAE.Exp
              local ee::DAE.Exp
              local crefs::List{DAE.ComponentRef}
              local oexps::List{Option{DAE.Exp}}
              local o::Option{DAE.Exp}

              oexp = getVarBinding(iels, icr)
              if isSome(oexp)
                @match SOME(e) = oexp
                (e, _) = ExpressionSimplify.simplify(e)
                if Expression.isConst(e)
                  oexp = SOME(e)
                  return oexp
                end
                crefs = Expression.getAllCrefs(e)
                oexps = ListUtil.map1(crefs, evaluateCref, iels)
                for c in crefs
                  @match _cons(SOME(ee), oexps) = oexps
                  e = Expression.replaceCref(e, (c, ee))
                  (e, _) = ExpressionSimplify.simplify(e)
                end
                oexp = SOME(e)
              end
               #=  is constant
               =#
               #=  not constant
               =#
          oexp
        end

         #= pour man's constant evaluation =#
        function evaluateExp(iexp::DAE.Exp, iels::List{<:DAE.Element}) ::Option{DAE.Exp}
              local oexp::Option{DAE.Exp} = NONE()

              local e::DAE.Exp
              local ee::DAE.Exp
              local crefs::List{DAE.ComponentRef}
              local oexps::List{Option{DAE.Exp}}
              local o::Option{DAE.Exp}

               #=  is constant
               =#
              if Expression.isConst(iexp)
                oexp = SOME(iexp)
                return oexp
              end
               #=  not constant
               =#
              try
                e = iexp
                crefs = Expression.getAllCrefs(e)
                oexps = ListUtil.map1(crefs, evaluateCref, iels)
                for c in crefs
                  @match _cons(SOME(ee), oexps) = oexps
                  e = Expression.replaceCrefBottomUp(e, c, ee)
                  (e, _) = ExpressionSimplify.simplify(e)
                end
                oexp = SOME(e)
              catch
                oexp = NONE()
              end
          oexp
        end

        function replaceCrefInDAEElements(inElements::List{<:DAE.Element}, inCref::DAE.ComponentRef, inExp::DAE.Exp) ::List{DAE.Element}
              local outElements::List{DAE.Element}

              local repl::VarTransform.VariableReplacements

              repl = VarTransform.emptyReplacements()
              repl = VarTransform.addReplacement(repl, inCref, inExp)
              (outElements, _) = traverseDAEElementList(inElements, replaceCrefBottomUp, repl)
          outElements
        end

        function replaceCrefBottomUp(inExp::DAE.Exp, replIn::VarTransform.VariableReplacements) ::Tuple{DAE.Exp, VarTransform.VariableReplacements}
              local replOut::VarTransform.VariableReplacements
              local outExp::DAE.Exp

              replOut = replIn
              (outExp, _) = Expression.traverseExpBottomUp(inExp, replaceCompRef, replIn)
          (outExp, replOut)
        end

        function replaceCompRef(inExp::DAE.Exp, replIn::VarTransform.VariableReplacements) ::Tuple{DAE.Exp, VarTransform.VariableReplacements}
              local replOut::VarTransform.VariableReplacements
              local outExp::DAE.Exp

              replOut = replIn
              (outExp, _) = VarTransform.replaceExp(inExp, replIn, NONE())
          (outExp, replOut)
        end

        function connectorTypeStr(connectorType::DAE.ConnectorType) ::String
              local string::String

              string = begin
                  local cref::DAE.ComponentRef
                  local cref_str::String
                @match connectorType begin
                  DAE.POTENTIAL(__)  => begin
                    ""
                  end

                  DAE.FLOW(__)  => begin
                    "flow"
                  end

                  DAE.STREAM(NONE())  => begin
                    "stream()"
                  end

                  DAE.STREAM(SOME(cref))  => begin
                      cref_str = ComponentReference.printComponentRefStr(cref)
                    "stream(" + cref_str + ")"
                  end

                  _  => begin
                      "non connector"
                  end
                end
              end
          string
        end

        function streamBool(inStream::DAE.ConnectorType) ::Bool
              local bStream::Bool

              bStream = begin
                @match inStream begin
                  DAE.STREAM(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          bStream
        end

        function potentialBool(inConnectorType::DAE.ConnectorType) ::Bool
              local outPotential::Bool

              outPotential = begin
                @match inConnectorType begin
                  DAE.POTENTIAL(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outPotential
        end

        function connectorTypeEqual(inConnectorType1::DAE.ConnectorType, inConnectorType2::DAE.ConnectorType) ::Bool
              local outEqual::Bool

              outEqual = begin
                @match (inConnectorType1, inConnectorType2) begin
                  (DAE.POTENTIAL(__), DAE.POTENTIAL(__))  => begin
                    true
                  end

                  (DAE.FLOW(__), DAE.FLOW(__))  => begin
                    true
                  end

                  (DAE.STREAM(_), DAE.STREAM(_))  => begin
                    true
                  end

                  (DAE.NON_CONNECTOR(__), DAE.NON_CONNECTOR(__))  => begin
                    true
                  end
                end
              end
          outEqual
        end

        function toSCodeConnectorType(daeConnectorType::DAE.ConnectorType) ::SCode.ConnectorType
              local scodeConnectorType::SCode.ConnectorType

              scodeConnectorType = begin
                @match daeConnectorType begin
                  DAE.FLOW(__)  => begin
                    SCode.FLOW()
                  end

                  DAE.STREAM(_)  => begin
                    SCode.STREAM()
                  end

                  DAE.POTENTIAL(__)  => begin
                    SCode.POTENTIAL()
                  end

                  DAE.NON_CONNECTOR(__)  => begin
                    SCode.POTENTIAL()
                  end
                end
              end
          scodeConnectorType
        end

         #= @author: adrpo
         experimental merging of all algorithm sections into:
         - one for initial algorithms
         - one for normal algorithms
         - only happens on a flag (-d=mergeAlgSections) =#
        function mergeAlgorithmSections(inDae::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              local els::List{DAE.Element}
              local newEls::List{DAE.Element} = nil
              local dAElist::List{DAE.Element}
              local istmts::List{DAE.Statement} = nil
              local stmts::List{DAE.Statement} = nil
              local s::List{DAE.Statement}
              local source::DAE.ElementSource
              local src::DAE.ElementSource
              local ident::DAE.Ident
              local comment::Option{SCode.Comment}

               #=  do nothing if the flag is not activated
               =#
              if ! Flags.isSet(Flags.MERGE_ALGORITHM_SECTIONS)
                outDae = inDae
                return outDae
              end
              @match DAE.DAE(els) = inDae
              for e in els
                _ = begin
                  @match e begin
                    DAE.COMP(ident, dAElist, src, comment)  => begin
                        @match DAE.DAE(dAElist) = mergeAlgorithmSections(DAE.DAE(dAElist))
                        newEls = _cons(DAE.COMP(ident, dAElist, src, comment), newEls)
                      ()
                    end

                    DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(s), source = source)  => begin
                        stmts = listAppend(stmts, s)
                      ()
                    end

                    DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(s), source = source)  => begin
                        istmts = listAppend(istmts, s)
                      ()
                    end

                    _  => begin
                          newEls = _cons(e, newEls)
                        ()
                    end
                  end
                end
              end
              newEls = listReverse(newEls)
              if ! listEmpty(istmts)
                newEls = listAppend(newEls, list(DAE.INITIALALGORITHM(DAE.ALGORITHM_STMTS(istmts), source)))
              end
              if ! listEmpty(stmts)
                newEls = listAppend(newEls, list(DAE.ALGORITHM(DAE.ALGORITHM_STMTS(stmts), source)))
              end
              outDae = DAE.DAE(newEls)
          outDae
        end

         #= Converts DAE.Element from the equation section to the initial equation section =#
        function moveElementToInitialSection(elt::DAE.Element) ::DAE.Element


              elt = begin
                @match elt begin
                  DAE.EQUATION(__)  => begin
                    DAE.INITIALEQUATION(elt.exp, elt.scalar, elt.source)
                  end

                  DAE.DEFINE(__)  => begin
                    DAE.INITIALDEFINE(elt.componentRef, elt.exp, elt.source)
                  end

                  DAE.ARRAY_EQUATION(__)  => begin
                    DAE.INITIAL_ARRAY_EQUATION(elt.dimension, elt.exp, elt.array, elt.source)
                  end

                  DAE.COMPLEX_EQUATION(__)  => begin
                    DAE.INITIAL_COMPLEX_EQUATION(elt.lhs, elt.rhs, elt.source)
                  end

                  DAE.IF_EQUATION(__)  => begin
                    DAE.INITIAL_IF_EQUATION(elt.condition1, elt.equations2, elt.equations3, elt.source)
                  end

                  DAE.ALGORITHM(__)  => begin
                    DAE.INITIALALGORITHM(elt.algorithm_, elt.source)
                  end

                  DAE.ASSERT(__)  => begin
                    DAE.INITIAL_ASSERT(elt.condition, elt.message, elt.level, elt.source)
                  end

                  DAE.TERMINATE(__)  => begin
                    DAE.INITIAL_TERMINATE(elt.message, elt.source)
                  end

                  DAE.NORETCALL(__)  => begin
                    DAE.INITIAL_NORETCALL(elt.exp, elt.source)
                  end

                  _  => begin
                      elt
                  end
                end
              end
          elt
        end

        function getParameters(elts::List{<:DAE.Element}, acc::List{<:DAE.Element}) ::List{DAE.Element}
              local params::List{DAE.Element}

              params = begin
                  local e::DAE.Element
                  local rest::List{DAE.Element}
                  local celts::List{DAE.Element}
                  local a::List{DAE.Element}
                @match (elts, acc) begin
                  ( nil(), _)  => begin
                    acc
                  end

                  (DAE.COMP(dAElist = celts) <| rest, _)  => begin
                      a = getParameters(celts, acc)
                      a = getParameters(rest, a)
                    a
                  end

                  (e && DAE.VAR(__) <| rest, _)  => begin
                    if isParameterOrConstant(e)
                          _cons(e, getParameters(rest, acc))
                        else
                          getParameters(rest, acc)
                        end
                  end

                  (_ <| rest, _)  => begin
                    getParameters(rest, acc)
                  end
                end
              end
          params
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

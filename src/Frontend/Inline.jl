  module Inline


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    Func = Function

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
        import AvlSetPath
        import BaseHashTable
        import DAE
        import HashTableCG
        import SCode
        import Util
        Functiontuple = Tuple

        import Ceval
        import ClassInf
        import ComponentReference
        import Config
        import DAEDump
        import Debug
        import ElementSource
        import Error
        import Expression
        import ExpressionDump
        import ExpressionSimplify
        import Flags
        import Global
        import ListUtil
        import SCodeUtil
        import Types
        import VarTransform

        function inlineStartAttribute(inVariableAttributesOption::Option{<:DAE.VariableAttributes}, isource::DAE.ElementSource, fns::Functiontuple) ::Tuple{Option{DAE.VariableAttributes}, DAE.ElementSource, Bool}
              local b::Bool
              local osource::DAE.ElementSource
              local outVariableAttributesOption::Option{DAE.VariableAttributes}

              (outVariableAttributesOption, osource, b) = begin
                  local source::DAE.ElementSource
                  local r::DAE.Exp
                  local quantity::Option{DAE.Exp}
                  local unit::Option{DAE.Exp}
                  local displayUnit::Option{DAE.Exp}
                  local fixed::Option{DAE.Exp}
                  local nominal::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local stateSelectOption::Option{DAE.StateSelect}
                  local uncertainOption::Option{DAE.Uncertainty}
                  local distributionOption::Option{DAE.Distribution}
                  local equationBound::Option{DAE.Exp}
                  local isProtected::Option{Bool}
                  local finalPrefix::Option{Bool}
                  local assrtLst::List{DAE.Statement}
                @matchcontinue (inVariableAttributesOption, isource, fns) begin
                  (NONE(), _, _)  => begin
                    (NONE(), isource, false)
                  end

                  (SOME(DAE.VAR_ATTR_REAL(quantity = quantity, unit = unit, displayUnit = displayUnit, min = min, max = max, start = SOME(r), fixed = fixed, nominal = nominal, stateSelectOption = stateSelectOption, uncertainOption = uncertainOption, distributionOption = distributionOption, equationBound = equationBound, isProtected = isProtected, finalPrefix = finalPrefix, startOrigin = so)), _, _)  => begin
                      @match (r, source, true, _) = inlineExp(r, fns, isource)
                    (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, SOME(r), fixed, nominal, stateSelectOption, uncertainOption, distributionOption, equationBound, isProtected, finalPrefix, so)), source, true)
                  end

                  (SOME(DAE.VAR_ATTR_INT(quantity = quantity, min = min, max = max, start = SOME(r), fixed = fixed, uncertainOption = uncertainOption, distributionOption = distributionOption, equationBound = equationBound, isProtected = isProtected, finalPrefix = finalPrefix, startOrigin = so)), _, _)  => begin
                      @match (r, source, true, _) = inlineExp(r, fns, isource)
                    (SOME(DAE.VAR_ATTR_INT(quantity, min, max, SOME(r), fixed, uncertainOption, distributionOption, equationBound, isProtected, finalPrefix, so)), source, true)
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(quantity = quantity, start = SOME(r), fixed = fixed, equationBound = equationBound, isProtected = isProtected, finalPrefix = finalPrefix, startOrigin = so)), _, _)  => begin
                      @match (r, source, true, _) = inlineExp(r, fns, isource)
                    (SOME(DAE.VAR_ATTR_BOOL(quantity, SOME(r), fixed, equationBound, isProtected, finalPrefix, so)), source, true)
                  end

                  (SOME(DAE.VAR_ATTR_STRING(quantity = quantity, start = SOME(r), fixed = fixed, equationBound = equationBound, isProtected = isProtected, finalPrefix = finalPrefix, startOrigin = so)), _, _)  => begin
                      @match (r, source, true, _) = inlineExp(r, fns, isource)
                    (SOME(DAE.VAR_ATTR_STRING(quantity, SOME(r), fixed, equationBound, isProtected, finalPrefix, so)), source, true)
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(quantity = quantity, min = min, max = max, start = SOME(r), fixed = fixed, equationBound = equationBound, isProtected = isProtected, finalPrefix = finalPrefix, startOrigin = so)), _, _)  => begin
                      @match (r, source, true, _) = inlineExp(r, fns, isource)
                    (SOME(DAE.VAR_ATTR_ENUMERATION(quantity, min, max, SOME(r), fixed, equationBound, isProtected, finalPrefix, so)), source, true)
                  end

                  _  => begin
                      (inVariableAttributesOption, isource, false)
                  end
                end
              end
          (outVariableAttributesOption, osource, b)
        end

         #= inlines calls in DAEElements =#
        function inlineCallsInFunctions(inElementList::List{<:DAE.Function}, inFunctions::Functiontuple, iAcc::List{<:DAE.Function}) ::List{DAE.Function}
              local outElementList::List{DAE.Function}

              outElementList = begin
                  local cdr::List{DAE.Function}
                  local elist::List{DAE.Element}
                  local elist_1::List{DAE.Element}
                  local el::DAE.Function
                  local res::DAE.Function
                  local t::DAE.Type
                  local partialPrefix::Bool
                  local isImpure::Bool
                  local p::Absyn.Path
                  local ext::DAE.ExternalDecl
                  local inlineType::DAE.InlineType
                  local funcDefs::List{DAE.FunctionDefinition}
                  local source::DAE.ElementSource
                  local cmt::Option{SCode.Comment}
                  local visibility::SCode.Visibility
                @matchcontinue (inElementList, inFunctions, iAcc) begin
                  ( nil(), _, _)  => begin
                    listReverse(iAcc)
                  end

                  (DAE.FUNCTION(p, DAE.FUNCTION_DEF(body = elist) <| funcDefs, t, visibility, partialPrefix, isImpure, inlineType, source, cmt) <| cdr, _, _)  => begin
                      @match (elist_1, true) = inlineDAEElements(elist, inFunctions, nil, false)
                      res = DAE.FUNCTION(p, _cons(DAE.FUNCTION_DEF(elist_1), funcDefs), t, visibility, partialPrefix, isImpure, inlineType, source, cmt)
                    inlineCallsInFunctions(cdr, inFunctions, _cons(res, iAcc))
                  end

                  (DAE.FUNCTION(p, DAE.FUNCTION_EXT(elist, ext) <| funcDefs, t, visibility, partialPrefix, isImpure, inlineType, source, cmt) <| cdr, _, _)  => begin
                      @match (elist_1, true) = inlineDAEElements(elist, inFunctions, nil, false)
                      res = DAE.FUNCTION(p, _cons(DAE.FUNCTION_EXT(elist_1, ext), funcDefs), t, visibility, partialPrefix, isImpure, inlineType, source, cmt)
                    inlineCallsInFunctions(cdr, inFunctions, _cons(res, iAcc))
                  end

                  (el <| cdr, _, _)  => begin
                    inlineCallsInFunctions(cdr, inFunctions, _cons(el, iAcc))
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Inline.inlineCallsInFunctions failed"))
                      fail()
                  end
                end
              end
               #=  external functions
               =#
          outElementList
        end

        function inlineDAEElementsLst(inElementList::List{<:List{<:DAE.Element}}, inFunctions::Functiontuple, iAcc::List{<:List{<:DAE.Element}}, iInlined::Bool) ::Tuple{List{List{DAE.Element}}, Bool}
              local OInlined::Bool
              local outElementList::List{List{DAE.Element}}

              (outElementList, OInlined) = begin
                  local elem::List{DAE.Element}
                  local rest::List{List{DAE.Element}}
                  local acc::List{List{DAE.Element}}
                  local inlined::Bool
                @match (inElementList, inFunctions, iAcc, iInlined) begin
                  ( nil(), _, _, _)  => begin
                    (listReverse(iAcc), iInlined)
                  end

                  (elem <| rest, _, _, _)  => begin
                      (elem, inlined) = inlineDAEElements(elem, inFunctions, nil, false)
                      (acc, inlined) = inlineDAEElementsLst(rest, inFunctions, _cons(elem, iAcc), inlined || iInlined)
                    (acc, inlined)
                  end
                end
              end
          (outElementList, OInlined)
        end

        function inlineDAEElements(inElementList::List{<:DAE.Element}, inFunctions::Functiontuple, iAcc::List{<:DAE.Element}, iInlined::Bool) ::Tuple{List{DAE.Element}, Bool}
              local OInlined::Bool
              local outElementList::List{DAE.Element}

              (outElementList, OInlined) = begin
                  local elem::DAE.Element
                  local rest::List{DAE.Element}
                  local acc::List{DAE.Element}
                  local inlined::Bool
                @match (inElementList, inFunctions, iAcc, iInlined) begin
                  ( nil(), _, _, _)  => begin
                    (listReverse(iAcc), iInlined)
                  end

                  (elem <| rest, _, _, _)  => begin
                      (elem, inlined) = inlineDAEElement(elem, inFunctions)
                      (acc, inlined) = inlineDAEElements(rest, inFunctions, _cons(elem, iAcc), inlined || iInlined)
                    (acc, inlined)
                  end
                end
              end
          (outElementList, OInlined)
        end

         #= inlines calls in DAEElements =#
        function inlineDAEElement(inElement::DAE.Element, inFunctions::Functiontuple) ::Tuple{DAE.Element, Bool}
              local inlined::Bool
              local outElement::DAE.Element

              (outElement, inlined) = begin
                  local fns::Functiontuple
                  local elist::List{DAE.Element}
                  local elist_1::List{DAE.Element}
                  local dlist::List{List{DAE.Element}}
                  local dlist_1::List{List{DAE.Element}}
                  local el::DAE.Element
                  local el_1::DAE.Element
                  local componentRef::DAE.ComponentRef
                  local kind::DAE.VarKind
                  local direction::DAE.VarDirection
                  local parallelism::DAE.VarParallelism
                  local protection::DAE.VarVisibility
                  local ty::DAE.Type
                  local binding::DAE.Exp
                  local binding_1::DAE.Exp
                  local exp::DAE.Exp
                  local exp_1::DAE.Exp
                  local exp1::DAE.Exp
                  local exp1_1::DAE.Exp
                  local exp2::DAE.Exp
                  local exp2_1::DAE.Exp
                  local exp3::DAE.Exp
                  local exp3_1::DAE.Exp
                  local dims::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local variableAttributesOption::Option{DAE.VariableAttributes}
                  local absynCommentOption::Option{SCode.Comment}
                  local innerOuter::Absyn.InnerOuter
                  local dimension::DAE.Dimensions
                  local alg::DAE.Algorithm
                  local alg_1::DAE.Algorithm
                  local i::String
                  local p::Absyn.Path
                  local explst::List{DAE.Exp}
                  local explst_1::List{DAE.Exp}
                  local source::DAE.ElementSource
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local assrtLst::List{DAE.Statement}
                @matchcontinue (inElement, inFunctions) begin
                  (DAE.VAR(componentRef, kind, direction, parallelism, protection, ty, SOME(binding), dims, ct, source, variableAttributesOption, absynCommentOption, innerOuter), fns)  => begin
                      @match (binding_1, source, true, _) = inlineExp(binding, fns, source)
                    (DAE.VAR(componentRef, kind, direction, parallelism, protection, ty, SOME(binding_1), dims, ct, source, variableAttributesOption, absynCommentOption, innerOuter), true)
                  end

                  (DAE.DEFINE(componentRef, exp, source), fns)  => begin
                      @match (exp_1, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.DEFINE(componentRef, exp_1, source), true)
                  end

                  (DAE.INITIALDEFINE(componentRef, exp, source), fns)  => begin
                      @match (exp_1, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.INITIALDEFINE(componentRef, exp_1, source), true)
                  end

                  (DAE.EQUATION(exp1, exp2, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      @match true = b1 || b2
                    (DAE.EQUATION(exp1_1, exp2_1, source), true)
                  end

                  (DAE.ARRAY_EQUATION(dimension, exp1, exp2, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      @match true = b1 || b2
                    (DAE.ARRAY_EQUATION(dimension, exp1_1, exp2_1, source), true)
                  end

                  (DAE.INITIAL_ARRAY_EQUATION(dimension, exp1, exp2, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      @match true = b1 || b2
                    (DAE.INITIAL_ARRAY_EQUATION(dimension, exp1_1, exp2_1, source), true)
                  end

                  (DAE.COMPLEX_EQUATION(exp1, exp2, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      @match true = b1 || b2
                    (DAE.COMPLEX_EQUATION(exp1_1, exp2_1, source), true)
                  end

                  (DAE.INITIAL_COMPLEX_EQUATION(exp1, exp2, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      @match true = b1 || b2
                    (DAE.INITIAL_COMPLEX_EQUATION(exp1_1, exp2_1, source), true)
                  end

                  (DAE.WHEN_EQUATION(exp, elist, SOME(el), source), fns)  => begin
                      (exp_1, source, b1, _) = inlineExp(exp, fns, source)
                      (elist_1, b2) = inlineDAEElements(elist, fns, nil, false)
                      (el_1, b3) = inlineDAEElement(el, fns)
                      @match true = b1 || b2 || b3
                    (DAE.WHEN_EQUATION(exp_1, elist_1, SOME(el_1), source), true)
                  end

                  (DAE.WHEN_EQUATION(exp, elist, NONE(), source), fns)  => begin
                      (exp_1, source, b1, _) = inlineExp(exp, fns, source)
                      (elist_1, b2) = inlineDAEElements(elist, fns, nil, false)
                      @match true = b1 || b2
                    (DAE.WHEN_EQUATION(exp_1, elist_1, NONE(), source), true)
                  end

                  (DAE.IF_EQUATION(explst, dlist, elist, source), fns)  => begin
                      (explst_1, source, b1) = inlineExps(explst, fns, source)
                      (dlist_1, b2) = inlineDAEElementsLst(dlist, fns, nil, false)
                      (elist_1, b3) = inlineDAEElements(elist, fns, nil, false)
                      @match true = b1 || b2 || b3
                    (DAE.IF_EQUATION(explst_1, dlist_1, elist_1, source), true)
                  end

                  (DAE.INITIAL_IF_EQUATION(explst, dlist, elist, source), fns)  => begin
                      (explst_1, source, b1) = inlineExps(explst, fns, source)
                      (dlist_1, b2) = inlineDAEElementsLst(dlist, fns, nil, false)
                      (elist_1, b3) = inlineDAEElements(elist, fns, nil, false)
                      @match true = b1 || b2 || b3
                    (DAE.INITIAL_IF_EQUATION(explst_1, dlist_1, elist_1, source), true)
                  end

                  (DAE.INITIALEQUATION(exp1, exp2, source), fns)  => begin
                      (exp1_1, source, _, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, _, _) = inlineExp(exp2, fns, source)
                    (DAE.INITIALEQUATION(exp1_1, exp2_1, source), true)
                  end

                  (DAE.ALGORITHM(alg, source), fns)  => begin
                      @match (alg_1, true) = inlineAlgorithm(alg, fns)
                    (DAE.ALGORITHM(alg_1, source), true)
                  end

                  (DAE.INITIALALGORITHM(alg, source), fns)  => begin
                      @match (alg_1, true) = inlineAlgorithm(alg, fns)
                    (DAE.INITIALALGORITHM(alg_1, source), true)
                  end

                  (DAE.COMP(i, elist, source, absynCommentOption), fns)  => begin
                      @match (elist_1, true) = inlineDAEElements(elist, fns, nil, false)
                    (DAE.COMP(i, elist_1, source, absynCommentOption), true)
                  end

                  (DAE.ASSERT(exp1, exp2, exp3, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      (exp3_1, source, b3, _) = inlineExp(exp3, fns, source)
                      @match true = b1 || b2 || b3
                    (DAE.ASSERT(exp1_1, exp2_1, exp3_1, source), true)
                  end

                  (DAE.INITIAL_ASSERT(exp1, exp2, exp3, source), fns)  => begin
                      (exp1_1, source, b1, _) = inlineExp(exp1, fns, source)
                      (exp2_1, source, b2, _) = inlineExp(exp2, fns, source)
                      (exp3_1, source, b3, _) = inlineExp(exp3, fns, source)
                      @match true = b1 || b2 || b3
                    (DAE.INITIAL_ASSERT(exp1_1, exp2_1, exp3_1, source), true)
                  end

                  (DAE.TERMINATE(exp, source), fns)  => begin
                      @match (exp_1, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.TERMINATE(exp_1, source), true)
                  end

                  (DAE.INITIAL_TERMINATE(exp, source), fns)  => begin
                      @match (exp_1, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.INITIAL_TERMINATE(exp_1, source), true)
                  end

                  (DAE.REINIT(componentRef, exp, source), fns)  => begin
                      @match (exp_1, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.REINIT(componentRef, exp_1, source), true)
                  end

                  (DAE.NORETCALL(exp, source), fns)  => begin
                      @match (exp, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.NORETCALL(exp, source), true)
                  end

                  (DAE.INITIAL_NORETCALL(exp, source), fns)  => begin
                      @match (exp, source, true, _) = inlineExp(exp, fns, source)
                    (DAE.INITIAL_NORETCALL(exp, source), true)
                  end

                  (el, _)  => begin
                    (el, false)
                  end
                end
              end
          (outElement, inlined)
        end

         #= inline calls in an DAE.Algorithm =#
        function inlineAlgorithm(inAlgorithm::DAE.Algorithm, inElementList::Functiontuple) ::Tuple{DAE.Algorithm, Bool}
              local inlined::Bool
              local outAlgorithm::DAE.Algorithm

              (outAlgorithm, inlined) = begin
                  local stmts::List{DAE.Statement}
                  local stmts_1::List{DAE.Statement}
                  local fns::Functiontuple
                @matchcontinue (inAlgorithm, inElementList) begin
                  (DAE.ALGORITHM_STMTS(stmts), fns)  => begin
                      (stmts_1, inlined) = inlineStatements(stmts, fns, nil, false)
                    (DAE.ALGORITHM_STMTS(stmts_1), inlined)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("Inline.inlineAlgorithm failed\\n")
                      fail()
                  end
                end
              end
          (outAlgorithm, inlined)
        end

        function inlineStatements(inStatements::List{<:DAE.Statement}, inElementList::Functiontuple, iAcc::List{<:DAE.Statement}, iInlined::Bool) ::Tuple{List{DAE.Statement}, Bool}
              local OInlined::Bool
              local outStatements::List{DAE.Statement}

              (outStatements, OInlined) = begin
                  local stmt::DAE.Statement
                  local rest::List{DAE.Statement}
                  local acc::List{DAE.Statement}
                  local inlined::Bool
                @match (inStatements, inElementList, iAcc, iInlined) begin
                  ( nil(), _, _, _)  => begin
                    (listReverse(iAcc), iInlined)
                  end

                  (stmt <| rest, _, _, _)  => begin
                      (stmt, inlined) = inlineStatement(stmt, inElementList)
                      (acc, inlined) = inlineStatements(rest, inElementList, _cons(stmt, iAcc), inlined || iInlined)
                    (acc, inlined)
                  end
                end
              end
          (outStatements, OInlined)
        end

         #= inlines calls in an DAE.Statement =#
        function inlineStatement(inStatement::DAE.Statement, inElementList::Functiontuple) ::Tuple{DAE.Statement, Bool}
              local inlined::Bool
              local outStatement::DAE.Statement

              (outStatement, inlined) = begin
                  local fns::Functiontuple
                  local stmt::DAE.Statement
                  local stmt_1::DAE.Statement
                  local t::DAE.Type
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e1::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2::DAE.Exp
                  local e2_1::DAE.Exp
                  local e3::DAE.Exp
                  local e3_1::DAE.Exp
                  local explst::List{DAE.Exp}
                  local explst_1::List{DAE.Exp}
                  local cref::DAE.ComponentRef
                  local a_else::DAE.Else
                  local a_else_1::DAE.Else
                  local stmts::List{DAE.Statement}
                  local stmts_1::List{DAE.Statement}
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local i::String
                  local ix::ModelicaInteger
                  local source::DAE.ElementSource
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                  local assrtLst::List{DAE.Statement}
                @matchcontinue (inStatement, inElementList) begin
                  (DAE.STMT_ASSIGN(t, e1, e2, source), fns)  => begin
                      (e1_1, source, b1, _) = inlineExp(e1, fns, source)
                      (e2_1, source, b2, _) = inlineExp(e2, fns, source)
                      @match true = b1 || b2
                    (DAE.STMT_ASSIGN(t, e1_1, e2_1, source), true)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(t, explst, e, source), fns)  => begin
                      (explst_1, source, b1) = inlineExps(explst, fns, source)
                      (e_1, source, b2, _) = inlineExp(e, fns, source)
                      @match true = b1 || b2
                    (DAE.STMT_TUPLE_ASSIGN(t, explst_1, e_1, source), true)
                  end

                  (DAE.STMT_ASSIGN_ARR(t, e1, e2, source), fns)  => begin
                      (e1_1, source, b1, _) = inlineExp(e1, fns, source)
                      (e2_1, source, b2, _) = inlineExp(e2, fns, source)
                      @match true = b1 || b2
                    (DAE.STMT_ASSIGN_ARR(t, e1_1, e2_1, source), true)
                  end

                  (DAE.STMT_IF(e, stmts, a_else, source), fns)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      (a_else_1, source, b3) = inlineElse(a_else, fns, source)
                      @match true = b1 || b2 || b3
                    (DAE.STMT_IF(e_1, stmts_1, a_else_1, source), true)
                  end

                  (DAE.STMT_FOR(t, b, i, ix, e, stmts, source), fns)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      @match true = b1 || b2
                    (DAE.STMT_FOR(t, b, i, ix, e_1, stmts_1, source), true)
                  end

                  (DAE.STMT_WHILE(e, stmts, source), fns)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      @match true = b1 || b2
                    (DAE.STMT_WHILE(e_1, stmts_1, source), true)
                  end

                  (DAE.STMT_WHEN(e, conditions, initialCall, stmts, SOME(stmt), source), fns)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      (stmt_1, b3) = inlineStatement(stmt, fns)
                      @match true = b1 || b2 || b3
                    (DAE.STMT_WHEN(e_1, conditions, initialCall, stmts_1, SOME(stmt_1), source), true)
                  end

                  (DAE.STMT_WHEN(e, conditions, initialCall, stmts, NONE(), source), fns)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      @match true = b1 || b2
                    (DAE.STMT_WHEN(e_1, conditions, initialCall, stmts_1, NONE(), source), true)
                  end

                  (DAE.STMT_ASSERT(e1, e2, e3, source), fns)  => begin
                      (e1_1, source, b1, _) = inlineExp(e1, fns, source)
                      (e2_1, source, b2, _) = inlineExp(e2, fns, source)
                      (e3_1, source, b3, _) = inlineExp(e3, fns, source)
                      @match true = b1 || b2 || b3
                    (DAE.STMT_ASSERT(e1_1, e2_1, e3_1, source), true)
                  end

                  (DAE.STMT_TERMINATE(e, source), fns)  => begin
                      @match (e_1, source, true, _) = inlineExp(e, fns, source)
                    (DAE.STMT_TERMINATE(e_1, source), true)
                  end

                  (DAE.STMT_REINIT(e1, e2, source), fns)  => begin
                      (e1_1, source, b1, _) = inlineExp(e1, fns, source)
                      (e2_1, source, b2, _) = inlineExp(e2, fns, source)
                      @match true = b1 || b2
                    (DAE.STMT_REINIT(e1_1, e2_1, source), true)
                  end

                  (DAE.STMT_NORETCALL(e, source), fns)  => begin
                      @match (e_1, source, true, _) = inlineExp(e, fns, source)
                    (DAE.STMT_NORETCALL(e_1, source), true)
                  end

                  (DAE.STMT_FAILURE(stmts, source), fns)  => begin
                      @match (stmts_1, true) = inlineStatements(stmts, fns, nil, false)
                    (DAE.STMT_FAILURE(stmts_1, source), true)
                  end

                  (stmt, _)  => begin
                    (stmt, false)
                  end
                end
              end
          (outStatement, inlined)
        end

         #= inlines calls in an DAE.Else =#
        function inlineElse(inElse::DAE.Else, inElementList::Functiontuple, inSource::DAE.ElementSource) ::Tuple{DAE.Else, DAE.ElementSource, Bool}
              local inlined::Bool
              local outSource::DAE.ElementSource
              local outElse::DAE.Else

              (outElse, outSource, inlined) = begin
                  local fns::Functiontuple
                  local a_else::DAE.Else
                  local a_else_1::DAE.Else
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local stmts_1::List{DAE.Statement}
                  local source::DAE.ElementSource
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local assrtLst::List{DAE.Statement}
                @matchcontinue (inElse, inElementList, inSource) begin
                  (DAE.ELSEIF(e, stmts, a_else), fns, source)  => begin
                      (e_1, source, b1, _) = inlineExp(e, fns, source)
                      (stmts_1, b2) = inlineStatements(stmts, fns, nil, false)
                      (a_else_1, source, b3) = inlineElse(a_else, fns, source)
                      @match true = b1 || b2 || b3
                    (DAE.ELSEIF(e_1, stmts_1, a_else_1), source, true)
                  end

                  (DAE.ELSE(stmts), fns, source)  => begin
                      @match (stmts_1, true) = inlineStatements(stmts, fns, nil, false)
                    (DAE.ELSE(stmts_1), source, true)
                  end

                  (a_else, _, source)  => begin
                    (a_else, source, false)
                  end
                end
              end
          (outElse, outSource, inlined)
        end

         #=
        function: inlineExpOpt
          inlines calls in an DAE.Exp =#
        function inlineExpOpt(inExpOption::Option{<:DAE.Exp}, inElementList::Functiontuple, inSource::DAE.ElementSource) ::Tuple{Option{DAE.Exp}, DAE.ElementSource, Bool}
              local inlined::Bool
              local outSource::DAE.ElementSource
              local outExpOption::Option{DAE.Exp}

              (outExpOption, outSource, inlined) = begin
                  local exp::DAE.Exp
                  local source::DAE.ElementSource
                  local b::Bool
                  local assrtLst::List{DAE.Statement}
                @match (inExpOption, inElementList, inSource) begin
                  (NONE(), _, _)  => begin
                    (NONE(), inSource, false)
                  end

                  (SOME(exp), _, _)  => begin
                      (exp, source, b, _) = inlineExp(exp, inElementList, inSource)
                    (SOME(exp), source, b)
                  end
                end
              end
          (outExpOption, outSource, inlined)
        end

        function fixFNS(fns)
          inlineCall(fns = fns)
        end

         #=
        function: inlineExp
          inlines calls in a DAE.Exp =#
        function inlineExp(inExp::DAE.Exp, inElementList::Functiontuple, inSource::DAE.ElementSource) ::Tuple{DAE.Exp, DAE.ElementSource, Bool, List{DAE.Statement}}
              local assrtLstOut::List{DAE.Statement}
              local inlined::Bool
              local outSource::DAE.ElementSource
              local outExp::DAE.Exp

              # TODO! FIXME! adrpo: disable inlining for now
              return (inExp, inSource, true, nil)

              (outExp, outSource, inlined, assrtLstOut) = begin
                  local fns::Functiontuple
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local source::DAE.ElementSource
                  local assrtLst::List{DAE.Statement}
                  local eq::DAE.EquationExp
                   #=  never inline WILD!
                   =#
                @matchcontinue (inExp, inElementList, inSource) begin
                  (DAE.CREF(componentRef = DAE.WILD(__)), _, _)  => begin
                    (inExp, inSource, false, nil)
                  end

                  (e, fns, source)  => begin
                      (e_1, assrtLst) = Expression.traverseExpBottomUp(e, fixFNS(fns), nil)
                      @match false = referenceEq(e, e_1)
                      if Flags.isSet(Flags.INFO_XML_OPERATIONS)
                        source = ElementSource.addSymbolicTransformation(source, DAE.OP_INLINE(DAE.PARTIAL_EQUATION(e), DAE.PARTIAL_EQUATION(e_1)))
                        @match (DAE.PARTIAL_EQUATION(e_2), source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.PARTIAL_EQUATION(e_1), source)
                      else
                        e_2 = ExpressionSimplify.simplify(e_1)
                      end
                    (e_2, source, true, assrtLst)
                  end

                  _  => begin
                      (inExp, inSource, false, nil)
                  end
                end
              end
          (outExp, outSource, inlined, assrtLstOut)
        end

         #=
        function: inlineExp
          inlines calls in an DAE.Exp =#
        function forceInlineExp(inExp::DAE.Exp, inElementList::Functiontuple, inSource::DAE.ElementSource) ::Tuple{DAE.Exp, DAE.ElementSource, Bool}
              local inlineperformed::Bool
              local outSource::DAE.ElementSource
              local outExp::DAE.Exp

              (outExp, outSource, inlineperformed) = begin
                  local fns::Functiontuple
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local source::DAE.ElementSource
                  local assrtLst::List{DAE.Statement}
                  local functionTree::DAE.FunctionTree
                  local b::Bool
                @match (inExp, inElementList, inSource) begin
                  (e, (SOME(functionTree), _), source) where (Expression.isConst(inExp))  => begin
                      e_1 = Ceval.cevalSimpleWithFunctionTreeReturnExp(inExp, functionTree)
                      source = ElementSource.addSymbolicTransformation(source, DAE.OP_INLINE(DAE.PARTIAL_EQUATION(e), DAE.PARTIAL_EQUATION(e_1)))
                    (e_1, source, true)
                  end

                  (e, fns, source)  => begin
                      (e_1, _) = Expression.traverseExpBottomUp(e, (fns, visitedPaths) -> forceInlineCall(fns = fns, visitedPaths = AvlSetPath.Tree.EMPTY()), nil)
                      b = ! referenceEq(e, e_1)
                      if b
                        source = ElementSource.addSymbolicTransformation(source, DAE.OP_INLINE(DAE.PARTIAL_EQUATION(e), DAE.PARTIAL_EQUATION(e_1)))
                        @match (DAE.PARTIAL_EQUATION(e_1), source) = ExpressionSimplify.simplifyAddSymbolicOperation(DAE.PARTIAL_EQUATION(e_1), source)
                      end
                    (e_1, source, b)
                  end

                  _  => begin
                      (inExp, inSource, false)
                  end
                end
              end
          (outExp, outSource, inlineperformed)
        end

         #=
        function: inlineExp
          inlines calls in an DAE.Exp =#
        function inlineExps(inExps::List{<:DAE.Exp}, inElementList::Functiontuple, inSource::DAE.ElementSource) ::Tuple{List{DAE.Exp}, DAE.ElementSource, Bool}
              local inlined::Bool
              local outSource::DAE.ElementSource
              local outExps::List{DAE.Exp}

              (outExps, outSource, inlined) = inlineExpsWork(inExps, inElementList, inSource, nil, false)
          (outExps, outSource, inlined)
        end

         #=
        function: inlineExp
          inlines calls in an DAE.Exp =#
        function inlineExpsWork(inExps::List{<:DAE.Exp}, fns::Functiontuple, inSource::DAE.ElementSource, iAcc::List{<:DAE.Exp}, iInlined::Bool) ::Tuple{List{DAE.Exp}, DAE.ElementSource, Bool}
              local oInlined::Bool
              local outSource::DAE.ElementSource
              local outExps::List{DAE.Exp}

              (outExps, outSource, oInlined) = begin
                  local e::DAE.Exp
                  local exps::List{DAE.Exp}
                  local source::DAE.ElementSource
                  local b::Bool
                  local assrtLst::List{DAE.Statement}
                @match (inExps, fns, inSource, iAcc, iInlined) begin
                  ( nil(), _, _, _, _)  => begin
                    (listReverse(iAcc), inSource, iInlined)
                  end

                  (e <| exps, _, _, _, _)  => begin
                      (e, source, b, _) = inlineExp(e, fns, inSource)
                      (exps, source, b) = inlineExpsWork(exps, fns, source, _cons(e, iAcc), b || iInlined)
                    (exps, source, b)
                  end
                end
              end
          (outExps, outSource, oInlined)
        end

         #= @author: adrpo
          check two types for equivalence =#
        function checkExpsTypeEquiv(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool
              local bEquiv::Bool

              bEquiv = begin
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local b::Bool
                @match (inExp1, inExp2) begin
                  (_, _)  => begin
                      if Config.acceptMetaModelicaGrammar()
                        b = true
                      else
                        ty1 = Expression.typeof(inExp1)
                        ty2 = Expression.typeof(inExp2)
                        (ty2, _) = Types.traverseType(ty2, -1, Types.makeExpDimensionsUnknown)
                        b = Types.equivtypesOrRecordSubtypeOf(ty1, ty2)
                      end
                    b
                  end
                end
              end
          bEquiv
        end

         #= replaces an inline call with the expression from the function =#
        function inlineCall(exp::DAE.Exp, assrtLst::List{<:DAE.Statement}, fns::Functiontuple) ::Tuple{DAE.Exp, List{DAE.Statement}}



              (exp, assrtLst) = begin
                  local fn::List{DAE.Element}
                  local p::Absyn.Path
                  local args::List{DAE.Exp}
                  local crefs::List{DAE.ComponentRef}
                  local argmap::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local lst_cr::List{DAE.ComponentRef}
                  local source::DAE.ElementSource
                  local newExp::DAE.Exp
                  local newExp1::DAE.Exp
                  local e1::DAE.Exp
                  local cond::DAE.Exp
                  local msg::DAE.Exp
                  local level::DAE.Exp
                  local newAssrtCond::DAE.Exp
                  local newAssrtMsg::DAE.Exp
                  local newAssrtLevel::DAE.Exp
                  local inlineType::DAE.InlineType
                  local assrt::DAE.Statement
                  local checkcr::HashTableCG.HashTable
                  local stmts::List{DAE.Statement}
                  local assrtStmts::List{DAE.Statement}
                  local repl::VarTransform.VariableReplacements
                  local generateEvents::Bool
                  local comment::Option{SCode.Comment}
                  local ty::DAE.Type
                   #=  If we disable inlining by use of flags, we still inline builtin functions
                   =#
                @matchcontinue exp begin
                  DAE.CALL(attr = DAE.CALL_ATTR(inlineType = inlineType))  => begin
                      @match false = Flags.isSet(Flags.INLINE_FUNCTIONS)
                      @match false = valueEq(DAE.BUILTIN_EARLY_INLINE(), inlineType)
                    (exp, assrtLst)
                  end

                  e1 && DAE.CALL(p, args, DAE.CALL_ATTR(ty = ty, inlineType = inlineType))  => begin
                      @match true = checkInlineType(inlineType, fns)
                      (fn, comment) = getFunctionBody(p, fns)
                      (checkcr, repl) = getInlineHashTableVarTransform()
                      if Config.acceptMetaModelicaGrammar()
                        crefs = ListUtil.map(fn, getInputCrefs)
                        crefs = ListUtil.select(crefs, removeWilds)
                        argmap = ListUtil.threadTuple(crefs, args)
                        @match false = ListUtil.exist(fn, DAEUtil.isProtectedVar)
                        newExp = getRhsExp(fn)
                        @match true = checkExpsTypeEquiv(e1, newExp)
                        (argmap, checkcr) = extendCrefRecords(argmap, checkcr)
                        newExp = Expression.addNoEventToRelationsAndConds(newExp)
                        @match (newExp, (_, _, true)) = Expression.traverseExpBottomUp(newExp, replaceArgs, (argmap, checkcr, true))
                        (newExp1, assrtLst) = Expression.traverseExpBottomUp(newExp, (fns) -> inlineCall(fns = fns), assrtLst)
                      else
                        (crefs, lst_cr, stmts, repl) = getFunctionInputsOutputBody(fn, repl)
                        (repl, assrtStmts) = myMergeFunctionBody(stmts, repl, nil)
                        if listEmpty(assrtStmts)
                          newExp = Expression.makeTuple(list(getReplacementCheckComplex(repl, cr, ty) for cr in lst_cr))
                          @match true = checkExpsTypeEquiv(e1, newExp)
                          argmap = ListUtil.threadTuple(crefs, args)
                          (checkcr, _) = getInlineHashTableVarTransform()
                          (argmap, checkcr) = extendCrefRecords(argmap, checkcr)
                          generateEvents = hasGenerateEventsAnnotation(comment)
                          newExp = if ! generateEvents
                                Expression.addNoEventToRelationsAndConds(newExp)
                              else
                                newExp
                              end
                          @match (newExp, (_, _, true)) = Expression.traverseExpBottomUp(newExp, replaceArgs, (argmap, checkcr, true))
                          (newExp1, assrtLst) = Expression.traverseExpBottomUp(newExp, (fns) -> inlineCall(fns = fns), assrtLst)
                        else
                          @match true = listLength(assrtStmts) == 1
                          assrt = listHead(assrtStmts)
                          @match DAE.STMT_ASSERT() = assrt
                          newExp = Expression.makeTuple(list(getReplacementCheckComplex(repl, cr, ty) for cr in lst_cr))
                          @match true = checkExpsTypeEquiv(e1, newExp)
                          argmap = ListUtil.threadTuple(crefs, args)
                          (argmap, checkcr) = extendCrefRecords(argmap, checkcr)
                          generateEvents = hasGenerateEventsAnnotation(comment)
                          newExp = if ! generateEvents
                                Expression.addNoEventToRelationsAndConds(newExp)
                              else
                                newExp
                              end
                          @match (newExp, (_, _, true)) = Expression.traverseExpBottomUp(newExp, replaceArgs, (argmap, checkcr, true))
                          assrt = inlineAssert(assrt, fns, argmap, checkcr)
                          (newExp1, assrtLst) = Expression.traverseExpBottomUp(newExp, (fns) -> inlineCall(fns = fns), _cons(assrt, assrtLst))
                        end
                      end
                    (newExp1, assrtLst)
                  end

                  _  => begin
                      (exp, assrtLst)
                  end
                end
              end
          (exp, assrtLst)
        end

        inlineCall(exp, assrtLst; fns) = inlineCall(exp, assrtLst, fns)

         #= inlines an assert.
        author:Waurich TUD 2013-10 =#
        function inlineAssert(assrtIn::DAE.Statement, fns::Functiontuple, argmap::List{<:Tuple{<:DAE.ComponentRef, DAE.Exp}}, checkcr::HashTableCG.HashTable) ::DAE.Statement
              local assrtOut::DAE.Statement

              local source::DAE.ElementSource
              local cond::DAE.Exp
              local msg::DAE.Exp
              local level::DAE.Exp

              @match DAE.STMT_ASSERT(cond = cond, msg = msg, level = level, source = source) = assrtIn
              @match (cond, (_, _, true)) = Expression.traverseExpBottomUp(cond, replaceArgs, (argmap, checkcr, true))
               #= print(\"ASSERT inlined: \"+ExpressionDump.printExpStr(cond)+\"\\n\");
               =#
              @match (msg, (_, _, true)) = Expression.traverseExpBottomUp(msg, replaceArgs, (argmap, checkcr, true))
               #=  These clear checkcr/repl and need to be performed last
               =#
               #=  (cond,_,_,_) := inlineExp(cond,fns,source);
               =#
               #=  (msg,_,_,_) := inlineExp(msg,fns,source);
               =#
              assrtOut = DAE.STMT_ASSERT(cond, msg, level, source)
          assrtOut
        end

        function hasGenerateEventsAnnotation(comment::Option{<:SCode.Comment}) ::Bool
              local b::Bool

              b = begin
                  local anno::SCode.Annotation
                  local annos::List{SCode.Annotation}
                @match comment begin
                  SOME(SCode.COMMENT(annotation_ = SOME(anno)))  => begin
                    SCodeUtil.hasBooleanNamedAnnotation(anno, "GenerateEvents")
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function dumpArgmap(inTpl::Tuple{<:DAE.ComponentRef, DAE.Exp})
              local cr::DAE.ComponentRef
              local exp::DAE.Exp

              (cr, exp) = inTpl
              print(ComponentReference.printComponentRefStr(cr) + " -> " + ExpressionDump.printExpStr(exp) + "\\n")
        end

         #= replaces an inline call with the expression from the function =#
        function forceInlineCall(exp::DAE.Exp, assrtLst::List{<:DAE.Statement}, fns::Functiontuple, visitedPaths::AvlSetPath.Tree = AvlSetPath.EMPTY()) ::Tuple{DAE.Exp, List{DAE.Statement}}



              (exp, assrtLst) = begin
                  local fn::List{DAE.Element}
                  local p::Absyn.Path
                  local args::List{DAE.Exp}
                  local lst_cr::List{DAE.ComponentRef}
                  local crefs::List{DAE.ComponentRef}
                  local assrtStmts::List{DAE.Statement}
                  local argmap::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local newExp::DAE.Exp
                  local newExp1::DAE.Exp
                  local e1::DAE.Exp
                  local inlineType::DAE.InlineType
                  local assrt::DAE.Statement
                  local checkcr::HashTableCG.HashTable
                  local stmts::List{DAE.Statement}
                  local repl::VarTransform.VariableReplacements
                  local generateEvents::Bool
                  local b::Bool
                  local comment::Option{SCode.Comment}
                @matchcontinue exp begin
                  e1 && DAE.CALL(p, args, DAE.CALL_ATTR(inlineType = inlineType)) where (! AvlSetPath.hasKey(visitedPaths, p))  => begin
                      @match false = Config.acceptMetaModelicaGrammar()
                      @match true = checkInlineType(inlineType, fns)
                      (fn, comment) = getFunctionBody(p, fns)
                      (checkcr, repl) = getInlineHashTableVarTransform()
                      (crefs, lst_cr, stmts, repl) = getFunctionInputsOutputBody(fn, repl)
                      (repl, _) = myMergeFunctionBody(stmts, repl, nil)
                      newExp = Expression.makeTuple(list(VarTransform.getReplacement(repl, cr) for cr in lst_cr))
                      @match true = checkExpsTypeEquiv(e1, newExp)
                      argmap = ListUtil.threadTuple(crefs, args)
                      (argmap, checkcr) = extendCrefRecords(argmap, checkcr)
                      generateEvents = hasGenerateEventsAnnotation(comment)
                      newExp = if ! generateEvents
                            Expression.addNoEventToRelationsAndConds(newExp)
                          else
                            newExp
                          end
                      @match (newExp, (_, _, true)) = Expression.traverseExpBottomUp(newExp, replaceArgs, (argmap, checkcr, true))
                      (newExp1, assrtLst) = Expression.traverseExpBottomUp(newExp, fn -> forceInlineCall(fns = fns, visitedPaths = AvlSetPath.add(visitedPaths, p)), assrtLst)
                    (newExp1, assrtLst)
                  end

                  _  => begin
                      (exp, assrtLst)
                  end
                end
              end
               #= print(printInlineTypeStr(inlineType));
               =#
               #=  get inputs, body and output
               =#
               #=  myMerge statements to one line
               =#
               #= newExp = VarTransform.getReplacement(repl,cr);
               =#
               #=  compare types
               =#
               #=  add noEvent to avoid events as usually for functions
               =#
               #=  MSL 3.2.1 need GenerateEvents to disable this
               =#
               #=  for inlinecalls in functions
               =#
          (exp, assrtLst)
        end

        function mergeFunctionBody(iStmts::List{<:DAE.Statement}, iRepl::VarTransform.VariableReplacements, assertStmtsIn::List{<:DAE.Statement}) ::Tuple{VarTransform.VariableReplacements, List{DAE.Statement}}
              local assertStmtsOut::List{DAE.Statement}
              local oRepl::VarTransform.VariableReplacements

              (oRepl, assertStmtsOut) = begin
                  local stmts::List{DAE.Statement}
                  local repl::VarTransform.VariableReplacements
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local source::DAE.ElementSource
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local stmt::DAE.Statement
                  local explst::List{DAE.Exp}
                  local assertStmts::List{DAE.Statement}
                @match (iStmts, iRepl, assertStmtsIn) begin
                  ( nil(), _, _)  => begin
                    (iRepl, assertStmtsIn)
                  end

                  (DAE.STMT_ASSIGN(exp1 = DAE.CREF(componentRef = cr), exp = exp) <| stmts, _, _)  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      repl = VarTransform.addReplacementNoTransitive(iRepl, cr, exp)
                      (repl, assertStmts) = myMergeFunctionBody(stmts, repl, assertStmtsIn)
                    (repl, assertStmts)
                  end

                  (DAE.STMT_ASSIGN_ARR(lhs = DAE.CREF(componentRef = cr), exp = exp) <| stmts, _, _)  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      repl = VarTransform.addReplacementNoTransitive(iRepl, cr, exp)
                      (repl, assertStmts) = myMergeFunctionBody(stmts, repl, assertStmtsIn)
                    (repl, assertStmts)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(expExpLst = explst, exp = exp) <| stmts, _, _)  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      repl = addTplAssignToRepl(explst, 1, exp, iRepl)
                      (repl, assertStmts) = myMergeFunctionBody(stmts, repl, assertStmtsIn)
                    (repl, assertStmts)
                  end

                  (DAE.STMT_ASSERT(cond = exp, msg = exp1, level = exp2, source = source) <| stmts, _, _)  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      (exp1, _) = VarTransform.replaceExp(exp1, iRepl, NONE())
                      (exp2, _) = VarTransform.replaceExp(exp2, iRepl, NONE())
                      stmt = DAE.STMT_ASSERT(exp, exp1, exp2, source)
                      (repl, assertStmts) = myMergeFunctionBody(stmts, iRepl, _cons(stmt, assertStmtsIn))
                    (repl, assertStmts)
                  end

                  (DAE.STMT_IF(exp = exp, statementLst = DAE.STMT_ASSIGN(exp1 = DAE.CREF(componentRef = cr1), exp = exp1) <|  nil(), else_ = DAE.ELSE(statementLst = DAE.STMT_ASSIGN(exp1 = DAE.CREF(componentRef = cr2), exp = exp2) <|  nil())) <| stmts, _, _) where (ComponentReference.crefEqual(cr1, cr2))  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      (exp1, _) = VarTransform.replaceExp(exp1, iRepl, NONE())
                      (exp2, _) = VarTransform.replaceExp(exp2, iRepl, NONE())
                      repl = VarTransform.addReplacementNoTransitive(iRepl, cr1, DAE.IFEXP(exp, exp1, exp2))
                      (repl, assertStmts) = myMergeFunctionBody(stmts, repl, assertStmtsIn)
                    (repl, assertStmts)
                  end

                  (DAE.STMT_IF(exp = exp, statementLst = DAE.STMT_ASSIGN_ARR(lhs = DAE.CREF(componentRef = cr1), exp = exp1) <|  nil(), else_ = DAE.ELSE(statementLst = DAE.STMT_ASSIGN_ARR(lhs = DAE.CREF(componentRef = cr2), exp = exp2) <|  nil())) <| stmts, _, _) where (ComponentReference.crefEqual(cr1, cr2))  => begin
                      (exp, _) = VarTransform.replaceExp(exp, iRepl, NONE())
                      (exp1, _) = VarTransform.replaceExp(exp1, iRepl, NONE())
                      (exp2, _) = VarTransform.replaceExp(exp2, iRepl, NONE())
                      repl = VarTransform.addReplacementNoTransitive(iRepl, cr1, DAE.IFEXP(exp, exp1, exp2))
                      (repl, assertStmts) = myMergeFunctionBody(stmts, repl, assertStmtsIn)
                    (repl, assertStmts)
                  end
                end
              end
               #=  if a then x := b; else x := c; end if; => x := if a then b else c;
               =#
          (oRepl, assertStmtsOut)
        end

        function addTplAssignToRepl(explst::List{<:DAE.Exp}, indx::ModelicaInteger, iExp::DAE.Exp, iRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local oRepl::VarTransform.VariableReplacements

              oRepl = begin
                  local repl::VarTransform.VariableReplacements
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                  local rest::List{DAE.Exp}
                  local tp::DAE.Type
                @match (explst, indx, iExp, iRepl) begin
                  ( nil(), _, _, _)  => begin
                    iRepl
                  end

                  (DAE.CREF(componentRef = cr, ty = tp) <| rest, _, _, _)  => begin
                      exp = DAE.TSUB(iExp, indx, tp)
                      repl = VarTransform.addReplacementNoTransitive(iRepl, cr, exp)
                    addTplAssignToRepl(rest, indx + 1, iExp, repl)
                  end
                end
              end
          oRepl
        end

        function getFunctionInputsOutputBody(fn::List{<:DAE.Element}, iRepl::VarTransform.VariableReplacements) ::Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}, List{DAE.Statement}, VarTransform.VariableReplacements}
              local oRepl::VarTransform.VariableReplacements = iRepl
              local oBody::List{DAE.Statement} = nil
              local oOutputs::List{DAE.ComponentRef} = nil
              local oInputs::List{DAE.ComponentRef} = nil

              local elt::DAE.Element
              local cr::DAE.ComponentRef
              local binding::Option{DAE.Exp}
              local tp::DAE.Type
              local st::List{DAE.Statement}

              for elt in fn
                _ = begin
                  @match elt begin
                    DAE.VAR(componentRef = cr, direction = DAE.INPUT(__))  => begin
                        oInputs = _cons(cr, oInputs)
                      ()
                    end

                    DAE.VAR(componentRef = cr, direction = DAE.OUTPUT(__), binding = binding)  => begin
                        binding = makeComplexBinding(binding, elt.ty)
                        oRepl = addOptBindingReplacements(cr, binding, oRepl)
                        oOutputs = _cons(cr, oOutputs)
                      ()
                    end

                    DAE.VAR(componentRef = cr, protection = DAE.PROTECTED(__), binding = binding)  => begin
                        tp = ComponentReference.crefTypeFull(cr)
                        @match false = Expression.isArrayType(tp)
                        @match false = Expression.isRecordType(tp)
                        oRepl = addOptBindingReplacements(cr, binding, oRepl)
                      ()
                    end

                    DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(st))  => begin
                        oBody = listAppend(oBody, st)
                      ()
                    end

                    _  => begin
                         #=  use type of cref, since var type is different
                         =#
                         #=  and has no hint on array or record type
                         =#
                        Error.addInternalError("Unknown element: " + DAEDump.dumpElementsStr(list(elt)), sourceInfo())
                      fail()
                    end
                  end
                end
              end
              oInputs = listReverse(oInputs)
              oOutputs = listReverse(oOutputs)
          (oInputs, oOutputs, oBody, oRepl)
        end

         #= Creates a record binding from the given type if the given binding is empty. =#
        function makeComplexBinding(binding::Option{<:DAE.Exp}, ty::DAE.Type) ::Option{DAE.Exp}


              binding = begin
                  local expl::List{DAE.Exp}
                  local strl::List{String}
                  local exp::DAE.Exp
                @match (binding, ty) begin
                  (NONE(), DAE.Type.T_COMPLEX(__))  => begin
                      expl = nil
                      strl = nil
                      for var in listReverse(ty.varLst)
                        () = begin
                          @match var begin
                            DAE.Var.TYPES_VAR(binding = DAE.Binding.EQBOUND(exp = exp))  => begin
                                expl = _cons(exp, expl)
                                strl = _cons(var.name, strl)
                              ()
                            end

                            _  => begin
                                  return
                                ()
                            end
                          end
                        end
                      end
                    SOME(DAE.Exp.RECORD(ClassInf.getStateName(ty.complexClassType), expl, strl, ty))
                  end

                  _  => begin
                      binding
                  end
                end
              end
          binding
        end

        function addOptBindingReplacements(cr::DAE.ComponentRef, binding::Option{<:DAE.Exp}, iRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local oRepl::VarTransform.VariableReplacements

              oRepl = begin
                  local e::DAE.Exp
                @match (cr, binding, iRepl) begin
                  (_, SOME(e), _)  => begin
                    addReplacement(cr, e, iRepl)
                  end

                  (_, NONE(), _)  => begin
                    iRepl
                  end
                end
              end
          oRepl
        end

        function addReplacement(iCr::DAE.ComponentRef, iExp::DAE.Exp, iRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local oRepl::VarTransform.VariableReplacements

              oRepl = begin
                  local tp::DAE.Type
                @match (iCr, iExp, iRepl) begin
                  (DAE.CREF_IDENT(identType = tp), _, _)  => begin
                    VarTransform.addReplacement(iRepl, iCr, iExp)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
          oRepl
        end

         #=
        Author: Frenkel TUD, 2010-05 =#
        function checkInlineType(inIT::DAE.InlineType, fns::Functiontuple) ::Bool
              local outb::Bool

              outb = begin
                  local it::DAE.InlineType
                  local itlst::List{DAE.InlineType}
                  local b::Bool
                @matchcontinue (inIT, fns) begin
                  (it, (_, itlst))  => begin
                      b = listMember(it, itlst)
                    b
                  end

                  _  => begin
                      false
                  end
                end
              end
          outb
        end

         #= extends crefs from records =#
        function extendCrefRecords(inArgmap::List{<:Tuple{<:DAE.ComponentRef, DAE.Exp}}, inCheckCr::HashTableCG.HashTable) ::Tuple{List{Tuple{DAE.ComponentRef, DAE.Exp}}, HashTableCG.HashTable}
              local outCheckCr::HashTableCG.HashTable
              local outArgmap::List{Tuple{DAE.ComponentRef, DAE.Exp}}

              (outArgmap, outCheckCr) = begin
                  local ht::HashTableCG.HashTable
                  local ht1::HashTableCG.HashTable
                  local ht2::HashTableCG.HashTable
                  local ht3::HashTableCG.HashTable
                  local res::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local res1::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local res2::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local new::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local new1::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local c::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                  local e::DAE.Exp
                  local varLst::List{DAE.Var}
                  local expl::List{DAE.Exp}
                  local crlst::List{DAE.ComponentRef}
                  local creftpllst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                @matchcontinue (inArgmap, inCheckCr) begin
                  ( nil(), ht)  => begin
                    (nil, ht)
                  end

                  ((c, DAE.CAST(exp = e, ty = DAE.T_COMPLEX(__))) <| res, ht)  => begin
                      (new1, ht1) = extendCrefRecords(_cons((c, e), res), ht)
                    (new1, ht1)
                  end

                  ((c, e && DAE.CREF(componentRef = cref, ty = DAE.T_COMPLEX(varLst = varLst))) <| res, ht)  => begin
                      (res1, ht1) = extendCrefRecords(res, ht)
                      new = ListUtil.map2(varLst, extendCrefRecords1, c, cref)
                      (new1, ht2) = extendCrefRecords(new, ht1)
                      res2 = listAppend(new1, res1)
                    (_cons((c, e), res2), ht2)
                  end

                  ((c, e && DAE.CREF(componentRef = cref)) <| res, ht)  => begin
                      @match DAE.T_COMPLEX(varLst = varLst) = ComponentReference.crefLastType(cref)
                      (res1, ht1) = extendCrefRecords(res, ht)
                      new = ListUtil.map2(varLst, extendCrefRecords1, c, cref)
                      (new1, ht2) = extendCrefRecords(new, ht1)
                      res2 = listAppend(new1, res1)
                    (_cons((c, e), res2), ht2)
                  end

                  ((c, e && DAE.CALL(expLst = expl, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(varLst = varLst)))) <| res, ht)  => begin
                      (res1, ht1) = extendCrefRecords(res, ht)
                      crlst = ListUtil.map1(varLst, extendCrefRecords2, c)
                      new = ListUtil.threadTuple(crlst, expl)
                      (new1, ht2) = extendCrefRecords(new, ht1)
                      res2 = listAppend(new1, res1)
                    (_cons((c, e), res2), ht2)
                  end

                  ((c, e && DAE.RECORD(exps = expl, ty = DAE.T_COMPLEX(varLst = varLst))) <| res, ht)  => begin
                      (res1, ht1) = extendCrefRecords(res, ht)
                      crlst = ListUtil.map1(varLst, extendCrefRecords2, c)
                      new = ListUtil.threadTuple(crlst, expl)
                      (new1, ht2) = extendCrefRecords(new, ht1)
                      res2 = listAppend(new1, res1)
                    (_cons((c, e), res2), ht2)
                  end

                  ((c, e) <| res, ht)  => begin
                      @match DAE.T_COMPLEX(varLst = varLst) = Expression.typeof(e)
                      crlst = ListUtil.map1(varLst, extendCrefRecords2, c)
                      creftpllst = ListUtil.map1(crlst, Util.makeTuple, c)
                      ht1 = ListUtil.fold(creftpllst, BaseHashTable.add, ht)
                      ht2 = getCheckCref(crlst, ht1)
                      (res1, ht3) = extendCrefRecords(res, ht2)
                    (_cons((c, e), res1), ht3)
                  end

                  ((c, e) <| res, ht)  => begin
                      (res1, ht1) = extendCrefRecords(res, ht)
                    (_cons((c, e), res1), ht1)
                  end
                end
              end
               #= /* All elements of the record have correct type already. No cast needed. */ =#
               #= /* cause of an error somewhere the type of the expression CREF is not equal to the componentreference type
                     this case is needed. */ =#
          (outArgmap, outCheckCr)
        end

        function getCheckCref(inCrefs::List{<:DAE.ComponentRef}, inCheckCr::HashTableCG.HashTable) ::HashTableCG.HashTable
              local outCheckCr::HashTableCG.HashTable

              outCheckCr = begin
                  local ht::HashTableCG.HashTable
                  local ht1::HashTableCG.HashTable
                  local ht2::HashTableCG.HashTable
                  local ht3::HashTableCG.HashTable
                  local rest::List{DAE.ComponentRef}
                  local crlst::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                  local varLst::List{DAE.Var}
                  local creftpllst::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                @matchcontinue (inCrefs, inCheckCr) begin
                  ( nil(), ht)  => begin
                    ht
                  end

                  (cr <| rest, ht)  => begin
                      @match DAE.T_COMPLEX(varLst = varLst) = ComponentReference.crefLastType(cr)
                      crlst = ListUtil.map1(varLst, extendCrefRecords2, cr)
                      ht1 = getCheckCref(crlst, ht)
                      creftpllst = ListUtil.map1(crlst, Util.makeTuple, cr)
                      ht2 = ListUtil.fold(creftpllst, BaseHashTable.add, ht1)
                      ht3 = getCheckCref(rest, ht2)
                    ht3
                  end

                  (_ <| rest, ht)  => begin
                      ht1 = getCheckCref(rest, ht)
                    ht1
                  end
                end
              end
          outCheckCr
        end

         #= helper for extendCrefRecords =#
        function extendCrefRecords1(ev::DAE.Var, c::DAE.ComponentRef, e::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, DAE.Exp}
              local outArg::Tuple{DAE.ComponentRef, DAE.Exp}

              outArg = begin
                  local tp::DAE.Type
                  local name::String
                  local c1::DAE.ComponentRef
                  local e1::DAE.ComponentRef
                  local exp::DAE.Exp
                @matchcontinue (ev, c, e) begin
                  (DAE.TYPES_VAR(name = name, ty = tp), _, _)  => begin
                      c1 = ComponentReference.crefPrependIdent(c, name, nil, tp)
                      e1 = ComponentReference.crefPrependIdent(e, name, nil, tp)
                      exp = Expression.makeCrefExp(e1, tp)
                    (c1, exp)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("Inline.extendCrefRecords1 failed\\n")
                      fail()
                  end
                end
              end
          outArg
        end

         #= helper for extendCrefRecords =#
        function extendCrefRecords2(ev::DAE.Var, c::DAE.ComponentRef) ::DAE.ComponentRef
              local outArg::DAE.ComponentRef

              outArg = begin
                  local tp::DAE.Type
                  local name::String
                  local c1::DAE.ComponentRef
                @matchcontinue (ev, c) begin
                  (DAE.TYPES_VAR(name = name, ty = tp), _)  => begin
                      c1 = ComponentReference.crefPrependIdent(c, name, nil, tp)
                    c1
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("Inline.extendCrefRecords2 failed\\n")
                      fail()
                  end
                end
              end
          outArg
        end

         #= returns the body of a function =#
        function getFunctionBody(p::Absyn.Path, fns::Functiontuple) ::Tuple{List{DAE.Element}, Option{SCode.Comment}}
              local oComment::Option{SCode.Comment}
              local outfn::List{DAE.Element}

              (outfn, oComment) = begin
                  local body::List{DAE.Element}
                  local ftree::DAE.FunctionTree
                  local comment::Option{SCode.Comment}
                @matchcontinue (p, fns) begin
                  (_, (SOME(ftree), _))  => begin
                      @match SOME(DAE.FUNCTION(functions = _cons(DAE.FUNCTION_DEF(body = body), _), comment = comment)) = DAE.AvlTreePathFunction.get(ftree, p)
                    (body, comment)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("Inline.getFunctionBody failed for function: " + AbsynUtil.pathString(p))
                      fail()
                  end
                end
              end
               #=  Error.addMessage(Error.INTERNAL_ERROR, {\"Inline.getFunctionBody failed\"});
               =#
          (outfn, oComment)
        end

         #= returns the right hand side of an assignment from a function =#
        function getRhsExp(inElementList::List{<:DAE.Element}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cdr::List{DAE.Element}
                  local res::DAE.Exp
                @match inElementList begin
                   nil()  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("Inline.getRhsExp failed - cannot inline such a function\\n")
                    fail()
                  end

                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(DAE.STMT_ASSIGN(exp = res) <|  nil())) <| _  => begin
                    res
                  end

                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(DAE.STMT_TUPLE_ASSIGN(exp = res) <|  nil())) <| _  => begin
                    res
                  end

                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(DAE.STMT_ASSIGN_ARR(exp = res) <|  nil())) <| _  => begin
                    res
                  end

                  _ <| cdr  => begin
                      res = getRhsExp(cdr)
                    res
                  end
                end
              end
          outExp
        end

         #= finds DAE.CREF and replaces them with new exps if the cref is in the argmap =#
        function replaceArgs(inExp::DAE.Exp, inTuple::Tuple{<:List{<:Tuple{<:DAE.ComponentRef, DAE.Exp}}, HashTableCG.HashTable, Bool}) ::Tuple{DAE.Exp, Tuple{List{Tuple{DAE.ComponentRef, DAE.Exp}}, HashTableCG.HashTable, Bool}}
              local outTuple::Tuple{List{Tuple{DAE.ComponentRef, DAE.Exp}}, HashTableCG.HashTable, Bool}
              local outExp::DAE.Exp

              (outExp, outTuple) = begin
                  local cref::DAE.ComponentRef
                  local firstCref::DAE.ComponentRef
                  local argmap::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                  local e::DAE.Exp
                  local path::Absyn.Path
                  local expLst::List{DAE.Exp}
                  local tuple_::Bool
                  local b::Bool
                  local isImpure::Bool
                  local isFunctionPointerCall::Bool
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local inlineType::DAE.InlineType
                  local tc::DAE.TailCall
                  local checkcr::HashTableCG.HashTable
                  local replacedfailed::Bool
                @matchcontinue (inExp, inTuple) begin
                  (DAE.CREF(componentRef = cref), (argmap, checkcr, true))  => begin
                      e = getExpFromArgMap(argmap, cref)
                      (e, _) = ExpressionSimplify.simplify(e)
                    (e, inTuple)
                  end

                  (DAE.CREF(componentRef = cref), (argmap, checkcr, true)) where (BaseHashTable.hasKey(ComponentReference.crefFirstCref(cref), checkcr))  => begin
                    (inExp, (argmap, checkcr, false))
                  end

                  (DAE.CREF(componentRef = cref), (argmap, checkcr, true))  => begin
                      firstCref = ComponentReference.crefFirstCref(cref)
                      @match nil = ComponentReference.crefSubs(firstCref)
                      e = getExpFromArgMap(argmap, firstCref)
                      while ! ComponentReference.crefIsIdent(cref)
                        cref = ComponentReference.crefRest(cref)
                        @match nil = ComponentReference.crefSubs(cref)
                        e = DAE.RSUB(e, -1, ComponentReference.crefFirstIdent(cref), ComponentReference.crefType(cref))
                      end
                    (e, inTuple)
                  end

                  (DAE.CREF(componentRef = cref), (argmap, checkcr, true))  => begin
                      getExpFromArgMap(argmap, ComponentReference.crefStripSubs(ComponentReference.crefFirstCref(cref)))
                    (inExp, (argmap, checkcr, false))
                  end

                  (DAE.UNBOX(DAE.CALL(path, expLst, DAE.CALL_ATTR(_, tuple_, false, isImpure, _, inlineType, tc)), ty), (argmap, checkcr, true))  => begin
                      cref = ComponentReference.pathToCref(path)
                      @match (@match DAE.CREF(componentRef = cref, ty = ty2) = e) = getExpFromArgMap(argmap, cref)
                      path = ComponentReference.crefToPath(cref)
                      expLst = ListUtil.map(expLst, Expression.unboxExp)
                      b = Expression.isBuiltinFunctionReference(e)
                      isFunctionPointerCall = Types.isFunctionReferenceVar(ty2)
                      e = DAE.CALL(path, expLst, DAE.CALL_ATTR(ty, tuple_, b, isImpure, isFunctionPointerCall, inlineType, tc))
                      (e, _) = ExpressionSimplify.simplify(e)
                    (e, inTuple)
                  end

                  (e && DAE.UNBOX(DAE.CALL(path, _, DAE.CALL_ATTR(builtin = false)), _), (argmap, checkcr, true))  => begin
                      cref = ComponentReference.pathToCref(path)
                      @match true = BaseHashTable.hasKey(cref, checkcr)
                    (e, (argmap, checkcr, false))
                  end

                  (DAE.CALL(path, expLst, DAE.CALL_ATTR(DAE.T_METATYPE(__), tuple_, false, isImpure, _, _, tc)), (argmap, checkcr, true))  => begin
                      cref = ComponentReference.pathToCref(path)
                      @match (@match DAE.CREF(componentRef = cref, ty = ty) = e) = getExpFromArgMap(argmap, cref)
                      path = ComponentReference.crefToPath(cref)
                      expLst = ListUtil.map(expLst, Expression.unboxExp)
                      b = Expression.isBuiltinFunctionReference(e)
                      (ty2, inlineType) = functionReferenceType(ty)
                      isFunctionPointerCall = Types.isFunctionReferenceVar(ty2)
                      e = DAE.CALL(path, expLst, DAE.CALL_ATTR(ty2, tuple_, b, isImpure, isFunctionPointerCall, inlineType, tc))
                      e = boxIfUnboxedFunRef(e, ty)
                      (e, _) = ExpressionSimplify.simplify(e)
                    (e, inTuple)
                  end

                  (e && DAE.CALL(path, _, DAE.CALL_ATTR(ty = DAE.T_METATYPE(__), builtin = false)), (argmap, checkcr, true))  => begin
                      cref = ComponentReference.pathToCref(path)
                      @match true = BaseHashTable.hasKey(cref, checkcr)
                    (e, (argmap, checkcr, false))
                  end

                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
               #=  We have something like v[i].re and v is in the inputs... So we fail to inline.
               =#
               #=  TODO: Use the inlineType of the function reference!
               =#
          (outExp, outTuple)
        end

         #= Replacing a function pointer with a regular function means that you:
          (1) Need to unbox all inputs
          (2) Need to box the output if it was not done before
          This function handles (2)
           =#
        function boxIfUnboxedFunRef(iexp::DAE.Exp, ty::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local t::DAE.Type
                  local exp::DAE.Exp
                @match (iexp, ty) begin
                  (exp, DAE.T_FUNCTION_REFERENCE_FUNC(functionType = DAE.T_FUNCTION(funcResultType = t)))  => begin
                      exp = if Types.isBoxedType(t)
                            exp
                          else
                            DAE.BOX(exp)
                          end
                    exp
                  end

                  _  => begin
                      iexp
                  end
                end
              end
          outExp
        end

         #= Retrieves the ExpType that the call should have (this changes if the replacing
          function does not return a boxed value).
          We also return the inline type of the new call. =#
        function functionReferenceType(ty1::DAE.Type) ::Tuple{DAE.Type, DAE.InlineType}
              local inlineType::DAE.InlineType
              local ty2::DAE.Type

              (ty2, inlineType) = begin
                  local ty::DAE.Type
                @match ty1 begin
                  DAE.T_FUNCTION_REFERENCE_FUNC(functionType = DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(inline = inlineType), funcResultType = ty))  => begin
                    (Types.simplifyType(ty), inlineType)
                  end

                  _  => begin
                      (ty1, DAE.NO_INLINE())
                  end
                end
              end
          (ty2, inlineType)
        end

         #= returns the exp from the given argmap with the given key =#
        function getExpFromArgMap(inArgMap::List{<:Tuple{<:DAE.ComponentRef, DAE.Exp}}, inComponentRef::DAE.ComponentRef) ::DAE.Exp
              local outExp::DAE.Exp

              local arg::Tuple{DAE.ComponentRef, DAE.Exp}
              local subs::List{DAE.Subscript}
              local key::DAE.ComponentRef
              local cref::DAE.ComponentRef
              local exp::DAE.Exp

              subs = ComponentReference.crefSubs(inComponentRef)
              key = ComponentReference.crefStripSubs(inComponentRef)
              for arg in inArgMap
                (cref, exp) = arg
                if ComponentReference.crefEqual(cref, key)
                  try
                    outExp = Expression.applyExpSubscripts(exp, subs)
                  catch
                    continue
                  end
                  return outExp
                end
              end
              if Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("Inline.getExpFromArgMap failed with empty argmap and cref: " + ComponentReference.printComponentRefStr(inComponentRef))
              end
              fail()
          outExp
        end

         #= returns the crefs of vars that are inputs, wild if not input =#
        function getInputCrefs(inElement::DAE.Element) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local cref::DAE.ComponentRef
                @match inElement begin
                  DAE.VAR(componentRef = cref, direction = DAE.INPUT(__))  => begin
                    cref
                  end

                  _  => begin
                      DAE.WILD()
                  end
                end
              end
          outComponentRef
        end

         #= returns false if the given cref is a wild =#
        function removeWilds(inComponentRef::DAE.ComponentRef) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inComponentRef begin
                  DAE.WILD(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outBoolean
        end

         #= Print what kind of inline we have =#
        function printInlineTypeStr(it::DAE.InlineType) ::String
              local str::String

              str = begin
                @match it begin
                  DAE.NO_INLINE(__)  => begin
                    "No inline"
                  end

                  DAE.AFTER_INDEX_RED_INLINE(__)  => begin
                    "Inline after index reduction"
                  end

                  DAE.EARLY_INLINE(__)  => begin
                    "Inline as soon as possible"
                  end

                  DAE.BUILTIN_EARLY_INLINE(__)  => begin
                    "Inline as soon as possible, even if inlining is globally disabled"
                  end

                  DAE.NORM_INLINE(__)  => begin
                    "Inline before index reduction"
                  end

                  DAE.DEFAULT_INLINE(__)  => begin
                    "Inline if necessary"
                  end
                end
              end
          str
        end

         #=
          Takes a residual or equality equation, then
          simplifies, inlines and simplifies again
         =#
        function simplifyAndInlineEquationExp(inExp::DAE.EquationExp, fns::Functiontuple, inSource::DAE.ElementSource) ::Tuple{DAE.EquationExp, DAE.ElementSource}
              local source::DAE.ElementSource
              local exp::DAE.EquationExp

              (exp, source) = ExpressionSimplify.simplifyAddSymbolicOperation(inExp, inSource)
              (exp, source) = inlineEquationExp(exp, (fns) -> inlineCall(fns = fns), source)
          (exp, source)
        end

         #=
          Takes a residual or equality equation, then
          simplifies, inlines and simplifies again
         =#
        function simplifyAndForceInlineEquationExp(inExp::DAE.EquationExp, fns::Functiontuple, inSource::DAE.ElementSource) ::Tuple{DAE.EquationExp, DAE.ElementSource}
              local source::DAE.ElementSource
              local exp::DAE.EquationExp

              (exp, source) = ExpressionSimplify.simplifyAddSymbolicOperation(inExp, inSource)
              (exp, source) = inlineEquationExp(exp, fn -> forceInlineCall(fns = fns, visitedPaths = AvlSetPath.Tree.EMPTY()), source)
          (exp, source)
        end

         #=
          Takes a residual or equality equation, then
          simplifies, inlines and simplifies again
         =#
        function inlineEquationExp(inExp::DAE.EquationExp, fn::Func, inSource::DAE.ElementSource) ::Tuple{DAE.EquationExp, DAE.ElementSource}
              local source::DAE.ElementSource
              local outExp::DAE.EquationExp

              (outExp, source) = begin
                  local changed::Bool
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e1::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2::DAE.Exp
                  local e2_1::DAE.Exp
                  local eq2::DAE.EquationExp
                  local fns::Functiontuple
                  local assrtLst::List{DAE.Statement}
                @match inExp begin
                  DAE.PARTIAL_EQUATION(e)  => begin
                      (e_1, _) = Expression.traverseExpBottomUp(e, fn, nil)
                      changed = ! referenceEq(e, e_1)
                      eq2 = DAE.PARTIAL_EQUATION(e_1)
                      source = ElementSource.condAddSymbolicTransformation(changed, inSource, DAE.OP_INLINE(inExp, eq2))
                      (eq2, source) = ExpressionSimplify.condSimplifyAddSymbolicOperation(changed, eq2, source)
                    (eq2, source)
                  end

                  DAE.RESIDUAL_EXP(e)  => begin
                      (e_1, _) = Expression.traverseExpBottomUp(e, fn, nil)
                      changed = ! referenceEq(e, e_1)
                      eq2 = DAE.RESIDUAL_EXP(e_1)
                      source = ElementSource.condAddSymbolicTransformation(changed, inSource, DAE.OP_INLINE(inExp, eq2))
                      (eq2, source) = ExpressionSimplify.condSimplifyAddSymbolicOperation(changed, eq2, source)
                    (eq2, source)
                  end

                  DAE.EQUALITY_EXPS(e1, e2)  => begin
                      (e1_1, _) = Expression.traverseExpBottomUp(e1, fn, nil)
                      (e2_1, _) = Expression.traverseExpBottomUp(e2, fn, nil)
                      changed = ! (referenceEq(e1, e1_1) && referenceEq(e2, e2_1))
                      eq2 = DAE.EQUALITY_EXPS(e1_1, e2_1)
                      source = ElementSource.condAddSymbolicTransformation(changed, inSource, DAE.OP_INLINE(inExp, eq2))
                      (eq2, source) = ExpressionSimplify.condSimplifyAddSymbolicOperation(changed, eq2, source)
                    (eq2, source)
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Inline.inlineEquationExp failed"))
                      fail()
                  end
                end
              end
          (outExp, source)
        end

        function getReplacementCheckComplex(repl::VarTransform.VariableReplacements, cr::DAE.ComponentRef, ty::DAE.Type) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local vars::List{DAE.Var}
                  local crs::List{DAE.ComponentRef}
                  local strs::List{String}
                  local exps::List{DAE.Exp}
                  local path::Absyn.Path
                @matchcontinue (repl, cr, ty) begin
                  (_, _, _)  => begin
                    VarTransform.getReplacement(repl, cr)
                  end

                  (_, _, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path), varLst = vars))  => begin
                      crs = ListUtil.map1(ListUtil.map(vars, Types.varName), ComponentReference.appendStringCref, cr)
                      exps = ListUtil.map1r(crs, VarTransform.getReplacement, repl)
                    DAE.CALL(path, exps, DAE.CALL_ATTR(ty, false, false, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
                  end
                end
              end
          exp
        end

        function getInlineHashTableVarTransform() ::Tuple{HashTableCG.HashTable, VarTransform.VariableReplacements}
              local repl::VarTransform.VariableReplacements
              local ht::HashTableCG.HashTable

              local opt::Option{Tuple{HashTableCG.HashTable, VarTransform.VariableReplacements}}
              local regRepl::HashTable2.HashTable
              local invRepl::HashTable3.HashTable

              opt = getGlobalRoot(Global.inlineHashTable)
              (ht, repl) = begin
                @match opt begin
                  SOME((ht, repl && VarTransform.REPLACEMENTS(regRepl, invRepl)))  => begin
                       #=  Always stored with n=0, etc with the first global root
                       =#
                      BaseHashTable.clearAssumeNoDelete(ht)
                      BaseHashTable.clearAssumeNoDelete(regRepl)
                      BaseHashTable.clearAssumeNoDelete(invRepl)
                    (ht, repl)
                  end

                  _  => begin
                        ht = HashTableCG.emptyHashTable()
                        repl = VarTransform.emptyReplacements()
                        setGlobalRoot(Global.inlineHashTable, SOME((ht, repl)))
                      (ht, repl)
                  end
                end
              end
          (ht, repl)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

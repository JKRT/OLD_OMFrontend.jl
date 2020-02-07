  module Algorithm


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

        import DAE

        import SCode

        import DAETraverse

        import Debug

        import ElementSource

        import Error

        import Expression

        import CrefForHashTable

        import Flags

        import ListUtil
        import SCodeUtil

        import SCodeDump

        import Types

        import Util

         #= Returns true if algorithm is empty, i.e. no statements =#
        function algorithmEmpty(alg::DAE.Algorithm) ::Bool
              local empty::Bool

              empty = begin
                @match alg begin
                  DAE.ALGORITHM_STMTS( nil())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          empty
        end

         #= returns true if statement is a reinit =#
        function isReinitStatement(stmt::DAE.Statement) ::Bool
              local res::Bool

              res = begin
                @match stmt begin
                  DAE.STMT_REINIT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if statement is NOT an assert =#
        function isNotAssertStatement(stmt::DAE.Statement) ::Bool
              local res::Bool

              res = begin
                @match stmt begin
                  DAE.STMT_ASSERT(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          res
        end

         #= Used to optimize assignments to NORETCALL if applicable =#
        function makeAssignmentNoTypeCheck(ty::DAE.Type, lhs::DAE.Exp, rhs::DAE.Exp, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                @match (ty, lhs, rhs, source) begin
                  (_, DAE.CREF(componentRef = DAE.WILD(__)), _, _)  => begin
                    DAE.STMT_NORETCALL(rhs, source)
                  end

                  (_, DAE.PATTERN(pattern = DAE.PAT_WILD(__)), _, _)  => begin
                    DAE.STMT_NORETCALL(rhs, source)
                  end

                  _  => begin
                      DAE.STMT_ASSIGN(ty, lhs, rhs, source)
                  end
                end
              end
          outStatement
        end

         #= Used to optimize assignments to NORETCALL if applicable =#
        function makeArrayAssignmentNoTypeCheck(ty::DAE.Type, lhs::DAE.Exp, rhs::DAE.Exp, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                @match (ty, lhs, rhs, source) begin
                  (_, DAE.CREF(DAE.WILD(__)), _, _)  => begin
                    DAE.STMT_NORETCALL(rhs, source)
                  end

                  _  => begin
                      DAE.STMT_ASSIGN_ARR(ty, lhs, rhs, source)
                  end
                end
              end
          outStatement
        end

         #= Used to optimize assignments to NORETCALL if applicable =#
        function makeTupleAssignmentNoTypeCheck(ty::DAE.Type, lhs::List{<:DAE.Exp}, rhs::DAE.Exp, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              local b1::Bool
              local b2::Bool

              b1 = ListUtil.mapBoolAnd(lhs, Expression.isWild)
              b2 = ListUtil.mapBoolAnd(ListUtil.restOrEmpty(lhs), Expression.isWild)
              outStatement = makeTupleAssignmentNoTypeCheck2(b1, b2, ty, lhs, rhs, source)
          outStatement
        end

        function makeTupleAssignmentNoTypeCheck2(allWild::Bool, singleAssign::Bool, ty::DAE.Type, lhs::List{<:DAE.Exp}, rhs::DAE.Exp, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local ty1::DAE.Type
                  local lhs1::DAE.Exp
                  local cr::DAE.ComponentRef
                @match (allWild, singleAssign, ty, lhs, rhs, source) begin
                  (true, _, _, _, _, _)  => begin
                    DAE.STMT_NORETCALL(rhs, source)
                  end

                  (_, true, DAE.T_TUPLE(types = ty1 && DAE.T_ARRAY(__) <| _), lhs1 <| _, _, _)  => begin
                    DAE.STMT_ASSIGN_ARR(ty1, lhs1, DAE.TSUB(rhs, 1, ty1), source)
                  end

                  (_, true, DAE.T_TUPLE(types = ty1 <| _), lhs1 <| _, _, _)  => begin
                    DAE.STMT_ASSIGN(ty1, lhs1, DAE.TSUB(rhs, 1, ty1), source)
                  end

                  _  => begin
                      DAE.STMT_TUPLE_ASSIGN(ty, lhs, rhs, source)
                  end
                end
              end
          outStatement
        end

         #= This function creates an `DAE.STMT_ASSIGN\\' construct, and checks that the
          assignment is semantically valid, which means that the component
          being assigned is not constant, and that the types match.
          LS: Added call to getPropType and isPropAnyConst instead of
          having PROP in the rules. Otherwise rules must be repeated because of
          combinations with PROP_TUPLE =#
        function makeAssignment(inExp1::DAE.Exp, inProperties2::DAE.Properties, inExp3::DAE.Exp, inProperties4::DAE.Properties, inAttributes::DAE.Attributes, initial_::SCode.Initial, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local lhs_str::String
                  local rhs_str::String
                  local lt_str::String
                  local rt_str::String
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local lprop::DAE.Properties
                  local rprop::DAE.Properties
                  local lhprop::DAE.Properties
                  local rhprop::DAE.Properties
                  local cr::DAE.ComponentRef
                  local lt::DAE.Type
                  local rt::DAE.Type
                  local direction::Absyn.Direction
                  local info::SourceInfo
                @matchcontinue (inExp1, inProperties2, inExp3, inProperties4, inAttributes, initial_, source) begin
                  (DAE.CREF(componentRef = DAE.WILD(__)), _, rhs, _, _, _, _)  => begin
                    DAE.STMT_NORETCALL(rhs, source)
                  end

                  (lhs && DAE.CREF(componentRef = cr), lhprop, rhs, rhprop, _, SCode.NON_INITIAL(__), _)  => begin
                      @match DAE.C_PARAM() = Types.propAnyConst(lhprop)
                      @match true = CrefForHashTable.isRecord(cr)
                      outStatement = makeAssignment2(lhs, lhprop, rhs, rhprop, source)
                    outStatement
                  end

                  (lhs, lprop, rhs, _, _, SCode.NON_INITIAL(__), _)  => begin
                      @match DAE.C_PARAM() = Types.propAnyConst(lprop)
                      lhs_str = CrefForHashTable.printExpStr(lhs)
                      rhs_str = CrefForHashTable.printExpStr(rhs)
                      Error.addSourceMessage(Error.ASSIGN_PARAM_ERROR, list(lhs_str, rhs_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end

                  (lhs, _, _, _, DAE.ATTR(variability = SCode.CONST(__)), _, _)  => begin
                      lhs_str = CrefForHashTable.printExpStr(lhs)
                      Error.addSourceMessage(Error.ASSIGN_READONLY_ERROR, list("constant", lhs_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end

                  (lhs, lhprop, rhs, rhprop, _, SCode.INITIAL(__), _)  => begin
                      @match DAE.C_PARAM() = Types.propAnyConst(lhprop)
                      outStatement = makeAssignment2(lhs, lhprop, rhs, rhprop, source)
                    outStatement
                  end

                  (lhs, lhprop, rhs, rhprop, DAE.ATTR(__), _, _)  => begin
                      @match DAE.C_VAR() = Types.propAnyConst(lhprop)
                      outStatement = makeAssignment2(lhs, lhprop, rhs, rhprop, source)
                    outStatement
                  end

                  (lhs, lprop, rhs, rprop, _, _, _)  => begin
                      lt = Types.getPropType(lprop)
                      rt = Types.getPropType(rprop)
                      @match false = Types.equivtypes(lt, rt)
                      lhs_str = CrefForHashTable.printExpStr(lhs)
                      rhs_str = CrefForHashTable.printExpStr(rhs)
                      lt_str = Types.unparseTypeNoAttr(lt)
                      rt_str = Types.unparseTypeNoAttr(rt)
                      info = ElementSource.getElementSourceFileInfo(source)
                      Types.typeErrorSanityCheck(lt_str, rt_str, info)
                      Error.addSourceMessage(Error.ASSIGN_TYPE_MISMATCH_ERROR, list(lhs_str, rhs_str, lt_str, rt_str), info)
                    fail()
                  end

                  (lhs, _, rhs, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Algorithm.makeAssignment failed")
                      Debug.trace("    ")
                      Debug.trace(CrefForHashTable.printExpStr(lhs))
                      Debug.trace(" := ")
                      Debug.traceln(CrefForHashTable.printExpStr(rhs))
                    fail()
                  end
                end
              end
               #=  assign to parameter in algorithm okay if record
               =#
               #=  assign to parameter in algorithm produce error
               =#
               #=  assignment to a constant, report error
               =#
               #=  assignment to parameter ok in initial algorithm
               =#
               #= /* report an error */ =#
               #= /* failing */ =#
          outStatement
        end

         #= Help function to makeAssignment =#
        function makeAssignment2(lhs::DAE.Exp, lhprop::DAE.Properties, rhs::DAE.Exp, rhprop::DAE.Properties, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local c::DAE.ComponentRef
                  local rhs_1::DAE.Exp
                  local e3::DAE.Exp
                  local e1::DAE.Exp
                  local t::DAE.Type
                  local ty::DAE.Type
                  local ea2::List{DAE.Exp}
                @match lhs begin
                  DAE.CREF(__) where (! Types.isPropArray(lhprop))  => begin
                      rhs_1 = Types.matchProp(rhs, rhprop, lhprop, true)
                      t = getPropExpType(lhprop)
                      _ = begin
                        @match rhs_1 begin
                          DAE.CALL(attr = DAE.CALL_ATTR(builtin = true), path = Absyn.IDENT("listAppend"), expLst = e1 && DAE.CREF(__) <| _) where (Expression.expEqual(lhs, e1))  => begin
                              if Flags.isSet(Flags.LIST_REVERSE_WRONG_ORDER) && ! max(SCodeUtil.commentHasBooleanNamedAnnotation(comment, "__OpenModelica_DisableListAppendWarning") for comment in ElementSource.getCommentsFromSource(source))
                                Error.addSourceMessage(Error.LIST_REVERSE_WRONG_ORDER, list(CrefForHashTable.printExpStr(e1)), ElementSource.getElementSourceFileInfo(source))
                                fail()
                              end
                            ()
                          end

                          _  => begin
                              ()
                          end
                        end
                      end
                    DAE.STMT_ASSIGN(t, lhs, rhs_1, source)
                  end

                  DAE.CREF(__)  => begin
                      (rhs_1, _) = Types.matchProp(rhs, rhprop, lhprop, false)
                      ty = Types.getPropType(lhprop)
                      t = Types.simplifyType(ty)
                    DAE.STMT_ASSIGN_ARR(t, lhs, rhs_1, source)
                  end

                  e3 && DAE.ASUB(_, _)  => begin
                      (rhs_1, _) = Types.matchProp(rhs, rhprop, lhprop, true)
                      t = getPropExpType(lhprop)
                    DAE.STMT_ASSIGN(t, e3, rhs_1, source)
                  end
                end
              end
               #= /* TODO: Use this when we have fixed states in BackendDAE .lower(...)
                      case (e1 as DAE.CALL(Absyn.IDENT(\"der\"), {DAE.CREF(_, _)}, _, _, _), lhprop, rhs, rhprop)
                    equation
                      (rhs_1, _) = Types.matchProp(rhs, rhprop, lhprop);
                      false = Types.isPropArray(lhprop);
                      t = getPropExpType(lhprop);
                    then
                      DAE.STMT_ASSIGN(t, e1, rhs_1);
                    */ =#
               #=  guard Types.isPropArray(lhprop)
               =#
               #= /* Don't duplicate errors */ =#
               #= false = Types.isPropArray(lhprop);
               =#
          outStatement
        end

        function makeSimpleAssignment(inTpl::Tuple{<:DAE.Exp, DAE.Exp}, source::DAE.ElementSource) ::DAE.Statement
              local outStmt::DAE.Statement

              local e1::DAE.Exp
              local e2::DAE.Exp
              local tp::DAE.Type

              @match (e1, e2) = inTpl
              @match DAE.CREF(ty = tp) = e1
              outStmt = DAE.STMT_ASSIGN(tp, e1, e2, source)
          outStmt
        end

        function makeAssignmentsList(lhsExps::List{<:DAE.Exp}, lhsProps::List{<:DAE.Properties}, rhsExps::List{<:DAE.Exp}, rhsProps::List{<:DAE.Properties}, attributes::DAE.Attributes, initial_::SCode.Initial, source::DAE.ElementSource) ::List{DAE.Statement}
              local assignments::List{DAE.Statement}

              assignments = begin
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local rest_lhs::List{DAE.Exp}
                  local rest_rhs::List{DAE.Exp}
                  local lhs_prop::DAE.Properties
                  local rhs_prop::DAE.Properties
                  local rest_lhs_prop::List{DAE.Properties}
                  local rest_rhs_prop::List{DAE.Properties}
                  local ass::DAE.Statement
                  local rest_ass::List{DAE.Statement}
                @match (lhsExps, lhsProps, rhsExps, rhsProps, attributes, initial_, source) begin
                  ( nil(),  nil(), _, _, _, _, _)  => begin
                    nil
                  end

                  (DAE.CREF(componentRef = DAE.WILD(__)) <| rest_lhs, _ <| rest_lhs_prop, _ <| rest_rhs, _ <| rest_rhs_prop, _, _, _)  => begin
                    makeAssignmentsList(rest_lhs, rest_lhs_prop, rest_rhs, rest_rhs_prop, attributes, initial_, source)
                  end

                  (lhs <| rest_lhs, lhs_prop <| rest_lhs_prop, rhs <| rest_rhs, rhs_prop <| rest_rhs_prop, _, _, _)  => begin
                      ass = makeAssignment(lhs, lhs_prop, rhs, rhs_prop, attributes, initial_, source)
                      rest_ass = makeAssignmentsList(rest_lhs, rest_lhs_prop, rest_rhs, rest_rhs_prop, attributes, initial_, source)
                    _cons(ass, rest_ass)
                  end
                end
              end
               #= /* rhs does not need to be empty */ =#
          assignments
        end

         #= @author: adrpo
         check if the parameters on rhs have fixed = false
         and fail otherwise =#
        function checkLHSWritable(lhs::List{<:DAE.Exp}, props::List{<:DAE.Properties}, rhs::DAE.Exp, source::DAE.ElementSource)
              local ty::DAE.Type
              local i::ModelicaInteger = 1
              local c::String
              local l::String
              local r::String

              for p in props
                _ = begin
                  @match p begin
                    DAE.PROP(constFlag = DAE.C_VAR(__))  => begin
                      ()
                    end

                    DAE.PROP(_, DAE.C_CONST(__))  => begin
                        l = stringAppendList(list("(", stringDelimitList(ListUtil.map(lhs, CrefForHashTable.printExpStr), ", "), ")"))
                        r = CrefForHashTable.printExpStr(rhs)
                        Error.addSourceMessage(Error.ASSIGN_CONSTANT_ERROR, list(l, r), ElementSource.getElementSourceFileInfo(source))
                        fail()
                      ()
                    end

                    DAE.PROP(ty, DAE.C_PARAM(__))  => begin
                        if Types.getFixedVarAttributeParameterOrConstant(ty)
                          l = stringAppendList(list("(", stringDelimitList(ListUtil.map(lhs, CrefForHashTable.printExpStr), ", "), ")"))
                          r = CrefForHashTable.printExpStr(rhs)
                          c = CrefForHashTable.printExpStr(listGet(lhs, i))
                          Error.addSourceMessage(Error.ASSIGN_PARAM_FIXED_ERROR, list(c, l, r), ElementSource.getElementSourceFileInfo(source))
                          fail()
                        end
                      ()
                    end

                    DAE.PROP_TUPLE(_, _)  => begin
                      ()
                    end
                  end
                end
                i = i + 1
              end
               #=  tuples? TODO! FIXME! can we get tuple here? maybe only for MetaModelica
               =#
        end

         #= This function creates an `DAE.STMT_TUPLE_ASSIGN\\' construct, and checks that the
          assignment is semantically valid, which means that the component
          being assigned is not constant, and that the types match. =#
        function makeTupleAssignment(inExpExpLst::List{<:DAE.Exp}, inTypesPropertiesLst::List{<:DAE.Properties}, inExp::DAE.Exp, inProperties::DAE.Properties, initial_::SCode.Initial, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local bvals::List{DAE.Const}
                  local sl::List{String}
                  local s::String
                  local lhs_str::String
                  local rhs_str::String
                  local str1::String
                  local str2::String
                  local strInitial::String
                  local lhs::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local lprop::List{DAE.Properties}
                  local lhprops::List{DAE.Properties}
                  local rhs::DAE.Exp
                  local rprop::DAE.Properties
                  local lhrtypes::List{DAE.Type}
                  local tpl::List{DAE.Type}
                  local clist::List{DAE.TupleConst}
                  local ty::DAE.Type
                  local constVar::DAE.Const
                @matchcontinue (inExpExpLst, inTypesPropertiesLst, inExp, inProperties, initial_, source) begin
                  (lhs, lprop, rhs, _, _, _)  => begin
                      bvals = ListUtil.map(lprop, Types.propAnyConst)
                      @match DAE.C_CONST() = ListUtil.reduce(bvals, Types.constOr)
                      sl = ListUtil.map(lhs, CrefForHashTable.printExpStr)
                      s = stringDelimitList(sl, ", ")
                      lhs_str = stringAppendList(list("(", s, ")"))
                      rhs_str = CrefForHashTable.printExpStr(rhs)
                      Error.addSourceMessage(Error.ASSIGN_CONSTANT_ERROR, list(lhs_str, rhs_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end

                  (lhs, lprop, rhs, _, SCode.NON_INITIAL(__), _)  => begin
                      bvals = ListUtil.map(lprop, Types.propAnyConst)
                      @match DAE.C_PARAM() = ListUtil.reduce(bvals, Types.constOr)
                      sl = ListUtil.map(lhs, CrefForHashTable.printExpStr)
                      s = stringDelimitList(sl, ", ")
                      lhs_str = stringAppendList(list("(", s, ")"))
                      rhs_str = CrefForHashTable.printExpStr(rhs)
                      Error.addSourceMessage(Error.ASSIGN_PARAM_ERROR, list(lhs_str, rhs_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end

                  (expl, lhprops, rhs, DAE.PROP(type_ = ty && DAE.T_TUPLE(types = tpl)), _, _)  => begin
                      checkLHSWritable(expl, lhprops, rhs, source)
                      lhrtypes = ListUtil.map(lhprops, Types.getPropType)
                      Types.matchTypeTupleCall(rhs, tpl, lhrtypes)
                    makeTupleAssignmentNoTypeCheck(ty, expl, rhs, source)
                  end

                  (expl, lhprops, rhs, DAE.PROP_TUPLE(type_ = ty && DAE.T_TUPLE(types = tpl), tupleConst = DAE.TUPLE_CONST(__)), _, _)  => begin
                      checkLHSWritable(expl, lhprops, rhs, source)
                      lhrtypes = ListUtil.map(lhprops, Types.getPropType)
                      Types.matchTypeTupleCall(rhs, tpl, lhrtypes)
                    makeTupleAssignmentNoTypeCheck(ty, expl, rhs, source)
                  end

                  (lhs, lprop, rhs, rprop, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      sl = ListUtil.map(lhs, CrefForHashTable.printExpStr)
                      s = stringDelimitList(sl, ", ")
                      lhs_str = stringAppendList(list("(", s, ")"))
                      rhs_str = CrefForHashTable.printExpStr(rhs)
                      str1 = stringDelimitList(ListUtil.map(lprop, Types.printPropStr), ", ")
                      str2 = Types.printPropStr(rprop)
                      strInitial = SCodeDump.printInitialStr(initial_)
                      Debug.traceln("- Algorithm.makeTupleAssignment failed on: \\n\\t" + lhs_str + " = " + rhs_str + "\\n\\tprops lhs: (" + str1 + ") =  props rhs: " + str2 + "\\n\\tin " + strInitial + " section")
                    fail()
                  end
                end
              end
               #=  a normal prop in rhs that contains a T_TUPLE!
               =#
               #= /* Don\\'t use new rhs\\', since type conversions of
                          several output args are not clearly defined. */ =#
               #=  a tuple in rhs
               =#
               #= /* Don\\'t use new rhs\\', since type conversions of several output args are not clearly defined. */ =#
          outStatement
        end

         #= Returns the expression type for a given Properties by calling
          getTypeExpType. Used by makeAssignment. =#
        function getPropExpType(p::DAE.Properties) ::DAE.Type
              local t::DAE.Type

              local ty::DAE.Type

              ty = Types.getPropType(p)
              t = Types.simplifyType(ty)
          t
        end

         #= This function creates an `DAE.STMT_IF\\' construct, checking that the types
          of the parts are correct. Else part is generated using the makeElse
          function. =#
        function makeIf(inExp::DAE.Exp, inProperties::DAE.Properties, inTrueBranch::List{<:DAE.Statement}, inElseIfBranches::List{<:Tuple{<:DAE.Exp, DAE.Properties, List{<:DAE.Statement}}}, inElseBranch::List{<:DAE.Statement}, source::DAE.ElementSource) ::List{DAE.Statement}
              local outStatements::List{DAE.Statement}

              outStatements = begin
                  local else_::DAE.Else
                  local e::DAE.Exp
                  local tb::List{DAE.Statement}
                  local fb::List{DAE.Statement}
                  local eib::List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}
                  local e_str::String
                  local t_str::String
                  local t::DAE.Type
                  local prop::DAE.Properties
                @matchcontinue (inExp, inProperties, inTrueBranch, inElseIfBranches, inElseBranch, source) begin
                  (DAE.BCONST(true), _, tb, _, _, _)  => begin
                    tb
                  end

                  (DAE.BCONST(false), _, _,  nil(), fb, _)  => begin
                    fb
                  end

                  (DAE.BCONST(false), _, _, (e, prop, tb) <| eib, fb, _)  => begin
                    makeIf(e, prop, tb, eib, fb, source)
                  end

                  (e, DAE.PROP(type_ = t), tb, eib, fb, _)  => begin
                      (e, _) = Types.matchType(e, t, DAE.T_BOOL_DEFAULT, true)
                      else_ = makeElse(eib, fb, source)
                    list(DAE.STMT_IF(e, tb, else_, source))
                  end

                  (e, DAE.PROP(type_ = t), _, _, _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      Error.addSourceMessage(Error.IF_CONDITION_TYPE_ERROR, list(e_str, t_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end
                end
              end
          outStatements
        end

         #=
          Create an if-statement from branches, optimizing as needed. =#
        function makeIfFromBranches(branches::List{<:Tuple{<:DAE.Exp, List{<:DAE.Statement}}}, source::DAE.ElementSource) ::List{DAE.Statement}
              local outStatements::List{DAE.Statement}

              outStatements = begin
                  local else_::DAE.Else
                  local e::DAE.Exp
                  local br::List{DAE.Statement}
                  local rest::List{Tuple{DAE.Exp, List{DAE.Statement}}}
                @match (branches, source) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  ((e, br) <| rest, _)  => begin
                      else_ = makeElseFromBranches(rest)
                    list(DAE.STMT_IF(e, br, else_, source))
                  end
                end
              end
          outStatements
        end

         #= Creates the ELSE part of the DAE.STMT_IF. =#
        function makeElseFromBranches(inTpl::List{<:Tuple{<:DAE.Exp, List{<:DAE.Statement}}}) ::DAE.Else
              local outElse::DAE.Else

              outElse = begin
                  local b::List{DAE.Statement}
                  local else_::DAE.Else
                  local e::DAE.Exp
                  local xs::List{Tuple{DAE.Exp, List{DAE.Statement}}}
                @match inTpl begin
                   nil()  => begin
                    DAE.NOELSE()
                  end

                  (DAE.BCONST(true), b) <|  nil()  => begin
                    DAE.ELSE(b)
                  end

                  (e, b) <| xs  => begin
                      else_ = makeElseFromBranches(xs)
                    DAE.ELSEIF(e, b, else_)
                  end
                end
              end
          outElse
        end

         #= Every time we re-create/walk an if-statement, we optimize a bit :) =#
        function optimizeIf(icond::DAE.Exp, istmts::List{<:DAE.Statement}, iels::DAE.Else, isource::DAE.ElementSource) ::Tuple{List{DAE.Statement}, Bool}
              local changed::Bool
              local ostmts::List{DAE.Statement} #= can be empty or selected branch =#

              (ostmts, changed) = begin
                  local stmts::List{DAE.Statement}
                  local els::DAE.Else
                  local source::DAE.ElementSource
                  local cond::DAE.Exp
                @match (icond, istmts, iels, isource) begin
                  (DAE.BCONST(true), stmts, _, _)  => begin
                    (stmts, true)
                  end

                  (DAE.BCONST(false), _, DAE.NOELSE(__), _)  => begin
                    (nil, true)
                  end

                  (DAE.BCONST(false), _, DAE.ELSE(stmts), _)  => begin
                    (stmts, true)
                  end

                  (DAE.BCONST(false), _, DAE.ELSEIF(cond, stmts, els), source)  => begin
                      (ostmts, _) = optimizeIf(cond, stmts, els, source)
                    (ostmts, true)
                  end

                  _  => begin
                      (_cons(DAE.STMT_IF(icond, istmts, iels, isource), nil), false)
                  end
                end
              end
          (ostmts #= can be empty or selected branch =#, changed)
        end

         #= Every time we re-create/walk an if-statement, we optimize a bit :) =#
        function optimizeElseIf(cond::DAE.Exp, stmts::List{<:DAE.Statement}, els::DAE.Else) ::DAE.Else
              local oelse::DAE.Else

              oelse = begin
                @match (cond, stmts, els) begin
                  (DAE.BCONST(true), _, _)  => begin
                    DAE.ELSE(stmts)
                  end

                  (DAE.BCONST(false), _, _)  => begin
                    els
                  end

                  _  => begin
                      DAE.ELSEIF(cond, stmts, els)
                  end
                end
              end
          oelse
        end

         #= This function creates the ELSE part of the DAE.STMT_IF and checks if is correct. =#
        function makeElse(inTuple::List{<:Tuple{<:DAE.Exp, DAE.Properties, List{<:DAE.Statement}}}, inStatementLst::List{<:DAE.Statement}, inSource::DAE.ElementSource) ::DAE.Else
              local outElse::DAE.Else

              outElse = begin
                  local fb::List{DAE.Statement}
                  local b::List{DAE.Statement}
                  local else_::DAE.Else
                  local e::DAE.Exp
                  local xs::List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}
                  local e_str::String
                  local t_str::String
                  local t::DAE.Type
                  local info::SourceInfo
                @matchcontinue (inTuple, inStatementLst, inSource) begin
                  ( nil(),  nil(), _)  => begin
                    DAE.NOELSE()
                  end

                  ( nil(), fb, _)  => begin
                    DAE.ELSE(fb)
                  end

                  ((DAE.BCONST(true), DAE.PROP(__), b) <| _, _, _)  => begin
                    DAE.ELSE(b)
                  end

                  ((DAE.BCONST(false), DAE.PROP(__), _) <| xs, fb, _)  => begin
                    makeElse(xs, fb, inSource)
                  end

                  ((e, DAE.PROP(type_ = t), b) <| xs, fb, _)  => begin
                      (e, _) = Types.matchType(e, t, DAE.T_BOOL_DEFAULT, true)
                      else_ = makeElse(xs, fb, inSource)
                    DAE.ELSEIF(e, b, else_)
                  end

                  ((e, DAE.PROP(type_ = t), _) <| _, _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      info = ElementSource.getElementSourceFileInfo(inSource)
                      Error.addSourceMessage(Error.IF_CONDITION_TYPE_ERROR, list(e_str, t_str), info)
                    fail()
                  end
                end
              end
               #= /* This removes empty else branches */ =#
          outElse
        end

         #= This function creates a DAE.STMT_FOR construct, checking
          that the types of the parts are correct. =#
        function makeFor(inIdent::String, inExp::DAE.Exp, inProperties::DAE.Properties, inStatementLst::List{<:DAE.Statement}, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local isArray::Bool
                  local et::DAE.Type
                  local i::String
                  local e_str::String
                  local t_str::String
                  local e::DAE.Exp
                  local t::DAE.Type
                  local stmts::List{DAE.Statement}
                  local dims::DAE.Dimensions
                @matchcontinue (inIdent, inExp, inProperties, inStatementLst, source) begin
                  (i, e, DAE.PROP(type_ = DAE.T_ARRAY(ty = t, dims = dims)), stmts, _)  => begin
                      isArray = Types.isNonscalarArray(t, dims)
                    DAE.STMT_FOR(t, isArray, i, -1, e, stmts, source)
                  end

                  (i, e, DAE.PROP(type_ = DAE.T_METALIST(ty = t)), stmts, _)  => begin
                      t = Types.simplifyType(t)
                    DAE.STMT_FOR(t, false, i, -1, e, stmts, source)
                  end

                  (i, e, DAE.PROP(type_ = DAE.T_METAARRAY(ty = t)), stmts, _)  => begin
                      t = Types.simplifyType(t)
                    DAE.STMT_FOR(t, false, i, -1, e, stmts, source)
                  end

                  (_, e, DAE.PROP(type_ = t), _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      Error.addSourceMessage(Error.FOR_EXPRESSION_TYPE_ERROR, list(e_str, t_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end
                end
              end
          outStatement
        end

         #= This function creates a DAE.STMT_PARFOR construct, checking
          that the types of the parts are correct. =#
        function makeParFor(inIdent::String, inExp::DAE.Exp, inProperties::DAE.Properties, inStatementLst::List{<:DAE.Statement}, inLoopPrlVars::List{<:Tuple{<:DAE.ComponentRef, SourceInfo}}, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local isArray::Bool
                  local et::DAE.Type
                  local i::String
                  local e_str::String
                  local t_str::String
                  local e::DAE.Exp
                  local t::DAE.Type
                  local stmts::List{DAE.Statement}
                  local dims::DAE.Dimensions
                @matchcontinue (inIdent, inExp, inProperties, inStatementLst, inLoopPrlVars, source) begin
                  (i, e, DAE.PROP(type_ = DAE.T_ARRAY(ty = t, dims = dims)), stmts, _, _)  => begin
                      isArray = Types.isNonscalarArray(t, dims)
                      _ = Types.simplifyType(t)
                    DAE.STMT_PARFOR(t, isArray, i, -1, e, stmts, inLoopPrlVars, source)
                  end

                  (_, e, DAE.PROP(type_ = t), _, _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      Error.addSourceMessage(Error.FOR_EXPRESSION_TYPE_ERROR, list(e_str, t_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end
                end
              end
          outStatement
        end

         #= This function creates a DAE.STMT_WHILE construct, checking that the types
          of the parts are correct. =#
        function makeWhile(inExp::DAE.Exp, inProperties::DAE.Properties, inStatementLst::List{<:DAE.Statement}, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local e::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local e_str::String
                  local t_str::String
                  local t::DAE.Type
                @matchcontinue (inExp, inProperties, inStatementLst, source) begin
                  (e, DAE.PROP(type_ = DAE.T_BOOL(__)), stmts, _)  => begin
                    DAE.STMT_WHILE(e, stmts, source)
                  end

                  (e, DAE.PROP(type_ = t), _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      Error.addSourceMessage(Error.WHILE_CONDITION_TYPE_ERROR, list(e_str, t_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end
                end
              end
          outStatement
        end

         #= This function creates a DAE.STMT_WHEN algorithm construct,
          checking that the types of the parts are correct. =#
        function makeWhenA(inExp::DAE.Exp, inProperties::DAE.Properties, inStatementLst::List{<:DAE.Statement}, elseWhenStmt::Option{<:DAE.Statement}, source::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local e::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local elsew::Option{DAE.Statement}
                  local e_str::String
                  local t_str::String
                  local t::DAE.Type
                @matchcontinue (inExp, inProperties, inStatementLst, elseWhenStmt, source) begin
                  (e, DAE.PROP(type_ = DAE.T_BOOL(__)), stmts, elsew, _)  => begin
                    DAE.STMT_WHEN(e, nil, false, stmts, elsew, source)
                  end

                  (e, DAE.PROP(type_ = DAE.T_ARRAY(ty = DAE.T_BOOL(__))), stmts, elsew, _)  => begin
                    DAE.STMT_WHEN(e, nil, false, stmts, elsew, source)
                  end

                  (e, DAE.PROP(type_ = t), _, _, _)  => begin
                      e_str = CrefForHashTable.printExpStr(e)
                      t_str = Types.unparseTypeNoAttr(t)
                      Error.addSourceMessage(Error.WHEN_CONDITION_TYPE_ERROR, list(e_str, t_str), ElementSource.getElementSourceFileInfo(source))
                    fail()
                  end
                end
              end
          outStatement
        end

         #=  creates a reinit statement in an algorithm
         statement, only valid in when algorithm sections. =#
        function makeReinit(inExp1::DAE.Exp, inExp2::DAE.Exp, inProperties3::DAE.Properties, inProperties4::DAE.Properties, source::DAE.ElementSource) ::List{DAE.Statement}
              local outStatement::List{DAE.Statement}

              outStatement = begin
                  local var::DAE.Exp
                  local val::DAE.Exp
                  local var_1::DAE.Exp
                  local val_1::DAE.Exp
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local tp1::DAE.Type
                  local tp2::DAE.Type
                @matchcontinue (inExp1, inExp2, inProperties3, inProperties4) begin
                  (var && DAE.CREF(__), val, DAE.PROP(tp1, _), DAE.PROP(tp2, _))  => begin
                      (val_1, _) = Types.matchType(val, tp2, DAE.T_REAL_DEFAULT, true)
                      (var_1, _) = Types.matchType(var, tp1, DAE.T_REAL_DEFAULT, true)
                    list(DAE.STMT_REINIT(var_1, val_1, source))
                  end

                  _  => begin
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list("reinit called with wrong args"), ElementSource.getElementSourceFileInfo(source))
                      fail()
                  end
                end
              end
               #=  TODO: Add checks for reinit here. 1. First argument must be variable. 2. Expressions must be real.
               =#
          outStatement
        end

         #= Creates an assert statement from two expressions.
         =#
        function makeAssert(cond::DAE.Exp #= condition =#, msg::DAE.Exp #= message =#, level::DAE.Exp, inProperties3::DAE.Properties, inProperties4::DAE.Properties, inProperties5::DAE.Properties, source::DAE.ElementSource) ::List{DAE.Statement}
              local outStatement::List{DAE.Statement}

              outStatement = begin
                  local info::SourceInfo
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local t3::DAE.Type
                  local strTy::String
                  local strExp::String
                @matchcontinue (cond, msg, level, inProperties3, inProperties4, inProperties5, source) begin
                  (DAE.BCONST(true), _, _, DAE.PROP(type_ = DAE.T_BOOL(__)), DAE.PROP(type_ = DAE.T_STRING(__)), DAE.PROP(type_ = DAE.T_ENUMERATION(path = Absyn.FULLYQUALIFIED(Absyn.IDENT("AssertionLevel")))), _)  => begin
                    nil
                  end

                  (_, _, _, DAE.PROP(type_ = DAE.T_BOOL(__)), DAE.PROP(type_ = DAE.T_STRING(__)), DAE.PROP(type_ = DAE.T_ENUMERATION(path = Absyn.FULLYQUALIFIED(Absyn.IDENT("AssertionLevel")))), _)  => begin
                    list(DAE.STMT_ASSERT(cond, msg, level, source))
                  end

                  (_, _, _, DAE.PROP(type_ = t1), DAE.PROP(type_ = t2), DAE.PROP(type_ = t3), _)  => begin
                      info = ElementSource.getElementSourceFileInfo(source)
                      strExp = CrefForHashTable.printExpStr(cond)
                      strTy = Types.unparseType(t1)
                      Error.assertionOrAddSourceMessage(Types.isBooleanOrSubTypeBoolean(t1), Error.EXP_TYPE_MISMATCH, list(strExp, "Boolean", strTy), info)
                      strExp = CrefForHashTable.printExpStr(msg)
                      strTy = Types.unparseType(t2)
                      Error.assertionOrAddSourceMessage(Types.isString(t2), Error.EXP_TYPE_MISMATCH, list(strExp, "String", strTy), info)
                      @shouldFail @match DAE.T_ENUMERATION(path = Absyn.IDENT("AssertionLevel")) = t3
                      strExp = CrefForHashTable.printExpStr(level)
                      strTy = Types.unparseType(t3)
                      Error.assertionOrAddSourceMessage(Types.isString(t3), Error.EXP_TYPE_MISMATCH, list(strExp, "AssertionLevel", strTy), info)
                    fail()
                  end
                end
              end
          outStatement
        end

         #=
          Creates a terminate statement from message expression.
         =#
        function makeTerminate(msg::DAE.Exp #= message =#, props::DAE.Properties, source::DAE.ElementSource) ::List{DAE.Statement}
              local outStatement::List{DAE.Statement}

              outStatement = begin
                @match (msg, props, source) begin
                  (_, DAE.PROP(type_ = DAE.T_STRING(__)), _)  => begin
                    list(DAE.STMT_TERMINATE(msg, source))
                  end
                end
              end
          outStatement
        end

         #= Returns all crefs from an algorithm =#
        function getCrefFromAlg(alg::DAE.Algorithm) ::List{DAE.ComponentRef}
              local crs::List{DAE.ComponentRef}

              crs = ListUtil.unionOnTrueList(ListUtil.map(getAllExps(alg), Expression.extractCrefsFromExp), CrefForHashTable.crefEqual)
          crs
        end

         #=
          This function goes through the Algorithm structure and finds all the
          expressions and returns them in a list
         =#
        function getAllExps(inAlgorithm::DAE.Algorithm) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = begin
                  local exps::List{DAE.Exp}
                  local stmts::List{DAE.Statement}
                @match inAlgorithm begin
                  DAE.ALGORITHM_STMTS(statementLst = stmts)  => begin
                      exps = getAllExpsStmts(stmts)
                    exps
                  end
                end
              end
          outExpExpLst
        end

         #=
          This function takes a list of statements and returns all expressions and subexpressions
          in all statements.
         =#
        function getAllExpsStmts(stmts::List{<:DAE.Statement}) ::List{DAE.Exp}
              local exps::List{DAE.Exp}

              (_, (_, exps)) = DAETraverse.traverseDAEEquationsStmts(stmts, Expression.traverseSubexpressionsHelper, (Expression.expressionCollector, nil))
          exps
        end

        function getStatementSource(stmt::DAE.Statement) ::DAE.ElementSource
              local source::DAE.ElementSource

              source = begin
                @match stmt begin
                  DAE.STMT_ASSIGN(source = source)  => begin
                    source
                  end

                  DAE.STMT_TUPLE_ASSIGN(source = source)  => begin
                    source
                  end

                  DAE.STMT_ASSIGN_ARR(source = source)  => begin
                    source
                  end

                  DAE.STMT_IF(source = source)  => begin
                    source
                  end

                  DAE.STMT_FOR(source = source)  => begin
                    source
                  end

                  DAE.STMT_PARFOR(source = source)  => begin
                    source
                  end

                  DAE.STMT_WHILE(source = source)  => begin
                    source
                  end

                  DAE.STMT_WHEN(source = source)  => begin
                    source
                  end

                  DAE.STMT_ASSERT(source = source)  => begin
                    source
                  end

                  DAE.STMT_TERMINATE(source = source)  => begin
                    source
                  end

                  DAE.STMT_REINIT(source = source)  => begin
                    source
                  end

                  DAE.STMT_NORETCALL(source = source)  => begin
                    source
                  end

                  DAE.STMT_RETURN(source = source)  => begin
                    source
                  end

                  DAE.STMT_BREAK(source = source)  => begin
                    source
                  end

                  DAE.STMT_CONTINUE(source = source)  => begin
                    source
                  end

                  DAE.STMT_FAILURE(source = source)  => begin
                    source
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Algorithm.getStatementSource"))
                      fail()
                  end
                end
              end
          source
        end

        function getAssertCond(stmt::DAE.Statement) ::DAE.Exp
              local cond::DAE.Exp

              @match DAE.STMT_ASSERT(cond = cond) = stmt
          cond
        end

        function isNotDummyStatement(stmt::DAE.Statement) ::Bool
              local b::Bool

              b = begin
                  local exp::DAE.Exp
                @match stmt begin
                  DAE.STMT_NORETCALL(exp = exp)  => begin
                      (_, b) = Expression.traverseExpBottomUp(exp, Expression.hasNoSideEffects, true)
                    ! b
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  has side effects => this is an expression that could do something
               =#
          b
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

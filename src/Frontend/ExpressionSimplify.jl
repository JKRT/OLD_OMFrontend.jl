module ExpressionSimplify


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    using Setfield

    GetArrayContents = Function
    MakeArrayFromList = Function
    ToString = Function

    GetArrayContents = Function
    ToString = Function

    Fun = Function

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
         #=  public imports
         =#

        Type_a = Any

        import Absyn

        import AbsynUtil

        import ClassInf

        import DAE

        import Error

        import ExpressionSimplifyTypes

        ComponentRef = DAE.ComponentRef

        Ident = String

        Operator = DAE.Operator

        Type = DAE.Type

        Subscript = DAE.Subscript
         #=  protected imports
         =#

        import Config

        import DAEUtilMinimal

        import Debug

        import FCore

        import FCoreUtil

        import FGraphUtil

        import ElementSource

        import ErrorExt

        import Expression

        import CrefForHashTable

        import Flags

        import ListUtil

        import MetaModelica.Dangerous

        import Prefix

        import Types

        import Util

        import Values

        import ValuesUtil

         const optionSimplifyOnly = ExpressionSimplifyTypes.optionSimplifyOnly::ExpressionSimplifyTypes.Options

         #= Simplifies expressions =#
        function simplify(inExp::DAE.Exp) ::Tuple{DAE.Exp, Bool}
              local hasChanged::Bool
              local outExp::DAE.Exp

              (outExp, hasChanged) = simplifyWithOptions(inExp, optionSimplifyOnly)
          (outExp, hasChanged)
        end

         #= Simplifies expressions on condition =#
        function condsimplify(cond::Bool, ioExp::DAE.Exp) ::Tuple{DAE.Exp, Bool}
              local hasChanged::Bool = false


              if cond
                (ioExp, hasChanged) = simplifyWithOptions(ioExp, optionSimplifyOnly)
              end
          (ioExp, hasChanged)
        end

        function simplifyBinaryExp(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local op::DAE.Operator
                @match inExp begin
                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                    simplifyBinary(inExp, op, e1, e2)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

        function simplifyUnaryExp(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local op::DAE.Operator
                @match inExp begin
                  DAE.UNARY(exp = e1, operator = op)  => begin
                    simplifyUnary(inExp, op, e1)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= Simplifies expressions =#
        function simplifyWithOptions(inExp::DAE.Exp, options::ExpressionSimplifyTypes.Options) ::Tuple{DAE.Exp, Bool}
              local hasChanged::Bool
              local outExp::DAE.Exp

              (outExp, hasChanged) = begin
                  local e::DAE.Exp
                  local eNew::DAE.Exp
                  local b::Bool
                @matchcontinue (inExp, options) begin
                  (e, (_, ExpressionSimplifyTypes.DO_EVAL(__)))  => begin
                      (eNew, _) = simplify1WithOptions(e, options)
                      Error.assertionOrAddSourceMessage(Expression.isConstValue(eNew), Error.INTERNAL_ERROR, list("eval exp failed"), AbsynUtil.dummyInfo)
                      b = ! Expression.expEqual(e, eNew)
                    (eNew, b)
                  end

                  (e, _)  => begin
                      @match false = Config.getNoSimplify()
                      (eNew, _) = simplify1WithOptions(e, options)
                      eNew = simplify2(eNew)
                      (eNew, _) = simplify1WithOptions(eNew, options)
                      b = ! Expression.expEqual(e, eNew)
                    (eNew, b)
                  end

                  (e, _)  => begin
                      (eNew, b) = simplify1WithOptions(e, options)
                    (eNew, b)
                  end
                end
              end
               #=  Basic local simplifications
               =#
               #= print(\"SIMPLIFY BEFORE->\" + CrefForHashTable.printExpStr(e) + \"\\n\");
               =#
               #=  Basic local simplifications
               =#
               #= print(\"SIMPLIFY INTERMEDIATE->\" + CrefForHashTable.printExpStr(eNew) + \"\\n\");
               =#
               #=  Advanced (global) simplifications
               =#
               #=  Basic local simplifications
               =#
               #= print(\"SIMPLIFY FINAL->\" + CrefForHashTable.printExpStr(eNew) + \"\\n\");
               =#
          (outExp, hasChanged)
        end

        function simplifyTraverseHelper(inExp::DAE.Exp, inA::Type_a) ::Tuple{DAE.Exp, Type_a}
              local a::Type_a
              local exp::DAE.Exp

              a = inA
              (exp, _) = simplify(inExp)
          (exp, a)
        end

        function simplify1TraverseHelper(inExp::DAE.Exp, inA::Type_a) ::Tuple{DAE.Exp, Type_a}
              local a::Type_a
              local outExp::DAE.Exp

              a = inA
              outExp = simplify1(inExp)
          (outExp, a)
        end

         #= simplify1 with timing =#
        function simplify1time(e::DAE.Exp) ::DAE.Exp
              local outE::DAE.Exp

              local t1::ModelicaReal
              local t2::ModelicaReal

              t1 = clock()
              (outE, _) = simplify1(e)
              t2 = clock()
              print(if t2 - t1 > 0.01
                    "simplify1 took " + realString(t2 - t1) + " seconds for exp: " + CrefForHashTable.printExpStr(e) + " \\nsimplified to :" + CrefForHashTable.printExpStr(outE) + "\\n"
                  else
                    ""
                  end)
          outE
        end

         #= This function does some very basic simplification
          on expressions, like 0*a = 0, [1][1] => 1, etc.
        This function can be optimised to a switch-statement due to all uniontypes being different.
         =#
        function simplifyWork(inExp::DAE.Exp, options::ExpressionSimplifyTypes.Options) ::Tuple{DAE.Exp, ExpressionSimplifyTypes.Options}
              local outOptions::ExpressionSimplifyTypes.Options
              local outExp::DAE.Exp

              (outExp, outOptions) = begin
                   #= /* switch: keep it as such */ =#
                  local n::ModelicaInteger
                  local i::ModelicaInteger
                  local e::DAE.Exp
                  local exp::DAE.Exp
                  local e1::DAE.Exp
                  local e_1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local exp1::DAE.Exp
                  local t::Type
                  local tp::Type
                  local b::Bool
                  local b2::Bool
                  local idn::String
                  local str::String
                  local expl::List{DAE.Exp}
                  local matrix::List{DAE.Exp}
                  local subs::List{DAE.Exp}
                  local s::List{Subscript}
                  local c_1::ComponentRef
                  local op::Operator
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local oe::Option{DAE.Exp}
                @match (inExp, options) begin
                  (DAE.SIZE(exp = e1, sz = oe), _)  => begin
                    (simplifySize(inExp, e1, oe), options)
                  end

                  (DAE.CAST(ty = tp, exp = e), _)  => begin
                      e = simplifyCast(inExp, e, tp)
                    (e, options)
                  end

                  (DAE.ASUB(exp = e, sub = subs), _)  => begin
                      e = simplifyAsubExp(inExp, e, subs)
                    (e, options)
                  end

                  (DAE.TSUB(__), _)  => begin
                    (simplifyTSub(inExp), options)
                  end

                  (DAE.UNARY(operator = op, exp = e1), _)  => begin
                      e = simplifyUnary(inExp, op, e1)
                    (e, options)
                  end

                  (DAE.BINARY(exp1 = e1, operator = op, exp2 = e2), _)  => begin
                      e = simplifyBinary(inExp, op, e1, e2)
                    (e, options)
                  end

                  (DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB), _)  => begin
                      e = simplifyRelation(inExp, op, e1, e2, index_, isExpisASUB)
                    (e, options)
                  end

                  (DAE.LUNARY(operator = op, exp = e1), _)  => begin
                      e = simplifyUnary(inExp, op, e1)
                    (e, options)
                  end

                  (DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), _)  => begin
                      e = simplifyLBinary(inExp, op, e1, e2)
                    (e, options)
                  end

                  (DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), _)  => begin
                      e = simplifyIfExp(inExp, e1, e2, e3)
                    (e, options)
                  end

                  (DAE.CREF(componentRef = c_1, ty = t), _)  => begin
                      e = simplifyCref(inExp, c_1, t)
                    (e, options)
                  end

                  (DAE.REDUCTION(reductionInfo, e1, riters), _)  => begin
                      (riters, b2) = simplifyReductionIterators(riters, nil, false)
                      exp1 = if b2
                            DAE.REDUCTION(reductionInfo, e1, riters)
                          else
                            inExp
                          end
                    (simplifyReduction(exp1), options)
                  end

                  (DAE.CALL(__), _)  => begin
                    (simplifyCall(inExp), options)
                  end

                  (DAE.RSUB(__), _)  => begin
                    (simplifyRSub(inExp), options)
                  end

                  (DAE.MATCHEXPRESSION(__), _)  => begin
                    (simplifyMatch(inExp), options)
                  end

                  (DAE.UNBOX(__), _)  => begin
                    (simplifyUnbox(inExp), options)
                  end

                  (DAE.BOX(__), _)  => begin
                    (simplifyUnbox(inExp), options)
                  end

                  (DAE.CONS(__), _)  => begin
                    (simplifyCons(inExp), options)
                  end

                  _  => begin
                      (inExp, options)
                  end
                end
              end
               #= /* simplify different casts. Optimized to only run simplify1 once on subexpression e*/ =#
               #=  unary operations
               =#
               #=  relations
               =#
               #=  logical unary expressions
               =#
               #=  logical binary expressions
               =#
               #=  if true and false branches are equal
               =#
               #=  component references
               =#
               #=  Look for things we really *should* have simplified, but only if we did not modify anything!
               =#
               #= /*    case ((e,(false,_)))
                    equation
                      true = Flags.isSet(Flags.CHECK_SIMPLIFY);
                      true = Expression.isConst(e);
                      false = Expression.isConstValue(e);
                      str = CrefForHashTable.printExpStr(e);
                      Error.addSourceMessage(Error.SIMPLIFY_CONSTANT_ERROR, {str}, AbsynUtil.dummyInfo);
                    then fail(); */ =#
               #=  anything else
               =#
          (outExp, outOptions)
        end

        function simplifyRSub(e::DAE.Exp) ::DAE.Exp


              e = begin
                  local cr::DAE.ComponentRef
                  local i::ModelicaInteger
                  local exps::List{DAE.Exp}
                  local comp::List{String}
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local ty::DAE.Type
                  local vars::List{DAE.Var}
                @match e begin
                  DAE.RSUB(exp = DAE.CREF(componentRef = cr), ix = -1)  => begin
                    DAE.CREF(CrefForHashTable.joinCrefs(cr, CrefForHashTable.makeCrefIdent(e.fieldName, e.ty, nil)), e.ty)
                  end

                  DAE.RSUB(exp = DAE.CALL(path = p1, expLst = exps, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = p2), varLst = vars))), ix = -1) where (AbsynUtil.pathEqual(p1, p2))  => begin
                    listGet(exps, ListUtil.position1OnTrue(list(v.name for v in vars), stringEq, e.fieldName))
                  end

                  DAE.RSUB(exp = DAE.RECORD(exps = exps, comp = comp), ix = -1)  => begin
                    listGet(exps, ListUtil.position1OnTrue(comp, stringEq, e.fieldName))
                  end

                  _  => begin
                      e
                  end
                end
              end
          e
        end

        function simplifyAsubExp(origExp::DAE.Exp, inExp::DAE.Exp, inSubs::List{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local sub::ModelicaInteger
                  local istart::ModelicaInteger
                  local istep::ModelicaInteger
                  local istop::ModelicaInteger
                  local tp::DAE.Type
                  local e::DAE.Exp
                  local eLst::List{DAE.Exp}
                  local subs::List{DAE.Exp}
                  local hasRange::Bool
                  local step::Option{DAE.Exp}
                   #=  No ASUB...
                   =#
                @matchcontinue (origExp, inExp, inSubs) begin
                  (_, e,  nil())  => begin
                    e
                  end

                  (_, DAE.CAST(tp, e), _)  => begin
                      tp = Expression.unliftArray(tp)
                      e = DAE.CAST(tp, DAE.ASUB(e, inSubs))
                    e
                  end

                  (_, DAE.TUPLE(PR = eLst), DAE.ICONST(sub) <|  nil()) where (sub <= listLength(eLst))  => begin
                    listGet(eLst, sub)
                  end

                  (_, _, _)  => begin
                    simplifyAsubSlicing(inExp, inSubs)
                  end

                  (_, _, _)  => begin
                       #=  ASUB(CAST(e)) -> CAST(liftArray(t), ASUB(e))
                       =#
                       #=  Simplify asubs which result from function calls
                       =#
                       #=  Simplify asubs where some of the subscripts are slices.
                       =#
                       #=  other subscripting/asub simplifications where e is not simplified first.
                       =#
                       #=  Are all expressions integers?
                       =#
                      for exp in inSubs
                        Expression.expInt(exp)
                      end
                    ListUtil.foldr(inSubs, simplifyAsub, inExp)
                  end

                  (_, _, _)  => begin
                       #=  Any range in the subscripts that we can evaluate?
                       =#
                      hasRange = false
                      subs = list(begin
                        @match exp begin
                          DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), step, DAE.ICONST(istop))  => begin
                              e = Expression.makeArray(list(DAE.ICONST(i) for i in simplifyRange(istart, begin
                                 @match step begin
                                   NONE()  => begin
                                     1
                                   end

                                   SOME(DAE.ICONST(istep))  => begin
                                     istep
                                   end
                                 end
                               end, istop)), DAE.T_INTEGER_DEFAULT, true)
                              hasRange = true
                            e
                          end

                          _  => begin
                              exp
                          end
                        end
                      end for exp in inSubs)
                      @match true = hasRange
                    DAE.ASUB(inExp, subs)
                  end

                  _  => begin
                      origExp
                  end
                end
              end
          outExp
        end

        function simplifyCall(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local exp::DAE.Exp
                  local zero::DAE.Exp
                  local matrix::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local attr::DAE.CallAttributes
                  local tp::DAE.Type
                  local b2::Bool
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local idn::String
                  local idn2::String
                  local n::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                   #=  homotopy(e, e) => e
                   =#
                @matchcontinue inExp begin
                  DAE.CALL(path = Absyn.IDENT("homotopy"), expLst = e1 <| e2 <|  nil()) where (Expression.expEqual(e1, e2))  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("noEvent"), expLst = e <|  nil())  => begin
                      b2 = Expression.isRelation(e) || Expression.isEventTriggeringFunctionExp(e)
                    if ! b2
                          simplifyNoEvent(e)
                        else
                          inExp
                        end
                  end

                  DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.UNARY(DAE.UMINUS(tp), e1 && DAE.CREF(__)) <|  nil(), attr = attr)  => begin
                    DAE.UNARY(DAE.UMINUS(tp), DAE.CALL(Absyn.IDENT("der"), list(e1), attr))
                  end

                  DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.UNARY(DAE.UMINUS_ARR(tp), e1 && DAE.CREF(__)) <|  nil(), attr = attr)  => begin
                    DAE.UNARY(DAE.UMINUS_ARR(tp), DAE.CALL(Absyn.IDENT("der"), list(e1), attr))
                  end

                  DAE.CALL(path = Absyn.IDENT("pre"), expLst = DAE.CREF(__) <|  nil())  => begin
                    inExp
                  end

                  DAE.CALL(path = Absyn.IDENT("previous"), expLst = DAE.CREF(__) <|  nil())  => begin
                    inExp
                  end

                  DAE.CALL(path = Absyn.IDENT("change"), expLst = DAE.CREF(__) <|  nil())  => begin
                    inExp
                  end

                  DAE.CALL(path = Absyn.IDENT("edge"), expLst = DAE.CREF(__) <|  nil())  => begin
                    inExp
                  end

                  DAE.CALL(path = Absyn.IDENT("pre"), expLst = e && DAE.ASUB(exp = exp) <|  nil())  => begin
                      b2 = Expression.isConst(exp)
                    if b2
                          e
                        else
                          inExp
                        end
                  end

                  DAE.CALL(path = Absyn.IDENT("previous"), expLst = e && DAE.ASUB(exp = exp) <|  nil())  => begin
                      b2 = Expression.isConst(exp)
                    if b2
                          e
                        else
                          inExp
                        end
                  end

                  DAE.CALL(path = Absyn.IDENT("change"), expLst = DAE.ASUB(exp = exp) <|  nil())  => begin
                      b2 = Expression.isConst(exp)
                    if b2
                          DAE.BCONST(false)
                        else
                          inExp
                        end
                  end

                  DAE.CALL(path = Absyn.IDENT("edge"), expLst = DAE.ASUB(exp = exp) <|  nil())  => begin
                      b2 = Expression.isConst(exp)
                    if b2
                          DAE.BCONST(false)
                        else
                          inExp
                        end
                  end

                  DAE.CALL(path = Absyn.IDENT("pre"), expLst = e <|  nil())  => begin
                      (e, _) = Expression.traverseExpTopDown(e, preCref, false)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("previous"), expLst = e <|  nil())  => begin
                      (e, _) = Expression.traverseExpTopDown(e, previousCref, false)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("change"), expLst = e <|  nil())  => begin
                      (e, _) = Expression.traverseExpTopDown(e, changeCref, false)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("edge"), expLst = e <|  nil())  => begin
                      (e, _) = Expression.traverseExpTopDown(e, edgeCref, false)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT(idn), expLst = expl, attr = DAE.CALL_ATTR(isImpure = false)) where (Expression.isConstWorkList(expl))  => begin
                    simplifyBuiltinConstantCalls(idn, inExp)
                  end

                  DAE.CALL(attr = DAE.CALL_ATTR(builtin = true))  => begin
                    simplifyBuiltinCalls(inExp)
                  end

                  DAE.CALL(path = Absyn.IDENT(name = "identity"), expLst = DAE.ICONST(n) <|  nil())  => begin
                      matrix = list(DAE.ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(n))), true, list(if i == j
                            DAE.ICONST(1)
                          else
                            DAE.ICONST(0)
                          end for i in 1:n)) for j in 1:n)
                    DAE.ARRAY(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(n), DAE.DIM_INTEGER(n))), false, matrix)
                  end

                  DAE.CALL(path = Absyn.IDENT(name = "diagonal"), expLst = DAE.ARRAY(array = expl, ty = tp) <|  nil())  => begin
                      n = listLength(expl)
                      tp = Types.arrayElementType(tp)
                      zero = Expression.makeConstZero(tp)
                      matrix = list(DAE.ARRAY(DAE.T_ARRAY(tp, list(DAE.DIM_INTEGER(n))), true, list(if i == j
                            listGet(expl, i)
                          else
                            zero
                          end for i in 1:n)) for j in 1:n)
                    DAE.ARRAY(DAE.T_ARRAY(tp, list(DAE.DIM_INTEGER(n), DAE.DIM_INTEGER(n))), false, matrix)
                  end

                  DAE.CALL(path = Absyn.IDENT(idn), expLst = DAE.CALL(path = Absyn.IDENT(idn2), expLst = e <|  nil()) <|  nil()) where (idn == "tan" && idn2 == "atan")  => begin
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("mod"), expLst = DAE.RCONST(r1) <| DAE.RCONST(r2) <|  nil()) where (r2 != 0.0)  => begin
                    DAE.RCONST(mod(r1, r2))
                  end

                  DAE.CALL(path = Absyn.IDENT("mod"), expLst = DAE.ICONST(i1) <| DAE.ICONST(i2) <|  nil()) where (i2 != 0.0)  => begin
                    DAE.ICONST(mod(i1, i2))
                  end

                  DAE.CALL(path = Absyn.IDENT("integer"), expLst = DAE.RCONST(r1) <|  nil())  => begin
                    DAE.ICONST(realInt(r1))
                  end

                  DAE.CALL(path = Absyn.IDENT("sin"), expLst = DAE.CALL(path = Absyn.IDENT("acos"), expLst = e <|  nil()) <|  nil())  => begin
                    Expression.makePureBuiltinCall("sqrt", list(DAE.BINARY(DAE.RCONST(1), DAE.SUB(DAE.T_REAL_DEFAULT), DAE.BINARY(e, DAE.MUL(DAE.T_REAL_DEFAULT), e))), DAE.T_REAL_DEFAULT)
                  end

                  DAE.CALL(path = Absyn.IDENT("cos"), expLst = DAE.CALL(path = Absyn.IDENT("asin"), expLst = e <|  nil()) <|  nil())  => begin
                    Expression.makePureBuiltinCall("sqrt", list(DAE.BINARY(DAE.RCONST(1), DAE.SUB(DAE.T_REAL_DEFAULT), DAE.BINARY(e, DAE.MUL(DAE.T_REAL_DEFAULT), e))), DAE.T_REAL_DEFAULT)
                  end

                  DAE.CALL(path = Absyn.IDENT("sin"), expLst = DAE.CALL(path = Absyn.IDENT("atan"), expLst = e <|  nil()) <|  nil())  => begin
                    DAE.BINARY(e, DAE.DIV(DAE.T_REAL_DEFAULT), Expression.makePureBuiltinCall("sqrt", list(DAE.BINARY(DAE.RCONST(1), DAE.ADD(DAE.T_REAL_DEFAULT), DAE.BINARY(e, DAE.MUL(DAE.T_REAL_DEFAULT), e))), DAE.T_REAL_DEFAULT))
                  end

                  DAE.CALL(path = Absyn.IDENT("cos"), expLst = DAE.CALL(path = Absyn.IDENT("atan"), expLst = e <|  nil()) <|  nil())  => begin
                    DAE.BINARY(DAE.RCONST(1), DAE.DIV(DAE.T_REAL_DEFAULT), Expression.makePureBuiltinCall("sqrt", list(DAE.BINARY(DAE.RCONST(1), DAE.ADD(DAE.T_REAL_DEFAULT), DAE.BINARY(e, DAE.MUL(DAE.T_REAL_DEFAULT), e))), DAE.T_REAL_DEFAULT))
                  end

                  DAE.CALL(path = Absyn.IDENT("atan2"), expLst = e1 <| e2 <|  nil()) where (Expression.isZero(e2))  => begin
                      e = Expression.makePureBuiltinCall("sign", list(e1), DAE.T_REAL_DEFAULT)
                    DAE.BINARY(DAE.RCONST(1.570796326794896619231321691639751442), DAE.MUL(DAE.T_REAL_DEFAULT), e)
                  end

                  DAE.CALL(path = Absyn.IDENT("atan2"), expLst = e1 && DAE.RCONST(0.0) <| _ <|  nil())  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("atan2"), expLst = DAE.RCONST(r1) <| DAE.RCONST(r2) <|  nil())  => begin
                    DAE.RCONST(atan2(r1, r2))
                  end

                  DAE.CALL(path = Absyn.IDENT("abs"), expLst = DAE.UNARY(operator = DAE.UMINUS(ty = tp), exp = e1) <|  nil())  => begin
                      e = Expression.makePureBuiltinCall("abs", list(e1), tp)
                    e
                  end

                  _ where (Config.acceptMetaModelicaGrammar())  => begin
                    simplifyMetaModelicaCalls(inExp)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #=  noEvent propagated to relations and event triggering functions
               =#
               #=  der(-v) -> -der(v)
               =#
               #=  move pre inside
               =#
               #=  normal (pure) call
               =#
               #=  simplify some builtin calls, like cross, etc
               =#
               #=  simplify identity
               =#
               #=  arcxxx(xxx(e)) => e; xxx(arcxxx(e)) => e
               =#
               #=       or (idn==\"sin\" and idn2==\"asin\")
               =#
               #=       or (idn==\"cos\" and idn2==\"acos\")
               =#
               #=  modulo for real values
               =#
               #=  modulo for integer values
               =#
               #=  integer call
               =#
               #=  sin(acos(e)) = sqrt(1-e^2)
               =#
               #=  cos(asin(e)) = sqrt(1-e^2)
               =#
               #=  sin(atan(e)) = e/sqrt(1+e^2)
               =#
               #=  cos(atan(e)) = 1/sqrt(1+e^2)
               =#
               #=  atan2(y,0) = sign(y)*pi/2
               =#
               #=  atan2(0,x) = 0
               =#
               #=  abs(-x) = abs(x)
               =#
               #=  MetaModelica builtin operators are calls
               =#
          outExp
        end

        function preCref(ie::DAE.Exp, ib::Bool) ::Tuple{DAE.Exp, Bool, Bool}
              local ob::Bool
              local cont::Bool
              local oe::DAE.Exp

              (oe, cont, ob) = begin
                  local e::DAE.Exp
                  local b::Bool
                  local ty::DAE.Type
                @match (ie, ib) begin
                  (e && DAE.CREF(ty = ty), _)  => begin
                    (Expression.makeBuiltinCall("pre", list(e), ty, false), false, true)
                  end

                  (e && DAE.CALL(path = Absyn.IDENT("pre")), b)  => begin
                    (e, false, b)
                  end

                  (e, b)  => begin
                    (e, ! b, b)
                  end
                end
              end
          (oe, cont, ob)
        end

        function previousCref(ie::DAE.Exp, ib::Bool) ::Tuple{DAE.Exp, Bool, Bool}
              local ob::Bool
              local cont::Bool
              local oe::DAE.Exp

              (oe, cont, ob) = begin
                  local e::DAE.Exp
                  local b::Bool
                  local ty::DAE.Type
                @match (ie, ib) begin
                  (e && DAE.CREF(ty = ty), _)  => begin
                    (Expression.makeBuiltinCall("previous", list(e), ty, false), false, true)
                  end

                  (e && DAE.CALL(path = Absyn.IDENT("previous")), b)  => begin
                    (e, false, b)
                  end

                  (e, b)  => begin
                    (e, ! b, b)
                  end
                end
              end
          (oe, cont, ob)
        end

        function changeCref(ie::DAE.Exp, ib::Bool) ::Tuple{DAE.Exp, Bool, Bool}
              local ob::Bool
              local cont::Bool
              local oe::DAE.Exp

              (oe, cont, ob) = begin
                  local e::DAE.Exp
                  local b::Bool
                  local ty::DAE.Type
                @match (ie, ib) begin
                  (e && DAE.CREF(ty = ty), _)  => begin
                    (Expression.makeBuiltinCall("change", list(e), ty, false), false, true)
                  end

                  (e && DAE.CALL(path = Absyn.IDENT("change")), b)  => begin
                    (e, false, b)
                  end

                  (e, b)  => begin
                    (e, ! b, b)
                  end
                end
              end
          (oe, cont, ob)
        end

        function edgeCref(ie::DAE.Exp, ib::Bool) ::Tuple{DAE.Exp, Bool, Bool}
              local ob::Bool
              local cont::Bool
              local oe::DAE.Exp

              (oe, cont, ob) = begin
                  local e::DAE.Exp
                  local b::Bool
                  local ty::DAE.Type
                @match (ie, ib) begin
                  (e && DAE.CREF(ty = ty), _)  => begin
                    (Expression.makeBuiltinCall("edge", list(e), ty, false), false, true)
                  end

                  (e && DAE.CALL(path = Absyn.IDENT("edge")), b)  => begin
                    (e, false, b)
                  end

                  (e, b)  => begin
                    (e, ! b, b)
                  end
                end
              end
          (oe, cont, ob)
        end

         #= This function does some very basic simplification
          on expressions, like 0*a = 0, [1][1] => 1, etc. =#
        function simplify1(inExp::DAE.Exp) ::Tuple{DAE.Exp, Bool}
              local hasChanged::Bool
              local outExp::DAE.Exp

              (outExp, hasChanged) = simplify1WithOptions(inExp, optionSimplifyOnly)
          (outExp, hasChanged)
        end

         #= This function does some very basic simplification
          on expressions, like 0*a = 0, [1][1] => 1, etc. =#
        function simplify1o(inExp::Option{<:DAE.Exp}) ::Option{DAE.Exp}
              local outExp::Option{DAE.Exp}

              outExp = begin
                  local e::DAE.Exp
                @match inExp begin
                  SOME(e)  => begin
                      (e, _) = simplify1WithOptions(e, optionSimplifyOnly)
                    SOME(e)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= This function does some very basic simplification
          on expressions, like 0*a = 0, [1][1] => 1, etc. =#
        function simplify1WithOptions(inExp::DAE.Exp, options::ExpressionSimplifyTypes.Options) ::Tuple{DAE.Exp, Bool}
              local hasChanged::Bool
              local outExp::DAE.Exp

              (outExp, hasChanged) = simplify1FixP(inExp, options, 100, true, false)
              checkSimplify(Flags.isSet(Flags.CHECK_SIMPLIFY), inExp, outExp)
          (outExp, hasChanged)
        end

         #= Verifies that the complexity of the expression is lower or equal than before the simplification was performed =#
        function checkSimplify(check::Bool, before::DAE.Exp, after::DAE.Exp)
              _ = begin
                  local c1::ModelicaInteger
                  local c2::ModelicaInteger
                  local b::Bool
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                @match (check, before, after) begin
                  (false, _, _)  => begin
                    ()
                  end

                  (true, _, _)  => begin
                      ty1 = Expression.typeOf(before)
                      ty2 = Expression.typeOf(after)
                      b = valueEq(ty1, ty2)
                      if ! b
                        s1 = CrefForHashTable.printExpStr(before)
                        s2 = CrefForHashTable.printExpStr(after)
                        s3 = Types.unparseType(ty1)
                        s4 = Types.unparseType(ty2)
                        Error.addMessage(Error.SIMPLIFICATION_TYPE, list(s1, s2, s3, s4))
                        fail()
                      end
                      c1 = Expression.complexity(before)
                      c2 = Expression.complexity(after)
                      b = c1 < c2
                      if b
                        s1 = intString(c2)
                        s2 = intString(c1)
                        s3 = CrefForHashTable.printExpStr(before)
                        s4 = CrefForHashTable.printExpStr(after)
                        Error.addMessage(Error.SIMPLIFICATION_COMPLEXITY, list(s1, s2, s3, s4))
                        fail()
                      end
                    ()
                  end
                end
              end
        end

         #= Does fixpoint simplify1 max n times =#
        function simplify1FixP(inExp::DAE.Exp, inOptions::ExpressionSimplifyTypes.Options, n::ModelicaInteger, cont::Bool, hasChanged::Bool) ::Tuple{DAE.Exp, Bool}
              local outHasChanged::Bool
              local outExp::DAE.Exp

              (outExp, outHasChanged) = begin
                  local exp::DAE.Exp
                  local expAfterSimplify::DAE.Exp
                  local b::Bool
                  local str1::String
                  local str2::String
                  local options::ExpressionSimplifyTypes.Options
                @match (inExp, inOptions, n, cont, hasChanged) begin
                  (exp, _, _, false, _)  => begin
                    (exp, hasChanged)
                  end

                  (exp, options, 0, _, _)  => begin
                      str1 = CrefForHashTable.printExpStr(exp)
                      (exp, _) = Expression.traverseExpBottomUp(exp, simplifyWork, options)
                      str2 = CrefForHashTable.printExpStr(exp)
                      Error.addMessage(Error.SIMPLIFY_FIXPOINT_MAXIMUM, list(str1, str2))
                    (exp, hasChanged)
                  end

                  (exp, options, _, true, _)  => begin
                      ErrorExt.setCheckpoint("ExpressionSimplify")
                      (expAfterSimplify, options) = Expression.traverseExpBottomUp(exp, simplifyWork, options)
                      b = ! referenceEq(expAfterSimplify, exp)
                      if b
                        ErrorExt.rollBack("ExpressionSimplify")
                      else
                        ErrorExt.delCheckpoint("ExpressionSimplify")
                      end
                      (expAfterSimplify, b) = simplify1FixP(expAfterSimplify, options, n - 1, b, b || hasChanged)
                    (expAfterSimplify, b)
                  end
                end
              end
               #=  print(\"simplify1 iter: \" + CrefForHashTable.printExpStr(expAfterSimplify) + \"\\n\");
               =#
          (outExp, outHasChanged)
        end

        function simplifyReductionIterators(inIters::List{<:DAE.ReductionIterator}, inAcc::List{<:DAE.ReductionIterator}, inChange::Bool) ::Tuple{List{DAE.ReductionIterator}, Bool}
              local outChange::Bool
              local outIters::List{DAE.ReductionIterator}

              (outIters, outChange) = begin
                  local id::String
                  local exp::DAE.Exp
                  local ty::DAE.Type
                  local iter::DAE.ReductionIterator
                  local iters::List{DAE.ReductionIterator}
                  local acc::List{DAE.ReductionIterator}
                  local change::Bool
                @match (inIters, inAcc, inChange) begin
                  ( nil(), acc, change)  => begin
                    (listReverse(acc), change)
                  end

                  (DAE.REDUCTIONITER(id, exp, SOME(DAE.BCONST(true)), ty) <| iters, acc, _)  => begin
                      (iters, change) = simplifyReductionIterators(iters, _cons(DAE.REDUCTIONITER(id, exp, NONE(), ty), acc), true)
                    (iters, change)
                  end

                  (DAE.REDUCTIONITER(id, _, SOME(DAE.BCONST(false)), ty) <| _, _, _)  => begin
                    (list(DAE.REDUCTIONITER(id, DAE.LIST(nil), NONE(), ty)), true)
                  end

                  (iter <| iters, acc, change)  => begin
                      (iters, change) = simplifyReductionIterators(iters, _cons(iter, acc), change)
                    (iters, change)
                  end
                end
              end
          (outIters, outChange)
        end

         #= Handles simplification of if-expressions =#
        function simplifyIfExp(origExp::DAE.Exp, cond::DAE.Exp, tb::DAE.Exp, fb::DAE.Exp) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                   #=  Condition is constant
                   =#
                @match (origExp, cond, tb, fb) begin
                  (_, DAE.BCONST(true), _, _)  => begin
                    tb
                  end

                  (_, DAE.BCONST(false), _, _)  => begin
                    fb
                  end

                  (_, exp, DAE.BCONST(true), DAE.BCONST(false))  => begin
                    exp
                  end

                  (_, exp, DAE.BCONST(false), DAE.BCONST(true))  => begin
                      exp = DAE.LUNARY(DAE.NOT(DAE.T_BOOL_DEFAULT), exp)
                    exp
                  end

                  (_, e, DAE.BOX(e1), DAE.BOX(e2))  => begin
                      e = DAE.IFEXP(e, e1, e2)
                    DAE.BOX(e)
                  end

                  _  => begin
                      if Expression.expEqual(tb, fb)
                            tb
                          else
                            origExp
                          end
                  end
                end
              end
               #=  The expression is the condition
               =#
               #=  Are the branches equal? Then why bother with the condition
               =#
          exp
        end

         #= simplifies MetaModelica operators =#
        function simplifyMetaModelicaCalls(exp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local path::Absyn.Path
                  local el::List{DAE.Exp}
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local s::String
                  local foldExp::Option{DAE.Exp}
                  local v::Option{Values.Value}
                  local ty::DAE.Type
                  local riters::DAE.ReductionIterators
                  local foldName::String
                  local resultName::String
                  local rit::Absyn.ReductionIterType
                @match exp begin
                  DAE.CALL(path = Absyn.IDENT("listAppend"), expLst = DAE.LIST(el) <| e2 <|  nil())  => begin
                      e = ListUtil.fold(listReverse(el), Expression.makeCons, e2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("listAppend"), expLst = e1 <| DAE.LIST(valList =  nil()) <|  nil())  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("intString"), expLst = DAE.ICONST(i) <|  nil())  => begin
                      s = intString(i)
                    DAE.SCONST(s)
                  end

                  DAE.CALL(path = Absyn.IDENT("realString"), expLst = DAE.RCONST(r) <|  nil())  => begin
                      s = realString(r)
                    DAE.SCONST(s)
                  end

                  DAE.CALL(path = Absyn.IDENT("boolString"), expLst = DAE.BCONST(b) <|  nil())  => begin
                      s = boolString(b)
                    DAE.SCONST(s)
                  end

                  DAE.CALL(path = Absyn.IDENT("listReverse"), expLst = DAE.LIST(el) <|  nil())  => begin
                      el = listReverse(el)
                      e1_1 = DAE.LIST(el)
                    e1_1
                  end

                  DAE.CALL(path = Absyn.IDENT("listReverse"), expLst = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("list"), rit, ty, v, foldName, resultName, foldExp), e1, riters) <|  nil())  => begin
                      e1 = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("listReverse"), rit, ty, v, foldName, resultName, foldExp), e1, riters)
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("listReverse"), expLst = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("listReverse"), rit, ty, v, foldName, resultName, foldExp), e1, riters) <|  nil())  => begin
                      e1 = DAE.REDUCTION(DAE.REDUCTIONINFO(Absyn.IDENT("list"), rit, ty, v, foldName, resultName, foldExp), e1, riters)
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("listLength"), expLst = DAE.LIST(el) <|  nil())  => begin
                      i = listLength(el)
                    DAE.ICONST(i)
                  end

                  DAE.CALL(path = Absyn.IDENT("mmc_mk_some"), expLst = e <|  nil())  => begin
                    DAE.META_OPTION(SOME(e))
                  end

                  DAE.CALL(path = Absyn.IDENT("sourceInfo"))  => begin
                      print("sourceInfo() - simplify?\\n")
                    fail()
                  end
                end
              end
          outExp
        end

        function simplifyCons(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local es::List{DAE.Exp}
                @match inExp begin
                  DAE.CONS(e, DAE.LIST(es))  => begin
                    DAE.LIST(_cons(e, es))
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= simplifies both box and unbox expressions =#
        function simplifyUnbox(exp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                @match exp begin
                  DAE.UNBOX(exp = DAE.BOX(outExp))  => begin
                    outExp
                  end

                  DAE.BOX(DAE.UNBOX(exp = outExp))  => begin
                    outExp
                  end

                  _  => begin
                      exp
                  end
                end
              end
          outExp
        end

         #= simplifies MetaModelica match expressions =#
        function simplifyMatch(exp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local path::Absyn.Path
                  local el::List{DAE.Exp}
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local s::String
                  local foldExp::Option{DAE.Exp}
                  local v::Option{Values.Value}
                  local ty::DAE.Type
                  local riters::DAE.ReductionIterators
                   #=  match () case () then exp; end match => exp
                   =#
                @match exp begin
                  DAE.MATCHEXPRESSION(inputs =  nil(), et = ty, localDecls =  nil(), cases = DAE.CASE(patterns =  nil(), localDecls =  nil(), body =  nil(), result = SOME(e)) <|  nil()) where (! Types.isTuple(ty))  => begin
                    e
                  end

                  DAE.MATCHEXPRESSION(inputs = e <|  nil(), et = ty, localDecls =  nil(), cases = DAE.CASE(patterns = DAE.PAT_CONSTANT(exp = DAE.BCONST(b1)) <|  nil(), localDecls =  nil(), body =  nil(), result = SOME(e1)) <| DAE.CASE(patterns = DAE.PAT_CONSTANT(exp = DAE.BCONST(b2)) <|  nil(), localDecls =  nil(), body =  nil(), result = SOME(e2)) <|  nil()) where (! boolEq(b1, b2) && ! Types.isTuple(ty))  => begin
                      e1_1 = if b1
                            e1
                          else
                            e2
                          end
                      e2_1 = if b1
                            e2
                          else
                            e1
                          end
                      e = DAE.IFEXP(e, e1_1, e2_1)
                    e
                  end

                  DAE.MATCHEXPRESSION(matchType = DAE.MATCH(__), et = ty, inputs = e <|  nil(), localDecls =  nil(), cases = DAE.CASE(patterns = DAE.PAT_CONSTANT(exp = DAE.BCONST(b1)) <|  nil(), localDecls =  nil(), body =  nil(), result = SOME(e1)) <| DAE.CASE(patterns = DAE.PAT_WILD(__) <|  nil(), localDecls =  nil(), body =  nil(), result = SOME(e2)) <|  nil()) where (! Types.isTuple(ty))  => begin
                      e1_1 = if b1
                            e1
                          else
                            e2
                          end
                      e2_1 = if b1
                            e2
                          else
                            e1
                          end
                      e = DAE.IFEXP(e, e1_1, e2_1)
                    e
                  end

                  _  => begin
                      exp
                  end
                end
              end
          outExp
        end

         #= help function to simplify1 =#
        function simplifyCast(origExp::DAE.Exp, exp::DAE.Exp, tp::Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local r::ModelicaReal
                  local i::ModelicaInteger
                  local n::ModelicaInteger
                  local b::Bool
                  local exps::List{DAE.Exp}
                  local exps_1::List{DAE.Exp}
                  local t::Type
                  local tp_1::Type
                  local tp1::Type
                  local tp2::Type
                  local t1::Type
                  local t2::Type
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cond::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e::DAE.Exp
                  local mexps::List{List{DAE.Exp}}
                  local mexps_1::List{List{DAE.Exp}}
                  local eo::Option{DAE.Exp}
                  local dims::DAE.Dimensions
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local p3::Absyn.Path
                  local fieldNames::List{String}
                   #=  Real -> Real
                   =#
                @match (origExp, exp, tp) begin
                  (_, DAE.RCONST(r), DAE.T_REAL(__))  => begin
                    DAE.RCONST(r)
                  end

                  (_, DAE.ICONST(i), DAE.T_REAL(__))  => begin
                      r = intReal(i)
                    DAE.RCONST(r)
                  end

                  (_, DAE.UNARY(DAE.UMINUS_ARR(_), e), _)  => begin
                      e = addCast(e, tp)
                    DAE.UNARY(DAE.UMINUS_ARR(tp), e)
                  end

                  (_, DAE.UNARY(DAE.UMINUS(_), e), _)  => begin
                      e = addCast(e, tp)
                    DAE.UNARY(DAE.UMINUS(tp), e)
                  end

                  (_, DAE.ARRAY(_, b, exps), _)  => begin
                      tp_1 = Expression.unliftArray(tp)
                      exps_1 = ListUtil.map1(exps, addCast, tp_1)
                    DAE.ARRAY(tp, b, exps_1)
                  end

                  (_, DAE.RANGE(ty = DAE.T_INTEGER(__), start = e1, step = eo, stop = e2), DAE.T_ARRAY(ty = tp2 && DAE.T_REAL(__)))  => begin
                      e1 = addCast(e1, tp2)
                      e2 = addCast(e2, tp2)
                      eo = Util.applyOption1(eo, addCast, tp2)
                    DAE.RANGE(tp2, e1, eo, e2)
                  end

                  (_, DAE.IFEXP(cond, e1, e2), _)  => begin
                      e1_1 = DAE.CAST(tp, e1)
                      e2_1 = DAE.CAST(tp, e2)
                    DAE.IFEXP(cond, e1_1, e2_1)
                  end

                  (_, DAE.MATRIX(_, n, mexps), _)  => begin
                      tp1 = Expression.unliftArray(tp)
                      tp2 = Expression.unliftArray(tp1)
                      mexps_1 = ListUtil.map1List(mexps, addCast, tp2)
                    DAE.MATRIX(tp, n, mexps_1)
                  end

                  (_, DAE.CALL(p1, exps, DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p2)))), DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p3))) where (AbsynUtil.pathEqual(p1, p2))  #= It is a record constructor since it has the same path called as its output type =# => begin
                    DAE.CALL(p3, exps, DAE.CALL_ATTR(tp, false, false, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
                  end

                  (_, DAE.RECORD(_, exps, fieldNames, _), DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p3)))  => begin
                    DAE.RECORD(p3, exps, fieldNames, tp)
                  end

                  (_, DAE.CALL(path = Absyn.IDENT("fill"), expLst = e <| exps), _)  => begin
                      tp_1 = ListUtil.fold(exps, Expression.unliftArrayIgnoreFirst, tp)
                      e = DAE.CAST(tp_1, e)
                      e = Expression.makePureBuiltinCall("fill", _cons(e, exps), tp)
                    e
                  end

                  (_, DAE.CALL(path = Absyn.IDENT("cat"), expLst = e && DAE.ICONST(n) <| exps), DAE.T_ARRAY(dims = dims)) where (Expression.dimensionUnknown(listGet(dims, n)))  => begin
                      exps = ListUtil.map1(exps, addCast, tp)
                    Expression.makePureBuiltinCall("cat", _cons(e, exps), tp)
                  end

                  (_, e, _)  => begin
                      t1 = Expression.arrayEltType(tp)
                      t2 = Expression.arrayEltType(Expression.typeOf(e))
                    if valueEq(t1, t2)
                          e
                        else
                          origExp
                        end
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  Int -> Real
               =#
               #=  cast of unary
               =#
               #=  cast of unary
               =#
               #=  cast of array
               =#
               #=  cast of array
               =#
               #=  simplify cast in an if expression
               =#
               #=  simplify cast of matrix expressions
               =#
               #=  simplify record constructor from one to another
               =#
               #=  fill(e, ...) can be simplified
               =#
               #=  cat(e, ...) can be simplified
               =#
               #=  expression already has a specified cast type.
               =#
          outExp
        end

         #= Adds a cast of a Type to an expression. =#
        function addCast(inExp::DAE.Exp, inType::Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = DAE.CAST(inType, inExp)
          outExp
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
                       str = "elabBuiltinFill2 failed in component" + PrefixUtil.printPrefixStr3(inPrefix) + " and scope: " + FGraphUtil.printGraphPathStr(inEnv) + " for expression: fill(" + Dump.printExpLstStr(inDims) + ")"
                       Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), inInfo)
                     fail()
                 end
               end
             end
              #=  fill with 0 then!
              =#
         (outCache, outExp, outProperties)
       end

         #= simplifies some builtin calls (with no constant expressions) =#
        function simplifyBuiltinCalls(exp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local mexpl::List{List{DAE.Exp}}
                  local es::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local e::DAE.Exp
                  local len_exp::DAE.Exp
                  local just_exp::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local tp::DAE.Type
                  local tp1::DAE.Type
                  local tp2::DAE.Type
                  local op::DAE.Operator
                  local v1::List{DAE.Exp}
                  local v2::List{DAE.Exp}
                  local scalar::Bool
                  local sc::Bool
                  local valueLst::List{Values.Value}
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local dim::ModelicaInteger
                  local r1::ModelicaReal
                  local marr::Array{Array{DAE.Exp}}
                  local name::String
                  local s1::String
                  local s2::String
                  local dims::List{ModelicaInteger}
                   #=  If the argument to min/max is an array, try to flatten it.
                   =#
                @matchcontinue exp begin
                  DAE.CALL(path = Absyn.IDENT(name), expLst = e && DAE.ARRAY(__) <|  nil(), attr = DAE.CALL_ATTR(ty = tp)) where (name == "max" || name == "min")  => begin
                      expl = Expression.flattenArrayExpToList(e)
                      e1 = Expression.makeScalarArray(expl, tp)
                      @match false = Expression.expEqual(e, e1)
                    Expression.makePureBuiltinCall(name, list(e1), tp)
                  end

                  DAE.CALL(path = Absyn.IDENT(name), expLst = DAE.ARRAY(array = expl && e <|  nil()) <|  nil()) where (name == "max" || name == "min")  => begin
                       #=  min/max function on arrays of only 1 element
                       =#
                      if Expression.isArrayType(Expression.typeOf(e))
                        @set exp.expLst = expl
                        e = exp
                      end
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("max"), expLst = DAE.ARRAY(array = e <|  nil()) <|  nil())  => begin
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("max"), expLst = DAE.ARRAY(array = es) <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      i1 = listLength(es)
                      es = ListUtil.union(es, nil)
                      i2 = listLength(es)
                      if i1 == i2
                        @match SOME(e) = ListUtil.fold(es, maxElement, NONE())
                        es = ListUtil.select(es, removeMinMaxFoldableValues)
                        es = _cons(e, es)
                        i2 = listLength(es)
                        @match true = i2 < i1
                        e = Expression.makeScalarArray(es, tp)
                      else
                        e = Expression.makeScalarArray(es, tp)
                      end
                    Expression.makePureBuiltinCall("max", list(e), tp)
                  end

                  DAE.CALL(path = Absyn.IDENT("min"), expLst = DAE.ARRAY(array = es) <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      i1 = listLength(es)
                      es = ListUtil.union(es, nil)
                      i2 = listLength(es)
                      if i1 == i2
                        @match SOME(e) = ListUtil.fold(es, minElement, NONE())
                        es = ListUtil.select(es, removeMinMaxFoldableValues)
                        es = _cons(e, es)
                        i2 = listLength(es)
                        @match true = i2 < i1
                        e = Expression.makeScalarArray(es, tp)
                      else
                        e = Expression.makeScalarArray(es, tp)
                      end
                    Expression.makePureBuiltinCall("min", list(e), tp)
                  end

                  DAE.CALL(path = Absyn.IDENT("min"), attr = DAE.CALL_ATTR(ty = tp), expLst = DAE.ARRAY(array = e1 <| e2 <|  nil()) <|  nil())  => begin
                      e = Expression.makePureBuiltinCall("min", list(e1, e2), tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("max"), attr = DAE.CALL_ATTR(ty = tp), expLst = DAE.ARRAY(array = e1 <| e2 <|  nil()) <|  nil())  => begin
                      e = Expression.makePureBuiltinCall("max", list(e1, e2), tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("min"), attr = DAE.CALL_ATTR(ty = DAE.T_BOOL(__)), expLst = e1 <| e2 <|  nil())  => begin
                      e = DAE.LBINARY(e1, DAE.AND(DAE.T_BOOL_DEFAULT), e2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("max"), attr = DAE.CALL_ATTR(ty = DAE.T_BOOL(__)), expLst = e1 <| e2 <|  nil())  => begin
                      e = DAE.LBINARY(e1, DAE.OR(DAE.T_BOOL_DEFAULT), e2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("min"), attr = DAE.CALL_ATTR(ty = DAE.T_BOOL(__)), expLst = DAE.ARRAY(array = expl) <|  nil())  => begin
                      e = Expression.makeLBinary(expl, DAE.AND(DAE.T_BOOL_DEFAULT))
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("max"), attr = DAE.CALL_ATTR(ty = DAE.T_BOOL(__)), expLst = DAE.ARRAY(array = expl) <|  nil())  => begin
                      e = Expression.makeLBinary(expl, DAE.OR(DAE.T_BOOL_DEFAULT))
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT(name), expLst = DAE.ARRAY(array = expl && _ <| _ <| _) <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      @match true = Config.scalarizeMinMax()
                      @match true = stringEq(name, "max") || stringEq(name, "min")
                      @match _cons(e1, _cons(e2, expl)) = listReverse(expl)
                      e1 = Expression.makePureBuiltinCall(name, list(e2, e1), tp)
                      e1 = ListUtil.fold2(expl, makeNestedReduction, name, tp, e1)
                    e1
                  end

                  e && DAE.CALL(path = Absyn.IDENT("cross"), expLst = expl)  => begin
                      @match DAE.ARRAY(array = v1) <| DAE.ARRAY(array = v2) <| nil = expl
                      expl = simplifyCross(v1, v2)
                      tp = Expression.typeOf(e)
                      scalar = ! Expression.isArrayType(Expression.unliftArray(tp))
                    DAE.ARRAY(tp, scalar, expl)
                  end

                  e && DAE.CALL(path = Absyn.IDENT("skew"), expLst = DAE.ARRAY(array = v1) <|  nil())  => begin
                      mexpl = simplifySkew(v1)
                      tp = Expression.typeOf(e)
                    DAE.MATRIX(tp, 3, mexpl)
                  end

                  DAE.CALL(path = Absyn.IDENT("fill"), expLst = e <| expl)  => begin
                      valueLst = ListUtil.map(expl, ValuesUtil.expValue)
                      (_, outExp, _) = elabBuiltinFill2(FCoreUtil.noCache(), FCore.emptyGraph, e, Expression.typeOf(e), valueLst, DAE.C_CONST(), Prefix.NOPRE(), nil, AbsynUtil.dummyInfo)
                    outExp
                  end

                  DAE.CALL(path = Absyn.IDENT("String"), expLst = e <| len_exp <| just_exp <|  nil())  => begin
                    simplifyBuiltinStringFormat(e, len_exp, just_exp)
                  end

                  DAE.CALL(path = Absyn.IDENT("stringAppendList"), expLst = DAE.LIST(expl) <|  nil())  => begin
                    simplifyStringAppendList(expl, nil, false)
                  end

                  DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = DAE.BINARY(e1, DAE.POW(ty = DAE.T_REAL(__)), e2) <|  nil())  => begin
                      e = DAE.BINARY(e1, DAE.POW(DAE.T_REAL_DEFAULT), DAE.BINARY(DAE.RCONST(0.5), DAE.MUL(DAE.T_REAL_DEFAULT), e2))
                    Expression.makePureBuiltinCall("abs", list(e), DAE.T_REAL_DEFAULT)
                  end

                  DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()) <|  nil())  => begin
                    DAE.BINARY(e1, DAE.POW(DAE.T_REAL_DEFAULT), DAE.RCONST(0.25))
                  end

                  DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = DAE.BINARY(e1 && DAE.RCONST(r1), DAE.MUL(tp), e2) <|  nil())  => begin
                      @match true = r1 >= 0.0
                      e = Expression.makePureBuiltinCall("sqrt", list(e1), DAE.T_REAL_DEFAULT)
                      e3 = Expression.makePureBuiltinCall("sqrt", list(e2), DAE.T_REAL_DEFAULT)
                    DAE.BINARY(e, DAE.MUL(tp), e3)
                  end

                  DAE.CALL(path = Absyn.IDENT("exp"), expLst = DAE.UNARY(DAE.UMINUS(__), e1) <|  nil())  => begin
                      expl = Expression.expandFactors(e1)
                      @match (e2 <| nil, es) = ListUtil.split1OnTrue(expl, Expression.isFunCall, "log")
                      @match DAE.CALL(expLst = e <| nil) = e2
                      e3 = Expression.makeProductLst(es)
                    Expression.expPow(e, Expression.negate(e3))
                  end

                  DAE.CALL(path = Absyn.IDENT("exp"), expLst = e1 <|  nil())  => begin
                      expl = Expression.expandFactors(e1)
                      @match (e2 <| nil, es) = ListUtil.split1OnTrue(expl, Expression.isFunCall, "log")
                      @match DAE.CALL(expLst = e <| nil) = e2
                      e3 = Expression.makeProductLst(es)
                    Expression.expPow(e, e3)
                  end

                  DAE.BINARY(DAE.CALL(path = Absyn.IDENT("exp"), expLst = e <|  nil()), DAE.POW(ty = DAE.T_REAL(__)), e2)  => begin
                      e3 = Expression.expMul(e, e2)
                    Expression.makePureBuiltinCall("exp", list(e3), DAE.T_REAL_DEFAULT)
                  end

                  DAE.CALL(path = Absyn.IDENT("log"), expLst = DAE.BINARY(e1, DAE.POW(ty = DAE.T_REAL(__)), DAE.RCONST(r1)) <|  nil())  => begin
                      @match 1.0 = realMod(r1, 2.0)
                      e3 = Expression.makePureBuiltinCall("log", list(e1), DAE.T_REAL_DEFAULT)
                    Expression.expMul(DAE.RCONST(r1), e3)
                  end

                  DAE.CALL(path = Absyn.IDENT("log"), expLst = DAE.BINARY(DAE.RCONST(1.0), DAE.DIV(ty = DAE.T_REAL(__)), e2) <|  nil())  => begin
                      e3 = Expression.makePureBuiltinCall("log", list(e2), DAE.T_REAL_DEFAULT)
                    DAE.UNARY(DAE.UMINUS(DAE.T_REAL_DEFAULT), e3)
                  end

                  DAE.CALL(path = Absyn.IDENT("log"), expLst = DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()) <|  nil())  => begin
                      e3 = Expression.makePureBuiltinCall("log", list(e1), DAE.T_REAL_DEFAULT)
                    DAE.BINARY(DAE.RCONST(0.5), DAE.MUL(DAE.T_REAL_DEFAULT), e3)
                  end

                  DAE.CALL(path = Absyn.IDENT("smooth"), expLst = _ <| e1 <|  nil()) where (Expression.isConst(e1))  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("\$_DF\$DER"), expLst = e1 <|  nil()) where (Expression.isConst(e1))  => begin
                    Expression.makeConstZeroE(e1)
                  end

                  e && DAE.CALL(path = Absyn.IDENT("delay"), expLst = e1 <| e2 <|  nil())  => begin
                       #=  cross
                       =#
                       #=  Since there is a bug somewhere in simplify that gives wrong types for arrays we take the type from cross.
                       =#
                       #=  Simplify built-in function fill. MathCore depends on this being done here, do not remove!
                       =#
                       #=  sqrt(e ^ r) => e ^ (0.5 * r)
                       =#
                       #=  sqrt(sqrt(e)) => e ^ (0.25)
                       =#
                       #=  sqrt(c*e) => c1*sqrt(e)
                       =#
                       #=  exp(-(...*log(x)*...))
                       =#
                       #=  exp(...*log(x)*...)
                       =#
                       #=  exp(e)^r = exp(e*r)
                       =#
                       #=  log(x^n) = n*log(x)
                       =#
                       #=  log(1/x) = -log(x)
                       =#
                       #=  log(sqrt(x)) = 0.5*log(x)
                       =#
                       #=  smooth of constant expression
                       =#
                       #=  df_der(const) --> 0
                       =#
                       #=  We only match delay with 3 arguments in most places...
                       =#
                      @set e.expLst = list(e1, e2, e2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("delay"), expLst = e1 <| _ <| _ <|  nil()) where (Expression.isConst(e1))  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("delay"), expLst = DAE.BINARY(e1, op, e2) <| e3 <| e4 <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      @match true = Expression.isConst(e1)
                      e = Expression.makeImpureBuiltinCall("delay", list(e2, e3, e4), tp)
                    DAE.BINARY(e1, op, e)
                  end

                  DAE.CALL(path = Absyn.IDENT("delay"), expLst = DAE.BINARY(e1, op, e2) <| e3 <| e4 <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      @match true = Expression.isConst(e2)
                      e = Expression.makeImpureBuiltinCall("delay", list(e1, e3, e4), tp)
                    DAE.BINARY(e, op, e2)
                  end

                  DAE.CALL(path = Absyn.IDENT("delay"), expLst = DAE.UNARY(op, e) <| e3 <| e4 <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      e = Expression.makeImpureBuiltinCall("delay", list(e, e3, e4), tp)
                    DAE.UNARY(op, e)
                  end

                  DAE.CALL(path = Absyn.IDENT("sum"), expLst = DAE.ARRAY(array =  nil()) <|  nil(), attr = DAE.CALL_ATTR(ty = tp1))  => begin
                    Expression.makeConstZero(tp1)
                  end

                  DAE.CALL(path = Absyn.IDENT("sum"), expLst = DAE.MATRIX(ty = tp1, matrix = mexpl) <|  nil(), attr = DAE.CALL_ATTR(ty = tp2))  => begin
                      es = ListUtil.flatten(mexpl)
                      tp1 = Expression.unliftArray(Expression.unliftArray(tp1))
                      sc = ! Expression.isArrayType(tp1)
                      tp1 = if sc
                            Expression.unliftArray(tp1)
                          else
                            tp1
                          end
                      tp1 = if sc
                            Expression.liftArrayLeft(tp1, DAE.DIM_UNKNOWN())
                          else
                            tp1
                          end
                      dim = listLength(es)
                      tp1 = Expression.liftArrayLeft(tp1, DAE.DIM_INTEGER(dim))
                      e = DAE.ARRAY(tp1, sc, es)
                      e = Expression.makePureBuiltinCall("sum", list(e), tp2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("sum"), expLst = DAE.ARRAY(array = es, ty = tp1, scalar = false) <|  nil(), attr = DAE.CALL_ATTR(ty = tp2))  => begin
                      es = simplifyCat(1, es)
                      tp1 = Expression.unliftArray(tp1)
                      sc = ! Expression.isArrayType(tp1)
                      tp1 = if sc
                            Expression.unliftArray(tp1)
                          else
                            tp1
                          end
                      tp1 = if sc
                            Expression.liftArrayLeft(tp1, DAE.DIM_UNKNOWN())
                          else
                            tp1
                          end
                      dim = listLength(es)
                      tp1 = Expression.liftArrayLeft(tp1, DAE.DIM_INTEGER(dim))
                      e = DAE.ARRAY(tp1, sc, es)
                      e = Expression.makePureBuiltinCall("sum", list(e), tp2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("sum"), expLst = DAE.ARRAY(array = e <|  nil(), scalar = false) <|  nil(), attr = DAE.CALL_ATTR(ty = tp2))  => begin
                      e = Expression.makePureBuiltinCall("sum", list(e), tp2)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("sum"), expLst = DAE.ARRAY(array = es, scalar = true) <|  nil())  => begin
                      e = Expression.makeSum(es)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("cat"), expLst = _ <| e1 <|  nil())  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("cat"), expLst = DAE.ICONST(i) <| es, attr = DAE.CALL_ATTR(ty = tp))  => begin
                      es = simplifyCat(i, es)
                      e = Expression.makePureBuiltinCall("cat", _cons(DAE.ICONST(i), es), tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("cat"), expLst = DAE.ICONST(i) <| es, attr = DAE.CALL_ATTR(ty = tp))  => begin
                       #=  delay of constant expression
                       =#
                       #=  delay of constant subexpression
                       =#
                       #=  delay of constant subexpression
                       =#
                       #=  delay(-x) = -delay(x)
                       =#
                       #=  The sum of an empty array is simply the sum of its elements
                       =#
                       #=  To calculate sums, first try matrix concatenation
                       =#
                       #=  print(\"Matrix sum: \" + boolString(sc) + Types.unparseType(tp1) + \" \" + CrefForHashTable.printExpStr(e) + \"\\n\");
                       =#
                       #=  Then try array concatenation
                       =#
                       #=  print(\"Array sum: \" + boolString(sc) + Types.unparseType(tp1) + \" \" + CrefForHashTable.printExpStr(e) + \"\\n\");
                       =#
                       #=  Try to reduce the number of dimensions
                       =#
                       #=  The sum of a single array is simply the sum of its elements
                       =#
                      (es, dims) = evalCat(i, es, getArrayContents = Expression.getArrayOrMatrixContents, toString = CrefForHashTable.printExpStr)
                      e = Expression.listToArray(es, list(DAE.DIM_INTEGER(d) for d in dims))
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("promote"), expLst = e1 <| DAE.ICONST(i) <|  nil()) where (Types.numberOfDimensions(Expression.typeOf(e1)) == i)  => begin
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("promote"), expLst = DAE.ARRAY(tp1 && DAE.T_ARRAY(dims = _ <|  nil()), sc, es) <| DAE.ICONST(2) <|  nil())  => begin
                      tp = Types.liftArray(Types.unliftArray(tp1), DAE.DIM_INTEGER(1))
                      es = ListUtil.map2(ListUtil.map(es, ListUtil.create), Expression.makeArray, tp, sc)
                      i = listLength(es)
                      tp = Expression.liftArrayLeft(tp, DAE.DIM_INTEGER(i))
                    DAE.ARRAY(tp, false, es)
                  end

                  DAE.CALL(path = Absyn.IDENT("promote"), expLst = e1 <| DAE.ICONST(i) <|  nil()) where (! Types.isArray(Expression.typeOf(e1)))  => begin
                       #=  promote n-dim to n-dim
                       =#
                       #=  promote 1-dim to 2-dim
                       =#
                       #=  scalar to n-dim
                       =#
                      tp = Expression.typeOf(e1)
                      for j in 1:i
                        tp1 = Types.liftArray(tp, DAE.DIM_INTEGER(1))
                        e1 = Expression.makeArray(list(e1), tp1, ! Types.isArray(tp))
                        tp = tp1
                      end
                    e1
                  end

                  DAE.CALL(path = Absyn.IDENT("transpose"), expLst = e <|  nil(), attr = DAE.CALL_ATTR(__))  => begin
                      @match (e, true) = Expression.transposeArray(e)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("symmetric"), expLst = e <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      mexpl = Expression.get2dArrayOrMatrixContent(e)
                      e = begin
                        @match mexpl begin
                           nil() <|  nil()  => begin
                            e
                          end

                          _ <|  nil() <|  nil()  => begin
                            e
                          end

                          _  => begin
                              marr = listArray(ListUtil.map(mexpl, listArray))
                              @match true = arrayLength(marr) == arrayLength(arrayGet(marr, 1))
                              @match true = arrayLength(marr) > 1
                              simplifySymmetric(marr, arrayLength(marr) - 1, arrayLength(marr))
                              mexpl = ListUtil.map(arrayList(marr), arrayList)
                              tp1 = Expression.unliftArray(tp)
                              es = ListUtil.map2(mexpl, Expression.makeArray, tp1, ! Types.isArray(tp1))
                              e = Expression.makeArray(es, tp, false)
                            e
                          end
                        end
                      end
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("scalar"), expLst = e <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      e = simplifyScalar(e, tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("vector"), expLst = es && e <| _, attr = DAE.CALL_ATTR(ty = DAE.T_ARRAY(tp, _)))  => begin
                      @match false = Types.isArray(Expression.typeOf(e))
                      i = listLength(es)
                      tp = DAE.T_ARRAY(tp, list(DAE.DIM_INTEGER(i)))
                    DAE.ARRAY(tp, true, es)
                  end

                  DAE.CALL(path = Absyn.IDENT("vector"), expLst = e && DAE.ARRAY(scalar = true) <|  nil(), attr = DAE.CALL_ATTR(__))  => begin
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("vector"), expLst = DAE.MATRIX(matrix = mexpl) <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      es = ListUtil.flatten(mexpl)
                      es = ListUtil.map1(es, Expression.makeVectorCall, tp)
                      e = Expression.makePureBuiltinCall("cat", _cons(DAE.ICONST(1), es), tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("vector"), expLst = DAE.ARRAY(array = es) <|  nil(), attr = DAE.CALL_ATTR(ty = tp))  => begin
                      es = ListUtil.map1(es, Expression.makeVectorCall, tp)
                      e = Expression.makePureBuiltinCall("cat", _cons(DAE.ICONST(1), es), tp)
                    e
                  end

                  DAE.CALL(path = Absyn.IDENT("inferredClock"), expLst =  nil())  => begin
                    DAE.CLKCONST(DAE.INFERRED_CLOCK())
                  end

                  DAE.CALL(path = Absyn.IDENT("realClock"), expLst = e1 <|  nil())  => begin
                    DAE.CLKCONST(DAE.REAL_CLOCK(e1))
                  end

                  DAE.CALL(path = Absyn.IDENT("booleanClock"), expLst = e1 <| e2 <|  nil())  => begin
                    DAE.CLKCONST(DAE.BOOLEAN_CLOCK(e1, e2))
                  end

                  DAE.CALL(path = Absyn.IDENT("rationalClock"), expLst = e1 <| e2 <|  nil())  => begin
                    DAE.CLKCONST(DAE.INTEGER_CLOCK(e1, e2))
                  end

                  DAE.CALL(path = Absyn.IDENT("solverClock"), expLst = e1 <| e2 <|  nil())  => begin
                    DAE.CLKCONST(DAE.SOLVER_CLOCK(e1, e2))
                  end

                  DAE.CALL(path = Absyn.IDENT("OpenModelica_uriToFilename"), expLst = DAE.SCONST(s1) <|  nil())  => begin
                       #= /* Current design uses a special DAE.Expression */ =#
                      s2 = OpenModelica.Scripting.uriToFilename(s1)
                      if Flags.getConfigBool(Flags.BUILDING_FMU)
                        e = Expression.makeImpureBuiltinCall("OpenModelica_fmuLoadResource", list(DAE.SCONST(s2)), DAE.T_STRING_DEFAULT)
                      else
                        e = DAE.SCONST(s2)
                      end
                    e
                  end
                end
              end
          outExp
        end

         #= Handle the scalar() operator =#
        function simplifyScalar(inExp::DAE.Exp, tp::DAE.Type) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                @match (inExp, tp) begin
                  (DAE.ARRAY(array = exp <|  nil()), _)  => begin
                    Expression.makePureBuiltinCall("scalar", list(exp), tp)
                  end

                  (DAE.MATRIX(matrix = exp <|  nil() <|  nil()), _)  => begin
                    Expression.makePureBuiltinCall("scalar", list(exp), tp)
                  end

                  (DAE.SIZE(exp = exp, sz = NONE()), _)  => begin
                      @match (_, _ <| nil) = Types.flattenArrayType(Expression.typeOf(inExp))
                    DAE.SIZE(exp, SOME(DAE.ICONST(1)))
                  end

                  _  => begin
                        @match (_, nil) = Types.flattenArrayType(Expression.typeOf(inExp))
                      inExp
                  end
                end
              end
          exp
        end

        function makeNestedReduction(inExp::DAE.Exp, inName::String, inType::DAE.Type, inCall::DAE.Exp) ::DAE.Exp
              local outCall::DAE.Exp

              outCall = Expression.makePureBuiltinCall(inName, list(inExp, inCall), inType)
          outCall
        end

        function simplifySymmetric(marr::Array{<:Array{<:DAE.Exp}}, i1::ModelicaInteger, i2::ModelicaInteger)
              _ = begin
                  local v1::Array{DAE.Exp}
                  local v2::Array{DAE.Exp}
                  local exp::DAE.Exp
                @match (marr, i1, i2) begin
                  (_, 0, 1)  => begin
                    ()
                  end

                  _  => begin
                        v1 = arrayGet(marr, i1)
                        v2 = arrayGet(marr, i2)
                        exp = arrayGet(v1, i2)
                        arrayUpdate(v2, i1, exp)
                        simplifySymmetric(marr, if i1 == 1
                              i2 - 2
                            else
                              i1 - 1
                            end, if i1 == 1
                              i2 - 1
                            else
                              i2
                            end)
                      ()
                  end
                end
              end
        end

        function simplifyCat(inDim::ModelicaInteger, inExpList::List{<:DAE.Exp}) ::List{DAE.Exp}
              local outExpList::List{DAE.Exp}

              outExpList = begin
                  local expl::List{DAE.Exp}
                @match (inDim, inExpList) begin
                  (1, _)  => begin
                      expl = ListUtil.map(inExpList, simplifyCatArg)
                    simplifyCat2(inDim, expl, nil, false)
                  end

                  _  => begin
                      simplifyCat2(inDim, inExpList, nil, false)
                  end
                end
              end
          outExpList
        end

        function simplifyCatArg(arg::DAE.Exp) ::DAE.Exp
              local outArg::DAE.Exp

              outArg = begin
                  local dim::DAE.Dimension
                @match arg begin
                  DAE.MATRIX(__)  => begin
                    Expression.matrixToArray(arg)
                  end

                  DAE.CREF(ty = DAE.T_ARRAY(dims = dim <|  nil())) where (Expression.dimensionKnown(dim))  => begin
                    DAE.ARRAY(arg.ty, true, Expression.expandExpression(arg, false))
                  end

                  _  => begin
                      arg
                  end
                end
              end
          outArg
        end

        function simplifyCat2(dim::ModelicaInteger, ies::List{<:DAE.Exp}, acc::List{<:DAE.Exp}, changed::Bool) ::List{DAE.Exp}
              local oes::List{DAE.Exp}

              oes = begin
                  local es1::List{DAE.Exp}
                  local es2::List{DAE.Exp}
                  local esn::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local e::DAE.Exp
                  local e2::DAE.Exp
                  local ndim::DAE.Dimension
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local dim11::DAE.Dimension
                  local dims::DAE.Dimensions
                  local etp::DAE.Type
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i::ModelicaInteger
                  local ms1::List{List{DAE.Exp}}
                  local ms2::List{List{DAE.Exp}}
                  local mss::List{List{DAE.Exp}}
                  local sc::Bool
                @matchcontinue (dim, ies, acc, changed) begin
                  (_,  nil(), _, true)  => begin
                    listReverse(acc)
                  end

                  (1, DAE.ARRAY(array = es1, scalar = sc, ty = DAE.T_ARRAY(dims = dim1 <| dims, ty = etp)) <| DAE.ARRAY(array = es2, ty = DAE.T_ARRAY(dims = dim2 <| _)) <| es, _, _)  => begin
                      esn = listAppend(es1, es2)
                      ndim = Expression.addDimensions(dim1, dim2)
                      etp = DAE.T_ARRAY(etp, _cons(ndim, dims))
                      e = DAE.ARRAY(etp, sc, esn)
                    simplifyCat2(dim, _cons(e, es), acc, true)
                  end

                  (2, DAE.MATRIX(matrix = ms1, integer = i, ty = DAE.T_ARRAY(dims = dim11 <| dim1 <| dims, ty = etp)) <| DAE.MATRIX(matrix = ms2, ty = DAE.T_ARRAY(dims = _ <| dim2 <| _)) <| es, _, _)  => begin
                      mss = ListUtil.threadMap(ms1, ms2, listAppend)
                      ndim = Expression.addDimensions(dim1, dim2)
                      etp = DAE.T_ARRAY(etp, _cons(dim11, _cons(ndim, dims)))
                      e = DAE.MATRIX(etp, i, mss)
                    simplifyCat2(dim, _cons(e, es), acc, true)
                  end

                  (_, e <| es, _, _)  => begin
                    simplifyCat2(dim, es, _cons(e, acc), changed)
                  end
                end
              end
          oes
        end

        function evalCat(dim::ModelicaInteger, exps::List{Exp}, getArrayContents::GetArrayContents, toString::ToString)  where {Exp}
              local outDims::List{ModelicaInteger}
              local outExps::List{Exp}

              local arr::List{Exp}
              local arrs::List{List{Exp}} = nil
              local dims::List{ModelicaInteger}
              local firstDims::List{ModelicaInteger} = nil
              local lastDims::List{ModelicaInteger}
              local reverseDims::List{ModelicaInteger}
              local dimsLst::List{List{ModelicaInteger}} = nil
              local j::ModelicaInteger
              local k::ModelicaInteger
              local l::ModelicaInteger
              local thisDim::ModelicaInteger
              local lastDim::ModelicaInteger
              local expArr::Array{Exp}

              @match true = dim >= 1
              @match false = listEmpty(exps)
              if 1 == dim
                outExps = listAppend(getArrayContents(e) for e in listReverse(exps))
                outDims = list(listLength(outExps))
                return (outExps, outDims)
              end
              for e in listReverse(exps)
                (arr, dims) = evalCatGetFlatArray(e, dim, getArrayContents = getArrayContents, toString = toString)
                arrs = _cons(arr, arrs)
                dimsLst = _cons(dims, dimsLst)
              end
               #=  Here we get a linear representation of all expressions in the array
               =#
               #=  and the dimensions necessary to build up the array again
               =#
              for i in 1:dim - 1
                j = min(listHead(d) for d in dimsLst)
                if j != max(listHead(d) for d in dimsLst)
                  Error.assertion(false, getInstanceName() + ": cat got uneven dimensions for dim=" + String(i) + " " + stringDelimitList(list(toString(e) for e in exps), ", "), sourceInfo())
                end
                firstDims = _cons(j, firstDims)
                dimsLst = list(listRest(d) for d in dimsLst)
              end
              reverseDims = firstDims
              firstDims = listReverse(firstDims)
              lastDims = list(listHead(d) for d in dimsLst)
              lastDim = sum(d for d in lastDims)
              reverseDims = _cons(lastDim, reverseDims)
               #=  Fill in the elements of the new array in the new order; this uses
               =#
               #=  an array structure for random access
               =#
              expArr = arrayCreate(lastDim * product(d for d in firstDims), listHead(listHead(arrs)))
              k = 1
              for exps in arrs
                @match _cons(thisDim, lastDims) = lastDims
                l = 0
                for e in exps
                  arrayUpdate(expArr, k + mod(l, thisDim) + lastDim * div(l, thisDim), e)
                  l = l + 1
                end
                k = k + thisDim
              end
               #=  Convert the flat array structure to a tree array structure with the
               =#
               #=  correct dimensions
               =#
              outExps = arrayList(expArr)
              outDims = listReverse(reverseDims)
          (outExps, outDims)
        end

        function evalCatGetFlatArray(e::Exp, dim::ModelicaInteger, getArrayContents::GetArrayContents, toString::ToString)  where {Exp}
              local outDims::List{ModelicaInteger} = nil
              local outExps::List{Exp} = nil

              local arr::List{Exp}
              local dims::List{ModelicaInteger}
              local i::ModelicaInteger

              if dim == 1
                outExps = getArrayContents(e)
                outDims = list(listLength(outExps))
                return (outExps, outDims)
              end
              i = 0
              for exp in listReverse(getArrayContents(e))
                (arr, dims) = evalCatGetFlatArray(exp, dim - 1, getArrayContents = getArrayContents, toString = toString)
                if listEmpty(outDims)
                  outDims = dims
                elseif ! valueEq(dims, outDims)
                  Error.assertion(false, getInstanceName() + ": Got unbalanced array from " + toString(e), sourceInfo())
                end
                outExps = listAppend(arr, outExps)
                i = i + 1
              end
              outDims = _cons(i, outDims)
          (outExps, outDims)
        end

        function simplifyBuiltinStringFormat(exp::DAE.Exp, len_exp::DAE.Exp, just_exp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local i::ModelicaInteger
                  local len::ModelicaInteger
                  local r::ModelicaReal
                  local b::Bool
                  local just::Bool
                  local str::String
                  local name::Absyn.Path
                @match (exp, len_exp, just_exp) begin
                  (DAE.ICONST(i), DAE.ICONST(len), DAE.BCONST(just))  => begin
                      str = intString(i)
                      str = cevalBuiltinStringFormat(str, stringLength(str), len, just)
                    DAE.SCONST(str)
                  end

                  (DAE.RCONST(r), DAE.ICONST(len), DAE.BCONST(just))  => begin
                      str = realString(r)
                      str = cevalBuiltinStringFormat(str, stringLength(str), len, just)
                    DAE.SCONST(str)
                  end

                  (DAE.BCONST(b), DAE.ICONST(len), DAE.BCONST(just))  => begin
                      str = boolString(b)
                      str = cevalBuiltinStringFormat(str, stringLength(str), len, just)
                    DAE.SCONST(str)
                  end

                  (DAE.ENUM_LITERAL(name = name), DAE.ICONST(len), DAE.BCONST(just))  => begin
                      str = AbsynUtil.pathLastIdent(name)
                      str = cevalBuiltinStringFormat(str, stringLength(str), len, just)
                    DAE.SCONST(str)
                  end
                end
              end
          outExp
        end

         #= Helper function to cevalBuiltinStringFormat, does the actual formatting. =#
        function cevalBuiltinStringFormat(inString::String, stringLength::ModelicaInteger, minLength::ModelicaInteger, leftJustified::Bool) ::String
              local outString::String

              outString = if stringLength >= minLength
                    inString
                  else
                    if leftJustified
                          inString + stringAppendList(ListUtil.fill(" ", minLength - stringLength))
                        else
                          stringAppendList(ListUtil.fill(" ", minLength - stringLength)) + inString
                        end
                  end
          outString
        end

         #=
        stringAppendList({abc,def,String(time),ghi,jkl}) => stringAppendList({abcdef,String(time),ghijkl})
        stringAppendList({abc,def,ghi,jkl}) => abcdefghijkl
        stringAppendList({}) => abcdefghijkl
         =#
        function simplifyStringAppendList(iexpl::List{<:DAE.Exp}, iacc::List{<:DAE.Exp}, ichange::Bool) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local s1::String
                  local s2::String
                  local s::String
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local rest::List{DAE.Exp}
                  local acc::List{DAE.Exp}
                  local change::Bool
                @match (iexpl, iacc, ichange) begin
                  ( nil(),  nil(), _)  => begin
                    DAE.SCONST("")
                  end

                  ( nil(), exp <|  nil(), _)  => begin
                    exp
                  end

                  ( nil(), exp1 <| exp2 <|  nil(), _)  => begin
                    DAE.BINARY(exp2, DAE.ADD(DAE.T_STRING_DEFAULT), exp1)
                  end

                  ( nil(), acc, true)  => begin
                      acc = listReverse(acc)
                      exp = DAE.LIST(acc)
                    Expression.makePureBuiltinCall("stringAppendList", list(exp), DAE.T_STRING_DEFAULT)
                  end

                  (DAE.SCONST(s1) <| rest, DAE.SCONST(s2) <| acc, _)  => begin
                      s = s2 + s1
                    simplifyStringAppendList(rest, _cons(DAE.SCONST(s), acc), true)
                  end

                  (exp <| rest, acc, change)  => begin
                    simplifyStringAppendList(rest, _cons(exp, acc), change)
                  end
                end
              end
          exp
        end

         #= simplifies some builtin calls if constant arguments =#
        function simplifyBuiltinConstantCalls(name::String, exp::DAE.Exp #= assumes already simplified call arguments =#) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local r::ModelicaReal
                  local v1::ModelicaReal
                  local v2::ModelicaReal
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                   #=  der(constant) ==> 0
                   =#
                @matchcontinue (name, exp) begin
                  ("der", DAE.CALL(expLst = e <|  nil()))  => begin
                      e1 = simplifyBuiltinConstantDer(e)
                    e1
                  end

                  ("pre", DAE.CALL(expLst = e <|  nil()))  => begin
                    e
                  end

                  ("previous", DAE.CALL(expLst = e <|  nil()))  => begin
                    e
                  end

                  ("edge", DAE.CALL(expLst = _ <|  nil()))  => begin
                    DAE.BCONST(false)
                  end

                  ("change", DAE.CALL(expLst = _ <|  nil()))  => begin
                    DAE.BCONST(false)
                  end

                  ("sqrt", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = sqrt(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("abs", DAE.CALL(expLst = DAE.RCONST(r) <|  nil()))  => begin
                      r = abs(r)
                    DAE.RCONST(r)
                  end

                  ("abs", DAE.CALL(expLst = DAE.ICONST(i) <|  nil()))  => begin
                      i = abs(i)
                    DAE.ICONST(i)
                  end

                  ("sin", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = sin(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("cos", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = cos(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("asin", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = Expression.toReal(e)
                      @match true = r >= (-1.0) && r <= 1.0
                      r = asin(r)
                    DAE.RCONST(r)
                  end

                  ("acos", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = Expression.toReal(e)
                      @match true = r >= (-1.0) && r <= 1.0
                      r = acos(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("tan", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = tan(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("exp", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = exp(Expression.toReal(e))
                    DAE.RCONST(r)
                  end

                  ("log", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = Expression.toReal(e)
                      @match true = r > 0
                      r = log(r)
                    DAE.RCONST(r)
                  end

                  ("log10", DAE.CALL(expLst = e <|  nil()))  => begin
                      r = Expression.toReal(e)
                      @match true = r > 0
                      r = log10(r)
                    DAE.RCONST(r)
                  end

                  ("min", DAE.CALL(expLst = DAE.ICONST(i) <| DAE.ICONST(j) <|  nil()))  => begin
                      i = min(i, j)
                    DAE.ICONST(i)
                  end

                  ("min", DAE.CALL(expLst = e <| e1 <|  nil(), attr = DAE.CALL_ATTR(ty = DAE.T_REAL(__))))  => begin
                      v1 = Expression.toReal(e)
                      v2 = Expression.toReal(e1)
                      r = min(v1, v2)
                    DAE.RCONST(r)
                  end

                  ("min", DAE.CALL(expLst = e && DAE.ENUM_LITERAL(index = i) <| e1 && DAE.ENUM_LITERAL(index = j) <|  nil()))  => begin
                      e2 = if i < j
                            e
                          else
                            e1
                          end
                    e2
                  end

                  ("max", DAE.CALL(expLst = DAE.ICONST(i) <| DAE.ICONST(j) <|  nil()))  => begin
                      i = max(i, j)
                    DAE.ICONST(i)
                  end

                  ("max", DAE.CALL(expLst = e <| e1 <|  nil(), attr = DAE.CALL_ATTR(ty = DAE.T_REAL(__))))  => begin
                      v1 = Expression.toReal(e)
                      v2 = Expression.toReal(e1)
                      r = max(v1, v2)
                    DAE.RCONST(r)
                  end

                  ("max", DAE.CALL(expLst = e && DAE.ENUM_LITERAL(index = i) <| e1 && DAE.ENUM_LITERAL(index = j) <|  nil()))  => begin
                      e2 = if i > j
                            e
                          else
                            e1
                          end
                    e2
                  end

                  ("sign", DAE.CALL(expLst = DAE.RCONST(r) <|  nil()))  => begin
                      i = if realEq(r, 0.0)
                            0
                          else
                            if realGt(r, 0.0)
                                  1
                                else
                                  -1
                                end
                          end
                    DAE.ICONST(i)
                  end
                end
              end
               #=  pre(constant) ==> constant
               =#
               #=  previous(constant) ==> constant
               =#
               #=  edge(constant) ==> false
               =#
               #=  change(constant) ==> false
               =#
               #=  sqrt function
               =#
               #=  abs on real
               =#
               #=  abs on integer
               =#
               #=  sin function
               =#
               #=  cos function
               =#
               #=  sin function
               =#
               #=  cos function
               =#
               #=  tangent function
               =#
               #=  DAE.Exp function
               =#
               #=  log function
               =#
               #=  log10 function
               =#
               #=  min function on integers
               =#
               #=  min function on reals
               =#
               #=  min function on enumerations
               =#
               #=  max function on integers
               =#
               #=  max function on reals
               =#
               #=  max function on enumerations
               =#
          outExp
        end

         #=  Function for simplifying
          x[{y,z,q}] to {x[y], x[z], x[q]} =#
        function simplifyCref(origExp::DAE.Exp, inCREF::ComponentRef, inType::Type) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local t::Type
                  local t2::Type
                  local t3::Type
                  local ssl::List{Subscript}
                  local cr::ComponentRef
                  local idn::Ident
                  local idn2::Ident
                  local expl_1::List{DAE.Exp}
                  local expCref::DAE.Exp
                  local index::ModelicaInteger
                @matchcontinue inCREF begin
                  DAE.CREF_IDENT(idn, t2, ssl && DAE.SLICE(DAE.ARRAY(_, _, _)) <| _)  => begin
                      cr = CrefForHashTable.makeCrefIdent(idn, t2, nil)
                      expCref = Expression.makeCrefExp(cr, inType)
                      exp = simplifyCref2(expCref, ssl)
                    exp
                  end

                  DAE.CREF_IDENT(subscriptLst = DAE.SLICE(exp = DAE.RANGE(__)) <| _)  => begin
                      cr = CrefForHashTable.crefStripSubs(inCREF)
                      expCref = Expression.makeCrefExp(cr, inType)
                    simplifyCref2(expCref, inCREF.subscriptLst)
                  end

                  DAE.CREF_QUAL(idn, DAE.T_METATYPE(ty = t2), ssl, cr)  => begin
                      exp = simplifyCrefMM1(idn, t2, ssl)
                      exp = simplifyCrefMM(exp, Expression.typeOf(exp), cr)
                    exp
                  end

                  _  => begin
                      origExp
                  end
                end
              end
          exp
        end

         #= Helper function for simplifyCref
         Does the recursion. =#
        function simplifyCref2(inExp::DAE.Exp, inSsl::List{<:Subscript}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local idn::Ident
                  local t::Type
                  local tp::Type
                  local exp_1::DAE.Exp
                  local crefExp::DAE.Exp
                  local exp::DAE.Exp
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local ss::Subscript
                  local ssl::List{Subscript}
                  local ssl_2::List{Subscript}
                  local subs::List{Subscript}
                  local crefs::List{ComponentRef}
                  local cr::ComponentRef
                  local dim::ModelicaInteger
                  local sc::Bool
                @matchcontinue (inExp, inSsl) begin
                  (exp_1,  nil())  => begin
                    exp_1
                  end

                  (DAE.CREF(cr && DAE.CREF_IDENT(_, _, _), t), DAE.SLICE(DAE.ARRAY(_, _, expl_1)) <| ssl)  => begin
                      subs = ListUtil.map(expl_1, Expression.makeIndexSubscript)
                      crefs = ListUtil.map1r(ListUtil.map(subs, ListUtil.create), CrefForHashTable.subscriptCref, cr)
                      t = Types.unliftArray(t)
                      expl = ListUtil.map1(crefs, Expression.makeCrefExp, t)
                      dim = listLength(expl)
                      exp = simplifyCref2(DAE.ARRAY(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(dim))), true, expl), ssl)
                    exp
                  end

                  (DAE.CREF(cr && DAE.CREF_IDENT(__), t), ss && DAE.SLICE(exp = DAE.RANGE(__)) <| ssl)  => begin
                      subs = Expression.expandSliceExp(ss.exp)
                      crefs = list(CrefForHashTable.subscriptCref(cr, ListUtil.create(s)) for s in subs)
                      t = Types.unliftArray(t)
                      expl = list(Expression.makeCrefExp(cr, t) for cr in crefs)
                      dim = listLength(expl)
                      exp = DAE.ARRAY(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(dim))), true, expl)
                    simplifyCref2(exp, ssl)
                  end

                  (DAE.ARRAY(tp, sc, expl), ssl)  => begin
                      expl = ListUtil.map1(expl, simplifyCref2, ssl)
                    DAE.ARRAY(tp, sc, expl)
                  end
                end
              end
          outExp
        end

        function simplifyCrefMM_index(inExp::DAE.Exp, ident::String, ty::DAE.Type) ::DAE.Exp
              local exp::DAE.Exp

              local index::ModelicaInteger
              local nty::DAE.Type
              local ty2::DAE.Type
              local fields::List{DAE.Var}

              fields = Types.getMetaRecordFields(ty)
              index = Types.findVarIndex(ident, fields) + 1
              @match DAE.TYPES_VAR(ty = nty) = listGet(fields, index)
              exp = DAE.RSUB(inExp, index, ident, nty)
          exp
        end

        function simplifyCrefMM(inExp::DAE.Exp, inType::DAE.Type, inCref::ComponentRef) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                @match inCref begin
                  DAE.CREF_IDENT(__)  => begin
                      exp = simplifyCrefMM_index(inExp, inCref.ident, inType)
                      exp = if listEmpty(inCref.subscriptLst)
                            exp
                          else
                            DAE.ASUB(exp, list(Expression.subscriptIndexExp(s) for s in inCref.subscriptLst))
                          end
                    exp
                  end

                  DAE.CREF_QUAL(__)  => begin
                      exp = simplifyCrefMM_index(inExp, inCref.ident, inType)
                      exp = if listEmpty(inCref.subscriptLst)
                            exp
                          else
                            DAE.ASUB(exp, list(Expression.subscriptIndexExp(s) for s in inCref.subscriptLst))
                          end
                      exp = simplifyCrefMM(exp, Expression.typeOf(exp), inCref.componentRef)
                    exp
                  end
                end
              end
          exp
        end

        function simplifyCrefMM1(ident::String, ty::DAE.Type, ssl::List{<:Subscript}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                @match ssl begin
                   nil()  => begin
                    DAE.CREF(DAE.CREF_IDENT(ident, ty, nil), ty)
                  end

                  _  => begin
                      DAE.ASUB(DAE.CREF(DAE.CREF_IDENT(ident, ty, nil), ty), list(Expression.subscriptIndexExp(s) for s in ssl))
                  end
                end
              end
          outExp
        end

         #= Advanced simplifications covering several
         terms or factors, like a +2a +3a = 5a  =#
        function simplify2(inExp::DAE.Exp, simplifyAddOrSub::Bool = true, simplifyMulOrDiv::Bool = true) ::DAE.Exp
              local outExp::DAE.Exp

              local ty::DAE.Type

              ty = Expression.typeOf(inExp)
              if ! Expression.isIntegerOrReal(ty)
                outExp = inExp
                return outExp
              end
              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local exp_2::DAE.Exp
                  local exp_3::DAE.Exp
                  local resConst::DAE.Exp
                  local lstConstExp::List{DAE.Exp}
                  local lstExp::List{DAE.Exp}
                  local op::Operator
                  local hasConst::Bool
                   #=  global simplify ADD and SUB
                   =#
                @match inExp begin
                  DAE.BINARY(operator = op) where (simplifyAddOrSub && Expression.isAddOrSub(op))  => begin
                      lstExp = Expression.terms(inExp)
                      (lstConstExp, lstExp) = ListUtil.splitOnTrue(lstExp, Expression.isConstValue)
                      hasConst = ! listEmpty(lstConstExp)
                      resConst = if hasConst
                            simplifyBinaryAddConstants(lstConstExp)
                          else
                            Expression.makeConstZero(ty)
                          end
                      exp_2 = if hasConst
                            Expression.makeSum1(lstExp)
                          else
                            inExp
                          end
                      exp_3 = simplifyBinaryCoeff(exp_2)
                      exp_3 = if hasConst
                            Expression.expAdd(resConst, simplify2(exp_3, false, true))
                          else
                            simplify2(exp_3, false, true)
                          end
                    exp_3
                  end

                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2) where (Expression.isAddOrSub(op))  => begin
                      e1 = simplify2(e1, false, true)
                      e2 = simplify2(e2, false, true)
                    DAE.BINARY(e1, op, e2)
                  end

                  DAE.BINARY(operator = op) where (simplifyMulOrDiv && Expression.isMulOrDiv(op))  => begin
                      lstExp = Expression.factors(inExp)
                      (lstConstExp, lstExp) = ListUtil.splitOnTrue(lstExp, Expression.isConst)
                      if ! listEmpty(lstConstExp)
                        resConst = simplifyBinaryMulConstants(lstConstExp)
                        exp_2 = Expression.makeProductLst(simplifyMul(lstExp))
                        if Expression.isConstOne(resConst)
                          exp_3 = simplify2(exp_2, true, false)
                        elseif Expression.isConstMinusOne(resConst)
                          exp_3 = Expression.negate(simplify2(exp_2, true, false))
                        else
                          exp_3 = Expression.expMul(resConst, simplify2(exp_2, true, false))
                        end
                      else
                        exp_2 = simplifyBinaryCoeff(inExp)
                        exp_3 = simplify2(exp_2, true, false)
                      end
                    exp_3
                  end

                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2) where (Expression.isMulOrDiv(op))  => begin
                      e1 = simplify2(e1, true, false)
                      e2 = simplify2(e2, true, false)
                    DAE.BINARY(e1, op, e2)
                  end

                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      e1 = simplify2(e1)
                      e2 = simplify2(e2)
                    DAE.BINARY(e1, op, e2)
                  end

                  DAE.UNARY(op, e1)  => begin
                      e1 = simplify2(e1)
                    DAE.UNARY(op, e1)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #= unlocked global simplify ADD and SUB
               =#
               #= locked global simplify MUL and DIV
               =#
               #= /* multiple terms simplifications */ =#
               #= others operators
               =#
               #= /* multiple terms/factor simplifications */ =#
          outExp
        end

        function simplifyBinaryArrayOp(inOperator::Operator) ::Bool
              local found::Bool

              found = begin
                @match inOperator begin
                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    true
                  end

                  DAE.ADD_ARR(__)  => begin
                    true
                  end

                  DAE.SUB_ARR(__)  => begin
                    true
                  end

                  DAE.MUL_ARR(__)  => begin
                    true
                  end

                  DAE.DIV_ARR(__)  => begin
                    true
                  end

                  DAE.POW_ARR(__)  => begin
                    true
                  end

                  DAE.POW_ARR2(__)  => begin
                    true
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    true
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    true
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    true
                  end

                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    true
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    true
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    true
                  end

                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    true
                  end

                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          found
        end

         #= Simplifies binary array expressions,
          e.g. matrix multiplication, etc. =#
        function simplifyBinaryArray(inExp1::DAE.Exp, inOperator2::Operator, inExp3::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res::DAE.Exp
                  local s1::DAE.Exp
                  local a1::DAE.Exp
                  local tp::Type
                  local op::Operator
                @matchcontinue (inExp1, inOperator2, inExp3) begin
                  (e1, DAE.MUL_MATRIX_PRODUCT(__), e2)  => begin
                      e_1 = simplifyMatrixProduct(e1, e2)
                    e_1
                  end

                  (e1, op && DAE.ADD_ARR(__), e2)  => begin
                      a1 = simplifyVectorBinary0(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.SUB_ARR(__), e2)  => begin
                      a1 = simplifyVectorBinary0(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.MUL_ARR(__), e2)  => begin
                      a1 = simplifyVectorBinary(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.DIV_ARR(__), e2)  => begin
                      a1 = simplifyVectorBinary(e1, op, e2)
                    a1
                  end

                  (e1, DAE.POW_ARR(__), e2)  => begin
                      tp = Expression.typeOf(e1)
                      a1 = simplifyMatrixPow(e1, tp, e2)
                    a1
                  end

                  (e1, DAE.POW_ARR2(__), e2)  => begin
                      tp = Expression.typeOf(e1)
                      a1 = simplifyVectorBinary(e1, DAE.POW_ARR2(tp), e2)
                    a1
                  end

                  (e1, DAE.SUB_ARR(ty = tp), DAE.UNARY(_, e2))  => begin
                    DAE.BINARY(e1, DAE.ADD_ARR(tp), e2)
                  end

                  (e1, DAE.ADD_ARR(ty = tp), DAE.UNARY(_, e2))  => begin
                    DAE.BINARY(e1, DAE.SUB_ARR(tp), e2)
                  end

                  (a1, op, s1)  => begin
                      @match true = Expression.isArrayScalarOp(op)
                      op = unliftOperator(a1, op)
                    simplifyVectorScalar(a1, op, s1)
                  end

                  (s1, op, a1)  => begin
                      @match true = Expression.isScalarArrayOp(op)
                      op = unliftOperator(a1, op)
                    simplifyVectorScalar(s1, op, a1)
                  end

                  (e1, DAE.MUL_SCALAR_PRODUCT(__), e2)  => begin
                      res = simplifyScalarProduct(e1, e2)
                    res
                  end

                  (e1, op && DAE.ADD_ARR(__), e2)  => begin
                      a1 = simplifyMatrixBinary(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.SUB_ARR(__), e2)  => begin
                      a1 = simplifyMatrixBinary(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.MUL_ARR(__), e2)  => begin
                      a1 = simplifyMatrixBinary(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.DIV_ARR(__), e2)  => begin
                      a1 = simplifyMatrixBinary(e1, op, e2)
                    a1
                  end

                  (e1, op && DAE.POW_ARR2(__), e2)  => begin
                      a1 = simplifyMatrixBinary(e1, op, e2)
                    a1
                  end

                  (_, DAE.MUL_ARRAY_SCALAR(ty = tp), e2)  => begin
                      @match true = Expression.isZero(e2)
                      (a1, _) = Expression.makeZeroExpression(Expression.arrayDimension(tp))
                    a1
                  end

                  (e1, DAE.DIV_ARR(__), _)  => begin
                      @match true = Expression.isZero(e1)
                      tp = Expression.typeOf(e1)
                      (a1, _) = Expression.makeZeroExpression(Expression.arrayDimension(tp))
                    a1
                  end

                  (e1, DAE.DIV_ARRAY_SCALAR(__), _)  => begin
                      @match true = Expression.isZero(e1)
                      tp = Expression.typeOf(e1)
                      (a1, _) = Expression.makeZeroExpression(Expression.arrayDimension(tp))
                    a1
                  end
                end
              end
               #=  v1 - -v2 => v1 + v2
               =#
               #=  v1 + -v2 => v1 - v2
               =#
               #=  print(\"simplifyMatrixBinary: \" + CrefForHashTable.printExpStr(e1) + \"=>\" + CrefForHashTable.printExpStr(a1) + \"\\n\");
               =#
          outExp
        end

         #= Simplifies the scalar product of two vectors. =#
        function simplifyScalarProduct(inVector1::DAE.Exp, inVector2::DAE.Exp) ::DAE.Exp
              local outProduct::DAE.Exp

              outProduct = begin
                  local expl::List{DAE.Exp}
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local exp::DAE.Exp
                  local tp::Type
                   #=  Both arrays are empty. The result is defined in the spec by sum, so we
                   =#
                   #=  return the default value which is 0.
                   =#
                @match (inVector1, inVector2) begin
                  (DAE.ARRAY(ty = tp, array =  nil()), DAE.ARRAY(array =  nil()))  => begin
                    Expression.makeConstZero(tp)
                  end

                  (DAE.ARRAY(array = expl1), DAE.ARRAY(array = expl2))  => begin
                      @match true = Expression.isVector(inVector1) && Expression.isVector(inVector2)
                      expl = ListUtil.threadMap(expl1, expl2, Expression.expMul)
                      exp = ListUtil.reduce(expl, Expression.expAdd)
                    exp
                  end

                  (_, _)  => begin
                      @match true = Expression.isZero(inVector1) || Expression.isZero(inVector2)
                    Expression.makeConstZero(DAE.T_REAL_DEFAULT)
                  end
                end
              end
               #=  Normal scalar product of two vectors.
               =#
               #=  Scalar product of any expression with zeros
               =#
          outProduct
        end

        function unliftOperator(inArray::DAE.Exp, inOperator::Operator) ::Operator
              local outOperator::Operator

              outOperator = begin
                @match (inArray, inOperator) begin
                  (DAE.MATRIX(__), _)  => begin
                    Expression.unliftOperatorX(inOperator, 2)
                  end

                  _  => begin
                      Expression.unliftOperator(inOperator)
                  end
                end
              end
          outOperator
        end

         #= Simplifies vector scalar operations. =#
        function simplifyVectorScalar(inLhs::DAE.Exp, inOperator::Operator, inRhs::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local s1::DAE.Exp
                  local op::Operator
                  local tp::Type
                  local sc::Bool
                  local es::List{DAE.Exp}
                  local mexpl::List{List{DAE.Exp}}
                  local dims::ModelicaInteger
                   #=  scalar operator array
                   =#
                @match (inLhs, inOperator, inRhs) begin
                  (_, _, DAE.ARRAY(ty = tp, scalar = sc, array = es))  => begin
                      es = ListUtil.map2r(es, Expression.makeBinaryExp, inLhs, inOperator)
                    DAE.ARRAY(tp, sc, es)
                  end

                  (s1, op, DAE.MATRIX(tp, dims, mexpl))  => begin
                      mexpl = simplifyVectorScalarMatrix(mexpl, op, s1, false)
                    DAE.MATRIX(tp, dims, mexpl)
                  end

                  (DAE.ARRAY(ty = tp, scalar = sc, array = es), _, _)  => begin
                      es = ListUtil.map2(es, Expression.makeBinaryExp, inOperator, inRhs)
                    DAE.ARRAY(tp, sc, es)
                  end

                  (DAE.MATRIX(tp, dims, mexpl), op, s1)  => begin
                      mexpl = simplifyVectorScalarMatrix(mexpl, op, s1, true)
                    DAE.MATRIX(tp, dims, mexpl)
                  end
                end
              end
               #= /*scalar-array*/ =#
               #=  array operator scalar
               =#
               #= /*array-scalar*/ =#
          outExp
        end

         #= help function to simplify1, prevents simplify1 to be called multiple times
         in subsequent cases =#
        function simplifyVectorBinary0(e1::DAE.Exp, op::Operator, e2::DAE.Exp) ::DAE.Exp
              local res::DAE.Exp

              res = begin
                  local a1::DAE.Exp
                @matchcontinue (e1, op, e2) begin
                  (_, _, _)  => begin
                      a1 = simplifyVectorBinary(e1, op, e2)
                    a1
                  end

                  (_, DAE.ADD(__), _)  => begin
                      @match true = Expression.isZero(e1)
                    e2
                  end

                  (_, DAE.ADD_ARR(__), _)  => begin
                      @match true = Expression.isZero(e1)
                    e2
                  end

                  (_, DAE.SUB_ARR(__), _)  => begin
                      @match true = Expression.isZero(e1)
                    Expression.negate(e2)
                  end

                  (_, DAE.SUB(__), _)  => begin
                      @match true = Expression.isZero(e1)
                    Expression.negate(e2)
                  end

                  _  => begin
                        @match true = Expression.isZero(e2)
                      e1
                  end
                end
              end
          res
        end

        function simplifyVectorBinary(inLhs::DAE.Exp, inOperator::Operator, inRhs::DAE.Exp) ::DAE.Exp
              local outResult::DAE.Exp

              local ty::DAE.Type
              local sc::Bool
              local lhs::List{DAE.Exp}
              local rhs::List{DAE.Exp}
              local res::List{DAE.Exp}
              local op::Operator

              @match DAE.ARRAY(ty = ty, scalar = sc, array = lhs) = inLhs
              @match DAE.ARRAY(array = rhs) = inRhs
              op = removeOperatorDimension(inOperator)
              res = ListUtil.threadMap1(lhs, rhs, simplifyVectorBinary2, op)
              outResult = DAE.ARRAY(ty, sc, res)
          outResult
        end

        function simplifyVectorBinary2(inLhs::DAE.Exp, inRhs::DAE.Exp, inOperator::Operator) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = DAE.BINARY(inLhs, inOperator, inRhs)
          outExp
        end

         #= Simplifies matrix addition and subtraction =#
        function simplifyMatrixBinary(inLhs::DAE.Exp, inOperator::Operator, inRhs::DAE.Exp) ::DAE.Exp
              local outResult::DAE.Exp

              local lhs::List{List{DAE.Exp}}
              local rhs::List{List{DAE.Exp}}
              local res::List{List{DAE.Exp}}
              local op::Operator
              local sz::ModelicaInteger
              local ty::DAE.Type

              lhs = Expression.get2dArrayOrMatrixContent(inLhs)
              rhs = Expression.get2dArrayOrMatrixContent(inRhs)
              op = removeOperatorDimension(inOperator)
              res = ListUtil.threadMap1(lhs, rhs, simplifyMatrixBinary1, op)
              sz = listLength(res)
              ty = Expression.typeOf(inLhs)
              outResult = DAE.MATRIX(ty, sz, res)
          outResult
        end

         #= Simplifies matrix addition and subtraction. =#
        function simplifyMatrixBinary1(inLhs::List{<:DAE.Exp}, inRhs::List{<:DAE.Exp}, inOperator::Operator) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp}

              outExpl = ListUtil.threadMap1(inLhs, inRhs, simplifyMatrixBinary2, inOperator)
          outExpl
        end

        function simplifyMatrixBinary2(inLhs::DAE.Exp, inRhs::DAE.Exp, inOperator::Operator) ::DAE.Exp
              local outExp::DAE.Exp

              local op::Operator

              op = removeOperatorDimension(inOperator)
              outExp = DAE.BINARY(inLhs, op, inRhs)
          outExp
        end

         #= author: Frenkel TUD
          Simplifies matrix powers. =#
        function simplifyMatrixPow(inExp1::DAE.Exp, inType::Type, inExp2::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local expl_1::List{List{DAE.Exp}}
                  local expl1::List{List{DAE.Exp}}
                  local expl2::List{List{DAE.Exp}}
                  local el::List{DAE.Exp}
                  local tp1::Type
                  local tp::Type
                  local size1::ModelicaInteger
                  local i::ModelicaInteger
                  local i_1::ModelicaInteger
                  local range::List{ModelicaInteger}
                  local e::DAE.Exp
                  local m::DAE.Exp
                  local res::DAE.Exp
                   #= /* A^0=I */ =#
                @matchcontinue (inExp1, inType, inExp2) begin
                  (DAE.MATRIX(ty = tp1, integer = size1), _, DAE.ICONST(integer = i))  => begin
                      @match 0 = i
                      el = ListUtil.fill(DAE.RCONST(0.0), size1)
                      expl2 = ListUtil.fill(el, size1)
                      range = ListUtil.intRange2(0, size1 - 1)
                      expl_1 = simplifyMatrixPow1(range, expl2, DAE.RCONST(1.0))
                    DAE.MATRIX(tp1, size1, expl_1)
                  end

                  (m && DAE.MATRIX(__), _, DAE.ICONST(integer = i))  => begin
                      @match 1 = i
                    m
                  end

                  (m && DAE.MATRIX(__), _, DAE.ICONST(integer = i))  => begin
                      @match 2 = i
                      res = simplifyMatrixProduct(m, m)
                    res
                  end

                  (m && DAE.MATRIX(ty = tp1), _, DAE.ICONST(integer = i))  => begin
                      @match true = i > 3
                      @match 0 = intMod(i, 2)
                      i_1 = intDiv(i, 2)
                      e = simplifyMatrixPow(m, tp1, DAE.ICONST(i_1))
                      res = simplifyMatrixProduct(e, e)
                    res
                  end

                  (m && DAE.MATRIX(ty = tp1), _, DAE.ICONST(integer = i))  => begin
                      @match true = 1 < i
                      i_1 = i - 1
                      e = simplifyMatrixPow(m, tp1, DAE.ICONST(i_1))
                      res = simplifyMatrixProduct(m, e)
                    res
                  end
                end
              end
               #= /* A^1=A */ =#
               #=  A^2 = A * A
               =#
               #=  A^n = A^m*A^m where n = 2*m
               =#
               #= /* A^i */ =#
          outExp
        end

         #= author: Frenkel TUD
          Simplifies matrix powers. =#
        function simplifyMatrixPow1(inRange::List{<:ModelicaInteger}, inMatrix::List{<:List{<:DAE.Exp}}, inValue::DAE.Exp) ::List{List{DAE.Exp}}
              local outMatrix::List{List{DAE.Exp}}

              outMatrix = begin
                  local rm::List{List{DAE.Exp}}
                  local rm1::List{List{DAE.Exp}}
                  local row::List{DAE.Exp}
                  local row1::List{DAE.Exp}
                  local e::DAE.Exp
                  local i::ModelicaInteger
                  local rr::List{ModelicaInteger}
                @matchcontinue (inRange, inMatrix, inValue) begin
                  ( nil(),  nil(), _)  => begin
                    nil
                  end

                  (i <|  nil(), row <|  nil(), e)  => begin
                      row1 = ListUtil.replaceAt(e, i + 1, row)
                    list(row1)
                  end

                  (i <| rr, row <| rm, e)  => begin
                      row1 = ListUtil.replaceAt(e, i + 1, row)
                      rm1 = simplifyMatrixPow1(rr, rm, e)
                    _cons(row1, rm1)
                  end
                end
              end
          outMatrix
        end

         #= Simplifies matrix multiplication. =#
        function simplifyMatrixProduct(inMatrix1::DAE.Exp, inMatrix2::DAE.Exp) ::DAE.Exp
              local outProduct::DAE.Exp

              local mat1::DAE.Exp
              local mat2::DAE.Exp

               #=  Convert any DAE.MATRIX expressions to DAE.ARRAY.
               =#
              mat1 = Expression.matrixToArray(inMatrix1)
              mat2 = Expression.matrixToArray(inMatrix2)
               #=  Transpose the second matrix. This makes it easier to do the multiplication,
               =#
               #=  since we can do row-row multiplications instead of row-column.
               =#
              (mat2, _) = Expression.transposeArray(mat2)
              outProduct = simplifyMatrixProduct2(mat1, mat2)
          outProduct
        end

         #= Helper function to simplifyMatrixProduct, does the actual work. Assumes that
           the second matrix has been transposed to make the multiplication easier. =#
        function simplifyMatrixProduct2(inMatrix1::DAE.Exp, inMatrix2::DAE.Exp) ::DAE.Exp
              local outProduct::DAE.Exp

              outProduct = begin
                  local n::DAE.Dimension
                  local m::DAE.Dimension
                  local p::DAE.Dimension
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local ty::DAE.Type
                  local row_ty::DAE.Type
                  local matrix::List{List{DAE.Exp}}
                  local zero::DAE.Exp
                  local dims::List{DAE.Dimension}
                   #=  The common dimension of the matrices is zero, the result will be an array
                   =#
                   #=  of zeroes (the default value of sum).
                   =#
                @matchcontinue (inMatrix1, inMatrix2) begin
                  (DAE.ARRAY(ty = ty && DAE.T_ARRAY(dims = dims)), DAE.ARRAY(__))  => begin
                      @match true = Expression.arrayContainZeroDimension(dims)
                      zero = Expression.makeConstZero(ty)
                      dims = simplifyMatrixProduct4(inMatrix1, inMatrix2)
                    Expression.arrayFill(dims, zero)
                  end

                  (DAE.ARRAY(ty = DAE.T_ARRAY(ty, n <| _ <|  nil()), array = expl1), DAE.ARRAY(ty = DAE.T_ARRAY(dims = _ <|  nil())))  => begin
                      expl1 = ListUtil.map1(expl1, simplifyScalarProduct, inMatrix2)
                      ty = DAE.T_ARRAY(ty, list(n))
                    DAE.ARRAY(ty, true, expl1)
                  end

                  (DAE.ARRAY(ty = DAE.T_ARRAY(dims = _ <|  nil())), DAE.ARRAY(ty = DAE.T_ARRAY(ty, m <| _ <|  nil()), array = expl2))  => begin
                      expl1 = ListUtil.map1r(expl2, simplifyScalarProduct, inMatrix1)
                      ty = DAE.T_ARRAY(ty, list(m))
                    DAE.ARRAY(ty, true, expl1)
                  end

                  (DAE.ARRAY(ty = DAE.T_ARRAY(ty, n <| _ <|  nil()), array = expl1), DAE.ARRAY(ty = DAE.T_ARRAY(dims = p <| _ <|  nil()), array = expl2))  => begin
                      matrix = ListUtil.map1(expl1, simplifyMatrixProduct3, expl2)
                      row_ty = DAE.T_ARRAY(ty, list(p))
                      expl1 = ListUtil.map2(matrix, Expression.makeArray, row_ty, true)
                    DAE.ARRAY(DAE.T_ARRAY(ty, list(n, p)), false, expl1)
                  end
                end
              end
               #=  It's sufficient to check the first array, because the only case where
               =#
               #=  the second array alone determines the result dimensions is the
               =#
               #=  vector-matrix case. The instantiation should just remove the
               =#
               #=  equations in that case, since the result will be an empty array.
               =#
               #=  Matrix-vector multiplication, c[n] = a[n, m] * b[m].
               =#
               #=  c[i] = a[i, :] * b for i in 1:n
               =#
               #=  Vector-matrix multiplication, c[m] = a[n] * b[n, m].
               =#
               #=  c[i] = a * b[:, i] for i in 1:m
               =#
               #=  Matrix-matrix multiplication, c[n, p] = a[n, m] * b[m, p].
               =#
               #=  c[i, j] = a[i, :] * b[:, j] for i in 1:n, j in 1:p
               =#
          outProduct
        end

         #= Helper function to simplifyMatrixProduct2. Multiplies the given matrix row
           with each row in the given matrix and returns a list with the results. =#
        function simplifyMatrixProduct3(inRow::DAE.Exp, inMatrix::List{<:DAE.Exp}) ::List{DAE.Exp}
              local outRow::List{DAE.Exp}

              outRow = ListUtil.map1r(inMatrix, simplifyScalarProduct, inRow)
          outRow
        end

         #= Helper function to simplifyMatrixProduct2. Returns the dimensions of the
           matrix multiplication product for two matrices. =#
        function simplifyMatrixProduct4(inMatrix1::DAE.Exp, inMatrix2::DAE.Exp) ::List{DAE.Dimension}
              local outDimensions::List{DAE.Dimension}

              outDimensions = begin
                  local n::DAE.Dimension
                  local m::DAE.Dimension
                  local p::DAE.Dimension
                   #=  c[n] = a[n, m] * b[m]
                   =#
                @match (inMatrix1, inMatrix2) begin
                  (DAE.ARRAY(ty = DAE.T_ARRAY(dims = n <| _ <|  nil())), DAE.ARRAY(ty = DAE.T_ARRAY(dims = _ <|  nil())))  => begin
                    list(n)
                  end

                  (DAE.ARRAY(ty = DAE.T_ARRAY(dims = _ <|  nil())), DAE.ARRAY(ty = DAE.T_ARRAY(dims = m <| _ <|  nil())))  => begin
                    list(m)
                  end

                  (DAE.ARRAY(ty = DAE.T_ARRAY(dims = n <| _ <|  nil())), DAE.ARRAY(ty = DAE.T_ARRAY(dims = p <| _ <|  nil())))  => begin
                    list(n, p)
                  end
                end
              end
               #=  c[m] = a[n] * b[n, m]
               =#
               #=  c[n, p] = a[n, m] * b[m, p]
               =#
          outDimensions
        end

         #= author: PA
          Sorts all constants of a sum or product to the
          beginning of the expression.
          Also combines expressions like 2a+4a and aaa+3a^3. =#
        function simplifyBinarySortConstants(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e_lst::List{DAE.Exp}
                  local const_es1::List{DAE.Exp}
                  local notconst_es1::List{DAE.Exp}
                  local const_es1_1::List{DAE.Exp}
                  local res::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res1::DAE.Exp
                  local res2::DAE.Exp
                  local tp::Type
                   #=  e1 * e2
                   =#
                @matchcontinue inExp begin
                  e && DAE.BINARY(operator = DAE.MUL(__))  => begin
                      res = simplifyBinarySortConstantsMul(e)
                    res
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = tp), exp2 = e2)  => begin
                      e1 = simplifyBinarySortConstantsMul(e1)
                      e2 = simplifyBinarySortConstantsMul(e2)
                    DAE.BINARY(e1, DAE.DIV(tp), e2)
                  end

                  e && DAE.BINARY(operator = DAE.ADD(__))  => begin
                      e_lst = Expression.terms(e)
                      (const_es1, notconst_es1) = ListUtil.splitOnTrue(e_lst, Expression.isConstValue)
                      if ! listEmpty(const_es1)
                        res1 = simplifyBinaryAddConstants(const_es1)
                        res2 = Expression.makeSum1(notconst_es1)
                        res = Expression.expAdd(res1, res2)
                      else
                        res = inExp
                      end
                    res
                  end

                  _  => begin
                      inExp
                  end
                end
              end
               #=  return e
               =#
          outExp
        end

         #= author: PA
          Combines expressions like 2a+4a and aaa+3a^3, etc =#
        function simplifyBinaryCoeff(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e_lst::List{DAE.Exp}
                  local e_lst_1::List{DAE.Exp}
                  local e1_lst::List{DAE.Exp}
                  local e2_lst::List{DAE.Exp}
                  local e2_lst_1::List{DAE.Exp}
                  local res::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local tp::Type
                @matchcontinue inExp begin
                  e && DAE.BINARY(operator = DAE.MUL(tp)) where (Types.isScalarReal(tp))  => begin
                      e_lst = Expression.factors(e)
                      e_lst_1 = simplifyMul(e_lst)
                      res = Expression.makeProductLst(e_lst_1)
                    res
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(__), exp2 = e2)  => begin
                      @match false = Expression.isZero(e2)
                      e1_lst = Expression.factors(e1)
                      e2_lst = Expression.factors(e2)
                      e2_lst_1 = ListUtil.map(e2_lst, Expression.inverseFactors)
                      e_lst = listAppend(e1_lst, e2_lst_1)
                      e_lst_1 = simplifyMul(e_lst)
                      res = Expression.makeProductLst(e_lst_1)
                    res
                  end

                  e && DAE.BINARY(operator = DAE.ADD(__))  => begin
                      e_lst = Expression.terms(e)
                      e_lst_1 = simplifyAdd(e_lst)
                      res = Expression.makeSum(e_lst_1)
                    res
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.SUB(__), exp2 = e2)  => begin
                      e1_lst = Expression.terms(e1)
                      e2_lst = Expression.terms(e2)
                      e2_lst = ListUtil.map(e2_lst, Expression.negate)
                      e_lst = listAppend(e1_lst, e2_lst)
                      e_lst_1 = simplifyAdd(e_lst)
                      res = Expression.makeSum(e_lst_1)
                    res
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= author: PA
          Adds all expressions in the list, given that they are constant. =#
        function simplifyBinaryAddConstants(inExpLst::List{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              local tp::Type
              local es::List{DAE.Exp}

              @match _cons(outExp, es) = inExpLst
              tp = Expression.typeOf(outExp)
              for e in es
                outExp = simplifyBinaryConst(DAE.ADD(tp), outExp, e)
              end
          outExp
        end

         #= author: PA
          Multiplies all expressions in the list, given that they are constant. =#
        function simplifyBinaryMulConstants(inExpLst::List{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              local es::List{DAE.Exp}
              local tp::Type

              @match _cons(outExp, es) = inExpLst
              tp = Expression.typeOf(outExp)
              for e in es
                outExp = simplifyBinaryConst(DAE.MUL(tp), outExp, e)
              end
          outExp
        end

         #= author: PA
          Simplifies expressions like a*a*a*b*a*b*a =#
        function simplifyMul(expl::List{<:DAE.Exp}) ::List{DAE.Exp}
              local expl_1::List{DAE.Exp}

              local exp_const::List{Tuple{DAE.Exp, ModelicaReal}}
              local exp_const_1::List{Tuple{DAE.Exp, ModelicaReal}}

              exp_const = ListUtil.map(expl, simplifyBinaryMulCoeff2)
              exp_const_1 = simplifyMulJoinFactors(exp_const)
              expl_1 = simplifyMulMakePow(exp_const_1)
          expl_1
        end

         #=  author: PA
          Helper function to simplifyMul.
          Joins expressions that have the same base.
          E.g. {(a,2), (a,4), (b,2)} => {(a,6), (b,2)} =#
        function simplifyMulJoinFactors(inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::List{Tuple{DAE.Exp, ModelicaReal}}
              local outTplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = nil

              local tplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = inTplExpRealLst
              local e::DAE.Exp
              local coeff::ModelicaReal
              local coeff2::ModelicaReal

              while ! listEmpty(tplExpRealLst)
                @match _cons((e, coeff), tplExpRealLst) = tplExpRealLst
                (coeff2, tplExpRealLst) = simplifyMulJoinFactorsFind(e, tplExpRealLst)
                coeff = coeff + coeff2
                outTplExpRealLst = _cons((e, coeff), outTplExpRealLst)
              end
               #=  outTplExpRealLst := listReverse(outTplExpRealLst);
               =#
          outTplExpRealLst
        end

         #= author: PA
          Helper function to simplifyMulJoinFactors.
          Searches rest of list to find all occurences of a base. =#
        function simplifyMulJoinFactorsFind(inExp::DAE.Exp, inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::Tuple{ModelicaReal, List{Tuple{DAE.Exp, ModelicaReal}}}
              local outTplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = nil
              local outReal::ModelicaReal = 0.0

              local tplExpReal::Tuple{DAE.Exp, ModelicaReal}

              for tplExpReal in inTplExpRealLst
                (outReal, outTplExpRealLst) = begin
                    local coeff::ModelicaReal
                    local e2::DAE.Exp
                    local e1::DAE.Exp
                    local op::DAE.Operator
                  @match tplExpReal begin
                    (e2, coeff) where (Expression.expEqual(inExp, e2))  => begin
                      (coeff + outReal, outTplExpRealLst)
                    end

                    (DAE.BINARY(exp1 = e1, operator = op && DAE.DIV(__), exp2 = e2), coeff) where (if Expression.isOne(e1)
                          Expression.expEqual(inExp, e2)
                        else
                          Expression.expEqual(inExp, DAE.BINARY(e2, op, e1))
                        end)  => begin
                      (outReal - coeff, outTplExpRealLst)
                    end

                    _  => begin
                        (outReal, _cons(tplExpReal, outTplExpRealLst))
                    end
                  end
                end
              end
               #= /* e1 == e2 */ =#
               #=  pow(a/b,n) * pow(b/a,m) = pow(a/b,n-m)
               =#
               #= /* not Expression.expEqual */ =#
              outTplExpRealLst = listReverse(outTplExpRealLst)
          (outReal, outTplExpRealLst)
        end

         #= author: PA
          Helper function to simplifyMul.
          Makes each item in the list into a pow
          expression, except when exponent is 1.0. =#
        function simplifyMulMakePow(inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::List{DAE.Exp}
              local outExpLst::List{DAE.Exp} = nil

              local tplExpReal::Tuple{DAE.Exp, ModelicaReal}
              local e::DAE.Exp
              local r::ModelicaReal

              for tplExpReal in inTplExpRealLst
                (e, r) = tplExpReal
                outExpLst = if r == 1.0
                      _cons(e, outExpLst)
                    else
                      _cons(DAE.BINARY(e, DAE.POW(DAE.T_REAL_DEFAULT), DAE.RCONST(r)), outExpLst)
                    end
              end
          outExpLst
        end

         #= author: PA
          Simplifies terms like 2a+4b+2a+a+b =#
        function simplifyAdd(inExpLst::List{<:DAE.Exp}) ::List{DAE.Exp}
              local outExpLst::List{DAE.Exp}

              outExpLst = begin
                  local exp_const::List{Tuple{DAE.Exp, ModelicaReal}}
                  local exp_const_1::List{Tuple{DAE.Exp, ModelicaReal}}
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                @matchcontinue inExpLst begin
                  _  => begin
                      exp_const = ListUtil.map(inExpLst, simplifyBinaryAddCoeff2)
                      exp_const_1 = simplifyAddJoinTerms(exp_const)
                      expl_1 = simplifyAddMakeMul(exp_const_1)
                    expl_1
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- ExpressionSimplify.simplifyAdd failed\\n")
                      fail()
                  end
                end
              end
          outExpLst
        end

         #= author: PA
          Helper function to simplifyAdd.
          Join all terms with the same expression.
          i.e. 2a+4a gives an element (a,6) in the list. =#
        function simplifyAddJoinTerms(inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::List{Tuple{DAE.Exp, ModelicaReal}}
              local outTplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = nil

              local tplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = inTplExpRealLst
              local t::Tuple{DAE.Exp, ModelicaReal}
              local e::DAE.Exp
              local coeff::ModelicaReal
              local coeff2::ModelicaReal

              while ! listEmpty(tplExpRealLst)
                @match _cons(t, tplExpRealLst) = tplExpRealLst
                (e, coeff) = t
                (coeff2, tplExpRealLst) = simplifyAddJoinTermsFind(e, tplExpRealLst)
                coeff = coeff + coeff2
                outTplExpRealLst = _cons(if coeff2 == 0
                      t
                    else
                      (e, coeff)
                    end, outTplExpRealLst)
              end
               #= outTplExpRealLst := listReverse(outTplExpRealLst);
               =#
          outTplExpRealLst
        end

         #= author: PA
          Helper function to simplifyAddJoinTerms, finds all occurences of Expression. =#
        function simplifyAddJoinTermsFind(inExp::DAE.Exp, inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::Tuple{ModelicaReal, List{Tuple{DAE.Exp, ModelicaReal}}}
              local outTplExpRealLst::List{Tuple{DAE.Exp, ModelicaReal}} = nil
              local outReal::ModelicaReal = 0.0

              local e::DAE.Exp
              local coeff::ModelicaReal

              for t in inTplExpRealLst
                (e, coeff) = t
                if Expression.expEqual(inExp, e)
                  outReal = outReal + coeff
                else
                  outTplExpRealLst = _cons(t, outTplExpRealLst)
                end
              end
              outTplExpRealLst = Dangerous.listReverseInPlace(outTplExpRealLst)
          (outReal, outTplExpRealLst)
        end

         #= author: PA
          Makes multiplications of each element
          in the list, except for coefficient 1.0 =#
        function simplifyAddMakeMul(inTplExpRealLst::List{<:Tuple{<:DAE.Exp, ModelicaReal}}) ::List{DAE.Exp}
              local outExpLst::List{DAE.Exp} = nil

              local tplExpReal::Tuple{DAE.Exp, ModelicaReal}

              for tplExpReal in inTplExpRealLst
                outExpLst = begin
                    local e::DAE.Exp
                    local r::ModelicaReal
                    local tmpInt::ModelicaInteger
                  @matchcontinue tplExpReal begin
                    (e, r) where (r == 1.0)  => begin
                      _cons(e, outExpLst)
                    end

                    (e, r)  => begin
                        @match DAE.T_INTEGER() = Expression.typeOf(e)
                        tmpInt = realInt(r)
                      _cons(DAE.BINARY(DAE.ICONST(tmpInt), DAE.MUL(DAE.T_INTEGER_DEFAULT), e), outExpLst)
                    end

                    (e, r)  => begin
                      _cons(DAE.BINARY(DAE.RCONST(r), DAE.MUL(DAE.T_REAL_DEFAULT), e), outExpLst)
                    end
                  end
                end
              end
          outExpLst
        end

         #= This function checks for x+x+x+x and returns (x,4.0) =#
        function simplifyBinaryAddCoeff2(inExp::DAE.Exp) ::Tuple{DAE.Exp, ModelicaReal}
              local outRes::Tuple{DAE.Exp, ModelicaReal}

              outRes = begin
                  local exp::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local coeff::ModelicaReal
                  local coeff_1::ModelicaReal
                  local icoeff::ModelicaInteger
                  local tp::Type
                @match inExp begin
                  DAE.CREF(__)  => begin
                    (inExp, 1.0)
                  end

                  DAE.UNARY(operator = DAE.UMINUS(ty = DAE.T_REAL(__)), exp = exp)  => begin
                      (exp, coeff) = simplifyBinaryAddCoeff2(exp)
                      coeff = realMul(-1.0, coeff)
                    (exp, coeff)
                  end

                  DAE.BINARY(exp1 = DAE.RCONST(real = coeff), operator = DAE.MUL(__), exp2 = e1)  => begin
                    (e1, coeff)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = DAE.RCONST(real = coeff))  => begin
                    (e1, coeff)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = DAE.ICONST(integer = icoeff))  => begin
                      coeff_1 = intReal(icoeff)
                    (e1, coeff_1)
                  end

                  DAE.BINARY(exp1 = DAE.ICONST(integer = icoeff), operator = DAE.MUL(__), exp2 = e1)  => begin
                      coeff_1 = intReal(icoeff)
                    (e1, coeff_1)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.ADD(__), exp2 = e2) where (Expression.expEqual(e1, e2))  => begin
                    (e1, 2.0)
                  end

                  _  => begin
                      (inExp, 1.0)
                  end
                end
              end
          outRes
        end

         #= This function takes an expression XXXXX
          and return (X,5.0) to be used for X^5. =#
        function simplifyBinaryMulCoeff2(inExp::DAE.Exp) ::Tuple{DAE.Exp, ModelicaReal}
              local outRes::Tuple{DAE.Exp, ModelicaReal}

              outRes = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cr::ComponentRef
                  local coeff::ModelicaReal
                  local coeff_1::ModelicaReal
                  local coeff_2::ModelicaReal
                  local tp::Type
                  local icoeff::ModelicaInteger
                @match inExp begin
                  e && DAE.CREF(__)  => begin
                    (e, 1.0)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.POW(__), exp2 = DAE.RCONST(real = coeff))  => begin
                    (e1, coeff)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.POW(__), exp2 = DAE.UNARY(operator = DAE.UMINUS(__), exp = DAE.RCONST(real = coeff)))  => begin
                      coeff_1 = 0.0 - coeff
                    (e1, coeff_1)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.POW(__), exp2 = DAE.ICONST(integer = icoeff))  => begin
                      coeff_1 = intReal(icoeff)
                    (e1, coeff_1)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.POW(__), exp2 = DAE.UNARY(operator = DAE.UMINUS(__), exp = DAE.ICONST(integer = icoeff)))  => begin
                      coeff_1 = 0.0 - intReal(icoeff)
                    (e1, coeff_1)
                  end

                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2) where (Expression.expEqual(e1, e2))  => begin
                    (e1, 2.0)
                  end

                  _  => begin
                      (inExp, 1.0)
                  end
                end
              end
          outRes
        end

         #=
          In: (a/b + c + d + e/b)
          In: operator in {MUL, DIV}
          In: b
          -> (a/b + c  + d)  operator b
          Out: a' + e' + (c + b) operator b

          where a' = simplified(a operator b) and e' = simplified(e operator b)

          author: Vitalij Ruge
         =#
        function simplifySumOperatorExpression(iSum::DAE.Exp, iop::DAE.Operator #= MUL or DIV =#, iExp::DAE.Exp) ::DAE.Exp
              local oExp::DAE.Exp

              local T::List{DAE.Exp} = Expression.termsExpandUnary(iSum)
              local b::Bool #= simplifed? =#
              local e::DAE.Exp
              local newE::DAE.Exp
              local sE::DAE.Exp
              local tp::DAE.Type = Expression.typeOfOp(iop)

              oExp = Expression.makeConstZero(tp)
              sE = oExp
              for elem in T
                e = DAE.BINARY(elem, iop, iExp)
                newE = simplifyBinaryCoeff(e)
                b = ! Expression.expEqual(e, newE)
                if b
                  sE = Expression.expAdd(sE, newE)
                else
                  oExp = Expression.expAdd(oExp, elem)
                end
              end
              e = DAE.BINARY(oExp, iop, iExp)
              oExp = Expression.expAdd(sE, e)
          oExp
        end

         #= simplifies asub when expression already has been simplified with simplify1
        Earlier these cases were directly in simplify1, but now they are here so simplify1 only is called once for
        the subexpression =#
        function simplifyAsub0(ie::DAE.Exp, sub::ModelicaInteger, inSubExp::DAE.Exp) ::DAE.Exp
              local res::DAE.Exp

              res = begin
                  local t::Type
                  local t1::Type
                  local b::Bool
                  local bstart::Bool
                  local bstop::Bool
                  local exps::List{DAE.Exp}
                  local mexps::List{List{DAE.Exp}}
                  local mexpl::List{DAE.Exp}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cond::DAE.Exp
                  local exp::DAE.Exp
                  local e::DAE.Exp
                  local istart::ModelicaInteger
                  local istop::ModelicaInteger
                  local istep::ModelicaInteger
                  local ival::ModelicaInteger
                  local rstart::ModelicaReal
                  local rstop::ModelicaReal
                  local rstep::ModelicaReal
                  local rval::ModelicaReal
                  local c::DAE.ComponentRef
                  local c_1::DAE.ComponentRef
                  local n::ModelicaInteger
                  local op::Operator
                  local iters::List{DAE.ReductionIterator}
                   #=  subscript of an array
                   =#
                @match (ie, sub, inSubExp) begin
                  (DAE.ARRAY(_, _, exps), _, _)  => begin
                      exp = listGet(exps, sub)
                    exp
                  end

                  (DAE.RANGE(DAE.T_BOOL(__), DAE.BCONST(bstart), NONE(), DAE.BCONST(bstop)), _, _)  => begin
                      b = listGet(simplifyRangeBool(bstart, bstop), sub)
                    DAE.BCONST(b)
                  end

                  (DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), NONE(), DAE.ICONST(istop)), _, _)  => begin
                      ival = listGet(simplifyRange(istart, 1, istop), sub)
                      exp = DAE.ICONST(ival)
                    exp
                  end

                  (DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), SOME(DAE.ICONST(istep)), DAE.ICONST(istop)), _, _)  => begin
                      ival = listGet(simplifyRange(istart, istep, istop), sub)
                      exp = DAE.ICONST(ival)
                    exp
                  end

                  (DAE.RANGE(DAE.T_REAL(__), DAE.RCONST(rstart), NONE(), DAE.RCONST(rstop)), _, _)  => begin
                      rval = listGet(simplifyRangeReal(rstart, 1.0, rstop), sub)
                      exp = DAE.RCONST(rval)
                    exp
                  end

                  (DAE.RANGE(DAE.T_REAL(__), DAE.RCONST(rstart), SOME(DAE.RCONST(rstep)), DAE.RCONST(rstop)), _, _)  => begin
                      rval = listGet(simplifyRangeReal(rstart, rstep, rstop), sub)
                      exp = DAE.RCONST(rval)
                    exp
                  end

                  (DAE.MATRIX(t, _, mexps), _, _)  => begin
                      t1 = Expression.unliftArray(t)
                      mexpl = listGet(mexps, sub)
                    DAE.ARRAY(t1, true, mexpl)
                  end

                  (DAE.IFEXP(cond, e1, e2), _, _)  => begin
                      e1 = Expression.makeASUB(e1, list(inSubExp))
                      e2 = Expression.makeASUB(e2, list(inSubExp))
                      e = DAE.IFEXP(cond, e1, e2)
                    e
                  end

                  (DAE.CREF(c, t), _, _)  => begin
                      @match true = Types.isArray(t)
                      t = Expression.unliftArray(t)
                      c_1 = simplifyAsubCref(c, inSubExp)
                      exp = Expression.makeCrefExp(c_1, t)
                    exp
                  end

                  (DAE.BINARY(e1, op, e2), _, _) where (Expression.isMulOrDiv(op) || Expression.isAddOrSub(op))  => begin
                      e1 = Expression.makeASUB(e1, list(inSubExp))
                      e2 = Expression.makeASUB(e2, list(inSubExp))
                      e = if Expression.isMul(op)
                            Expression.expMul(e1, e2)
                          elseif (Expression.isDiv(op))
                                Expression.makeDiv(e1, e2)
                          elseif (Expression.isAdd(op))
                                Expression.expAdd(e1, e2)
                          else
                            Expression.expSub(e1, e2)
                          end
                    e
                  end
                end
              end
               #=  subscript of a matrix
               =#
               #=  subscript of an if-expression
               =#
               #=  name subscript
               =#
               #=  BINARAY
               =#
               #= wrap operator
               =#
          res
        end

        function simplifyAsubCref(cr::DAE.ComponentRef, sub::DAE.Exp) ::DAE.ComponentRef
              local res::DAE.ComponentRef

              res = begin
                  local t2::Type
                  local c::DAE.ComponentRef
                  local c_1::DAE.ComponentRef
                  local s::List{Subscript}
                  local s_1::List{Subscript}
                  local idn::String
                  local dims::DAE.Dimensions
                   #=  simple name subscript
                   =#
                @matchcontinue (cr, sub) begin
                  (DAE.CREF_IDENT(idn, t2, s), _)  => begin
                      s_1 = Expression.subscriptsAppend(s, sub)
                      c_1 = CrefForHashTable.makeCrefIdent(idn, t2, s_1)
                    c_1
                  end

                  (DAE.CREF_QUAL(idn, t2 && DAE.T_ARRAY(dims = dims), s, c), _)  => begin
                      @match true = listLength(dims) > listLength(s)
                      s_1 = Expression.subscriptsAppend(s, sub)
                      c_1 = CrefForHashTable.makeCrefQual(idn, t2, s_1, c)
                    c_1
                  end

                  (DAE.CREF_QUAL(idn, t2, s, c), _)  => begin
                      s = Expression.subscriptsReplaceSlice(s, DAE.INDEX(sub))
                    CrefForHashTable.makeCrefQual(idn, t2, s, c)
                  end

                  (DAE.CREF_QUAL(idn, t2, s, c), _)  => begin
                      c_1 = simplifyAsubCref(c, sub)
                      c_1 = CrefForHashTable.makeCrefQual(idn, t2, s, c_1)
                    c_1
                  end
                end
              end
               #= /* TODO: Make sure that the IDENT has enough dimensions? */ =#
               #=   qualified name subscript
               =#
          res
        end

         #= This function simplifies array subscripts on vector operations =#
        function simplifyAsub(inExp::DAE.Exp, inSub::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local exp::DAE.Exp
                  local cond::DAE.Exp
                  local sub::DAE.Exp
                  local t::Type
                  local t_1::Type
                  local t2::Type
                  local indx::ModelicaInteger
                  local i_1::ModelicaInteger
                  local n::ModelicaInteger
                  local op::Operator
                  local op2::Operator
                  local b::Bool
                  local exps::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local lstexps::List{List{DAE.Exp}}
                  local iters::List{DAE.ReductionIterator}
                  local iter::DAE.ReductionIterator
                @matchcontinue (inExp, inSub) begin
                  (e, sub)  => begin
                      exp = simplifyAsub0(e, Expression.expInt(sub), inSub)
                    exp
                  end

                  (DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e), sub)  => begin
                      e_1 = simplifyAsub(e, sub)
                      t2 = Expression.typeOf(e_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.UMINUS_ARR(t2)
                          else
                            DAE.UMINUS(t2)
                          end
                      exp = DAE.UNARY(op2, e_1)
                    exp
                  end

                  (DAE.LUNARY(operator = DAE.NOT(__), exp = e), sub)  => begin
                      e_1 = simplifyAsub(e, sub)
                      t2 = Expression.typeOf(e_1)
                      exp = DAE.LUNARY(DAE.NOT(t2), e_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.SUB_ARR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.SUB_ARR(t2)
                          else
                            DAE.SUB(t2)
                          end
                      exp = DAE.BINARY(e1_1, op2, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.MUL_ARRAY_SCALAR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.MUL_ARRAY_SCALAR(t2)
                          else
                            DAE.MUL(t2)
                          end
                      exp = DAE.BINARY(e1_1, op, e2)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.ADD_ARRAY_SCALAR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.ADD_ARRAY_SCALAR(t2)
                          else
                            DAE.ADD(t2)
                          end
                      exp = DAE.BINARY(e1_1, op, e2)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.SUB_SCALAR_ARRAY(__), exp2 = e2), sub)  => begin
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e2_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.SUB_SCALAR_ARRAY(t2)
                          else
                            DAE.SUB(t2)
                          end
                      exp = DAE.BINARY(e1, op, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.MUL_MATRIX_PRODUCT(__), exp2 = e2), sub)  => begin
                      e = simplifyMatrixProduct(e1, e2)
                      e = simplifyAsub(e, sub)
                    e
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.DIV_SCALAR_ARRAY(__), exp2 = e2), sub)  => begin
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e2_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.DIV_SCALAR_ARRAY(t2)
                          else
                            DAE.DIV(t2)
                          end
                      exp = DAE.BINARY(e1, op, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.DIV_ARRAY_SCALAR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.DIV_ARRAY_SCALAR(t2)
                          else
                            DAE.DIV(t2)
                          end
                      exp = DAE.BINARY(e1_1, op, e2)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.POW_SCALAR_ARRAY(__), exp2 = e2), sub)  => begin
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e2_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.POW_SCALAR_ARRAY(t2)
                          else
                            DAE.POW(t2)
                          end
                      exp = DAE.BINARY(e1, op, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.POW_ARRAY_SCALAR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op = if b
                            DAE.POW_ARRAY_SCALAR(t2)
                          else
                            DAE.POW(t2)
                          end
                      exp = DAE.BINARY(e1_1, op, e2)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.ADD_ARR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.ADD_ARR(t2)
                          else
                            DAE.ADD(t2)
                          end
                      exp = DAE.BINARY(e1_1, op2, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.MUL_ARR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.MUL_ARR(t2)
                          else
                            DAE.MUL(t2)
                          end
                      exp = DAE.BINARY(e1_1, op2, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.DIV_ARR(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.DIV_ARR(t2)
                          else
                            DAE.DIV(t2)
                          end
                      exp = DAE.BINARY(e1_1, op2, e2_1)
                    exp
                  end

                  (DAE.BINARY(exp1 = e1, operator = DAE.POW_ARR2(__), exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      b = DAEUtilMinimal.expTypeArray(t2)
                      op2 = if b
                            DAE.POW_ARR2(t2)
                          else
                            DAE.POW(t2)
                          end
                      exp = DAE.BINARY(e1_1, op2, e2_1)
                    exp
                  end

                  (DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                      t2 = Expression.typeOf(e1_1)
                      op = Expression.setOpType(op, t2)
                      exp = DAE.LBINARY(e1_1, op, e2_1)
                    exp
                  end

                  (DAE.ARRAY(array = exps), sub)  => begin
                      indx = Expression.expInt(sub)
                      exp = listGet(exps, indx)
                    exp
                  end

                  (DAE.MATRIX(ty = t, matrix = lstexps), sub)  => begin
                      indx = Expression.expInt(sub)
                      expl = listGet(lstexps, indx)
                      t_1 = Expression.unliftArray(t)
                    DAE.ARRAY(t_1, true, expl)
                  end

                  (DAE.IFEXP(cond, e1, e2), sub)  => begin
                      e1_1 = simplifyAsub(e1, sub)
                      e2_1 = simplifyAsub(e2, sub)
                    DAE.IFEXP(cond, e1_1, e2_1)
                  end

                  (DAE.REDUCTION(DAE.REDUCTIONINFO(path = Absyn.IDENT("array"), iterType = Absyn.THREAD(__)), exp, iters), sub)  => begin
                      exp = ListUtil.fold1(iters, simplifyAsubArrayReduction, sub, exp)
                    exp
                  end

                  (DAE.REDUCTION(DAE.REDUCTIONINFO(path = Absyn.IDENT("array"), iterType = Absyn.COMBINE(__)), exp, iter <|  nil()), sub)  => begin
                      exp = simplifyAsubArrayReduction(iter, sub, exp)
                    exp
                  end
                end
              end
               #=  For Matrix product M1 * M2
               =#
          outExp
        end

        function simplifyAsubArrayReduction(iter::DAE.ReductionIterator, sub::DAE.Exp, acc::DAE.Exp) ::DAE.Exp
              local res::DAE.Exp

              res = begin
                  local exp::DAE.Exp
                  local id::String
                @match (iter, sub, acc) begin
                  (DAE.REDUCTIONITER(id = id, exp = exp, guardExp = NONE()), _, _)  => begin
                      exp = Expression.makeASUB(exp, list(sub))
                      exp = replaceIteratorWithExp(exp, acc, id)
                    exp
                  end
                end
              end
          res
        end

        function simplifyAsubOperator(inExp1::DAE.Exp, inOperator2::Operator, inOperator3::Operator) ::Operator
              local outOperator::Operator

              outOperator = begin
                @match inExp1 begin
                  DAE.ARRAY(__)  => begin
                    inOperator3
                  end

                  DAE.MATRIX(__)  => begin
                    inOperator3
                  end

                  DAE.RANGE(__)  => begin
                    inOperator3
                  end

                  _  => begin
                      inOperator2
                  end
                end
              end
          outOperator
        end

         #= Simplifies asubs where some of the subscripts are slices.
            Ex: x[i, 1:3] => {x[i, 1], x[i, 2], x[i, 3]} =#
        function simplifyAsubSlicing(inExp::DAE.Exp, inSubscripts::List{<:DAE.Exp}) ::DAE.Exp
              local outAsubArray::DAE.Exp

              local indices::List{List{DAE.Exp}}
              local asubs::List{DAE.Exp}
              local es::List{DAE.Exp}
              local sz::ModelicaInteger
              local elem::DAE.Exp
              local ty::DAE.Type
              local didSplit::Bool = false
              local b::Bool

               #=  Expand the subscripts.
               =#
              indices = list(begin
                @match () begin
                  ()  => begin
                      (es, b) = Expression.splitArray(simplify1(e))
                      didSplit = didSplit || b
                    es
                  end
                end
              end for e in inSubscripts)
               #=  We don't want to loop forever... So keep track of if we actually expanded something
               =#
              @match true = didSplit
              for is in indices
                for i in is
                  _ = begin
                    @match Expression.typeOf(i) begin
                      DAE.T_INTEGER(__)  => begin
                        ()
                      end

                      DAE.T_BOOL(__)  => begin
                        ()
                      end

                      DAE.T_ENUMERATION(__)  => begin
                        ()
                      end

                      _  => begin
                          fail()
                      end
                    end
                  end
                end
              end
               #=  Make sure all asubs are scalar (were split by splitArray; no function calls or weird stuff left)
               =#
               #=  Make asubs from all combinations of the subscript indices.
               =#
              asubs = ListUtil.combinationMap1(indices, simplifyAsubSlicing2, inExp)
              outAsubArray = Expression.makeScalarArray(asubs, Types.unliftArray(Expression.typeOf(inExp)))
          outAsubArray
        end

        function simplifyAsubSlicing2(inSubscripts::List{<:DAE.Exp}, inExp::DAE.Exp) ::DAE.Exp
              local outAsub::DAE.Exp

              outAsub = Expression.makeASUB(inExp, inSubscripts)
          outAsub
        end

         #= This function evaluates constant binary expressions. =#
        function simplifyBinaryConst(inOperator1::Operator, inExp2::DAE.Exp, inExp3::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local ie1::ModelicaInteger
                  local ie2::ModelicaInteger
                  local e2_1::ModelicaReal
                  local e1_1::ModelicaReal
                  local v1::ModelicaReal
                  local v2::ModelicaReal
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local val::DAE.Exp
                  local re1::ModelicaReal
                  local re2::ModelicaReal
                  local re3::ModelicaReal
                  local str::String
                  local s1::String
                  local s2::String
                  local oexp::Option{DAE.Exp}
                  local ty::DAE.Type
                @match (inOperator1, inExp2, inExp3) begin
                  (DAE.ADD(__), DAE.ICONST(integer = ie1), DAE.ICONST(integer = ie2))  => begin
                      val = safeIntOp(ie1, ie2, ExpressionSimplifyTypes.ADDOP())
                    val
                  end

                  (DAE.ADD(__), DAE.RCONST(real = re1), DAE.RCONST(real = re2))  => begin
                      re3 = re1 + re2
                    DAE.RCONST(re3)
                  end

                  (DAE.ADD(__), DAE.RCONST(real = re1), DAE.ICONST(integer = ie2))  => begin
                      e2_1 = intReal(ie2)
                      re3 = re1 + e2_1
                    DAE.RCONST(re3)
                  end

                  (DAE.ADD(__), DAE.ICONST(integer = ie1), DAE.RCONST(real = re2))  => begin
                      e1_1 = intReal(ie1)
                      re3 = e1_1 + re2
                    DAE.RCONST(re3)
                  end

                  (DAE.ADD(__), DAE.SCONST(string = s1), DAE.SCONST(string = s2))  => begin
                      str = s1 + s2
                    DAE.SCONST(str)
                  end

                  (DAE.SUB(__), DAE.ICONST(integer = ie1), DAE.ICONST(integer = ie2))  => begin
                      val = safeIntOp(ie1, ie2, ExpressionSimplifyTypes.SUBOP())
                    val
                  end

                  (DAE.SUB(__), DAE.RCONST(real = re1), DAE.RCONST(real = re2))  => begin
                      re3 = re1 - re2
                    DAE.RCONST(re3)
                  end

                  (DAE.SUB(__), DAE.RCONST(real = re1), DAE.ICONST(integer = ie2))  => begin
                      e2_1 = intReal(ie2)
                      re3 = re1 - e2_1
                    DAE.RCONST(re3)
                  end

                  (DAE.SUB(__), DAE.ICONST(integer = ie1), DAE.RCONST(real = re2))  => begin
                      e1_1 = intReal(ie1)
                      re3 = e1_1 - re2
                    DAE.RCONST(re3)
                  end

                  (DAE.MUL(__), DAE.ICONST(integer = ie1), DAE.ICONST(integer = ie2))  => begin
                      val = safeIntOp(ie1, ie2, ExpressionSimplifyTypes.MULOP())
                    val
                  end

                  (DAE.MUL(__), DAE.RCONST(real = re1), DAE.RCONST(real = re2))  => begin
                      re3 = re1 * re2
                    DAE.RCONST(re3)
                  end

                  (DAE.MUL(__), DAE.RCONST(real = re1), DAE.ICONST(integer = ie2))  => begin
                      e2_1 = intReal(ie2)
                      re3 = re1 * e2_1
                    DAE.RCONST(re3)
                  end

                  (DAE.MUL(__), DAE.ICONST(integer = ie1), DAE.RCONST(real = re2))  => begin
                      e1_1 = intReal(ie1)
                      re3 = e1_1 * re2
                    DAE.RCONST(re3)
                  end

                  (DAE.DIV(__), DAE.ICONST(integer = ie1), DAE.ICONST(integer = ie2))  => begin
                      val = safeIntOp(ie1, ie2, ExpressionSimplifyTypes.DIVOP())
                    val
                  end

                  (DAE.DIV(__), DAE.RCONST(real = re1), DAE.RCONST(real = re2))  => begin
                      re3 = re1 / re2
                    DAE.RCONST(re3)
                  end

                  (DAE.DIV(__), DAE.RCONST(real = re1), DAE.ICONST(integer = ie2))  => begin
                      e2_1 = intReal(ie2)
                      re3 = re1 / e2_1
                    DAE.RCONST(re3)
                  end

                  (DAE.DIV(__), DAE.ICONST(integer = ie1), DAE.RCONST(real = re2))  => begin
                      e1_1 = intReal(ie1)
                      re3 = e1_1 / re2
                    DAE.RCONST(re3)
                  end

                  (DAE.POW(__), DAE.RCONST(real = re1), DAE.RCONST(real = re2))  => begin
                      re3 = re1 ^ re2
                    DAE.RCONST(re3)
                  end
                end
              end
          outExp
        end

         #= This function evaluates constant binary expressions. =#
        function simplifyRelationConst(op::Operator, e1::DAE.Exp, e2::DAE.Exp) ::Bool
              local b::Bool

              b = begin
                  local v1::ModelicaReal
                  local v2::ModelicaReal
                  local b1::Bool
                  local b2::Bool
                  local s1::String
                  local s2::String
                   #=  Relation operations
                   =#
                @match (op, e1, e2) begin
                  (DAE.LESS(__), DAE.BCONST(false), DAE.BCONST(true))  => begin
                    true
                  end

                  (DAE.LESS(__), DAE.BCONST(_), DAE.BCONST(_))  => begin
                    false
                  end

                  (DAE.LESS(__), _, _)  => begin
                      v1 = Expression.toReal(e1)
                      v2 = Expression.toReal(e2)
                      b = v1 < v2
                    b
                  end

                  (DAE.LESSEQ(__), DAE.BCONST(true), DAE.BCONST(false))  => begin
                    false
                  end

                  (DAE.LESSEQ(__), DAE.BCONST(_), DAE.BCONST(_))  => begin
                    true
                  end

                  (DAE.LESSEQ(__), _, _)  => begin
                      v1 = Expression.toReal(e1)
                      v2 = Expression.toReal(e2)
                      b = v1 <= v2
                    b
                  end

                  (DAE.EQUAL(__), DAE.BCONST(b1), DAE.BCONST(b2))  => begin
                    boolEq(b1, b2)
                  end

                  (DAE.EQUAL(__), DAE.SCONST(s1), DAE.SCONST(s2))  => begin
                    stringEqual(s1, s2)
                  end

                  (DAE.EQUAL(__), _, _)  => begin
                      v1 = Expression.toReal(e1)
                      v2 = Expression.toReal(e2)
                    realEq(v1, v2)
                  end

                  (DAE.GREATER(__), _, _)  => begin
                    ! simplifyRelationConst(DAE.LESSEQ(DAE.T_REAL_DEFAULT), e1, e2)
                  end

                  (DAE.GREATEREQ(__), _, _)  => begin
                    ! simplifyRelationConst(DAE.LESS(DAE.T_REAL_DEFAULT), e1, e2)
                  end

                  (DAE.GREATER(__), DAE.BCONST(false), DAE.BCONST(true))  => begin
                    ! simplifyRelationConst(DAE.LESSEQ(DAE.T_REAL_DEFAULT), e1, e2)
                  end

                  (DAE.GREATEREQ(__), DAE.BCONST(false), DAE.BCONST(true))  => begin
                    ! simplifyRelationConst(DAE.LESS(DAE.T_REAL_DEFAULT), e1, e2)
                  end

                  (DAE.NEQUAL(__), _, _)  => begin
                    ! simplifyRelationConst(DAE.EQUAL(DAE.T_REAL_DEFAULT), e1, e2)
                  end
                end
              end
               #=  Express GT, GE, NE using LE, LT, EQ
               =#
          b
        end

         #= Safe mul, add, sub or pow operations for integers.
           The function returns an integer if possible, otherwise a real.
           =#
        function safeIntOp(val1::ModelicaInteger, val2::ModelicaInteger, op::ExpressionSimplifyTypes.IntOp) ::DAE.Exp
              local outv::DAE.Exp

              outv = begin
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local rv3::ModelicaReal
                  local ires::ModelicaInteger
                @match (val1, val2, op) begin
                  (_, _, ExpressionSimplifyTypes.MULOP(__))  => begin
                      rv1 = intReal(val1)
                      rv2 = intReal(val2)
                      rv3 = rv1 * rv2
                      outv = Expression.realToIntIfPossible(rv3)
                    outv
                  end

                  (_, _, ExpressionSimplifyTypes.DIVOP(__))  => begin
                      ires = intDiv(val1, val2)
                    DAE.ICONST(ires)
                  end

                  (_, _, ExpressionSimplifyTypes.SUBOP(__))  => begin
                      rv1 = intReal(val1)
                      rv2 = intReal(val2)
                      rv3 = rv1 - rv2
                      outv = Expression.realToIntIfPossible(rv3)
                    outv
                  end

                  (_, _, ExpressionSimplifyTypes.ADDOP(__))  => begin
                      rv1 = intReal(val1)
                      rv2 = intReal(val2)
                      rv3 = rv1 + rv2
                      outv = Expression.realToIntIfPossible(rv3)
                    outv
                  end

                  (_, _, ExpressionSimplifyTypes.POWOP(__))  => begin
                      rv1 = intReal(val1)
                      rv2 = intReal(val2)
                      rv3 = realPow(rv1, rv2)
                      outv = Expression.realToIntIfPossible(rv3)
                    outv
                  end
                end
              end
          outv
        end

         #= This function simplifies commutative binary expressions. =#
        function simplifyBinaryCommutativeWork(op::Operator, lhs::DAE.Exp, rhs::DAE.Exp) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res::DAE.Exp
                  local op1::Operator
                  local op2::Operator
                  local ty::Type
                  local ty2::Type
                  local tp::Type
                  local tp2::Type
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local r3::ModelicaReal
                   #= /* sin(2*x) = 2*sin(x)*cos(x) */ =#
                @matchcontinue (op, lhs, rhs) begin
                  (DAE.MUL(_), DAE.CALL(path = Absyn.IDENT("sin"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("cos"), expLst = e2 <|  nil())) where (Expression.expEqual(e1, e2))  => begin
                      op1 = DAE.MUL(DAE.T_REAL_DEFAULT)
                      e = DAE.BINARY(DAE.RCONST(2.0), op1, e1)
                      e = Expression.makePureBuiltinCall("sin", list(e), DAE.T_REAL_DEFAULT)
                    DAE.BINARY(DAE.RCONST(0.5), op1, e)
                  end

                  (DAE.ADD(_), DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sin"), expLst = e1 <|  nil()), DAE.POW(DAE.T_REAL(__)), DAE.RCONST(real = 2.0)), DAE.BINARY(DAE.CALL(path = Absyn.IDENT("cos"), expLst = e2 <|  nil()), DAE.POW(DAE.T_REAL(__)), DAE.RCONST(real = 2.0))) where (Expression.expEqual(e1, e2))  => begin
                    DAE.RCONST(1.0)
                  end

                  (DAE.MUL(tp), DAE.CALL(path = Absyn.IDENT("tan"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("cos"), expLst = e2 <|  nil())) where (Expression.expEqual(e1, e2))  => begin
                    Expression.makePureBuiltinCall("sin", list(e1), tp)
                  end

                  (DAE.ADD(_), DAE.BINARY(DAE.CALL(path = Absyn.IDENT("cosh"), expLst = e1 <|  nil()), DAE.POW(DAE.T_REAL(__)), DAE.RCONST(real = 2.0)), DAE.UNARY(operator = DAE.UMINUS(__), exp = DAE.BINARY(DAE.CALL(path = Absyn.IDENT("sinh"), expLst = e2 <|  nil()), DAE.POW(DAE.T_REAL(__)), DAE.RCONST(real = 2.0)))) where (Expression.expEqual(e1, e2))  => begin
                    DAE.RCONST(1.0)
                  end

                  (DAE.MUL(tp), DAE.CALL(path = Absyn.IDENT("tanh"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("cosh"), expLst = e2 <|  nil())) where (Expression.expEqual(e1, e2))  => begin
                    Expression.makePureBuiltinCall("sinh", list(e1), tp)
                  end

                  (DAE.ADD(ty = tp), e1, DAE.UNARY(operator = DAE.UMINUS(__), exp = e2))  => begin
                    DAE.BINARY(e1, DAE.SUB(tp), e2)
                  end

                  (DAE.ADD(ty = tp), e1, DAE.BINARY(DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), op2, e3)) where (Expression.isMulOrDiv(op2))  => begin
                    DAE.BINARY(e1, DAE.SUB(tp), DAE.BINARY(e2, op2, e3))
                  end

                  (DAE.ADD(__), e1, e2) where (Expression.isZero(e1))  => begin
                    e2
                  end

                  (DAE.MUL(ty = tp), e1, DAE.BINARY(exp1 = e2, operator = DAE.DIV(ty = tp2), exp2 = e3))  => begin
                      @match (e, true) = simplify1(DAE.BINARY(e1, DAE.MUL(tp), e2))
                    DAE.BINARY(e, DAE.DIV(tp2), e3)
                  end

                  (DAE.MUL(__), _, e2) where (Expression.isZero(e2))  => begin
                    e2
                  end

                  (DAE.MUL(__), e1, e2) where (Expression.isConstOne(e2))  => begin
                    e1
                  end

                  (DAE.MUL(ty = ty), e1, e2) where (Expression.isConstMinusOne(e2))  => begin
                    DAE.UNARY(DAE.UMINUS(ty), e1)
                  end

                  (DAE.MUL(__), DAE.BINARY(e2, op1 && DAE.MUL(ty), e3), e1) where (Types.isScalarReal(ty) && Expression.expEqual(e2, e1))  => begin
                    DAE.BINARY(e3, op1, DAE.BINARY(e1, DAE.POW(ty), DAE.RCONST(2.0)))
                  end

                  (DAE.MUL(__), e1, DAE.BINARY(e2, op1 && DAE.MUL(ty), e3)) where (Types.isScalarReal(ty) && Expression.expEqual(e1, e3))  => begin
                    DAE.BINARY(e2, op1, DAE.BINARY(e1, DAE.POW(ty), DAE.RCONST(2.0)))
                  end

                  (DAE.MUL(__), DAE.RCONST(real = r1), DAE.BINARY(DAE.RCONST(real = r2), DAE.MUL(DAE.T_REAL(__)), e2))  => begin
                    DAE.BINARY(DAE.RCONST(r1 * r2), DAE.MUL(DAE.T_REAL_DEFAULT), e2)
                  end

                  (DAE.MUL(__), DAE.RCONST(real = r1), DAE.BINARY(e2, DAE.MUL(DAE.T_REAL(__)), DAE.RCONST(real = r2)))  => begin
                    DAE.BINARY(DAE.RCONST(r1 * r2), DAE.MUL(DAE.T_REAL_DEFAULT), e2)
                  end

                  (DAE.ADD(__), DAE.RCONST(r1), DAE.BINARY(DAE.RCONST(r2), DAE.SUB(ty = ty), e1 && DAE.CREF(_)))  => begin
                    DAE.BINARY(DAE.RCONST(realAdd(r1, r2)), DAE.SUB(ty), e1)
                  end

                  (DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("abs"), expLst = e1 <|  nil()), e2) where (Expression.expEqual(e1, e2))  => begin
                    Expression.makePureBuiltinCall("sign", list(e1), ty)
                  end

                  (op1 && DAE.ADD(ty), e1, DAE.BINARY(e2, op2 && DAE.MUL(__), e3)) where (! Expression.isConstValue(e1))  => begin
                      if Expression.expEqual(e1, e3)
                        exp = DAE.BINARY(e1, op2, DAE.BINARY(Expression.makeConstOne(ty), op1, e2))
                      else
                        if Expression.expEqual(e1, e2)
                          exp = DAE.BINARY(e1, op2, DAE.BINARY(Expression.makeConstOne(ty), op1, e3))
                        else
                          fail()
                        end
                      end
                    exp
                  end

                  (DAE.MUL(__), DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()), e2) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BINARY(e1, DAE.POW(DAE.T_REAL_DEFAULT), DAE.RCONST(1.5))
                  end

                  (DAE.MUL(__), DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()), DAE.BINARY(e2, DAE.POW(__), e)) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BINARY(e1, DAE.POW(DAE.T_REAL_DEFAULT), DAE.BINARY(e, DAE.ADD(DAE.T_REAL_DEFAULT), DAE.RCONST(0.5)))
                  end

                  (DAE.MUL(__), e1, DAE.BINARY(e3, op1 && DAE.POW(tp), e4)) where (Expression.expEqual(e1, e3))  => begin
                      e = Expression.makeConstOne(tp)
                    DAE.BINARY(e1, op1, DAE.BINARY(e, DAE.ADD(tp), e4))
                  end
                end
              end
               #=  sqrt(e) * e => e^1.5
               =#
               #=  sqrt(e) * e^r => e^(r+0.5)
               =#
               #=  x*x^y => x^(y+1)
               =#
          exp
        end

         #= This function simplifies binary expressions. =#
        function simplifyBinary(origExp::DAE.Exp, inOperator2::Operator, lhs::DAE.Exp #= Note: already simplified =#, rhs::DAE.Exp #= Note: aldready simplified =#) ::DAE.Exp
              local outExp::DAE.Exp

              local lhsIsConstValue::Bool = Expression.isConstValue(lhs)
              local rhsIsConstValue::Bool = Expression.isConstValue(rhs)

              outExp = begin
                  local e1_1::DAE.Exp
                  local e3::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e4::DAE.Exp
                  local e5::DAE.Exp
                  local e6::DAE.Exp
                  local res::DAE.Exp
                  local one::DAE.Exp
                  local oper::Operator
                  local op1::Operator
                  local op2::Operator
                  local op3::Operator
                  local op::Operator
                  local ty::Type
                  local ty2::Type
                  local tp::Type
                  local tp2::Type
                  local ty1::Type
                  local exp_lst::List{DAE.Exp}
                  local exp_lst_1::List{DAE.Exp}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local b::Bool
                  local b2::Bool
                  local r::ModelicaReal
                  local r1::ModelicaReal
                  local i2::ModelicaInteger
                  local oexp::Option{DAE.Exp}
                   #=  binary operations on arrays
                   =#
                @matchcontinue (origExp, inOperator2, lhs, rhs, lhsIsConstValue, rhsIsConstValue) begin
                  (_, op, e1, e2, _, _) where (simplifyBinaryArrayOp(op))  => begin
                    simplifyBinaryArray(e1, op, e2)
                  end

                  (_, op, e1, e2, _, _)  => begin
                    simplifyBinaryCommutativeWork(op, e1, e2)
                  end

                  (_, op, e1, e2, _, _)  => begin
                    simplifyBinaryCommutativeWork(op, e2, e1)
                  end

                  (_, oper, e1, e2, true, true)  => begin
                      e3 = simplifyBinaryConst(oper, e1, e2)
                    e3
                  end

                  (_, oper, DAE.BINARY(e1, op1, e2), DAE.BINARY(e3, op2, e4), _, _)  => begin
                    simplifyTwoBinaryExpressions(e1, op1, e2, oper, e3, op2, e4, Expression.expEqual(e1, e3), Expression.expEqual(e1, e4), Expression.expEqual(e2, e3), Expression.expEqual(e2, e4), Expression.isConstValue(e1), Expression.isConstValue(e2), Expression.isConstValue(e3), Expression.operatorEqual(op1, op2))
                  end

                  (_, oper, e1, e2, _, _)  => begin
                      @match true = Expression.isConstZeroLength(e1) || Expression.isConstZeroLength(e2)
                      checkZeroLengthArrayOp(oper)
                    e1
                  end

                  (_, DAE.MUL(__), e1, DAE.BINARY(exp1 = e2, operator = op1 && DAE.POW(ty = ty2), exp2 = DAE.UNARY(exp = e3, operator = DAE.UMINUS(__))), _, _)  => begin
                      res = DAE.BINARY(e1, DAE.DIV(ty2), DAE.BINARY(e2, op1, e3))
                    res
                  end

                  (_, DAE.DIV(__), e1, DAE.BINARY(exp1 = e2, operator = op1 && DAE.POW(ty = ty2), exp2 = DAE.UNARY(exp = e3, operator = DAE.UMINUS(__))), _, _)  => begin
                      res = DAE.BINARY(e1, DAE.MUL(ty2), DAE.BINARY(e2, op1, e3))
                    res
                  end

                  (_, DAE.MUL(__), e1, DAE.BINARY(exp1 = e2, operator = op1 && DAE.POW(ty = ty2), exp2 = DAE.RCONST(r)), _, _)  => begin
                      @match true = realLt(r, 0.0)
                      r = realNeg(r)
                      res = DAE.BINARY(e1, DAE.DIV(ty2), DAE.BINARY(e2, op1, DAE.RCONST(r)))
                    res
                  end

                  (_, DAE.DIV(__), e1, DAE.BINARY(exp1 = e2, operator = op1 && DAE.POW(ty = ty2), exp2 = DAE.RCONST(r)), _, _)  => begin
                      @match true = realLt(r, 0.0)
                      r = realNeg(r)
                      res = DAE.BINARY(e1, DAE.MUL(ty2), DAE.BINARY(e2, op1, DAE.RCONST(r)))
                    res
                  end

                  (_, DAE.DIV(_), DAE.BINARY(DAE.BINARY(e1, DAE.MUL(_), e2), op1, e3), e4, _, _)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.expEqual(e2, e4)
                      e = Expression.makeDiv(e3, e4)
                      res = DAE.BINARY(e1, op1, e)
                    res
                  end

                  (_, DAE.DIV(_), DAE.BINARY(e3, op1, DAE.BINARY(e1, DAE.MUL(_), e2)), e4, _, _)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.expEqual(e2, e4)
                      e = Expression.makeDiv(e3, e4)
                      res = DAE.BINARY(e, op1, e1)
                    res
                  end

                  (_, DAE.DIV(_), DAE.BINARY(DAE.BINARY(e1, op2 && DAE.MUL(__), DAE.BINARY(e2, DAE.MUL(_), e3)), op1, e4), e5, _, _)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.expEqual(e3, e5)
                      e = Expression.makeDiv(e4, e3)
                      e1_1 = DAE.BINARY(e1, op2, e2)
                      res = DAE.BINARY(e1_1, op1, e)
                    res
                  end

                  (_, op2, DAE.CALL(path = Absyn.IDENT("abs"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("abs"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.isMulOrDiv(op2)
                      ty = Expression.typeOf(e1)
                      res = DAE.BINARY(e1, op2, e2)
                    Expression.makePureBuiltinCall("abs", list(res), ty)
                  end

                  (_, DAE.DIV(ty), e1, DAE.CALL(path = Absyn.IDENT("exp"), expLst = e2 <|  nil()), _, _)  => begin
                      e = DAE.UNARY(DAE.UMINUS(ty), e2)
                      (e, _) = simplify1(e)
                      e3 = Expression.makePureBuiltinCall("exp", list(e), ty)
                      res = DAE.BINARY(e1, DAE.MUL(ty), e3)
                    res
                  end

                  (_, DAE.MUL(ty), DAE.CALL(path = Absyn.IDENT("exp"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("exp"), expLst = e2 <|  nil()), _, _)  => begin
                      @match false = Expression.isConstValue(e1) || Expression.isConstValue(e2)
                      e = DAE.BINARY(e1, DAE.ADD(ty), e2)
                      res = Expression.makePureBuiltinCall("exp", list(e), ty)
                    res
                  end

                  (_, op1 && DAE.DIV(ty = ty), DAE.BINARY(exp1 = e1, operator = op2 && DAE.ADD(ty = ty2), exp2 = e2), e3, _, true)  => begin
                      (e, b) = simplify1(DAE.BINARY(e1, op1, e3))
                      (e4, b2) = simplify1(DAE.BINARY(e2, op1, e3))
                      @match true = b || b2
                    DAE.BINARY(e, op2, e4)
                  end

                  (_, op1 && DAE.DIV(ty = ty), DAE.BINARY(exp1 = e1, operator = op2 && DAE.SUB(ty = ty2), exp2 = e2), e3, _, true)  => begin
                      (e, b) = simplify1(DAE.BINARY(e1, op1, e3))
                      (e4, b2) = simplify1(DAE.BINARY(e2, op1, e3))
                      @match true = b || b2
                    DAE.BINARY(e, op2, e4)
                  end

                  (_, DAE.DIV(ty = tp), e1, DAE.BINARY(exp1 = e2, operator = op2 && DAE.DIV(ty = tp2), exp2 = e3), _, _)  => begin
                    DAE.BINARY(DAE.BINARY(e1, DAE.MUL(tp), e3), op2, e2)
                  end

                  (_, DAE.DIV(ty = tp), DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = tp2), exp2 = e2), e3, _, _)  => begin
                    DAE.BINARY(e1, DAE.DIV(tp2), DAE.BINARY(e2, DAE.MUL(tp), e3))
                  end

                  (_, DAE.DIV(__), e1, DAE.BINARY(exp1 = e2, operator = DAE.MUL(ty = tp2), exp2 = e3), _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                    DAE.BINARY(DAE.RCONST(1.0), DAE.DIV(tp2), e2)
                  end

                  (_, DAE.DIV(__), e1, DAE.BINARY(exp1 = e2, operator = DAE.MUL(ty = tp2), exp2 = e3), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                    DAE.BINARY(DAE.RCONST(1.0), DAE.DIV(tp2), e3)
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2), e3, _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                    e2
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2), e3, _, _)  => begin
                      @match true = Expression.expEqual(e2, e3)
                    e1
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), operator = DAE.MUL(__), exp2 = e2), e3, _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      tp2 = Expression.typeOf(e2)
                      e = DAE.UNARY(DAE.UMINUS(tp2), e2)
                    e
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), operator = DAE.MUL(__), exp2 = e2), e3, _, _)  => begin
                      @match true = Expression.expEqual(e2, e3)
                      tp2 = Expression.typeOf(e1)
                      e = DAE.UNARY(DAE.UMINUS(tp2), e1)
                    e
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2), DAE.UNARY(operator = DAE.UMINUS(__), exp = e3), _, _)  => begin
                      @match true = Expression.expEqual(e2, e3)
                      tp2 = Expression.typeOf(e1)
                    DAE.UNARY(DAE.UMINUS(tp2), e1)
                  end

                  (_, DAE.DIV(__), DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2), DAE.UNARY(operator = DAE.UMINUS(__), exp = e3), _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      tp2 = Expression.typeOf(e2)
                    DAE.UNARY(DAE.UMINUS(tp2), e2)
                  end

                  (_, DAE.SUB(ty = ty), e1, e2, true, _)  => begin
                      @match true = Expression.isZero(e1)
                    DAE.UNARY(DAE.UMINUS(ty), e2)
                  end

                  (_, DAE.SUB(__), e1, e2, _, true)  => begin
                      @match true = Expression.isZero(e2)
                    e1
                  end

                  (_, DAE.SUB(ty = ty), e1, e2, _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                    Expression.makeConstZero(ty)
                  end

                  (_, DAE.ADD(ty = ty), e1, e2, _, _)  => begin
                      @match true = Types.isRealOrSubTypeReal(ty)
                      @match true = Expression.expEqual(e1, e2)
                      e = Expression.makeConstNumber(ty, 2)
                    DAE.BINARY(e, DAE.MUL(ty), e1)
                  end

                  (_, DAE.SUB(ty = ty), e1, DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), _, _)  => begin
                    DAE.BINARY(e1, DAE.ADD(ty), e2)
                  end

                  (_, DAE.SUB(ty = ty), e1, DAE.BINARY(DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), op1 && DAE.MUL(_), e3), _, _)  => begin
                    DAE.BINARY(e1, DAE.ADD(ty), DAE.BINARY(e2, op1, e3))
                  end

                  (_, DAE.SUB(ty = ty), e1, DAE.BINARY(DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), op1 && DAE.DIV(_), e3), _, _)  => begin
                    DAE.BINARY(e1, DAE.ADD(ty), DAE.BINARY(e2, op1, e3))
                  end

                  (_, DAE.DIV(__), e1, e2, true, false)  => begin
                      @match true = Expression.isZero(e1)
                      @match false = Expression.isZero(e2)
                    DAE.RCONST(0.0)
                  end

                  (_, DAE.DIV(__), e1, e2, false, true)  => begin
                      @match true = Expression.isConstOne(e2)
                    e1
                  end

                  (_, DAE.DIV(ty = ty), e1, e2, _, _)  => begin
                      @match true = Expression.isConstMinusOne(e2)
                      e = DAE.UNARY(DAE.UMINUS(ty), e1)
                    e
                  end

                  (_, DAE.DIV(ty = ty), e1, e2, _, _)  => begin
                      @match false = Expression.isZero(e2)
                      @match true = Expression.expEqual(e1, e2)
                      res = Expression.makeConstOne(ty)
                    res
                  end

                  (_, DAE.MUL(ty = ty), e1, e2, _, _)  => begin
                      @match false = Expression.isZero(e2)
                      @match true = Types.isRealOrSubTypeReal(ty)
                      @match true = Expression.expEqual(e1, e2)
                      res = DAE.BINARY(e1, DAE.POW(ty), DAE.RCONST(2.0))
                    res
                  end

                  (_, DAE.DIV(ty = tp), e1, DAE.RCONST(real = r1), _, _)  => begin
                      @match true = realAbs(r1) > 0.0
                      r = 1.0 / r1
                      r1 = 1e12 * r
                      @match 0.0 = realMod(r1, 1.0)
                      e3 = DAE.BINARY(DAE.RCONST(r), DAE.MUL(tp), e1)
                    e3
                  end

                  (_, op2 && DAE.DIV(ty = tp), e1, DAE.BINARY(DAE.RCONST(real = r1), DAE.MUL(_), e3), _, _)  => begin
                      @match true = realAbs(r1) > 0.0
                      r = 1.0 / r1
                      r1 = 1e12 * r
                      @match 0.0 = realMod(r1, 1.0)
                    DAE.BINARY(DAE.BINARY(DAE.RCONST(r), DAE.MUL(tp), e1), op2, e3)
                  end

                  (_, op1 && DAE.DIV(ty = ty), DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), _, _)  => begin
                    DAE.BINARY(e1, op1, e2)
                  end

                  (_, op2 && DAE.MUL(__), DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), DAE.BINARY(e2, op1 && DAE.SUB(_), e3), _, _)  => begin
                    DAE.BINARY(e1, op2, DAE.BINARY(e3, op1, e2))
                  end

                  (_, op2 && DAE.DIV(__), DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), DAE.BINARY(e2, op1 && DAE.SUB(_), e3), _, _)  => begin
                    DAE.BINARY(e1, op2, DAE.BINARY(e3, op1, e2))
                  end

                  (_, op2 && DAE.MUL(__), e1, DAE.BINARY(DAE.UNARY(operator = op3 && DAE.UMINUS(__), exp = e2), DAE.SUB(ty = ty), e3), _, _)  => begin
                    DAE.BINARY(DAE.UNARY(op3, e1), op2, DAE.BINARY(e2, DAE.ADD(ty), e3))
                  end

                  (_, op2 && DAE.DIV(__), e1, DAE.BINARY(DAE.UNARY(operator = op3 && DAE.UMINUS(__), exp = e2), DAE.SUB(ty = ty), e3), _, _)  => begin
                    DAE.BINARY(DAE.UNARY(op3, e1), op2, DAE.BINARY(e2, DAE.ADD(ty), e3))
                  end

                  (_, op2 && DAE.POW(__), DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), e2 && DAE.RCONST(2.0), _, _)  => begin
                    DAE.BINARY(e1, op2, e2)
                  end

                  (_, op1 && DAE.DIV(ty = ty), e1, DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), _, _)  => begin
                      e1_1 = DAE.UNARY(DAE.UMINUS(ty), e1)
                    DAE.BINARY(e1_1, op1, e2)
                  end

                  (_, op1 && DAE.DIV(ty = tp2), DAE.BINARY(exp1 = e2, operator = op2 && DAE.MUL(ty = tp), exp2 = e3), e1, _, true)  => begin
                      @match true = Expression.isConstValue(e3)
                      @match (e, true) = simplify1(DAE.BINARY(e3, op1, e1))
                    DAE.BINARY(e, op2, e2)
                  end

                  (_, op1 && DAE.DIV(ty = tp2), DAE.BINARY(exp1 = e2, operator = op2 && DAE.MUL(ty = tp), exp2 = e3), e1, _, true)  => begin
                      @match true = Expression.isConstValue(e2)
                      @match (e, true) = simplify1(DAE.BINARY(e2, op1, e1))
                    DAE.BINARY(e, op2, e3)
                  end

                  (_, DAE.POW(__), e1, e, _, true)  => begin
                      @match true = Expression.isConstOne(e)
                    e1
                  end

                  (_, DAE.POW(ty = tp), e2, e, _, _)  => begin
                      @match true = Expression.isConstMinusOne(e)
                      one = Expression.makeConstOne(tp)
                    DAE.BINARY(one, DAE.DIV(DAE.T_REAL_DEFAULT), e2)
                  end

                  (_, DAE.POW(__), e1, e, _, true)  => begin
                      @match true = Expression.isZero(e)
                      tp = Expression.typeOf(e1)
                    Expression.makeConstOne(tp)
                  end

                  (_, DAE.POW(__), DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e <|  nil()), DAE.RCONST(2.0), _, _)  => begin
                    e
                  end

                  (_, oper && DAE.POW(__), DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()), e, _, _)  => begin
                    DAE.BINARY(e1, oper, DAE.BINARY(DAE.RCONST(0.5), DAE.MUL(DAE.T_REAL_DEFAULT), e))
                  end

                  (_, DAE.DIV(__), e1, DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                    Expression.makePureBuiltinCall("sqrt", list(e1), DAE.T_REAL_DEFAULT)
                  end

                  (_, DAE.DIV(__), DAE.BINARY(e1, op1 && DAE.POW(ty), e2), e3, _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      e4 = Expression.makeConstOne(ty)
                      e4 = DAE.BINARY(e2, DAE.SUB(ty), e4)
                    DAE.BINARY(e1, op1, e4)
                  end

                  (_, DAE.DIV(__), DAE.BINARY(DAE.BINARY(e1, op1 && DAE.POW(ty), e2), op2 && DAE.MUL(_), e5), e3, _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      e4 = Expression.makeConstOne(ty)
                      e4 = DAE.BINARY(e2, DAE.SUB(ty), e4)
                    DAE.BINARY(DAE.BINARY(e1, op1, e4), op2, e5)
                  end

                  (_, DAE.DIV(__), e3, DAE.BINARY(e1, op1 && DAE.POW(ty), e2), _, _)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      e4 = Expression.makeConstOne(ty)
                      e4 = DAE.BINARY(e4, DAE.SUB(ty), e2)
                    DAE.BINARY(e1, op1, e4)
                  end

                  (_, op2 && DAE.POW(__), DAE.BINARY(e1, op1 && DAE.DIV(_), e2), DAE.RCONST(r), _, _)  => begin
                      @match true = realLt(r, 0.0)
                      r = realNeg(r)
                    DAE.BINARY(DAE.BINARY(e2, op1, e1), op2, DAE.RCONST(r))
                  end

                  (_, DAE.POW(__), e1, _, true, _)  => begin
                      @match true = Expression.isConstOne(e1)
                    e1
                  end

                  (_, op1, DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), DAE.IFEXP(expCond = e4, expThen = e5, expElse = e6), _, _)  => begin
                      @match true = Expression.expEqual(e1, e4)
                      e = DAE.BINARY(e2, op1, e5)
                      res = DAE.BINARY(e3, op1, e6)
                    DAE.IFEXP(e1, e, res)
                  end

                  (_, DAE.SUB(ty), DAE.BINARY(e && DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), op2 && DAE.MUL(__), e2), DAE.BINARY(e3, DAE.MUL(__), e4), false, false)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      res = DAE.BINARY(e, op2, DAE.BINARY(e2, DAE.ADD(ty), e4))
                    res
                  end

                  (_, DAE.SUB(ty), DAE.BINARY(e && DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), DAE.DIV(__), e2), DAE.BINARY(e3, DAE.DIV(__), e4), false, false)  => begin
                      @match true = Expression.expEqual(e1, e3)
                      res = DAE.BINARY(e, DAE.MUL(ty), DAE.BINARY(Expression.inverseFactors(e2), DAE.ADD(ty), Expression.inverseFactors(e4)))
                    res
                  end

                  (_, op1, DAE.BINARY(e1, oper && DAE.MUL(_), DAE.BINARY(e2, op2, e3)), DAE.BINARY(e4, DAE.MUL(_), DAE.BINARY(e5, op3, e6)), false, false)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.isMulOrDiv(op2)
                      @match true = Expression.isMulOrDiv(op3)
                      @match true = Expression.expEqual(e2, e5)
                    DAE.BINARY(e5, oper, DAE.BINARY(DAE.BINARY(e1, op2, e3), op1, DAE.BINARY(e4, op3, e6)))
                  end

                  (_, op1, DAE.BINARY(e1, oper && DAE.MUL(_), e2), DAE.BINARY(e4, DAE.MUL(_), DAE.BINARY(e5, op3, e6)), false, false)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.isMulOrDiv(op3)
                      @match true = Expression.expEqual(e2, e5)
                    DAE.BINARY(e5, oper, DAE.BINARY(e1, op1, DAE.BINARY(e4, op3, e6)))
                  end

                  (_, op1, DAE.BINARY(e1, oper && DAE.MUL(_), DAE.BINARY(e2, op2, e3)), DAE.BINARY(e4, DAE.MUL(__), e5), false, false)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.isMulOrDiv(op2)
                      if Expression.expEqual(e2, e5)
                        outExp = DAE.BINARY(e5, oper, DAE.BINARY(DAE.BINARY(e1, op2, e3), op1, e4))
                      else
                        if Expression.expEqual(e2, e4)
                          outExp = DAE.BINARY(e4, oper, DAE.BINARY(DAE.BINARY(e1, op2, e3), op1, e5))
                        else
                          fail()
                        end
                      end
                    outExp
                  end

                  (_, op1, DAE.BINARY(DAE.BINARY(e1, oper && DAE.MUL(_), e2), op2, e3), DAE.BINARY(e4, DAE.MUL(__), e5), false, false)  => begin
                      @match true = Expression.isAddOrSub(op1)
                      @match true = Expression.isMulOrDiv(op2)
                      if Expression.expEqual(e2, e5)
                        outExp = DAE.BINARY(e5, oper, DAE.BINARY(DAE.BINARY(e1, op2, e3), op1, e4))
                      else
                        if Expression.expEqual(e2, e4)
                          outExp = DAE.BINARY(e4, oper, DAE.BINARY(DAE.BINARY(e1, op2, e3), op1, e5))
                        else
                          fail()
                        end
                      end
                    outExp
                  end

                  (_, DAE.POW(__), e1, e2, _, true)  => begin
                      @match (@match _cons(_, _cons(_, _cons(_, _))) = exp_lst) = Expression.factors(e1)
                      @match true = ListUtil.exist(exp_lst, Expression.isConstValue)
                      exp_lst_1 = simplifyBinaryDistributePow(exp_lst, e2)
                    Expression.makeProductLst(exp_lst_1)
                  end

                  (_, DAE.POW(__), DAE.BINARY(e1, DAE.POW(__), e2), e3, _, _)  => begin
                    DAE.BINARY(e1, DAE.POW(DAE.T_REAL_DEFAULT), DAE.BINARY(e2, DAE.MUL(DAE.T_REAL_DEFAULT), e3))
                  end

                  (_, DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("sin"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("cos"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                    Expression.makePureBuiltinCall("tan", list(e1), ty)
                  end

                  (_, op2 && DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("tan"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("sin"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                      e3 = DAE.RCONST(1.0)
                      e4 = Expression.makePureBuiltinCall("cos", list(e2), ty)
                      e = DAE.BINARY(e3, op2, e4)
                    e
                  end

                  (_, DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("cos"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("tan"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                      e = Expression.makePureBuiltinCall("sin", list(e2), ty)
                    e
                  end

                  (_, op2 && DAE.DIV(ty), e1, DAE.CALL(path = Absyn.IDENT("tan"), expLst = e2 <|  nil()), _, _)  => begin
                      e3 = Expression.makePureBuiltinCall("sin", list(e2), ty)
                      e4 = Expression.makePureBuiltinCall("cos", list(e2), ty)
                      e = DAE.BINARY(e4, op2, e3)
                    DAE.BINARY(e1, DAE.MUL(ty), e)
                  end

                  (_, DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("sinh"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("cosh"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                    Expression.makePureBuiltinCall("tanh", list(e1), ty)
                  end

                  (_, op2 && DAE.DIV(ty), e1, DAE.CALL(path = Absyn.IDENT("tanh"), expLst = e2 <|  nil()), _, _)  => begin
                      e3 = Expression.makePureBuiltinCall("sinh", list(e2), ty)
                      e4 = Expression.makePureBuiltinCall("cosh", list(e2), ty)
                      e = DAE.BINARY(e4, op2, e3)
                    DAE.BINARY(e1, DAE.MUL(ty), e)
                  end

                  (_, op2 && DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("tanh"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("sinh"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                      e3 = DAE.RCONST(1.0)
                      e4 = Expression.makePureBuiltinCall("cosh", list(e2), ty)
                      e = DAE.BINARY(e3, op2, e4)
                    e
                  end

                  (_, DAE.DIV(ty), DAE.CALL(path = Absyn.IDENT("cosh"), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT("tanh"), expLst = e2 <|  nil()), _, _)  => begin
                      @match true = Expression.expEqual(e1, e2)
                      e = Expression.makePureBuiltinCall("sinh", list(e2), ty)
                    e
                  end

                  (_, DAE.MUL(ty = ty), e1, DAE.UNARY(operator = DAE.UMINUS(__), exp = e2), _, _)  => begin
                      e1_1 = DAE.UNARY(DAE.UMINUS(ty), e1)
                    DAE.BINARY(e1_1, DAE.MUL(ty), e2)
                  end

                  (_, DAE.ADD(__), DAE.RANGE(ty = ty, start = e1, step = oexp, stop = e2), _, _, _)  => begin
                      e1 = simplifyBinary(DAE.BINARY(e1, inOperator2, rhs), inOperator2, e1, rhs)
                      e2 = simplifyBinary(DAE.BINARY(e2, inOperator2, rhs), inOperator2, e2, rhs)
                    DAE.RANGE(ty, e1, oexp, e2)
                  end

                  (_, DAE.ADD(__), _, DAE.RANGE(ty = ty, start = e1, step = oexp, stop = e2), _, _)  => begin
                      e1 = simplifyBinary(DAE.BINARY(lhs, inOperator2, e1), inOperator2, lhs, e1)
                      e2 = simplifyBinary(DAE.BINARY(lhs, inOperator2, e1), inOperator2, lhs, e2)
                    DAE.RANGE(ty, e1, oexp, e2)
                  end

                  (_, DAE.SUB(__), DAE.RANGE(ty = ty, start = e1, step = oexp, stop = e2), _, _, _)  => begin
                      e1 = simplifyBinary(DAE.BINARY(e1, inOperator2, rhs), inOperator2, e1, rhs)
                      e2 = simplifyBinary(DAE.BINARY(e2, inOperator2, rhs), inOperator2, e2, rhs)
                    DAE.RANGE(ty, e1, oexp, e2)
                  end

                  (_, DAE.SUB(__), _, DAE.RANGE(ty = ty, start = e1, step = oexp, stop = e2), _, _)  => begin
                      e1 = simplifyBinary(DAE.BINARY(lhs, inOperator2, e1), inOperator2, lhs, e1)
                      e2 = simplifyBinary(DAE.BINARY(lhs, inOperator2, e1), inOperator2, lhs, e2)
                    DAE.RANGE(ty, e1, oexp, e2)
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  (a1a2...an)^e2 => a1^e2a2^e2..an^e2
               =#
               #= /*
                       * Only do this for constant exponent and any constant expression.
                       * Exponentation is very expensive compared to the inner expressions.
                       */ =#
               #=  (e1^e2)^e3 => e1^(e2*e3)
               =#
               #=  sin(e)/cos(e) => tan(e)
               =#
               #=  tan(e2)/sin(e2) => 1.0/cos(e2)
               =#
               #=  cos(e2)/tan(e2) => sin(e2)
               =#
               #=  e1/tan(e2) => e1*cos(e2)/sin(e2)
               =#
               #=  sinh(e)/cosh(e) => tan(e)
               =#
               #=  e1/tanh(e2) => e1*cos(e2)/sin(e2)
               =#
               #=  tanh(e2)/sinh(e2) => 1.0/cosh(e2)
               =#
               #=  cosh(e2)/tanh(e2) => sinh(e2)
               =#
               #=  e1  -e2 => -e1  e2
               =#
               #=  Note: This rule is *not* commutative
               =#
          outExp
        end

         #= This function simplifies a binary expression of two binary expressions:
        (e1 lhsOp e2) mainOp (e3 rhsOp e4)
         =#
        function simplifyTwoBinaryExpressions(e1::DAE.Exp, lhsOperator::Operator, e2::DAE.Exp, mainOperator::Operator, e3::DAE.Exp, rhsOperator::Operator, e4::DAE.Exp, expEqual_e1_e3::Bool, expEqual_e1_e4::Bool, expEqual_e2_e3::Bool, expEqual_e2_e4::Bool, isConst_e1::Bool, isConst_e2::Bool, isConst_e3::Bool, operatorEqualLhsRhs::Bool) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1_1::DAE.Exp
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e_3::DAE.Exp
                  local e_4::DAE.Exp
                  local e_5::DAE.Exp
                  local e_6::DAE.Exp
                  local res::DAE.Exp
                  local one::DAE.Exp
                  local oper::Operator
                  local op1::Operator
                  local op2::Operator
                  local op3::Operator
                  local op::Operator
                  local ty::Type
                  local ty2::Type
                  local tp::Type
                  local tp2::Type
                  local ty1::Type
                  local exp_lst::List{DAE.Exp}
                  local exp_lst_1::List{DAE.Exp}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local b::Bool
                  local r::ModelicaReal
                  local oexp::Option{DAE.Exp}
                   #=  (e*e1) + (e*e2) => e*(e1+e2)
                   =#
                @match (e1, lhsOperator, e2, mainOperator, e3, rhsOperator, e4, expEqual_e1_e3, expEqual_e1_e4, expEqual_e2_e3, expEqual_e2_e4, isConst_e1, isConst_e2, isConst_e3, operatorEqualLhsRhs) begin
                  (_, op2 && DAE.MUL(__), _, op1 && DAE.ADD(__), _, DAE.MUL(__), _, true, _, _, _, _, _, _, _)  => begin
                    DAE.BINARY(e1, op2, DAE.BINARY(e2, op1, e4))
                  end

                  (_, op2 && DAE.MUL(__), _, op1 && DAE.ADD(__), _, DAE.MUL(__), _, _, true, _, _, _, _, _, _)  => begin
                    DAE.BINARY(e1, op2, DAE.BINARY(e2, op1, e3))
                  end

                  (_, op2 && DAE.MUL(__), _, op1 && DAE.ADD(__), _, DAE.MUL(__), _, _, _, true, _, _, _, _, _)  => begin
                    DAE.BINARY(e2, op2, DAE.BINARY(e1, op1, e4))
                  end

                  (_, op2 && DAE.MUL(__), _, op1 && DAE.ADD(__), _, DAE.MUL(__), _, _, _, _, true, _, _, _, _)  => begin
                    DAE.BINARY(e2, op2, DAE.BINARY(e1, op1, e3))
                  end

                  (_, DAE.POW(__), _, DAE.MUL(__), _, DAE.POW(__), _, _, _, _, true, _, _, _, _)  => begin
                      res = DAE.BINARY(DAE.BINARY(e1, mainOperator, e3), lhsOperator, e2)
                    res
                  end

                  (_, DAE.POW(__), _, DAE.DIV(__), _, DAE.POW(__), _, _, _, _, true, _, _, _, _)  => begin
                      res = DAE.BINARY(DAE.BINARY(e1, mainOperator, e3), lhsOperator, e2)
                    res
                  end

                  (_, DAE.POW(__), _, DAE.MUL(__), _, DAE.POW(__), _, true, _, _, _, _, _, _, _)  => begin
                      res = Expression.expAdd(e2, e4)
                      res = Expression.expPow(e1, res)
                    res
                  end

                  (_, DAE.POW(__), _, DAE.DIV(__), _, DAE.POW(__), _, true, _, _, _, _, _, _, _)  => begin
                      res = Expression.expSub(e2, e4)
                      res = Expression.expPow(e1, res)
                    res
                  end

                  (_, op2, _, op1, _, _, _, _, _, _, true, _, false, _, true) where (Expression.isAddOrSub(op1) && Expression.isMulOrDiv(op2))  => begin
                    DAE.BINARY(DAE.BINARY(e1, op1, e3), op2, e4)
                  end

                  (_, op && DAE.MUL(ty), _, op1, _, DAE.DIV(_), _, true, _, _, _, false, _, _, _) where (Expression.isAddOrSub(op1))  => begin
                      one = Expression.makeConstOne(ty)
                      e = Expression.makeDiv(one, e4)
                    DAE.BINARY(DAE.BINARY(e2, op1, e), op, e1)
                  end

                  (_, DAE.DIV(ty), _, op1, _, DAE.MUL(_), _, true, _, _, _, false, _, _, _) where (Expression.isAddOrSub(op1))  => begin
                      one = Expression.makeConstOne(ty)
                      e = Expression.makeDiv(one, e2)
                    DAE.BINARY(DAE.BINARY(e, op1, e4), DAE.MUL(ty), e1)
                  end

                  (e1_1, op2, e_3, op1, e, _, _, _, _, _, true, _, false, _, true) where (Expression.isAddOrSub(op1) && Expression.isMulOrDiv(op2))  => begin
                      res = DAE.BINARY(e1_1, op1, e)
                    DAE.BINARY(res, op2, e_3)
                  end

                  (DAE.BINARY(e_1, op2, e_2), op && DAE.MUL(ty), e_3, op1, e, op3, e_6, _, _, _, _, _, _, _, _) where (! Expression.isConstValue(e_2) && Expression.expEqual(e_2, e_6) && Expression.operatorEqual(op2, op3) && Expression.isAddOrSub(op1) && Expression.isMulOrDiv(op2))  => begin
                      e1_1 = DAE.BINARY(e_1, op, e_3)
                      res = DAE.BINARY(e1_1, op1, e)
                    DAE.BINARY(res, op2, e_2)
                  end

                  (DAE.BINARY(e_1, op2, e_2), op && DAE.MUL(ty), e_3, op1, DAE.BINARY(e_4, op3, e_5), DAE.MUL(_), e_6, _, _, _, _, _, _, _, _) where (! Expression.isConstValue(e_2) && Expression.expEqual(e_2, e_5) && Expression.operatorEqual(op2, op3) && Expression.isAddOrSub(op1) && Expression.isMulOrDiv(op2))  => begin
                      e1_1 = DAE.BINARY(e_1, op, e_3)
                      e = DAE.BINARY(e_4, op, e_6)
                      res = DAE.BINARY(e1_1, op1, e)
                    DAE.BINARY(res, op2, e_2)
                  end

                  (e_1, op2, e_3, op1, DAE.BINARY(e_4, op3, e_5), op && DAE.MUL(ty), e_6, _, _, _, _, _, false, _, _) where (Expression.expEqual(e_3, e_5) && Expression.operatorEqual(op2, op3) && Expression.isAddOrSub(op1) && Expression.isMulOrDiv(op2))  => begin
                      e = DAE.BINARY(e_4, op, e_6)
                      res = DAE.BINARY(e_1, op1, e)
                    DAE.BINARY(res, op2, e_3)
                  end

                  (_, DAE.MUL(__), _, DAE.SUB(__), _, DAE.MUL(__), _, true, _, _, _, _, _, _, _)  => begin
                    DAE.BINARY(e1, lhsOperator, DAE.BINARY(e2, mainOperator, e4))
                  end

                  (_, DAE.MUL(__), _, DAE.SUB(__), _, DAE.MUL(__), _, _, true, _, _, _, _, _, _)  => begin
                    DAE.BINARY(e1, lhsOperator, DAE.BINARY(e2, mainOperator, e3))
                  end
                end
              end
               #= /*e1==e3*/ =#
               #=  (e*e1) + (e2*e) = e*(e1+e2)
               =#
               #= /*e1==e4*/ =#
               #=  (e1*e) + (e*e4) = e*(e1+e2)
               =#
               #= /*e2==e3*/ =#
               #=  (e1*e) + (e*e4) = e*(e1+e2)
               =#
               #= /*e2==e4*/ =#
               #=  a^e*b^e => (a*b)^e
               =#
               #= /*e2==e4*/ =#
               #=  a^e/b^e => (a/b)^e
               =#
               #= /*e2==e4*/ =#
               #=  a^e1*a^e2 => a^(e1+e2)
               =#
               #= /*e1==e3*/ =#
               #=  a^e1/a^e2 => a^(e1-e2)
               =#
               #= /*e1==e3*/ =#
               #=  (e1 op2 e2) op1 (e3 op3 e4) => (e1 op1 e3) op2 e2
               =#
               #=  e2 = e4; op2=op3 \\in {*, /}; op1 \\in {+, -}
               =#
               #= /*e2==e4*/ =#
               #= /*isConst(e2)*/ =#
               #= /*op2==op3*/ =#
               #=  (e1 * e2) op1 (e3 / e4) => (e1 * e2) op1 (e1 * (1/ e4) ) => e1*(e2 op1 (1/ e4))
               =#
               #=  e1 = e3; op1 \\in {+, -}
               =#
               #= /*e1==e3*/ =#
               #= /*isConst(e1)*/ =#
               #=  (e1 / e2) op1 (e3 * e4) => (e1 * (1/e2)) op1 (e1 * e4 ) => e1*(1/e2 op1 e4)
               =#
               #=  e1 = e3; op1 \\in {+, -}
               =#
               #= /*e1==e3*/ =#
               #= /*isConst(e1)*/ =#
               #=  [x op2 e] op1 [y op2 e] => (x op1 y) op2 e
               =#
               #=  op2 \\in {*, /}; op1 \\in {+, -}
               =#
               #= /*e2==e4==e_3==e_5*/ =#
               #= /*isConst(e2==e_3)*/ =#
               #= /*op2==op3*/ =#
               #=  [(e1 op2 e) * e3] op1 [e4 op2 e] => (e1*e3 op1 e4) op2 e
               =#
               #=  op2 \\in {*, /}; op1 \\in {+, -}
               =#
               #=  [(e1 op2 e) * e3] op1 [(e4 op2 e) * e6] => (e1*e3 op1 e4*e6) op2 e
               =#
               #=  op2 \\in {*, /}; op1 \\in {+, -}
               =#
               #=  [e1 op2 e] op1 [(e4 op2 e) * e6] => (e1 op1 e4*e6) op2 e
               =#
               #=  op2 \\in {*, /}; op1 \\in {+, -}
               =#
               #= /*isConst(e2==e_3)*/ =#
               #=  (e*e1) - (e*e2) => e*(e1-e2)
               =#
               #= /*e1==e3*/ =#
               #=  (e*e1) - (e2*e) => e*(e1-e2)
               =#
               #= /*e1==e4*/ =#
          outExp
        end

         #= This function simplifies logical binary expressions. =#
        function simplifyLBinary(origExp::DAE.Exp, inOperator2::Operator, inExp3::DAE.Exp #= Note: already simplified =#, inExp4::DAE.Exp #= Note: aldready simplified =#) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local b::Bool
                   #=  fix for PNLib where \"{} and not {}\" is evaluated
                   =#
                @match (origExp, inOperator2, inExp3, inExp4) begin
                  (_, _, DAE.ARRAY(array =  nil()), _)  => begin
                    origExp
                  end

                  (_, _, _, DAE.ARRAY(array =  nil()))  => begin
                    origExp
                  end

                  (_, DAE.AND(DAE.T_BOOL(__)), e1, DAE.LUNARY(DAE.NOT(_), e2)) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BCONST(false)
                  end

                  (_, DAE.AND(DAE.T_BOOL(__)), DAE.LUNARY(DAE.NOT(_), e1), e2) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BCONST(false)
                  end

                  (_, DAE.OR(DAE.T_BOOL(__)), e1, DAE.LUNARY(DAE.NOT(_), e2)) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BCONST(true)
                  end

                  (_, DAE.OR(DAE.T_BOOL(__)), DAE.LUNARY(DAE.NOT(_), e1), e2) where (Expression.expEqual(e1, e2))  => begin
                    DAE.BCONST(true)
                  end

                  (_, DAE.AND(_), e1 && DAE.BCONST(b), e2)  => begin
                    if b
                          e2
                        else
                          e1
                        end
                  end

                  (_, DAE.AND(_), e1, e2 && DAE.BCONST(b))  => begin
                    if b
                          e1
                        else
                          e2
                        end
                  end

                  (_, DAE.OR(_), e1 && DAE.BCONST(b), e2)  => begin
                    if b
                          e1
                        else
                          e2
                        end
                  end

                  (_, DAE.OR(_), e1, e2 && DAE.BCONST(b))  => begin
                    if b
                          e2
                        else
                          e1
                        end
                  end

                  (_, DAE.AND(_), e1, e2) where (Expression.expEqual(e1, e2))  => begin
                    e1
                  end

                  (_, DAE.OR(_), e1, e2) where (Expression.expEqual(e1, e2))  => begin
                    e1
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  a AND not a -> false
               =#
               #=  a OR not a -> true
               =#
               #=  true AND e => e
               =#
               #=  false OR e => e
               =#
               #=  a AND a -> a
               =#
               #=  a OR a -> a
               =#
          outExp
        end

         #= This function simplifies logical binary expressions. =#
        function simplifyRelation(origExp::DAE.Exp, inOperator2::Operator, inExp3::DAE.Exp #= Note: already simplified =#, inExp4::DAE.Exp #= Note: aldready simplified =#, index::ModelicaInteger, optionExpisASUB::Option{<:Tuple{<:DAE.Exp, ModelicaInteger, ModelicaInteger}}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1_1::DAE.Exp
                  local e3::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e4::DAE.Exp
                  local e5::DAE.Exp
                  local e6::DAE.Exp
                  local res::DAE.Exp
                  local one::DAE.Exp
                  local oper::Operator
                  local op1::Operator
                  local op2::Operator
                  local op3::Operator
                  local ty::Type
                  local ty2::Type
                  local tp::Type
                  local tp2::Type
                  local ty1::Type
                  local exp_lst::List{DAE.Exp}
                  local exp_lst_1::List{DAE.Exp}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local b::Bool
                  local b1::Bool
                  local r::ModelicaReal
                  local oexp::Option{DAE.Exp}
                   #=  constants
                   =#
                @matchcontinue (origExp, inOperator2, inExp3, inExp4) begin
                  (_, oper, e1, e2)  => begin
                      @match true = Expression.isConstValue(e1)
                      @match true = Expression.isConstValue(e2)
                      b = simplifyRelationConst(oper, e1, e2)
                    DAE.BCONST(b)
                  end

                  (_, DAE.EQUAL(_), DAE.CREF(cr1, _), DAE.CREF(cr2, _))  => begin
                      @match true = CrefForHashTable.crefEqual(cr1, cr2)
                    DAE.BCONST(true)
                  end

                  (_, DAE.NEQUAL(_), DAE.CREF(cr1, _), DAE.CREF(cr2, _))  => begin
                      @match true = CrefForHashTable.crefEqual(cr1, cr2)
                    DAE.BCONST(false)
                  end

                  (_, DAE.GREATEREQ(__), _, _)  => begin
                    simplifyRelation2(origExp, inOperator2, inExp3, inExp4, index, optionExpisASUB, Expression.isPositiveOrZero)
                  end

                  (_, DAE.GREATER(__), _, _)  => begin
                    simplifyRelation2(origExp, inOperator2, inExp3, inExp4, index, optionExpisASUB, Expression.isPositiveOrZero)
                  end

                  (_, DAE.LESSEQ(__), _, _)  => begin
                    simplifyRelation2(origExp, inOperator2, inExp4, inExp3, index, optionExpisASUB, Expression.isPositiveOrZero)
                  end

                  (_, DAE.LESS(__), _, _)  => begin
                    simplifyRelation2(origExp, inOperator2, inExp4, inExp3, index, optionExpisASUB, Expression.isPositiveOrZero)
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  relation: cr1 == cr2, where cr1 and cr2 are the same
               =#
               #=  relation: cr1 <> cr2 . where cr1 and cr2 are the same
               =#
               #=  a >= b
               =#
               #=  a > b
               =#
               #=  a <= b
               =#
               #=  a < b
               =#
          outExp
        end

         #= This function simplifies logical binary expressions. =#
        function simplifyRelation2(origExp::DAE.Exp, inOp::Operator, lhs::DAE.Exp #= Note: already simplified =#, rhs::DAE.Exp #= Note: aldready simplified =#, index::ModelicaInteger, optionExpisASUB::Option{<:Tuple{<:DAE.Exp, ModelicaInteger, ModelicaInteger}}, isPositive::Fun) ::DAE.Exp
              local oExp::DAE.Exp

              local b::Bool
              local tp::Type

              oExp = Expression.expSub(lhs, rhs)
              (oExp, b) = simplify(oExp)
              if Expression.isGreatereqOrLesseq(inOp) && isPositive(oExp)
                oExp = DAE.BCONST(true)
              else
                if Expression.isGreatereqOrLesseq(inOp)
                  oExp = origExp
                else
                  oExp = Expression.negate(oExp)
                  (oExp, _) = simplify(oExp)
                  oExp = if isPositive(oExp)
                        DAE.BCONST(false)
                      else
                        origExp
                      end
                end
              end
               #= /*
                elseif b and not (Expression.isConstValue(rhs) or Expression.isConstValue(lhs)) then
                  tp := Expression.typeOf(oExp);
                  oExp := if Expression.isLesseqOrLess(inOp) then
                               DAE.RELATION(Expression.makeConstZero(tp), inOp, oExp, index,optionExpisASUB)
                          else DAE.RELATION(oExp, inOp,Expression.makeConstZero(tp),index,optionExpisASUB);
              */ =#
          oExp
        end

         #= author: PA
          Distributes the pow operator over a list of expressions.
          Removes 1^pow_e
          ({e1,e2,..,en} , pow_e) =>  {e1^pow_e, e2^pow_e,..,en^pow_e} =#
        function simplifyBinaryDistributePow(inExpLst::List{<:DAE.Exp}, inExp::DAE.Exp) ::List{DAE.Exp}
              local outExpLst::List{DAE.Exp}

              outExpLst = list(DAE.BINARY(e, DAE.POW(Expression.typeOf(e)), inExp) for e in inExpLst if ! Expression.isConstOne(e))
          outExpLst
        end

         #= Simplifies unary expressions. =#
        function simplifyUnary(origExp::DAE.Exp, inOperator2::Operator, inExp3::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local ty::Type
                  local ty1::Type
                  local e1::DAE.Exp
                  local e_1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local i_1::ModelicaInteger
                  local i::ModelicaInteger
                  local r_1::ModelicaReal
                  local r::ModelicaReal
                  local b1::Bool
                  local attr::DAE.CallAttributes
                  local expl::List{DAE.Exp}
                  local mat::List{List{DAE.Exp}}
                  local op::Operator
                  local op2::Operator
                  local path::Absyn.Path
                   #=  not true => false, not false => true
                   =#
                @matchcontinue (origExp, inOperator2, inExp3) begin
                  (_, DAE.NOT(__), e1)  => begin
                      b1 = Expression.toBool(e1)
                      b1 = ! b1
                    DAE.BCONST(b1)
                  end

                  (_, DAE.NOT(_), DAE.LUNARY(DAE.NOT(_), e1))  => begin
                    e1
                  end

                  (_, DAE.UMINUS(__), DAE.ICONST(integer = i))  => begin
                      i_1 = intNeg(i)
                    DAE.ICONST(i_1)
                  end

                  (_, DAE.UMINUS(__), DAE.RCONST(real = r))  => begin
                      r_1 = realNeg(r)
                    DAE.RCONST(r_1)
                  end

                  (_, op2 && DAE.UMINUS(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.MUL(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(DAE.UNARY(op2, e1), op, e2)
                  end

                  (_, op2 && DAE.UMINUS_ARR(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.MUL_ARR(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(DAE.UNARY(op2, e1), op, e2)
                  end

                  (_, DAE.UMINUS(__), e1) where (Expression.isZero(e1))  => begin
                    e1
                  end

                  (_, DAE.UMINUS_ARR(__), e1) where (Expression.isZero(e1))  => begin
                    e1
                  end

                  (_, DAE.UMINUS(__), DAE.BINARY(exp1 = e1, operator = op && DAE.SUB(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(e2, op, e1)
                  end

                  (_, DAE.UMINUS_ARR(__), DAE.BINARY(exp1 = e1, operator = op && DAE.SUB_ARR(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(e2, op, e1)
                  end

                  (_, op2 && DAE.UMINUS(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.ADD(ty = ty1), exp2 = e2))  => begin
                      @match (e_1, true) = simplify1(DAE.BINARY(DAE.UNARY(op2, e1), op, DAE.UNARY(op2, e2)))
                    e_1
                  end

                  (_, op2 && DAE.UMINUS_ARR(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.ADD_ARR(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(DAE.UNARY(op2, e1), op, DAE.UNARY(op2, e2))
                  end

                  (_, op2 && DAE.UMINUS(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.DIV(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(DAE.UNARY(op2, e1), op, e2)
                  end

                  (_, op2 && DAE.UMINUS_ARR(ty = ty), DAE.BINARY(exp1 = e1, operator = op && DAE.DIV_ARR(ty = ty1), exp2 = e2))  => begin
                    DAE.BINARY(DAE.UNARY(op2, e1), op, e2)
                  end

                  (_, DAE.UMINUS(__), DAE.UNARY(operator = DAE.UMINUS(__), exp = e1))  => begin
                    e1
                  end

                  (_, DAE.UMINUS_ARR(__), DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e1))  => begin
                    e1
                  end

                  (_, DAE.UMINUS(__), DAE.CALL(path = path && Absyn.IDENT("semiLinear"), expLst = DAE.UNARY(exp = e1) <| e2 <| e3 <|  nil(), attr = attr))  => begin
                    DAE.CALL(path, list(e1, e3, e2), attr)
                  end

                  (_, DAE.UMINUS_ARR(__), DAE.ARRAY(ty1, b1, expl))  => begin
                      expl = ListUtil.map(expl, Expression.negate)
                    DAE.ARRAY(ty1, b1, expl)
                  end

                  (_, DAE.UMINUS_ARR(__), DAE.MATRIX(ty1, i, mat))  => begin
                      mat = ListUtil.mapList(mat, Expression.negate)
                    DAE.MATRIX(ty1, i, mat)
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  not(not(exp)) -> exp
               =#
               #=  -x => 0 - x
               =#
               #=  -x => 0.0 - x
               =#
               #=  -(a * b) => (-a) * b
               =#
               #=  -(a*b) => (-a)*b
               =#
               #=  -0 => 0
               =#
               #=   -(a-b) => b - a
               =#
               #=  -(a + b) => -b - a
               =#
               #=  -( a / b) => (-a) / b
               =#
               #=  --a => a
               =#
               #= /* --a => a */ =#
               #= /* --a => a */ =#
               #=  -semiLinear(-x,sb,sa) = semiLinear(x,sa,sb)
               =#
          outExp
        end

         #= Help function to simplifyVectorScalar,
        handles MATRIX expressions =#
        function simplifyVectorScalarMatrix(imexpl::List{<:List{<:DAE.Exp}}, op::Operator, s1::DAE.Exp, arrayScalar::Bool #= if true, array op scalar, otherwise scalar op array =#) ::List{List{DAE.Exp}}
              local outExp::List{List{DAE.Exp}}

              outExp = if arrayScalar
                    list(list(DAE.BINARY(e, op, s1) for e in row) for row in imexpl)
                  else
                    list(list(DAE.BINARY(s1, op, e) for e in row) for row in imexpl)
                  end
          outExp
        end

         #= Helper relation to simplifyBinarySortConstants =#
        function simplifyBinarySortConstantsMul(inExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              local e_lst::List{DAE.Exp}
              local e_lst_1::List{DAE.Exp}
              local const_es1::List{DAE.Exp}
              local const_es1_1::List{DAE.Exp}
              local notconst_es1::List{DAE.Exp}
              local res1::DAE.Exp
              local res2::DAE.Exp

              e_lst = Expression.factors(inExp)
               #= e_lst_1 := List.map(e_lst,simplify2);  simplify2 for recursive
               =#
              (const_es1, notconst_es1) = ListUtil.splitOnTrue(e_lst, Expression.isConst)
              if ! listEmpty(const_es1)
                res1 = simplifyBinaryMulConstants(const_es1)
                (res1, _) = simplify1(res1)
                res2 = Expression.makeProductLst(notconst_es1)
                outExp = Expression.expMul(res1, res2)
              else
                outExp = inExp
              end
               #=  simplify1 for basic constant evaluation.
               =#
               #=  Cannot simplify this, if const_es1_1 empty => infinite recursion.
               =#
          outExp
        end

         #= returns 0.0 or an array filled with 0.0 if the input is Real, Integer or an array of Real/Integer =#
        function simplifyBuiltinConstantDer(inExp::DAE.Exp #= assumes already simplified constant expression =#) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local dims::DAE.Dimensions
                @match inExp begin
                  DAE.RCONST(_)  => begin
                    DAE.RCONST(0.0)
                  end

                  DAE.ICONST(_)  => begin
                    DAE.RCONST(0.0)
                  end

                  DAE.ARRAY(ty = DAE.T_ARRAY(ty = DAE.T_REAL(__), dims = dims))  => begin
                      (e, _) = Expression.makeZeroExpression(dims)
                    e
                  end

                  DAE.ARRAY(ty = DAE.T_ARRAY(ty = DAE.T_INTEGER(__), dims = dims))  => begin
                      (e, _) = Expression.makeZeroExpression(dims)
                    e
                  end
                end
              end
          outExp
        end

         #= Function: removeOperatorDimension
        Helper function for simplifyVectorBinary, removes an dimension from the operator.
         =#
        function removeOperatorDimension(inop::Operator) ::Operator
              local outop::Operator

              outop = begin
                  local ty1::Type
                  local ty2::Type
                  local b::Bool
                  local op::Operator
                @match inop begin
                  DAE.ADD_ARR(ty = ty1)  => begin
                      ty2 = Expression.unliftArray(ty1)
                      b = DAEUtilMinimal.expTypeArray(ty2)
                      op = if b
                            DAE.ADD_ARR(ty2)
                          else
                            DAE.ADD(ty2)
                          end
                    op
                  end

                  DAE.SUB_ARR(ty = ty1)  => begin
                      ty2 = Expression.unliftArray(ty1)
                      b = DAEUtilMinimal.expTypeArray(ty2)
                      op = if b
                            DAE.SUB_ARR(ty2)
                          else
                            DAE.SUB(ty2)
                          end
                    op
                  end

                  DAE.DIV_ARR(ty = ty1)  => begin
                      ty2 = Expression.unliftArray(ty1)
                      b = DAEUtilMinimal.expTypeArray(ty2)
                      op = if b
                            DAE.DIV_ARR(ty2)
                          else
                            DAE.DIV(ty2)
                          end
                    op
                  end

                  DAE.MUL_ARR(ty = ty1)  => begin
                      ty2 = Expression.unliftArray(ty1)
                      b = DAEUtilMinimal.expTypeArray(ty2)
                      op = if b
                            DAE.MUL_ARR(ty2)
                          else
                            DAE.MUL(ty2)
                          end
                    op
                  end

                  DAE.POW_ARR2(ty = ty1)  => begin
                      ty2 = Expression.unliftArray(ty1)
                      b = DAEUtilMinimal.expTypeArray(ty2)
                      op = if b
                            DAE.POW_ARR2(ty2)
                          else
                            DAE.POW(ty2)
                          end
                    op
                  end
                end
              end
          outop
        end

         #= This function evaluates a Boolean range expression. =#
        function simplifyRangeBool(inStart::Bool, inStop::Bool) ::List{Bool}
              local outRange::List{Bool}

              outRange = if inStart
                    if inStop
                          list(true)
                        else
                          nil
                        end
                  else
                    if inStop
                          list(false, true)
                        else
                          list(false)
                        end
                  end
          outRange
        end

         #= This function evaluates an Integer range expression. =#
        function simplifyRange(inStart::ModelicaInteger, inStep::ModelicaInteger, inStop::ModelicaInteger) ::List{ModelicaInteger}
              local outValues::List{ModelicaInteger}

              outValues = ListUtil.intRange3(inStart, inStep, inStop)
          outValues
        end

         #= This function evaluates a Real range expression. =#
        function simplifyRangeReal(inStart::ModelicaReal, inStep::ModelicaReal, inStop::ModelicaReal) ::List{ModelicaReal}
              local outValues::List{ModelicaReal}

              outValues = begin
                  local error_str::String
                  local steps::ModelicaInteger
                @matchcontinue (inStart, inStep, inStop) begin
                  (_, _, _)  => begin
                      @match true = realAbs(inStep) <= 1e-14
                      error_str = stringDelimitList(ListUtil.map(list(inStart, inStep, inStop), realString), ":")
                      Error.addMessage(Error.ZERO_STEP_IN_ARRAY_CONSTRUCTOR, list(error_str))
                    fail()
                  end

                  (_, _, _)  => begin
                      equality(inStart, inStop)
                    list(inStart)
                  end

                  _  => begin
                        steps = Util.realRangeSize(inStart, inStep, inStop) - 1
                      simplifyRangeReal2(inStart, inStep, steps, nil)
                  end
                end
              end
          outValues
        end

         #= Helper function to simplifyRangeReal. =#
        function simplifyRangeReal2(inStart::ModelicaReal, inStep::ModelicaReal, inSteps::ModelicaInteger, inValues::List{<:ModelicaReal}) ::List{ModelicaReal}
              local outValues::List{ModelicaReal}

              outValues = begin
                  local next::ModelicaReal
                  local vals::List{ModelicaReal}
                @match (inStart, inStep, inSteps, inValues) begin
                  (_, _, +1, _)  => begin
                    inValues
                  end

                  _  => begin
                        next = inStart + inStep * intReal(inSteps)
                        vals = _cons(next, inValues)
                      simplifyRangeReal2(inStart, inStep, inSteps - 1, vals)
                  end
                end
              end
          outValues
        end

        function simplifyReduction(inReduction::DAE.Exp) ::DAE.Exp
              local outValue::DAE.Exp

              outValue = begin
                  local expr::DAE.Exp
                  local cref::DAE.Exp
                  local range::DAE.Exp
                  local foldExpr::DAE.Exp
                  local foldExpr2::DAE.Exp
                  local iter_name::DAE.Ident
                  local values::List{DAE.Exp}
                  local defaultValue::Option{Values.Value}
                  local v::Values.Value
                  local str::String
                  local foldExp::Option{DAE.Exp}
                  local ty::DAE.Type
                  local ty1::DAE.Type
                  local ety::DAE.Type
                  local iter::DAE.ReductionIterator
                  local iterators::List{DAE.ReductionIterator}
                  local foldName::String
                  local resultName::String
                  local foldName2::String
                  local resultName2::String
                  local path::Absyn.Path
                @matchcontinue inReduction begin
                  DAE.REDUCTION(iterators = iterators, reductionInfo = DAE.REDUCTIONINFO(defaultValue = SOME(v)))  => begin
                      @match true = hasZeroLengthIterator(iterators)
                      expr = ValuesUtil.valueExp(v)
                    expr
                  end

                  DAE.REDUCTION(iterators = iterators)  => begin
                      @match true = hasZeroLengthIterator(iterators)
                      expr = ValuesUtil.valueExp(Values.META_FAIL())
                    expr
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = path, foldName = foldName, resultName = resultName, foldExp = foldExp, exprType = ty, defaultValue = defaultValue), expr = expr, iterators = DAE.REDUCTIONITER(id = iter_name, guardExp = NONE(), exp = range) <|  nil())  => begin
                      values = Expression.getArrayOrRangeContents(range)
                      ety = Types.simplifyType(ty)
                      values = ListUtil.map2(values, replaceIteratorWithExp, expr, iter_name)
                      expr = simplifyReductionFoldPhase(path, foldExp, foldName, resultName, ety, values, defaultValue)
                    expr
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = path, iterType = Absyn.THREAD(__), foldName = foldName, resultName = resultName, exprType = ty, foldExp = foldExp, defaultValue = defaultValue), expr = expr, iterators = iterators)  => begin
                      @match _cons(DAE.REDUCTIONITER(id = iter_name, guardExp = NONE(), exp = range), iterators) = iterators
                      values = Expression.getArrayOrRangeContents(range)
                      ety = Types.simplifyType(ty)
                      values = ListUtil.map2(values, replaceIteratorWithExp, expr, iter_name)
                      values = ListUtil.fold(iterators, getIteratorValues, values)
                      expr = simplifyReductionFoldPhase(path, foldExp, foldName, resultName, ety, values, defaultValue)
                    expr
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = path && Absyn.IDENT("array"), iterType = Absyn.COMBINE(__), foldName = foldName, resultName = resultName, exprType = ty), expr = expr, iterators = iter <| iterators && _ <| _)  => begin
                      foldName2 = Util.getTempVariableIndex()
                      resultName2 = Util.getTempVariableIndex()
                      ty1 = Types.unliftArray(ty)
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty1, NONE(), foldName, resultName, NONE()), expr, iterators)
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty, NONE(), foldName2, resultName2, NONE()), expr, list(iter))
                    expr
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = path, iterType = Absyn.COMBINE(__), foldName = foldName, resultName = resultName, exprType = ty, foldExp = NONE(), defaultValue = defaultValue), expr = expr, iterators = iter <| iterators && _ <| _)  => begin
                      foldName2 = Util.getTempVariableIndex()
                      resultName2 = Util.getTempVariableIndex()
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty, defaultValue, foldName2, resultName2, NONE()), expr, list(iter))
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty, defaultValue, foldName, resultName, NONE()), expr, iterators)
                    expr
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = path, iterType = Absyn.COMBINE(__), foldName = foldName, resultName = resultName, exprType = ty, foldExp = SOME(foldExpr), defaultValue = defaultValue), expr = expr, iterators = iter <| iterators && _ <| _)  => begin
                      foldName2 = Util.getTempVariableIndex()
                      resultName2 = Util.getTempVariableIndex()
                      (foldExpr2, _) = Expression.traverseExpBottomUp(foldExpr, Expression.renameExpCrefIdent, (foldName, foldName2))
                      (foldExpr2, _) = Expression.traverseExpBottomUp(foldExpr2, Expression.renameExpCrefIdent, (resultName, resultName2))
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty, defaultValue, foldName2, resultName2, SOME(foldExpr2)), expr, list(iter))
                      expr = DAE.REDUCTION(DAE.REDUCTIONINFO(path, Absyn.COMBINE(), ty, defaultValue, foldName, resultName, SOME(foldExpr)), expr, iterators)
                    expr
                  end

                  _  => begin
                      inReduction
                  end
                end
              end
               #=  TODO: Use foldExp
               =#
               #= ty = Types.unliftArray(ty);
               =#
               #=  iterType=THREAD() can handle multiple iterators
               =#
               #=  Start like for the normal reductions
               =#
               #=  Then also fix the rest of the iterators
               =#
               #=  And fold
               =#
               #=  array can handle multiple iterators
               =#
               #=  rest can also handle multiple iterators
               =#
          outValue
        end

        function getIteratorValues(iter::DAE.ReductionIterator, inValues::List{<:DAE.Exp}) ::List{DAE.Exp}
              local values::List{DAE.Exp}

              local iter_name::String
              local range::DAE.Exp

              @match DAE.REDUCTIONITER(id = iter_name, guardExp = NONE(), exp = range) = iter
              values = Expression.getArrayOrRangeContents(range)
              values = ListUtil.threadMap1(values, inValues, replaceIteratorWithExp, iter_name)
          values
        end

        function replaceIteratorWithExp(iterExp::DAE.Exp, exp::DAE.Exp, name::String) ::DAE.Exp
              local outExp::DAE.Exp

              @match (outExp, (_, _, true)) = Expression.traverseExpBottomUp(exp, replaceIteratorWithExpTraverser, (name, iterExp, true))
          outExp
        end

        function replaceIteratorWithExpTraverser(inExp::DAE.Exp, inTpl::Tuple{<:String, DAE.Exp, Bool}) ::Tuple{DAE.Exp, Tuple{String, DAE.Exp, Bool}}
              local outTpl::Tuple{String, DAE.Exp, Bool}
              local outExp::DAE.Exp

              (outExp, outTpl) = begin
                  local id::String
                  local id2::String
                  local name::String
                  local replName::String
                  local iterExp::DAE.Exp
                  local ty::DAE.Type
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ss::List{DAE.Subscript}
                  local b::Bool
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                  local tpl::Tuple{String, DAE.Exp, Bool}
                  local callPath::Absyn.Path
                  local recordPath::Absyn.Path
                  local varLst::List{DAE.Var}
                  local exps::List{DAE.Exp}
                  local i::ModelicaInteger
                @matchcontinue (inExp, inTpl) begin
                  (_, (_, _, false))  => begin
                    (inExp, inTpl)
                  end

                  (DAE.CREF(DAE.CREF_IDENT(id, _,  nil()), _), tpl && (name, iterExp, _)) where (stringEq(name, id))  => begin
                    (iterExp, tpl)
                  end

                  (exp && DAE.CREF(componentRef = DAE.CREF_IDENT(ident = id)), (name, iterExp, _)) where (stringEq(name, id))  => begin
                    (exp, (name, iterExp, false))
                  end

                  (DAE.CREF(DAE.CREF_QUAL(id, ty1, ss, cr), ty), tpl && (name, DAE.CREF(componentRef = DAE.CREF_IDENT(ident = replName, subscriptLst =  nil())), _)) where (stringEq(name, id))  => begin
                    (DAE.CREF(DAE.CREF_QUAL(replName, ty1, ss, cr), ty), tpl)
                  end

                  (DAE.CREF(DAE.CREF_QUAL(id, ty1,  nil(), cr), ty), tpl && (name, DAE.CREF(componentRef = DAE.CREF_IDENT(ident = replName, subscriptLst = ss)), _)) where (stringEq(name, id))  => begin
                    (DAE.CREF(DAE.CREF_QUAL(replName, ty1, ss, cr), ty), tpl)
                  end

                  (DAE.CREF(componentRef = DAE.CREF_QUAL(id, _,  nil(), DAE.CREF_IDENT(id2, _,  nil()))), tpl && (name, DAE.CALL(expLst = exps, path = callPath, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD(recordPath)))), _))  => begin
                      @match true = stringEq(name, id)
                      @match true = AbsynUtil.pathEqual(callPath, recordPath)
                      @match true = listLength(varLst) == listLength(exps)
                      i = ListUtil.position1OnTrue(varLst, DAEUtilMinimal.typeVarIdentEqual, id2)
                      exp = listGet(exps, i)
                    (exp, tpl)
                  end

                  (exp && DAE.CREF(componentRef = DAE.CREF_QUAL(ident = id)), (name, iterExp, _)) where (stringEq(name, id))  => begin
                    (exp, (name, iterExp, false))
                  end

                  _  => begin
                      (inExp, inTpl)
                  end
                end
              end
          (outExp, outTpl)
        end

        function simplifyReductionFoldPhase(path::Absyn.Path, optFoldExp::Option{<:DAE.Exp}, foldName::String, resultName::String, ty::DAE.Type, inExps::List{<:DAE.Exp}, defaultValue::Option{<:Values.Value}) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local val::Values.Value
                  local arr_exp::DAE.Exp
                  local foldExp::DAE.Exp
                  local aty::DAE.Type
                  local ty2::DAE.Type
                  local exps::List{DAE.Exp}
                  local length::ModelicaInteger
                @match (path, optFoldExp, foldName, resultName, ty, inExps, defaultValue) begin
                  (Absyn.IDENT("array"), _, _, _, _, _, _)  => begin
                      aty = Types.unliftArray(Types.expTypetoTypesType(ty))
                      length = listLength(inExps)
                      ty2 = Types.liftArray(aty, DAE.DIM_INTEGER(length))
                      exp = Expression.makeArray(inExps, ty2, ! Types.isArray(aty))
                    exp
                  end

                  (_, _, _, _, _,  nil(), SOME(val))  => begin
                    ValuesUtil.valueExp(val)
                  end

                  (_, _, _, _, _,  nil(), NONE())  => begin
                    fail()
                  end

                  (Absyn.IDENT("min"), _, _, _, _, _, _)  => begin
                      arr_exp = Expression.makeScalarArray(inExps, ty)
                    Expression.makePureBuiltinCall("min", list(arr_exp), ty)
                  end

                  (Absyn.IDENT("max"), _, _, _, _, _, _)  => begin
                      arr_exp = Expression.makeScalarArray(inExps, ty)
                    Expression.makePureBuiltinCall("max", list(arr_exp), ty)
                  end

                  (_, SOME(_), _, _, _, exp <|  nil(), _)  => begin
                    exp
                  end

                  (_, SOME(foldExp), _, _, _, exp <| exps, _)  => begin
                      exp = simplifyReductionFoldPhase2(exps, foldExp, foldName, resultName, exp)
                    exp
                  end
                end
              end
               #=  The size can be unknown before the reduction...
               =#
               #=  foldExp=(a+b) ; exps={1,2,3,4}
               =#
               #=  step 1: result=4
               =#
               #=  step 2: result= (replace b in (a+b) with 4, a with 3): 3+4
               =#
               #=  ...
               =#
               #=  Why reverse order? Smaller expressions to perform the replacements in
               =#
          exp
        end

        function simplifyReductionFoldPhase2(inExps::List{<:DAE.Exp}, foldExp::DAE.Exp, foldName::String, resultName::String, acc::DAE.Exp) ::DAE.Exp
              local exp::DAE.Exp

              exp = begin
                  local exps::List{DAE.Exp}
                @match (inExps, foldExp, foldName, resultName, acc) begin
                  ( nil(), _, _, _, _)  => begin
                    acc
                  end

                  (exp <| exps, _, _, _, _)  => begin
                      exp = replaceIteratorWithExp(exp, foldExp, foldName)
                      exp = replaceIteratorWithExp(acc, exp, resultName)
                    simplifyReductionFoldPhase2(exps, foldExp, foldName, resultName, exp)
                  end
                end
              end
          exp
        end

        function hasZeroLengthIterator(inIters::List{<:DAE.ReductionIterator}) ::Bool
              local b::Bool

              b = begin
                  local iters::List{DAE.ReductionIterator}
                @match inIters begin
                   nil()  => begin
                    false
                  end

                  DAE.REDUCTIONITER(guardExp = SOME(DAE.BCONST(false))) <| _  => begin
                    true
                  end

                  DAE.REDUCTIONITER(exp = DAE.LIST( nil())) <| _  => begin
                    true
                  end

                  DAE.REDUCTIONITER(exp = DAE.ARRAY(array =  nil())) <| _  => begin
                    true
                  end

                  _ <| iters  => begin
                    hasZeroLengthIterator(iters)
                  end
                end
              end
          b
        end

        function simplifyList(expl::List{<:DAE.Exp}) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp}

              outExpl = list(simplify1(exp) for exp in expl)
          outExpl
        end

        function simplifyList1(expl::List{<:DAE.Exp}) ::Tuple{List{DAE.Exp}, List{Bool}}
              local outBool::List{Bool} = nil
              local outExpl::List{DAE.Exp}

              outExpl = list(begin
                  local e::DAE.Exp
                  local b2::Bool
                @match exp begin
                  _  => begin
                      (e, b2) = simplify(exp)
                      outBool = _cons(b2, outBool)
                    e
                  end
                end
              end for exp in expl)
              outBool = Dangerous.listReverseInPlace(outBool)
          (outExpl, outBool)
        end

        function condsimplifyList1(blst::List{<:Bool}, expl::List{<:DAE.Exp}) ::Tuple{List{DAE.Exp}, List{Bool}}
              local outBool::List{Bool} = nil
              local outExpl::List{DAE.Exp} = nil

              local rest_expl::List{DAE.Exp} = expl
              local exp::DAE.Exp
              local b2::Bool

              for b in blst
                @match _cons(exp, rest_expl) = rest_expl
                (exp, b2) = condsimplify(b, exp)
                outExpl = _cons(exp, outExpl)
                outBool = _cons(b2, outBool)
              end
              outExpl = Dangerous.listReverseInPlace(outExpl)
              outBool = Dangerous.listReverseInPlace(outBool)
          (outExpl, outBool)
        end

         #= If this succeeds, and either argument to the operation is empty, the whole operation is empty =#
        function checkZeroLengthArrayOp(op::DAE.Operator)
              _ = begin
                @match op begin
                  DAE.ADD_ARR(__)  => begin
                    ()
                  end

                  DAE.SUB_ARR(__)  => begin
                    ()
                  end

                  DAE.MUL_ARR(__)  => begin
                    ()
                  end

                  DAE.DIV_ARR(__)  => begin
                    ()
                  end

                  DAE.POW_ARR(__)  => begin
                    ()
                  end

                  DAE.POW_ARR2(__)  => begin
                    ()
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    ()
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    ()
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    ()
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    ()
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    ()
                  end

                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    ()
                  end
                end
              end
        end

        function simplifyAddSymbolicOperation(exp::DAE.EquationExp, source::DAE.ElementSource) ::Tuple{DAE.EquationExp, DAE.ElementSource}
              local outSource::DAE.ElementSource
              local outExp::DAE.EquationExp

              (outExp, outSource) = begin
                  local changed::Bool
                  local changed1::Bool
                  local changed2::Bool
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                @match (exp, source) begin
                  (DAE.PARTIAL_EQUATION(e), _)  => begin
                      (e, changed) = simplify(e)
                      outExp = if changed
                            DAE.PARTIAL_EQUATION(e)
                          else
                            exp
                          end
                      outSource = ElementSource.condAddSymbolicTransformation(changed, source, DAE.SIMPLIFY(exp, outExp))
                    (outExp, outSource)
                  end

                  (DAE.RESIDUAL_EXP(e), _)  => begin
                      (e, changed) = simplify(e)
                      outExp = if changed
                            DAE.RESIDUAL_EXP(e)
                          else
                            exp
                          end
                      outSource = ElementSource.condAddSymbolicTransformation(changed, source, DAE.SIMPLIFY(exp, outExp))
                    (outExp, outSource)
                  end

                  (DAE.EQUALITY_EXPS(e1, e2), _)  => begin
                      (e1, changed1) = simplify(e1)
                      (e2, changed2) = simplify(e2)
                      changed = changed1 || changed2
                      outExp = if changed
                            DAE.EQUALITY_EXPS(e1, e2)
                          else
                            exp
                          end
                      outSource = ElementSource.condAddSymbolicTransformation(changed, source, DAE.SIMPLIFY(exp, outExp))
                    (outExp, outSource)
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("ExpressionSimplify.simplifyAddSymbolicOperation failed"))
                      fail()
                  end
                end
              end
          (outExp, outSource)
        end

        function condSimplifyAddSymbolicOperation(cond::Bool, exp::DAE.EquationExp, source::DAE.ElementSource) ::Tuple{DAE.EquationExp, DAE.ElementSource}



              if cond
                (exp, source) = simplifyAddSymbolicOperation(exp, source)
              end
          (exp, source)
        end

        function simplifySize(origExp::DAE.Exp, exp::DAE.Exp, optDim::Option{<:DAE.Exp}) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local i::ModelicaInteger
                  local n::ModelicaInteger
                  local t::DAE.Type
                  local dims::DAE.Dimensions
                  local dim::DAE.Dimension
                  local dimExp::DAE.Exp
                   #=  simplify size operator
                   =#
                @matchcontinue (origExp, exp, optDim) begin
                  (_, _, SOME(dimExp))  => begin
                      i = Expression.expInt(dimExp)
                      t = Expression.typeOf(exp)
                      dims = Expression.arrayDimension(t)
                      dim = listGet(dims, i)
                      n = Expression.dimensionSize(dim)
                    DAE.ICONST(n)
                  end

                  _  => begin
                      origExp
                  end
                end
              end
               #=  TODO: Handle optDim=NONE() when dims are known
               =#
          outExp
        end

        function simplifyTSub(origExp::DAE.Exp) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local expl::List{DAE.Exp}
                  local i::ModelicaInteger
                  local e::DAE.Exp
                   #=  NOTE: It should be impossible for TSUB to use an index that becomes out of range, so match is correct here...
                   =#
                @match origExp begin
                  DAE.TSUB(exp = DAE.CAST(exp = DAE.TUPLE(PR = expl)), ix = i)  => begin
                    listGet(expl, i)
                  end

                  DAE.TSUB(exp = DAE.TUPLE(PR = expl), ix = i)  => begin
                    listGet(expl, i)
                  end

                  DAE.TSUB(exp = e && DAE.RCONST(__))  => begin
                    e
                  end

                  _  => begin
                      origExp
                  end
                end
              end
          outExp
        end

         #= Adds noEvent() only to required subexpressions =#
        function simplifyNoEvent(inExp::DAE.Exp) ::DAE.Exp
              local e::DAE.Exp

              e = Expression.addNoEventToEventTriggeringFunctions(Expression.addNoEventToRelations(Expression.stripNoEvent(inExp)))
          e
        end

        function maxElement(e1::DAE.Exp, e2::Option{<:DAE.Exp}) ::Option{DAE.Exp}
              local elt::Option{DAE.Exp}

              elt = begin
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local b1::Bool
                  local b2::Bool
                @match (e1, e2) begin
                  (DAE.RCONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.ICONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.BCONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.RCONST(r1), SOME(DAE.RCONST(r2)))  => begin
                    if r1 > r2
                          SOME(e1)
                        else
                          e2
                        end
                  end

                  (DAE.ICONST(i1), SOME(DAE.ICONST(i2)))  => begin
                    if intGt(i1, i2)
                          SOME(e1)
                        else
                          e2
                        end
                  end

                  (DAE.BCONST(b1), SOME(DAE.BCONST(b2)))  => begin
                    if b2 || b1 == b2
                          e2
                        else
                          SOME(DAE.BCONST(b1))
                        end
                  end

                  _  => begin
                      e2
                  end
                end
              end
          elt
        end

        function minElement(e1::DAE.Exp, e2::Option{<:DAE.Exp}) ::Option{DAE.Exp}
              local elt::Option{DAE.Exp}

              elt = begin
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local b1::Bool
                  local b2::Bool
                @match (e1, e2) begin
                  (DAE.RCONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.ICONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.BCONST(_), NONE())  => begin
                    SOME(e1)
                  end

                  (DAE.RCONST(r1), SOME(DAE.RCONST(r2)))  => begin
                    if r1 < r2
                          SOME(e1)
                        else
                          e2
                        end
                  end

                  (DAE.ICONST(i1), SOME(DAE.ICONST(i2)))  => begin
                    if intLt(i1, i2)
                          SOME(e1)
                        else
                          e2
                        end
                  end

                  (DAE.BCONST(b1), SOME(DAE.BCONST(b2)))  => begin
                    if ! b2 || b1 == b2
                          e2
                        else
                          SOME(DAE.BCONST(b1))
                        end
                  end

                  _  => begin
                      e2
                  end
                end
              end
          elt
        end

        function removeMinMaxFoldableValues(e::DAE.Exp) ::Bool
              local filter::Bool

              filter = begin
                @match e begin
                  DAE.RCONST(_)  => begin
                    false
                  end

                  DAE.ICONST(_)  => begin
                    false
                  end

                  DAE.BCONST(_)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          filter
        end

         #= Simplifies the skew operator. =#
        function simplifySkew(v1::List{<:DAE.Exp}) ::List{List{DAE.Exp}}
              local res::List{List{DAE.Exp}}

              local x1::DAE.Exp
              local x2::DAE.Exp
              local x3::DAE.Exp
              local zero::DAE.Exp

              @match x1 <| x2 <| x3 <| nil = v1
              zero = Expression.makeConstZero(Expression.typeOf(x1))
              res = list(list(zero, Expression.negate(x3), x2), list(x3, zero, Expression.negate(x1)), list(Expression.negate(x2), x1, zero))
          res
        end

         #= Simplifies the cross operator. =#
        function simplifyCross(v1::List{<:DAE.Exp}, v2::List{<:DAE.Exp}) ::List{DAE.Exp}
              local res::List{DAE.Exp}

              local x1::DAE.Exp
              local x2::DAE.Exp
              local x3::DAE.Exp
              local y1::DAE.Exp
              local y2::DAE.Exp
              local y3::DAE.Exp

              @match x1 <| x2 <| x3 <| nil = v1
              @match y1 <| y2 <| y3 <| nil = v2
               #=  res = {x[2]*y[3] - x[3]*y[2], x[3]*y[1] - x[1]*y[3], x[1]*y[2] - x[2]*y[1]}
               =#
              res = list(Expression.makeDiff(Expression.makeProduct(x2, y3), Expression.makeProduct(x3, y2)), Expression.makeDiff(Expression.makeProduct(x3, y1), Expression.makeProduct(x1, y3)), Expression.makeDiff(Expression.makeProduct(x1, y2), Expression.makeProduct(x2, y1)))
          res
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

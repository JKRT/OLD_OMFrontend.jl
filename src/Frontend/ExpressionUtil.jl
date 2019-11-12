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

module ExpressionUtil

import DAE
import Error

         #= Helper function to typeof =#
        function typeofOp(inOperator::DAE.Operator) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::Type
                @match inOperator begin
                  DAE.ADD(ty = t)  => begin
                    t
                  end

                  DAE.SUB(ty = t)  => begin
                    t
                  end

                  DAE.MUL(ty = t)  => begin
                    t
                  end

                  DAE.DIV(ty = t)  => begin
                    t
                  end

                  DAE.POW(ty = t)  => begin
                    t
                  end

                  DAE.UMINUS(ty = t)  => begin
                    t
                  end

                  DAE.UMINUS_ARR(ty = t)  => begin
                    t
                  end

                  DAE.ADD_ARR(ty = t)  => begin
                    t
                  end

                  DAE.SUB_ARR(ty = t)  => begin
                    t
                  end

                  DAE.MUL_ARR(ty = t)  => begin
                    t
                  end

                  DAE.DIV_ARR(ty = t)  => begin
                    t
                  end

                  DAE.MUL_ARRAY_SCALAR(ty = t)  => begin
                    t
                  end

                  DAE.ADD_ARRAY_SCALAR(ty = t)  => begin
                    t
                  end

                  DAE.SUB_SCALAR_ARRAY(ty = t)  => begin
                    t
                  end

                  DAE.MUL_SCALAR_PRODUCT(ty = t)  => begin
                    t
                  end

                  DAE.MUL_MATRIX_PRODUCT(ty = t)  => begin
                    t
                  end

                  DAE.DIV_ARRAY_SCALAR(ty = t)  => begin
                    t
                  end

                  DAE.DIV_SCALAR_ARRAY(ty = t)  => begin
                    t
                  end

                  DAE.POW_ARRAY_SCALAR(ty = t)  => begin
                    t
                  end

                  DAE.POW_SCALAR_ARRAY(ty = t)  => begin
                    t
                  end

                  DAE.POW_ARR(ty = t)  => begin
                    t
                  end

                  DAE.POW_ARR2(ty = t)  => begin
                    t
                  end

                  DAE.AND(ty = t)  => begin
                    t
                  end

                  DAE.OR(ty = t)  => begin
                    t
                  end

                  DAE.NOT(ty = t)  => begin
                    t
                  end

                  DAE.LESS(ty = t)  => begin
                    t
                  end

                  DAE.LESSEQ(ty = t)  => begin
                    t
                  end

                  DAE.GREATER(ty = t)  => begin
                    t
                  end

                  DAE.GREATEREQ(ty = t)  => begin
                    t
                  end

                  DAE.EQUAL(ty = t)  => begin
                    t
                  end

                  DAE.NEQUAL(ty = t)  => begin
                    t
                  end

                  DAE.USERDEFINED(__)  => begin
                    DAE.T_UNKNOWN_DEFAULT
                  end
                end
              end
          outType
        end

         #= Retrieves the Type of the Expression =#
        function typeof(inExp::DAE.Exp) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local tp::Type
                  local op::Operator
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e::DAE.Exp
                  local iterExp::DAE.Exp
                  local operExp::DAE.Exp
                  local explist::List{DAE.Exp}
                  local exps::List{DAE.Exp}
                  local p::Absyn.Path
                  local msg::String
                  local ty::DAE.Type
                  local iterTp::DAE.Type
                  local operTp::DAE.Type
                  local tys::List{DAE.Type}
                  local typeVars::List{DAE.Type}
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local dim::DAE.Dimension
                  local iterdims::DAE.Dimensions
                @matchcontinue inExp begin
                  DAE.ICONST(__)  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  DAE.RCONST(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  DAE.SCONST(__)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  DAE.BCONST(__)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  DAE.CLKCONST(__)  => begin
                    DAE.T_CLOCK_DEFAULT
                  end

                  DAE.ENUM_LITERAL(name = p, index = i)  => begin
                    DAE.T_ENUMERATION(SOME(i), p, nil, nil, nil)
                  end

                  DAE.CREF(ty = tp)  => begin
                    tp
                  end

                  DAE.BINARY(operator = op)  => begin
                    typeofOp(op)
                  end

                  DAE.UNARY(operator = op)  => begin
                    typeofOp(op)
                  end

                  DAE.LBINARY(operator = op)  => begin
                    typeofOp(op)
                  end

                  DAE.LUNARY(operator = op)  => begin
                    typeofOp(op)
                  end

                  DAE.RELATION(operator = op)  => begin
                    typeofRelation(typeofOp(op))
                  end

                  DAE.IFEXP(expThen = e2)  => begin
                    typeof(e2)
                  end

                  DAE.CALL(attr = DAE.CALL_ATTR(ty = tp))  => begin
                    tp
                  end

                  DAE.RECORD(ty = tp)  => begin
                    tp
                  end

                  DAE.PARTEVALFUNCTION(ty = tp)  => begin
                    tp
                  end

                  DAE.ARRAY(ty = tp)  => begin
                    tp
                  end

                  DAE.MATRIX(ty = tp)  => begin
                    tp
                  end

                  DAE.RANGE(start = DAE.ICONST(i1), step = NONE(), stop = DAE.ICONST(i2), ty = tp && DAE.T_INTEGER(__))  => begin
                      i = intMax(0, i2 - i1 + 1)
                    DAE.T_ARRAY(tp, list(DAE.DIM_INTEGER(i)))
                  end

                  DAE.RANGE(start = DAE.ICONST(1), step = NONE(), stop = e, ty = tp && DAE.T_INTEGER(__))  => begin
                    DAE.T_ARRAY(tp, list(DAE.DIM_EXP(e)))
                  end

                  DAE.RANGE(ty = tp)  => begin
                    DAE.T_ARRAY(tp, list(DAE.DIM_UNKNOWN()))
                  end

                  DAE.CAST(ty = tp)  => begin
                    tp
                  end

                  DAE.ASUB(exp = e, sub = explist)  => begin
                      i = sum(1 for e in explist if isScalar(e))
                      tp = unliftArrayX(typeof(e), i)
                    tp
                  end

                  DAE.TSUB(ty = tp)  => begin
                    tp
                  end

                  DAE.RSUB(__)  => begin
                    inExp.ty
                  end

                  DAE.CODE(ty = tp)  => begin
                    tp
                  end

                  DAE.REDUCTION(iterators = DAE.REDUCTIONITER(exp = iterExp, guardExp = NONE()) <|  nil(), expr = operExp, reductionInfo = DAE.REDUCTIONINFO(exprType = DAE.T_ARRAY(dims = dim <| _), path = Absyn.IDENT("array")))  => begin
                      @match false = dimensionKnown(dim)
                      iterTp = typeof(iterExp)
                      operTp = typeof(operExp)
                      @match DAE.T_ARRAY(dims = iterdims) = iterTp
                      tp = Types.liftTypeWithDims(operTp, iterdims)
                    tp
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(exprType = ty))  => begin
                    Types.simplifyType(ty)
                  end

                  DAE.SIZE(_, NONE())  => begin
                    DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN()))
                  end

                  DAE.SIZE(_, SOME(_))  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  DAE.LIST(__)  => begin
                    DAE.T_METATYPE(DAE.T_METALIST_DEFAULT)
                  end

                  DAE.CONS(__)  => begin
                    DAE.T_METATYPE(DAE.T_METALIST_DEFAULT)
                  end

                  DAE.META_TUPLE(exps)  => begin
                      tys = ListUtil.map(exps, typeof)
                    DAE.T_METATYPE(DAE.T_METATUPLE(tys))
                  end

                  DAE.TUPLE(exps)  => begin
                      tys = ListUtil.map(exps, typeof)
                    DAE.T_TUPLE(tys, NONE())
                  end

                  DAE.META_OPTION(__)  => begin
                    DAE.T_METATYPE(DAE.T_NONE_DEFAULT)
                  end

                  DAE.METARECORDCALL(path = p, index = i, typeVars = typeVars)  => begin
                    DAE.T_METATYPE(DAE.T_METARECORD(p, AbsynUtil.stripLast(p), typeVars, i, nil, false))
                  end

                  DAE.BOX(e)  => begin
                    DAE.T_METATYPE(DAE.T_METABOXED(typeof(e)))
                  end

                  DAE.MATCHEXPRESSION(et = tp)  => begin
                    tp
                  end

                  DAE.UNBOX(ty = tp)  => begin
                    tp
                  end

                  DAE.SHARED_LITERAL(exp = e)  => begin
                    typeof(e)
                  end

                  DAE.EMPTY(ty = tp)  => begin
                    tp
                  end

                  e  => begin
                      msg = "- Expression.typeof failed for " + dump(e)
                      Error.addMessage(Error.INTERNAL_ERROR, list(msg))
                    fail()
                  end
                end
              end
               #=  Count the number of scalar subscripts, and remove as many dimensions.
               =#
               #= /* array reduction with known size */ =#
               #=  MetaModelica extension
               =#
               #=  A little crazy, but sometimes we call typeof on things that will not be used in the end...
               =#
          outType
        end
         #= Returns true if the two expressions are equal, otherwise false. =#
        function expEqual(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool
              local outEqual::Bool
              outEqual = 0 == compare(inExp1, inExp2)
          outEqual
        end


@exportAll
end

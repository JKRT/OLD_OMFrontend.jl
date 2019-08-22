  module Expression 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    MapFunc = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType2 = Function

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

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncCrefTypeA = Function

    FuncCrefTypeA = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

    FuncType = Function

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
         #=  public imports
         =#

        import Absyn

        import AbsynUtil

        import DAE

        import DAEDump

        ComponentRef = DAE.ComponentRef 
        Exp = DAE.Exp 
        Operator = DAE.Operator 
        Type = DAE.Type 
        Subscript = DAE.Subscript 
        Var = DAE.Var 
         #=  protected imports
         =#

        import ArrayUtil

        import ClassInf

        import ComponentReference

        import Config

        import DAEUtil

        import Debug

        import DoubleEnded

        import FCore

        import FGraph

        import Error

        import ExpressionDump

        import ExpressionDump.printExpStr

        import ExpressionSimplify

        import Dump

        import Flags

        import ListUtil

        import Patternm

        import Prefix

        import Static

        import System
         #=  stringReal
         =#

        import Types

        import Util
         #= /***************************************************/ =#
         #= /* transform to other types */ =#
         #= /***************************************************/ =#

         #= Converts an integer into an index subscript. =#
        function intSubscript(inInteger::ModelicaInteger) ::DAE.Subscript 
              local outSubscript::DAE.Subscript

              outSubscript = DAE.INDEX(DAE.ICONST(inInteger))
          outSubscript
        end

         #= Converts a list of integers into index subscripts. =#
        function intSubscripts(inIntegers::List{<:ModelicaInteger}) ::List{DAE.Subscript} 
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = ListUtil.map(inIntegers, intSubscript)
          outSubscripts
        end

         #= Tries to convert a subscript to an integer index. =#
        function subscriptInt(inSubscript::DAE.Subscript) ::ModelicaInteger 
              local outInteger::ModelicaInteger = expArrayIndex(subscriptIndexExp(inSubscript))
          outInteger
        end

         #= Tries to convert a list of subscripts to integer indices. =#
        function subscriptsInt(inSubscripts::List{<:DAE.Subscript}) ::List{ModelicaInteger} 
              local outIntegers::List{ModelicaInteger}

              outIntegers = ListUtil.map(inSubscripts, subscriptInt)
          outIntegers
        end

        function dimensionIsZero(inDimension::DAE.Dimension) ::Bool 
              local outIsZero::Bool

              outIsZero = 0 == dimensionSize(inDimension)
          outIsZero
        end

         #= Transform an DAE.Exp into Absyn.Expression.
          Note: This function currently only works for
          constants and component references. =#
        function unelabExp(inExp::DAE.Exp) ::Absyn.Exp 
              local outExp::Absyn.Exp

              outExp = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local s::String
                  local b::Bool
                  local cr_1::Absyn.ComponentRef
                  local cr::ComponentRef
                  local expl_1::List{Absyn.Exp}
                  local aexpl::List{Absyn.Exp}
                  local expl::List{DAE.Exp}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local op::Operator
                  local ae1::Absyn.Exp
                  local ae2::Absyn.Exp
                  local ae3::Absyn.Exp
                  local aop::Absyn.Operator
                  local mexpl2::List{List{DAE.Exp}}
                  local amexpl::List{List{Absyn.Exp}}
                  local acref::Absyn.ComponentRef
                  local path::Absyn.Path
                  local code::Absyn.CodeNode
                  local riters::DAE.ReductionIterators
                  local aiters::Absyn.ForIterators
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                  local iterType::Absyn.ReductionIterType
                @matchcontinue inExp begin
                  DAE.ICONST(integer = i)  => begin
                    Absyn.INTEGER(i)
                  end
                  
                  DAE.RCONST(real = r)  => begin
                      s = realString(r)
                    Absyn.REAL(s)
                  end
                  
                  DAE.SCONST(string = s)  => begin
                    Absyn.STRING(s)
                  end
                  
                  DAE.BCONST(bool = b)  => begin
                    Absyn.BOOL(b)
                  end
                  
                  DAE.ENUM_LITERAL(name = path)  => begin
                      cr_1 = AbsynUtil.pathToCref(path)
                    Absyn.CREF(cr_1)
                  end
                  
                  DAE.CREF(componentRef = cr)  => begin
                      cr_1 = ComponentReference.unelabCref(cr)
                    Absyn.CREF(cr_1)
                  end
                  
                  DAE.BINARY(e1, op, e2)  => begin
                      aop = unelabOperator(op)
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                    Absyn.BINARY(ae1, aop, ae2)
                  end
                  
                  DAE.UNARY(op, e1)  => begin
                      aop = unelabOperator(op)
                      ae1 = unelabExp(e1)
                    Absyn.UNARY(aop, ae1)
                  end
                  
                  DAE.LBINARY(e1, op, e2)  => begin
                      aop = unelabOperator(op)
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                    Absyn.LBINARY(ae1, aop, ae2)
                  end
                  
                  DAE.LUNARY(op, e1)  => begin
                      aop = unelabOperator(op)
                      ae1 = unelabExp(e1)
                    Absyn.LUNARY(aop, ae1)
                  end
                  
                  DAE.RELATION(exp1 = e1, operator = op, exp2 = e2)  => begin
                      aop = unelabOperator(op)
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                    Absyn.RELATION(ae1, aop, ae2)
                  end
                  
                  DAE.IFEXP(e1, e2, e3)  => begin
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                      ae3 = unelabExp(e3)
                    Absyn.IFEXP(ae1, ae2, ae3, nil)
                  end
                  
                  DAE.CALL(path, expl, _)  => begin
                      aexpl = ListUtil.map(expl, unelabExp)
                      acref = AbsynUtil.pathToCref(path)
                    Absyn.CALL(acref, Absyn.FUNCTIONARGS(aexpl, nil))
                  end
                  
                  DAE.RECORD(path = path, exps = expl)  => begin
                      aexpl = ListUtil.map(expl, unelabExp)
                      acref = AbsynUtil.pathToCref(path)
                    Absyn.CALL(acref, Absyn.FUNCTIONARGS(aexpl, nil))
                  end
                  
                  DAE.PARTEVALFUNCTION(path, expl, _, _)  => begin
                      aexpl = ListUtil.map(expl, unelabExp)
                      acref = AbsynUtil.pathToCref(path)
                    Absyn.PARTEVALFUNCTION(acref, Absyn.FUNCTIONARGS(aexpl, nil))
                  end
                  
                  DAE.ARRAY(array =  nil(), ty = ty)  => begin
                      (ty, dims) = Types.flattenArrayType(ty)
                      ae1 = unleabZeroExpFromType(ty)
                      expl_1 = ListUtil.map(dims, unelabDimensionToFillExp)
                    Absyn.CALL(Absyn.CREF_IDENT("fill", nil), Absyn.FUNCTIONARGS(_cons(ae1, expl_1), nil))
                  end
                  
                  DAE.ARRAY(array = expl)  => begin
                      expl_1 = ListUtil.map(expl, unelabExp)
                    Absyn.ARRAY(expl_1)
                  end
                  
                  DAE.MATRIX(matrix = mexpl2)  => begin
                      amexpl = ListUtil.mapList(mexpl2, unelabExp)
                    Absyn.MATRIX(amexpl)
                  end
                  
                  DAE.RANGE(_, e1, SOME(e2), e3)  => begin
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                      ae3 = unelabExp(e3)
                    Absyn.RANGE(ae1, SOME(ae2), ae3)
                  end
                  
                  DAE.RANGE(_, e1, NONE(), e3)  => begin
                      ae1 = unelabExp(e1)
                      ae3 = unelabExp(e3)
                    Absyn.RANGE(ae1, NONE(), ae3)
                  end
                  
                  DAE.TUPLE(expl)  => begin
                      expl_1 = ListUtil.map(expl, unelabExp)
                    Absyn.TUPLE(expl_1)
                  end
                  
                  DAE.CAST(_, e1)  => begin
                      ae1 = unelabExp(e1)
                    ae1
                  end
                  
                  DAE.ASUB(_, _)  => begin
                      print("Internal Error, can not unelab ASUB\\n")
                    fail()
                  end
                  
                  DAE.TSUB(e1, _, _)  => begin
                      ae1 = unelabExp(e1)
                    ae1
                  end
                  
                  DAE.SIZE(e1, SOME(e2))  => begin
                      ae1 = unelabExp(e1)
                      ae2 = unelabExp(e2)
                    Absyn.CALL(Absyn.CREF_IDENT("size", nil), Absyn.FUNCTIONARGS(list(ae1, ae2), nil))
                  end
                  
                  DAE.CODE(code, _)  => begin
                    Absyn.CODE(code)
                  end
                  
                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(iterType = iterType, path = path), expr = e1, iterators = riters)  => begin
                      acref = AbsynUtil.pathToCref(path)
                      ae1 = unelabExp(e1)
                      aiters = ListUtil.map(riters, unelabReductionIterator)
                    Absyn.CALL(acref, Absyn.FOR_ITER_FARG(ae1, iterType, aiters))
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        print("Expression.unelabExp failed on: " + ExpressionDump.printExpStr(inExp) + "\\n")
                      fail()
                  end
                end
              end
               #=  ASUB can not be unelabed since it has no representation in Absyn.
               =#
               #=  TSUB(expression) => expression
               =#
               #= /* WHAT? exactly the same case as above???!!!
                  case(DAE.SIZE(e1,SOME(e2))) equation
                    ae1 = unelabExp(e1);
                    ae2 = unelabExp(e2);
                  then Absyn.CALL(Absyn.CREF_IDENT(\"size\",{}),Absyn.FUNCTIONARGS({ae1,ae2},{}));
                  */ =#
               #= print(\"unelab of reduction not impl. yet\");
               =#
          outExp
        end

         #= Transform an DAE.Dimension into Absyn.Subscript, if possible =#
        function unelabDimension(inDim::DAE.Dimension) ::Absyn.Subscript 
              local outDim::Absyn.Subscript

              outDim = begin
                  local i::ModelicaInteger
                  local p::Absyn.Path
                  local c::Absyn.ComponentRef
                  local e::DAE.Exp
                  local ae::Absyn.Exp
                @match inDim begin
                  DAE.DIM_INTEGER(i)  => begin
                    Absyn.SUBSCRIPT(Absyn.INTEGER(i))
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    Absyn.SUBSCRIPT(Absyn.CREF(Absyn.CREF_IDENT("Boolean", nil)))
                  end
                  
                  DAE.DIM_ENUM(enumTypeName = p)  => begin
                      c = AbsynUtil.pathToCref(p)
                    Absyn.SUBSCRIPT(Absyn.CREF(c))
                  end
                  
                  DAE.DIM_EXP(e)  => begin
                      ae = unelabExp(e)
                    Absyn.SUBSCRIPT(ae)
                  end
                  
                  DAE.DIM_UNKNOWN(__)  => begin
                    Absyn.NOSUB()
                  end
                end
              end
          outDim
        end

        function unleabZeroExpFromType(ty::DAE.Type) ::Absyn.Exp 
              local outExp::Absyn.Exp

              outExp = begin
                @match ty begin
                  DAE.T_BOOL(__)  => begin
                    Absyn.BOOL(false)
                  end
                  
                  DAE.T_STRING(__)  => begin
                    Absyn.STRING("")
                  end
                  
                  DAE.T_INTEGER(__)  => begin
                    Absyn.INTEGER(0)
                  end
                  
                  DAE.T_REAL(__)  => begin
                    Absyn.REAL("0.0")
                  end
                  
                  DAE.T_UNKNOWN(__)  => begin
                    Absyn.REAL("0.0")
                  end
                end
              end
               #= /* Look at the crap unelabMod needs... */ =#
          outExp
        end

         #= Transform an DAE.Dimension into Absyn.Exp, if possible =#
        function unelabDimensionToFillExp(inDim::DAE.Dimension) ::Absyn.Exp 
              local outExp::Absyn.Exp

              outExp = begin
                  local i::ModelicaInteger
                  local e::DAE.Exp
                @match inDim begin
                  DAE.DIM_INTEGER(i)  => begin
                    Absyn.INTEGER(i)
                  end
                  
                  DAE.DIM_EXP(e)  => begin
                    unelabExp(e)
                  end
                  
                  _  => begin
                      Absyn.INTEGER(1)
                  end
                end
              end
               #= /* Probably bad, but only used with zero-length arrays */ =#
          outExp
        end

        function unelabReductionIterator(riter::DAE.ReductionIterator) ::Absyn.ForIterator 
              local aiter::Absyn.ForIterator

              aiter = begin
                  local id::String
                  local exp::DAE.Exp
                  local gexp::Option{DAE.Exp}
                  local aexp::Absyn.Exp
                  local agexp::Option{Absyn.Exp}
                @match riter begin
                  DAE.REDUCTIONITER(id = id, exp = exp, guardExp = gexp)  => begin
                      aexp = unelabExp(exp)
                      agexp = Util.applyOption(gexp, unelabExp)
                    Absyn.ITERATOR(id, agexp, SOME(aexp))
                  end
                end
              end
          aiter
        end

         #= help function to unelabExpression. =#
        function unelabOperator(op::DAE.Operator) ::Absyn.Operator 
              local aop::Absyn.Operator

              aop = begin
                @match op begin
                  DAE.ADD(_)  => begin
                    Absyn.ADD()
                  end
                  
                  DAE.SUB(_)  => begin
                    Absyn.SUB()
                  end
                  
                  DAE.MUL(_)  => begin
                    Absyn.MUL()
                  end
                  
                  DAE.DIV(_)  => begin
                    Absyn.DIV()
                  end
                  
                  DAE.POW(_)  => begin
                    Absyn.POW()
                  end
                  
                  DAE.UMINUS(_)  => begin
                    Absyn.UMINUS()
                  end
                  
                  DAE.UMINUS_ARR(_)  => begin
                    Absyn.UMINUS()
                  end
                  
                  DAE.ADD_ARR(_)  => begin
                    Absyn.ADD()
                  end
                  
                  DAE.SUB_ARR(_)  => begin
                    Absyn.SUB()
                  end
                  
                  DAE.MUL_ARR(_)  => begin
                    Absyn.MUL()
                  end
                  
                  DAE.DIV_ARR(_)  => begin
                    Absyn.DIV()
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(_)  => begin
                    Absyn.MUL()
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(_)  => begin
                    Absyn.ADD()
                  end
                  
                  DAE.SUB_SCALAR_ARRAY(_)  => begin
                    Absyn.SUB()
                  end
                  
                  DAE.MUL_SCALAR_PRODUCT(_)  => begin
                    Absyn.MUL()
                  end
                  
                  DAE.MUL_MATRIX_PRODUCT(_)  => begin
                    Absyn.MUL()
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(_)  => begin
                    Absyn.DIV()
                  end
                  
                  DAE.DIV_ARRAY_SCALAR(_)  => begin
                    Absyn.DIV()
                  end
                  
                  DAE.POW_SCALAR_ARRAY(_)  => begin
                    Absyn.POW()
                  end
                  
                  DAE.POW_ARRAY_SCALAR(_)  => begin
                    Absyn.POW()
                  end
                  
                  DAE.POW_ARR(_)  => begin
                    Absyn.POW()
                  end
                  
                  DAE.POW_ARR2(_)  => begin
                    Absyn.POW()
                  end
                  
                  DAE.AND(_)  => begin
                    Absyn.AND()
                  end
                  
                  DAE.OR(_)  => begin
                    Absyn.OR()
                  end
                  
                  DAE.NOT(_)  => begin
                    Absyn.NOT()
                  end
                  
                  DAE.LESS(_)  => begin
                    Absyn.LESS()
                  end
                  
                  DAE.LESSEQ(_)  => begin
                    Absyn.LESSEQ()
                  end
                  
                  DAE.GREATER(_)  => begin
                    Absyn.GREATER()
                  end
                  
                  DAE.GREATEREQ(_)  => begin
                    Absyn.GREATEREQ()
                  end
                  
                  DAE.EQUAL(_)  => begin
                    Absyn.EQUAL()
                  end
                  
                  DAE.NEQUAL(_)  => begin
                    Absyn.NEQUAL()
                  end
                end
              end
          aop
        end

         #= This function takes an expression and transforms all component
          reference  names contained in the expression to a simpler form.
          For instance DAE.CREF_QUAL(a,{}, DAE.CREF_IDENT(b,{})) becomes
          DAE.CREF_IDENT(a.b,{})

          NOTE: This function should not be used in OMC, since the OMC backend no longer
                uses stringified components. It is still used by MathCore though. =#
        function stringifyCrefs(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = traverseExpDummy(inExp, traversingstringifyCrefFinder)
          outExp
        end

         #= 
        helper for stringifyCrefs =#
        function traversingstringifyCrefFinder(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local cr::ComponentRef
                  local crs::ComponentRef
                  local ty::Type
                  local e::DAE.Exp
                  local blist::List{Bool}
                @match inExp begin
                  DAE.CREF(ty = DAE.T_FUNCTION_REFERENCE_VAR(__))  => begin
                    inExp
                  end
                  
                  DAE.CREF(ty = DAE.T_FUNCTION_REFERENCE_FUNC(__))  => begin
                    inExp
                  end
                  
                  DAE.CREF(cr, ty)  => begin
                      crs = ComponentReference.stringifyComponentRef(cr)
                    makeCrefExp(crs, ty)
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

        function CodeVarToCref(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e_cref::ComponentRef
                  local cref::Absyn.ComponentRef
                  local e::DAE.Exp
                @match inExp begin
                  DAE.CODE(Absyn.C_VARIABLENAME(cref), _)  => begin
                      (_, e_cref) = Static.elabUntypedCref(FCore.emptyCache(), FGraph.empty(), cref, false, Prefix.NOPRE(), AbsynUtil.dummyInfo)
                      e = crefExp(e_cref)
                    e
                  end
                  
                  DAE.CODE(Absyn.C_EXPRESSION(Absyn.CALL(Absyn.CREF_IDENT("der",  nil()), Absyn.FUNCTIONARGS(Absyn.CREF(cref) <|  nil(),  nil()))), _)  => begin
                      (_, e_cref) = Static.elabUntypedCref(FCore.emptyCache(), FGraph.empty(), cref, false, Prefix.NOPRE(), AbsynUtil.dummyInfo)
                      e = crefExp(e_cref)
                    DAE.CALL(Absyn.IDENT("der"), list(e), DAE.callAttrBuiltinReal)
                  end
                end
              end
          outExp
        end

         #= converts to ICONST if possible. If it does
         not fit, a RCONST is returned instead. =#
        function realToIntIfPossible(inVal::ModelicaReal) ::DAE.Exp 
              local outVal::DAE.Exp

              try
                outVal = DAE.ICONST(realInt(inVal))
              catch
                outVal = DAE.RCONST(inVal)
              end
          outVal
        end

         #= 
          function liftArrayR
          Converts a type into an array type with dimension n as first dim =#
        function liftArrayR(tp::DAE.Type, n::DAE.Dimension) ::DAE.Type 
              local outTp::DAE.Type

              outTp = begin
                  local elt_tp::Type
                  local dims::List{DAE.Dimension}
                @match (tp, n) begin
                  (DAE.T_ARRAY(elt_tp, dims), _)  => begin
                      dims = _cons(n, dims)
                    DAE.T_ARRAY(elt_tp, dims)
                  end
                  
                  _  => begin
                      DAE.T_ARRAY(tp, list(n))
                  end
                end
              end
          outTp
        end

         #= Converts (extracts) a dimension to an expression.
          This function will fail if dimension is unknown or an expression (in case the dimension is from a different scope).
          If you want to(kind of) handle unknown dims use dimensionSizeExpHandleUnkown. =#
        function dimensionSizeConstantExp(dim::DAE.Dimension) ::DAE.Exp 
              local exp::DAE.Exp

              exp = begin
                  local i::ModelicaInteger
                @match dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    DAE.ICONST(2)
                  end
                end
              end
          exp
        end

         #= Converts (extracts) a dimension to an expression.
          This function will fail if dimension is unknown. i.e. DIM_UNKNOWN.
          If you want to(kind of) handle unknown dims use dimensionSizeExpHandleUnkown. =#
        function dimensionSizeExp(dim::DAE.Dimension) ::DAE.Exp 
              local exp::DAE.Exp

              exp = begin
                  local i::ModelicaInteger
                  local e::DAE.Exp
                @match dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    DAE.ICONST(2)
                  end
                  
                  DAE.DIM_EXP(exp = e)  => begin
                    e
                  end
                end
              end
          exp
        end

         #= Converts (extracts) a dimension to an expression.
          This function will change unknown dims to DAE.ICONST(-1).
          we use it to handle unknown dims in code generation. unknown dims
          are okay if the variable is a function input (it's just holds the slot
          and will not be generated). Otherwise it's an error
          since it shouldn't have reached there. =#
        function dimensionSizeExpHandleUnkown(dim::DAE.Dimension) ::DAE.Exp 
              local exp::DAE.Exp

              exp = begin
                @match dim begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    DAE.ICONST(-1)
                  end
                  
                  _  => begin
                      dimensionSizeExp(dim)
                  end
                end
              end
          exp
        end

         #= Converts an integer to an array dimension. =#
        function intDimension(value::ModelicaInteger) ::DAE.Dimension 
              local dim::DAE.Dimension

              dim = DAE.DIM_INTEGER(value)
          dim
        end

         #= Converts an array dimension to a subscript. =#
        function dimensionSubscript(dim::DAE.Dimension) ::DAE.Subscript 
              local sub::DAE.Subscript

              sub = begin
                  local i::ModelicaInteger
                @match dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    DAE.INDEX(DAE.ICONST(i))
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    DAE.INDEX(DAE.ICONST(i))
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    DAE.INDEX(DAE.ICONST(2))
                  end
                  
                  DAE.DIM_UNKNOWN(__)  => begin
                    DAE.WHOLEDIM()
                  end
                end
              end
          sub
        end

         #= /***************************************************/ =#
         #= /* Change  */ =#
         #= /***************************************************/ =#

         #= author: PA
          Negates an expression. =#
        function negate(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local t::Type
                  local op::Operator
                  local b::Bool
                  local b_1::Bool
                  local r::ModelicaReal
                  local r_1::ModelicaReal
                  local i::ModelicaInteger
                  local i_1::ModelicaInteger
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                   #=  to avoid un-necessary --e
                   =#
                @match inExp begin
                  DAE.UNARY(DAE.UMINUS(_), e)  => begin
                    e
                  end
                  
                  DAE.UNARY(DAE.UMINUS_ARR(_), e)  => begin
                    e
                  end
                  
                  DAE.LUNARY(DAE.NOT(_), e)  => begin
                    e
                  end
                  
                  DAE.BINARY(e1, op, e2) where (isMulOrDiv(op))  => begin
                    DAE.BINARY(negate(e1), op, e2)
                  end
                  
                  DAE.BINARY(e1, op, e2) where (isSub(op))  => begin
                    DAE.BINARY(e2, op, e1)
                  end
                  
                  e where (isZero(e))  => begin
                    e
                  end
                  
                  DAE.ICONST(i)  => begin
                      i_1 = 0 - i
                    DAE.ICONST(i_1)
                  end
                  
                  DAE.RCONST(r)  => begin
                      r_1 = 0.0 - r
                    DAE.RCONST(r_1)
                  end
                  
                  DAE.BCONST(b)  => begin
                      b_1 = ! b
                    DAE.BCONST(b_1)
                  end
                  
                  e  => begin
                      t = typeof(e)
                      outExp = begin
                        @match t begin
                          DAE.T_BOOL(__)  => begin
                            DAE.LUNARY(DAE.NOT(t), e)
                          end
                          
                          _  => begin
                                b = DAEUtil.expTypeArray(t)
                                op = if b
                                      DAE.UMINUS_ARR(t)
                                    else
                                      DAE.UMINUS(t)
                                    end
                              DAE.UNARY(op, e)
                          end
                        end
                      end
                    outExp
                  end
                end
              end
               #=  -(a*b) = (-a)*b
               =#
               #=  -(a/b) = (-a)/b
               =#
               #=  -(a-b) = b-a
               =#
               #=  -0 = 0
               =#
               #=  not e
               =#
          outExp
        end

        function negateReal(inReal::DAE.Exp) ::DAE.Exp 
              local outNegatedReal::DAE.Exp

              outNegatedReal = DAE.UNARY(DAE.UMINUS(DAE.T_REAL_DEFAULT), inReal)
          outNegatedReal
        end

         #= expands products
        For example
        a *(b+c) => a*b + a*c =#
        function expand(e::DAE.Exp) ::DAE.Exp 
              local outE::DAE.Exp

              outE = begin
                  local tp::DAE.Type
                  local op::DAE.Operator
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e21::DAE.Exp
                  local e22::DAE.Exp
                @match e begin
                  DAE.BINARY(e1, DAE.MUL(tp), e2 && DAE.BINARY(e21, op, e22)) where (isAddOrSub(op))  => begin
                      @match DAE.BINARY(e21, op, e22) = expand(e2)
                    DAE.BINARY(DAE.BINARY(e1, DAE.MUL(tp), e21), op, DAE.BINARY(e1, DAE.MUL(tp), e22))
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          outE
        end

         #= author: Frenkel TUD 2012-11
          exp -> der(exp) =#
        function expDer(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = DAE.CALL(Absyn.IDENT("der"), list(inExp), DAE.callAttrBuiltinReal)
          outExp
        end

         #= author: PA
          Makes the expression absolute. i.e. non-negative. =#
        function expAbs(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local i2::ModelicaInteger
                  local i::ModelicaInteger
                  local r2::ModelicaReal
                  local r::ModelicaReal
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local tp::Type
                  local op::Operator
                @match inExp begin
                  DAE.ICONST(integer = i)  => begin
                      i2 = intAbs(i)
                    DAE.ICONST(i2)
                  end
                  
                  DAE.RCONST(real = r)  => begin
                      r2 = realAbs(r)
                    DAE.RCONST(r2)
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS(__), exp = e)  => begin
                      e_1 = expAbs(e)
                    e_1
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      e1_1 = expAbs(e1)
                      e2_1 = expAbs(e2)
                    DAE.BINARY(e1_1, op, e2_1)
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= Function that strips all noEvent() calls in an expression =#
        function stripNoEvent(e::DAE.Exp) ::DAE.Exp 
              local outE::DAE.Exp

              outE = traverseExpDummy(e, stripNoEventExp)
          outE
        end

         #= 
        traversal function for stripNoEvent =#
        function stripNoEventExp(e::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                @match e begin
                  DAE.CALL(path = Absyn.IDENT("noEvent"), expLst = outExp <|  nil())  => begin
                    outExp
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          outExp
        end

         #= Function that adds a noEvent() call to all relations in an expression =#
        function addNoEventToRelations(e::DAE.Exp) ::DAE.Exp 
              local outE::DAE.Exp

              outE = traverseExpDummy(e, addNoEventToRelationExp)
          outE
        end

         #= 
        traversal function for addNoEventToRelations =#
        function addNoEventToRelationExp(e::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                @match e begin
                  DAE.RELATION(__)  => begin
                    makeNoEvent(e)
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          outExp
        end

         #= Function that adds a noEvent() call to all relations in an expression =#
        function addNoEventToRelationsAndConds(e::DAE.Exp) ::DAE.Exp 
              local outE::DAE.Exp

              outE = traverseExpDummy(e, addNoEventToRelationandCondExp)
          outE
        end

         #= 
        traversal function for addNoEventToRelationsAndConds =#
        function addNoEventToRelationandCondExp(e::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                @match e begin
                  DAE.RELATION(__)  => begin
                    makeNoEvent(e)
                  end
                  
                  DAE.IFEXP(e1, e2, e3)  => begin
                    DAE.IFEXP(makeNoEvent(e1), e2, e3)
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          outExp
        end

         #=  Function that adds a noEvent() call to all event triggering functions in an expression =#
        function addNoEventToEventTriggeringFunctions(e::DAE.Exp) ::DAE.Exp 
              local outE::DAE.Exp

              outE = traverseExpDummy(e, addNoEventToEventTriggeringFunctionsExp)
          outE
        end

         #= 
        traversal function for addNoEventToEventTriggeringFunctions =#
        function addNoEventToEventTriggeringFunctionsExp(e::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                @match e begin
                  DAE.CALL(__) where (isEventTriggeringFunctionExp(e))  => begin
                    makeNoEvent(e)
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          outExp
        end

         #= Strips the last subscripts of a Exp =#
        function expStripLastSubs(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local cr::ComponentRef
                  local cr_1::ComponentRef
                  local ty::Type
                  local op::Operator
                  local op1::Operator
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local b::Bool
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                      ty = ComponentReference.crefLastType(cr)
                      cr_1 = ComponentReference.crefStripLastSubs(cr)
                      e = makeCrefExp(cr_1, ty)
                    e
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                      e_1 = expStripLastSubs(e)
                      ty = typeof(e_1)
                      b = DAEUtil.expTypeArray(ty)
                      op1 = if b
                            DAE.UMINUS_ARR(ty)
                          else
                            DAE.UMINUS(ty)
                          end
                    DAE.UNARY(op1, e_1)
                  end
                end
              end
          outExp
        end

         #= Strips the last identifier of a cref Exp =#
        function expStripLastIdent(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local cr::ComponentRef
                  local cr_1::ComponentRef
                  local ty::Type
                  local op::Operator
                  local op1::Operator
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local b::Bool
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                      cr_1 = ComponentReference.crefStripLastIdent(cr)
                      ty = ComponentReference.crefLastType(cr_1)
                      e = makeCrefExp(cr_1, ty)
                    e
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                      e_1 = expStripLastIdent(e)
                      ty = typeof(e_1)
                      b = DAEUtil.expTypeArray(ty)
                      op1 = if b
                            DAE.UMINUS_ARR(ty)
                          else
                            DAE.UMINUS(ty)
                          end
                    DAE.UNARY(op1, e_1)
                  end
                end
              end
          outExp
        end

         #= Prepends a subscript to a CREF expression
         For instance a.b[1,2] with subscript 'i' becomes a.b[i,1,2]. =#
        function prependSubscriptExp(exp::DAE.Exp, subscr::DAE.Subscript) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local t::Type
                  local cr::ComponentRef
                  local cr1::ComponentRef
                  local cr2::ComponentRef
                  local subs::List{DAE.Subscript}
                  local e::DAE.Exp
                @match (exp, subscr) begin
                  (DAE.CREF(cr, t), _)  => begin
                      cr1 = ComponentReference.crefStripLastSubs(cr)
                      subs = ComponentReference.crefLastSubs(cr)
                      cr2 = ComponentReference.subscriptCref(cr1, _cons(subscr, subs))
                      e = makeCrefExp(cr2, t)
                    e
                  end
                end
              end
          outExp
        end

         #= 
        author: PA
        Takes an arbitrary expression and applies subscripts to it. This is done by creating asub
        expressions given the original expression and then simplify them.
        Note: The subscripts must be INDEX

        alternative names: subsriptExp (but already taken), subscriptToAsub =#
        function applyExpSubscripts(exp::DAE.Exp, inSubs::List{<:DAE.Subscript}) ::DAE.Exp 


              local s::DAE.Exp

              exp = applyExpSubscriptsFoldCheckSimplify(exp, inSubs)
          exp
        end

         #= 
        author: PA
        Takes an arbitrary expression and applies subscripts to it. This is done by creating asub
        expressions given the original expression and then simplify them.
        Note: The subscripts must be INDEX

        alternative names: subsriptExp (but already taken), subscriptToAsub

        This version of the function also returns a boolean stating if simplify
        improved anything (can be used as a heuristic if you want to apply
        the subscript when scalarizing) =#
        function applyExpSubscriptsFoldCheckSimplify(exp::DAE.Exp, inSubs::List{<:DAE.Subscript}, checkSimplify::Bool = false) ::Tuple{DAE.Exp, Bool} 



              local b::Bool
              local s::DAE.Exp

              for sub in inSubs
                try
                  s = getSubscriptExp(sub)
                  (exp, b) = ExpressionSimplify.simplify(makeASUB(exp, list(s)))
                  checkSimplify = b || checkSimplify
                catch
                end
              end
               #=  Apply one subscript at a time, so simplify works fine on it.
               =#
               #= s := subscriptIndexExp(sub);
               =#
               #=  skipped DAE.WHOLEDIM
               =#
          (exp, checkSimplify)
        end

         #= @mahge
          This function does the same job as 'applyExpSubscripts' function.
          However this one doesn't use ExpressionSimplify.simplify.


          Takes an expression and a list of subscripts and subscripts
          the given expression.
          If a component reference is given the subs are applied to it.
          If an array(DAE.ARRAY) is given the element at the specified
          subscripts is returned.
          e.g. subscriptExp on ({{1,2},{3,4}}) with sub [2,1] gives 3
               subscriptExp on (a) with sub [2,1] gives a[2,1]

         =#
        function subscriptExp(inExp::DAE.Exp, inSubs::List{<:DAE.Subscript}) ::DAE.Exp 
              local outArg::DAE.Exp

              outArg = begin
                  local cref::DAE.ComponentRef
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local explst::List{DAE.Exp}
                  local sub::DAE.Subscript
                  local restsubs::List{DAE.Subscript}
                  local op::DAE.Operator
                  local str::String
                @match (inExp, inSubs) begin
                  (_,  nil())  => begin
                    inExp
                  end
                  
                  (DAE.CREF(cref, ty), _)  => begin
                      cref = ComponentReference.subscriptCref(cref, inSubs)
                    DAE.CREF(cref, ty)
                  end
                  
                  (DAE.ARRAY(_, _, explst), sub <| restsubs)  => begin
                      exp = listGet(explst, subscriptInt(sub))
                    subscriptExp(exp, restsubs)
                  end
                  
                  (DAE.BINARY(exp1, op, exp2), _)  => begin
                      exp1 = subscriptExp(exp1, inSubs)
                      exp2 = subscriptExp(exp2, inSubs)
                    DAE.BINARY(exp1, op, exp2)
                  end
                  
                  (DAE.CAST(ty, exp1), _)  => begin
                      exp1 = subscriptExp(exp1, inSubs)
                      ty = Types.arrayElementType(ty)
                      exp1 = DAE.CAST(ty, exp1)
                    exp1
                  end
                  
                  _  => begin
                        str = "Expression.subscriptExp failed on " + ExpressionDump.printExpStr(inExp) + "\\n"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
          outArg
        end

         #= Converts an array type into its element type
          See also Types.unliftArray.
          . =#
        function unliftArray(inType::DAE.Type) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local tp::Type
                  local t::Type
                  local d::DAE.Dimension
                  local ds::DAE.Dimensions
                @match inType begin
                  DAE.T_ARRAY(ty = tp, dims = _ <|  nil())  => begin
                    tp
                  end
                  
                  DAE.T_ARRAY(ty = tp, dims = _ <| ds)  => begin
                    DAE.T_ARRAY(tp, ds)
                  end
                  
                  DAE.T_METATYPE(ty = tp)  => begin
                    Types.simplifyType(unliftArray(tp))
                  end
                  
                  DAE.T_METAARRAY(ty = tp)  => begin
                    tp
                  end
                  
                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

        function unliftArrayIgnoreFirst(a::A, inType::DAE.Type) ::DAE.Type 
              local outType::DAE.Type

              outType = unliftArray(inType)
          outType
        end

        function unliftExp(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local ty::Type
                  local cr::DAE.ComponentRef
                  local s::Bool
                  local a::List{DAE.Exp}
                  local i::ModelicaInteger
                  local mat::List{List{DAE.Exp}}
                  local expCref::DAE.Exp
                @match inExp begin
                  DAE.CREF(componentRef = cr, ty = ty)  => begin
                      ty = unliftArray(ty)
                      expCref = makeCrefExp(cr, ty)
                    expCref
                  end
                  
                  DAE.ARRAY(ty = ty, scalar = s, array = a)  => begin
                      ty = unliftArray(ty)
                    DAE.ARRAY(ty, s, a)
                  end
                  
                  DAE.MATRIX(ty = ty, integer = i, matrix = mat)  => begin
                      ty = unliftArray(ty)
                    DAE.MATRIX(ty, i, mat)
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

        function liftExp(inExp::DAE.Exp, inDimension::DAE.Dimension) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = DAE.ARRAY(Types.liftArray(typeof(inExp), inDimension), false, ListUtil.fill(inExp, dimensionSize(inDimension)))
          outExp
        end

        function liftExpList(inExp::DAE.Exp, inDimensions::List{<:DAE.Dimension}) ::DAE.Exp 
              local outExp::DAE.Exp = inExp

              for dim in listReverse(inDimensions)
                outExp = liftExp(outExp, dim)
              end
          outExp
        end

         #= 
        This function adds an array dimension to a type on the right side, i.e.
        liftArrayRigth(Real[2,3],SOME(4)) => Real[2,3,4].
        This function has the same functionality as Types.liftArrayType but for DAE.Type.' =#
        function liftArrayRight(inType::DAE.Type, inDimension::DAE.Dimension) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty_1::Type
                  local ty::Type
                  local dims::DAE.Dimensions
                  local dim::DAE.Dimension
                @match (inType, inDimension) begin
                  (DAE.T_ARRAY(ty, dims), dim)  => begin
                      ty_1 = liftArrayRight(ty, dim)
                    DAE.T_ARRAY(ty_1, dims)
                  end
                  
                  _  => begin
                      DAE.T_ARRAY(inType, list(inDimension))
                  end
                end
              end
          outType
        end

         #= 
        author: PA
        This function adds an array dimension to a type on the left side, i.e.
        liftArrayRigth(Real[2,3],SOME(4)) => Real[4,2,3] =#
        function liftArrayLeft(inType::DAE.Type, inDimension::DAE.Dimension) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local dims::DAE.Dimensions
                  local dim::DAE.Dimension
                @match (inType, inDimension) begin
                  (DAE.T_ARRAY(ty, dims), dim)  => begin
                    DAE.T_ARRAY(ty, _cons(dim, dims))
                  end
                  
                  _  => begin
                      DAE.T_ARRAY(inType, list(inDimension))
                  end
                end
              end
          outType
        end

        function liftArrayLeftList(inType::DAE.Type, inDimensions::List{<:DAE.Dimension}) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local dims::DAE.Dimensions
                @match (inType, inDimensions) begin
                  (_,  nil())  => begin
                    inType
                  end
                  
                  (DAE.T_ARRAY(ty, dims), _)  => begin
                      dims = listAppend(inDimensions, dims)
                    DAE.T_ARRAY(ty, dims)
                  end
                  
                  _  => begin
                      DAE.T_ARRAY(inType, inDimensions)
                  end
                end
              end
          outType
        end

         #= Sets the type of an operator. =#
        function setOpType(inOp::DAE.Operator, inType::DAE.Type) ::DAE.Operator 
              local outOp::DAE.Operator

              outOp = begin
                @match (inOp, inType) begin
                  (DAE.ADD(__), _)  => begin
                    DAE.ADD(inType)
                  end
                  
                  (DAE.SUB(__), _)  => begin
                    DAE.SUB(inType)
                  end
                  
                  (DAE.MUL(__), _)  => begin
                    DAE.MUL(inType)
                  end
                  
                  (DAE.DIV(__), _)  => begin
                    DAE.DIV(inType)
                  end
                  
                  (DAE.POW(__), _)  => begin
                    DAE.POW(inType)
                  end
                  
                  (DAE.UMINUS(__), _)  => begin
                    DAE.UMINUS(inType)
                  end
                  
                  (DAE.UMINUS_ARR(__), _)  => begin
                    DAE.UMINUS_ARR(inType)
                  end
                  
                  (DAE.ADD_ARR(__), _)  => begin
                    DAE.ADD_ARR(inType)
                  end
                  
                  (DAE.SUB_ARR(__), _)  => begin
                    DAE.SUB_ARR(inType)
                  end
                  
                  (DAE.MUL_ARR(__), _)  => begin
                    DAE.MUL_ARR(inType)
                  end
                  
                  (DAE.DIV_ARR(__), _)  => begin
                    DAE.DIV_ARR(inType)
                  end
                  
                  (DAE.MUL_ARRAY_SCALAR(__), _)  => begin
                    DAE.MUL_ARRAY_SCALAR(inType)
                  end
                  
                  (DAE.ADD_ARRAY_SCALAR(__), _)  => begin
                    DAE.ADD_ARRAY_SCALAR(inType)
                  end
                  
                  (DAE.SUB_SCALAR_ARRAY(__), _)  => begin
                    DAE.SUB_SCALAR_ARRAY(inType)
                  end
                  
                  (DAE.MUL_SCALAR_PRODUCT(__), _)  => begin
                    DAE.MUL_SCALAR_PRODUCT(inType)
                  end
                  
                  (DAE.MUL_MATRIX_PRODUCT(__), _)  => begin
                    DAE.MUL_MATRIX_PRODUCT(inType)
                  end
                  
                  (DAE.DIV_ARRAY_SCALAR(__), _)  => begin
                    DAE.DIV_ARRAY_SCALAR(inType)
                  end
                  
                  (DAE.DIV_SCALAR_ARRAY(__), _)  => begin
                    DAE.DIV_SCALAR_ARRAY(inType)
                  end
                  
                  (DAE.POW_ARRAY_SCALAR(__), _)  => begin
                    DAE.POW_ARRAY_SCALAR(inType)
                  end
                  
                  (DAE.POW_SCALAR_ARRAY(__), _)  => begin
                    DAE.POW_SCALAR_ARRAY(inType)
                  end
                  
                  (DAE.POW_ARR(__), _)  => begin
                    DAE.POW_ARR(inType)
                  end
                  
                  (DAE.POW_ARR2(__), _)  => begin
                    DAE.POW_ARR2(inType)
                  end
                  
                  (DAE.AND(__), _)  => begin
                    DAE.AND(inType)
                  end
                  
                  (DAE.OR(__), _)  => begin
                    DAE.OR(inType)
                  end
                  
                  (DAE.NOT(__), _)  => begin
                    DAE.NOT(inType)
                  end
                  
                  (DAE.LESS(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.LESSEQ(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.GREATER(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.GREATEREQ(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.EQUAL(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.NEQUAL(__), _)  => begin
                    inOp
                  end
                  
                  (DAE.USERDEFINED(__), _)  => begin
                    inOp
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Expression.setOpType failed on unknown operator")
                      fail()
                  end
                end
              end
          outOp
        end

         #= Unlifts the type of an operator by removing one dimension from the operator
           type. The operator is changed to the scalar version if the type becomes a
           scalar type. =#
        function unliftOperator(inOperator::DAE.Operator) ::DAE.Operator 
              local outOperator::DAE.Operator

              local ty::Type

              ty = typeofOp(inOperator)
              ty = unliftArray(ty)
              outOperator = unliftOperator2(inOperator, ty)
          outOperator
        end

         #= Unlifts the type of an operator by removing X dimensions from the operator
           type. The operator is changed to the scalar version if the type becomes a
           scalar type. =#
        function unliftOperatorX(inOperator::DAE.Operator, inX::ModelicaInteger) ::DAE.Operator 
              local outOperator::DAE.Operator

              local ty::Type

              ty = typeofOp(inOperator)
              ty = unliftArrayX(ty, inX)
              outOperator = unliftOperator2(inOperator, ty)
          outOperator
        end

         #= Helper function to unliftOperator. Sets the type of the given operator, and
           changes the operator to the scalar version if the type is scalar. =#
        function unliftOperator2(inOperator::DAE.Operator, inType::DAE.Type) ::DAE.Operator 
              local outOperator::DAE.Operator

              outOperator = begin
                @match (inOperator, inType) begin
                  (_, DAE.T_ARRAY(__))  => begin
                    setOpType(inOperator, inType)
                  end
                  
                  _  => begin
                      makeScalarOpFromArrayOp(inOperator, inType)
                  end
                end
              end
          outOperator
        end

         #= Helper function to makeScalarOpFromArrayOp. Returns the scalar version of a
           given array operator. =#
        function makeScalarOpFromArrayOp(inOperator::DAE.Operator, inType::DAE.Type) ::DAE.Operator 
              local outOperator::DAE.Operator

              outOperator = begin
                @match (inOperator, inType) begin
                  (DAE.MUL_ARRAY_SCALAR(__), _)  => begin
                    DAE.MUL(inType)
                  end
                  
                  (DAE.ADD_ARRAY_SCALAR(__), _)  => begin
                    DAE.ADD(inType)
                  end
                  
                  (DAE.SUB_SCALAR_ARRAY(__), _)  => begin
                    DAE.SUB(inType)
                  end
                  
                  (DAE.DIV_ARRAY_SCALAR(__), _)  => begin
                    DAE.DIV(inType)
                  end
                  
                  (DAE.DIV_SCALAR_ARRAY(__), _)  => begin
                    DAE.DIV(inType)
                  end
                  
                  (DAE.POW_ARRAY_SCALAR(__), _)  => begin
                    DAE.POW(inType)
                  end
                  
                  (DAE.POW_SCALAR_ARRAY(__), _)  => begin
                    DAE.POW(inType)
                  end
                  
                  (DAE.UMINUS_ARR(__), _)  => begin
                    DAE.UMINUS(inType)
                  end
                  
                  (DAE.ADD_ARR(__), _)  => begin
                    DAE.ADD(inType)
                  end
                  
                  (DAE.SUB_ARR(__), _)  => begin
                    DAE.SUB(inType)
                  end
                  
                  (DAE.MUL_ARR(__), _)  => begin
                    DAE.MUL(inType)
                  end
                  
                  (DAE.DIV_ARR(__), _)  => begin
                    DAE.DIV(inType)
                  end
                  
                  _  => begin
                      inOperator
                  end
                end
              end
          outOperator
        end

         #= Returns true if the operator takes a scalar and an array as arguments. =#
        function isScalarArrayOp(inOperator::DAE.Operator) ::Bool 
              local outIsScalarArrayOp::Bool

              outIsScalarArrayOp = begin
                @match inOperator begin
                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    true
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    true
                  end
                  
                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsScalarArrayOp
        end

         #= Returns true if the operator takes an array and a scalar as arguments. =#
        function isArrayScalarOp(inOperator::DAE.Operator) ::Bool 
              local outIsArrayScalarOp::Bool

              outIsArrayScalarOp = begin
                @match inOperator begin
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
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsArrayScalarOp
        end

         #= This function takes a subscript list and adds a new subscript.
          But there are a few special cases.  When the last existing
          subscript is a slice, it is replaced by the slice indexed by
          the new subscript. =#
        function subscriptsAppend(inSubscriptLst::List{<:DAE.Subscript}, inSubscript::DAE.Exp) ::List{DAE.Subscript} 
              local outSubscriptLst::List{DAE.Subscript}

              outSubscriptLst = begin
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local s::Subscript
                  local ss_1::List{DAE.Subscript}
                  local ss::List{DAE.Subscript}
                @match (inSubscriptLst, inSubscript) begin
                  ( nil(), _)  => begin
                    list(DAE.INDEX(inSubscript))
                  end
                  
                  (DAE.WHOLEDIM(__) <| ss, _)  => begin
                    _cons(DAE.INDEX(inSubscript), ss)
                  end
                  
                  (DAE.SLICE(exp = e) <|  nil(), _)  => begin
                      (e_1, _) = ExpressionSimplify.simplify1(makeASUB(e, list(inSubscript)))
                    list(DAE.INDEX(e_1))
                  end
                  
                  (s && DAE.INDEX(__) <|  nil(), _)  => begin
                    list(s, DAE.INDEX(inSubscript))
                  end
                  
                  (s <| ss, _)  => begin
                      ss_1 = subscriptsAppend(ss, inSubscript)
                    _cons(s, ss_1)
                  end
                end
              end
          outSubscriptLst
        end

         #= Replaces the first slice subscript in the given list with the given subscript. =#
        function subscriptsReplaceSlice(inSubscripts::List{<:DAE.Subscript}, inSubscript::DAE.Subscript) ::List{DAE.Subscript} 
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = begin
                  local rest_subs::List{DAE.Subscript}
                  local sub::DAE.Subscript
                @match (inSubscripts, inSubscript) begin
                  (DAE.WHOLEDIM(__) <| rest_subs, _)  => begin
                    _cons(inSubscript, rest_subs)
                  end
                  
                  (DAE.SLICE(__) <| rest_subs, _)  => begin
                    _cons(inSubscript, rest_subs)
                  end
                  
                  (sub <| rest_subs, _)  => begin
                      rest_subs = subscriptsReplaceSlice(rest_subs, inSubscript)
                    _cons(sub, rest_subs)
                  end
                end
              end
          outSubscripts
        end

         #= 
        helper function for renameVarsToUnderlineVar2 unlifts array type as much as we have subscripts =#
        function unliftArrayTypeWithSubs(subs::List{<:DAE.Subscript}, ity::DAE.Type) ::DAE.Type 
              local oty::DAE.Type

              oty = begin
                  local rest::List{DAE.Subscript}
                  local ty::Type
                @match (subs, ity) begin
                  ( nil(), ty)  => begin
                    ty
                  end
                  
                  (_ <| rest, ty)  => begin
                      ty = unliftArray(ty)
                      ty = unliftArrayTypeWithSubs(rest, ty)
                    ty
                  end
                end
              end
          oty
        end

         #= Function: unliftArrayX
        Unlifts a type with X dimensions... =#
        function unliftArrayX(inType::DAE.Type, x::ModelicaInteger) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                @match (inType, x) begin
                  (_, 0)  => begin
                    inType
                  end
                  
                  _  => begin
                        ty = unliftArray(inType)
                      unliftArrayX(ty, x - 1)
                  end
                end
              end
          outType
        end

         #= Appends a new element to a DAE.ARRAY. =#
        function arrayAppend(head::DAE.Exp, rest::DAE.Exp) ::DAE.Exp 
              local array::DAE.Exp

              array = begin
                  local ty::DAE.Type
                  local scalar::Bool
                  local expl::List{DAE.Exp}
                  local dim::ModelicaInteger
                  local dims::DAE.Dimensions
                @match (head, rest) begin
                  (_, DAE.ARRAY(DAE.T_ARRAY(ty = ty, dims = DAE.DIM_INTEGER(dim) <| dims), scalar, expl))  => begin
                      dim = dim + 1
                      dims = _cons(DAE.DIM_INTEGER(dim), dims)
                    DAE.ARRAY(DAE.T_ARRAY(ty, dims), scalar, _cons(head, expl))
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Expression.arrayAppend failed.")
                      fail()
                  end
                end
              end
          array
        end

         #= Updates the first dimension of an array type. =#
        function arrayDimensionSetFirst(inArrayType::DAE.Type, dimension::DAE.Dimension) ::DAE.Type 
              local outArrayType::DAE.Type

              outArrayType = begin
                  local ty::DAE.Type
                  local rest_dims::DAE.Dimensions
                @match (inArrayType, dimension) begin
                  (DAE.T_ARRAY(ty = ty, dims = _ <| rest_dims), _)  => begin
                    DAE.T_ARRAY(ty, _cons(dimension, rest_dims))
                  end
                end
              end
          outArrayType
        end

         #= /***************************************************/ =#
         #= /* Getter  */ =#
         #= /***************************************************/ =#

         #= Returns the value of a constant Real expression. =#
        function toReal(inExp::DAE.Exp) ::ModelicaReal 
              local outReal::ModelicaReal

              outReal = begin
                @match inExp begin
                  DAE.RCONST(__)  => begin
                    inExp.real
                  end
                  
                  DAE.ICONST(__)  => begin
                    intReal(inExp.integer)
                  end
                  
                  DAE.CAST(__)  => begin
                    toReal(inExp.exp)
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    intReal(inExp.index)
                  end
                end
              end
          outReal
        end

         #= Returns the value of a constant Boolean expression. =#
        function toBool(inExp::DAE.Exp) ::Bool 
              local outBool::Bool

              @match DAE.BCONST(outBool) = inExp
          outBool
        end

         #= returns the int value if expression is constant Real that can be represented by an Integer =#
        function realExpIntLit(exp::DAE.Exp) ::Option{ModelicaInteger} 
              local oi::Option{ModelicaInteger}

              oi = begin
                  local r::ModelicaReal
                  local i::ModelicaInteger
                  local op::Option{ModelicaInteger}
                @match exp begin
                  DAE.RCONST(real = r)  => begin
                      i = realInt(r)
                      op = if realEq(r, intReal(i))
                            SOME(i)
                          else
                            NONE()
                          end
                    op
                  end
                  
                  _  => begin
                      NONE()
                  end
                end
              end
          oi
        end

         #= returns the int value if expression is constant Integer =#
        function expInt(exp::DAE.Exp) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                @match exp begin
                  DAE.ICONST(__)  => begin
                    exp.integer
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    exp.index
                  end
                  
                  DAE.BCONST(__)  => begin
                    if exp.bool
                          1
                        else
                          0
                        end
                  end
                end
              end
          i
        end

         #= Returns a real interval expression for any clock kind; 0.0 if unknown. =#
        function getClockInterval(inClk::DAE.ClockKind) ::DAE.Exp 
              local outIntvl::DAE.Exp

              local e::DAE.Exp
              local e2::DAE.Exp
              local res::ModelicaInteger

              outIntvl = begin
                @match inClk begin
                  DAE.REAL_CLOCK(e)  => begin
                    e
                  end
                  
                  DAE.INTEGER_CLOCK(e, e2)  => begin
                    DAE.BINARY(DAE.CAST(DAE.T_REAL_DEFAULT, e), DAE.DIV(DAE.T_REAL_DEFAULT), DAE.CAST(DAE.T_REAL_DEFAULT, e2))
                  end
                  
                  DAE.BOOLEAN_CLOCK(e, e2)  => begin
                    e2
                  end
                  
                  _  => begin
                      DAE.RCONST(0.0)
                  end
                end
              end
               #=  startInterval
               =#
          outIntvl
        end

         #= Returns the array index that an expression represents as an integer. =#
        function expArrayIndex(inExp::DAE.Exp) ::ModelicaInteger 
              local outIndex::ModelicaInteger

              outIndex = begin
                @match inExp begin
                  DAE.ICONST(__)  => begin
                    inExp.integer
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    inExp.index
                  end
                  
                  DAE.BCONST(__)  => begin
                    if inExp.bool
                          2
                        else
                          1
                        end
                  end
                end
              end
          outIndex
        end

        function sconstEnumNameString(exp::DAE.Exp) ::String 
              local str::String

              str = begin
                  local s::String
                  local name::Absyn.Path
                @match exp begin
                  DAE.SCONST(s)  => begin
                    s
                  end
                  
                  DAE.ENUM_LITERAL(name)  => begin
                    AbsynUtil.pathString(name)
                  end
                end
              end
          str
        end

         #= Returns the name of a Var =#
        function varName(v::DAE.Var) ::String 
              local name::String

              name = begin
                @match v begin
                  DAE.TYPES_VAR(name = name)  => begin
                    name
                  end
                end
              end
          name
        end

         #= Returns the type of a Var =#
        function varType(v::DAE.Var) ::DAE.Type 
              local tp::DAE.Type

              tp = begin
                @match v begin
                  DAE.TYPES_VAR(ty = tp)  => begin
                    tp
                  end
                end
              end
          tp
        end

         #= Returns the componentref if DAE.Exp is a CREF or DER(CREF) =#
        function expOrDerCref(inExp::DAE.Exp) ::Tuple{DAE.ComponentRef, Bool} 
              local isDer::Bool
              local outComponentRef::DAE.ComponentRef

              (outComponentRef, isDer) = begin
                  local cr::ComponentRef
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                    (cr, false)
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "der"), expLst = DAE.CREF(cr, _) <|  nil())  => begin
                    (cr, true)
                  end
                end
              end
          (outComponentRef, isDer)
        end

         #= Returns the componentref if DAE.Exp is a CREF, =#
        function expCref(inExp::DAE.Exp) ::DAE.ComponentRef 
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local cr::ComponentRef
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                    cr
                  end
                end
              end
          outComponentRef
        end

         #= Returns the componentref if DAE.Exp is a CREF or -CREF =#
        function expCrefNegCref(inExp::DAE.Exp) ::DAE.ComponentRef 
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local cr::ComponentRef
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                    cr
                  end
                  
                  DAE.UNARY(DAE.UMINUS(_), DAE.CREF(componentRef = cr))  => begin
                    cr
                  end
                  
                  DAE.UNARY(DAE.UMINUS_ARR(_), DAE.CREF(componentRef = cr))  => begin
                    cr
                  end
                end
              end
          outComponentRef
        end

         #= Returns the componentref if the expression in inTuple is a CREF. =#
        function expCrefTuple(inTuple::Tuple{<:DAE.Exp, Bool}) ::DAE.ComponentRef 
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local cr::ComponentRef
                @match inTuple begin
                  (DAE.CREF(componentRef = cr), _)  => begin
                    cr
                  end
                end
              end
          outComponentRef
        end

         #= Returns the componentref if DAE.Exp is a CREF, or the factors of CREF if expression is an if expression.
          This is used in e.g. the tearing algorithm to detect potential division by zero in
          expressions like 1/(if b then 1.0 else x) which could lead to division by zero if b is false and x is 0;  =#
        function expCrefInclIfExpFactors(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local outComponentRefs::List{DAE.ComponentRef}

              outComponentRefs = begin
                  local cr::ComponentRef
                  local c::DAE.Exp
                  local tb::DAE.Exp
                  local fb::DAE.Exp
                  local f::List{DAE.Exp}
                  local crefs::List{DAE.ComponentRef}
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                    list(cr)
                  end
                  
                  DAE.IFEXP(_, tb, fb)  => begin
                      f = ListUtil.select(listAppend(factors(tb), factors(fb)), isCref)
                      crefs = ListUtil.map(f, expCref)
                    crefs
                  end
                end
              end
          outComponentRefs
        end

         #= returns the list of expressions in the array =#
        function getArrayContents(e::DAE.Exp) ::List{DAE.Exp} 
              local es::List{DAE.Exp}

              @match DAE.ARRAY(array = es) = e
          es
        end

         #= Returns the contents of an array or matrix as a list of expressions. =#
        function getArrayOrMatrixContents(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outContents::List{DAE.Exp}

              outContents = begin
                  local expl::List{DAE.Exp}
                  local mat::List{List{DAE.Exp}}
                  local ty::DAE.Type
                  local el_ty::DAE.Type
                  local dims::DAE.Dimensions
                  local sc::Bool
                @match inExp begin
                  DAE.ARRAY(array = expl)  => begin
                    expl
                  end
                  
                  DAE.MATRIX(ty = DAE.T_ARRAY(el_ty, _ <| dims), matrix = mat)  => begin
                      ty = DAE.T_ARRAY(el_ty, dims)
                      sc = Types.basicType(el_ty)
                    ListUtil.map2(mat, makeArray, ty, sc)
                  end
                end
              end
          outContents
        end

         #= makes all asubs for the complete dimension of the exp. =#
        function makeASUBsForDimension(eIn::DAE.Exp) ::List{DAE.Exp} 
              local eLstOut::List{DAE.Exp} = nil

              local size::ModelicaInteger
              local dims::DAE.Dimensions

              dims = expDimensions(eIn)
              try
                @match list(DAE.DIM_INTEGER(integer = size)) = dims
                for i in size:(-1):1
                  eLstOut = _cons(makeASUBSingleSub(eIn, DAE.ICONST(i)), eLstOut)
                end
              catch
                eLstOut = nil
              end
          eLstOut
        end

         #= returns the list of expressions from a complex structure like array,record,call,tuple...
        author:Waurich TUD 2014-04 =#
        function getComplexContents(e::DAE.Exp) ::List{DAE.Exp} 
              local es::List{DAE.Exp}

              es = begin
                  local noArr::Bool
                  local cref::DAE.ComponentRef
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local ty::DAE.Type
                  local expLst::List{DAE.Exp}
                  local expLst1::List{DAE.Exp}
                  local expLst2::List{DAE.Exp}
                  local expLstLst::List{List{DAE.Exp}}
                  local crefs::List{DAE.ComponentRef}
                @matchcontinue e begin
                  DAE.CREF(__)  => begin
                      expLst = arrayElements(e)
                      noArr = listLength(expLst) == 1
                      exp = listHead(expLst)
                      noArr = noArr && expEqual(exp, e)
                      expLst = if noArr
                            nil
                          else
                            expLst
                          end
                    expLst
                  end
                  
                  DAE.BINARY(exp1 = exp1, operator = DAE.ADD_ARR(__), exp2 = exp2)  => begin
                      if isArray(exp1)
                        expLst1 = getComplexContents(exp1)
                      else
                        expLst1 = makeASUBsForDimension(exp1)
                      end
                      if isArray(exp2)
                        expLst2 = getComplexContents(exp2)
                      else
                        expLst2 = makeASUBsForDimension(exp2)
                      end
                      ty = typeof(listHead(expLst1))
                      expLst = ListUtil.threadMap(expLst1, expLst2, (DAE.ADD(ty)) -> makeBinaryExp(inOp = DAE.ADD(ty)))
                    expLst
                  end
                  
                  DAE.CALL(expLst = expLst)  => begin
                      expLstLst = ListUtil.map(expLst, getComplexContentsInCall)
                      expLst = ListUtil.flatten(expLstLst)
                    expLst
                  end
                  
                  DAE.RECORD(exps = expLst)  => begin
                    expLst
                  end
                  
                  DAE.ARRAY(__)  => begin
                      expLst = arrayElements(e)
                    expLst
                  end
                  
                  DAE.MATRIX(matrix = expLstLst)  => begin
                      expLst = ListUtil.flatten(expLstLst)
                    expLst
                  end
                  
                  DAE.TUPLE(PR = expLst)  => begin
                    expLst
                  end
                  
                  DAE.CAST(exp = exp)  => begin
                      expLst = getComplexContents(exp)
                    expLst
                  end
                  
                  DAE.ASUB(exp = exp)  => begin
                      expLst = getComplexContents(exp)
                    expLst
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
               #= print(\"complexed expLst1:\\n\"+ExpressionDump.printExpListStr(expLst1)+\"\\n\");
               =#
               #= print(\"complexed expLst2:\\n\"+ExpressionDump.printExpListStr(expLst2)+\"\\n\");
               =#
          es
        end

         #= gets the scalars for the complex expressions inside a function call =#
        function getComplexContentsInCall(expIn::DAE.Exp) ::List{DAE.Exp} 
              local expsOut::List{DAE.Exp}

              local expLst::List{DAE.Exp}

              expLst = getComplexContents(expIn)
              expsOut = if listEmpty(expLst)
                    list(expIn)
                  else
                    expLst
                  end
          expsOut
        end

         #= returns the list of expressions in the array =#
        function getArrayOrRangeContents(e::DAE.Exp) ::List{DAE.Exp} 
              local es::List{DAE.Exp}

              es = begin
                  local bstart::Bool
                  local bstop::Bool
                  local istart::ModelicaInteger
                  local istep::ModelicaInteger
                  local istop::ModelicaInteger
                  local rstart::ModelicaReal
                  local rstep::ModelicaReal
                  local rstop::ModelicaReal
                  local matrix::List{List{DAE.Exp}}
                  local ty::DAE.Type
                @match e begin
                  DAE.ARRAY(array = es)  => begin
                    es
                  end
                  
                  DAE.MATRIX(matrix = matrix, ty = ty)  => begin
                      ty = Types.unliftArray(ty)
                      es = ListUtil.map2(matrix, makeArray, ty, ! Types.arrayType(ty))
                    es
                  end
                  
                  DAE.CREF(ty = DAE.T_ARRAY(dims = DAE.DIM_INTEGER(istop) <| _))  => begin
                      es = ListUtil.map(ExpressionSimplify.simplifyRange(1, 1, istop), makeIntegerExp)
                      es = ListUtil.map1r(es, makeASUBSingleSub, e)
                    es
                  end
                  
                  DAE.RANGE(DAE.T_BOOL(__), DAE.BCONST(bstart), NONE(), DAE.BCONST(bstop))  => begin
                    ListUtil.map(ExpressionSimplify.simplifyRangeBool(bstart, bstop), makeBoolExp)
                  end
                  
                  DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), NONE(), DAE.ICONST(istop))  => begin
                    ListUtil.map(ExpressionSimplify.simplifyRange(istart, 1, istop), makeIntegerExp)
                  end
                  
                  DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), SOME(DAE.ICONST(istep)), DAE.ICONST(istop))  => begin
                    ListUtil.map(ExpressionSimplify.simplifyRange(istart, istep, istop), makeIntegerExp)
                  end
                  
                  DAE.RANGE(DAE.T_REAL(__), DAE.RCONST(rstart), NONE(), DAE.RCONST(rstop))  => begin
                    ListUtil.map(ExpressionSimplify.simplifyRangeReal(rstart, 1.0, rstop), makeRealExp)
                  end
                  
                  DAE.RANGE(DAE.T_REAL(__), DAE.RCONST(rstart), SOME(DAE.RCONST(rstep)), DAE.RCONST(rstop))  => begin
                    ListUtil.map(ExpressionSimplify.simplifyRangeReal(rstart, rstep, rstop), makeRealExp)
                  end
                end
              end
          es
        end

         #= returns the list of expressions in the array =#
        function get2dArrayOrMatrixContent(e::DAE.Exp) ::List{List{DAE.Exp}} 
              local outExps::List{List{DAE.Exp}}

              outExps = begin
                  local es::List{DAE.Exp}
                  local ess::List{List{DAE.Exp}}
                @match e begin
                  DAE.ARRAY(array = es)  => begin
                    ListUtil.map(es, getArrayContents)
                  end
                  
                  DAE.MATRIX(matrix = ess)  => begin
                    ess
                  end
                end
              end
          outExps
        end

         #=  stefan
         =#

         #= takes a type, and if it is boxed, unbox it
          otherwise return the given type =#
        function unboxExpType(inType::DAE.Type) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                @match inType begin
                  DAE.T_METABOXED(ty = ty)  => begin
                    ty
                  end
                  
                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= takes an expression and unboxes it if it is boxed =#
        function unboxExp(ie::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                @match ie begin
                  DAE.BOX(e)  => begin
                    unboxExp(e)
                  end
                  
                  _  => begin
                      ie
                  end
                end
              end
          outExp
        end

         #= takes an expression and boxes it =#
        function boxExp(e::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                @match e begin
                  DAE.BOX(_)  => begin
                    e
                  end
                  
                  _  => begin
                      DAE.BOX(e)
                  end
                end
              end
          outExp
        end

         #= Returns the expression in a subscript index.
          If the subscript is not an index the function fails. =#
        function subscriptIndexExp(inSubscript::DAE.Subscript) ::DAE.Exp 
              local outExp::DAE.Exp

              @match DAE.INDEX(exp = outExp) = inSubscript
          outExp
        end

         #= Returns the subscript expression, or fails on DAE.WHOLEDIM. =#
        function getSubscriptExp(inSubscript::DAE.Subscript) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                @match inSubscript begin
                  DAE.SLICE(exp = e)  => begin
                    e
                  end
                  
                  DAE.INDEX(exp = e)  => begin
                    e
                  end
                  
                  DAE.WHOLE_NONEXP(exp = e)  => begin
                    e
                  end
                end
              end
          outExp
        end

         #= Returns the expression in a subscript representing non-expanded array.
          If the subscript is not WHOLE_NONEXP the function fails. =#
        function subscriptNonExpandedExp(inSubscript::DAE.Subscript) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                @match inSubscript begin
                  DAE.WHOLE_NONEXP(exp = e)  => begin
                    e
                  end
                end
              end
          outExp
        end

         #= Returns true if the given subscript is the first index for a dimension, i.e.
           1, false or the first enumeration literal in an enumeration. =#
        function subscriptIsFirst(inSubscript::DAE.Subscript) ::Bool 
              local outIsFirst::Bool

              outIsFirst = begin
                @match inSubscript begin
                  DAE.INDEX(exp = DAE.ICONST(1))  => begin
                    true
                  end
                  
                  DAE.INDEX(exp = DAE.BCONST(false))  => begin
                    true
                  end
                  
                  DAE.INDEX(exp = DAE.ENUM_LITERAL(index = 1))  => begin
                    true
                  end
                end
              end
          outIsFirst
        end

         #= author: PA
          Returns the nth expression of an array expression. =#
        function nthArrayExp(inExp::DAE.Exp, inInteger::ModelicaInteger) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local expl::List{DAE.Exp}
                  local op::Operator
                  local ty::Type
                @matchcontinue inExp begin
                  DAE.BINARY(operator = op, exp1 = e1, exp2 = e2)  => begin
                      ty = typeofOp(op)
                      @match true = Types.isArray(ty)
                      e_1 = nthArrayExp(e1, inInteger)
                      e_2 = nthArrayExp(e2, inInteger)
                    DAE.BINARY(e_1, op, e_2)
                  end
                  
                  DAE.ARRAY(array = expl)  => begin
                      e1 = listGet(expl, inInteger)
                    e1
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= Return the last subscripts of a Exp =#
        function expLastSubs(inExp::DAE.Exp) ::List{DAE.Subscript} 
              local outSubscriptLst::List{DAE.Subscript}

              outSubscriptLst = begin
                  local cr::ComponentRef
                  local subs::List{DAE.Subscript}
                  local e::DAE.Exp
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                      subs = ComponentReference.crefLastSubs(cr)
                    subs
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                      subs = expLastSubs(e)
                    subs
                  end
                end
              end
          outSubscriptLst
        end

         #= Tries to return the dimensions from an expression, typically an array. =#
        function expDimensions(inExp::DAE.Exp) ::DAE.Dimensions 
              local outDims::DAE.Dimensions

              outDims = begin
                  local tp::DAE.Type
                  local e::Exp
                @match inExp begin
                  DAE.ARRAY(ty = tp)  => begin
                    arrayDimension(tp)
                  end
                  
                  DAE.MATRIX(ty = tp)  => begin
                    arrayDimension(tp)
                  end
                  
                  DAE.LUNARY(exp = e)  => begin
                    expDimensions(e)
                  end
                  
                  DAE.LBINARY(exp1 = e)  => begin
                    expDimensions(e)
                  end
                  
                  DAE.CALL(attr = DAE.CALL_ATTR(ty = tp))  => begin
                    arrayDimension(tp)
                  end
                end
              end
          outDims
        end

         #= 
        Author BZ
        Get dimension of array.
         =#
        function arrayDimension(tp::DAE.Type) ::DAE.Dimensions 
              local dims::DAE.Dimensions

              dims = begin
                @match tp begin
                  DAE.T_ARRAY(dims = dims)  => begin
                    dims
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          dims
        end

         #= Return the array dimensions of a type. =#
        function arrayTypeDimensions(tp::DAE.Type) ::DAE.Dimensions 
              local dims::DAE.Dimensions

              dims = begin
                @match tp begin
                  DAE.T_ARRAY(dims = dims)  => begin
                    dims
                  end
                end
              end
          dims
        end

         #= Converts a list of subscript to a list of dimensions. =#
        function subscriptDimensions(inSubscripts::List{<:DAE.Subscript}) ::DAE.Dimensions 
              local outDimensions::DAE.Dimensions

              outDimensions = ListUtil.map(inSubscripts, subscriptDimension)
          outDimensions
        end

         #= Converts a subscript to a dimension by interpreting the subscript as a
           dimension. =#
        function subscriptDimension(inSubscript::DAE.Subscript) ::DAE.Dimension 
              local outDimension::DAE.Dimension

              outDimension = begin
                  local x::ModelicaInteger
                  local e::DAE.Exp
                  local sub_str::String
                @match inSubscript begin
                  DAE.INDEX(exp = DAE.ICONST(x))  => begin
                    DAE.DIM_INTEGER(x)
                  end
                  
                  DAE.INDEX(exp = e)  => begin
                    DAE.DIM_EXP(e)
                  end
                  
                  DAE.WHOLEDIM(__)  => begin
                    DAE.DIM_UNKNOWN()
                  end
                  
                  DAE.WHOLE_NONEXP(exp = DAE.ICONST(x)) where (! Config.splitArrays())  => begin
                    DAE.DIM_INTEGER(x)
                  end
                  
                  DAE.WHOLE_NONEXP(exp = e) where (! Config.splitArrays())  => begin
                    DAE.DIM_EXP(e)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        sub_str = ExpressionDump.subscriptString(inSubscript)
                        Debug.traceln("- Expression.subscriptDimension failed on " + sub_str)
                      fail()
                  end
                end
              end
               #=  Special cases for non-expanded arrays
               =#
          outDimension
        end

         #=  Returns the element type of an array expression. =#
        function arrayEltType(inType::DAE.Type) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local t::Type
                @match inType begin
                  DAE.T_ARRAY(ty = t)  => begin
                    arrayEltType(t)
                  end
                  
                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= Returns the size of an ET_ARRAY or ET_COMPLEX =#
        function sizeOf(inType::DAE.Type) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                  local ad::DAE.Dimensions
                  local nr::ModelicaInteger
                  local lstInt::List{ModelicaInteger}
                  local varLst::List{Var}
                  local typs::List{DAE.Type}
                  local ty::Type
                   #=  count the variables in array
                   =#
                @matchcontinue inType begin
                  DAE.T_ARRAY(dims = ad)  => begin
                      nr = dimensionSize(ListUtil.reduce(ad, dimensionsMult))
                      nr = nr * sizeOf(inType.ty)
                    nr
                  end
                  
                  DAE.T_COMPLEX(varLst = varLst)  => begin
                      lstInt = ListUtil.mapMap(varLst, varType, sizeOf)
                      nr = ListUtil.reduce(lstInt, intAdd)
                    nr
                  end
                  
                  DAE.T_TUPLE(types = typs)  => begin
                      nr = ListUtil.applyAndFold(typs, intAdd, sizeOf, 0)
                    nr
                  end
                  
                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    sizeOf(ty)
                  end
                  
                  DAE.T_METATYPE(ty = ty)  => begin
                    sizeOf(ty)
                  end
                  
                  DAE.T_UNKNOWN(__)  => begin
                    0
                  end
                  
                  _  => begin
                      1
                  end
                end
              end
               #=  count the variables in record
               =#
               #= /* Size of Enumeration is 1 like a Integer
                  case DAE.T_ENUMERATION(index=NONE(),names=strlst)
                    then
                      listLength(strlst);
              */ =#
               #=  0 for T_UNKNOWN as it can only appear in tuples for WILD()??!!
               =#
               #=  for all other consider it just 1 variable
               =#
          i
        end

         #= Extracts an integer from an array dimension =#
        function dimensionSize(dim::DAE.Dimension) ::ModelicaInteger 
              local value::ModelicaInteger

              value = begin
                  local i::ModelicaInteger
                @match dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    i
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    i
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    2
                  end
                  
                  DAE.DIM_EXP(exp = DAE.ICONST(integer = i))  => begin
                    i
                  end
                  
                  DAE.DIM_EXP(exp = DAE.ENUM_LITERAL(index = i))  => begin
                    i
                  end
                end
              end
          value
        end

        function addDimensions(dim1::DAE.Dimension, dim2::DAE.Dimension) ::DAE.Dimension 
              local dim::DAE.Dimension

              dim = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i::ModelicaInteger
                @matchcontinue (dim1, dim2) begin
                  (_, _)  => begin
                      i = dimensionSize(dim1) + dimensionSize(dim2)
                    DAE.DIM_INTEGER(i)
                  end
                  
                  _  => begin
                      DAE.DIM_UNKNOWN()
                  end
                end
              end
          dim
        end

         #= Extracts an integer from an array dimension. Also handles DIM_EXP and
          DIM_UNKNOWN if checkModel is used. =#
        function dimensionSizeAll(dim::DAE.Dimension) ::ModelicaInteger 
              local value::ModelicaInteger

              value = begin
                  local i::ModelicaInteger
                  local e::DAE.Exp
                @matchcontinue dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    i
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    i
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    2
                  end
                  
                  DAE.DIM_EXP(exp = e)  => begin
                    expInt(e)
                  end
                  
                  DAE.DIM_EXP(__)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                    0
                  end
                  
                  DAE.DIM_UNKNOWN(__)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                    0
                  end
                end
              end
          value
        end

         #= Extracts a list of integers from a list of array dimensions =#
        function dimensionsSizes(inDims::DAE.Dimensions) ::List{ModelicaInteger} 
              local outValues::List{ModelicaInteger}

              outValues = ListUtil.map(inDims, dimensionSizeAll)
          outValues
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
                      msg = "- Expression.typeof failed for " + ExpressionDump.printExpStr(e)
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

         #= Boolean or array of boolean =#
        function typeofRelation(inType::DAE.Type) ::DAE.Type 
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local ty1::Type
                  local dims::DAE.Dimensions
                @match inType begin
                  DAE.T_ARRAY(ty = ty, dims = dims)  => begin
                      _ = typeofRelation(ty)
                    DAE.T_ARRAY(ty, dims)
                  end
                  
                  _  => begin
                      DAE.T_BOOL_DEFAULT
                  end
                end
              end
          outType
        end

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

         #= Retrieve all function sub expressions in an expression. =#
        function getRelations(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

              outExpLst = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cond::DAE.Exp
                  local tb::DAE.Exp
                  local fb::DAE.Exp
                  local rellst1::List{DAE.Exp}
                  local rellst2::List{DAE.Exp}
                  local rellst::List{DAE.Exp}
                  local rellst3::List{DAE.Exp}
                  local rellst4::List{DAE.Exp}
                  local xs::List{DAE.Exp}
                  local t::Type
                  local sc::Bool
                @match inExp begin
                  e && DAE.RELATION(__)  => begin
                    list(e)
                  end
                  
                  DAE.LBINARY(exp1 = e1, exp2 = e2)  => begin
                      rellst1 = getRelations(e1)
                      rellst2 = getRelations(e2)
                      rellst = listAppend(rellst1, rellst2)
                    rellst
                  end
                  
                  DAE.LUNARY(exp = e)  => begin
                      rellst = getRelations(e)
                    rellst
                  end
                  
                  DAE.BINARY(exp1 = e1, exp2 = e2)  => begin
                      rellst1 = getRelations(e1)
                      rellst2 = getRelations(e2)
                      rellst = listAppend(rellst1, rellst2)
                    rellst
                  end
                  
                  DAE.IFEXP(expCond = cond, expThen = tb, expElse = fb)  => begin
                      rellst1 = getRelations(cond)
                      rellst2 = getRelations(tb)
                      rellst3 = getRelations(fb)
                      rellst4 = listAppend(rellst1, rellst2)
                      rellst = listAppend(rellst3, rellst4)
                    rellst
                  end
                  
                  DAE.ARRAY(array = e <|  nil())  => begin
                      rellst = getRelations(e)
                    rellst
                  end
                  
                  DAE.ARRAY(ty = t, scalar = sc, array = e <| xs)  => begin
                      rellst1 = getRelations(DAE.ARRAY(t, sc, xs))
                      rellst2 = getRelations(e)
                      rellst = listAppend(rellst1, rellst2)
                    rellst
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                      rellst = getRelations(e)
                    rellst
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outExpLst
        end

         #= author: lochel
          This function extracts all crefs from the input expression, except 'time'. =#
        function getAllCrefs(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local outCrefs::List{DAE.ComponentRef}

              (_, outCrefs) = traverseExpBottomUp(inExp, getAllCrefs2, nil)
          outCrefs
        end

        function getAllCrefs2(inExp::DAE.Exp, inCrefList::List{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, List{DAE.ComponentRef}} 
              local outCrefList::List{DAE.ComponentRef} = inCrefList
              local outExp::DAE.Exp = inExp

              local cr::DAE.ComponentRef

              if isCref(inExp)
                @match DAE.CREF(componentRef = cr) = inExp
                if ! ComponentReference.crefEqual(cr, DAE.crefTime) && ! listMember(cr, inCrefList)
                  outCrefList = _cons(cr, outCrefList)
                end
              end
          (outExp, outCrefList)
        end

         #= author: ptaeuber
          This function extracts all crefs from the input expression (except 'time') and expands arrays and records. =#
        function getAllCrefsExpanded(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local outCrefs::List{DAE.ComponentRef}

              (_, outCrefs) = traverseExpBottomUp(inExp, getAllCrefsExpanded2, nil)
          outCrefs
        end

        function getAllCrefsExpanded2(inExp::DAE.Exp, inCrefList::List{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, List{DAE.ComponentRef}} 
              local outCrefList::List{DAE.ComponentRef} = inCrefList
              local outExp::DAE.Exp = inExp

              local cr::DAE.ComponentRef
              local crlst::List{DAE.ComponentRef}

              if isCref(inExp)
                @match DAE.CREF(componentRef = cr) = inExp
                crlst = ComponentReference.expandCref(cr, true)
                for c in crlst
                  if ! ComponentReference.crefEqual(c, DAE.crefTime) && ! listMember(c, inCrefList)
                    outCrefList = _cons(c, outCrefList)
                  end
                end
              end
          (outExp, outCrefList)
        end

         #= similar to terms, but also performs expansion of
         multiplications to reveal more terms, like for instance:
         allTerms((a+b)*(b+c)) => {a*b,a*c,b*b,b*c} =#
        function allTerms(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

              outExpLst = begin
                  local f1::List{DAE.Exp}
                  local f2::List{DAE.Exp}
                  local res::List{DAE.Exp}
                  local f2_1::List{DAE.Exp}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local tp::Type
                  local cr::ComponentRef
                @matchcontinue inExp begin
                  DAE.BINARY(exp1 = e1, operator = DAE.ADD(__), exp2 = e2)  => begin
                      f1 = allTerms(e1)
                      f2 = allTerms(e2)
                      res = listAppend(f1, f2)
                    res
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.SUB(__), exp2 = e2)  => begin
                      f1 = allTerms(e1)
                      f2 = allTerms(e2)
                      f2_1 = ListUtil.map(f2, negate)
                      res = listAppend(f1, f2_1)
                    res
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.ADD_ARR(__), exp2 = e2)  => begin
                      f1 = allTerms(e1)
                      f2 = allTerms(e2)
                      res = listAppend(f1, f2)
                    res
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.SUB_ARR(__), exp2 = e2)  => begin
                      f1 = allTerms(e1)
                      f2 = allTerms(e2)
                      f2_1 = ListUtil.map(f2, negate)
                      res = listAppend(f1, f2_1)
                    res
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e2)
                      f1 = ListUtil.map1(f1, makeProduct, e1)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.MUL_ARR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e2)
                      f1 = ListUtil.map1(f1, makeProduct, e1)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.MUL_ARRAY_SCALAR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e2)
                      f1 = ListUtil.map1(f1, makeProduct, e1)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, makeProduct, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.MUL_ARR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, makeProduct, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.MUL_ARRAY_SCALAR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, makeProduct, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.DIV(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, expDiv, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.DIV_ARR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, expDiv, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.DIV_ARRAY_SCALAR(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, expDiv, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.BINARY(e1, DAE.DIV_SCALAR_ARRAY(_), e2)  => begin
                      @match (@match _cons(_, _cons(_, _)) = f1) = allTerms(e1)
                      f1 = ListUtil.map1(f1, expDiv, e2)
                      f1 = ListUtil.flatten(ListUtil.map(f1, allTerms))
                    f1
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS(__), exp = e1)  => begin
                      f1 = allTerms(e1)
                      f1 = ListUtil.map(f1, negate)
                    f1
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e1)  => begin
                      f1 = allTerms(e1)
                      f1 = ListUtil.map(f1, negate)
                    f1
                  end
                  
                  DAE.LUNARY(operator = DAE.NOT(__), exp = e1)  => begin
                      f1 = allTerms(e1)
                      f1 = ListUtil.map(f1, negate)
                    f1
                  end
                  
                  DAE.ASUB(exp = e1, sub = f2)  => begin
                      f1 = allTerms(e1)
                      f1 = ListUtil.map1(f1, makeASUB, f2)
                    f1
                  end
                  
                  _  => begin
                      list(inExp)
                  end
                end
              end
               #=  terms( a*(b+c)) => {a*b, c*b}
               =#
               #=  terms( (b+c)*a) => {b*a, c*a}
               =#
               #=  terms( (b+c)/a) => {b/a, c/a}
               =#
               #= /*
                  case (e as DAE.BINARY(operator = DAE.MUL())) then {e};
                  case (e as DAE.BINARY(operator = DAE.MUL_ARR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.MUL_ARRAY_SCALAR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.DIV())) then {e};
                  case (e as DAE.BINARY(operator = DAE.DIV_ARR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.DIV_ARRAY_SCALAR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.DIV_SCALAR_ARRAY())) then {e};
                  case (e as DAE.BINARY(operator = DAE.POW())) then {e};
                  case (e as DAE.BINARY(operator = DAE.POW_ARR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.POW_ARR2())) then {e};
                  case (e as DAE.BINARY(operator = DAE.POW_ARRAY_SCALAR())) then {e};
                  case (e as DAE.BINARY(operator = DAE.POW_SCALAR_ARRAY())) then {e};
                  case (e as DAE.CREF()) then {e};
                  case (e as DAE.ICONST()) then {e};
                  case (e as DAE.RCONST()) then {e};
                  case (e as DAE.SCONST()) then {e};
                  case ((e as DAE.ENUM_LITERAL())) then {e};
                  case (e as DAE.UNARY()) then {e};
                  case (e as DAE.IFEXP()) then {e};
                  case (e as DAE.CALL()) then {e};
                  case (e as DAE.RECORD()) then {e};
                  case (e as DAE.PARTEVALFUNCTION()) then {e};
                  case (e as DAE.ARRAY()) then {e};
                  case (e as DAE.MATRIX()) then {e};
                  case (e as DAE.RANGE()) then {e};
                  case (e as DAE.CAST()) then {e};
                  case (e as DAE.ASUB()) then {e};
                  case (e as DAE.SIZE()) then {e};
                  case (e as DAE.REDUCTION()) then {e};
              */ =#
          outExpLst
        end

         #= simliar to terms, but also perform expansion of
         multiplications to reveal more terms, like for instance:
         allTerms((a(x)+b(x))*(c+d)) => {a(x)*(c+d),b(x)*(c+d)} =#
        function allTermsForCref(inExp::DAE.Exp, cr::DAE.ComponentRef #= x =#, inFunc::MapFunc) ::Tuple{List{DAE.Exp}, List{DAE.Exp}} 
              local outExpLstWithoutX::List{DAE.Exp}
              local outExpLstWithX::List{DAE.Exp}

              (outExpLstWithX, outExpLstWithoutX) = begin
                  local f1::List{DAE.Exp}
                  local f2::List{DAE.Exp}
                  local fx1::List{DAE.Exp}
                  local fx2::List{DAE.Exp}
                  local res::List{DAE.Exp}
                  local resx::List{DAE.Exp}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local tp::Type
                @matchcontinue inExp begin
                  DAE.BINARY(exp1 = e1, operator = DAE.ADD(__), exp2 = e2)  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx2, f2) = allTermsForCref(e2, cr, inFunc)
                      res = listAppend(f1, f2)
                      resx = listAppend(fx1, fx2)
                    (resx, res)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.SUB(__), exp2 = e2)  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx2, f2) = allTermsForCref(e2, cr, inFunc)
                      f2 = ListUtil.map(f2, negate)
                      fx2 = ListUtil.map(fx2, negate)
                      res = listAppend(f1, f2)
                      resx = listAppend(fx1, fx2)
                    (resx, res)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.ADD_ARR(__), exp2 = e2)  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx2, f2) = allTermsForCref(e2, cr, inFunc)
                      res = listAppend(f1, f2)
                      resx = listAppend(fx1, fx2)
                    (resx, res)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.SUB_ARR(__), exp2 = e2)  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx2, f2) = allTermsForCref(e2, cr, inFunc)
                      f2 = ListUtil.map(f2, negate)
                      fx2 = ListUtil.map(fx2, negate)
                      res = listAppend(f1, f2)
                      resx = listAppend(fx1, fx2)
                    (resx, res)
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(_), e2) where (inFunc(e2, cr))  => begin
                      (fx1, f1) = allTermsForCref(e2, cr, inFunc)
                      (fx1, f2) = ListUtil.split1OnTrue(fx1, inFunc, cr)
                      res = listAppend(f1, f2)
                      e = makeSum1(res)
                      e = expMul(e, e1)
                      fx1 = ListUtil.map1(fx1, expMul, e1)
                      if ! isZero(e)
                        if expHasCrefNoPreOrStart(e1, cr)
                          fx1 = _cons(e, fx1)
                          f1 = nil
                        else
                          f1 = list(e)
                        end
                      end
                    (fx1, f1)
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(_), e2) where (inFunc(e1, cr))  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx1, f2) = ListUtil.split1OnTrue(fx1, inFunc, cr)
                      res = listAppend(f1, f2)
                      e = makeSum1(res)
                      e = expMul(e, e2)
                      fx1 = ListUtil.map1(fx1, expMul, e2)
                      if ! isZero(e)
                        if expHasCrefNoPreOrStart(e1, cr)
                          fx1 = _cons(e, fx1)
                          f1 = nil
                        else
                          f1 = list(e)
                        end
                      end
                    (fx1, f1)
                  end
                  
                  DAE.BINARY(e1, DAE.DIV(_), e2) where (inFunc(e1, cr))  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      (fx1, f2) = ListUtil.split1OnTrue(fx1, inFunc, cr)
                      res = listAppend(f1, f2)
                      e = makeSum1(res)
                      e = makeDiv(e, e2)
                      fx1 = ListUtil.map1(fx1, makeDiv, e2)
                      if ! isZero(e)
                        if expHasCrefNoPreOrStart(e1, cr)
                          fx1 = _cons(e, fx1)
                          f1 = nil
                        else
                          f1 = list(e)
                        end
                      end
                    (fx1, f1)
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS(__), exp = e1)  => begin
                      (fx1, f1) = allTermsForCref(e1, cr, inFunc)
                      f1 = ListUtil.map(f1, negate)
                      fx1 = ListUtil.map(fx1, negate)
                    (fx1, f1)
                  end
                  
                  _  => begin
                        if inFunc(inExp, cr)
                          res = nil
                          resx = list(inExp)
                        else
                          resx = nil
                          res = list(inExp)
                        end
                      (resx, res)
                  end
                end
              end
          (outExpLstWithX, outExpLstWithoutX)
        end

         #= Returns the terms of the expression if any as a list of expressions =#
        function termsExpandUnary(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

              outExpLst = begin
                  local e::DAE.Exp
                @match inExp begin
                  DAE.UNARY(operator = DAE.UMINUS(__), exp = e)  => begin
                    ListUtil.map(terms(e), negate)
                  end
                  
                  _  => begin
                      terms(inExp)
                  end
                end
              end
          outExpLst
        end

         #= Returns the terms of the expression if any as a list of expressions =#
        function terms(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

              outExpLst = terms2(inExp, nil, false)
          outExpLst
        end

         #= Returns the terms of the expression if any as a list of expressions =#
        function terms2(inExp::DAE.Exp, inAcc::List{<:DAE.Exp}, neg::Bool) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

              outExpLst = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local acc::List{DAE.Exp}
                @match (inExp, inAcc, neg) begin
                  (DAE.BINARY(exp1 = e1, operator = DAE.ADD(__), exp2 = e2), acc, _)  => begin
                      acc = terms2(e2, acc, neg)
                      acc = terms2(e1, acc, neg)
                    acc
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.SUB(__), exp2 = e2), acc, _)  => begin
                      acc = terms2(e2, acc, ! neg)
                      acc = terms2(e1, acc, neg)
                    acc
                  end
                  
                  (e, acc, true)  => begin
                      e = negate(e)
                    _cons(e, acc)
                  end
                  
                  (e, acc, _)  => begin
                    _cons(e, acc)
                  end
                end
              end
          outExpLst
        end

         #= author: PA
          Returns the quotient of an expression.
          For instance e = p/q returns (p,q) for numerator p and denominator q. =#
        function quotient(inExp::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp} 
              local denom::DAE.Exp
              local num::DAE.Exp

              (num, denom) = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local p::DAE.Exp
                  local q::DAE.Exp
                  local tp::Type
                @matchcontinue inExp begin
                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(__), exp2 = e2)  => begin
                    (e1, e2)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2)  => begin
                      (p, q) = quotient(e1)
                      tp = typeof(p)
                    (DAE.BINARY(e2, DAE.MUL(tp), p), q)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2)  => begin
                      (p, q) = quotient(e2)
                      tp = typeof(p)
                    (DAE.BINARY(e1, DAE.MUL(tp), p), q)
                  end
                end
              end
               #= /* (numerator,denominator) */ =#
          (num, denom)
        end

         #= Returns the factors of the expression if any as a list of expressions =#
        function factors(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

               #=  TODO: Remove this listReverse as it is pointless.
               =#
               #=  It transforms a*b to b*a, but the testsuite expects this :(
               =#
              outExpLst = listReverse(factorsWork(inExp, nil, false))
          outExpLst
        end

         #= Returns the factors of the expression if any as a list of expressions =#
        function factorsWork(inExp::DAE.Exp, acc::List{<:DAE.Exp}, doInverseFactors::Bool #= Decides if a factor e should be 1/e instead =#) ::List{DAE.Exp} 


              acc = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                @match inExp begin
                  DAE.BINARY(exp1 = e1, operator = DAE.MUL(__), exp2 = e2)  => begin
                      acc = factorsWork(e1, acc, doInverseFactors)
                      acc = factorsWork(e2, acc, doInverseFactors)
                    acc
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = DAE.T_REAL(__)), exp2 = e2)  => begin
                      acc = factorsWork(e1, acc, doInverseFactors)
                      acc = factorsWork(e2, acc, ! doInverseFactors)
                    acc
                  end
                  
                  DAE.ICONST(integer = 1)  => begin
                    acc
                  end
                  
                  DAE.RCONST(real = 1.0)  => begin
                    acc
                  end
                  
                  _  => begin
                      _cons(if doInverseFactors
                            inverseFactors(inExp)
                          else
                            inExp
                          end, acc)
                  end
                end
              end
               #=  case DAE.UNARY()  factor(-(x*y)) is -(x*y) ??
               =#
          acc
        end

         #= each expression in the list inversed.
          For example: inverseFactors {a, 3+b} => {1/a, 1/3+b} =#
        function inverseFactors(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local tp2::Type
                  local tp::Type
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local op::DAE.Operator
                   #=  e1^e2 =>e1^(-e2)
                   =#
                @matchcontinue inExp begin
                  DAE.BINARY(exp1 = e1, operator = DAE.POW(ty = tp), exp2 = e2)  => begin
                      tp2 = typeof(e2)
                    DAE.BINARY(e1, DAE.POW(tp), DAE.UNARY(DAE.UMINUS(tp2), e2))
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = op && DAE.DIV(__), exp2 = e2)  => begin
                      @match false = isZero(e1)
                    DAE.BINARY(e2, op, e1)
                  end
                  
                  e  => begin
                      @match false = isZero(e)
                      tp = typeof(e)
                      e = begin
                        @match tp begin
                          DAE.T_REAL(__)  => begin
                            DAE.BINARY(DAE.RCONST(1.0), DAE.DIV(DAE.T_REAL_DEFAULT), e)
                          end
                          
                          DAE.T_INTEGER(__)  => begin
                            DAE.BINARY(DAE.ICONST(1), DAE.DIV(DAE.T_INTEGER_DEFAULT), e)
                          end
                        end
                      end
                    e
                  end
                end
              end
               #=  e1 / e2 = e2 / e1
               =#
          outExp
        end

         #= 
         Returns the factors of the expression if any as a list of expressions.
         e.g.
         -(x*(x*y)^n) -> {-1,x,x^n,x^n}
         =#
        function expandFactors(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp}

               #=  TODO: Remove this listReverse as it is pointless.
               =#
               #=  It transforms a*b to b*a, but the testsuite expects this :(
               =#
               #=  issue with expEqual(a*b,b*a) return false
               =#
              outExpLst = listReverse(expandFactorsWork(inExp, nil, false))
          outExpLst
        end

         #= Returns the factors of the expression if any as a list of expressions =#
        function expandFactorsWork(inExp::DAE.Exp, acc::List{<:DAE.Exp}, doInverseFactors::Bool #= Decides if a factor e should be 1/e instead =#) ::List{DAE.Exp} 


              acc = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e::DAE.Exp
                  local tp::Type
                  local pow_acc::List{DAE.Exp}
                  local pow_acc2::List{DAE.Exp}
                  local op::Operator
                   #=  (x*y)^n = x^n*y^n
                   =#
                @match inExp begin
                  DAE.BINARY(DAE.BINARY(e1, DAE.MUL(__), e2), DAE.POW(__), e3)  => begin
                      pow_acc = expandFactorsWork(e1, nil, doInverseFactors)
                      pow_acc = expPowLst(pow_acc, e3)
                      pow_acc2 = expandFactorsWork(e2, nil, doInverseFactors)
                      pow_acc2 = expPowLst(pow_acc2, e3)
                      acc = listAppend(pow_acc, acc)
                      acc = listAppend(pow_acc2, acc)
                    acc
                  end
                  
                  DAE.BINARY(DAE.BINARY(e1, DAE.DIV(__), e2), DAE.POW(__), e3)  => begin
                      pow_acc = expandFactorsWork(e1, nil, doInverseFactors)
                      pow_acc = expPowLst(pow_acc, e3)
                      pow_acc2 = expandFactorsWork(e2, nil, doInverseFactors)
                      pow_acc2 = expPowLst(pow_acc2, negate(e3))
                      acc = listAppend(pow_acc, acc)
                      acc = listAppend(pow_acc2, acc)
                    acc
                  end
                  
                  DAE.BINARY(DAE.BINARY(e1, DAE.POW(__), e2), DAE.POW(__), e3)  => begin
                      e = expMul(e2, e3)
                      pow_acc = expandFactorsWork(e1, nil, doInverseFactors)
                      pow_acc = expPowLst(pow_acc, e)
                      acc = listAppend(pow_acc, acc)
                    acc
                  end
                  
                  DAE.BINARY(e1, op && DAE.DIV(tp), e2) where (isZero(e2))  => begin
                       #=  (x/y)^n = x^n*y^(-n)
                       =#
                       #=  (x^n)^m = x^(n*m)
                       =#
                       #=  ToDo
                       =#
                       #=  exp(x + y) = exp(x)*exp(y)
                       =#
                       #=  exp(x - y) = exp(x)/exp(y)
                       =#
                       #=  abs(x*y) = abs(x)*abs(y)
                       =#
                       #=  abs(x/y) = abs(x)/abs(y);
                       =#
                       #=  x/0 = x * 1/0
                       =#
                      if doInverseFactors
                        e = e2
                      else
                        e = DAE.BINARY(makeConstOne(tp), op, e2)
                      end
                      acc = expandFactorsWork(e1, acc, doInverseFactors)
                    _cons(e, acc)
                  end
                  
                  DAE.UNARY(DAE.UMINUS(tp), e1)  => begin
                      e = makeConstOne(tp)
                      acc = expandFactorsWork(e1, acc, doInverseFactors)
                      e = negate(e)
                    _cons(e, acc)
                  end
                  
                  DAE.UNARY(DAE.UMINUS_ARR(tp), e1)  => begin
                      e = makeConstOne(tp)
                      acc = expandFactorsWork(e1, acc, doInverseFactors)
                      e = negate(e)
                    _cons(e, acc)
                  end
                  
                  _  => begin
                        acc = expandFactorsWork3(inExp, acc, doInverseFactors)
                      expandFactorsWork2(acc, doInverseFactors)
                  end
                end
              end
               #=  -(x) = -1*x
               =#
          acc
        end

        function expandFactorsWork3(inExp::DAE.Exp, acc::List{<:DAE.Exp}, doInverseFactors::Bool #= Decides if a factor e should be 1/e instead =#) ::List{DAE.Exp} 


              local e1::DAE.Exp
              local e2::DAE.Exp
              local e::DAE.Exp
              local op::Operator

              acc = begin
                @matchcontinue inExp begin
                  _  => begin
                    factorsWork(inExp, acc, doInverseFactors)
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(__), e2)  => begin
                      acc = expandFactorsWork(e1, acc, doInverseFactors)
                      acc = expandFactorsWork(e2, acc, doInverseFactors)
                    acc
                  end
                  
                  DAE.BINARY(DAE.BINARY(e, op && DAE.DIV(__), e1), DAE.DIV(__), e2)  => begin
                      e = DAE.BINARY(e, op, expMul(e1, e2))
                      acc = expandFactorsWork(e, acc, doInverseFactors)
                    acc
                  end
                  
                  DAE.BINARY(DAE.BINARY(e, DAE.MUL(__), e1), op && DAE.DIV(__), e2)  => begin
                      acc = expandFactorsWork(e, acc, doInverseFactors)
                      acc = expandFactorsWork(DAE.BINARY(e1, op, e2), acc, doInverseFactors)
                    acc
                  end
                  
                  _  => begin
                    _cons(inExp, acc)
                  end
                end
              end
               #= equation
               =#
               #=   print(\"\\ninExp*: \");print(ExpressionDump.printExpStr(inExp));
               =#
          acc
        end

        function expandFactorsWork2(inAcc::List{<:DAE.Exp}, doInverseFactors::Bool #= Decides if a factor e should be 1/e instead =#) ::List{DAE.Exp} 
              local outExpLst::List{DAE.Exp} = nil

              local tmpExpLst::List{DAE.Exp}

              for elem in inAcc
                tmpExpLst = begin
                  @match elem begin
                    DAE.BINARY(DAE.BINARY(_, DAE.DIV(__), _), DAE.POW(__), _)  => begin
                      expandFactorsWork(elem, nil, doInverseFactors)
                    end
                    
                    DAE.BINARY(DAE.BINARY(_, DAE.MUL(__), _), DAE.POW(__), _)  => begin
                      expandFactorsWork(elem, nil, doInverseFactors)
                    end
                    
                    DAE.BINARY(DAE.BINARY(_, DAE.POW(__), _), DAE.POW(__), _)  => begin
                      expandFactorsWork(elem, nil, doInverseFactors)
                    end
                    
                    DAE.UNARY(DAE.UMINUS(__), _)  => begin
                      expandFactorsWork(elem, nil, doInverseFactors)
                    end
                    
                    DAE.UNARY(DAE.UMINUS_ARR(__), _)  => begin
                      expandFactorsWork(elem, nil, doInverseFactors)
                    end
                    
                    _  => begin
                        list(elem)
                    end
                  end
                end
                outExpLst = listAppend(tmpExpLst, outExpLst)
              end
          outExpLst
        end

         #= Retrieves all terms of an expression containing a variable,
          given as second argument (in the form of an Exp) =#
        function getTermsContainingX(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp} 
              local outExp2::DAE.Exp
              local outExp1::DAE.Exp

              (outExp1, outExp2) = begin
                  local xt1::DAE.Exp
                  local nonxt1::DAE.Exp
                  local xt2::DAE.Exp
                  local nonxt2::DAE.Exp
                  local xt::DAE.Exp
                  local nonxt::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cr::DAE.Exp
                  local e::DAE.Exp
                  local zero::DAE.Exp
                  local ty::Type
                  local res::Bool
                @matchcontinue (inExp1, inExp2) begin
                  (DAE.BINARY(exp1 = e1, operator = DAE.ADD(ty = ty), exp2 = e2), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e1, cr)
                      (xt2, nonxt2) = getTermsContainingX(e2, cr)
                      xt = DAE.BINARY(xt1, DAE.ADD(ty), xt2)
                      nonxt = DAE.BINARY(nonxt1, DAE.ADD(ty), nonxt2)
                    (xt, nonxt)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.SUB(ty = ty), exp2 = e2), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e1, cr)
                      (xt2, nonxt2) = getTermsContainingX(e2, cr)
                      xt = DAE.BINARY(xt1, DAE.SUB(ty), xt2)
                      nonxt = DAE.BINARY(nonxt1, DAE.SUB(ty), nonxt2)
                    (xt, nonxt)
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS(ty = ty), exp = e), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e, cr)
                      xt = DAE.UNARY(DAE.UMINUS(ty), xt1)
                      nonxt = DAE.UNARY(DAE.UMINUS(ty), nonxt1)
                    (xt, nonxt)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.ADD_ARR(ty = ty), exp2 = e2), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e1, cr)
                      (xt2, nonxt2) = getTermsContainingX(e2, cr)
                      xt = DAE.BINARY(xt1, DAE.ADD_ARR(ty), xt2)
                      nonxt = DAE.BINARY(nonxt1, DAE.ADD_ARR(ty), nonxt2)
                    (xt, nonxt)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.SUB_ARR(ty = ty), exp2 = e2), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e1, cr)
                      (xt2, nonxt2) = getTermsContainingX(e2, cr)
                      xt = DAE.BINARY(xt1, DAE.SUB_ARR(ty), xt2)
                      nonxt = DAE.BINARY(nonxt1, DAE.SUB_ARR(ty), nonxt2)
                    (xt, nonxt)
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS_ARR(ty = ty), exp = e), cr && DAE.CREF(__))  => begin
                      (xt1, nonxt1) = getTermsContainingX(e, cr)
                      xt = DAE.UNARY(DAE.UMINUS_ARR(ty), xt1)
                      nonxt = DAE.UNARY(DAE.UMINUS_ARR(ty), nonxt1)
                    (xt, nonxt)
                  end
                  
                  (e, cr && DAE.CREF(ty = ty))  => begin
                      res = expContains(e, cr)
                      (zero, _) = makeZeroExpression(arrayDimension(ty))
                      xt = if res
                            e
                          else
                            zero
                          end
                      nonxt = if res
                            zero
                          else
                            e
                          end
                    (xt, nonxt)
                  end
                  
                  _  => begin
                      fail()
                  end
                end
              end
               #= /*Print.printBuf(\"Expression.getTerms_containingX failed: \");
                      ExpressionDump.printExp(e);
                      Print.printBuf(\"\\nsolving for: \");
                      ExpressionDump.printExp(cr);
                      Print.printBuf(\"\\n\");*/ =#
          (outExp1, outExp2)
        end

         #= returns all non-array expressions of an array expression as a long list
        E.g. {[1,2;3,4],[4,5;6,7]} => {1,2,3,4,4,5,6,7} =#
        function flattenArrayExpToList(e::DAE.Exp) ::List{DAE.Exp} 
              local expLst::List{DAE.Exp}

              expLst = begin
                  local expl::List{DAE.Exp}
                  local mexpl::List{List{DAE.Exp}}
                @matchcontinue e begin
                  DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = DAE.ARRAY(array = expl))  => begin
                      expl = ListUtil.flatten(ListUtil.map(expl, flattenArrayExpToList))
                      expLst = ListUtil.map(expl, negate)
                    expLst
                  end
                  
                  DAE.ARRAY(array = expl)  => begin
                      expLst = ListUtil.flatten(ListUtil.map(expl, flattenArrayExpToList))
                    expLst
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = DAE.MATRIX(matrix = mexpl))  => begin
                      expl = ListUtil.flatten(ListUtil.map(ListUtil.flatten(mexpl), flattenArrayExpToList))
                      expLst = ListUtil.map(expl, negate)
                    expLst
                  end
                  
                  DAE.MATRIX(matrix = mexpl)  => begin
                      expLst = ListUtil.flatten(ListUtil.map(ListUtil.flatten(mexpl), flattenArrayExpToList))
                    expLst
                  end
                  
                  _  => begin
                      list(e)
                  end
                end
              end
          expLst
        end

         #= /***************************************************/ =#
         #= /* generate  */ =#
         #= /***************************************************/ =#

         #=  adds a noEvent call around an expression =#
        function makeNoEvent(e1::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = Expression.makePureBuiltinCall("noEvent", list(e1), DAE.T_BOOL_DEFAULT)
          res
        end

         #=  =#
        function makeAbs(e1::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = Expression.makePureBuiltinCall("abs", list(e1), DAE.T_REAL_DEFAULT)
          res
        end

         #=  =#
        function makeSign(e1::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = Expression.makePureBuiltinCall("sign", list(e1), DAE.T_REAL_DEFAULT)
          res
        end

         #= creates a nested if expression given a list of conditions and
        guarded expressions and a default value (the else branch) =#
        function makeNestedIf(inConds::List{<:DAE.Exp} #= conditions =#, inTbExps::List{<:DAE.Exp} #=  guarded expressions, for each condition =#, fExp::DAE.Exp #= default value, else branch =#) ::DAE.Exp 
              local ifExp::DAE.Exp

              ifExp = begin
                  local c::DAE.Exp
                  local tbExp::DAE.Exp
                  local conds::List{DAE.Exp}
                  local tbExps::List{DAE.Exp}
                @match (inConds, inTbExps, fExp) begin
                  (c <|  nil(), tbExp <|  nil(), _)  => begin
                    DAE.IFEXP(c, tbExp, fExp)
                  end
                  
                  (c <| conds, tbExp <| tbExps, _)  => begin
                      ifExp = makeNestedIf(conds, tbExps, fExp)
                    DAE.IFEXP(c, tbExp, ifExp)
                  end
                end
              end
          ifExp
        end

         #= Makes an expression of a component reference, given also a type =#
        function makeCrefExp(inCref::DAE.ComponentRef, inExpType::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local cref::ComponentRef
                  local tGiven::Type
                  local tExisting::Type
                @match (inCref, inExpType) begin
                  (cref, tGiven)  => begin
                      if Flags.isSet(Flags.CHECK_DAE_CREF_TYPE)
                        tExisting = ComponentReference.crefLastType(cref)
                        if ! valueEq(tGiven, tExisting)
                          Debug.traceln("Warning: Expression.makeCrefExp: cref " + ComponentReference.printComponentRefStr(cref) + " was given type DAE.CREF.ty: " + Types.unparseType(tGiven) + " is different from existing DAE.CREF.componentRef.ty: " + Types.unparseType(tExisting))
                        end
                      end
                    DAE.CREF(cref, tGiven)
                  end
                end
              end
          outExp
        end

         #=  mahge:
          creates a DAE.Exp from a cref by exrtacting the type from the types of the cref (if qualified) and
          considering the dimensions and subscripts that exist in the cref.
         =#
        function crefToExp(cr::DAE.ComponentRef) ::DAE.Exp 
              local cref::DAE.Exp

              cref = DAE.CREF(cr, ComponentReference.crefTypeFull(cr))
          cref
        end

         #=  ***deprecated.
          mahge: use crefToExp(). This is not correct. We need to consider more than just the last subs.

        Author: BZ, 2008-08
        generate an DAE.CREF(ComponentRef, Type) from a ComponenRef, make array type correct from subs =#
        function crefExp(cr::DAE.ComponentRef) ::DAE.Exp 
              local cref::DAE.Exp

              cref = begin
                  local ty1::Type
                  local ty2::Type
                  local subs::List{DAE.Subscript}
                @match cr begin
                  _  => begin
                      ty1 = ComponentReference.crefLastType(cr)
                      cref = begin
                        @match ty1 begin
                          DAE.T_ARRAY(__)  => begin
                              subs = ComponentReference.crefLastSubs(cr)
                              ty2 = unliftArrayTypeWithSubs(subs, ty1)
                            DAE.CREF(cr, ty2)
                          end
                          
                          _  => begin
                              DAE.CREF(cr, ty1)
                          end
                        end
                      end
                    cref
                  end
                end
              end
          cref
        end

         #= @author: adrpo
          Creates an ASUB given an expression and a list of expression indexes.
          If flag -d=checkASUB is ON we give a warning that the given exp is
          not a component reference. =#
        function makeASUB(inExp::DAE.Exp, inSubs::List{<:DAE.Exp}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local exp::DAE.Exp
                  local subs::List{DAE.Exp}
                  local subs1::List{DAE.Exp}
                  local subs2::List{DAE.Exp}
                   #=  We need to be careful when constructing ASUB's. All subscripts should be in a list.
                   =#
                @match (inExp, inSubs) begin
                  (DAE.ASUB(exp, subs1), subs2)  => begin
                      subs = listAppend(subs1, subs2)
                      exp = DAE.ASUB(exp, subs)
                    exp
                  end
                  
                  (_, _)  => begin
                      if Flags.isSet(Flags.CHECK_ASUB)
                        _ = begin
                          @match inExp begin
                            DAE.CREF(__)  => begin
                                Debug.traceln("Warning: makeASUB: given expression: " + ExpressionDump.printExpStr(inExp) + " contains a component reference!\\n" + " Subscripts exps: [" + stringDelimitList(ListUtil.map(inSubs, ExpressionDump.printExpStr), ",") + "]\\n" + "DAE.ASUB should not be used for component references, instead the subscripts should be added directly to the component reference!")
                              ()
                            end
                            
                            _  => begin
                                ()
                            end
                          end
                        end
                      end
                      exp = DAE.ASUB(inExp, inSubs)
                    exp
                  end
                end
              end
          outExp
        end

        function makeASUBSingleSub(exp::DAE.Exp, sub::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = makeASUB(exp, list(sub))
          outExp
        end

        function makeTuple(inExps::List{<:DAE.Exp}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = if listLength(inExps) > 1
                    DAE.TUPLE(inExps)
                  else
                    ListUtil.first(inExps)
                  end
          outExp
        end

         #= 
        Author: Frenkel TUD 2010-05 =#
        function generateCrefsExpFromExpVar(inVar::DAE.Var, inCrefPrefix::DAE.ComponentRef) ::DAE.Exp 
              local outCrefExp::DAE.Exp

              outCrefExp = begin
                  local name::String
                  local ty::DAE.Type
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                @match (inVar, inCrefPrefix) begin
                  (DAE.TYPES_VAR(name = name, ty = ty), _)  => begin
                      cr = ComponentReference.crefPrependIdent(inCrefPrefix, name, nil, ty)
                      e = makeCrefExp(cr, ty)
                    e
                  end
                end
              end
          outCrefExp
        end

         #= 
        Author: Frenkel TUD 2010-05 =#
        function generateCrefsFromExpVar(inVar::DAE.Var, inCrefPrefix::DAE.ComponentRef) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              outCref = begin
                  local name::String
                  local ty::DAE.Type
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                @match (inVar, inCrefPrefix) begin
                  (DAE.TYPES_VAR(name = name, ty = ty), _)  => begin
                      cr = ComponentReference.crefPrependIdent(inCrefPrefix, name, nil, ty)
                    cr
                  end
                end
              end
          outCref
        end

        function generateCrefsExpFromExp(inExp::DAE.Exp, inCrefPrefix::DAE.ComponentRef) ::DAE.Exp 
              local outCrefExp::DAE.Exp

              outCrefExp = begin
                  local name::String
                  local ty::DAE.Type
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local explst::List{DAE.Exp}
                  local b::Bool
                  local attr::DAE.CallAttributes
                @match inExp begin
                  DAE.CREF(componentRef = DAE.WILD(__))  => begin
                    inExp
                  end
                  
                  DAE.ARRAY(ty = ty, scalar = b, array = explst)  => begin
                      explst = ListUtil.map1(explst, generateCrefsExpFromExp, inCrefPrefix)
                    DAE.ARRAY(ty, b, explst)
                  end
                  
                  DAE.CALL(path = p1, expLst = explst, attr = attr && DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p2))))  => begin
                      @match true = AbsynUtil.pathEqual(p1, p2) #= is record constructor =#
                      explst = ListUtil.map1(explst, generateCrefsExpFromExp, inCrefPrefix)
                    DAE.CALL(p1, explst, attr)
                  end
                  
                  DAE.CREF(componentRef = cr, ty = ty)  => begin
                      name = ComponentReference.crefModelicaStr(cr)
                      cr = ComponentReference.crefPrependIdent(inCrefPrefix, name, nil, ty)
                      e = makeCrefExp(cr, ty)
                    e
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                    negate(generateCrefsExpFromExp(e, inCrefPrefix))
                  end
                  
                  _  => begin
                        print("Expression.generateCrefsExpFromExp: fail for" + ExpressionDump.printExpStr(inExp) + "\\n")
                      fail()
                  end
                end
              end
               #= /*ToDo: check*/ =#
          outCrefExp
        end

        function generateCrefsExpLstFromExp(inExp::DAE.Exp, inCrefPrefix::Option{<:DAE.ComponentRef}) ::List{DAE.Exp} 
              local outCrefExpList::List{DAE.Exp}

              outCrefExpList = begin
                  local name::String
                  local ty::DAE.Type
                  local cr::DAE.ComponentRef
                  local incref::DAE.ComponentRef
                  local e::DAE.Exp
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local explst::List{DAE.Exp}
                  local b::Bool
                @match (inExp, inCrefPrefix) begin
                  (DAE.TUPLE(PR = explst), _)  => begin
                      explst = ListUtil.flatten(ListUtil.map1(explst, generateCrefsExpLstFromExp, inCrefPrefix))
                    explst
                  end
                  
                  (DAE.ARRAY(array = explst), _)  => begin
                      explst = ListUtil.flatten(ListUtil.map1(explst, generateCrefsExpLstFromExp, inCrefPrefix))
                    explst
                  end
                  
                  (DAE.CALL(path = p1, expLst = explst, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p2)))), _) where (AbsynUtil.pathEqual(p1, p2))  #= is record constructor =# => begin
                    ListUtil.flatten(ListUtil.map1(explst, generateCrefsExpLstFromExp, inCrefPrefix))
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = incref) <|  nil()), _)  => begin
                      cr = ComponentReference.crefPrefixDer(incref)
                      e = Expression.crefExp(cr)
                    generateCrefsExpLstFromExp(e, inCrefPrefix)
                  end
                  
                  (DAE.CREF(componentRef = cr, ty = ty), SOME(incref))  => begin
                      name = ComponentReference.crefModelicaStr(cr)
                      cr = ComponentReference.crefPrependIdent(incref, name, nil, ty)
                      e = makeCrefExp(cr, ty)
                    list(e)
                  end
                  
                  (DAE.CREF(__), NONE())  => begin
                    list(inExp)
                  end
                  
                  (DAE.UNARY(exp = e), _)  => begin
                    generateCrefsExpLstFromExp(e, inCrefPrefix)
                  end
                  
                  _  => begin
                        print("Expression.generateCrefsExpLstFromExp: fail for " + ExpressionDump.printExpStr(inExp) + "\\n")
                      fail()
                  end
                end
              end
               #= /*ToDo: check*/ =#
          outCrefExpList
        end

        function makeArray(inElements::List{<:DAE.Exp}, inType::DAE.Type, inScalar::Bool) ::DAE.Exp 
              local outArray::DAE.Exp

              outArray = DAE.ARRAY(inType, inScalar, inElements)
          outArray
        end

        function makeArrayFromList(inElements::List{<:DAE.Exp}) ::DAE.Exp 
              local outArray::DAE.Exp

              local ty::DAE.Type

              ty = typeof(listHead(inElements))
              outArray = DAE.ARRAY(DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(listLength(inElements)))), ! Types.isArray(ty), inElements)
          outArray
        end

         #= Constructs an array of the given scalar type. =#
        function makeScalarArray(inExpLst::List{<:DAE.Exp}, et::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              local i::ModelicaInteger

              i = listLength(inExpLst)
              outExp = DAE.ARRAY(DAE.T_ARRAY(et, list(DAE.DIM_INTEGER(i))), true, inExpLst)
          outExp
        end

         #= Construct an array node of an DAE.Exp list of type REAL. =#
        function makeRealArray(expl::List{<:DAE.Exp}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = makeScalarArray(expl, DAE.T_REAL_DEFAULT)
          outExp
        end

         #= Construct an add node of the two expressions of type REAL. =#
        function makeRealAdd(inExp1::DAE.Exp, inExp2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = DAE.BINARY(inExp1, DAE.ADD(DAE.T_REAL_DEFAULT), inExp2)
          outExp
        end

         #= author: PA
          Adds two scalar expressions. =#
        function expAdd(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local tp::Type
                  local b::Bool
                  local op::Operator
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local e::DAE.Exp
                  local x::DAE.Exp
                  local y::DAE.Exp
                  local z::DAE.Exp
                @matchcontinue (e1, e2) begin
                  (_, _)  => begin
                      @match true = isZero(e1)
                    e2
                  end
                  
                  (_, _)  => begin
                      @match true = isZero(e2)
                    e1
                  end
                  
                  (DAE.RCONST(r1), DAE.RCONST(r2))  => begin
                      r1 = realAdd(r1, r2)
                    DAE.RCONST(r1)
                  end
                  
                  (DAE.ICONST(i1), DAE.ICONST(i2))  => begin
                      i1 = intAdd(i1, i2)
                    DAE.ICONST(i1)
                  end
                  
                  (_, DAE.UNARY(operator = DAE.UMINUS(__), exp = e))  => begin
                    expSub(e1, e)
                  end
                  
                  (_, DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e))  => begin
                    expSub(e1, e)
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.MUL(__), y))  => begin
                    expSub(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.MUL_ARR(__), y))  => begin
                    expSub(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.DIV(__), y))  => begin
                    expSub(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.DIV_ARR(__), y))  => begin
                    expSub(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS(__), exp = e), _)  => begin
                    expSub(e2, e)
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e), _)  => begin
                    expSub(e2, e)
                  end
                  
                  (DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.MUL(__), y), _)  => begin
                    expSub(e2, DAE.BINARY(x, op, y))
                  end
                  
                  (DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.MUL_ARR(__), y), _)  => begin
                    expSub(e2, DAE.BINARY(x, op, y))
                  end
                  
                  (DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.DIV(__), y), _)  => begin
                    expSub(e2, DAE.BINARY(x, op, y))
                  end
                  
                  (DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.DIV_ARR(__), y), _)  => begin
                    expSub(e2, DAE.BINARY(x, op, y))
                  end
                  
                  (_, _)  => begin
                      tp = typeof(e1)
                      @match true = Types.isIntegerOrRealOrSubTypeOfEither(tp)
                      b = DAEUtil.expTypeArray(tp) #=   array_elt_type(tp) => tp\\' =#
                      op = if b
                            DAE.ADD_ARR(tp)
                          else
                            DAE.ADD(tp)
                          end
                    DAE.BINARY(e1, op, e2)
                  end
                  
                  _  => begin
                        tp = typeof(e1)
                        @match true = Types.isEnumeration(tp)
                      DAE.BINARY(e1, DAE.ADD(tp), e2)
                  end
                end
              end
               #= /* a + (-b) = a - b */ =#
               #=  x +(-y)*z
               =#
               #=  x +(-y)/z
               =#
               #= /* -b + a = a - b */ =#
               #=  (-y)*z+x
               =#
               #=  (-y)/z + x
               =#
          outExp
        end

         #= author: PA
          Subtracts two scalar expressions. =#
        function expSub(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local tp::Type
                  local b::Bool
                  local op::Operator
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local e::DAE.Exp
                  local x::DAE.Exp
                  local y::DAE.Exp
                @matchcontinue (e1, e2) begin
                  (_, _)  => begin
                      @match true = isZero(e1)
                    negate(e2)
                  end
                  
                  (_, _)  => begin
                      @match true = isZero(e2)
                    e1
                  end
                  
                  (DAE.RCONST(r1), DAE.RCONST(r2))  => begin
                      r1 = realSub(r1, r2)
                    DAE.RCONST(r1)
                  end
                  
                  (DAE.ICONST(i1), DAE.ICONST(i2))  => begin
                      i1 = intSub(i1, i2)
                    DAE.ICONST(i1)
                  end
                  
                  (_, DAE.UNARY(operator = DAE.UMINUS(__), exp = e))  => begin
                    expAdd(e1, e)
                  end
                  
                  (_, DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e))  => begin
                    expAdd(e1, e)
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.MUL(__), y))  => begin
                    expAdd(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.MUL_ARR(__), y))  => begin
                    expAdd(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS(__), x), op && DAE.DIV(__), y))  => begin
                    expAdd(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (_, DAE.BINARY(DAE.UNARY(DAE.UMINUS_ARR(__), x), op && DAE.DIV_ARR(__), y))  => begin
                    expAdd(e1, DAE.BINARY(x, op, y))
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS(__), exp = e), _)  => begin
                      e = expAdd(e, e2)
                    negate(e)
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = e), _)  => begin
                      e = expAdd(e, e2)
                    negate(e)
                  end
                  
                  (_, _)  => begin
                      tp = typeof(e1)
                      if Types.isIntegerOrRealOrSubTypeOfEither(tp)
                        b = DAEUtil.expTypeArray(tp)
                        op = if b
                              DAE.SUB_ARR(tp)
                            else
                              DAE.SUB(tp)
                            end
                        outExp = DAE.BINARY(e1, op, e2)
                      else
                        if Types.isEnumeration(tp)
                          outExp = DAE.BINARY(e1, DAE.SUB(tp), e2)
                        else
                          fail()
                        end
                      end
                    outExp
                  end
                end
              end
          outExp
        end

         #= Takes two expressions and create
         the difference between them =#
        function makeDiff(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = if isZero(e2)
                    e1
                  elseif (isZero(e1))
                        negate(e2)
                  else
                    expSub(e1, e2)
                  end
          res
        end

         #= Takes two expressions and create
         the difference between them --> a-(b+c) = a-b-c =#
        function makeDifference(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = makeDiff(e1, e2)
          res
        end

         #= Makes a binary logical expression of all elements in the list. =#
        function makeLBinary(inExpLst::List{<:DAE.Exp}, op::DAE.Operator) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res::DAE.Exp
                  local rest::List{DAE.Exp}
                  local str::String
                @match (inExpLst, op) begin
                  ( nil(), DAE.AND(_))  => begin
                    DAE.BCONST(true)
                  end
                  
                  ( nil(), DAE.OR(_))  => begin
                    DAE.BCONST(false)
                  end
                  
                  (e1 <|  nil(), _)  => begin
                    e1
                  end
                  
                  (e1 <| e2 <|  nil(), _)  => begin
                    DAE.LBINARY(e1, op, e2)
                  end
                  
                  (e1 <| rest, _)  => begin
                      res = makeLBinary(rest, op)
                      res = DAE.LBINARY(e1, op, res)
                    res
                  end
                  
                  _  => begin
                        str = "Expression.makeLBinary failed for operator " + ExpressionDump.lbinopSymbol(op)
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
          outExp
        end

         #= Takes a list of expressions an makes a sum
          expression sorting adding all elements in the list.

        Note:
        makeSum1 => (a + b) + c
        makeSum => a + (b + c)
         =#
        function makeSum1(inExpLst::List{<:DAE.Exp}, simplify::Bool = false) ::DAE.Exp 
              local outExp::DAE.Exp

              local e1::DAE.Exp
              local e2::DAE.Exp

              outExp = begin
                @matchcontinue inExpLst begin
                   nil()  => begin
                    DAE.RCONST(0.0)
                  end
                  
                  e1 <|  nil()  => begin
                    e1
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                    expAdd(e1, e2)
                  end
                  
                  _  => begin
                    makeSumWork(inExpLst, simplify)
                  end
                  
                  _  => begin
                        if Flags.isSet(Flags.FAILTRACE)
                          Debug.trace("-Expression.makeSum1 failed, DAE.Exp lst:")
                          Debug.trace(ExpressionDump.printExpListStr(inExpLst))
                        end
                      fail()
                  end
                end
              end
          outExp
        end

         #= Takes a list of expressions an makes a sum
          expression adding all elements in the list. =#
        function makeSumWork(inExpLst::List{<:DAE.Exp}, simplify::Bool = false) ::DAE.Exp 
              local outExp::DAE.Exp

              local tp::Type
              local rest::List{DAE.Exp}
              local eLst::DAE.Exp
              local op::DAE.Operator

              @match _cons(eLst, rest) = inExpLst
              tp = typeof(eLst)
              op = if DAEUtil.expTypeArray(tp)
                    DAE.ADD_ARR(tp)
                  else
                    DAE.ADD(tp)
                  end
              outExp = eLst
              for elem in rest
                outExp = if isZero(elem)
                      outExp
                    elseif (isZero(outExp))
                          elem
                    elseif (simplify)
                          ExpressionSimplify.simplify1(DAE.BINARY(outExp, op, elem))
                    else
                      DAE.BINARY(outExp, op, elem)
                    end
              end
          outExp
        end

         #= Takes a list of expressions an makes a sum
          expression adding all elements in the list. =#
        function makeSum(inExpLst::List{<:DAE.Exp}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res::DAE.Exp
                  local b1::Bool
                  local tp::Type
                  local rest::List{DAE.Exp}
                  local lst::List{DAE.Exp}
                  local explst::List{String}
                  local str::String
                  local op::Operator
                  local b::Bool
                @matchcontinue inExpLst begin
                   nil()  => begin
                    DAE.RCONST(0.0)
                  end
                  
                  e1 <|  nil()  => begin
                    e1
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                      @match true = isZero(e1)
                    e2
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                      @match true = isZero(e2)
                    e1
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                      tp = typeof(e1) #= Take type info from e1, ok since type checking already performed. =#
                      b = DAEUtil.expTypeArray(tp)
                      op = if b
                            DAE.ADD_ARR(tp)
                          else
                            DAE.ADD(tp)
                          end
                    DAE.BINARY(e1, op, e2)
                  end
                  
                  e1 <| rest  => begin
                      b1 = isZero(e1)
                      e2 = makeSum(rest)
                      tp = typeof(e2)
                      b = DAEUtil.expTypeArray(tp)
                      op = if b
                            DAE.ADD_ARR(tp)
                          else
                            DAE.ADD(tp)
                          end
                      res = DAE.BINARY(e1, op, e2)
                      res = if b1
                            e2
                          else
                            res
                          end
                    res
                  end
                  
                  lst  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("-Expression.makeSum failed, DAE.Exp lst:")
                      explst = ListUtil.map(lst, ExpressionDump.printExpStr)
                      str = stringDelimitList(explst, ", ")
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
               #= res = DAE.BINARY(e1, DAE.ADD(tp), e2);
               =#
               #= then res;
               =#
               #= /*case ({e1,e2})
                    equation
                      b1 = isZero(e1);
                      tp = typeof(e1) \"Take type info from e1, ok since type checking already performed.\" ;
                      res = DAE.BINARY(e1,DAE.ADD(tp),e2);
                      res = if_(b1,e2,res);
                    then
                      res;*/ =#
          outExp
        end

         #= author: PA
          Multiplies two scalar expressions. =#
        function expMul(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local tp::Type
                  local b1::Bool
                  local b2::Bool
                  local op::Operator
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                @matchcontinue (e1, e2) begin
                  (_, _)  => begin
                      @match true = isZero(e1)
                    e1
                  end
                  
                  (_, _)  => begin
                      @match true = isZero(e2)
                    e2
                  end
                  
                  (DAE.RCONST(real = 1.0), _)  => begin
                    e2
                  end
                  
                  (_, DAE.RCONST(real = 1.0))  => begin
                    e1
                  end
                  
                  (DAE.ICONST(1), _)  => begin
                    e2
                  end
                  
                  (_, DAE.ICONST(1))  => begin
                    e1
                  end
                  
                  (DAE.RCONST(r1), DAE.RCONST(r2))  => begin
                      r1 = realMul(r1, r2)
                    DAE.RCONST(r1)
                  end
                  
                  (DAE.ICONST(i1), DAE.ICONST(i2))  => begin
                      i1 = intMul(i1, i2)
                    DAE.ICONST(i1)
                  end
                  
                  _  => begin
                        tp = typeof(e1)
                        @match true = Types.isIntegerOrRealOrSubTypeOfEither(tp)
                        b1 = DAEUtil.expTypeArray(tp)
                        tp = typeof(e2)
                        @match true = Types.isIntegerOrRealOrSubTypeOfEither(tp)
                        b2 = DAEUtil.expTypeArray(tp)
                        (e1_1, e2_1) = Util.swap(! b1 && b2, e1, e2)
                        op = if b1 && b2
                              DAE.MUL_ARR(tp)
                            else
                              if b1 == b2
                                    DAE.MUL(tp)
                                  else
                                    DAE.MUL_ARRAY_SCALAR(tp)
                                  end
                            end
                      DAE.BINARY(e1_1, op, e2_1)
                  end
                end
              end
               #= /* swap e1 and e2 if we have scalar mul array */ =#
               #= /* Create all kinds of multiplication with scalars or arrays */ =#
          outExp
        end

         #= author: vitalij =#
        function expPow(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local tp::Type
                  local e::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local e5::DAE.Exp
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local b::Bool
                  local op::Operator
                   #=  e1^1 = e1
                   =#
                @match (e1, e2) begin
                  (_, _) where (isOne(e2))  => begin
                    e1
                  end
                  
                  (_, _) where (isZero(e2))  => begin
                    makeConstOne(typeof(e1))
                  end
                  
                  (_, _) where (isConstOne(e1))  => begin
                    e1
                  end
                  
                  (_, _) where (isZero(e1) && expIsPositive(e2))  => begin
                    makeConstZero(typeof(e1))
                  end
                  
                  (DAE.UNARY(DAE.UMINUS(__), e), _) where (isEven(e2))  => begin
                    expPow(e, e2)
                  end
                  
                  (DAE.BINARY(e3, DAE.DIV(__), e4), DAE.UNARY(DAE.UMINUS(__), e5))  => begin
                      e = makeDiv(e4, e3)
                      e = expPow(e, e5)
                    e
                  end
                  
                  (DAE.BINARY(e3, DAE.DIV(__), e4), _) where (isNegativeOrZero(e2))  => begin
                    expPow(makeDiv(e4, e3), negate(e2))
                  end
                  
                  (_, _) where (isHalf(e2))  => begin
                    Expression.makePureBuiltinCall("sqrt", list(e1), DAE.T_REAL_DEFAULT)
                  end
                  
                  _  => begin
                        tp = typeof(e1)
                        b = DAEUtil.expTypeArray(tp)
                        op = if b
                              DAE.POW_ARR(tp)
                            else
                              DAE.POW(tp)
                            end
                      DAE.BINARY(e1, op, e2)
                  end
                end
              end
               #=  e1^0 = 1
               =#
               #=  1^e2 = 1
               =#
               #=  0^e2 = 0
               =#
               #=  (-e)^r = e^r if r is even
               =#
               #=  (x/y)^(-z) = (y/x)^z
               =#
               #=  (e1/e2)^(-r) = (e2/e1)^r
               =#
               #=  x^0.5 => sqrt(x)
               =#
          outExp
        end

         #= 
        {a,b}^n -> {a^n, b^n}
        author: vitalij =#
        function expPowLst(expLst::List{<:DAE.Exp}, n::DAE.Exp) ::List{DAE.Exp} 
              local outExp::List{DAE.Exp} = ListUtil.map1(expLst, expPow, n)
          outExp
        end

         #= author: Frenkel TUD 2011-04
          returns max(e1,e2). =#
        function expMaxScalar(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              local tp::Type

              tp = typeof(e1)
              outExp = DAE.CALL(Absyn.IDENT("max"), list(e1, e2), DAE.CALL_ATTR(tp, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
          outExp
        end

        function expOptMaxScalar(e1::Option{<:DAE.Exp}, e2::Option{<:DAE.Exp}) ::Option{DAE.Exp} 
              local outExp::Option{DAE.Exp}

              outExp = begin
                  local e11::DAE.Exp
                  local e22::DAE.Exp
                @match (e1, e2) begin
                  (_, NONE())  => begin
                    e1
                  end
                  
                  (NONE(), _)  => begin
                    e2
                  end
                  
                  (SOME(e11), SOME(e22))  => begin
                    SOME(expMaxScalar(e11, e22))
                  end
                end
              end
          outExp
        end

         #= author: Frenkel TUD 2011-04
          returns min(e1,e2). =#
        function expMinScalar(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              local tp::Type
              local b::Bool

              tp = typeof(e1)
              outExp = DAE.CALL(Absyn.IDENT("min"), list(e1, e2), DAE.CALL_ATTR(tp, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
          outExp
        end

        function expOptMinScalar(e1::Option{<:DAE.Exp}, e2::Option{<:DAE.Exp}) ::Option{DAE.Exp} 
              local outExp::Option{DAE.Exp}

              outExp = begin
                  local e11::DAE.Exp
                  local e22::DAE.Exp
                @match (e1, e2) begin
                  (_, NONE())  => begin
                    e1
                  end
                  
                  (NONE(), _)  => begin
                    e2
                  end
                  
                  (SOME(e11), SOME(e22))  => begin
                    SOME(expMinScalar(e11, e22))
                  end
                end
              end
          outExp
        end

         #= takes and expression e1 and a list of expressisions {v1,v2,...,vn} and returns
        {e1*v1,e1*v2,...,e1*vn} =#
        function makeProductVector(e1::DAE.Exp, v::List{<:DAE.Exp}) ::List{DAE.Exp} 
              local res::List{DAE.Exp}

              res = ListUtil.map1(v, makeProduct, e1)
          res
        end

         #= calculate a scalr product <v,w> =#
        function makeScalarProduct(v::Array{<:DAE.Exp}, w::Array{<:DAE.Exp}) ::DAE.Exp 
              local s::DAE.Exp = DAE.RCONST(0.0)

              local size1::ModelicaInteger = arrayLength(v)
              local size2::ModelicaInteger = arrayLength(w)

              if size1 != size2
                print("makeScalarProduct faili.\\n")
                return s
              end
              s = makeSum1(list(expMul(arrayGet(v, i), arrayGet(w, i)) for i in 1:size1))
              (s, _) = ExpressionSimplify.simplify(s)
          s
        end

        function lenVec(v::Array{<:DAE.Exp}) ::DAE.Exp 
              local len::DAE.Exp = makeScalarProduct(v, v)

              len = Expression.makePureBuiltinCall("sqrt", list(len), DAE.T_REAL_DEFAULT)
          len
        end

        function addVec(v::Array{<:DAE.Exp}, w::Array{<:DAE.Exp}) ::Array{DAE.Exp} 
              local y::Array{DAE.Exp}

              local size1::ModelicaInteger = arrayLength(v)
              local size2::ModelicaInteger = arrayLength(w)

              if size1 != size2
                print("addVec fail.\\n")
                return y
              end
              y = arrayCreate(size1, DAE.RCONST(0.0))
              for i in 1:size1
                arrayUpdate(y, i, expAdd(arrayGet(v, i), arrayGet(w, i)))
              end
          y
        end

        function subVec(v::Array{<:DAE.Exp}, w::Array{<:DAE.Exp}) ::Array{DAE.Exp} 
              local y::Array{DAE.Exp}

              local size1::ModelicaInteger = arrayLength(v)
              local size2::ModelicaInteger = arrayLength(w)

              if size1 != size2
                print("addVec fail.\\n")
                return y
              end
              y = arrayCreate(size1, DAE.RCONST(0.0))
              for i in 1:size1
                arrayUpdate(y, i, expSub(arrayGet(v, i), arrayGet(w, i)))
              end
          y
        end

         #= Makes a product of two expressions =#
        function makeProduct(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local product::DAE.Exp

              product = makeProductLst(list(e1, e2))
          product
        end

         #= Takes a list of expressions an makes a product
          expression multiplying all elements in the list. =#
        function makeProductLst(inExpLst::List{<:DAE.Exp}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local res::DAE.Exp
                  local e::DAE.Exp
                  local e2::DAE.Exp
                  local p1::DAE.Exp
                  local es::List{DAE.Exp}
                  local rest::List{DAE.Exp}
                  local lst::List{DAE.Exp}
                  local tp::Type
                  local explst::List{String}
                  local str::String
                  local b_isZero::Bool
                  local b1::Bool
                  local b2::Bool
                @matchcontinue inExpLst begin
                   nil()  => begin
                    DAE.RCONST(1.0)
                  end
                  
                  e1 <|  nil()  => begin
                    e1
                  end
                  
                  e <| es  => begin
                      @match true = isConstOne(e)
                      res = makeProductLst(es)
                    res
                  end
                  
                  DAE.BINARY(operator = DAE.DIV(__), exp2 = e) <| _  => begin
                      @match true = isZero(e)
                    fail()
                  end
                  
                  _ <| DAE.BINARY(operator = DAE.DIV(__), exp2 = e) <|  nil()  => begin
                      @match true = isZero(e)
                    fail()
                  end
                  
                  e <| _  => begin
                      @match true = isZero(e)
                    e
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = tp), exp2 = e) <| e2 <|  nil()  => begin
                      @match true = isConstOne(e1)
                    DAE.BINARY(e2, DAE.DIV(tp), e)
                  end
                  
                  e2 <| DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = tp), exp2 = e) <|  nil()  => begin
                      @match true = isConstOne(e1)
                    DAE.BINARY(e2, DAE.DIV(tp), e)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = DAE.DIV(ty = tp), exp2 = e) <| es  => begin
                      @match true = isConstOne(e1)
                      p1 = makeProductLst(es)
                      res = DAE.BINARY(p1, DAE.DIV(tp), e)
                      b_isZero = isZero(p1)
                      res = if b_isZero
                            makeConstZero(typeof(e))
                          else
                            res
                          end
                    res
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                      @match true = isConstOne(e2)
                    e1
                  end
                  
                  e1 <| e2 <|  nil()  => begin
                      b1 = isZero(e1)
                      b2 = isZero(e2)
                      b_isZero = boolOr(b1, b2)
                      tp = typeof(e1) #= Take type info from e1, ok since type checking already performed. =#
                      tp = checkIfOther(tp)
                      res = DAE.BINARY(e1, DAE.MUL(tp), e2)
                      res = if b_isZero
                            makeConstZero(tp)
                          else
                            res
                          end
                    res
                  end
                  
                  e1 <| rest  => begin
                      e2 = makeProductLst(rest)
                      tp = typeof(e1)
                      tp = checkIfOther(tp)
                      res = DAE.BINARY(e1, DAE.MUL(tp), e2)
                      b1 = isZero(e1)
                      b2 = isZero(e2)
                      b_isZero = boolOr(b1, b2)
                      res = if b_isZero
                            makeConstZero(typeof(e1))
                          else
                            res
                          end
                    res
                  end
                  
                  lst  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("-Expression.makeProductLst failed, DAE.Exp lst:")
                      explst = ListUtil.map(lst, ExpressionDump.printExpStr)
                      str = stringDelimitList(explst, ", ")
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
               #= /* to prevent infinite recursion, disregard constant 1. */ =#
               #=  e1/e*e2 for e = 0 => fail
               =#
               #=  e2*e1/e for e = 0 => fail
               =#
               #= /* to prevent infinite recursion, disregard constant 0. */ =#
          outExp
        end

         #= Checks if a type is OTHER and in that case returns REAL instead.
         This is used to make proper transformations in case OTHER is
         retrieved from subexpression where it should instead be REAL or INT =#
        function checkIfOther(inTp::DAE.Type) ::DAE.Type 
              local outTp::DAE.Type

              outTp = begin
                @match inTp begin
                  DAE.T_UNKNOWN(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end
                  
                  _  => begin
                      inTp
                  end
                end
              end
          outTp
        end

         #= 
        function expDiv
          author: PA
          Divides two scalar expressions. =#
        function expDiv(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              local tp::Type
              local b::Bool
              local op::Operator

              tp = typeof(e1)
              @match true = Types.isIntegerOrRealOrSubTypeOfEither(tp)
              b = DAEUtil.expTypeArray(tp)
              op = if b
                    DAE.DIV_ARR(tp)
                  else
                    DAE.DIV(tp)
                  end
              outExp = DAE.BINARY(e1, op, e2)
          outExp
        end

         #= Takes two expressions and create a division =#
        function makeDiv(e1::DAE.Exp, e2::DAE.Exp) ::DAE.Exp 
              local res::DAE.Exp

              res = begin
                @match (e1, e2) begin
                  (_, _) where (isZero(e1) && ! isZero(e2))  => begin
                    e1
                  end
                  
                  (_, _) where (isOne(e2))  => begin
                    e1
                  end
                  
                  _  => begin
                      expDiv(e1, e2)
                  end
                end
              end
          res
        end

         #= takes and expression e1 and a list of expressisions {v1,v2,...,vn} and returns
        {v1/e1,v2/e1,...,vn/e1} =#
        function makeDivVector(v::List{<:DAE.Exp}, e1::DAE.Exp) ::List{DAE.Exp} 
              local res::List{DAE.Exp}

              res = ListUtil.map1(v, makeDiv, e1)
          res
        end

         #= creates an ASUB given an expression and an index =#
        function makeAsubAddIndex(e::DAE.Exp, indx::ModelicaInteger) ::DAE.Exp 
              local outExp::DAE.Exp = e

              outExp = begin
                @match outExp begin
                  DAE.ASUB(__)  => begin
                      outExp.sub = listAppend(outExp.sub, list(DAE.ICONST(indx)))
                    outExp
                  end
                  
                  _  => begin
                      makeASUB(e, list(DAE.ICONST(indx)))
                  end
                end
              end
          outExp
        end

         #= Creates an integer constant expression given the integer input. =#
        function makeIntegerExp(i::ModelicaInteger) ::DAE.Exp 
              local e::DAE.Exp

              e = DAE.ICONST(i)
          e
        end

         #= Creates an integer constant expression given the integer input. =#
        function makeRealExp(r::ModelicaReal) ::DAE.Exp 
              local e::DAE.Exp

              e = DAE.RCONST(r)
          e
        end

         #= Creates an integer constant expression given the integer input. =#
        function makeBoolExp(b::Bool) ::DAE.Exp 
              local e::DAE.Exp

              e = DAE.BCONST(b)
          e
        end

         #= author: PA
          Create the constant value one, given a type that is INT or REAL =#
        function makeConstOne(inType::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.ICONST(1)
                  end
                  
                  DAE.T_REAL(__)  => begin
                    DAE.RCONST(1.0)
                  end
                  
                  _  => begin
                      DAE.RCONST(1.0)
                  end
                end
              end
          outExp
        end

         #= Generates a zero constant =#
        function makeConstZero(inType::DAE.Type) ::DAE.Exp 
              local const::DAE.Exp

              const = begin
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    DAE.RCONST(0.0)
                  end
                  
                  DAE.T_INTEGER(__)  => begin
                    DAE.ICONST(0)
                  end
                  
                  _  => begin
                      DAE.RCONST(0.0)
                  end
                end
              end
          const
        end

        function makeConstNumber(ty::DAE.Type, n::ModelicaInteger) ::DAE.Exp 
              local exp::DAE.Exp

              exp = begin
                @match ty begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.ICONST(n)
                  end
                  
                  _  => begin
                      DAE.RCONST(n)
                  end
                end
              end
          exp
        end

         #= Generates a zero constant, using type from inExp =#
        function makeConstZeroE(iExp::DAE.Exp) ::DAE.Exp 
              local const::DAE.Exp

              local tp::DAE.Type = typeof(iExp)

              const = makeConstZero(tp)
          const
        end

        function makeListOfZeros(inDimension::ModelicaInteger) ::List{DAE.Exp} 
              local outList::List{DAE.Exp} = nil

              if inDimension > 0
                for i in 1:inDimension
                  outList = _cons(DAE.RCONST(0.0), outList)
                end
              end
          outList
        end

        function makeRealArrayOfZeros(inDimension::ModelicaInteger) ::DAE.Exp 
              local outExp::DAE.Exp

              local l::List{DAE.Exp}

              l = makeListOfZeros(inDimension)
              outExp = makeRealArray(l)
          outExp
        end

        function createZeroExpression(inType::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local e::DAE.Exp
                  local typeLst::List{DAE.Type}
                  local expLst::List{DAE.Exp}
                  local dims::DAE.Dimensions
                  local cr::DAE.ComponentRef
                  local crefs::List{DAE.ComponentRef}
                  local path::Absyn.Path
                  local varLst::List{DAE.Var}
                  local varNames::List{String}
                   #=  real and integer
                   =#
                @match inType begin
                  _ where (isIntegerOrReal(inType))  => begin
                    makeConstZero(inType)
                  end
                  
                  DAE.T_TUPLE(types = typeLst)  => begin
                      expLst = ListUtil.map(typeLst, createZeroExpression)
                      e = DAE.TUPLE(expLst)
                    e
                  end
                  
                  DAE.T_ARRAY(dims = dims)  => begin
                      (e, _) = makeZeroExpression(dims)
                    e
                  end
                  
                  DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD(path))  => begin
                      cr = DAE.CREF_IDENT("TMP", inType, nil)
                      typeLst = list(v.ty for v in varLst)
                      expLst = ListUtil.map(typeLst, createZeroExpression)
                      varNames = ListUtil.map(varLst, varName)
                      @match true = listLength(varNames) == listLength(expLst)
                      e = DAE.RECORD(path, expLst, varNames, inType)
                    e
                  end
                  
                  _  => begin
                      fail()
                  end
                end
              end
               #=  record type
               =#
               #=  all other are failing cases
               =#
          outExp
        end

         #=  creates a Real or array<Real> zero expression with given dimensions, also returns its type =#
        function makeZeroExpression(inDims::DAE.Dimensions) ::Tuple{DAE.Exp, DAE.Type} 
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType) = begin
                  local i::ModelicaInteger
                  local d::DAE.Dimension
                  local dims::DAE.Dimensions
                  local e::DAE.Exp
                  local eLst::List{DAE.Exp}
                  local ty::DAE.Type
                  local scalar::Bool
                @match inDims begin
                   nil()  => begin
                    (DAE.RCONST(0.0), DAE.T_REAL_DEFAULT)
                  end
                  
                  d <| dims  => begin
                      i = dimensionSize(d)
                      (e, ty) = makeZeroExpression(dims)
                      eLst = ListUtil.fill(e, i)
                      scalar = listEmpty(dims)
                    (DAE.ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, _cons(d, dims)), scalar, eLst), DAE.T_ARRAY(ty, list(d)))
                  end
                end
              end
          (outExp, outType)
        end

         #=  creates a Real or array<Real> one expression with given dimensions, also returns its type =#
        function makeOneExpression(inDims::DAE.Dimensions) ::Tuple{DAE.Exp, DAE.Type} 
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType) = begin
                  local i::ModelicaInteger
                  local d::DAE.Dimension
                  local dims::DAE.Dimensions
                  local e::DAE.Exp
                  local eLst::List{DAE.Exp}
                  local ty::DAE.Type
                  local scalar::Bool
                @match inDims begin
                   nil()  => begin
                    (DAE.RCONST(1.0), DAE.T_REAL_DEFAULT)
                  end
                  
                  d <| dims  => begin
                      i = dimensionSize(d)
                      (e, ty) = makeOneExpression(dims)
                      eLst = ListUtil.fill(e, i)
                      scalar = listEmpty(dims)
                    (DAE.ARRAY(DAE.T_ARRAY(DAE.T_REAL_DEFAULT, _cons(d, dims)), scalar, eLst), DAE.T_ARRAY(ty, list(d)))
                  end
                end
              end
          (outExp, outType)
        end

         #=  @mahge:
          creates an array from a list of expressions and
          dimensions. e.g.
           listToArray({1,2,3,4,5,6}, {3,2}) -> {{1,2}, {3,4}, {5,6}}
         =#
        function listToArray(inList::List{<:DAE.Exp}, dims::DAE.Dimensions) ::DAE.Exp 
              local oExp::DAE.Exp

              oExp = begin
                  local ty::DAE.Type
                  local exp::DAE.Exp
                @matchcontinue (inList, dims) begin
                  (_,  nil())  => begin
                      Error.addMessage(Error.INTERNAL_ERROR, list("Expression.listToArray called with empty dimension list."))
                    fail()
                  end
                  
                  ( nil(), _)  => begin
                      Error.addMessage(Error.INTERNAL_ERROR, list("Expression.listToArray called with empty list."))
                    fail()
                  end
                  
                  (exp <| _, _)  => begin
                      ty = typeof(exp)
                      oExp = listToArray2(inList, dims, ty)
                    oExp
                  end
                end
              end
               #=  Here we assume that all the elements of the list
               =#
               #=  have the same type.
               =#
          oExp
        end

        function listToArray2(inList::List{<:DAE.Exp}, iDims::DAE.Dimensions, inType::DAE.Type) ::DAE.Exp 
              local oExp::DAE.Exp

              oExp = begin
                  local i::ModelicaInteger
                  local d::DAE.Dimension
                  local explst::List{DAE.Exp}
                  local arrexp::DAE.Exp
                  local dims::DAE.Dimensions
                @matchcontinue (inList, iDims, inType) begin
                  (_, d <|  nil(), _)  => begin
                      i = dimensionSize(d)
                      @match true = i == listLength(inList)
                    makeArrayFromList(inList)
                  end
                  
                  (_, d <|  nil(), _)  => begin
                      i = dimensionSize(d)
                      @match true = i > listLength(inList)
                      Error.addMessage(Error.INTERNAL_ERROR, list("Expression.listToArray2: Not enough elements left in list to fit dimension."))
                    fail()
                  end
                  
                  (_, _ <| _, _)  => begin
                      (d, dims) = ListUtil.splitLast(iDims)
                      explst = listToArray3(inList, d, inType)
                      arrexp = listToArray2(explst, dims, inType)
                    arrexp
                  end
                end
              end
          oExp
        end

        function listToArray3(inList::List{<:DAE.Exp}, iDim::DAE.Dimension, inType::DAE.Type) ::List{DAE.Exp} 
              local oExps::List{DAE.Exp}

              oExps = begin
                  local i::ModelicaInteger
                  local d::DAE.Dimension
                  local explst::List{DAE.Exp}
                  local restexps::List{DAE.Exp}
                  local restarr::List{DAE.Exp}
                  local arrexp::DAE.Exp
                @match (inList, iDim, inType) begin
                  ( nil(), _, _)  => begin
                    nil
                  end
                  
                  (_, d, _)  => begin
                      i = dimensionSize(d)
                      if i > listLength(inList)
                        Error.addMessage(Error.INTERNAL_ERROR, list("Expression.listToArray3: Not enough elements left in list to fit dimension."))
                        fail()
                      else
                        (explst, restexps) = ListUtil.split(inList, i)
                        arrexp = makeArrayFromList(explst)
                        restarr = listToArray3(restexps, d, inType)
                      end
                    _cons(arrexp, restarr)
                  end
                end
              end
          oExps
        end

        function arrayFill(dims::DAE.Dimensions, inExp::DAE.Exp) ::DAE.Exp 
              local oExp::DAE.Exp

              oExp = begin
                @match (dims, inExp) begin
                  ( nil(), _)  => begin
                    inExp
                  end
                  
                  _  => begin
                        oExp = arrayFill2(dims, inExp)
                      oExp
                  end
                end
              end
          oExp
        end

        function arrayFill2(iDims::DAE.Dimensions, inExp::DAE.Exp) ::DAE.Exp 
              local oExp::DAE.Exp

              oExp = begin
                  local i::ModelicaInteger
                  local d::DAE.Dimension
                  local ty::Type
                  local expl::List{DAE.Exp}
                  local arrexp::DAE.Exp
                  local dims::DAE.Dimensions
                @match (iDims, inExp) begin
                  (d <|  nil(), _)  => begin
                      ty = typeof(inExp)
                      i = dimensionSize(d)
                      expl = ListUtil.fill(inExp, i)
                    DAE.ARRAY(DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(i))), true, expl)
                  end
                  
                  (d <| dims, _)  => begin
                      arrexp = arrayFill2(list(d), inExp)
                      arrexp = arrayFill2(dims, arrexp)
                    arrexp
                  end
                end
              end
          oExp
        end

         #= Creates a Subscript INDEX from an Expression. =#
        function makeIndexSubscript(exp::DAE.Exp) ::DAE.Subscript 
              local subscript::DAE.Subscript

              subscript = DAE.INDEX(exp)
          subscript
        end

         #= Creates a Var given a name and Type =#
        function makeVar(name::String, tp::DAE.Type) ::DAE.Var 
              local v::DAE.Var

              v = DAE.TYPES_VAR(name, DAE.dummyAttrVar, tp, DAE.UNBOUND(), NONE())
          v
        end

         #= Multiplies two dimensions. =#
        function dimensionsMult(dim1::DAE.Dimension, dim2::DAE.Dimension) ::DAE.Dimension 
              local res::DAE.Dimension

              res = intDimension(dimensionSize(dim1) * dimensionSize(dim2))
          res
        end

         #= Adds two dimensions. =#
        function dimensionsAdd(dim1::DAE.Dimension, dim2::DAE.Dimension) ::DAE.Dimension 
              local res::DAE.Dimension

              try
                res = intDimension(dimensionSize(dim1) + dimensionSize(dim2))
              catch
                res = DAE.DIM_UNKNOWN()
              end
          res
        end

         #= Concatenates two array types, so that the resulting type is correct. =#
        function concatArrayType(arrayType1::DAE.Type, arrayType2::DAE.Type) ::DAE.Type 
              local concatType::DAE.Type

              concatType = begin
                  local et::DAE.Type
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local dims1::DAE.Dimensions
                  local dims2::DAE.Dimensions
                @match (arrayType1, arrayType2) begin
                  (DAE.T_ARRAY(ty = et, dims = dim1 <| dims1), DAE.T_ARRAY(dims = dim2 <| _))  => begin
                      dim1 = dimensionsAdd(dim1, dim2)
                    DAE.T_ARRAY(et, _cons(dim1, dims1))
                  end
                end
              end
          concatType
        end

         #= Help function to e.g. detectImplicitDiscreteAlgsStatemensFor =#
        function replaceExpTpl(inExp::DAE.Exp, tpl::Tuple{<:DAE.Exp, DAE.Exp}) ::Tuple{DAE.Exp, Tuple{DAE.Exp, DAE.Exp}} 
              local outTpl::Tuple{DAE.Exp, DAE.Exp}
              local outExp::DAE.Exp

              (outExp, outTpl) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local s::DAE.Exp
                  local t::DAE.Exp
                @match (inExp, tpl) begin
                  (e, (s, t))  => begin
                      (e1, _) = replaceExp(e, s, t)
                    (e1, tpl)
                  end
                end
              end
          (outExp, outTpl)
        end

         #= Helper function to replaceExpList. =#
        function replaceExp(inExp::DAE.Exp, inSourceExp::DAE.Exp, inTargetExp::DAE.Exp) ::Tuple{DAE.Exp, ModelicaInteger} 
              local out::Tuple{DAE.Exp, ModelicaInteger}

              local exp::DAE.Exp
              local i::ModelicaInteger

              (exp, (_, _, i)) = traverseExpTopDown(inExp, replaceExpWork, (inSourceExp, inTargetExp, 0))
              out = (exp, i)
          out
        end

        function replaceExpWork(inExp::DAE.Exp, inTpl::Tuple{<:DAE.Exp, DAE.Exp, ModelicaInteger}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.Exp, DAE.Exp, ModelicaInteger}} 
              local otpl::Tuple{DAE.Exp, DAE.Exp, ModelicaInteger}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, otpl) = begin
                  local tpl::Tuple{DAE.Exp, DAE.Exp, ModelicaInteger}
                  local expr::DAE.Exp
                  local source::DAE.Exp
                  local target::DAE.Exp
                  local c::ModelicaInteger
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                @match (inExp, inTpl) begin
                  (_, (source, target, c)) where (expEqual(inExp, source))  => begin
                    (target, false, (source, target, c + 1))
                  end
                  
                  _  => begin
                      (inExp, true, inTpl)
                  end
                end
              end
          (outExp, cont, otpl)
        end

        function expressionCollector(exp::DAE.Exp, acc::List{<:DAE.Exp}) ::Tuple{DAE.Exp, List{DAE.Exp}} 
              local outExps::List{DAE.Exp}
              local outExp::DAE.Exp

              outExp = exp
              outExps = _cons(exp, acc)
          (outExp, outExps)
        end

        function replaceCrefBottomUp(inExp::DAE.Exp, inSourceExp::DAE.ComponentRef, inTargetExp::DAE.Exp) ::DAE.Exp 
              local exp::DAE.Exp

              (exp, _) = traverseExpBottomUp(inExp, replaceCref, (inSourceExp, inTargetExp))
          exp
        end

         #= Replace a componentref with a expression =#
        function replaceCref(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, DAE.Exp}) ::Tuple{DAE.Exp, Tuple{DAE.ComponentRef, DAE.Exp}} 
              local otpl::Tuple{DAE.ComponentRef, DAE.Exp}
              local outExp::DAE.Exp

              (outExp, otpl) = begin
                  local target::DAE.Exp
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CREF(componentRef = cr), (cr1, target)) where (ComponentReference.crefEqualNoStringCompare(cr, cr1))  => begin
                    (target, inTpl)
                  end
                  
                  _  => begin
                      (inExp, inTpl)
                  end
                end
              end
          (outExp, otpl)
        end

         #= public function containsInitialCall
          author: lochel
          Spec33 p. 90:
          [...] The equations of a when-clause are active during initialization, if
          and only if they are explicitly enabled with the initial() operator; and
          only in one of the two forms when initial() then or when {…,initial(),…}
          then. [...] =#
        function containsInitialCall(condition::DAE.Exp) ::Bool 
              local res::Bool

              res = begin
                  local array::List{Exp}
                @match condition begin
                  DAE.CALL(path = Absyn.IDENT(name = "initial"))  => begin
                    true
                  end
                  
                  DAE.ARRAY(array = array)  => begin
                    ListUtil.mapBoolOr(array, containsInitialCall)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= /***************************************************/ =#
         #= /* traverse DAE.Exp */ =#
         #= /***************************************************/ =#

         #= Traverses all subexpressions of an expression.
          Takes a function and an extra argument passed through the traversal.
          The function can potentially change the expression. In such cases,
          the changes are made bottom-up, i.e. a subexpression is traversed
          and changed before the complete expression is traversed.

          NOTE: The user-provided function is not allowed to fail! If you want to
          detect a failure, return NONE() in your user-provided datatype. =#
        function traverseExpBottomUp(inExp::DAE.Exp, inFunc::FuncExpType, inExtArg::T)  where {T}
              local outExtArg::T
              local outExp::DAE.Exp

              (outExp, outExtArg) = begin
                  local e1_1::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local e4_1::DAE.Exp
                  local ext_arg::T
                  local op::Operator
                  local rel::FuncExpType
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local fn::Absyn.Path
                  local scalar::Bool
                  local tp::Type
                  local t::Type
                  local i::ModelicaInteger
                  local lstexpl_1::List{List{DAE.Exp}}
                  local lstexpl::List{List{DAE.Exp}}
                  local dim::ModelicaInteger
                  local str::String
                  local localDecls::List{DAE.Element}
                  local fieldNames::List{String}
                  local attr::DAE.CallAttributes
                  local cases::List{DAE.MatchCase}
                  local cases_1::List{DAE.MatchCase}
                  local matchTy::DAE.MatchType
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local riters_1::DAE.ReductionIterators
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local aliases::List{List{String}}
                  local clk::DAE.ClockKind
                  local clk1::DAE.ClockKind
                  local typeVars::List{DAE.Type}
                @match inExp begin
                  DAE.EMPTY(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.ICONST(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.RCONST(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.SCONST(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.BCONST(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.CLKCONST(clk)  => begin
                      (clk1, ext_arg) = traverseExpClk(clk, inFunc, inExtArg)
                      e = if referenceEq(clk1, clk)
                            inExp
                          else
                            DAE.CLKCONST(clk1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.CREF(cr, tp)  => begin
                      (cr_1, ext_arg) = traverseExpCref(cr, inFunc, inExtArg)
                      e = if referenceEq(cr, cr_1)
                            inExp
                          else
                            DAE.CREF(cr_1, tp)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.UNARY(operator = op, exp = e1)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.UNARY(op, e1_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.BINARY(e1_1, op, e2_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.LUNARY(operator = op, exp = e1)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.LUNARY(op, e1_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.LBINARY(e1_1, op, e2_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.RELATION(e1_1, op, e2_1, index_, isExpisASUB)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      (e3_1, ext_arg) = traverseExpBottomUp(e3, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                            inExp
                          else
                            DAE.IFEXP(e1_1, e2_1, e3_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.CALL(path = fn, expLst = expl, attr = attr)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.CALL(fn, expl_1, attr)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.RECORD(path = fn, exps = expl, comp = fieldNames, ty = tp)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.RECORD(fn, expl_1, fieldNames, tp)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.PARTEVALFUNCTION(fn, expl, tp, t)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.PARTEVALFUNCTION(fn, expl_1, tp, t)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.ARRAY(ty = tp, scalar = scalar, array = expl)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.ARRAY(tp, scalar, expl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.MATRIX(ty = tp, integer = dim, matrix = lstexpl)  => begin
                      (lstexpl_1, ext_arg) = traverseExpMatrix(lstexpl, inFunc, inExtArg)
                      e = if referenceEq(lstexpl, lstexpl_1)
                            inExp
                          else
                            DAE.MATRIX(tp, dim, lstexpl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.RANGE(ty = tp, start = e1, step = NONE(), stop = e2)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.RANGE(tp, e1_1, NONE(), e2_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.RANGE(ty = tp, start = e1, step = SOME(e2), stop = e3)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      (e3_1, ext_arg) = traverseExpBottomUp(e3, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                            inExp
                          else
                            DAE.RANGE(tp, e1_1, SOME(e2_1), e3_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.TUPLE(PR = expl)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.TUPLE(expl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.CAST(ty = tp, exp = e1)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.CAST(tp, e1_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.ASUB(exp = e1, sub = expl)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(expl, expl_1)
                            inExp
                          else
                            makeASUB(e1_1, expl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.TSUB(e1, i, tp)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.TSUB(e1_1, i, tp)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  e1 && DAE.RSUB(__)  => begin
                       #=  unary
                       =#
                       #=  binary
                       =#
                       #=  logical unary
                       =#
                       #=  logical binary
                       =#
                       #=  relation
                       =#
                       #=  if expressions
                       =#
                      (e1_1, ext_arg) = traverseExpBottomUp(e1.exp, inFunc, inExtArg)
                      if ! referenceEq(e1.exp, e1_1)
                        e1.exp = e1_1
                      end
                      (e1, ext_arg) = inFunc(e1, ext_arg)
                    (e1, ext_arg)
                  end
                  
                  DAE.SIZE(exp = e1, sz = NONE())  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.SIZE(e1_1, NONE())
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.SIZE(exp = e1, sz = SOME(e2))  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.SIZE(e1_1, SOME(e2_1))
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.REDUCTION(reductionInfo = reductionInfo, expr = e1, iterators = riters)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (riters_1, ext_arg) = traverseReductionIterators(riters, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(riters, riters_1)
                            inExp
                          else
                            DAE.REDUCTION(reductionInfo, e1_1, riters_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.CONS(e1, e2)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      (e2_1, ext_arg) = traverseExpBottomUp(e2, inFunc, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.CONS(e1_1, e2_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.LIST(expl)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.LIST(expl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.META_TUPLE(expl)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.META_TUPLE(expl_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.META_OPTION(NONE())  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.META_OPTION(SOME(e1))  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.META_OPTION(SOME(e1_1))
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.BOX(e1)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.BOX(e1_1)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.UNBOX(e1, tp)  => begin
                      (e1_1, ext_arg) = traverseExpBottomUp(e1, inFunc, inExtArg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.UNBOX(e1_1, tp)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.METARECORDCALL(fn, expl, fieldNames, i, typeVars)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.METARECORDCALL(fn, expl_1, fieldNames, i, typeVars)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.MATCHEXPRESSION(matchTy, expl, aliases, localDecls, cases, tp)  => begin
                      (expl_1, ext_arg) = traverseExpList(expl, inFunc, inExtArg)
                      (cases_1, ext_arg) = Patternm.traverseCases(cases, inFunc, ext_arg)
                      e = if referenceEq(expl, expl_1) && referenceEq(cases, cases_1)
                            inExp
                          else
                            DAE.MATCHEXPRESSION(matchTy, expl_1, aliases, localDecls, cases_1, tp)
                          end
                      (e, ext_arg) = inFunc(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  DAE.SHARED_LITERAL(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.PATTERN(__)  => begin
                      (e, ext_arg) = inFunc(inExp, inExtArg)
                    (e, ext_arg)
                  end
                  
                  DAE.CODE(__)  => begin
                    (inExp, inExtArg)
                  end
                  
                  _  => begin
                        str = ExpressionDump.printExpStr(inExp)
                        str = "Expression.traverseExpBottomUp or one of the user-defined functions using it is not implemented correctly: " + str
                        Error.addInternalError(str, sourceInfo())
                      fail()
                  end
                end
              end
               #=  MetaModelica list
               =#
               #=  ---------------------
               =#
               #=  Don't traverse the local declarations; we don't store bindings there (yet)
               =#
               #=  Why don't we call inFunc() for these expressions?
               =#
          (outExp, outExtArg)
        end

         #= Like traverseExpBottomUp but passes a default 0 argument =#
        function traverseExpDummy(inExp::DAE.Exp, func::FuncExpType) ::DAE.Exp 
              local outExp::DAE.Exp

              (outExp, _) = traverseExpBottomUp(inExp, traverseExpDummyHelper, func)
          outExp
        end

         #= Like traverseExpBottomUp but does not use an extra argument =#
        function traverseExpDummyHelper(inExp::DAE.Exp, func::FuncExpType) ::Tuple{DAE.Exp, FuncExpType} 
              local outFunc::FuncExpType
              local outExp::DAE.Exp

              outExp = func(inExp)
              outFunc = func
          (outExp, outFunc)
        end

         #= This function is used as input to a traverse function that does not traverse all subexpressions.
        The extra argument is a tuple of the actul function to call on each subexpression and the extra argument. =#
        function traverseSubexpressionsHelper(inExp::DAE.Exp, itpl::Tuple{<:FuncExpType, Type_a}) ::Tuple{DAE.Exp, Tuple{FuncExpType, Type_a}} 
              local otpl::Tuple{FuncExpType, Type_a}
              local outExp::DAE.Exp

              local rel::FuncExpType
              local ext_arg::Type_a
              local ext_arg2::Type_a

              (rel, ext_arg) = itpl
              (outExp, ext_arg2) = traverseExpBottomUp(inExp, rel, ext_arg)
              otpl = if referenceEq(ext_arg, ext_arg2)
                    itpl
                  else
                    (rel, ext_arg2)
                  end
          (outExp, otpl)
        end

         #= This function is used as input to a traverse function that does not traverse all subexpressions.
        The extra argument is a tuple of the actul function to call on each subexpression and the extra argument. =#
        function traverseSubexpressions(e::DAE.Exp, arg::Type_a, func::FuncExpType) ::Tuple{DAE.Exp, Type_a} 



              (e, arg) = traverseExpBottomUp(e, func, arg)
          (e, arg)
        end

         #= This function is used as input to a traverse function that does not traverse all subexpressions.
        The extra argument is a tuple of the actul function to call on each subexpression and the extra argument.
         =#
        function traverseSubexpressionsDummyHelper(inExp::DAE.Exp, inFunc::FuncExpType) ::Tuple{DAE.Exp, FuncExpType} 
              local outFunc::FuncExpType
              local outExp::DAE.Exp

              (outExp, outFunc) = traverseExpBottomUp(inExp, traverseExpDummyHelper, inFunc)
          (outExp, outFunc)
        end

         #= This function is used as input to a traverse function that does not traverse all subexpressions.
        The extra argument is a tuple of the actual function to call on each subexpression and the extra argument. =#
        function traverseSubexpressionsTopDownHelper(inExp::DAE.Exp, itpl::Tuple{<:FuncExpType2, Type_a}) ::Tuple{DAE.Exp, Tuple{FuncExpType2, Type_a}} 
              local otpl::Tuple{FuncExpType2, Type_a}
              local outExp::DAE.Exp

              local rel::FuncExpType2
              local ext_arg::Type_a
              local ext_arg2::Type_a

              (rel, ext_arg) = itpl
              (outExp, ext_arg2) = traverseExpTopDown(inExp, rel, ext_arg)
              otpl = if referenceEq(ext_arg, ext_arg2)
                    itpl
                  else
                    (rel, ext_arg2)
                  end
          (outExp, otpl)
        end

         #= author: PA
           Helper function to traverseExpBottomUp, traverses matrix expressions. =#
        function traverseExpMatrix(inMatrix::List{<:List{<:DAE.Exp}}, func::FuncExpType, inTypeA::Type_a) ::Tuple{List{List{DAE.Exp}}, Type_a} 
              local outTypeA::Type_a = inTypeA
              local outMatrix::List{List{DAE.Exp}} = nil

              local row_1::List{DAE.Exp}
              local same::Bool = true

              for row in inMatrix
                (row_1, outTypeA) = traverseExpList(row, func, outTypeA)
                same = if referenceEq(row, row_1)
                      same
                    else
                      false
                    end
                outMatrix = _cons(row_1, outMatrix)
              end
              if same
                outMatrix = inMatrix
              else
                outMatrix = MetaModelica.Dangerous.listReverseInPlace(outMatrix)
              end
          (outMatrix, outTypeA)
        end

         #= Calls traverseExpBottomUp for each element of list. =#
        function traverseExpList(inExpl::List{DAE.Exp}, rel::FuncExpType, iext_arg::ArgT)  where {ArgT}
              local ext_arg::ArgT = iext_arg
              local expl::List{DAE.Exp}

              local e1::DAE.Exp
              local allEq::Bool = true
              local delst::DoubleEnded.MutableList{DAE.Exp}
              local nEq::ModelicaInteger = 0

              for e in inExpl
                (e1, ext_arg) = traverseExpBottomUp(e, rel, ext_arg)
                if if allEq
                      ! referenceEq(e, e1)
                    else
                      false
                    end
                  allEq = false
                  delst = DoubleEnded.empty(e1)
                  for elt in inExpl
                    if nEq < 1
                      break
                    end
                    DoubleEnded.push_back(delst, elt)
                    nEq = nEq - 1
                  end
                end
                if allEq
                  nEq = nEq + 1
                else
                  DoubleEnded.push_back(delst, e1)
                end
              end
               #=  Preserve reference equality without any allocation if nothing changed
               =#
              expl = if allEq
                    inExpl
                  else
                    DoubleEnded.toListAndClear(delst)
                  end
          (expl, ext_arg)
        end

         #= Traverses all subexpressions of an expression.
          Takes a function and an extra argument passed through the traversal.
          The function can potentially change the expression. In such cases,
          the changes are made top-down, i.e. a subexpression is traversed
          and changed after the complete expression is traversed. =#
        function traverseExpTopDown(inExp::DAE.Exp, func::FuncExpType, ext_arg::Type_a) ::Tuple{DAE.Exp, Type_a} 
              local outArg::Type_a
              local outExp::DAE.Exp

              local cont::Bool

              (outExp, cont, outArg) = func(inExp, ext_arg)
              (outExp, outArg) = traverseExpTopDown1(cont, outExp, func, outArg)
          (outExp, outArg)
        end

        function traverseExpClk(inClk::DAE.ClockKind, func::FuncExpType, inArg::Type_a) ::Tuple{DAE.ClockKind, Type_a} 
              local outArg::Type_a
              local outClk::DAE.ClockKind

              (outClk, outArg) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local ea::DAE.Exp
                  local eb::DAE.Exp
                  local intvl::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local arg::Type_a
                  local str::String
                  local clk::DAE.ClockKind
                @match inClk begin
                  DAE.INTEGER_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpBottomUp(e1, func, inArg)
                      (eb, arg) = traverseExpBottomUp(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.INTEGER_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  DAE.REAL_CLOCK(e)  => begin
                      (e1, arg) = traverseExpBottomUp(e, func, inArg)
                      clk = if referenceEq(e1, e)
                            inClk
                          else
                            DAE.REAL_CLOCK(e1)
                          end
                    (clk, arg)
                  end
                  
                  DAE.BOOLEAN_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpBottomUp(e1, func, inArg)
                      (eb, arg) = traverseExpBottomUp(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.BOOLEAN_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  DAE.SOLVER_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpBottomUp(e1, func, inArg)
                      (eb, arg) = traverseExpBottomUp(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.SOLVER_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  _  => begin
                      (inClk, inArg)
                  end
                end
              end
          (outClk, outArg)
        end

        function traverseExpTopDownClockHelper(inClk::DAE.ClockKind, func::FuncExpType, inArg::Type_a) ::Tuple{DAE.ClockKind, Type_a} 
              local outArg::Type_a
              local outClk::DAE.ClockKind

              (outClk, outArg) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local ea::DAE.Exp
                  local eb::DAE.Exp
                  local intvl::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local arg::Type_a
                  local str::String
                  local clk::DAE.ClockKind
                @match inClk begin
                  DAE.INTEGER_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpTopDown(e1, func, inArg)
                      (eb, arg) = traverseExpTopDown(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.INTEGER_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  DAE.REAL_CLOCK(e)  => begin
                      (e1, arg) = traverseExpTopDown(e, func, inArg)
                      clk = if referenceEq(e1, e)
                            inClk
                          else
                            DAE.REAL_CLOCK(e1)
                          end
                    (clk, arg)
                  end
                  
                  DAE.BOOLEAN_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpTopDown(e1, func, inArg)
                      (eb, arg) = traverseExpTopDown(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.BOOLEAN_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  DAE.SOLVER_CLOCK(e1, e2)  => begin
                      (ea, arg) = traverseExpTopDown(e1, func, inArg)
                      (eb, arg) = traverseExpTopDown(e2, func, inArg)
                      clk = if referenceEq(ea, e1) && referenceEq(eb, e2)
                            inClk
                          else
                            DAE.SOLVER_CLOCK(ea, eb)
                          end
                    (clk, arg)
                  end
                  
                  _  => begin
                      (inClk, inArg)
                  end
                end
              end
          (outClk, outArg)
        end

         #= Helper for traverseExpTopDown. =#
        function traverseExpTopDown1(cont::Bool, inExp::DAE.Exp, func::FuncExpType, inArg::Type_a) ::Tuple{DAE.Exp, Type_a} 
              local outArg::Type_a
              local outExp::DAE.Exp

              (outExp, outArg) = begin
                  local e1_1::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local e4_1::DAE.Exp
                  local ext_arg_1::Type_a
                  local ext_arg_2::Type_a
                  local ext_arg::Type_a
                  local ext_arg_3::Type_a
                  local ext_arg_4::Type_a
                  local op::Operator
                  local rel::FuncExpType
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local fn::Absyn.Path
                  local scalar::Bool
                  local tp::Type
                  local et::Type
                  local t::Type
                  local i::ModelicaInteger
                  local str::String
                  local fieldNames::List{String}
                  local lstexpl_1::List{List{DAE.Exp}}
                  local lstexpl::List{List{DAE.Exp}}
                  local dim::ModelicaInteger
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local oe1::Option{DAE.Exp}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local attr::DAE.CallAttributes
                  local localDecls::List{DAE.Element}
                  local matchType::DAE.MatchType
                  local cases::List{DAE.MatchCase}
                  local cr::ComponentRef
                  local cr_1::ComponentRef
                  local aliases::List{List{String}}
                  local clk::DAE.ClockKind
                  local clk1::DAE.ClockKind
                  local typeVars::List{DAE.Type}
                @match (cont, inExp, func, inArg) begin
                  (false, _, _, _)  => begin
                    (inExp, inArg)
                  end
                  
                  (_, DAE.ICONST(_), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.RCONST(_), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.SCONST(_), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.BCONST(_), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.CLKCONST(clk), _, ext_arg)  => begin
                      (clk1, ext_arg) = traverseExpTopDownClockHelper(clk, func, ext_arg)
                      e = if referenceEq(clk1, clk)
                            inExp
                          else
                            DAE.CLKCONST(clk1)
                          end
                    (e, ext_arg)
                  end
                  
                  (_, DAE.ENUM_LITERAL(__), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.CREF(cr, tp), rel, ext_arg)  => begin
                      (cr_1, ext_arg_1) = traverseExpTopDownCrefHelper(cr, rel, ext_arg)
                    (if referenceEq(cr, cr_1)
                          inExp
                        else
                          DAE.CREF(cr_1, tp)
                        end, ext_arg_1)
                  end
                  
                  (_, DAE.UNARY(operator = op, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (if referenceEq(e1, e1_1)
                          inExp
                        else
                          DAE.UNARY(op, e1_1)
                        end, ext_arg_1)
                  end
                  
                  (_, DAE.BINARY(exp1 = e1, operator = op, exp2 = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.BINARY(e1_1, op, e2_1)
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.LUNARY(operator = op, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (if referenceEq(e1, e1_1)
                          inExp
                        else
                          DAE.LUNARY(op, e1_1)
                        end, ext_arg_1)
                  end
                  
                  (_, DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.LBINARY(e1_1, op, e2_1)
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.RELATION(e1_1, op, e2_1, index_, isExpisASUB)
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                      (e3_1, ext_arg_3) = traverseExpTopDown(e3, rel, ext_arg_2)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                          inExp
                        else
                          DAE.IFEXP(e1_1, e2_1, e3_1)
                        end, ext_arg_3)
                  end
                  
                  (_, DAE.CALL(path = fn, expLst = expl, attr = attr), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.CALL(fn, expl_1, attr), ext_arg_1)
                  end
                  
                  (_, DAE.RECORD(path = fn, exps = expl, comp = fieldNames, ty = tp), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.RECORD(fn, expl_1, fieldNames, tp), ext_arg_1)
                  end
                  
                  (_, DAE.PARTEVALFUNCTION(fn, expl, tp, t), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.PARTEVALFUNCTION(fn, expl_1, tp, t), ext_arg_1)
                  end
                  
                  (_, DAE.ARRAY(ty = tp, scalar = scalar, array = expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.ARRAY(tp, scalar, expl_1), ext_arg_1)
                  end
                  
                  (_, DAE.MATRIX(ty = tp, integer = dim, matrix = lstexpl), rel, ext_arg)  => begin
                      (lstexpl_1, ext_arg_1) = traverseExpMatrixTopDown(lstexpl, rel, ext_arg)
                    (DAE.MATRIX(tp, dim, lstexpl_1), ext_arg_1)
                  end
                  
                  (_, DAE.RANGE(ty = tp, start = e1, step = NONE(), stop = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.RANGE(tp, e1_1, NONE(), e2_1)
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.RANGE(ty = tp, start = e1, step = SOME(e2), stop = e3), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                      (e3_1, ext_arg_3) = traverseExpTopDown(e3, rel, ext_arg_2)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                          inExp
                        else
                          DAE.RANGE(tp, e1_1, SOME(e2_1), e3_1)
                        end, ext_arg_3)
                  end
                  
                  (_, DAE.TUPLE(PR = expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.TUPLE(expl_1), ext_arg_1)
                  end
                  
                  (_, DAE.CAST(ty = tp, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (DAE.CAST(tp, e1_1), ext_arg_1)
                  end
                  
                  (_, DAE.ASUB(exp = e1, sub = expl_1), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (expl_1, ext_arg_2) = traverseExpListTopDown(expl_1, rel, ext_arg_1)
                    (makeASUB(e1_1, expl_1), ext_arg_2)
                  end
                  
                  (_, DAE.TSUB(e1, i, tp), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (DAE.TSUB(e1_1, i, tp), ext_arg_1)
                  end
                  
                  (_, e1 && DAE.RSUB(__), rel, ext_arg)  => begin
                       #=  unary
                       =#
                       #=  binary
                       =#
                       #=  logical unary
                       =#
                       #=  logical binary
                       =#
                       #=  relation
                       =#
                       #=  if expressions
                       =#
                       #=  call
                       =#
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1.exp, rel, ext_arg)
                      if ! referenceEq(e1.exp, e1_1)
                        e1.exp = e1_1
                      end
                    (e1, ext_arg_1)
                  end
                  
                  (_, DAE.SIZE(exp = e1, sz = NONE()), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (DAE.SIZE(e1_1, NONE()), ext_arg_1)
                  end
                  
                  (_, DAE.SIZE(exp = e1, sz = SOME(e2)), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.SIZE(e1_1, SOME(e2_1))
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.CODE(__), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.REDUCTION(reductionInfo = reductionInfo, expr = e1, iterators = riters), rel, ext_arg)  => begin
                      (e1, ext_arg) = traverseExpTopDown(e1, rel, ext_arg)
                      (riters, ext_arg) = traverseReductionIteratorsTopDown(riters, rel, ext_arg)
                    (DAE.REDUCTION(reductionInfo, e1, riters), ext_arg)
                  end
                  
                  (_, DAE.EMPTY(__), _, _)  => begin
                    (inExp, inArg)
                  end
                  
                  (_, DAE.CONS(e1, e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                      (e2_1, ext_arg_2) = traverseExpTopDown(e2, rel, ext_arg_1)
                    (if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                          inExp
                        else
                          DAE.CONS(e1_1, e2_1)
                        end, ext_arg_2)
                  end
                  
                  (_, DAE.LIST(expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.LIST(expl_1), ext_arg_1)
                  end
                  
                  (_, DAE.META_TUPLE(expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.META_TUPLE(expl_1), ext_arg_1)
                  end
                  
                  (_, DAE.META_OPTION(oe1), rel, ext_arg)  => begin
                      (oe1, ext_arg) = traverseExpOptTopDown(oe1, rel, ext_arg)
                    (DAE.META_OPTION(oe1), ext_arg)
                  end
                  
                  (_, DAE.MATCHEXPRESSION(matchType, expl, aliases, localDecls, cases, et), rel, ext_arg)  => begin
                      (expl, ext_arg) = traverseExpListTopDown(expl, rel, ext_arg)
                      (cases, ext_arg) = Patternm.traverseCasesTopDown(cases, rel, ext_arg)
                    (DAE.MATCHEXPRESSION(matchType, expl, aliases, localDecls, cases, et), ext_arg)
                  end
                  
                  (_, DAE.METARECORDCALL(fn, expl, fieldNames, i, typeVars), rel, ext_arg)  => begin
                      (expl_1, ext_arg_1) = traverseExpListTopDown(expl, rel, ext_arg)
                    (DAE.METARECORDCALL(fn, expl_1, fieldNames, i, typeVars), ext_arg_1)
                  end
                  
                  (_, DAE.UNBOX(e1, tp), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (DAE.UNBOX(e1_1, tp), ext_arg_1)
                  end
                  
                  (_, DAE.BOX(e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg_1) = traverseExpTopDown(e1, rel, ext_arg)
                    (DAE.BOX(e1_1), ext_arg_1)
                  end
                  
                  (_, DAE.PATTERN(__), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  (_, DAE.SHARED_LITERAL(__), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  _  => begin
                        str = ExpressionDump.printExpStr(inExp)
                        str = getInstanceName() + " or " + System.dladdr(func) + "not implemented correctly: " + str
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  MetaModelica list
               =#
          (outExp, outArg)
        end

         #= author: PA
           Helper function to traverseExpTopDown, traverses matrix expressions. =#
        function traverseExpMatrixTopDown(inMatrix::List{<:List{<:DAE.Exp}}, func::FuncExpType, inTypeA::Type_a) ::Tuple{List{List{DAE.Exp}}, Type_a} 
              local outTypeA::Type_a = inTypeA
              local outMatrix::List{List{DAE.Exp}} = nil

              local row_1::List{DAE.Exp}
              local same::Bool = true

              for row in inMatrix
                (row_1, outTypeA) = traverseExpListTopDown(row, func, outTypeA)
                same = if referenceEq(row, row_1)
                      same
                    else
                      false
                    end
                outMatrix = _cons(row_1, outMatrix)
              end
              if same
                outMatrix = inMatrix
              else
                outMatrix = MetaModelica.Dangerous.listReverseInPlace(outMatrix)
              end
          (outMatrix, outTypeA)
        end

         #=  author PA:
         Calls traverseExpListTopDown for each element of list. =#
        function traverseExpListTopDown(inExpl::List{<:DAE.Exp}, rel::FuncExpType, inExt_arg::Type_a) ::Tuple{List{DAE.Exp}, Type_a} 
              local outA::Type_a = inExt_arg
              local outExpl::List{DAE.Exp} = nil

              local e_1::DAE.Exp
              local same::Bool = true

              for e in inExpl
                (e_1, outA) = traverseExpTopDown(e, rel, outA)
                same = if referenceEq(e, e_1)
                      same
                    else
                      false
                    end
                outExpl = _cons(e_1, outExpl)
              end
              if same
                outExpl = inExpl
              else
                outExpl = MetaModelica.Dangerous.listReverseInPlace(outExpl)
              end
          (outExpl, outA)
        end

         #= Calls traverseExpBottomUp for SOME(exp) and does nothing for NONE =#
        function traverseExpOpt(inExp::Option{<:DAE.Exp}, func::FuncExpType, inTypeA::Type_a) ::Tuple{Option{DAE.Exp}, Type_a} 
              local outTypeA::Type_a
              local outExp::Option{DAE.Exp}

              (outExp, outTypeA) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local a::Type_a
                  local oe::Option{DAE.Exp}
                @match (inExp, func, inTypeA) begin
                  (NONE(), _, a)  => begin
                    (inExp, a)
                  end
                  
                  (oe && SOME(e), _, a)  => begin
                      (e1, a) = traverseExpBottomUp(e, func, a)
                      oe = if referenceEq(e, e1)
                            oe
                          else
                            SOME(e1)
                          end
                    (oe, a)
                  end
                end
              end
               #= /*In case external functions create a copy of NONE()*/ =#
          (outExp, outTypeA)
        end

         #= Calls traverseExpTopDown for SOME(exp) and does nothing for NONE =#
        function traverseExpOptTopDown(inExp::Option{<:DAE.Exp}, func::FuncExpType, inTypeA::Type_a) ::Tuple{Option{DAE.Exp}, Type_a} 
              local outA::Type_a
              local outExp::Option{DAE.Exp}

              (outExp, outA) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local a::Type_a
                @match (inExp, func, inTypeA) begin
                  (NONE(), _, a)  => begin
                    (NONE(), a)
                  end
                  
                  (SOME(e), _, a)  => begin
                      (e1, a) = traverseExpTopDown(e, func, a)
                    (if referenceEq(e, e1)
                          inExp
                        else
                          SOME(e1)
                        end, a)
                  end
                end
              end
          (outExp, outA)
        end

        function traverseExpCrefDims(inCref::DAE.ComponentRef, inFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outCref::DAE.ComponentRef

              (outCref, outArg) = begin
                  local id::DAE.Ident
                  local ty::DAE.Type
                  local new_ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local new_cr::DAE.ComponentRef
                  local arg::ArgT
                  local idx::ModelicaInteger
                @match inCref begin
                  DAE.CREF_QUAL(id, ty, subs, cr)  => begin
                      (new_cr, arg) = traverseExpCrefDims(cr, inFunc, inArg)
                      (new_ty, arg) = traverseExpTypeDims(ty, inFunc, inArg)
                      cr = if referenceEq(new_cr, cr) && referenceEq(new_ty, ty)
                            inCref
                          else
                            DAE.CREF_QUAL(id, new_ty, subs, new_cr)
                          end
                    (cr, arg)
                  end
                  
                  DAE.CREF_IDENT(id, ty, subs)  => begin
                      (new_ty, arg) = traverseExpTypeDims(ty, inFunc, inArg)
                      cr = if referenceEq(new_ty, ty)
                            inCref
                          else
                            DAE.CREF_IDENT(id, new_ty, subs)
                          end
                    (cr, arg)
                  end
                  
                  DAE.CREF_ITER(id, idx, ty, subs)  => begin
                      (new_ty, arg) = traverseExpTypeDims(ty, inFunc, inArg)
                      cr = if referenceEq(new_ty, ty)
                            inCref
                          else
                            DAE.CREF_ITER(id, idx, new_ty, subs)
                          end
                    (cr, arg)
                  end
                  
                  _  => begin
                      (inCref, inArg)
                  end
                end
              end
          (outCref, outArg)
        end

        function traverseExpTypeDims(inType::DAE.Type, inFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outType::DAE.Type

              (outType, outArg) = begin
                  local ty::DAE.Type
                  local new_ty::DAE.Type
                  local dims::List{DAE.Dimension}
                  local new_dims::List{DAE.Dimension}
                  local arg::ArgT
                  local changed::Bool
                  local state::ClassInf.State
                  local vars::List{DAE.Var}
                  local ec::DAE.EqualityConstraint
                @match inType begin
                  DAE.T_ARRAY(ty, dims)  => begin
                      (_, arg, changed) = traverseExpTypeDims2(dims, inFunc, inArg)
                      ty = if changed
                            DAE.T_ARRAY(ty, dims)
                          else
                            inType
                          end
                    (ty, arg)
                  end
                  
                  DAE.T_SUBTYPE_BASIC(state, vars, ty, ec)  => begin
                      (new_ty, arg) = traverseExpTypeDims(ty, inFunc, inArg)
                      ty = if referenceEq(new_ty, ty)
                            inType
                          else
                            DAE.T_SUBTYPE_BASIC(state, vars, ty, ec)
                          end
                    (ty, arg)
                  end
                  
                  _  => begin
                      (inType, inArg)
                  end
                end
              end
          (outType, outArg)
        end

        function traverseExpTypeDims2(inDims::List{DAE.Dimension}, inFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outChanged::Bool = false
              local outArg::ArgT = inArg
              local outDims::List{DAE.Dimension} = nil

              local changed::Bool
              local exp::DAE.Exp
              local new_exp::DAE.Exp

              for dim in inDims
                dim = begin
                  @match dim begin
                    DAE.DIM_EXP(exp)  => begin
                        (new_exp, outArg) = inFunc(exp, outArg)
                        changed = ! referenceEq(new_exp, exp)
                        outChanged = outChanged || changed
                      if changed
                            DAE.DIM_EXP(exp)
                          else
                            dim
                          end
                    end
                    
                    _  => begin
                        dim
                    end
                  end
                end
                outDims = _cons(dim, outDims)
              end
              outDims = if outChanged
                    listReverse(outDims)
                  else
                    inDims
                  end
          (outDims, outArg, outChanged)
        end

         #= 
        Author: BZ 2008-06, Extracts all ComponentRef from an Expression. =#
        function extractCrefsFromExp(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local ocrefs::List{DAE.ComponentRef}

              (_, ocrefs) = traverseExpBottomUp(inExp, traversingComponentRefFinder, nil)
          ocrefs
        end

         #= Extracts all unique ComponentRef from an Expression. =#
        function extractUniqueCrefsFromExp(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local ocrefs::List{DAE.ComponentRef}

               #=  ocrefs := List.unique(List.flatten(List.map1(extractCrefsFromExp(inExp), ComponentReference.expandCref, true)));
               =#
              ocrefs = ListUtil.unique(extractCrefsFromExp(inExp))
          ocrefs
        end

         #=  author mahge: Same as extractCrefsFromExp except:
          This function will not treat der(), pre() and start() as calls
          but as unique ids. i.e. x is different from der(x) and given der(x) x will not
          be extreacted as a unique id. Instead you get $DER.x. Same oes for pre and start. =#
        function extractCrefsFromExpDerPreStart(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local ocrefs::List{DAE.ComponentRef}

              (_, ocrefs) = traverseExpDerPreStart(inExp, traversingComponentRefFinder, nil)
          ocrefs
        end

         #= author mahge: Same as extractUniqueCrefsFromExp except:
          This function will not treat der(), pre() and start() as calls
          but as unique ids. i.e. x is different from der(x) and given der(x) x will not
          be extreacted as a unique id. Instead you get $DER.x. Same oes for pre and start.. =#
        function extractUniqueCrefsFromExpDerPreStart(inExp::DAE.Exp) ::List{DAE.ComponentRef} 
              local ocrefs::List{DAE.ComponentRef}

               #=  ocrefs := List.unique(List.flatten(List.map1(extractCrefsFromExp(inExp), ComponentReference.expandCref, true)));
               =#
              ocrefs = ListUtil.unique(extractCrefsFromExpDerPreStart(inExp))
          ocrefs
        end

         #= authot mahge: Extracts all unique ComponentRef from Statments. =#
        function extractUniqueCrefsFromStatmentS(inStmts::List{<:DAE.Statement}) ::Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}} 
              local ocrefs::Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}}

              local lhscreflstlst::List{List{DAE.ComponentRef}}
              local rhscreflstlst::List{List{DAE.ComponentRef}}
              local orhscrefs::List{DAE.ComponentRef}
              local olhscrefs::List{DAE.ComponentRef}

              (lhscreflstlst, rhscreflstlst) = ListUtil.map_2(inStmts, extractCrefsStatment)
              orhscrefs = ListUtil.unique(ListUtil.flatten(rhscreflstlst))
              olhscrefs = ListUtil.unique(ListUtil.flatten(lhscreflstlst))
              ocrefs = (olhscrefs, orhscrefs)
          ocrefs
        end

         #= Extracts all ComponentRef from a Statment. =#
        function extractCrefsStatment(inStmt::DAE.Statement) ::Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}} 
              local orcrefs::List{DAE.ComponentRef}
              local olcrefs::List{DAE.ComponentRef}

              (olcrefs, orcrefs) = begin
                  local exp1::Exp
                  local exp2::Exp
                  local expLst::List{DAE.Exp}
                  local stmtLst::List{DAE.Statement}
                @match inStmt begin
                  DAE.STMT_ASSIGN(exp1 = exp1, exp = exp2)  => begin
                      olcrefs = extractCrefsFromExpDerPreStart(exp1)
                      orcrefs = extractCrefsFromExpDerPreStart(exp2)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_TUPLE_ASSIGN(expExpLst = expLst, exp = exp2)  => begin
                      olcrefs = ListUtil.flatten(ListUtil.map(expLst, extractCrefsFromExpDerPreStart))
                      orcrefs = extractCrefsFromExpDerPreStart(exp2)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_ASSIGN_ARR(lhs = exp1, exp = exp2)  => begin
                      olcrefs = extractCrefsFromExpDerPreStart(exp1)
                      orcrefs = extractCrefsFromExpDerPreStart(exp2)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_IF(statementLst = stmtLst)  => begin
                      (olcrefs, orcrefs) = extractUniqueCrefsFromStatmentS(stmtLst)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_FOR(statementLst = stmtLst)  => begin
                      (olcrefs, orcrefs) = extractUniqueCrefsFromStatmentS(stmtLst)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_WHILE(statementLst = stmtLst)  => begin
                      (olcrefs, orcrefs) = extractUniqueCrefsFromStatmentS(stmtLst)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_WHEN(statementLst = stmtLst)  => begin
                      (olcrefs, orcrefs) = extractUniqueCrefsFromStatmentS(stmtLst)
                    (olcrefs, orcrefs)
                  end
                  
                  DAE.STMT_ASSERT(cond = exp1)  => begin
                      orcrefs = extractCrefsFromExpDerPreStart(exp1)
                    (nil, orcrefs)
                  end
                  
                  _  => begin
                      (nil, nil)
                  end
                end
              end
          (olcrefs, orcrefs)
        end

         #= Extracts all lhs crefs from Statements.
          author: ptaeuber =#
        function getLhsCrefsFromStatements(inStmts::List{<:DAE.Statement}) ::List{DAE.ComponentRef} 
              local lhsCrefs::List{DAE.ComponentRef}

              local lhsCrefsLst::List{List{DAE.ComponentRef}}

              lhsCrefsLst = ListUtil.map(inStmts, getLhsCrefsFromStatement)
              lhsCrefs = ListUtil.flatten(lhsCrefsLst)
          lhsCrefs
        end

         #= Extracts all lhs crefs from a statement.
          author: ptaeuber =#
        function getLhsCrefsFromStatement(inStmt::DAE.Statement) ::List{DAE.ComponentRef} 
              local lhsCrefs::List{DAE.ComponentRef}

              lhsCrefs = begin
                  local exp1::Exp
                  local exp2::Exp
                  local expLst::List{DAE.Exp}
                  local stmtLst::List{DAE.Statement}
                @match inStmt begin
                  DAE.STMT_ASSIGN(exp1 = exp1)  => begin
                      lhsCrefs = extractCrefsFromExpDerPreStart(exp1)
                    lhsCrefs
                  end
                  
                  DAE.STMT_TUPLE_ASSIGN(expExpLst = expLst)  => begin
                      lhsCrefs = ListUtil.flatten(ListUtil.map(expLst, extractCrefsFromExpDerPreStart))
                    lhsCrefs
                  end
                  
                  DAE.STMT_ASSIGN_ARR(lhs = exp1)  => begin
                      lhsCrefs = extractCrefsFromExpDerPreStart(exp1)
                    lhsCrefs
                  end
                  
                  DAE.STMT_IF(statementLst = stmtLst)  => begin
                      lhsCrefs = getLhsCrefsFromStatements(stmtLst)
                    lhsCrefs
                  end
                  
                  DAE.STMT_FOR(statementLst = stmtLst)  => begin
                      lhsCrefs = getLhsCrefsFromStatements(stmtLst)
                    lhsCrefs
                  end
                  
                  DAE.STMT_WHILE(statementLst = stmtLst)  => begin
                      lhsCrefs = getLhsCrefsFromStatements(stmtLst)
                    lhsCrefs
                  end
                  
                  DAE.STMT_WHEN(statementLst = stmtLst)  => begin
                      lhsCrefs = getLhsCrefsFromStatements(stmtLst)
                    lhsCrefs
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          lhsCrefs
        end

         #= 
         returns true if the expression contains any initial() call =#
        function expHasInitial(exp::DAE.Exp) ::Bool 
              local found::Bool

              (_, found) = traverseExpTopDown(exp, traversingexpHasInitial, false)
          found
        end

        function traversingexpHasInitial(exp::DAE.Exp, found::Bool) ::Tuple{DAE.Exp, Bool, Bool} 

              local cont::Bool


              if found
                cont = false
                return (exp, cont, found)
              end
              (cont, found) = begin
                @match exp begin
                  DAE.CALL(path = Absyn.IDENT("initial"))  => begin
                    (false, true)
                  end
                  
                  _  => begin
                      (true, found)
                  end
                end
              end
          (exp, cont, found)
        end

         #= 
        @author: adrpo 2011-04-29
         returns true if the expression contains crefs =#
        function expHasCrefs(inExp::DAE.Exp) ::Bool 
              local hasCrefs::Bool

              hasCrefs = begin
                  local b::Bool
                @match inExp begin
                  _  => begin
                      (_, b) = traverseExpTopDown(inExp, traversingComponentRefPresent, false)
                    b
                  end
                end
              end
          hasCrefs
        end

         #= Returns a true if the exp is a componentRef =#
        function traversingComponentRefPresent(inExp::DAE.Exp, found::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outFound::Bool
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outFound) = begin
                @match (inExp, found) begin
                  (_, true)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CREF(__), _)  => begin
                    (inExp, false, true)
                  end
                  
                  _  => begin
                      (inExp, true, false)
                  end
                end
              end
          (outExp, cont, outFound)
        end

         #= 
        Author: BZ 2008-06
        Exp traverser that Union the current ComponentRef with list if it is already there.
        Returns a list containing, unique, all componentRef in an Expression. =#
        function traversingComponentRefFinder(inExp::DAE.Exp, inCrefs::List{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, List{DAE.ComponentRef}} 
              local crefs::List{DAE.ComponentRef}
              local outExp::DAE.Exp

              (outExp, crefs) = begin
                  local cr::ComponentRef
                @match (inExp, inCrefs) begin
                  (DAE.CREF(componentRef = cr), crefs)  => begin
                      crefs = ListUtil.unionEltOnTrue(cr, crefs, ComponentReference.crefEqual)
                    (inExp, crefs)
                  end
                  
                  _  => begin
                      (inExp, inCrefs)
                  end
                end
              end
          (outExp, crefs)
        end

         #= 
        Author: BZ 2008-06
        Exp traverser that Union the current ComponentRef with list if it is already there.
        Returns a list containing, unique, all componentRef in an Expression. =#
        function traversingComponentRefFinderNoPreDer(inExp::DAE.Exp, inCrefs::List{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, Bool, List{DAE.ComponentRef}} 
              local crefs::List{DAE.ComponentRef}
              local cont::Bool
              local e::DAE.Exp

              (e, cont, crefs) = begin
                  local cr::ComponentRef
                @match (inExp, inCrefs) begin
                  (DAE.CREF(componentRef = cr), crefs)  => begin
                      crefs = ListUtil.unionEltOnTrue(cr, crefs, ComponentReference.crefEqual)
                    (inExp, false, crefs)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "der")), _)  => begin
                    (inExp, false, inCrefs)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "pre")), _)  => begin
                    (inExp, false, inCrefs)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "previous")), _)  => begin
                    (inExp, false, inCrefs)
                  end
                  
                  _  => begin
                      (inExp, true, inCrefs)
                  end
                end
              end
          (e, cont, crefs)
        end

         #= 
        Author: Frenkel TUD 2012-06
        Exp traverser that Union the current ComponentRef with list if it is already there.
        Returns a list containing, unique, all componentRef in an Expression and a second list
        containing all componentRef from a der function. =#
        function traversingDerAndComponentRefFinder(inExp::Tuple{<:DAE.Exp, Tuple{<:List{<:DAE.ComponentRef}, List{<:DAE.ComponentRef}}}) ::Tuple{DAE.Exp, Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}}} 
              local outExp::Tuple{DAE.Exp, Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}}}

              outExp = begin
                  local crefs::List{DAE.ComponentRef}
                  local dcrefs::List{DAE.ComponentRef}
                  local cr::ComponentRef
                  local ty::Type
                  local e::DAE.Exp
                @matchcontinue inExp begin
                  (e && DAE.CREF(cr, _), (crefs, dcrefs))  => begin
                      crefs = ListUtil.unionEltOnTrue(cr, crefs, ComponentReference.crefEqual)
                    (e, (crefs, dcrefs))
                  end
                  
                  (e && DAE.CALL(path = Absyn.IDENT(name = "der"), expLst = DAE.CREF(cr, _) <|  nil()), (crefs, dcrefs))  => begin
                      dcrefs = ListUtil.unionEltOnTrue(cr, dcrefs, ComponentReference.crefEqual)
                    (e, (crefs, dcrefs))
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
               #=  e = makeCrefExp(cr,ty);
               =#
               #=  e = makeCrefExp(cr,ty);
               =#
          outExp
        end

         #= author: Frenkel TUD 2011-04
          returns true if the expression contains the cref =#
        function expHasCref(inExp::DAE.Exp, inCr::DAE.ComponentRef) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasCref, (inCr, false))
          hasCref
        end

         #= 
        @author: Frenkel TUD 2011-04
        Returns a true if the exp the componentRef =#
        function traversingexpHasCref(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outTpl::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local cr::ComponentRef
                  local cr1::ComponentRef
                @matchcontinue (inExp, inTpl) begin
                  (DAE.CREF(componentRef = cr1), (cr, false))  => begin
                      b = ComponentReference.crefEqualNoStringCompare(cr, cr1)
                    (inExp, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, b))  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
          (outExp, cont, outTpl)
        end

         #= Returns a true if the exp contains a cref that starts with the given name =#
        function expHasCrefName(inExp::DAE.Exp, name::String) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasName, (name, false))
          hasCref
        end

         #= Returns a true if any exp contains a cref that starts with the given name =#
        function anyExpHasCrefName(inExps::List{<:DAE.Exp}, name::String) ::Bool 
              local hasCref::Bool

              hasCref = ListUtil.applyAndFold1(inExps, boolOr, expHasCrefName, name, false)
          hasCref
        end

         #= Returns a true if the exp contains a cref that starts with the given name =#
        function traversingexpHasName(inExp::DAE.Exp, inTpl::Tuple{<:String, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{String, Bool}} 
              local outTpl::Tuple{String, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local name::String
                  local cr::DAE.ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CREF(componentRef = cr), (name, false))  => begin
                      b = name == ComponentReference.crefFirstIdent(cr)
                    (inExp, ! b, if b
                          (name, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, b))  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
          (outExp, cont, outTpl)
        end

         #= 
        @author: Frenkel TUD 2012-06
         returns true if the expression contains the cref in function der =#
        function expHasDerCref(inExp::DAE.Exp, inCr::DAE.ComponentRef) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasDerCref, (inCr, false))
          hasCref
        end

         #= 
        @author: Frenkel TUD 2012-06
        Returns a true if the exp contains the componentRef in der =#
        function traversingexpHasDerCref(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outTpl::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local cr::ComponentRef
                  local cr1::ComponentRef
                @matchcontinue (inExp, inTpl) begin
                  (DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = cr1) <|  nil()), (cr, false))  => begin
                      b = ComponentReference.crefEqualNoStringCompare(cr, cr1)
                    (inExp, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = cr1) <|  nil()), (cr, false))  => begin
                      b = ComponentReference.crefPrefixOf(cr, cr1)
                    (inExp, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, b))  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
          (outExp, cont, outTpl)
        end

         #= 
         returns true if the expression contains the  function der =#
        function expHasDer(inExp::DAE.Exp) ::Bool 
              local hasCref::Bool

              (_, hasCref) = traverseExpTopDown(inExp, traversingexpHasDer, false)
          hasCref
        end

         #= 
        Returns a true if the exp contains in der =#
        function traversingexpHasDer(inExp::DAE.Exp, inTpl::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outTpl::Bool
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local cr::ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CALL(path = Absyn.IDENT("der")), false)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CREF(componentRef = cr), false) where (intEq(System.strncmp(ComponentReference.crefFirstIdent(cr), "DERAlias", 9), 0))  => begin
                    (inExp, false, true)
                  end
                  
                  (_, b)  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
               #= isAlias
               =#
               #= BackendDAE.derivativeNamePrefix
               =#
          (outExp, cont, outTpl)
        end

         #= 
         Returns true if the expression contains the operator pre =#
        function expHasPre(inExp::DAE.Exp) ::Bool 
              local hasPre::Bool

              (_, hasPre) = traverseExpTopDown(inExp, traversingexpHasPre, false)
          hasPre
        end

         #= 
        Returns true if the exp is pre(..) =#
        function traversingexpHasPre(inExp::DAE.Exp, inHasIt::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outHasIt::Bool
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outHasIt) = begin
                  local b::Bool
                  local cr::ComponentRef
                @match (inExp, inHasIt) begin
                  (DAE.CALL(path = Absyn.IDENT("pre")), false)  => begin
                    (inExp, false, true)
                  end
                  
                  (_, b)  => begin
                    (inExp, ! b, inHasIt)
                  end
                end
              end
          (outExp, cont, outHasIt)
        end

         #= 
        Returns true if the expression contains the operator previous =#
        function expHasPrevious(inExp::DAE.Exp) ::Bool 
              local hasPre::Bool

              (_, hasPre) = traverseExpTopDown(inExp, traversingexpHasPrevious, false)
          hasPre
        end

         #= 
        Returns true if the exp is pre(..) =#
        function traversingexpHasPrevious(inExp::DAE.Exp, inHasIt::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outHasIt::Bool
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outHasIt) = begin
                  local b::Bool
                  local cr::ComponentRef
                @match (inExp, inHasIt) begin
                  (DAE.CALL(path = Absyn.IDENT("previous")), false)  => begin
                    (inExp, false, true)
                  end
                  
                  (_, b)  => begin
                    (inExp, ! b, inHasIt)
                  end
                end
              end
          (outExp, cont, outHasIt)
        end

         #= 
        @author: Frenkel TUD 2011-04
         returns true if the expression contains the cref, but not in pre,change,edge =#
        function expHasCrefNoPreorDer(inExp::DAE.Exp, inCr::DAE.ComponentRef) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasCrefNoPreorDer, (inCr, false))
          hasCref
        end

         #= 
        @author: Frenkel TUD 2011-04
        Returns a true if the exp the componentRef =#
        function traversingexpHasCrefNoPreorDer(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outTpl::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CALL(path = Absyn.IDENT(name = "pre")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "previous")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CREF(componentRef = cr1), (cr, false))  => begin
                      b = ComponentReference.crefEqualNoStringCompare(cr, cr1)
                    (inExp, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, b))  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
               #= /* Not reachable...
                  case (DAE.CREF(componentRef = cr1), (cr,false))
                    equation
                      b = ComponentReference.crefPrefixOf(cr1,cr);
                    then (inExp,not b,(cr,b));
              */ =#
          (outExp, cont, outTpl)
        end

         #= 
         returns true if the expression contains one cref from the list, but not in pre(),change(),edge(),start(), delay() =#
        function expHasCrefsNoPreOrStart(inExp::DAE.Exp, inCr::List{<:DAE.ComponentRef}) ::Bool 
              local hasCref::Bool = false

              for cr in inCr
                (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasCrefNoPreOrStart, (cr, false))
                if hasCref
                  break
                end
              end
          hasCref
        end

         #= 
         returns true if the expression contains the cref, but not in pre(),change(),edge(),start(), delay() =#
        function expHasCrefNoPreOrStart(inExp::DAE.Exp, inCr::DAE.ComponentRef) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, traversingexpHasCrefNoPreOrStart, (inCr, false))
          hasCref
        end

         #= 
        return true if the exp the componentRef =#
        function traversingexpHasCrefNoPreOrStart(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outTpl::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CALL(path = Absyn.IDENT(name = "pre")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "previous")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "change")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "delay")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "edge")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "$_round")), _)  => begin
                    (inExp, false, inTpl)
                  end
                  
                  (DAE.CREF(componentRef = cr1), (cr, false))  => begin
                      b = ComponentReference.crefEqualNoStringCompare(cr, cr1)
                    (inExp, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, b))  => begin
                    (inExp, ! b, inTpl)
                  end
                end
              end
          (outExp, cont, outTpl)
        end

         #= 
        Returns a true if the exp contains the componentRef in if,sign,semiLinear =#
        function expHasCrefInIf(inExp::DAE.Exp, inCr::DAE.ComponentRef) ::Bool 
              local hasCref::Bool

              (_, (_, hasCref)) = traverseExpTopDown(inExp, expHasCrefInIfWork, (inCr, false))
          hasCref
        end

         #= 
        Returns a true if the exp contains the componentRef in if,sign,semiLinear =#
        function expHasCrefInIfWork(inExp::DAE.Exp, inTpl::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outTpl::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outTpl) = begin
                  local b::Bool
                  local i::ModelicaInteger
                  local cr::ComponentRef
                  local e1::DAE.Exp
                @match (inExp, inTpl) begin
                  (DAE.IFEXP(e1, _, _), (cr, false)) where (! isFunCall(e1, "noEvent"))  => begin
                      b = expHasCref(e1, cr)
                    (e1, true, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "smooth"), expLst = DAE.ICONST(i) <| e1 <|  nil()), (cr, false)) where (i > 1)  => begin
                    (e1, true, (cr, true))
                  end
                  
                  (DAE.CALL(__), (cr, false)) where (isEventTriggeringFunctionExp(inExp))  => begin
                      b = expHasCref(inExp, cr)
                    (inExp, true, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "semiLinear"), expLst = e1 <| _ <| _ <|  nil()), (cr, false))  => begin
                      b = expHasCref(e1, cr)
                    (e1, true, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "sign"), expLst = e1 <|  nil()), (cr, false))  => begin
                      b = expHasCref(e1, cr)
                    (e1, ! b, if b
                          (cr, b)
                        else
                          inTpl
                        end)
                  end
                  
                  (_, (_, true))  => begin
                    (inExp, false, inTpl)
                  end
                  
                  _  => begin
                      (inExp, true, inTpl)
                  end
                end
              end
          (outExp, cont, outTpl)
        end

         #= 
        Author: Frenkel TUD 2011-05, traverses all ComponentRef from an Expression. =#
        function traverseCrefsFromExp(inExp::DAE.Exp, inFunc::FuncCrefTypeA, inArg::Type_a) ::Type_a 
              local outArg::Type_a

              outArg = begin
                  local arg::Type_a
                @match (inExp, inFunc, inArg) begin
                  (_, _, _)  => begin
                      (_, (_, arg)) = traverseExpBottomUp(inExp, traversingCrefFinder, (inFunc, inArg))
                    arg
                  end
                end
              end
          outArg
        end

         #= 
        Author: Frenkel TUD 2011-05 =#
        function traversingCrefFinder(inExp::DAE.Exp, inTpl::Tuple{<:FuncCrefTypeA, Type_a}) ::Tuple{DAE.Exp, Tuple{FuncCrefTypeA, Type_a}} 
              local outTpl::Tuple{FuncCrefTypeA, Type_a}
              local outExp::DAE.Exp

              (outExp, outTpl) = begin
                  local arg::Type_a
                  local arg1::Type_a
                  local func::FuncCrefTypeA
                  local cr::ComponentRef
                @match (inExp, inTpl) begin
                  (DAE.CREF(cr, _), (func, arg))  => begin
                      arg1 = func(cr, arg)
                    (inExp, if referenceEq(arg, arg1)
                          inTpl
                        else
                          (func, arg1)
                        end)
                  end
                  
                  _  => begin
                      (inExp, inTpl)
                  end
                end
              end
          (outExp, outTpl)
        end

         #= 
        Author: Frenkel TUD 2010-02, Extracts all Division DAE.Exp from an Expression. =#
        function extractDivExpFromExp(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExps::List{DAE.Exp}

              (_, outExps) = traverseExpBottomUp(inExp, traversingDivExpFinder, nil)
          outExps
        end

         #= 
        Author: Frenkel TUD 2010-02
        Returns a list containing, all division DAE.Exp in an Expression. =#
        function traversingDivExpFinder(e::DAE.Exp, exps::List{<:DAE.Exp}) ::Tuple{DAE.Exp, List{DAE.Exp}} 
              local acc::List{DAE.Exp}
              local outExp::DAE.Exp

              (outExp, acc) = begin
                  local e2::DAE.Exp
                @match (e, exps) begin
                  (DAE.BINARY(operator = DAE.DIV(_), exp2 = e2), _)  => begin
                    (e, _cons(e2, exps))
                  end
                  
                  (DAE.BINARY(operator = DAE.DIV_ARR(_), exp2 = e2), _)  => begin
                    (e, _cons(e2, exps))
                  end
                  
                  (DAE.BINARY(operator = DAE.DIV_ARRAY_SCALAR(_), exp2 = e2), _)  => begin
                    (e, _cons(e2, exps))
                  end
                  
                  (DAE.BINARY(operator = DAE.DIV_SCALAR_ARRAY(_), exp2 = e2), _)  => begin
                    (e, _cons(e2, exps))
                  end
                  
                  _  => begin
                      (e, exps)
                  end
                end
              end
          (outExp, acc)
        end

         #= Traverses a list of expressions, calling traverseExpBidir on each
          expression. =#
        function traverseExpListBidir(inExpl::List{DAE.Exp}, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outExpl::List{DAE.Exp}

              (outExpl, outArg) = ListUtil.map2Fold(inExpl, traverseExpBidir, inEnterFunc, inExitFunc, inArg)
          (outExpl, outArg)
        end

         #= This function takes an expression and a tuple with an enter function, an exit
          function, and an extra argument. For each expression it encounters it calls
          the enter function with the expression and the extra argument. It then
          traverses all subexpressions in the expression and calls traverseExpBidir on
          them with the updated argument. Finally it calls the exit function, again with
          the updated argument. This means that this function is bidirectional, and can
          be used to emulate both top-down and bottom-up traversal. =#
        function traverseExpBidir(inExp::DAE.Exp, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outExp::DAE.Exp

              (outExp, outArg) = inEnterFunc(inExp, inArg)
              (outExp, outArg) = traverseExpBidirSubExps(outExp, inEnterFunc, inExitFunc, outArg)
              (outExp, outArg) = inExitFunc(outExp, outArg)
          (outExp, outArg)
        end

         #= Same as traverseExpBidir, but with an optional expression. Calls
          traverseExpBidir if the option is SOME(), or just returns the input if it's
          NONE() =#
        function traverseExpOptBidir(inExp::Option{DAE.Exp}, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outExp::Option{DAE.Exp}

              (outExp, outArg) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local arg::ArgT
                @match inExp begin
                  SOME(e)  => begin
                      (e1, arg) = traverseExpBidir(e, inEnterFunc, inExitFunc, inArg)
                    (if referenceEq(e, e1)
                          inExp
                        else
                          SOME(e1)
                        end, arg)
                  end
                  
                  _  => begin
                      (inExp, inArg)
                  end
                end
              end
          (outExp, outArg)
        end

         #= Helper function to traverseExpBidir. Traverses the subexpressions of an
          expression and calls traverseExpBidir on them. =#
        function traverseExpBidirSubExps(inExp::DAE.Exp, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outExp::DAE.Exp

              (outExp, outArg) = begin
                  local i::ModelicaInteger
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local oe1::Option{DAE.Exp}
                  local op::DAE.Operator
                  local cref::ComponentRef
                  local expl::List{DAE.Exp}
                  local mat_expl::List{List{DAE.Exp}}
                  local error_msg::String
                  local match_ty::DAE.MatchType
                  local match_decls::List{DAE.Element}
                  local match_cases::List{DAE.MatchCase}
                  local index::ModelicaInteger
                  local dim::ModelicaInteger
                  local opt_exp_asub::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local path::Absyn.Path
                  local b1::Bool
                  local ty::Type
                  local t::Type
                  local strl::List{String}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local attr::DAE.CallAttributes
                  local aliases::List{List{String}}
                  local arg::ArgT
                  local typeVars::List{DAE.Type}
                @match inExp begin
                  DAE.ICONST(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.RCONST(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.SCONST(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.BCONST(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.CREF(componentRef = cref, ty = ty)  => begin
                      (cref, arg) = traverseExpBidirCref(cref, inEnterFunc, inExitFunc, inArg)
                    (DAE.CREF(cref, ty), arg)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                    (DAE.BINARY(e1, op, e2), arg)
                  end
                  
                  DAE.UNARY(operator = op, exp = e1)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.UNARY(op, e1), arg)
                  end
                  
                  DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                    (DAE.LBINARY(e1, op, e2), arg)
                  end
                  
                  DAE.LUNARY(operator = op, exp = e1)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.LUNARY(op, e1), arg)
                  end
                  
                  DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index, optionExpisASUB = opt_exp_asub)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                    (DAE.RELATION(e1, op, e2, index, opt_exp_asub), arg)
                  end
                  
                  DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                      (e3, arg) = traverseExpBidir(e3, inEnterFunc, inExitFunc, arg)
                    (DAE.IFEXP(e1, e2, e3), arg)
                  end
                  
                  DAE.CALL(path = path, expLst = expl, attr = attr)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.CALL(path, expl, attr), arg)
                  end
                  
                  DAE.RECORD(path = path, exps = expl, comp = strl, ty = ty)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.RECORD(path, expl, strl, ty), arg)
                  end
                  
                  DAE.PARTEVALFUNCTION(path, expl, ty, t)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.PARTEVALFUNCTION(path, expl, ty, t), arg)
                  end
                  
                  DAE.ARRAY(ty = ty, scalar = b1, array = expl)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.ARRAY(ty, b1, expl), arg)
                  end
                  
                  DAE.MATRIX(ty = ty, integer = dim, matrix = mat_expl)  => begin
                      (mat_expl, arg) = ListUtil.map2Fold(mat_expl, traverseExpListBidir, inEnterFunc, inExitFunc, inArg)
                    (DAE.MATRIX(ty, dim, mat_expl), arg)
                  end
                  
                  DAE.RANGE(ty = ty, start = e1, step = oe1, stop = e2)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (oe1, arg) = traverseExpOptBidir(oe1, inEnterFunc, inExitFunc, arg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                    (DAE.RANGE(ty, e1, oe1, e2), arg)
                  end
                  
                  DAE.TUPLE(PR = expl)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.TUPLE(expl), arg)
                  end
                  
                  DAE.CAST(ty = ty, exp = e1)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.CAST(ty, e1), arg)
                  end
                  
                  DAE.ASUB(exp = e1, sub = expl)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, arg)
                    (DAE.ASUB(e1, expl), arg)
                  end
                  
                  e1 && DAE.RSUB(__)  => begin
                      (e2, arg) = traverseExpBidir(e1.exp, inEnterFunc, inExitFunc, inArg)
                      e1.exp = e2
                    (e1, arg)
                  end
                  
                  DAE.TSUB(e1, i, ty)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.TSUB(e1, i, ty), arg)
                  end
                  
                  DAE.SIZE(exp = e1, sz = oe1)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (oe1, arg) = traverseExpOptBidir(oe1, inEnterFunc, inExitFunc, arg)
                    (DAE.SIZE(e1, oe1), arg)
                  end
                  
                  DAE.CODE(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.REDUCTION(reductionInfo = reductionInfo, expr = e1, iterators = riters)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (riters, arg) = ListUtil.map2Fold(riters, traverseReductionIteratorBidir, inEnterFunc, inExitFunc, arg)
                    (DAE.REDUCTION(reductionInfo, e1, riters), arg)
                  end
                  
                  DAE.LIST(valList = expl)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.LIST(expl), arg)
                  end
                  
                  DAE.CONS(car = e1, cdr = e2)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                      (e2, arg) = traverseExpBidir(e2, inEnterFunc, inExitFunc, arg)
                    (DAE.CONS(e1, e2), arg)
                  end
                  
                  DAE.META_TUPLE(listExp = expl)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.TUPLE(expl), arg)
                  end
                  
                  DAE.META_OPTION(exp = oe1)  => begin
                      (oe1, arg) = traverseExpOptBidir(oe1, inEnterFunc, inExitFunc, inArg)
                    (DAE.META_OPTION(oe1), arg)
                  end
                  
                  DAE.METARECORDCALL(path = path, args = expl, fieldNames = strl, index = index, typeVars = typeVars)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                    (DAE.METARECORDCALL(path, expl, strl, index, typeVars), arg)
                  end
                  
                  DAE.MATCHEXPRESSION(matchType = match_ty, inputs = expl, aliases = aliases, localDecls = match_decls, cases = match_cases, et = ty)  => begin
                      (expl, arg) = traverseExpListBidir(expl, inEnterFunc, inExitFunc, inArg)
                      Error.addSourceMessage(Error.COMPILER_NOTIFICATION, list(getInstanceName() + " not yet implemented for match expressions. Called using: " + System.dladdr(inEnterFunc) + " " + System.dladdr(inExitFunc)), sourceInfo())
                    (DAE.MATCHEXPRESSION(match_ty, expl, aliases, match_decls, match_cases, ty), arg)
                  end
                  
                  DAE.BOX(exp = e1)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.BOX(e1), arg)
                  end
                  
                  DAE.UNBOX(exp = e1, ty = ty)  => begin
                      (e1, arg) = traverseExpBidir(e1, inEnterFunc, inExitFunc, inArg)
                    (DAE.UNBOX(e1, ty), arg)
                  end
                  
                  DAE.SHARED_LITERAL(__)  => begin
                    (inExp, inArg)
                  end
                  
                  DAE.PATTERN(__)  => begin
                    (inExp, inArg)
                  end
                  
                  _  => begin
                        Error.addInternalError(getInstanceName() + " - Unknown expression " + ExpressionDump.printExpStr(inExp) + ". Called using: " + System.dladdr(inEnterFunc) + " " + System.dladdr(inExitFunc), sourceInfo())
                      fail()
                  end
                end
              end
               #= (cases, tup) = List.mapFold(cases, traverseMatchCase, tup);
               =#
          (outExp, outArg)
        end

         #= Helper function to traverseExpBidirSubExps. Traverses any expressions in a
          component reference (i.e. in it's subscripts). =#
        function traverseExpBidirCref(inCref::DAE.ComponentRef, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outCref::DAE.ComponentRef

              (outCref, outArg) = begin
                  local name::String
                  local cr::ComponentRef
                  local ty::Type
                  local subs::List{DAE.Subscript}
                  local arg::ArgT
                @match inCref begin
                  DAE.CREF_QUAL(name, ty, subs, cr)  => begin
                      (subs, arg) = ListUtil.map2Fold(subs, traverseExpBidirSubs, inEnterFunc, inExitFunc, inArg)
                      (cr, arg) = traverseExpBidirCref(cr, inEnterFunc, inExitFunc, arg)
                    (DAE.CREF_QUAL(name, ty, subs, cr), arg)
                  end
                  
                  DAE.CREF_IDENT(ident = name, identType = ty, subscriptLst = subs)  => begin
                      (subs, arg) = ListUtil.map2Fold(subs, traverseExpBidirSubs, inEnterFunc, inExitFunc, inArg)
                    (DAE.CREF_IDENT(name, ty, subs), arg)
                  end
                  
                  _  => begin
                      (inCref, inArg)
                  end
                end
              end
          (outCref, outArg)
        end

         #= Helper function to traverseExpBottomUp. Traverses any expressions in a
          component reference (i.e. in it's subscripts). =#
        function traverseExpCref(inCref::DAE.ComponentRef, rel::FuncType, iarg::Type_a) ::Tuple{DAE.ComponentRef, Type_a} 
              local outArg::Type_a
              local outCref::DAE.ComponentRef

              (outCref, outArg) = begin
                  local name::String
                  local cr::ComponentRef
                  local cr_1::ComponentRef
                  local ty::Type
                  local subs::List{DAE.Subscript}
                  local subs_1::List{DAE.Subscript}
                  local arg::Type_a
                  local ix::ModelicaInteger
                  local instant::String
                @match (inCref, rel, iarg) begin
                  (DAE.CREF_QUAL(ident = name, identType = ty, subscriptLst = subs, componentRef = cr), _, arg)  => begin
                      (subs_1, arg) = traverseExpSubs(subs, rel, arg)
                      (cr_1, arg) = traverseExpCref(cr, rel, arg)
                      cr = if referenceEq(cr, cr_1) && referenceEq(subs, subs_1)
                            inCref
                          else
                            DAE.CREF_QUAL(name, ty, subs_1, cr_1)
                          end
                    (cr, arg)
                  end
                  
                  (DAE.CREF_IDENT(ident = name, identType = ty, subscriptLst = subs), _, arg)  => begin
                      (subs_1, arg) = traverseExpSubs(subs, rel, arg)
                      cr = if referenceEq(subs, subs_1)
                            inCref
                          else
                            DAE.CREF_IDENT(name, ty, subs_1)
                          end
                    (cr, arg)
                  end
                  
                  (DAE.CREF_ITER(ident = name, index = ix, identType = ty, subscriptLst = subs), _, arg)  => begin
                      (subs_1, arg) = traverseExpSubs(subs, rel, arg)
                      cr = if referenceEq(subs, subs_1)
                            inCref
                          else
                            DAE.CREF_ITER(name, ix, ty, subs_1)
                          end
                    (cr, arg)
                  end
                  
                  (DAE.OPTIMICA_ATTR_INST_CREF(componentRef = cr, instant = instant), _, arg)  => begin
                      (cr_1, arg) = traverseExpCref(cr, rel, arg)
                      cr = if referenceEq(cr, cr_1)
                            inCref
                          else
                            DAE.OPTIMICA_ATTR_INST_CREF(cr_1, instant)
                          end
                    (cr, arg)
                  end
                  
                  (DAE.WILD(__), _, arg)  => begin
                    (inCref, arg)
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Expression.traverseExpCref: Unknown cref"))
                      fail()
                  end
                end
              end
          (outCref, outArg)
        end

        function traverseExpSubs(inSubscript::List{<:DAE.Subscript}, rel::FuncType, iarg::Type_a) ::Tuple{List{DAE.Subscript}, Type_a} 
              local outArg::Type_a
              local outSubscript::List{DAE.Subscript}

              (outSubscript, outArg) = begin
                  local sub_exp::DAE.Exp
                  local sub_exp_1::DAE.Exp
                  local rest::List{DAE.Subscript}
                  local res::List{DAE.Subscript}
                  local arg::Type_a
                @match (inSubscript, rel, iarg) begin
                  ( nil(), _, arg)  => begin
                    (inSubscript, arg)
                  end
                  
                  (DAE.WHOLEDIM(__) <| rest, _, arg)  => begin
                      (res, arg) = traverseExpSubs(rest, rel, arg)
                      res = if referenceEq(rest, res)
                            inSubscript
                          else
                            _cons(DAE.WHOLEDIM(), res)
                          end
                    (res, arg)
                  end
                  
                  (DAE.SLICE(exp = sub_exp) <| rest, _, arg)  => begin
                      (sub_exp_1, arg) = traverseExpBottomUp(sub_exp, rel, arg)
                      (res, arg) = traverseExpSubs(rest, rel, arg)
                      res = if referenceEq(sub_exp, sub_exp_1) && referenceEq(rest, res)
                            inSubscript
                          else
                            _cons(DAE.SLICE(sub_exp_1), res)
                          end
                    (res, arg)
                  end
                  
                  (DAE.INDEX(exp = sub_exp) <| rest, _, arg)  => begin
                      (sub_exp_1, arg) = traverseExpBottomUp(sub_exp, rel, arg)
                      (res, arg) = traverseExpSubs(rest, rel, arg)
                      res = if referenceEq(sub_exp, sub_exp_1) && referenceEq(rest, res)
                            inSubscript
                          else
                            _cons(DAE.INDEX(sub_exp_1), res)
                          end
                    (res, arg)
                  end
                  
                  (DAE.WHOLE_NONEXP(exp = sub_exp) <| rest, _, arg)  => begin
                      (sub_exp_1, arg) = traverseExpBottomUp(sub_exp, rel, arg)
                      (res, arg) = traverseExpSubs(rest, rel, arg)
                      res = if referenceEq(sub_exp, sub_exp_1) && referenceEq(rest, res)
                            inSubscript
                          else
                            _cons(DAE.WHOLE_NONEXP(sub_exp_1), res)
                          end
                    (res, arg)
                  end
                end
              end
          (outSubscript, outArg)
        end

        function traverseExpTopDownCrefHelper(inCref::DAE.ComponentRef, rel::FuncType, iarg::Argument) ::Tuple{DAE.ComponentRef, Argument} 
              local outArg::Argument
              local outCref::DAE.ComponentRef

              (outCref, outArg) = begin
                  local name::String
                  local cr::ComponentRef
                  local cr_1::ComponentRef
                  local ty::Type
                  local subs::List{DAE.Subscript}
                  local subs_1::List{DAE.Subscript}
                  local arg::Argument
                @match (inCref, rel, iarg) begin
                  (DAE.CREF_QUAL(ident = name, identType = ty, subscriptLst = subs, componentRef = cr), _, arg)  => begin
                      (subs_1, arg) = traverseExpTopDownSubs(subs, rel, arg)
                      (cr_1, arg) = traverseExpTopDownCrefHelper(cr, rel, arg)
                    (if referenceEq(subs, subs_1) && referenceEq(cr, cr_1)
                          inCref
                        else
                          DAE.CREF_QUAL(name, ty, subs_1, cr_1)
                        end, arg)
                  end
                  
                  (DAE.CREF_IDENT(ident = name, identType = ty, subscriptLst = subs), _, arg)  => begin
                      (subs_1, arg) = traverseExpTopDownSubs(subs, rel, arg)
                    (if referenceEq(subs, subs_1)
                          inCref
                        else
                          DAE.CREF_IDENT(name, ty, subs_1)
                        end, arg)
                  end
                  
                  (DAE.WILD(__), _, arg)  => begin
                    (inCref, arg)
                  end
                end
              end
          (outCref, outArg)
        end

         #= Helper function to traverseExpBidirCref. Traverses expressions in a
          subscript. =#
        function traverseExpBidirSubs(inSubscript::DAE.Subscript, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outSubscript::DAE.Subscript

              (outSubscript, outArg) = begin
                  local sub_exp::DAE.Exp
                  local arg::ArgT
                @match inSubscript begin
                  DAE.WHOLEDIM(__)  => begin
                    (inSubscript, inArg)
                  end
                  
                  DAE.SLICE(exp = sub_exp)  => begin
                      (sub_exp, arg) = traverseExpBidir(sub_exp, inEnterFunc, inExitFunc, inArg)
                    (DAE.SLICE(sub_exp), arg)
                  end
                  
                  DAE.INDEX(exp = sub_exp)  => begin
                      (sub_exp, arg) = traverseExpBidir(sub_exp, inEnterFunc, inExitFunc, inArg)
                    (DAE.INDEX(sub_exp), arg)
                  end
                  
                  DAE.WHOLE_NONEXP(exp = sub_exp)  => begin
                      (sub_exp, arg) = traverseExpBidir(sub_exp, inEnterFunc, inExitFunc, inArg)
                    (DAE.WHOLE_NONEXP(sub_exp), arg)
                  end
                end
              end
          (outSubscript, outArg)
        end

        function traverseExpTopDownSubs(inSubscript::List{<:DAE.Subscript}, rel::FuncType, iarg::Argument) ::Tuple{List{DAE.Subscript}, Argument} 
              local arg::Argument = iarg
              local outSubscript::List{DAE.Subscript}

              local exp::DAE.Exp
              local nsub::DAE.Subscript
              local allEq::Bool = true
              local delst::DoubleEnded.MutableList{DAE.Subscript}
              local nEq::ModelicaInteger = 0

              for sub in inSubscript
                nsub = begin
                  @match sub begin
                    DAE.WHOLEDIM(__)  => begin
                      sub
                    end
                    
                    DAE.SLICE(__)  => begin
                        (exp, arg) = traverseExpTopDown(sub.exp, rel, arg)
                      if referenceEq(sub.exp, exp)
                            sub
                          else
                            DAE.SLICE(exp)
                          end
                    end
                    
                    DAE.INDEX(__)  => begin
                        (exp, arg) = traverseExpTopDown(sub.exp, rel, arg)
                      if referenceEq(sub.exp, exp)
                            sub
                          else
                            DAE.INDEX(exp)
                          end
                    end
                    
                    DAE.WHOLE_NONEXP(__)  => begin
                        (exp, arg) = traverseExpTopDown(sub.exp, rel, arg)
                      if referenceEq(sub.exp, exp)
                            sub
                          else
                            DAE.WHOLE_NONEXP(exp)
                          end
                    end
                  end
                end
                if if allEq
                      ! referenceEq(nsub, sub)
                    else
                      false
                    end
                  allEq = false
                  delst = DoubleEnded.empty(nsub)
                  for elt in inSubscript
                    if nEq < 1
                      break
                    end
                    DoubleEnded.push_back(delst, elt)
                    nEq = nEq - 1
                  end
                end
                if allEq
                  nEq = nEq + 1
                else
                  DoubleEnded.push_back(delst, nsub)
                end
              end
               #=  Preserve reference equality without any allocation if nothing changed
               =#
              outSubscript = if allEq
                    inSubscript
                  else
                    DoubleEnded.toListAndClear(delst)
                  end
          (outSubscript, arg)
        end

         #= /***************************************************/ =#
         #= /* Compare and Check DAE.Exp */ =#
         #= /***************************************************/ =#

         #= returns true if operator is division or multiplication =#
        function operatorDivOrMul(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.MUL(_)  => begin
                    true
                  end
                  
                  DAE.DIV(_)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns true if expression is a range expression. =#
        function isRange(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.RANGE(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

        function isReduction(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.REDUCTION(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is constant
          and has the value one, otherwise false =#
        function isOne(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local ival::ModelicaInteger
                  local rval::ModelicaReal
                  local res::Bool
                  local t::Type
                  local e::DAE.Exp
                @match inExp begin
                  DAE.ICONST(integer = ival)  => begin
                    intEq(ival, 1)
                  end
                  
                  DAE.RCONST(real = rval)  => begin
                    realEq(rval, 1.0)
                  end
                  
                  DAE.CAST(exp = e)  => begin
                      res = isOne(e) #= Casting to one is still one =#
                    res
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is constant
          and has the value zero, otherwise false =#
        function isZero(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local ival::ModelicaInteger
                  local rval::ModelicaReal
                  local t::Type
                  local e::DAE.Exp
                  local ae::List{DAE.Exp}
                  local matrix::List{List{DAE.Exp}}
                @match inExp begin
                  DAE.ICONST(integer = ival)  => begin
                    intEq(ival, 0)
                  end
                  
                  DAE.RCONST(real = rval)  => begin
                    realEq(rval, 0.0)
                  end
                  
                  DAE.CAST(exp = e)  => begin
                    isZero(e)
                  end
                  
                  DAE.UNARY(DAE.UMINUS(_), e)  => begin
                    isZero(e)
                  end
                  
                  DAE.ARRAY(array = ae)  => begin
                    ListUtil.mapAllValueBool(ae, isZero, true)
                  end
                  
                  DAE.MATRIX(matrix = matrix)  => begin
                    ListUtil.mapListAllValueBool(matrix, isZero, true)
                  end
                  
                  DAE.UNARY(DAE.UMINUS_ARR(_), e)  => begin
                    isZero(e)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is constant
          and zero or near to zero, otherwise false =#
        function isZeroOrAlmostZero(inExp::DAE.Exp, nominal::DAE.Exp = DAE.RCONST(1.0)) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local ival::ModelicaInteger
                  local rval::ModelicaReal
                  local t::Type
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local ae::List{DAE.Exp}
                  local matrix::List{List{DAE.Exp}}
                  local rNom::ModelicaReal
                @match (inExp, nominal) begin
                  (DAE.ICONST(integer = ival), _)  => begin
                    intEq(ival, 0)
                  end
                  
                  (DAE.RCONST(real = rval), DAE.RCONST(real = rNom))  => begin
                    realLt(abs(rval), 1e-6 * abs(rNom))
                  end
                  
                  (DAE.RCONST(real = rval), _)  => begin
                    realLt(abs(rval), 1e-6)
                  end
                  
                  (DAE.CAST(exp = e), _)  => begin
                    isZeroOrAlmostZero(e, nominal)
                  end
                  
                  (DAE.UNARY(DAE.UMINUS(_), e), _)  => begin
                    isZeroOrAlmostZero(e, nominal)
                  end
                  
                  (DAE.ARRAY(array = ae), _)  => begin
                    ListUtil.map1AllValueBool(ae, isZeroOrAlmostZero, true, nominal)
                  end
                  
                  (DAE.MATRIX(matrix = matrix), _)  => begin
                    ListUtil.map1ListAllValueBool(matrix, isZeroOrAlmostZero, true, nominal)
                  end
                  
                  (DAE.UNARY(DAE.UMINUS_ARR(_), e), _)  => begin
                    isZeroOrAlmostZero(e, nominal)
                  end
                  
                  (DAE.IFEXP(_, e, e1), _)  => begin
                    isZeroOrAlmostZero(e, nominal) || isZeroOrAlmostZero(e1, nominal)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is known to be >= 0 =#
        function isPositiveOrZero(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local i::ModelicaInteger
                  local r::ModelicaReal
                   #= /* abs(e) */ =#
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT("abs"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("exp"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("cosh"))  => begin
                    true
                  end
                  
                  DAE.ICONST(i)  => begin
                    i >= 0
                  end
                  
                  DAE.RCONST(r)  => begin
                    realGe(r, 0.0)
                  end
                  
                  DAE.BINARY(e1, DAE.ADD(__), e2)  => begin
                    isPositiveOrZero(e1) && isPositiveOrZero(e2)
                  end
                  
                  DAE.BINARY(e1, DAE.SUB(__), e2)  => begin
                    isPositiveOrZero(e1) && isNegativeOrZero(e2)
                  end
                  
                  DAE.BINARY(e1, DAE.MUL(__), e2)  => begin
                      b1 = isPositiveOrZero(e1) && isPositiveOrZero(e2)
                      b2 = isNegativeOrZero(e1) && isNegativeOrZero(e2)
                      b3 = expEqual(e1, e2)
                    b1 || b2 || b3
                  end
                  
                  DAE.BINARY(e1, DAE.DIV(__), e2)  => begin
                      b1 = isPositiveOrZero(e1) && isPositiveOrZero(e2)
                      b2 = isNegativeOrZero(e1) && isNegativeOrZero(e2)
                    b1 || b2
                  end
                  
                  DAE.BINARY(e1, DAE.POW(__), DAE.RCONST(r))  => begin
                      i = realInt(r)
                      b1 = realEq(r, intReal(i))
                      b2 = 0 == intMod(i, 2)
                      b3 = isPositiveOrZero(e1)
                      b = b2 || b3
                    b1 && b
                  end
                  
                  DAE.BINARY(_, DAE.POW(__), e2)  => begin
                    isEven(e2)
                  end
                  
                  DAE.UNARY(DAE.UMINUS(__), e1)  => begin
                    isNegativeOrZero(e1)
                  end
                  
                  _  => begin
                      isZero(inExp)
                  end
                end
              end
               #=  exp(x)
               =#
               #=  cosh(x)
               =#
               #= /* literals */ =#
               #= /* e1 + e2 */ =#
               #= /* e1 - e2 */ =#
               #= /* e1 * e2 , -e1 * -e2, e ^ 2.0 */ =#
               #= /* e1 / e2, -e1 / -e2 */ =#
               #= /* Integer power we can say something good about */ =#
               #=  -(x)
               =#
          outBoolean
        end

         #= Returns true if an expression is known to be <= 0 =#
        function isNegativeOrZero(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                   #= /* literals */ =#
                @match inExp begin
                  DAE.ICONST(i)  => begin
                    i <= 0
                  end
                  
                  DAE.RCONST(r)  => begin
                    r <= 0.0
                  end
                  
                  DAE.UNARY(DAE.UMINUS(__), e1)  => begin
                    isPositiveOrZero(e1)
                  end
                  
                  DAE.BINARY(_, DAE.POW(__), e2) where (isOdd(e2))  => begin
                    isNegativeOrZero(e2)
                  end
                  
                  _  => begin
                      isZero(inExp)
                  end
                end
              end
               #=  -(x)
               =#
               #= /* Integer power we can say something good about */ =#
          outBoolean
        end

         #= Returns true if an expression is 0.5 =#
        function isHalf(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local rval::ModelicaReal
                @match inExp begin
                  DAE.RCONST(real = rval)  => begin
                    realEq(rval, 0.5)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

        function isAtomic(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.CREF(__)  => begin
                    true
                  end
                  
                  DAE.CALL(__)  => begin
                    true
                  end
                  
                  DAE.ICONST(__)  => begin
                    inExp.integer >= 0
                  end
                  
                  DAE.RCONST(__)  => begin
                    inExp.real > 0.0
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= author: lochel
          Returns true if an expression contains an impure function call. =#
        function isImpure(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = isConstWork(inExp)
              (_, outBoolean) = traverseExpTopDown(inExp, isImpureWork, false)
          outBoolean
        end

         #= author: lochel =#
        function isImpureWork(inExp::DAE.Exp, isImpure::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outImpure::Bool
              local cont::Bool
              local outExp::DAE.Exp

              (outExp, cont, outImpure) = begin
                @match (inExp, isImpure) begin
                  (_, true)  => begin
                    (inExp, true, true)
                  end
                  
                  (DAE.CALL(attr = DAE.CALL_ATTR(isImpure = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "alarm"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "compareFilesAndMove"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "delay"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "initial"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "print"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "readFile"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "sample"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "system"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "system_parallel"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "terminal"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "writeFile"), attr = DAE.CALL_ATTR(builtin = true)), _)  => begin
                    (inExp, false, true)
                  end
                  
                  _  => begin
                      (inExp, true, false)
                  end
                end
              end
               #=  workaround for builtin functions that are impure, but not marked as impure
               =#
          (outExp, cont, outImpure)
        end

         #=  Returns true if an expression contains a record type. =#
        function containsRecordType(inExp::DAE.Exp) ::Bool 
              local isRec::Bool

              (_, isRec) = traverseExpTopDown(inExp, containsRecordTypeWork, false)
          isRec
        end

        function containsRecordTypeWork(inExp::DAE.Exp, inRec::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outRec::Bool = inRec
              local cont::Bool = false
              local outExp::DAE.Exp = inExp

              if ! inRec
                (outExp, cont, outRec) = begin
                    local ty::DAE.Type
                    local expLst::List{DAE.Exp}
                    local subRec::Bool
                    local cr::DAE.ComponentRef
                  @matchcontinue inExp begin
                    DAE.RECORD(__)  => begin
                      (inExp, false, true)
                    end
                    
                    DAE.CALL(expLst = expLst, attr = DAE.CALL_ATTR(ty = ty))  => begin
                        subRec = isRecordType(ty)
                        if ! subRec
                          for exp in expLst
                            subRec = containsRecordType(exp)
                            if subRec
                              break
                            end
                          end
                        end
                      (inExp, ! subRec, subRec)
                    end
                    
                    _  => begin
                        (inExp, true, false)
                    end
                  end
                end
              end
          (outExp, cont, outRec)
        end

         #= Returns true if an expression is constant =#
        function isConst(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = isConstWork(inExp)
          outBoolean
        end

         #= Returns true if an expression is really a constant scalar value. no calls, casts, or something =#
        function isEvaluatedConst(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = isEvaluatedConstWork(inExp, true)
          outBoolean
        end

         #= Returns true if an expression is really constant =#
        function isEvaluatedConstWork(inExp::DAE.Exp, inRes::Bool) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local e::DAE.Exp
                @match (inExp, inRes) begin
                  (_, false)  => begin
                    false
                  end
                  
                  (DAE.ICONST(__), _)  => begin
                    true
                  end
                  
                  (DAE.RCONST(__), _)  => begin
                    true
                  end
                  
                  (DAE.BCONST(__), _)  => begin
                    true
                  end
                  
                  (DAE.SCONST(__), _)  => begin
                    true
                  end
                  
                  (DAE.ENUM_LITERAL(__), _)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is constant =#
        function isConstWork(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local res::Bool
                  local op::Operator
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local t::Type
                  local ae::List{DAE.Exp}
                  local matrix::List{List{DAE.Exp}}
                  local path::Absyn.Path
                @match inExp begin
                  DAE.ICONST(__)  => begin
                    true
                  end
                  
                  DAE.RCONST(__)  => begin
                    true
                  end
                  
                  DAE.BCONST(__)  => begin
                    true
                  end
                  
                  DAE.SCONST(__)  => begin
                    true
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                    isConstWork(e)
                  end
                  
                  DAE.CAST(exp = e)  => begin
                    isConstWork(e)
                  end
                  
                  DAE.BINARY(e1, _, e2)  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.IFEXP(e, e1, e2)  => begin
                      res = isConstWork(e2)
                      if res
                        res = isConstWork(e1)
                      end
                    if res
                          isConstWork(e)
                        else
                          false
                        end
                  end
                  
                  DAE.LBINARY(exp1 = e1, exp2 = e2)  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.LUNARY(exp = e)  => begin
                    isConstWork(e)
                  end
                  
                  DAE.RELATION(exp1 = e1, exp2 = e2)  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.ARRAY(array = ae)  => begin
                    isConstWorkList(ae)
                  end
                  
                  DAE.MATRIX(matrix = matrix)  => begin
                    isConstWorkListList(matrix)
                  end
                  
                  DAE.RANGE(start = e1, step = NONE(), stop = e2)  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.RANGE(start = e, step = SOME(e1), stop = e2)  => begin
                      res = isConstWork(e2)
                      if res
                        res = isConstWork(e1)
                      end
                    if res
                          isConstWork(e)
                        else
                          false
                        end
                  end
                  
                  DAE.PARTEVALFUNCTION(expList = ae)  => begin
                    isConstWorkList(ae)
                  end
                  
                  DAE.TUPLE(PR = ae)  => begin
                    isConstWorkList(ae)
                  end
                  
                  DAE.ASUB(exp = e, sub = ae)  => begin
                      res = isConstWork(e)
                    if res
                          isConstWorkList(ae)
                        else
                          false
                        end
                  end
                  
                  DAE.TSUB(exp = e)  => begin
                    isConstWork(e)
                  end
                  
                  DAE.SIZE(exp = e, sz = NONE())  => begin
                    isConstWork(e)
                  end
                  
                  DAE.SIZE(exp = e1, sz = SOME(e2))  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.CALL(expLst = ae, attr = DAE.CALL_ATTR(builtin = false, isImpure = false))  => begin
                    isConstWorkList(ae)
                  end
                  
                  DAE.CALL(path = path, expLst = ae, attr = DAE.CALL_ATTR(builtin = true))  => begin
                    if listMember(AbsynUtil.pathFirstIdent(path), list("initial", "terminal", "sample"))
                          false
                        else
                          isConstWorkList(ae)
                        end
                  end
                  
                  DAE.RECORD(exps = ae)  => begin
                    isConstWorkList(ae)
                  end
                  
                  DAE.REDUCTION(expr = e1, iterators = DAE.REDUCTIONITER(exp = e2) <|  nil())  => begin
                      res = isConstWork(e2)
                    if res
                          isConstWork(e1)
                        else
                          false
                        end
                  end
                  
                  DAE.BOX(exp = e)  => begin
                    isConstWork(e)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #= /* der/edge/change/pre belongs to this list usually, but if we optimize the expression, we might end up with pre of a constant expression... */ =#
               #= /*TODO:Make this work for multiple iters, guard exps*/ =#
          outBoolean
        end

         #= Returns true if an expression is a constant value =#
        function isConstValueWork(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local res::Bool
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local ae::List{DAE.Exp}
                  local matrix::List{List{DAE.Exp}}
                @match inExp begin
                  DAE.ICONST(__)  => begin
                    true
                  end
                  
                  DAE.RCONST(__)  => begin
                    true
                  end
                  
                  DAE.BCONST(__)  => begin
                    true
                  end
                  
                  DAE.SCONST(__)  => begin
                    true
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  DAE.ARRAY(array = ae)  => begin
                    isConstValueWorkList(ae)
                  end
                  
                  DAE.MATRIX(matrix = matrix)  => begin
                    isConstValueWorkListList(matrix)
                  end
                  
                  DAE.RECORD(__)  => begin
                    true
                  end
                  
                  DAE.METARECORDCALL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if an expression is a constant value (not a composite operation) =#
        function isConstValue(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = isConstValueWork(inExp)
          outBoolean
        end

         #= Returns true if a list of expressions is constant =#
        function isConstWorkList(inExps::List{<:DAE.Exp}) ::Bool 
              local outBoolean::Bool

              local e::DAE.Exp
              local exps::List{DAE.Exp}
              local b::Bool = true

              exps = inExps
              while b && ! listEmpty(exps)
                @match _cons(e, exps) = exps
                b = isConstWork(e)
              end
              outBoolean = b
          outBoolean
        end

        function isConstWorkListList(inExps::List{<:List{<:DAE.Exp}}) ::Bool 
              local outIsConst::Bool

              local e::List{DAE.Exp}
              local exps::List{List{DAE.Exp}}
              local b::Bool = true

              exps = inExps
              while b && ! listEmpty(exps)
                @match _cons(e, exps) = exps
                b = isConstWorkList(e)
              end
              outIsConst = b
          outIsConst
        end

         #= Returns true if a list of expressions is a constant value =#
        function isConstValueWorkList(inExps::List{<:DAE.Exp}) ::Bool 
              local outBoolean::Bool

              local e::DAE.Exp
              local exps::List{DAE.Exp}
              local b::Bool = true

              exps = inExps
              while b && ! listEmpty(exps)
                @match _cons(e, exps) = exps
                b = isConstValueWork(e)
              end
              outBoolean = b
          outBoolean
        end

        function isConstValueWorkListList(inExps::List{<:List{<:DAE.Exp}}) ::Bool 
              local outIsConst::Bool

              local e::List{DAE.Exp}
              local exps::List{List{DAE.Exp}}
              local b::Bool = true

              exps = inExps
              while b && ! listEmpty(exps)
                @match _cons(e, exps) = exps
                b = isConstValueWorkList(e)
              end
              outIsConst = b
          outIsConst
        end

         #= author: PA
          Check if expression is not constant. =#
        function isNotConst(e::DAE.Exp) ::Bool 
              local nb::Bool

              local b::Bool

              b = isConst(e)
              nb = boolNot(b)
          nb
        end

         #= Returns true if expression is a relation =#
        function isRelation(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.RELATION(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

        function isEventTriggeringFunctionExp(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT("div"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("mod"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("rem"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("ceil"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("floor"))  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.IDENT("integer"))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= returns true if operator is ADD or SUB =#
        function isAddOrSub(op::DAE.Operator) ::Bool 
              local res::Bool

              res = isAdd(op) || isSub(op)
          res
        end

         #= returns true if operator is ADD =#
        function isAdd(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.ADD(__)  => begin
                    true
                  end
                  
                  DAE.ADD_ARR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if operator is SUB =#
        function isSub(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.SUB(__)  => begin
                    true
                  end
                  
                  DAE.SUB_ARR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if BINARY is a+b or a-b =#
        function isAddOrSubBinary(iExp::DAE.Exp) ::Bool 
              local res::Bool

              local op::DAE.Operator

              res = begin
                @match iExp begin
                  DAE.BINARY(_, op, _)  => begin
                    isAddOrSub(op)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if operator is MUL or DIV =#
        function isMulOrDiv(op::DAE.Operator) ::Bool 
              local res::Bool = isMul(op) || isDiv(op)
          res
        end

         #= returns true if operator is MUL =#
        function isMul(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.MUL(__)  => begin
                    true
                  end
                  
                  DAE.MUL_ARR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if operator is DIV =#
        function isDiv(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.DIV(__)  => begin
                    true
                  end
                  
                  DAE.DIV_ARR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if BINARY is a/b =#
        function isDivBinary(iExp::DAE.Exp) ::Bool 
              local res::Bool

              local op::DAE.Operator

              res = begin
                @match iExp begin
                  DAE.BINARY(_, op, _)  => begin
                    isDiv(op)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if BINARY is a/b or a*b =#
        function isMulorDivBinary(iExp::DAE.Exp) ::Bool 
              local res::Bool

              local op::DAE.Operator

              res = begin
                @match iExp begin
                  DAE.BINARY(_, op, _)  => begin
                    isMulOrDiv(op)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if operator is POW =#
        function isPow(op::DAE.Operator) ::Bool 
              local res::Bool

              res = begin
                @match op begin
                  DAE.POW(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= return true if expression is DAE.CALL(path=Absyn.IDENT(name)) =#
        function isFunCall(iExp::DAE.Exp, name::String) ::Bool 
              local res::Bool

              res = begin
                  local name_::String
                @match (iExp, name) begin
                  (DAE.CALL(path = Absyn.IDENT(name_)), _)  => begin
                    name_ == name
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #=  =#
        function equalTypes(t1::DAE.Type, t2::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                  local vars1::List{DAE.Var}
                  local vars2::List{DAE.Var}
                  local ty1::Type
                  local ty2::Type
                  local ad1::DAE.Dimensions
                  local ad2::DAE.Dimensions
                  local li1::List{ModelicaInteger}
                  local li2::List{ModelicaInteger}
                @matchcontinue (t1, t2) begin
                  (DAE.T_INTEGER(__), DAE.T_INTEGER(__))  => begin
                    true
                  end
                  
                  (DAE.T_REAL(__), DAE.T_REAL(__))  => begin
                    true
                  end
                  
                  (DAE.T_STRING(__), DAE.T_STRING(__))  => begin
                    true
                  end
                  
                  (DAE.T_BOOL(__), DAE.T_BOOL(__))  => begin
                    true
                  end
                  
                  (DAE.T_CLOCK(__), DAE.T_CLOCK(__))  => begin
                    true
                  end
                  
                  (DAE.T_COMPLEX(varLst = vars1), DAE.T_COMPLEX(varLst = vars2))  => begin
                    equalTypesComplexVars(vars1, vars2)
                  end
                  
                  (DAE.T_ARRAY(ty1, ad1), DAE.T_ARRAY(ty2, ad2))  => begin
                      li1 = ListUtil.map(ad1, dimensionSize)
                      li2 = ListUtil.map(ad2, dimensionSize)
                      @match true = ListUtil.isEqualOnTrue(li1, li2, intEq)
                      @match true = equalTypes(ty1, ty2)
                    true
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

         #=  =#
        function equalTypesComplexVars(inVars1::List{<:DAE.Var}, inVars2::List{<:DAE.Var}) ::Bool 
              local b::Bool

              b = begin
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local s1::String
                  local s2::String
                  local vars1::List{DAE.Var}
                  local vars2::List{DAE.Var}
                @matchcontinue (inVars1, inVars2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (DAE.TYPES_VAR(name = s1, ty = t1) <| vars1, DAE.TYPES_VAR(name = s2, ty = t2) <| vars2)  => begin
                      @match true = stringEq(s1, s2)
                      @match true = equalTypes(t1, t2)
                    equalTypesComplexVars(vars1, vars2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #= print(\" verify subvars: \" + s1 + \" and \" + s2 + \" to go: \" + intString(listLength(vars1)) + \" , \" + intString(listLength(vars2))  + \"\\n\");
               =#
               #= print(\" types: \" + Types.unparseType(t1) + \" and \" + Types.unparseType(t2) + \"\\n\");
               =#
               #= print(s1 + \" and \" + s2 + \" EQUAL \\n\\n\");
               =#
          b
        end

         #= Returns true if type is one of the builtin types. =#
        function typeBuiltin(inType::DAE.Type) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
                    true
                  end
                  
                  DAE.T_REAL(__)  => begin
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
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
          outBoolean
        end

         #=  =#
        function isWholeDim(s::DAE.Subscript) ::Bool 
              local b::Bool

              b = begin
                @match s begin
                  DAE.WHOLEDIM(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=  =#
        function isInt(it::DAE.Type) ::Bool 
              local re::Bool

              re = begin
                  local t1::Type
                @match it begin
                  DAE.T_INTEGER(__)  => begin
                    true
                  end
                  
                  DAE.T_ARRAY(ty = t1)  => begin
                    isInt(t1)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          re
        end

         #=  =#
        function isReal(it::DAE.Type) ::Bool 
              local re::Bool

              re = begin
                  local t1::Type
                @match it begin
                  DAE.T_REAL(__)  => begin
                    true
                  end
                  
                  DAE.T_ARRAY(ty = t1)  => begin
                    isReal(t1)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          re
        end

         #=  =#
        function isExpReal(e::DAE.Exp) ::Bool 
              local re::Bool

              re = isReal(typeof(e))
          re
        end

         #= Return true if expression has zero-dimension =#
        function isConstZeroLength(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.ARRAY(array =  nil())  => begin
                    true
                  end
                  
                  DAE.MATRIX(matrix =  nil())  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if expression is false =#
        function isConstFalse(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.BCONST(false)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if expression is true =#
        function isConstTrue(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inExp begin
                  DAE.BCONST(true)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if expression is 1 =#
        function isConstOne(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local rval::ModelicaReal
                  local ival::ModelicaInteger
                   #=  constant real 1.0
                   =#
                @match inExp begin
                  DAE.RCONST(rval)  => begin
                    realEq(rval, 1.0)
                  end
                  
                  DAE.ICONST(ival)  => begin
                    intEq(ival, 1)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  constant integer 1
               =#
               #=  anything else
               =#
          outBoolean
        end

         #= Return true if expression is -1 =#
        function isConstMinusOne(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local rval::ModelicaReal
                  local ival::ModelicaInteger
                   #=  is real -1.0
                   =#
                @match inExp begin
                  DAE.RCONST(rval)  => begin
                    realEq(rval, -1.0)
                  end
                  
                  DAE.ICONST(ival)  => begin
                    intEq(ival, -1)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  is integer -1
               =#
               #=  anything else
               =#
          outBoolean
        end

        function isGreatereqOrLesseq(op::DAE.Operator) ::Bool 
              local b::Bool

              b = begin
                @match op begin
                  DAE.GREATEREQ(__)  => begin
                    true
                  end
                  
                  DAE.LESSEQ(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isLesseqOrLess(op::DAE.Operator) ::Bool 
              local b::Bool

              b = begin
                @match op begin
                  DAE.LESS(__)  => begin
                    true
                  end
                  
                  DAE.LESSEQ(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if expression or subexpression is a
         functioncall that returns an array, otherwise false.
          Note: the der operator is represented as a
                function call but still return false. =#
        function containVectorFunctioncall(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local e3::DAE.Exp
                  local res::Bool
                  local blst::List{Bool}
                  local elst::List{DAE.Exp}
                  local flatexplst::List{DAE.Exp}
                  local explst::List{List{DAE.Exp}}
                  local optexp::Option{DAE.Exp}
                   #=  der is not a vector function
                   =#
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT(name = "der"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "pre"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "previous"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "inStream"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "actualStream"))  => begin
                    false
                  end
                  
                  DAE.CALL(attr = DAE.CALL_ATTR(ty = DAE.T_ARRAY(__)))  => begin
                    true
                  end
                  
                  DAE.CALL(__)  => begin
                    false
                  end
                  
                  DAE.PARTEVALFUNCTION(expList = elst)  => begin
                    ListUtil.mapBoolOr(elst, containVectorFunctioncall)
                  end
                  
                  DAE.BINARY(exp1 = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.BINARY(exp2 = e2) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                    containVectorFunctioncall(e)
                  end
                  
                  DAE.LBINARY(exp1 = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.LBINARY(exp2 = e2) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.LUNARY(exp = e)  => begin
                    containVectorFunctioncall(e)
                  end
                  
                  DAE.RELATION(exp1 = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.RELATION(exp2 = e2) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expCond = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expThen = e2) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expElse = e3) where (containVectorFunctioncall(e3))  => begin
                    true
                  end
                  
                  DAE.ARRAY(array = elst)  => begin
                    ListUtil.mapBoolOr(elst, containVectorFunctioncall)
                  end
                  
                  DAE.MATRIX(matrix = explst)  => begin
                      flatexplst = ListUtil.flatten(explst)
                      res = ListUtil.mapBoolOr(flatexplst, containVectorFunctioncall)
                    res
                  end
                  
                  DAE.RANGE(start = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.RANGE(stop = e2) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.RANGE(step = SOME(e)) where (containVectorFunctioncall(e))  => begin
                    true
                  end
                  
                  DAE.TUPLE(PR = elst)  => begin
                    ListUtil.mapBoolOr(elst, containVectorFunctioncall)
                  end
                  
                  DAE.CAST(exp = e)  => begin
                    containVectorFunctioncall(e)
                  end
                  
                  DAE.SIZE(exp = e1) where (containVectorFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.SIZE(sz = SOME(e2)) where (containVectorFunctioncall(e2))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  pre is not a vector function, adrpo: 2009-03-03 -> pre is also needed here!
               =#
               #=  inStream and actualStream are not a vector function, adrpo: 2010-08-31 -> they are also needed here!
               =#
               #=  a call that has an return array type returns true
               =#
               #=  any other call returns false
               =#
               #=  partial evaluation
               =#
               #=  stefan
               =#
               #=  binary operators, e1 has a vector function call
               =#
               #=  binary operators, e2 has a vector function call
               =#
               #=  unary operators
               =#
               #=  logical binary operators, e1 is a vector call
               =#
               #=  logical binary operators, e2 is a vector call
               =#
               #=  logical unary operators, e is a vector call
               =#
               #=  relations e1 op e2, where e1 is a vector call
               =#
               #=  relations e1 op e2, where e2 is a vector call
               =#
               #=  if expression where the condition is a vector call
               =#
               #=  if expression where the then part is a vector call
               =#
               #=  if expression where the else part is a vector call
               =#
               #=  arrays
               =#
               #=  matrixes
               =#
               #=  ranges [e1:step:e2], where e1 is a vector call
               =#
               #=  ranges [e1:step:e2], where e2 is a vector call
               =#
               #=  ranges [e1:step:e2], where step is a vector call
               =#
               #=  tuples return true all the time???!! adrpo: FIXME! TODO! is this really true?
               =#
               #=  cast
               =#
               #=  size operator
               =#
               #=  size operator
               =#
               #=  any other expressions return false
               =#
          outBoolean
        end

         #= Returns true if expression or subexpression
          is a functioncall, otherwise false.
          Note: the der and pre operators are represented
                as function calls but still returns false. =#
        function containFunctioncall(inExp::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local e3::DAE.Exp
                  local res::Bool
                  local blst::List{Bool}
                  local elst::List{DAE.Exp}
                  local flatexplst::List{DAE.Exp}
                  local explst::List{List{DAE.Exp}}
                  local optexp::Option{DAE.Exp}
                   #=  der(x) is not a function call
                   =#
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT(name = "der"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "pre"))  => begin
                    false
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name = "previous"))  => begin
                    false
                  end
                  
                  DAE.CALL(__)  => begin
                    true
                  end
                  
                  DAE.PARTEVALFUNCTION(expList = elst)  => begin
                      res = ListUtil.mapBoolOr(elst, containFunctioncall)
                    res
                  end
                  
                  DAE.BINARY(exp1 = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.BINARY(exp2 = e2) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.UNARY(exp = e)  => begin
                    containFunctioncall(e)
                  end
                  
                  DAE.LBINARY(exp1 = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.LBINARY(exp2 = e2) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.LUNARY(exp = e)  => begin
                    containFunctioncall(e)
                  end
                  
                  DAE.RELATION(exp1 = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.RELATION(exp2 = e2) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expCond = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expThen = e2) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.IFEXP(expElse = e3) where (containFunctioncall(e3))  => begin
                    true
                  end
                  
                  DAE.ARRAY(array = elst)  => begin
                    ListUtil.mapBoolOr(elst, containFunctioncall)
                  end
                  
                  DAE.MATRIX(matrix = explst)  => begin
                      flatexplst = ListUtil.flatten(explst)
                      res = ListUtil.mapBoolOr(flatexplst, containFunctioncall)
                    res
                  end
                  
                  DAE.RANGE(start = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.RANGE(stop = e2) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  DAE.RANGE(step = SOME(e)) where (containFunctioncall(e))  => begin
                    true
                  end
                  
                  DAE.TUPLE(PR = elst)  => begin
                    ListUtil.mapBoolOr(elst, containVectorFunctioncall)
                  end
                  
                  DAE.CAST(exp = e)  => begin
                    containFunctioncall(e)
                  end
                  
                  DAE.ASUB(exp = e)  => begin
                    containFunctioncall(e)
                  end
                  
                  DAE.SIZE(exp = e1) where (containFunctioncall(e1))  => begin
                    true
                  end
                  
                  DAE.SIZE(sz = SOME(e2)) where (containFunctioncall(e2))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  pre(x) is not a function call
               =#
               #=  any other call is a function call
               =#
               #=  partial evaluation functions
               =#
               #=  stefan
               =#
               #=  binary
               =#
               #=  unary
               =#
               #=  logical binary
               =#
               #=  logical unary
               =#
               #=  relations
               =#
               #=  if expressions
               =#
               #=  arrays
               =#
               #=  matrix
               =#
               #=  ranges
               =#
               #=  tuples return true all the time???!! adrpo: FIXME! TODO! is this really true?
               =#
               #=  cast
               =#
               #=  asub
               =#
               #=  size
               =#
               #=  anything else
               =#
          outBoolean
        end

         #= Function: expIntOrder
        This function takes a list of Exp, assumes they are all ICONST
        and checks wheter the ICONST are in order. =#
        function expIntOrder(expectedValue::ModelicaInteger, integers::List{<:DAE.Exp}) ::Bool 
              local ob::Bool

              ob = begin
                  local expl::List{DAE.Exp}
                  local x1::ModelicaInteger
                  local x2::ModelicaInteger
                  local b::Bool
                @match (expectedValue, integers) begin
                  (_,  nil())  => begin
                    true
                  end
                  
                  (x1, DAE.ICONST(x2) <| expl) where (intEq(x1, x2))  => begin
                    expIntOrder(x1 + 1, expl)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          ob
        end

         #= returns true if expression is an array.
         =#
        function isArray(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.ARRAY(__)  => begin
                    true
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = DAE.ARRAY(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= returns true if expression is a MM array. =#
        function isMetaArray(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = Types.isMetaArray(typeof(inExp))
          outB
        end

         #= returns true if expression is an matrix.
         =#
        function isMatrix(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.MATRIX(__)  => begin
                    true
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = DAE.MATRIX(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= Returns true if the expression is a vector, i.e. an array with one dimension,
           otherwise false. =#
        function isVector(inExp::DAE.Exp) ::Bool 
              local outIsVector::Bool

              outIsVector = begin
                @match inExp begin
                  DAE.ARRAY(ty = DAE.T_ARRAY(ty = DAE.T_ARRAY(__)))  => begin
                    false
                  end
                  
                  DAE.ARRAY(ty = DAE.T_ARRAY(dims = _ <|  nil()))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  Nested arrays are not vectors.
               =#
               #=  Non-nested array with one dimension is a vector.
               =#
          outIsVector
        end

         #= Returns true if expression is an unary. =#
        function isUnary(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.UNARY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= Returns true if expression is an binary. =#
        function isBinary(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.BINARY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= Returns true if expression is a negative unary. =#
        function isNegativeUnary(inExp::DAE.Exp) ::Bool 
              local outB::Bool

              outB = begin
                @match inExp begin
                  DAE.UNARY(operator = DAE.UMINUS(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= Returns true if the given expression is a component reference,
           otherwise false. =#
        function isCref(inExp::DAE.Exp) ::Bool 
              local outIsCref::Bool

              outIsCref = begin
                @match inExp begin
                  DAE.CREF(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsCref
        end

        function isUnaryCref(inExp::DAE.Exp) ::Bool 
              local outIsCref::Bool

              outIsCref = begin
                @match inExp begin
                  DAE.UNARY(DAE.UMINUS(__), DAE.CREF(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsCref
        end

         #= Returns true if the given expression is a function call,
           otherwise false. =#
        function isCall(inExp::DAE.Exp) ::Bool 
              local outIsCall::Bool

              outIsCall = begin
                @match inExp begin
                  DAE.CALL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsCall
        end

         #= Returns true if the given expression is TSUB,
           otherwise false. =#
        function isTSUB(inExp::DAE.Exp) ::Bool 
              local outIsCall::Bool

              outIsCall = begin
                @match inExp begin
                  DAE.TSUB(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsCall
        end

         #= Returns true if the given expression is a pure function call,
           otherwise false. =#
        function isPureCall(inExp::DAE.Exp) ::Bool 
              local outIsPureCall::Bool

              outIsPureCall = isCall(inExp) && ! isImpure(inExp)
          outIsPureCall
        end

         #= Returns true if the given expression is a pure function call,
           otherwise false. =#
        function isImpureCall(inExp::DAE.Exp) ::Bool 
              local outIsPureCall::Bool

              outIsPureCall = isCall(inExp) && isImpure(inExp)
          outIsPureCall
        end

         #= Returns true if the given expression is a record call,i.e. a function call without elements
           otherwise false. =#
        function isRecordCall(inExp::DAE.Exp, funcsIn::DAE.FunctionTree) ::Bool 
              local outIsCall::Bool

              outIsCall = begin
                  local path::Absyn.Path
                  local func::DAE.Function
                @match (inExp, funcsIn) begin
                  (DAE.CALL(path = path), _)  => begin
                      @match SOME(func) = DAE.AvlTreePathFunction.get(funcsIn, path)
                    listEmpty(DAEUtil.getFunctionElements(func))
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsCall
        end

         #= Returns true if the given expression is a not component reference,
           otherwise false. =#
        function isNotCref(inExp::DAE.Exp) ::Bool 
              local outIsCref::Bool

              outIsCref = begin
                @match inExp begin
                  DAE.CREF(__)  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          outIsCref
        end

         #= Checks whether a cref is an array or not.
         =#
        function isCrefArray(inExp::DAE.Exp) ::Bool 
              local outIsArray::Bool

              outIsArray = begin
                @match inExp begin
                  DAE.CREF(ty = DAE.T_ARRAY(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsArray
        end

         #= Checks whether an expression is a scalar cref or not. =#
        function isCrefScalar(inExp::DAE.Exp) ::Bool 
              local isScalar::Bool

              isScalar = begin
                  local cr::ComponentRef
                  local b::Bool
                @matchcontinue inExp begin
                  DAE.CREF(ty = DAE.T_ARRAY(__))  => begin
                      cr = expCref(inExp)
                      b = ComponentReference.crefHasScalarSubscripts(cr)
                    b
                  end
                  
                  DAE.CREF(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isScalar
        end

         #= Returns true if the given expression is a tuple,
           otherwise false. =#
        function isTuple(inExp::DAE.Exp) ::Bool 
              local outIsTuple::Bool

              outIsTuple = begin
                @match inExp begin
                  DAE.TUPLE(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsTuple
        end

         #= Returns true if the given expression is a record,
           otherwise false. =#
        function isRecord(inExp::DAE.Exp) ::Bool 
              local outIsRecord::Bool

              outIsRecord = begin
                @match inExp begin
                  DAE.RECORD(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsRecord
        end

         #= Returns true if the given expression is a scalar constant, otherwise false. =#
        function isScalarConst(inExp::DAE.Exp) ::Bool 
              local outIsScalar::Bool

              outIsScalar = begin
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
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsScalar
        end

         #= Returns true if an expression is positive,
        Returns true in the following cases:
        constant >= 0

        See also isPositiveOrZero.
         =#
        function expIsPositive(e::DAE.Exp) ::Bool 
              local res::Bool

              res = isPositiveOrZero(e) && ! isZero(e)
          res
        end

         #= returns true if const expression is even =#
        function isEven(e::DAE.Exp) ::Bool 
              local even::Bool

              even = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local exp::DAE.Exp
                @match e begin
                  DAE.ICONST(i)  => begin
                    intMod(i, 2) == 0
                  end
                  
                  DAE.RCONST(r)  => begin
                    realMod(r, 2.0) == 0.0
                  end
                  
                  DAE.CAST(exp = exp)  => begin
                    isEven(exp)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          even
        end

         #= returns true if const expression is odd =#
        function isOdd(e::DAE.Exp) ::Bool 
              local even::Bool

              even = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local exp::DAE.Exp
                @match e begin
                  DAE.ICONST(i)  => begin
                    intMod(i, 2) == 1
                  end
                  
                  DAE.RCONST(r)  => begin
                    realMod(r, 2.0) == 1.0
                  end
                  
                  DAE.CAST(exp = exp)  => begin
                    isOdd(exp)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          even
        end

         #= Returns true if Type is Integer or Real =#
        function isIntegerOrReal(tp::DAE.Type) ::Bool 
              local res::Bool

              res = begin
                @match tp begin
                  DAE.T_REAL(__)  => begin
                    true
                  end
                  
                  DAE.T_INTEGER(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns true if the two expressions are equal, otherwise false. =#
        function expEqual(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool 
              local outEqual::Bool

              outEqual = 0 == compare(inExp1, inExp2)
          outEqual
        end

        function compareOpt(inExp1::Option{<:DAE.Exp}, inExp2::Option{<:DAE.Exp}) ::ModelicaInteger 
              local comp::ModelicaInteger

              local e1::DAE.Exp
              local e2::DAE.Exp

              comp = begin
                @match (inExp1, inExp2) begin
                  (NONE(), NONE())  => begin
                    0
                  end
                  
                  (NONE(), _)  => begin
                    -1
                  end
                  
                  (_, NONE())  => begin
                    1
                  end
                  
                  (SOME(e1), SOME(e2))  => begin
                    compare(e1, e2)
                  end
                end
              end
          comp
        end

        function compareList(inExpl1::List{<:DAE.Exp}, inExpl2::List{<:DAE.Exp}) ::ModelicaInteger 
              local comp::ModelicaInteger

              local len1::ModelicaInteger
              local len2::ModelicaInteger
              local e2::DAE.Exp
              local rest_expl2::List{DAE.Exp} = inExpl2
              local len1::ModelicaInteger
              local len2::ModelicaInteger

               #=  Check that the lists have the same length, otherwise they can't be equal.
               =#
              len1 = listLength(inExpl1)
              len2 = listLength(inExpl2)
              comp = Util.intCompare(len1, len2)
              if comp != 0
                return comp
              end
              for e1 in inExpl1
                @match _cons(e2, rest_expl2) = rest_expl2
                comp = compare(e1, e2)
                if 0 != comp
                  return comp
                end
              end
               #=  Return false if the expressions are not equal.
               =#
              comp = 0
          comp
        end

        function compareListList(inExpl1::List{<:List{<:DAE.Exp}}, inExpl2::List{<:List{<:DAE.Exp}}) ::ModelicaInteger 
              local comp::ModelicaInteger

              local expl2::List{DAE.Exp}
              local rest_expl2::List{List{DAE.Exp}} = inExpl2
              local len1::ModelicaInteger
              local len2::ModelicaInteger

               #=  Check that the lists have the same length, otherwise they can't be equal.
               =#
              len1 = listLength(inExpl1)
              len2 = listLength(inExpl2)
              comp = Util.intCompare(len1, len2)
              if comp != 0
                return comp
              end
              for expl1 in inExpl1
                @match _cons(expl2, rest_expl2) = rest_expl2
                comp = compareList(expl1, expl2)
                if 0 != comp
                  return comp
                end
              end
               #=  Return false if the expression lists are not equal.
               =#
              comp = 0
          comp
        end

         #= Returns true if the two expressions are structural equal. This means
          only the componentreference can be different =#
        function expStructuralEqual(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local s1::String
                  local s2::String
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local res::Bool
                  local e11::DAE.Exp
                  local e12::DAE.Exp
                  local e21::DAE.Exp
                  local e22::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e13::DAE.Exp
                  local e23::DAE.Exp
                  local op1::Operator
                  local op2::Operator
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local explstlst1::List{List{Exp}}
                  local explstlst2::List{List{Exp}}
                  local tp1::Type
                  local tp2::Type
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local enum1::Absyn.Path
                  local enum2::Absyn.Path
                  local cr1::ComponentRef
                  local cr2::ComponentRef
                  local ae1::List{DAE.Exp}
                  local ae2::List{DAE.Exp}
                @match (inExp1, inExp2) begin
                  (DAE.ICONST(integer = i1), DAE.ICONST(integer = i2))  => begin
                    i1 == i2
                  end
                  
                  (DAE.UNARY(DAE.UMINUS(_), DAE.ICONST(integer = i1)), DAE.ICONST(integer = i2))  => begin
                      i1 = -i1
                    i1 == i2
                  end
                  
                  (DAE.ICONST(integer = i1), DAE.UNARY(DAE.UMINUS(_), DAE.ICONST(integer = i2)))  => begin
                      i2 = -i2
                    i1 == i2
                  end
                  
                  (DAE.RCONST(real = r1), DAE.RCONST(real = r2))  => begin
                    r1 == r2
                  end
                  
                  (DAE.UNARY(DAE.UMINUS(_), DAE.RCONST(real = r1)), DAE.RCONST(real = r2))  => begin
                      r1 = -r1
                    r1 == r2
                  end
                  
                  (DAE.RCONST(real = r1), DAE.UNARY(DAE.UMINUS(_), DAE.RCONST(real = r2)))  => begin
                      r2 = -r2
                    r1 == r2
                  end
                  
                  (DAE.SCONST(string = s1), DAE.SCONST(string = s2))  => begin
                    stringEq(s1, s2)
                  end
                  
                  (DAE.BCONST(bool = b1), DAE.BCONST(bool = b2))  => begin
                    boolEq(b1, b2)
                  end
                  
                  (DAE.ENUM_LITERAL(name = enum1), DAE.ENUM_LITERAL(name = enum2))  => begin
                    AbsynUtil.pathEqual(enum1, enum2)
                  end
                  
                  (DAE.CREF(__), DAE.CREF(__))  => begin
                    true
                  end
                  
                  (DAE.BINARY(exp1 = e11, operator = op1, exp2 = e12), DAE.BINARY(exp1 = e21, operator = op2, exp2 = e22))  => begin
                      b = operatorEqual(op1, op2)
                      b = if b
                            expStructuralEqual(e11, e21)
                          else
                            b
                          end
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.LBINARY(exp1 = e11, operator = op1, exp2 = e12), DAE.LBINARY(exp1 = e21, operator = op2, exp2 = e22))  => begin
                      b = operatorEqual(op1, op2)
                      b = if b
                            expStructuralEqual(e11, e21)
                          else
                            b
                          end
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.UNARY(operator = op1, exp = e1), DAE.UNARY(operator = op2, exp = e2))  => begin
                      b = operatorEqual(op1, op2)
                      b = if b
                            expStructuralEqual(e1, e2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.LUNARY(operator = op1, exp = e1), DAE.LUNARY(operator = op2, exp = e2))  => begin
                      b = operatorEqual(op1, op2)
                      b = if b
                            expStructuralEqual(e1, e2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.RELATION(exp1 = e11, operator = op1, exp2 = e12), DAE.RELATION(exp1 = e21, operator = op2, exp2 = e22))  => begin
                      b = operatorEqual(op1, op2)
                      b = if b
                            expStructuralEqual(e11, e21)
                          else
                            b
                          end
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.IFEXP(expCond = e11, expThen = e12, expElse = e13), DAE.IFEXP(expCond = e21, expThen = e22, expElse = e23))  => begin
                      b = expStructuralEqual(e11, e21)
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                      b = if b
                            expStructuralEqual(e13, e23)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.CALL(path = path1, expLst = expl1), DAE.CALL(path = path2, expLst = expl2))  => begin
                      b = AbsynUtil.pathEqual(path1, path2)
                      b = if b
                            expStructuralEqualList(expl1, expl2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.RECORD(path = path1, exps = expl1), DAE.RECORD(path = path2, exps = expl2))  => begin
                      b = AbsynUtil.pathEqual(path1, path2)
                      b = if b
                            expStructuralEqualList(expl1, expl2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.PARTEVALFUNCTION(path = path1, expList = expl1), DAE.PARTEVALFUNCTION(path = path2, expList = expl2))  => begin
                      b = AbsynUtil.pathEqual(path1, path2)
                      b = if b
                            expStructuralEqualList(expl1, expl2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.ARRAY(ty = tp1, array = expl1), DAE.ARRAY(ty = tp2, array = expl2))  => begin
                      b = valueEq(tp1, tp2)
                      b = if b
                            expStructuralEqualList(expl1, expl2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.MATRIX(matrix = explstlst1), DAE.MATRIX(matrix = explstlst2))  => begin
                    expStructuralEqualListLst(explstlst1, explstlst2)
                  end
                  
                  (DAE.RANGE(start = e11, step = NONE(), stop = e13), DAE.RANGE(start = e21, step = NONE(), stop = e23))  => begin
                      b = expStructuralEqual(e11, e21)
                      b = if b
                            expStructuralEqual(e13, e23)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.RANGE(start = e11, step = SOME(e12), stop = e13), DAE.RANGE(start = e21, step = SOME(e22), stop = e23))  => begin
                      b = expStructuralEqual(e11, e21)
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                      b = if b
                            expStructuralEqual(e13, e23)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.TUPLE(PR = expl1), DAE.TUPLE(PR = expl2))  => begin
                    expStructuralEqualList(expl1, expl2)
                  end
                  
                  (DAE.CAST(ty = tp1, exp = e1), DAE.CAST(ty = tp2, exp = e2))  => begin
                      b = valueEq(tp1, tp2)
                      b = if b
                            expStructuralEqual(e1, e2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.ASUB(exp = e1, sub = ae1), DAE.ASUB(sub = ae2))  => begin
                      b = expStructuralEqual(e1, e1)
                      b = if b
                            expStructuralEqualList(ae1, ae2)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.SIZE(exp = e1, sz = NONE()), DAE.SIZE(exp = e2, sz = NONE()))  => begin
                    expStructuralEqual(e1, e2)
                  end
                  
                  (DAE.SIZE(exp = e1, sz = SOME(e11)), DAE.SIZE(exp = e2, sz = SOME(e22)))  => begin
                      b = expStructuralEqual(e1, e2)
                      b = if b
                            expStructuralEqual(e11, e22)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.CODE(__), DAE.CODE(__))  => begin
                      Debug.trace("exp_equal on CODE not impl.\\n")
                    false
                  end
                  
                  (DAE.REDUCTION(__), DAE.REDUCTION(__))  => begin
                      res = valueEq(inExp1, inExp2)
                    res
                  end
                  
                  (DAE.LIST(valList = expl1), DAE.LIST(valList = expl2))  => begin
                    expStructuralEqualList(expl1, expl2)
                  end
                  
                  (DAE.CONS(car = e11, cdr = e12), DAE.CONS(car = e21, cdr = e22))  => begin
                      b = expStructuralEqual(e11, e21)
                      b = if b
                            expStructuralEqual(e12, e22)
                          else
                            b
                          end
                    b
                  end
                  
                  (DAE.META_TUPLE(listExp = expl1), DAE.META_TUPLE(listExp = expl2))  => begin
                    expStructuralEqualList(expl1, expl2)
                  end
                  
                  (DAE.META_OPTION(exp = NONE()), DAE.META_OPTION(exp = NONE()))  => begin
                    true
                  end
                  
                  (DAE.META_OPTION(exp = SOME(e1)), DAE.META_OPTION(exp = SOME(e2)))  => begin
                    expStructuralEqual(e1, e2)
                  end
                  
                  (DAE.METARECORDCALL(path = path1, args = expl1), DAE.METARECORDCALL(path = path2, args = expl2))  => begin
                      b = AbsynUtil.pathEqual(path1, path2)
                      b = if b
                            expStructuralEqualList(expl1, expl2)
                          else
                            b
                          end
                    b
                  end
                  
                  (e1 && DAE.MATCHEXPRESSION(__), e2 && DAE.MATCHEXPRESSION(__))  => begin
                    valueEq(e1, e2)
                  end
                  
                  (DAE.BOX(e1), DAE.BOX(e2))  => begin
                    expStructuralEqual(e1, e2)
                  end
                  
                  (DAE.UNBOX(exp = e1), DAE.UNBOX(exp = e2))  => begin
                    expStructuralEqual(e1, e2)
                  end
                  
                  (DAE.SHARED_LITERAL(index = i1), DAE.SHARED_LITERAL(index = i2))  => begin
                    intEq(i1, i2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  binary ops
               =#
               #=  logical binary ops
               =#
               #=  unary ops
               =#
               #=  logical unary ops
               =#
               #=  relational ops
               =#
               #=  if expressions
               =#
               #=  function calls
               =#
               #=  partially evaluated functions
               =#
               #=  arrays
               =#
               #=  matrix
               =#
               #=  ranges [start:stop]
               =#
               #=  ranges [start:step:stop]
               =#
               #=  tuples
               =#
               #=  casting
               =#
               #=  array subscripts
               =#
               #=  size(a)
               =#
               #=  size(a, dim)
               =#
               #=  metamodeling code
               =#
               #=  Reductions contain too much information to compare equality in a sane manner
               =#
               #=  end id
               =#
               #= /* everything else failed, try structural equality
                  case (e1,e2)
                    equation
                      equality(e1 = e2);
                    then true;
                  case (e1,e2)
                    equation
                      failure(equality(e1 = e2));
                    then false;
                  */ =#
               #=  not equal
               =#
          outBoolean
        end

         #= Returns true if the two lists of expressions are structural equal. =#
        function expStructuralEqualList(inExp1::List{<:DAE.Exp}, inExp2::List{<:DAE.Exp}) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local es1::List{DAE.Exp}
                  local es2::List{DAE.Exp}
                  local b::Bool
                @match (inExp1, inExp2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (e1 <| es1, e2 <| es2) where (expStructuralEqual(e1, e2))  => begin
                    expStructuralEqualList(es1, es2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if the two lists of lists of expressions are structural equal. =#
        function expStructuralEqualListLst(inExp1::List{<:List{<:DAE.Exp}}, inExp2::List{<:List{<:DAE.Exp}}) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local e1::List{DAE.Exp}
                  local e2::List{DAE.Exp}
                  local es1::List{List{DAE.Exp}}
                  local es2::List{List{DAE.Exp}}
                  local b::Bool
                @match (inExp1, inExp2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (e1 <| es1, e2 <| es2) where (expStructuralEqualList(e1, e2))  => begin
                    expStructuralEqualListLst(es1, es2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if first expression contains the second one as a sub expression.
        Only constants, component references or der(componentReference) can be checked
        so far. =#
        function expContains(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local b1::Bool
                  local b2::Bool
                  local res::Bool
                  local cr1::ComponentRef
                  local cr2::ComponentRef
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local c::DAE.Exp
                  local t::DAE.Exp
                  local f::DAE.Exp
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local expLst::List{DAE.Exp}
                  local expl::List{List{DAE.Exp}}
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local str::String
                  local s1::String
                  local s2::String
                @matchcontinue (inExp1, inExp2) begin
                  (DAE.ICONST(i1), DAE.ICONST(i2))  => begin
                    i1 == i2
                  end
                  
                  (DAE.ICONST(__), _)  => begin
                    false
                  end
                  
                  (DAE.RCONST(r1), DAE.RCONST(r2))  => begin
                    r1 == r2
                  end
                  
                  (DAE.RCONST(__), _)  => begin
                    false
                  end
                  
                  (DAE.SCONST(s1), DAE.SCONST(s2))  => begin
                    s1 == s2
                  end
                  
                  (DAE.SCONST(__), _)  => begin
                    false
                  end
                  
                  (DAE.BCONST(b1), DAE.BCONST(b2))  => begin
                    b1 == b2
                  end
                  
                  (DAE.BCONST(__), _)  => begin
                    true
                  end
                  
                  (DAE.ENUM_LITERAL(__), _)  => begin
                    false
                  end
                  
                  (DAE.ARRAY(array = expLst), _)  => begin
                      res = ListUtil.map1BoolOr(expLst, expContains, inExp2)
                    res
                  end
                  
                  (DAE.MATRIX(matrix = expl), _)  => begin
                      res = ListUtil.map1ListBoolOr(expl, expContains, inExp2)
                    res
                  end
                  
                  (DAE.CREF(componentRef = cr1), DAE.CREF(componentRef = cr2))  => begin
                      res = ComponentReference.crefEqual(cr1, cr2)
                      if ! res
                        expLst = ListUtil.map(ComponentReference.crefSubs(cr1), getSubscriptExp)
                        res = ListUtil.map1BoolOr(expLst, expContains, inExp2)
                      end
                    res
                  end
                  
                  (DAE.CREF(__), _)  => begin
                    false
                  end
                  
                  (DAE.BINARY(exp1 = e1, exp2 = e2), _)  => begin
                      res = expContains(e1, inExp2)
                      res = if res
                            true
                          else
                            expContains(e2, inExp2)
                          end
                    res
                  end
                  
                  (DAE.UNARY(exp = e), _)  => begin
                      res = expContains(e, inExp2)
                    res
                  end
                  
                  (DAE.LBINARY(exp1 = e1, exp2 = e2), _)  => begin
                      res = expContains(e1, inExp2)
                      res = if res
                            true
                          else
                            expContains(e2, inExp2)
                          end
                    res
                  end
                  
                  (DAE.LUNARY(exp = e), _)  => begin
                      res = expContains(e, inExp2)
                    res
                  end
                  
                  (DAE.RELATION(exp1 = e1, exp2 = e2), _)  => begin
                      res = expContains(e1, inExp2)
                      res = if res
                            true
                          else
                            expContains(e2, inExp2)
                          end
                    res
                  end
                  
                  (DAE.IFEXP(expCond = c, expThen = t, expElse = f), _)  => begin
                      res = expContains(c, inExp2)
                      res = if res
                            true
                          else
                            expContains(t, inExp2)
                          end
                      res = if res
                            true
                          else
                            expContains(f, inExp2)
                          end
                    res
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "der"), expLst = DAE.CREF(cr1) <|  nil()), DAE.CALL(path = Absyn.IDENT(name = "der"), expLst = DAE.CREF(cr2) <|  nil()))  => begin
                      res = ComponentReference.crefEqual(cr1, cr2)
                    res
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "pre")), _)  => begin
                    false
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT(name = "previous")), _)  => begin
                    false
                  end
                  
                  (DAE.CALL(expLst =  nil()), _)  => begin
                    false
                  end
                  
                  (DAE.CALL(expLst = expLst), _)  => begin
                      res = ListUtil.map1BoolOr(expLst, expContains, inExp2)
                    res
                  end
                  
                  (DAE.PARTEVALFUNCTION(expList = expLst), DAE.CREF(__))  => begin
                      res = ListUtil.map1BoolOr(expLst, expContains, inExp2)
                    res
                  end
                  
                  (DAE.CAST(ty = DAE.T_REAL(__), exp = DAE.ICONST(__)), _)  => begin
                    false
                  end
                  
                  (DAE.CAST(ty = DAE.T_REAL(__), exp = e), _)  => begin
                      res = expContains(e, inExp2)
                    res
                  end
                  
                  (DAE.ASUB(exp = e, sub = expLst), _)  => begin
                      res = ListUtil.map1BoolOr(expLst, expContains, inExp2)
                      res = if res
                            true
                          else
                            expContains(e, inExp2)
                          end
                    res
                  end
                  
                  (DAE.REDUCTION(expr = e), _)  => begin
                      res = expContains(e, inExp2)
                    res
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Expression.expContains failed\\n")
                        s1 = ExpressionDump.printExpStr(inExp1)
                        s2 = ExpressionDump.printExpStr(inExp2)
                        str = stringAppendList(list("exp = ", s1, " subexp = ", s2))
                        Debug.traceln(str)
                      fail()
                  end
                end
              end
               #=  pre(v) does not contain variable v
               =#
               #=  special rule for no arguments
               =#
               #=  general case for arguments
               =#
               #= /* record constructors
                  case (DAE.RECORD(exps=expLst), DAE.CREF()) equation
                    res = List.map1BoolOr(expLst, expContains, inExp2);
                  then res; */ =#
          outBoolean
        end

         #= Author BZ 2008-06 same as expContains, but reversed. =#
        function containsExp(inExp1::DAE.Exp, inExp2::DAE.Exp) ::Bool 
              local outBoolean::Bool

              outBoolean = expContains(inExp2, inExp1)
          outBoolean
        end

         #= Returns true if expression is a componentRef or an if expression =#
        function isExpCrefOrIfExp(e::DAE.Exp) ::Bool 
              local res::Bool

              res = begin
                @match e begin
                  DAE.CREF(_, _)  => begin
                    true
                  end
                  
                  DAE.IFEXP(_, _, _)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns true if expression is an if expression =#
        function isExpIfExp(e::DAE.Exp) ::Bool 
              local res::Bool

              res = begin
                @match e begin
                  DAE.IFEXP(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Helper function to expEqual. =#
        function operatorEqual(inOperator1::DAE.Operator, inOperator2::DAE.Operator) ::Bool 
              local outBoolean::Bool

              outBoolean = 0 == operatorCompare(inOperator1, inOperator2)
          outBoolean
        end

         #= Helper function to expEqual. =#
        function operatorCompare(inOperator1::DAE.Operator, inOperator2::DAE.Operator) ::ModelicaInteger 
              local comp::ModelicaInteger

              comp = begin
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                @match (inOperator1, inOperator2) begin
                  (DAE.USERDEFINED(fqName = p1), DAE.USERDEFINED(fqName = p2))  => begin
                    AbsynUtil.pathCompare(p1, p2)
                  end
                  
                  _  => begin
                      Util.intCompare(valueConstructor(inOperator1), valueConstructor(inOperator2))
                  end
                end
              end
          comp
        end

         #= Checks if one of the dimensions in a list is zero. =#
        function arrayContainZeroDimension(inDimensions::List{<:DAE.Dimension}) ::Bool 
              local outContainZeroDim::Bool

              outContainZeroDim = begin
                  local rest_dims::List{DAE.Dimension}
                @match inDimensions begin
                  DAE.DIM_INTEGER(0) <| _  => begin
                    true
                  end
                  
                  _ <| rest_dims  => begin
                    arrayContainZeroDimension(rest_dims)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outContainZeroDim
        end

         #= Checks if a list of dimensions contain a wholedim, i.e. NONE. =#
        function arrayContainWholeDimension(inDim::DAE.Dimensions) ::Bool 
              local wholedim::Bool

              wholedim = begin
                  local rest_dims::DAE.Dimensions
                @match inDim begin
                  DAE.DIM_UNKNOWN(__) <| _  => begin
                    true
                  end
                  
                  _ <| rest_dims  => begin
                    arrayContainWholeDimension(rest_dims)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          wholedim
        end

         #= Returns true if inType is an T_ARRAY =#
        function isArrayType(inType::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Return true if the type is a record type. =#
        function isRecordType(inType::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= returns true if the exp is 1-dimensional =#
        function isNotComplex(e::DAE.Exp) ::Bool 
              local b::Bool

              b = begin
                  local b2::Bool
                  local e2::DAE.Exp
                @match e begin
                  DAE.CALL(__)  => begin
                    false
                  end
                  
                  DAE.RECORD(__)  => begin
                    false
                  end
                  
                  DAE.ARRAY(__)  => begin
                    false
                  end
                  
                  DAE.CAST(exp = e2)  => begin
                      b2 = isNotComplex(e2)
                    b2
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          b
        end

         #= Return true if the type is Real. =#
        function isRealType(inType::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns whether two dimensions are equal or not. =#
        function dimensionsEqual(dim1::DAE.Dimension, dim2::DAE.Dimension) ::Bool 
              local res::Bool

              res = begin
                  local b::Bool
                @match (dim1, dim2) begin
                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    true
                  end
                  
                  (_, DAE.DIM_UNKNOWN(__))  => begin
                    true
                  end
                  
                  (DAE.DIM_EXP(__), _)  => begin
                    true
                  end
                  
                  (_, DAE.DIM_EXP(__))  => begin
                    true
                  end
                  
                  _  => begin
                        b = intEq(dimensionSize(dim1), dimensionSize(dim2))
                      b
                  end
                end
              end
          res
        end

         #= Returns whether two dimensions are equal or not. =#
        function dimsEqual(dims1::DAE.Dimensions, dims2::DAE.Dimensions) ::Bool 
              local res::Bool

              res = begin
                  local d1::DAE.Dimension
                  local d2::DAE.Dimension
                  local dl1::DAE.Dimensions
                  local dl2::DAE.Dimensions
                @match (dims1, dims2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (d1 <| dl1, d2 <| dl2) where (dimensionsEqual(d1, d2))  => begin
                    dimsEqual(dl1, dl2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns whether two dimensions are equal or not.
         0 == anydim is allowed =#
        function dimsEqualAllowZero(dims1::DAE.Dimensions, dims2::DAE.Dimensions) ::Bool 
              local res::Bool

              res = begin
                  local d1::DAE.Dimension
                  local d2::DAE.Dimension
                  local dl1::DAE.Dimensions
                  local dl2::DAE.Dimensions
                @match (dims1, dims2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (d1 <| dl1, d2 <| dl2) where (dimensionsEqualAllowZero(d1, d2))  => begin
                    dimsEqualAllowZero(dl1, dl2)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns whether two dimensions are equal or not.
         0 == anyDim is allowed =#
        function dimensionsEqualAllowZero(dim1::DAE.Dimension, dim2::DAE.Dimension) ::Bool 
              local res::Bool

              res = begin
                  local b::Bool
                  local d1::ModelicaInteger
                  local d2::ModelicaInteger
                @match (dim1, dim2) begin
                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    true
                  end
                  
                  (_, DAE.DIM_UNKNOWN(__))  => begin
                    true
                  end
                  
                  (DAE.DIM_EXP(__), _)  => begin
                    true
                  end
                  
                  (_, DAE.DIM_EXP(__))  => begin
                    true
                  end
                  
                  _  => begin
                        d1 = dimensionSize(dim1)
                        d2 = dimensionSize(dim2)
                        b = boolOr(intEq(d1, d2), boolOr(boolAnd(intEq(d1, 0), intNe(d2, 0)), boolAnd(intEq(d2, 0), intNe(d1, 0))))
                      b
                  end
                end
              end
          res
        end

         #= Checks that two dimensions are specified and equal. =#
        function dimensionsKnownAndEqual(dim1::DAE.Dimension, dim2::DAE.Dimension) ::Bool 
              local res::Bool

              res = begin
                @match (dim1, dim2) begin
                  (DAE.DIM_UNKNOWN(__), _)  => begin
                    false
                  end
                  
                  (_, DAE.DIM_UNKNOWN(__))  => begin
                    false
                  end
                  
                  _  => begin
                      expEqual(dimensionSizeExp(dim1), dimensionSizeExp(dim2))
                  end
                end
              end
               #=  dimensionSizeExp fails on DIM_UNKNOWN...
               =#
          res
        end

         #= Checks whether a dimensions is known or not. =#
        function dimensionKnown(dim::DAE.Dimension) ::Bool 
              local known::Bool

              known = begin
                @match dim begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    false
                  end
                  
                  DAE.DIM_EXP(exp = DAE.ICONST(__))  => begin
                    true
                  end
                  
                  DAE.DIM_EXP(exp = DAE.BCONST(__))  => begin
                    true
                  end
                  
                  DAE.DIM_EXP(exp = DAE.ENUM_LITERAL(__))  => begin
                    true
                  end
                  
                  DAE.DIM_EXP(__)  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          known
        end

         #= Checks whether a dimensions is known or not. =#
        function dimensionKnownAndNonZero(dim::DAE.Dimension) ::Bool 
              local known::Bool

              known = begin
                @match dim begin
                  DAE.DIM_EXP(exp = DAE.ICONST(0))  => begin
                    false
                  end
                  
                  DAE.DIM_INTEGER(0)  => begin
                    false
                  end
                  
                  _  => begin
                      dimensionKnown(dim)
                  end
                end
              end
          known
        end

         #= Checks whether all dimensions are known or not.
          TODO: mahge: imprive this for speed =#
        function dimensionsKnownAndNonZero(dims::List{<:DAE.Dimension}) ::Bool 
              local allKnown::Bool

              allKnown = ListUtil.mapBoolAnd(dims, dimensionKnownAndNonZero)
          allKnown
        end

         #= Checks whether a dimensions is known or not. =#
        function dimensionUnknownOrExp(dim::DAE.Dimension) ::Bool 
              local known::Bool

              known = begin
                @match dim begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    true
                  end
                  
                  DAE.DIM_EXP(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          known
        end

        function dimensionUnknown(inDimension::DAE.Dimension) ::Bool 
              local outUnknown::Bool

              outUnknown = begin
                @match inDimension begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outUnknown
        end

         #= Returns true if two subscript lists are equal. =#
        function subscriptEqual(inSubscriptLst1::List{<:DAE.Subscript}, inSubscriptLst2::List{<:DAE.Subscript}) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local xs1::List{DAE.Subscript}
                  local xs2::List{DAE.Subscript}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                   #=  both lists are empty
                   =#
                @match (inSubscriptLst1, inSubscriptLst2) begin
                  ( nil(),  nil())  => begin
                    true
                  end
                  
                  (DAE.WHOLEDIM(__) <| xs1, DAE.WHOLEDIM(__) <| xs2)  => begin
                    subscriptEqual(xs1, xs2)
                  end
                  
                  (DAE.SLICE(exp = e1) <| xs1, DAE.SLICE(exp = e2) <| xs2)  => begin
                    if expEqual(e1, e2)
                          subscriptEqual(xs1, xs2)
                        else
                          false
                        end
                  end
                  
                  (DAE.INDEX(exp = e1) <| xs1, DAE.INDEX(exp = e2) <| xs2)  => begin
                    if expEqual(e1, e2)
                          subscriptEqual(xs1, xs2)
                        else
                          false
                        end
                  end
                  
                  (DAE.WHOLE_NONEXP(exp = e1) <| xs1, DAE.WHOLE_NONEXP(exp = e2) <| xs2)  => begin
                    if expEqual(e1, e2)
                          subscriptEqual(xs1, xs2)
                        else
                          false
                        end
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  wholedims as list heads, compare the rest
               =#
               #=  slices as heads, compare the slice exps and then compare the rest
               =#
               #=  indexes as heads, compare the index exps and then compare the rest
               =#
               #=  subscripts are not equal, return false
               =#
          outBoolean
        end

         #= 
        returns true if all subscripts are known (i.e no cref) constant values (no slice or wholedim) =#
        function subscriptConstants(inSubs::List{<:DAE.Subscript}) ::Bool 
              local areConstant::Bool = true

              for sub in inSubs
                areConstant = begin
                  @match sub begin
                    DAE.INDEX(exp = DAE.ICONST(__))  => begin
                      true
                    end
                    
                    DAE.INDEX(exp = DAE.ENUM_LITERAL(__))  => begin
                      true
                    end
                    
                    DAE.INDEX(exp = DAE.BCONST(__))  => begin
                      true
                    end
                    
                    _  => begin
                        false
                    end
                  end
                end
                if ! areConstant
                  return areConstant
                end
              end
          areConstant
        end

         #= Checks if an expression is a valid subscript, i.e. an integer or enumeration
          literal. =#
        function isValidSubscript(inSub::DAE.Exp) ::Bool 
              local isValid::Bool

              isValid = begin
                @match inSub begin
                  DAE.ICONST(__)  => begin
                    true
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  DAE.BCONST(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isValid
        end

         #= This function checks whether sub2 contains sub1 or not(DAE.WHOLEDIM()) =#
        function subscriptContain(issl1::List{<:DAE.Subscript}, issl2::List{<:DAE.Subscript}) ::Bool 
              local contained::Bool

              contained = begin
                  local b::Bool
                  local ss1::Subscript
                  local ss2::Subscript
                  local ssl1::List{DAE.Subscript}
                  local ssl2::List{DAE.Subscript}
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local i::ModelicaInteger
                  local expl::List{DAE.Exp}
                @match (issl1, issl2) begin
                  ( nil(), _)  => begin
                    true
                  end
                  
                  (_ <| ssl1, DAE.WHOLEDIM(__) <| ssl2)  => begin
                      b = subscriptContain(ssl1, ssl2)
                    b
                  end
                  
                  (_ <| ssl1, DAE.WHOLE_NONEXP(_) <| ssl2)  => begin
                      b = subscriptContain(ssl1, ssl2)
                    b
                  end
                  
                  (DAE.INDEX(DAE.ICONST(i)) <| ssl1, DAE.SLICE(DAE.ARRAY(_, _, expl)) <| ssl2)  => begin
                      @match true = subscriptContain2(i, expl)
                      b = subscriptContain(ssl1, ssl2)
                    b
                  end
                  
                  (ss1 <| ssl1, ss2 <| ssl2)  => begin
                      @match true = subscriptEqual(list(ss1), list(ss2))
                      b = subscriptContain(ssl1, ssl2)
                    b
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  Should there be additional checking in this case?
               =#
               #= /*    case(ss1::ssl1, (ss2 as DAE.SLICE(exp)) ::ssl2)
                    local DAE.Exp exp;
                      equation
                       b = subscriptContain(ssl1,ssl2);
                      then
                        b;
                        */ =#
          contained
        end

         #= 
         =#
        function subscriptContain2(inInt::ModelicaInteger, inExp2::List{<:DAE.Exp}) ::Bool 
              local contained::Bool

              contained = begin
                  local b::Bool
                  local b2::Bool
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local expl::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                @match (inInt, inExp2) begin
                  (i, DAE.ICONST(j) <| _) where (i == j)  => begin
                    true
                  end
                  
                  (i, DAE.ICONST(_) <| expl) where (subscriptContain2(i, expl))  => begin
                    true
                  end
                  
                  (i, DAE.ARRAY(_, _, expl2) <| expl)  => begin
                      b = subscriptContain2(i, expl2)
                      b2 = if b
                            true
                          else
                            subscriptContain2(i, expl)
                          end
                    b2
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          contained
        end

         #= Returns true if the expression is free from side-effects. Use with traverseExpBottomUp. =#
        function hasNoSideEffects(inExp::DAE.Exp, ib::Bool) ::Tuple{DAE.Exp, Bool} 
              local ob::Bool
              local outExp::DAE.Exp

              (outExp, ob) = begin
                  local e::DAE.Exp
                @match (inExp, ib) begin
                  (DAE.CALL(__), _)  => begin
                    (inExp, false)
                  end
                  
                  (DAE.MATCHEXPRESSION(__), _)  => begin
                    (inExp, false)
                  end
                  
                  _  => begin
                      (inExp, ib)
                  end
                end
              end
          (outExp, ob)
        end

         #= Returns true if the expression is a reference to a builtin function =#
        function isBuiltinFunctionReference(exp::DAE.Exp) ::Bool 
              local b::Bool

              b = begin
                @match exp begin
                  DAE.CREF(ty = DAE.T_FUNCTION_REFERENCE_FUNC(builtin = true))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= DAE.CONS =#
        function makeCons(car::DAE.Exp, cdr::DAE.Exp) ::DAE.Exp 
              local exp::DAE.Exp

              exp = DAE.CONS(car, cdr)
          exp
        end

         #= Create a DAE.CALL with the given data for a call to a builtin function. =#
        function makeBuiltinCall(name::String, args::List{<:DAE.Exp}, result_type::DAE.Type, isImpure::Bool) ::DAE.Exp 
              local call::DAE.Exp

              call = DAE.CALL(Absyn.IDENT(name), args, DAE.CALL_ATTR(result_type, false, true, isImpure, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
          call
        end

         #= Create a DAE.CALL with the given data for a call to a builtin function. =#
        function makePureBuiltinCall(name::String, args::List{<:DAE.Exp}, result_type::DAE.Type) ::DAE.Exp 
              local call::DAE.Exp

              call = makeBuiltinCall(name, args, result_type, false)
          call
        end

         #= Create a DAE.CALL with the given data for a call to a builtin function. =#
        function makeImpureBuiltinCall(name::String, args::List{<:DAE.Exp}, result_type::DAE.Type) ::DAE.Exp 
              local call::DAE.Exp

              call = makeBuiltinCall(name, args, result_type, true)
          call
        end

        function reductionIterName(iter::DAE.ReductionIterator) ::String 
              local name::String

              @match DAE.REDUCTIONITER(id = name) = iter
          name
        end

        function traverseReductionIteratorBidir(inIter::DAE.ReductionIterator, inEnterFunc::FuncType, inExitFunc::FuncType, inArg::ArgT)  where {ArgT}
              local outArg::ArgT
              local outIter::DAE.ReductionIterator

              (outIter, outArg) = begin
                  local id::String
                  local exp::DAE.Exp
                  local gexp::Option{DAE.Exp}
                  local ty::DAE.Type
                  local arg::ArgT
                @match inIter begin
                  DAE.REDUCTIONITER(id, exp, gexp, ty)  => begin
                      (exp, arg) = traverseExpBidir(exp, inEnterFunc, inExitFunc, inArg)
                      (gexp, arg) = traverseExpOptBidir(gexp, inEnterFunc, inExitFunc, arg)
                    (DAE.REDUCTIONITER(id, exp, gexp, ty), arg)
                  end
                end
              end
          (outIter, outArg)
        end

        function traverseReductionIteratorTopDown(iter::DAE.ReductionIterator, func::FuncExpType, inArg::Type_a) ::Tuple{DAE.ReductionIterator, Type_a} 
              local outArg::Type_a
              local outIter::DAE.ReductionIterator

              (outIter, outArg) = begin
                  local id::String
                  local exp::DAE.Exp
                  local gexp::Option{DAE.Exp}
                  local ty::DAE.Type
                  local arg::Type_a
                @match (iter, func, inArg) begin
                  (DAE.REDUCTIONITER(id, exp, gexp, ty), _, arg)  => begin
                      (exp, arg) = traverseExpTopDown(exp, func, arg)
                      (gexp, arg) = traverseExpOptTopDown(gexp, func, arg)
                    (DAE.REDUCTIONITER(id, exp, gexp, ty), arg)
                  end
                end
              end
          (outIter, outArg)
        end

        function traverseReductionIteratorsTopDown(inIters::DAE.ReductionIterators, func::FuncExpType, inArg::Type_a) ::Tuple{DAE.ReductionIterators, Type_a} 
              local outArg::Type_a
              local outIters::DAE.ReductionIterators

              (outIters, outArg) = begin
                  local arg::Type_a
                  local iter::DAE.ReductionIterator
                  local iters::DAE.ReductionIterators
                @match (inIters, func, inArg) begin
                  ( nil(), _, arg)  => begin
                    (inIters, arg)
                  end
                  
                  (iter <| iters, _, arg)  => begin
                      (iter, arg) = traverseReductionIteratorTopDown(iter, func, arg)
                      (iters, arg) = traverseReductionIteratorsTopDown(iters, func, arg)
                    (_cons(iter, iters), arg)
                  end
                end
              end
          (outIters, outArg)
        end

        function traverseReductionIterator(iter::DAE.ReductionIterator, func::FuncExpType, iarg::Type_a) ::Tuple{DAE.ReductionIterator, Type_a} 
              local outArg::Type_a
              local outIter::DAE.ReductionIterator

              (outIter, outArg) = begin
                  local id::String
                  local exp::DAE.Exp
                  local exp1::DAE.Exp
                  local gexp::Option{DAE.Exp}
                  local gexp1::Option{DAE.Exp}
                  local ty::DAE.Type
                  local arg::Type_a
                @match (iter, func, iarg) begin
                  (DAE.REDUCTIONITER(id, exp, gexp, ty), _, arg)  => begin
                      (exp1, arg) = traverseExpBottomUp(exp, func, arg)
                      (gexp1, arg) = traverseExpOpt(gexp, func, arg)
                      outIter = if referenceEq(exp, exp1) && referenceEq(gexp, gexp1)
                            iter
                          else
                            DAE.REDUCTIONITER(id, exp1, gexp1, ty)
                          end
                    (outIter, arg)
                  end
                end
              end
          (outIter, outArg)
        end

        function traverseReductionIterators(iters::DAE.ReductionIterators, func::FuncExpType, arg::Type_a) ::Tuple{DAE.ReductionIterators, Type_a} 



              (iters, arg) = begin
                  local iter::DAE.ReductionIterator
                  local iter1::DAE.ReductionIterator
                  local rest::DAE.ReductionIterators
                  local iters1::DAE.ReductionIterators
                @match iters begin
                   nil()  => begin
                    (iters, arg)
                  end
                  
                  iter <| rest  => begin
                      (iter1, arg) = traverseReductionIterator(iter, func, arg)
                      (iters1, arg) = traverseReductionIterators(rest, func, arg)
                      iters = if referenceEq(iter, iter1) && referenceEq(rest, iters1)
                            iters
                          else
                            _cons(iter1, iters1)
                          end
                    (iters, arg)
                  end
                end
              end
          (iters, arg)
        end

        function simpleCrefName(exp::DAE.Exp) ::String 
              local name::String

              @match DAE.CREF(componentRef = DAE.CREF_IDENT(ident = name, subscriptLst = nil)) = exp
          name
        end

        function isTailCall(exp::DAE.Exp) ::Bool 
              local isTail::Bool

              isTail = begin
                @match exp begin
                  DAE.CALL(attr = DAE.CALL_ATTR(tailCall = DAE.TAIL(__)))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isTail
        end

        function complexityTraverse(exp::DAE.Exp, complexity::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local outComplexity::ModelicaInteger
              local outExp::DAE.Exp

              (outExp, outComplexity) = traverseExpBottomUp(exp, complexityTraverse2, complexity)
          (outExp, outComplexity)
        end

        function complexityTraverse2(exp::DAE.Exp, complexity_::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local outComplexity::ModelicaInteger
              local outExp::DAE.Exp

              outComplexity = complexity_ + complexity(exp)
              outExp = exp
          (outExp, outComplexity)
        end

         const complexityAlloc = 5::ModelicaInteger

         const complexityVeryBig = 500000 #= Things that are too hard to calculate :( =#::ModelicaInteger

         const complexityDimLarge = 1000 #= Unknown dimensions usually aren't big, but might be =#::ModelicaInteger

        function complexity(exp::DAE.Exp) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                  local op::DAE.Operator
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local c1::ModelicaInteger
                  local c2::ModelicaInteger
                  local c3::ModelicaInteger
                  local exps::List{DAE.Exp}
                  local matrix::List{List{DAE.Exp}}
                  local str::String
                  local name::String
                  local tp::DAE.Type
                @match exp begin
                  DAE.ICONST(__)  => begin
                    0
                  end
                  
                  DAE.RCONST(__)  => begin
                    0
                  end
                  
                  DAE.SCONST(__)  => begin
                    0
                  end
                  
                  DAE.BCONST(__)  => begin
                    0
                  end
                  
                  DAE.SHARED_LITERAL(__)  => begin
                    0
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    0
                  end
                  
                  DAE.CREF(ty = tp)  => begin
                    tpComplexity(tp)
                  end
                  
                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      c1 = complexity(e1)
                      c2 = complexity(e2)
                      c3 = opComplexity(op)
                    c1 + c2 + c3
                  end
                  
                  DAE.UNARY(exp = e, operator = op)  => begin
                      c1 = complexity(e)
                      c2 = opComplexity(op)
                    c1 + c2
                  end
                  
                  DAE.LBINARY(exp1 = e1, exp2 = e2, operator = op)  => begin
                      c1 = complexity(e1)
                      c2 = complexity(e2)
                      c3 = opComplexity(op)
                    c1 + c2 + c3
                  end
                  
                  DAE.LUNARY(exp = e, operator = op)  => begin
                      c1 = complexity(e)
                      c2 = opComplexity(op)
                    c1 + c2
                  end
                  
                  DAE.RELATION(exp1 = e1, exp2 = e2, operator = op)  => begin
                      c1 = complexity(e1)
                      c2 = complexity(e2)
                      c3 = opComplexity(op)
                    c1 + c2 + c3
                  end
                  
                  DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3)  => begin
                      c1 = complexity(e1)
                      c2 = complexity(e2)
                      c3 = complexity(e3)
                    c1 + intMax(c2, c3)
                  end
                  
                  DAE.CALL(path = Absyn.IDENT(name), expLst = exps, attr = DAE.CALL_ATTR(ty = tp, builtin = true))  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, 0)
                      c2 = complexityBuiltin(name, tp)
                    c1 + c2
                  end
                  
                  DAE.CALL(expLst = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, 0)
                      c2 = listLength(exps)
                    c1 + c2 + 25
                  end
                  
                  DAE.RECORD(exps = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, 1)
                    c1
                  end
                  
                  DAE.PARTEVALFUNCTION(__)  => begin
                    complexityVeryBig
                  end
                  
                  DAE.ARRAY(array = exps, ty = tp)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, if isArrayType(tp)
                            0
                          else
                            complexityAlloc
                          end)
                      c2 = listLength(exps)
                    c1 + c2
                  end
                  
                  DAE.MATRIX(matrix = matrix && exps <| _)  => begin
                      c1 = ListUtil.applyAndFold(ListUtil.flatten(matrix), intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps) * listLength(matrix)
                    c1 + c2
                  end
                  
                  DAE.RANGE(start = e1, stop = e2, step = NONE())  => begin
                    complexityDimLarge + complexity(e1) + complexity(e2)
                  end
                  
                  DAE.RANGE(start = e1, stop = e2, step = SOME(e3))  => begin
                    complexityDimLarge + complexity(e1) + complexity(e2) + complexity(e3)
                  end
                  
                  DAE.TUPLE(PR = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps)
                    c1 + c2
                  end
                  
                  DAE.CAST(exp = e, ty = tp)  => begin
                    tpComplexity(tp) + complexity(e)
                  end
                  
                  DAE.ASUB(exp = e, sub = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps)
                      c3 = complexity(e)
                    c1 + c2 + c3
                  end
                  
                  DAE.TSUB(exp = e)  => begin
                    complexity(e) + 1
                  end
                  
                  DAE.SIZE(exp = e, sz = NONE())  => begin
                    complexity(e) + complexityAlloc + 10
                  end
                  
                  DAE.SIZE(exp = e1, sz = SOME(e2))  => begin
                    complexity(e1) + complexity(e2) + 1
                  end
                  
                  DAE.CODE(__)  => begin
                    complexityVeryBig
                  end
                  
                  DAE.EMPTY(__)  => begin
                    complexityVeryBig
                  end
                  
                  DAE.REDUCTION(__)  => begin
                    complexityVeryBig
                  end
                  
                  DAE.LIST(valList = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps)
                    c1 + c2 + complexityAlloc
                  end
                  
                  DAE.CONS(car = e1, cdr = e2)  => begin
                    complexityAlloc + complexity(e1) + complexity(e2)
                  end
                  
                  DAE.META_TUPLE(listExp = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps)
                    complexityAlloc + c1 + c2
                  end
                  
                  DAE.META_OPTION(exp = NONE())  => begin
                    0
                  end
                  
                  DAE.META_OPTION(exp = SOME(e))  => begin
                    complexity(e) + complexityAlloc
                  end
                  
                  DAE.METARECORDCALL(args = exps)  => begin
                      c1 = ListUtil.applyAndFold(exps, intAdd, complexity, complexityAlloc)
                      c2 = listLength(exps)
                    c1 + c2 + complexityAlloc
                  end
                  
                  DAE.MATCHEXPRESSION(__)  => begin
                    complexityVeryBig
                  end
                  
                  DAE.BOX(exp = e)  => begin
                    complexityAlloc + complexity(e)
                  end
                  
                  DAE.UNBOX(exp = e)  => begin
                    1 + complexity(e)
                  end
                  
                  DAE.PATTERN(__)  => begin
                    0
                  end
                  
                  _  => begin
                        str = "Expression.complexityWork failed: " + ExpressionDump.printExpStr(exp)
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #= /* TODO: Cost is based on type and size of inputs. Maybe even name for builtins :) */ =#
               #= /* TODO: Cost is based on type and size of inputs. Maybe even name for builtins :) */ =#
               #= /* This should not be here anyway :) */ =#
               #= /* TODO: Check type maybe? */ =#
               #= /* TODO: Check type maybe? */ =#
               #= /* TODO: Cost is based on type (creating the array) */ =#
               #= /* TODO: We need a real traversal... */ =#
          i
        end

        function complexityBuiltin(name::String, tp::DAE.Type) ::ModelicaInteger 
              local complexity::ModelicaInteger

              complexity = begin
                @match (name, tp) begin
                  ("identity", _)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  ("cross", _)  => begin
                    3 * 3
                  end
                  
                  _  => begin
                      25
                  end
                end
              end
          complexity
        end

        function tpComplexity(tp::DAE.Type) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                  local dims::List{DAE.Dimension}
                @match tp begin
                  DAE.T_ARRAY(dims = dims)  => begin
                      i = ListUtil.applyAndFold(dims, intMul, dimComplexity, 1)
                    i
                  end
                  
                  _  => begin
                      0
                  end
                end
              end
          i
        end

        function dimComplexity(dim::DAE.Dimension) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                @match dim begin
                  DAE.DIM_INTEGER(integer = i)  => begin
                    i
                  end
                  
                  DAE.DIM_ENUM(size = i)  => begin
                    i
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    2
                  end
                  
                  _  => begin
                      complexityDimLarge
                  end
                end
              end
          i
        end

        function opComplexity(op::DAE.Operator) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                  local tp::DAE.Type
                @match op begin
                  DAE.ADD(ty = DAE.T_STRING(__))  => begin
                    100
                  end
                  
                  DAE.ADD(__)  => begin
                    1
                  end
                  
                  DAE.SUB(__)  => begin
                    1
                  end
                  
                  DAE.MUL(__)  => begin
                    1
                  end
                  
                  DAE.DIV(__)  => begin
                    1
                  end
                  
                  DAE.POW(__)  => begin
                    30
                  end
                  
                  DAE.UMINUS(__)  => begin
                    1
                  end
                  
                  DAE.UMINUS_ARR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.ADD_ARR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.SUB_ARR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.MUL_ARR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.DIV_ARR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.SUB_SCALAR_ARRAY(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.MUL_SCALAR_PRODUCT(ty = tp)  => begin
                    complexityAlloc + 3 * tpComplexity(tp)
                  end
                  
                  DAE.MUL_MATRIX_PRODUCT(ty = tp)  => begin
                    complexityAlloc + 3 * tpComplexity(tp)
                  end
                  
                  DAE.DIV_ARRAY_SCALAR(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(ty = tp)  => begin
                    complexityAlloc + tpComplexity(tp)
                  end
                  
                  DAE.POW_ARRAY_SCALAR(ty = tp)  => begin
                    complexityAlloc + 30 * tpComplexity(tp)
                  end
                  
                  DAE.POW_SCALAR_ARRAY(ty = tp)  => begin
                    complexityAlloc + 30 * tpComplexity(tp)
                  end
                  
                  DAE.POW_ARR(ty = tp)  => begin
                    complexityAlloc + 30 * tpComplexity(tp)
                  end
                  
                  DAE.POW_ARR2(ty = tp)  => begin
                    complexityAlloc + 30 * tpComplexity(tp)
                  end
                  
                  DAE.AND(__)  => begin
                    1
                  end
                  
                  DAE.OR(__)  => begin
                    1
                  end
                  
                  DAE.NOT(__)  => begin
                    1
                  end
                  
                  DAE.LESS(__)  => begin
                    1
                  end
                  
                  DAE.LESSEQ(__)  => begin
                    1
                  end
                  
                  DAE.GREATER(__)  => begin
                    1
                  end
                  
                  DAE.GREATEREQ(__)  => begin
                    1
                  end
                  
                  DAE.EQUAL(__)  => begin
                    1
                  end
                  
                  DAE.NEQUAL(__)  => begin
                    1
                  end
                  
                  DAE.USERDEFINED(__)  => begin
                    100
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Expression.opWCET failed"))
                      fail()
                  end
                end
              end
               #= /* TODO: Array dims? */ =#
               #= /* TODO: Array ops? */ =#
          i
        end

         #= Construct a list of enumeration literal expression given the type name of an
           enumeration an a list of literal names. =#
        function makeEnumLiterals(inTypeName::Absyn.Path, inLiterals::List{<:String}) ::List{DAE.Exp} 
              local outLiterals::List{DAE.Exp}

              local enum_lit_names::List{Absyn.Path}
              local enum_lit_expl::List{DAE.Exp}

              enum_lit_names = ListUtil.map1r(inLiterals, AbsynUtil.suffixPath, inTypeName)
              (outLiterals, _) = ListUtil.mapFold(enum_lit_names, makeEnumLiteral, 1)
          outLiterals
        end

         #= Creates a new enumeration literal. For use with listMapAndFold. =#
        function makeEnumLiteral(name::Absyn.Path, index::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local newIndex::ModelicaInteger
              local enumExp::DAE.Exp

              enumExp = DAE.ENUM_LITERAL(name, index)
              newIndex = index + 1
          (enumExp, newIndex)
        end

         #= Determines whether an operand in an expression needs parentheses around it. =#
        function shouldParenthesize(inOperand::DAE.Exp, inOperator::DAE.Exp, inLhs::Bool) ::Bool 
              local outShouldParenthesize::Bool

              outShouldParenthesize = begin
                  local diff::ModelicaInteger
                @match (inOperand, inOperator, inLhs) begin
                  (DAE.UNARY(__), _, _)  => begin
                    true
                  end
                  
                  _  => begin
                        diff = Util.intCompare(priority(inOperand, inLhs), priority(inOperator, inLhs))
                      shouldParenthesize2(diff, inOperand, inLhs)
                  end
                end
              end
          outShouldParenthesize
        end

        function shouldParenthesize2(inPrioDiff::ModelicaInteger, inOperand::DAE.Exp, inLhs::Bool) ::Bool 
              local outShouldParenthesize::Bool

              outShouldParenthesize = begin
                @match (inPrioDiff, inOperand, inLhs) begin
                  (1, _, _)  => begin
                    true
                  end
                  
                  (0, _, false)  => begin
                    ! isAssociativeExp(inOperand)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outShouldParenthesize
        end

         #= Determines whether the given expression represents an associative operation or not. =#
        function isAssociativeExp(inExp::DAE.Exp) ::Bool 
              local outIsAssociative::Bool

              outIsAssociative = begin
                  local op::DAE.Operator
                @match inExp begin
                  DAE.BINARY(operator = op)  => begin
                    isAssociativeOp(op)
                  end
                  
                  DAE.LBINARY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsAssociative
        end

         #= Determines whether the given operator is associative or not. =#
        function isAssociativeOp(inOperator::DAE.Operator) ::Bool 
              local outIsAssociative::Bool

              outIsAssociative = begin
                @match inOperator begin
                  DAE.ADD(__)  => begin
                    true
                  end
                  
                  DAE.MUL(__)  => begin
                    true
                  end
                  
                  DAE.ADD_ARR(__)  => begin
                    true
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    true
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsAssociative
        end

         #= Returns an integer priority given an expression, which is used by
           ExpressionDumpTpl to add parentheses when dumping expressions. The inLhs
           argument should be true if the expression occurs on the left side of a binary
           operation, otherwise false. This is because we don't need to add parentheses
           to expressions such as x * y / z, but x / (y * z) needs them, so the
           priorities of some binary operations differ depending on which side they are. =#
        function priority(inExp::DAE.Exp, inLhs::Bool) ::ModelicaInteger 
              local outPriority::ModelicaInteger

              outPriority = begin
                  local op::DAE.Operator
                @match (inExp, inLhs) begin
                  (DAE.BINARY(operator = op), false)  => begin
                    priorityBinopRhs(op)
                  end
                  
                  (DAE.BINARY(operator = op), true)  => begin
                    priorityBinopLhs(op)
                  end
                  
                  (DAE.RCONST(__), _) where (inExp.real < 0.0)  => begin
                    4
                  end
                  
                  (DAE.UNARY(__), _)  => begin
                    4
                  end
                  
                  (DAE.LBINARY(operator = op), _)  => begin
                    priorityLBinop(op)
                  end
                  
                  (DAE.LUNARY(__), _)  => begin
                    7
                  end
                  
                  (DAE.RELATION(__), _)  => begin
                    6
                  end
                  
                  (DAE.RANGE(__), _)  => begin
                    10
                  end
                  
                  (DAE.IFEXP(__), _)  => begin
                    11
                  end
                  
                  _  => begin
                      0
                  end
                end
              end
               #=  Same as unary minus of a real literal
               =#
          outPriority
        end

         #= Returns the priority for a binary operation on the left hand side. Add and
           sub has the same priority, and mul and div too, in contrast with
           priorityBinopRhs. =#
        function priorityBinopLhs(inOp::DAE.Operator) ::ModelicaInteger 
              local outPriority::ModelicaInteger

              outPriority = begin
                @match inOp begin
                  DAE.ADD(__)  => begin
                    5
                  end
                  
                  DAE.SUB(__)  => begin
                    5
                  end
                  
                  DAE.MUL(__)  => begin
                    2
                  end
                  
                  DAE.DIV(__)  => begin
                    2
                  end
                  
                  DAE.POW(__)  => begin
                    1
                  end
                  
                  DAE.ADD_ARR(__)  => begin
                    5
                  end
                  
                  DAE.SUB_ARR(__)  => begin
                    5
                  end
                  
                  DAE.MUL_ARR(__)  => begin
                    2
                  end
                  
                  DAE.DIV_ARR(__)  => begin
                    2
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    2
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    5
                  end
                  
                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    5
                  end
                  
                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    2
                  end
                  
                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    2
                  end
                  
                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    2
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    2
                  end
                  
                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    1
                  end
                  
                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    1
                  end
                  
                  DAE.POW_ARR(__)  => begin
                    1
                  end
                  
                  DAE.POW_ARR2(__)  => begin
                    1
                  end
                end
              end
          outPriority
        end

         #= Returns the priority for a binary operation on the right hand side. Add and
           sub has different priorities, and mul and div too, in contrast with
           priorityBinopLhs. =#
        function priorityBinopRhs(inOp::DAE.Operator) ::ModelicaInteger 
              local outPriority::ModelicaInteger

              outPriority = begin
                @match inOp begin
                  DAE.ADD(__)  => begin
                    6
                  end
                  
                  DAE.SUB(__)  => begin
                    5
                  end
                  
                  DAE.MUL(__)  => begin
                    3
                  end
                  
                  DAE.DIV(__)  => begin
                    2
                  end
                  
                  DAE.POW(__)  => begin
                    1
                  end
                  
                  DAE.ADD_ARR(__)  => begin
                    6
                  end
                  
                  DAE.SUB_ARR(__)  => begin
                    5
                  end
                  
                  DAE.MUL_ARR(__)  => begin
                    3
                  end
                  
                  DAE.DIV_ARR(__)  => begin
                    2
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    3
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    6
                  end
                  
                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    5
                  end
                  
                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    3
                  end
                  
                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    3
                  end
                  
                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    2
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    2
                  end
                  
                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    1
                  end
                  
                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    1
                  end
                  
                  DAE.POW_ARR(__)  => begin
                    1
                  end
                  
                  DAE.POW_ARR2(__)  => begin
                    1
                  end
                end
              end
          outPriority
        end

        function priorityLBinop(inOp::DAE.Operator) ::ModelicaInteger 
              local outPriority::ModelicaInteger

              outPriority = begin
                @match inOp begin
                  DAE.AND(__)  => begin
                    8
                  end
                  
                  DAE.OR(__)  => begin
                    9
                  end
                end
              end
          outPriority
        end

        function isWild(exp::DAE.Exp) ::Bool 
              local b::Bool

              b = begin
                @match exp begin
                  DAE.CREF(componentRef = DAE.WILD(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isNotWild(exp::DAE.Exp) ::Bool 
              local b::Bool

              b = begin
                @match exp begin
                  DAE.CREF(componentRef = DAE.WILD(__))  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          b
        end

         #= Takes a list of dimensions and select the expressions dimensions, returning a list of expressions =#
        function dimensionsToExps(dims::List{<:DAE.Dimension}) ::List{DAE.Exp} 
              local exps::List{DAE.Exp} = nil

              for d in dims
                exps = begin
                    local exp::DAE.Exp
                  @match d begin
                    DAE.DIM_EXP(exp)  => begin
                      _cons(exp, exps)
                    end
                    
                    _  => begin
                        exps
                    end
                  end
                end
              end
              exps = listReverse(exps)
          exps
        end

         #= Splits a record into its elements. Works for crefs, records constructor calls, and casts of the same =#
        function splitRecord(inExp::DAE.Exp, ty::DAE.Type) ::List{DAE.Exp} 
              local outExps::List{DAE.Exp}

              outExps = begin
                  local exp::DAE.Exp
                  local vs::List{DAE.Var}
                  local cr::DAE.ComponentRef
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local exps::List{DAE.Exp}
                @match (inExp, ty) begin
                  (DAE.CAST(exp = exp), _)  => begin
                    splitRecord(exp, ty)
                  end
                  
                  (DAE.CREF(__), DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(__), varLst =  nil()))  => begin
                    fail()
                  end
                  
                  (DAE.CREF(componentRef = cr), DAE.T_COMPLEX(varLst = vs))  => begin
                    ListUtil.map1(vs, splitRecord2, cr)
                  end
                  
                  (DAE.CALL(path = p1, expLst = exps, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p2)))), _)  => begin
                      @match true = AbsynUtil.pathEqual(p1, p2) #= is record constructor =#
                    exps
                  end
                  
                  (DAE.RECORD(exps = exps), _)  => begin
                    exps
                  end
                end
              end
               #= Don't split External objects
               =#
          outExps
        end

        function splitRecord2(var::DAE.Var, cr::DAE.ComponentRef) ::DAE.Exp 
              local exp::DAE.Exp

              local n::String
              local tt::DAE.Type
              local ty::DAE.Type

              @match DAE.TYPES_VAR(name = n, ty = tt) = var
              ty = Types.simplifyType(tt)
              exp = makeCrefExp(ComponentReference.crefPrependIdent(cr, n, nil, ty), ty)
          exp
        end

         #= Splits an array into a list of elements. =#
        function splitArray(inExp::DAE.Exp) ::Tuple{List{DAE.Exp}, Bool} 
              local didSplit::Bool
              local outExp::List{DAE.Exp}

              (outExp, didSplit) = begin
                  local expl::List{DAE.Exp}
                  local mat::List{List{DAE.Exp}}
                  local istart::ModelicaInteger
                  local istop::ModelicaInteger
                  local istep::ModelicaInteger
                  local step::Option{DAE.Exp}
                @match inExp begin
                  DAE.ARRAY(array = expl)  => begin
                    (expl, true)
                  end
                  
                  DAE.MATRIX(matrix = mat)  => begin
                    (ListUtil.flatten(mat), true)
                  end
                  
                  DAE.RANGE(DAE.T_INTEGER(__), DAE.ICONST(istart), step, DAE.ICONST(istop))  => begin
                    (list(DAE.ICONST(i) for i in ExpressionSimplify.simplifyRange(istart, begin
                       @match step begin
                         NONE()  => begin
                           1
                         end
                         
                         SOME(DAE.ICONST(istep))  => begin
                           istep
                         end
                       end
                     end, istop)), true)
                  end
                  
                  _  => begin
                      (list(inExp), false)
                  end
                end
              end
          (outExp, didSplit)
        end

        function equationExpEqual(exp1::DAE.EquationExp, exp2::DAE.EquationExp) ::Bool 
              local b::Bool

              b = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                @match (exp1, exp2) begin
                  (DAE.PARTIAL_EQUATION(e1), DAE.PARTIAL_EQUATION(e2))  => begin
                    expEqual(e1, e2)
                  end
                  
                  (DAE.RESIDUAL_EXP(e1), DAE.RESIDUAL_EXP(e2))  => begin
                    expEqual(e1, e2)
                  end
                  
                  (DAE.EQUALITY_EXPS(e1, e2), DAE.EQUALITY_EXPS(e3, e4))  => begin
                    expEqual(e1, e3) && expEqual(e2, e4)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= This function corresponds to the promote function described in the Modelica
           spec. It takes an expression, the type of the expression and a number of
           dimensions, and adds dimensions of size 1 to the right of the expression
           until the expression has as many dimensions as given. It also returns the
           type of the promoted expression. E.g.:

             promoteExp({1, 2, 3}, Integer[3], 3) =>
                ({{{1}}, {{2}}, {{3}}}, Integer[3,1,1])

           The reason why this function takes a type instead of using the type of the
           expression is because it's used by Static.promoteExp, which already knows the
           type. =#
        function promoteExp(inExp::DAE.Exp, inType::DAE.Type, inDims::ModelicaInteger) ::Tuple{DAE.Exp, DAE.Type} 
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType) = begin
                  local dims_to_add::ModelicaInteger
                  local ty::DAE.Type
                  local res_ty::DAE.Type
                  local exp::DAE.Exp
                  local tys::List{DAE.Type}
                  local dims::List{DAE.Dimension}
                  local added_dims::List{DAE.Dimension}
                  local is_array_ty::Bool
                @matchcontinue (inExp, inType, inDims) begin
                  (_, _, _)  => begin
                      dims_to_add = inDims - Types.numberOfDimensions(inType)
                      @match true = dims_to_add > 0
                      added_dims = ListUtil.fill(DAE.DIM_INTEGER(1), dims_to_add)
                      dims = listAppend(Types.getDimensions(inType), added_dims)
                      ty = Types.arrayElementType(inType)
                      res_ty = Types.liftArrayListDims(ty, dims)
                      ty = Types.simplifyType(ty)
                      tys = makePromotedTypes(dims, ty, nil)
                      is_array_ty = Types.isArray(inType)
                      exp = promoteExp2(inExp, is_array_ty, inDims, tys)
                    (exp, res_ty)
                  end
                  
                  _  => begin
                      (inExp, inType)
                  end
                end
              end
               #=  Figure out how many dimensions we need to add.
               =#
               #=  If the expression already has at least as many dimensions as we want,
               =#
               #=  fail and return the unchanged expression.
               =#
               #=  Construct all the types we will need here, to avoid having to
               =#
               #=  construct new types for all the subexpressions created.
               =#
               #=  Add as many dimensions of size 1 as needed.
               =#
               #=  Append the dimensions from the type and the added dimensions.
               =#
               #=  Construct the result type.
               =#
               #=  Construct the expression types.
               =#
               #=  Use the constructed types to promote the expression.
               =#
          (outExp, outType)
        end

         #= Creates a lift of types given a list of dimensions and an element type. The
           types are created by removing the head of the dimension list one by one and
           creating types from the remaining dimensions. E.g.:

             makePromotedTypes({[2], [3], [1]}, Real) =>
                {Real[2,3,1], Real[3,1], Real[1]}
            =#
        function makePromotedTypes(inDimensions::List{<:DAE.Dimension}, inElementType::DAE.Type, inAccumTypes::List{<:DAE.Type}) ::List{DAE.Type} 
              local outAccumTypes::List{DAE.Type}

              outAccumTypes = begin
                  local rest_dims::List{DAE.Dimension}
                  local ty::DAE.Type
                @match (inDimensions, inElementType, inAccumTypes) begin
                  (_ <| rest_dims, _, _)  => begin
                      ty = DAE.T_ARRAY(inElementType, inDimensions)
                    makePromotedTypes(rest_dims, inElementType, _cons(ty, inAccumTypes))
                  end
                  
                  ( nil(), _, _)  => begin
                    listReverse(inAccumTypes)
                  end
                end
              end
          outAccumTypes
        end

         #= Helper function to promoteExp. =#
        function promoteExp2(inExp::DAE.Exp, inIsArray::Bool, inDims::ModelicaInteger, inTypes::List{<:DAE.Type}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local ty::DAE.Type
                  local expl::List{DAE.Exp}
                  local rest_ty::List{DAE.Type}
                   #=  No types left, we're done!
                   =#
                @match (inExp, inIsArray, inDims, inTypes) begin
                  (_, _, _,  nil())  => begin
                    inExp
                  end
                  
                  (DAE.ARRAY(_, _, expl), _, _, ty <| rest_ty)  => begin
                      expl = ListUtil.map3(expl, promoteExp2, false, inDims, rest_ty)
                    DAE.ARRAY(ty, false, expl)
                  end
                  
                  (_, true, _, ty <| _)  => begin
                    makePureBuiltinCall("promote", list(inExp, DAE.ICONST(inDims)), ty)
                  end
                  
                  _  => begin
                      promoteExp3(inExp, inTypes)
                  end
                end
              end
               #=  An array, promote each element in the array.
               =#
               #=  An expression with array type, but which is not an array expression. Such
               =#
               #=  an expression can't be promoted here, so we create a promote call instead.
               =#
               #=  Any other expression, call promoteExp3.
               =#
          outExp
        end

         #= Helper function to promoteExp2. Promotes a scalar expression as many times as
           the number of types given. =#
        function promoteExp3(inExp::DAE.Exp, inTypes::List{<:DAE.Type}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local ty::DAE.Type
                  local rest_ty::List{DAE.Type}
                  local exp::DAE.Exp
                   #=  No types left, were' done!
                   =#
                @match (inExp, inTypes) begin
                  (_,  nil())  => begin
                    inExp
                  end
                  
                  (_, ty <|  nil())  => begin
                    makeArray(list(inExp), ty, true)
                  end
                  
                  (_, ty <| rest_ty)  => begin
                      exp = promoteExp3(inExp, rest_ty)
                    makeArray(list(exp), ty, false)
                  end
                end
              end
               #=  Only one type left, create a scalar array with it.
               =#
               #=  Several types left. Promote the expression using the rest of the types,
               =#
               #=  and then create an non-scalar array of the expression with the first type.
               =#
          outExp
        end

         #= 
        author: PA
        hash expression to value in range [0,mod-1] =#
        function hashExpMod(e::DAE.Exp, mod::ModelicaInteger) ::ModelicaInteger 
              local hash::ModelicaInteger

              hash = intMod(intAbs(hashExp(e)), mod)
          hash
        end

         #= help function to hashExpMod =#
        function hashExp(e::DAE.Exp) ::ModelicaInteger 
              local hash::ModelicaInteger

              hash = begin
                  local r::ModelicaReal
                  local i::ModelicaInteger
                  local b::Bool
                  local s::String
                  local path::Absyn.Path
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local op::DAE.Operator
                  local expl::List{DAE.Exp}
                  local mexpl::List{List{DAE.Exp}}
                  local cr::DAE.ComponentRef
                  local iters::DAE.ReductionIterators
                  local info::DAE.ReductionInfo
                @matchcontinue e begin
                  DAE.ICONST(i)  => begin
                    stringHashDjb2(intString(i))
                  end
                  
                  DAE.RCONST(r)  => begin
                    stringHashDjb2(realString(r))
                  end
                  
                  DAE.BCONST(b)  => begin
                    stringHashDjb2(boolString(b))
                  end
                  
                  DAE.SCONST(s)  => begin
                    stringHashDjb2(s)
                  end
                  
                  DAE.ENUM_LITERAL(name = path)  => begin
                    stringHashDjb2(AbsynUtil.pathString(path))
                  end
                  
                  DAE.CREF(componentRef = cr)  => begin
                    ComponentReference.hashComponentRef(cr)
                  end
                  
                  DAE.BINARY(e1, op, e2)  => begin
                    1 + hashExp(e1) + hashOp(op) + hashExp(e2)
                  end
                  
                  DAE.UNARY(op, e1)  => begin
                    2 + hashOp(op) + hashExp(e1)
                  end
                  
                  DAE.LBINARY(e1, op, e2)  => begin
                    3 + hashExp(e1) + hashOp(op) + hashExp(e2)
                  end
                  
                  DAE.LUNARY(op, e1)  => begin
                    4 + hashOp(op) + hashExp(e1)
                  end
                  
                  DAE.RELATION(e1, op, e2, _, _)  => begin
                    5 + hashExp(e1) + hashOp(op) + hashExp(e2)
                  end
                  
                  DAE.IFEXP(e1, e2, e3)  => begin
                    6 + hashExp(e1) + hashExp(e2) + hashExp(e3)
                  end
                  
                  DAE.CALL(path = path, expLst = expl)  => begin
                    7 + stringHashDjb2(AbsynUtil.pathString(path)) + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.RECORD(path = path, exps = expl)  => begin
                    8 + stringHashDjb2(AbsynUtil.pathString(path)) + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.PARTEVALFUNCTION(path = path, expList = expl)  => begin
                    9 + stringHashDjb2(AbsynUtil.pathString(path)) + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.ARRAY(array = expl)  => begin
                    10 + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.MATRIX(matrix = mexpl)  => begin
                    11 + ListUtil.reduce(ListUtil.map(ListUtil.flatten(mexpl), hashExp), intAdd)
                  end
                  
                  DAE.RANGE(_, e1, SOME(e2), e3)  => begin
                    12 + hashExp(e1) + hashExp(e2) + hashExp(e3)
                  end
                  
                  DAE.RANGE(_, e1, NONE(), e3)  => begin
                    13 + hashExp(e1) + hashExp(e3)
                  end
                  
                  DAE.TUPLE(expl)  => begin
                    14 + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.CAST(_, e1)  => begin
                    15 + hashExp(e1)
                  end
                  
                  DAE.ASUB(e1, expl)  => begin
                    16 + hashExp(e1) + ListUtil.reduce(ListUtil.map(expl, hashExp), intAdd)
                  end
                  
                  DAE.TSUB(e1, i, _)  => begin
                    17 + hashExp(e1) + stringHashDjb2(intString(i))
                  end
                  
                  DAE.SIZE(e1, SOME(e2))  => begin
                    18 + hashExp(e1) + hashExp(e2)
                  end
                  
                  DAE.SIZE(e1, NONE())  => begin
                    19 + hashExp(e1)
                  end
                  
                  DAE.REDUCTION(info, e1, iters)  => begin
                    22 + hashReductionInfo(info) + hashExp(e1) + ListUtil.reduce(ListUtil.map(iters, hashReductionIter), intAdd)
                  end
                  
                  _  => begin
                      stringHashDjb2(ExpressionDump.printExpStr(e))
                  end
                end
              end
               #=  case(DAE.CODE(_,_))                             then 20;  TODO: implement hashing of CODE AST
               =#
               #=  case(DAE.EMPTY(scope=_))                        then 21;  TODO: implement hashing of EMTPY (needed ?)
               =#
               #=  TODO: hashing of all MetaModelica extensions
               =#
          hash
        end

         #= help function to hashExp =#
        function hashReductionInfo(info::DAE.ReductionInfo) ::ModelicaInteger 
              local hash::ModelicaInteger

              hash = begin
                  local path::Absyn.Path
                   #=  TODO: complete hasing of all subexpressions
                   =#
                @match info begin
                  DAE.REDUCTIONINFO(path = path)  => begin
                    22 + stringHashDjb2(AbsynUtil.pathString(path))
                  end
                end
              end
          hash
        end

         #= help function to hashExp =#
        function hashReductionIter(iter::DAE.ReductionIterator) ::ModelicaInteger 
              local hash::ModelicaInteger

              hash = begin
                  local id::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                @match iter begin
                  DAE.REDUCTIONITER(id, e1, SOME(e2), _)  => begin
                    23 + stringHashDjb2(id) + hashExp(e1) + hashExp(e2)
                  end
                  
                  DAE.REDUCTIONITER(id, e1, NONE(), _)  => begin
                    24 + stringHashDjb2(id) + hashExp(e1)
                  end
                end
              end
          hash
        end

         #= help function to hashExp =#
        function hashOp(op::DAE.Operator) ::ModelicaInteger 
              local hash::ModelicaInteger

              hash = begin
                  local path::Absyn.Path
                @match op begin
                  DAE.ADD(_)  => begin
                    25
                  end
                  
                  DAE.SUB(_)  => begin
                    26
                  end
                  
                  DAE.MUL(_)  => begin
                    27
                  end
                  
                  DAE.DIV(_)  => begin
                    28
                  end
                  
                  DAE.POW(_)  => begin
                    29
                  end
                  
                  DAE.UMINUS(_)  => begin
                    30
                  end
                  
                  DAE.UMINUS_ARR(_)  => begin
                    31
                  end
                  
                  DAE.ADD_ARR(_)  => begin
                    32
                  end
                  
                  DAE.SUB_ARR(_)  => begin
                    33
                  end
                  
                  DAE.MUL_ARR(_)  => begin
                    34
                  end
                  
                  DAE.DIV_ARR(_)  => begin
                    35
                  end
                  
                  DAE.MUL_ARRAY_SCALAR(_)  => begin
                    36
                  end
                  
                  DAE.ADD_ARRAY_SCALAR(_)  => begin
                    37
                  end
                  
                  DAE.SUB_SCALAR_ARRAY(_)  => begin
                    38
                  end
                  
                  DAE.MUL_SCALAR_PRODUCT(_)  => begin
                    39
                  end
                  
                  DAE.MUL_MATRIX_PRODUCT(_)  => begin
                    40
                  end
                  
                  DAE.DIV_ARRAY_SCALAR(_)  => begin
                    41
                  end
                  
                  DAE.DIV_SCALAR_ARRAY(_)  => begin
                    42
                  end
                  
                  DAE.POW_ARRAY_SCALAR(_)  => begin
                    43
                  end
                  
                  DAE.POW_SCALAR_ARRAY(_)  => begin
                    44
                  end
                  
                  DAE.POW_ARR(_)  => begin
                    45
                  end
                  
                  DAE.POW_ARR2(_)  => begin
                    46
                  end
                  
                  DAE.AND(_)  => begin
                    47
                  end
                  
                  DAE.OR(_)  => begin
                    48
                  end
                  
                  DAE.NOT(_)  => begin
                    49
                  end
                  
                  DAE.LESS(_)  => begin
                    50
                  end
                  
                  DAE.LESSEQ(_)  => begin
                    51
                  end
                  
                  DAE.GREATER(_)  => begin
                    52
                  end
                  
                  DAE.GREATEREQ(_)  => begin
                    53
                  end
                  
                  DAE.EQUAL(_)  => begin
                    54
                  end
                  
                  DAE.NEQUAL(_)  => begin
                    55
                  end
                  
                  DAE.USERDEFINED(path)  => begin
                    56 + stringHashDjb2(AbsynUtil.pathString(path))
                  end
                end
              end
          hash
        end

        function matrixToArray(inMatrix::DAE.Exp) ::DAE.Exp 
              local outArray::DAE.Exp

              outArray = begin
                  local ty::DAE.Type
                  local row_ty::DAE.Type
                  local matrix::List{List{Exp}}
                  local rows::List{DAE.Exp}
                @match inMatrix begin
                  DAE.MATRIX(ty = ty, matrix = matrix)  => begin
                      row_ty = unliftArray(ty)
                      rows = ListUtil.map2(matrix, makeArray, row_ty, true)
                    DAE.ARRAY(ty, false, rows)
                  end
                  
                  _  => begin
                      inMatrix
                  end
                end
              end
          outArray
        end

        function transposeArray(inArray::DAE.Exp) ::Tuple{DAE.Exp, Bool} 
              local outWasTransposed::Bool
              local outArray::DAE.Exp

              (outArray, outWasTransposed) = begin
                  local ty::DAE.Type
                  local row_ty::DAE.Type
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local rest_dims::DAE.Dimensions
                  local expl::List{Exp}
                  local matrix::List{List{Exp}}
                  local i::ModelicaInteger
                   #=  Empty array, just transpose the type.
                   =#
                @match inArray begin
                  DAE.ARRAY(DAE.T_ARRAY(ty, dim1 <| dim2 <| rest_dims), _,  nil())  => begin
                    (DAE.ARRAY(DAE.T_ARRAY(ty, _cons(dim2, _cons(dim1, rest_dims))), false, nil), true)
                  end
                  
                  DAE.ARRAY(DAE.T_ARRAY(ty, dim1 <| dim2 <| rest_dims), _, expl)  => begin
                      row_ty = DAE.T_ARRAY(ty, _cons(dim1, rest_dims))
                      matrix = ListUtil.map(expl, getArrayOrMatrixContents)
                      matrix = ListUtil.transposeList(matrix)
                      expl = ListUtil.map2(matrix, makeArray, row_ty, true)
                    (DAE.ARRAY(DAE.T_ARRAY(ty, _cons(dim2, _cons(dim1, rest_dims))), false, expl), true)
                  end
                  
                  DAE.MATRIX(matrix = matrix, ty = DAE.T_ARRAY(ty, dim1 <| dim2 <|  nil()))  => begin
                      matrix = ListUtil.transposeList(matrix)
                      ty = DAE.T_ARRAY(ty, list(dim2, dim1))
                      i = listLength(matrix)
                    (DAE.MATRIX(ty, i, matrix), true)
                  end
                  
                  _  => begin
                      (inArray, false)
                  end
                end
              end
          (outArray, outWasTransposed)
        end

         #= Get the cref from an expression that might be ASUB. If so, return the base CREF (this function does *not* always return a CREF with the same type as the full expression). =#
        function getCrefFromCrefOrAsub(exp::DAE.Exp) ::DAE.ComponentRef 
              local cr::DAE.ComponentRef

              cr = begin
                @match exp begin
                  DAE.CREF(componentRef = cr)  => begin
                    cr
                  end
                  
                  DAE.ASUB(exp = DAE.CREF(componentRef = cr))  => begin
                    cr
                  end
                end
              end
          cr
        end

         #= Returns the array elements of an expression. =#
        function arrayElements(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outExp::List{DAE.Exp}

              outExp = begin
                  local expl::List{DAE.Exp}
                  local cr::DAE.ComponentRef
                  local crl::List{DAE.ComponentRef}
                  local mat::List{List{DAE.Exp}}
                @match inExp begin
                  DAE.CREF(componentRef = cr)  => begin
                      crl = ComponentReference.expandCref(cr, false)
                      expl = ListUtil.map(crl, crefExp)
                    expl
                  end
                  
                  DAE.ARRAY(array = expl, ty = DAE.T_ARRAY(__))  => begin
                    ListUtil.mapFlat(expl, arrayElements)
                  end
                  
                  DAE.ARRAY(array = expl)  => begin
                    expl
                  end
                  
                  DAE.MATRIX(matrix = mat)  => begin
                    ListUtil.flatten(mat)
                  end
                  
                  _  => begin
                      list(inExp)
                  end
                end
              end
          outExp
        end

         #= Returns the contents of an array expression, i.e. a list of expressions. =#
        function arrayContent(inExp::DAE.Exp) ::List{DAE.Exp} 
              local outContent::List{DAE.Exp}

              @match DAE.ARRAY(array = outContent) = inExp
          outContent
        end

         #= @author: adrpo
         transform Absyn.Exp into DAE.Exp, unknown types are used =#
        function fromAbsynExp(inAExp::Absyn.Exp) ::DAE.Exp 
              local outDExp::DAE.Exp

              outDExp = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local b::Bool
                  local s::String
                  local ae::Absyn.Exp
                  local ae1::Absyn.Exp
                  local ae2::Absyn.Exp
                  local cond::Absyn.Exp
                  local aop::Absyn.Operator
                  local acr::Absyn.ComponentRef
                  local aexps::List{Absyn.Exp}
                  local aexpslst::List{List{Absyn.Exp}}
                  local fargs::Absyn.FunctionArgs
                  local p::Absyn.Path
                  local aoe::Option{Absyn.Exp}
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local op::DAE.Operator
                  local exps::List{DAE.Exp}
                  local expslst::List{List{DAE.Exp}}
                  local oe::Option{DAE.Exp}
                @match inAExp begin
                  Absyn.INTEGER(i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  Absyn.REAL(s)  => begin
                      r = System.stringReal(s)
                    DAE.RCONST(r)
                  end
                  
                  Absyn.BOOL(b)  => begin
                    DAE.BCONST(b)
                  end
                  
                  Absyn.STRING(s)  => begin
                    DAE.SCONST(s)
                  end
                  
                  Absyn.CREF(acr)  => begin
                      cr = ComponentReference.toExpCref(acr)
                      e = makeCrefExp(cr, DAE.T_UNKNOWN_DEFAULT)
                    e
                  end
                  
                  Absyn.BINARY(ae1, aop, ae2)  => begin
                      op = fromAbsynOperator(aop, DAE.T_UNKNOWN_DEFAULT)
                      e1 = fromAbsynExp(ae1)
                      e2 = fromAbsynExp(ae2)
                      e = DAE.BINARY(e1, op, e2)
                    e
                  end
                  
                  Absyn.UNARY(aop, ae)  => begin
                      op = fromAbsynOperator(aop, DAE.T_UNKNOWN_DEFAULT)
                      e = fromAbsynExp(ae)
                      e = DAE.UNARY(op, e)
                    e
                  end
                  
                  Absyn.LBINARY(ae1, aop, ae2)  => begin
                      op = fromAbsynOperator(aop, DAE.T_UNKNOWN_DEFAULT)
                      e1 = fromAbsynExp(ae1)
                      e2 = fromAbsynExp(ae2)
                      e = DAE.LBINARY(e1, op, e2)
                    e
                  end
                  
                  Absyn.LUNARY(aop, ae)  => begin
                      op = fromAbsynOperator(aop, DAE.T_UNKNOWN_DEFAULT)
                      e = fromAbsynExp(ae)
                      e = DAE.LUNARY(op, e)
                    e
                  end
                  
                  Absyn.RELATION(ae1, aop, ae2)  => begin
                      op = fromAbsynOperator(aop, DAE.T_UNKNOWN_DEFAULT)
                      e1 = fromAbsynExp(ae1)
                      e2 = fromAbsynExp(ae2)
                      e = DAE.RELATION(e1, op, e2, 0, NONE())
                    e
                  end
                  
                  ae && Absyn.IFEXP(__)  => begin
                      @match Absyn.IFEXP(ifExp = cond, trueBranch = ae1, elseBranch = ae2) = AbsynUtil.canonIfExp(ae)
                      e = fromAbsynExp(cond)
                      e1 = fromAbsynExp(ae1)
                      e2 = fromAbsynExp(ae2)
                      e = DAE.IFEXP(e, e1, e2)
                    e
                  end
                  
                  Absyn.CALL(acr, fargs)  => begin
                      exps = fargsToExps(fargs)
                      p = AbsynUtil.crefToPath(acr)
                      e = DAE.CALL(p, exps, DAE.callAttrBuiltinOther)
                    e
                  end
                  
                  Absyn.PARTEVALFUNCTION(acr, fargs)  => begin
                      exps = fargsToExps(fargs)
                      p = AbsynUtil.crefToPath(acr)
                      e = DAE.PARTEVALFUNCTION(p, exps, DAE.T_UNKNOWN_DEFAULT, DAE.T_UNKNOWN_DEFAULT)
                    e
                  end
                  
                  Absyn.ARRAY(aexps)  => begin
                      exps = ListUtil.map(aexps, fromAbsynExp)
                      e = DAE.ARRAY(DAE.T_UNKNOWN_DEFAULT, false, exps)
                    e
                  end
                  
                  Absyn.MATRIX(aexpslst)  => begin
                      expslst = ListUtil.mapList(aexpslst, fromAbsynExp)
                      i = listLength(listHead(expslst))
                      e = DAE.MATRIX(DAE.T_UNKNOWN_DEFAULT, i, expslst)
                    e
                  end
                  
                  Absyn.RANGE(ae1, aoe, ae2)  => begin
                      e1 = fromAbsynExp(ae1)
                      e2 = fromAbsynExp(ae2)
                      oe = fromAbsynExpOpt(aoe)
                      e = DAE.RANGE(DAE.T_UNKNOWN_DEFAULT, e1, oe, e2)
                    e
                  end
                  
                  Absyn.TUPLE(aexps)  => begin
                      exps = ListUtil.map(aexps, fromAbsynExp)
                      e = DAE.TUPLE(exps)
                    e
                  end
                  
                  _  => begin
                        print("Expression.fromAbsynExp: Unhandled expression: " + Dump.printExpStr(inAExp) + "\\n")
                      fail()
                  end
                end
              end
          outDExp
        end

        function fargsToExps(inFargs::Absyn.FunctionArgs) ::List{DAE.Exp} 
              local outExps::List{DAE.Exp}

              outExps = begin
                  local exps::List{DAE.Exp}
                  local nargs::List{Absyn.NamedArg}
                  local aexps::List{Absyn.Exp}
                @matchcontinue inFargs begin
                  Absyn.FUNCTIONARGS(aexps,  nil())  => begin
                      exps = ListUtil.map(aexps, fromAbsynExp)
                    exps
                  end
                  
                  Absyn.FUNCTIONARGS(_, _)  => begin
                      print("Expression.fargsToExps: Named arguments are not handled!\\n")
                    nil
                  end
                end
              end
          outExps
        end

        function fromAbsynExpOpt(aoe::Option{<:Absyn.Exp}) ::Option{DAE.Exp} 
              local oe::Option{DAE.Exp}

              oe = begin
                  local ae::Absyn.Exp
                  local e::DAE.Exp
                @match aoe begin
                  NONE()  => begin
                    NONE()
                  end
                  
                  SOME(ae)  => begin
                      e = fromAbsynExp(ae)
                    SOME(e)
                  end
                end
              end
          oe
        end

         #= @author: adrpo =#
        function fromAbsynOperator(aop::Absyn.Operator, ty::DAE.Type) ::DAE.Operator 
              local op::DAE.Operator

              op = begin
                @match (aop, ty) begin
                  (Absyn.ADD(__), _)  => begin
                    DAE.ADD(ty)
                  end
                  
                  (Absyn.SUB(__), _)  => begin
                    DAE.SUB(ty)
                  end
                  
                  (Absyn.MUL(__), _)  => begin
                    DAE.MUL(ty)
                  end
                  
                  (Absyn.DIV(__), _)  => begin
                    DAE.DIV(ty)
                  end
                  
                  (Absyn.POW(__), _)  => begin
                    DAE.POW(ty)
                  end
                  
                  (Absyn.UMINUS(__), _)  => begin
                    DAE.UMINUS(ty)
                  end
                  
                  (Absyn.AND(__), _)  => begin
                    DAE.AND(ty)
                  end
                  
                  (Absyn.OR(__), _)  => begin
                    DAE.OR(ty)
                  end
                  
                  (Absyn.NOT(__), _)  => begin
                    DAE.NOT(ty)
                  end
                  
                  (Absyn.LESS(__), _)  => begin
                    DAE.LESS(ty)
                  end
                  
                  (Absyn.LESSEQ(__), _)  => begin
                    DAE.LESSEQ(ty)
                  end
                  
                  (Absyn.GREATER(__), _)  => begin
                    DAE.GREATER(ty)
                  end
                  
                  (Absyn.GREATEREQ(__), _)  => begin
                    DAE.GREATEREQ(ty)
                  end
                  
                  (Absyn.EQUAL(__), _)  => begin
                    DAE.EQUAL(ty)
                  end
                  
                  (Absyn.NEQUAL(__), _)  => begin
                    DAE.NEQUAL(ty)
                  end
                  
                  _  => begin
                        print("Expression.fromAbsynOperator: Unhandled operator: " + Dump.opSymbol(aop) + "\\n")
                      fail()
                  end
                end
              end
          op
        end

         #= Replaces all der(cref) with $DER.cref in an expression. =#
        function replaceDerOpInExp(inExp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              (outExp, _) = traverseExpBottomUp(inExp, replaceDerOpInExpTraverser, NONE())
          outExp
        end

         #= Replaces der(cref) with $DER.cref in an expression, where the cref to replace
          is explicitly given. =#
        function replaceDerOpInExpCond(e::DAE.Exp, cr::Option{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, Option{DAE.ComponentRef}} 
              local outCr::Option{DAE.ComponentRef}
              local outExp::DAE.Exp

              (outExp, outCr) = traverseExpBottomUp(e, replaceDerOpInExpTraverser, cr)
          (outExp, outCr)
        end

         #= Used with Expression.traverseExpBottomUp to traverse an expression an replace calls to
          der(cref) with a component reference $DER.cref. If an optional component
          reference is supplied, then only that component reference is replaced.
          Otherwise all calls to der are replaced.

          This is done since some parts of the compiler can't handle der-calls, such as
          Derive.differentiateExpression. Ideally these parts should be fixed so that they can
          handle der-calls, but until that happens we just replace the der-calls with
          crefs. =#
        function replaceDerOpInExpTraverser(e::DAE.Exp, optCr::Option{<:DAE.ComponentRef}) ::Tuple{DAE.Exp, Option{DAE.ComponentRef}} 
              local outCr::Option{DAE.ComponentRef}
              local outExp::DAE.Exp

              (outExp, outCr) = begin
                  local cr::DAE.ComponentRef
                  local derCr::DAE.ComponentRef
                  local cref_exp::DAE.Exp
                  local cref::DAE.ComponentRef
                @matchcontinue (e, optCr) begin
                  (DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = cr) <|  nil()), SOME(cref))  => begin
                      derCr = ComponentReference.crefPrefixDer(cr)
                      @match true = ComponentReference.crefEqualNoStringCompare(derCr, cref)
                      cref_exp = crefExp(derCr)
                    (cref_exp, optCr)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = cr) <|  nil()), NONE())  => begin
                      cr = ComponentReference.crefPrefixDer(cr)
                      cref_exp = crefExp(cr)
                    (cref_exp, NONE())
                  end
                  
                  _  => begin
                      (e, optCr)
                  end
                end
              end
          (outExp, outCr)
        end

        function makeBinaryExp(inLhs::DAE.Exp, inOp::DAE.Operator, inRhs::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = DAE.BINARY(inLhs, inOp, inRhs)
          outExp
        end

         #= Extracts an integer from an exp =#
        function checkExpDimensionSizes(dim::DAE.Exp) ::Bool 
              local value::Bool

              value = begin
                @match dim begin
                  DAE.ICONST(__)  => begin
                    if dim.integer > 0
                          true
                        else
                          false
                        end
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          value
        end

         #= Extracts an integer from an array dimension. Also handles DIM_EXP and
          DIM_UNKNOWN if checkModel is used. =#
        function checkDimensionSizes(dim::DAE.Dimension) ::Bool 
              local value::Bool

              value = begin
                @match dim begin
                  DAE.DIM_INTEGER(__)  => begin
                    true
                  end
                  
                  DAE.DIM_ENUM(__)  => begin
                    true
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    true
                  end
                  
                  DAE.DIM_EXP(__)  => begin
                    true
                  end
                  
                  DAE.DIM_UNKNOWN(__)  => begin
                    false
                  end
                end
              end
          value
        end

         #= Extracts a list of integers from a list of array dimensions =#
        function dimensionsList(inDims::DAE.Dimensions) ::List{ModelicaInteger} 
              local outValues::List{ModelicaInteger}

              local dims::List{ModelicaInteger}

              outValues = begin
                @matchcontinue inDims begin
                  _  => begin
                      @match true = ListUtil.mapBoolAnd(inDims, checkDimensionSizes)
                      dims = ListUtil.map(inDims, dimensionSizeAll)
                    dims
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outValues
        end

         #= Extracts a list of integers from a list of expressions =#
        function expDimensionsList(inDims::List{<:DAE.Exp}) ::List{ModelicaInteger} 
              local outValues::List{ModelicaInteger}

              local dims::List{ModelicaInteger}

              outValues = begin
                @matchcontinue inDims begin
                  _  => begin
                      @match true = ListUtil.mapBoolAnd(inDims, checkExpDimensionSizes)
                      dims = ListUtil.map(inDims, expInt)
                    dims
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outValues
        end

         #= Checks if all expressions in the given list are crefs with the same identifiers.
            e.g.  {A[1],A[2],…,A[n]} -> true
                  {A[1],B[1]} -> false =#
        function isCrefListWithEqualIdents(iExpressions::List{<:DAE.Exp}) ::Bool 
              local oCrefWithEqualIdents::Bool

              local tmpCrefWithEqualIdents::Bool
              local boolHelperList::List{Bool}
              local crefs::List{DAE.ComponentRef}
              local head::DAE.Exp
              local headCref::DAE.ComponentRef

              oCrefWithEqualIdents = begin
                @matchcontinue iExpressions begin
                  head <| _  => begin
                      @match true = ListUtil.mapBoolAnd(iExpressions, isCref)
                      crefs = ListUtil.map(iExpressions, expCref)
                      headCref = expCref(head)
                      tmpCrefWithEqualIdents = ListUtil.map1BoolAnd(crefs, ComponentReference.crefEqualWithoutLastSubs, headCref)
                    tmpCrefWithEqualIdents
                  end
                  
                   nil()  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #= print(\"isCrefListWithEqualIdents: \\n\" + stringDelimitList(List.map1(iExpressions, ExpressionDump.dumpExpStr, 1), \"\"));
               =#
               #= print(\"isCrefListWithEqualIdents: all crefs!\\n\");
               =#
               #= print(\"isCrefListWithEqualIdents: returns \" + boolString(tmpCrefWithEqualIdents) + \"\\n\\n\");
               =#
               #= print(\"isCrefListWithEqualIdents: returns false\\n\\n\");
               =#
          oCrefWithEqualIdents
        end

         #=  TODO: REPLACE THIS ABOMINATION WITH A BETTER traverseExpBottomUp

          Traverses all subexpressions of an expression.
          Takes a function and an extra argument passed through the traversal.
          The function can potentially change the expression. In such cases,
          the changes are made bottom-up, i.e. a subexpression is traversed
          and changed before the complete expression is traversed.

          NOTE: The user-provided function is not allowed to fail! If you want to
          detect a failure, return NONE() in your user-provided datatype.

          mahge : This function will not treat der(), pre() and start() as calls
          but as unique ids. i.e. x is different from der(x) and given der(x) x will not
          be extreacted as a unique id. Instead you get $DER.x. Same oes for pre and start.
         =#
        function traverseExpDerPreStart(inExp::DAE.Exp, func::FuncExpType, inTypeA::Type_a) ::Tuple{DAE.Exp, Type_a} 
              local outA::Type_a
              local outExp::DAE.Exp

              (outExp, outA) = begin
                  local e1_1::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local ext_arg_1::Type_a
                  local ext_arg_2::Type_a
                  local ext_arg::Type_a
                  local ext_arg_3::Type_a
                  local ext_arg_4::Type_a
                  local op::Operator
                  local rel::FuncExpType
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local fn::Absyn.Path
                  local scalar::Bool
                  local tp::Type
                  local t::Type
                  local i::ModelicaInteger
                  local lstexpl_1::List{List{DAE.Exp}}
                  local lstexpl::List{List{DAE.Exp}}
                  local dim::ModelicaInteger
                  local str::String
                  local localDecls::List{DAE.Element}
                  local res::Tuple{DAE.Exp, Type_a}
                  local fieldNames::List{String}
                  local attr::DAE.CallAttributes
                  local cases::List{DAE.MatchCase}
                  local cases_1::List{DAE.MatchCase}
                  local matchTy::DAE.MatchType
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local riters_1::DAE.ReductionIterators
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local aliases::List{List{String}}
                  local typeVars::List{DAE.Type}
                @match (inExp, func, inTypeA) begin
                  (e && DAE.EMPTY(__), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (e && DAE.ICONST(_), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (e && DAE.RCONST(_), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (e && DAE.SCONST(_), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (e && DAE.BCONST(_), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (e && DAE.ENUM_LITERAL(__), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.CREF(cr, tp), rel, ext_arg)  => begin
                      (cr_1, ext_arg) = traverseExpCref(cr, rel, ext_arg)
                      e = if referenceEq(cr, cr_1)
                            inExp
                          else
                            DAE.CREF(cr_1, tp)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.UNARY(operator = op, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.UNARY(op, e1_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = op, exp2 = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.BINARY(e1_1, op, e2_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.LUNARY(operator = op, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.LUNARY(op, e1_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.LBINARY(e1_1, op, e2_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.RELATION(e1_1, op, e2_1, index_, isExpisASUB)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      (e3_1, ext_arg) = traverseExpDerPreStart(e3, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                            inExp
                          else
                            DAE.IFEXP(e1_1, e2_1, e3_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.CALL(path = fn, expLst = expl, attr = attr), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.CALL(fn, expl_1, attr)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.RECORD(path = fn, exps = expl, comp = fieldNames, ty = tp), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.RECORD(fn, expl_1, fieldNames, tp)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.PARTEVALFUNCTION(fn, expl, tp, t), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.PARTEVALFUNCTION(fn, expl_1, tp, t)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.ARRAY(ty = tp, scalar = scalar, array = expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.ARRAY(tp, scalar, expl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.MATRIX(ty = tp, integer = dim, matrix = lstexpl), rel, ext_arg)  => begin
                      (lstexpl_1, ext_arg) = traverseExpMatrix(lstexpl, rel, ext_arg)
                      e = if referenceEq(lstexpl, lstexpl_1)
                            inExp
                          else
                            DAE.MATRIX(tp, dim, lstexpl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.RANGE(ty = tp, start = e1, step = NONE(), stop = e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.RANGE(tp, e1_1, NONE(), e2_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.RANGE(ty = tp, start = e1, step = SOME(e2), stop = e3), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      (e3_1, ext_arg) = traverseExpDerPreStart(e3, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1) && referenceEq(e3, e3_1)
                            inExp
                          else
                            DAE.RANGE(tp, e1_1, SOME(e2_1), e3_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.TUPLE(PR = expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.TUPLE(expl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.CAST(ty = tp, exp = e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.CAST(tp, e1_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.ASUB(exp = e1, sub = expl), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(expl, expl_1)
                            inExp
                          else
                            makeASUB(e1_1, expl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.TSUB(e1, i, tp), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.TSUB(e1_1, i, tp)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.SIZE(exp = e1, sz = NONE()), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.SIZE(e1_1, NONE())
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.SIZE(exp = e1, sz = SOME(e2)), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.SIZE(e1_1, SOME(e2_1))
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.REDUCTION(reductionInfo = reductionInfo, expr = e1, iterators = riters), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (riters_1, ext_arg) = traverseReductionIterators(riters, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(riters, riters_1)
                            inExp
                          else
                            DAE.REDUCTION(reductionInfo, e1_1, riters_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.CONS(e1, e2), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      (e2_1, ext_arg) = traverseExpDerPreStart(e2, rel, ext_arg)
                      e = if referenceEq(e1, e1_1) && referenceEq(e2, e2_1)
                            inExp
                          else
                            DAE.CONS(e1_1, e2_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.LIST(expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.LIST(expl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.META_TUPLE(expl), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.META_TUPLE(expl_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.META_OPTION(NONE()), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(inExp, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.META_OPTION(SOME(e1)), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.META_OPTION(SOME(e1_1))
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.BOX(e1), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.BOX(e1_1)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.UNBOX(e1, tp), rel, ext_arg)  => begin
                      (e1_1, ext_arg) = traverseExpDerPreStart(e1, rel, ext_arg)
                      e = if referenceEq(e1, e1_1)
                            inExp
                          else
                            DAE.UNBOX(e1_1, tp)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.METARECORDCALL(fn, expl, fieldNames, i, typeVars), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      e = if referenceEq(expl, expl_1)
                            inExp
                          else
                            DAE.METARECORDCALL(fn, expl_1, fieldNames, i, typeVars)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.MATCHEXPRESSION(matchTy, expl, aliases, localDecls, cases, tp), rel, ext_arg)  => begin
                      (expl_1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      (cases_1, ext_arg) = Patternm.traverseCases(cases, rel, ext_arg)
                      e = if referenceEq(expl, expl_1) && referenceEq(cases, cases_1)
                            inExp
                          else
                            DAE.MATCHEXPRESSION(matchTy, expl_1, aliases, localDecls, cases_1, tp)
                          end
                      (e, ext_arg) = rel(e, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.SHARED_LITERAL(__), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(inExp, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.PATTERN(__), rel, ext_arg)  => begin
                      (e, ext_arg) = rel(inExp, ext_arg)
                    (e, ext_arg)
                  end
                  
                  (DAE.CODE(__), _, ext_arg)  => begin
                    (inExp, ext_arg)
                  end
                  
                  _  => begin
                        str = ExpressionDump.printExpStr(inExp)
                        str = "Expression.traverseExpDerPreStart or one of the user-defined functions using it is not implemented correctly: " + str
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  unary
               =#
               #=  binary
               =#
               #=  logical unary
               =#
               #=  logical binary
               =#
               #=  relation
               =#
               #=  if expressions
               =#
               #=  MetaModelica list
               =#
               #=  ---------------------
               =#
               #=  Don't traverse the local declarations; we don't store bindings there (yet)
               =#
               #=  Why don't we call rel() for these expressions?
               =#
          (outExp, outA)
        end

         #=  TODO: REPLACE THIS ABOMINATION WITH A BETTER traverseExpBottomUp

          author mahge: Same as traverseExpList except:
          This function will not treat der(), pre() and start() as calls
          but as unique ids. i.e. x is different from der(x) and given der(x) x will not
          be extreacted as a unique id. Instead you get $DER.x. Same oes for pre and start.. =#
        function traverseExpDerPreStartList(inExpl::List{<:DAE.Exp}, rel::FuncExpType, iext_arg::Type_a) ::Tuple{List{DAE.Exp}, Type_a} 
              local outA::Type_a
              local outExpl::List{DAE.Exp}

              (outExpl, outA) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local expl::List{DAE.Exp}
                  local expl1::List{DAE.Exp}
                  local ext_arg::Type_a
                @match (inExpl, rel, iext_arg) begin
                  ( nil(), _, ext_arg)  => begin
                    (inExpl, ext_arg)
                  end
                  
                  (e <| expl, _, ext_arg)  => begin
                      (e1, ext_arg) = traverseExpDerPreStart(e, rel, ext_arg)
                      (expl1, ext_arg) = traverseExpDerPreStartList(expl, rel, ext_arg)
                      expl = if referenceEq(e, e1) && referenceEq(expl, expl1)
                            inExpl
                          else
                            _cons(e1, expl1)
                          end
                    (expl, ext_arg)
                  end
                end
              end
          (outExpl, outA)
        end

        function renameExpCrefIdent(inExp::DAE.Exp, inTpl::Tuple{<:String, String}) ::Tuple{DAE.Exp, Tuple{String, String}} 
              local outTpl::Tuple{String, String}
              local outExp::DAE.Exp

              (outExp, outTpl) = begin
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local name::String
                  local from::String
                  local to::String
                  local exp::DAE.Exp
                @match (inExp, inTpl) begin
                  (DAE.CREF(DAE.CREF_IDENT(name, ty1,  nil()), ty2), (from, to))  => begin
                      exp = if stringEq(name, from)
                            DAE.CREF(DAE.CREF_IDENT(to, ty1, nil), ty2)
                          else
                            inExp
                          end
                    (exp, inTpl)
                  end
                  
                  _  => begin
                      (inExp, inTpl)
                  end
                end
              end
          (outExp, outTpl)
        end

        function emptyToWild(exp::DAE.Exp) ::DAE.Exp 
              local outExp::DAE.Exp

              local ty::DAE.Type

              ty = typeof(exp)
              outExp = if Types.isZeroLengthArray(ty)
                    DAE.CREF(DAE.WILD(), ty)
                  else
                    exp
                  end
          outExp
        end

        function makeVectorCall(exp::DAE.Exp, tp::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = makePureBuiltinCall("vector", list(exp), tp)
          outExp
        end

        function expandCrefs(exp::DAE.Exp, dummy::ModelicaInteger = 0 #= For traversal =#) ::Tuple{DAE.Exp, ModelicaInteger} 



              exp = begin
                  local ty::DAE.Type
                @match exp begin
                  DAE.CREF(ty = DAE.T_ARRAY(ty = ty))  => begin
                    makeArray(list(makeCrefExp(cr, ty) for cr in ComponentReference.expandCref(exp.componentRef, true)), exp.ty, ! Types.isArray(ty))
                  end
                  
                  _  => begin
                      exp
                  end
                end
              end
          (exp, dummy #= For traversal =#)
        end

         #=  mahge:
           Expands a given expression to a list of expression. this means flattening any records in the
           expression and  vectorizing arrays.

           Currently can only handle crefs and array expressions. Maybe we need to handle binary operations at least.

           Right now this is used in generating simple residual equations from complex ones in SimCode.
          =#
        function expandExpression(inExp::DAE.Exp, expandRecord::Bool) ::List{DAE.Exp} 
              local outExps::List{DAE.Exp}

              outExps = begin
                  local cr::DAE.ComponentRef
                  local crlst::List{DAE.ComponentRef}
                  local expl::List{DAE.Exp} = nil
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local msg::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local op::DAE.Operator
                @match inExp begin
                  DAE.CREF(cr, _)  => begin
                      crlst = ComponentReference.expandCref(cr, expandRecord)
                      outExps = ListUtil.map(crlst, crefToExp)
                    outExps
                  end
                  
                  DAE.UNARY(operator = DAE.UMINUS(__))  => begin
                      expl = list(DAE.UNARY(inExp.operator, exp) for exp in expandExpression(inExp.exp, expandRecord))
                    expl
                  end
                  
                  DAE.BINARY(__)  => begin
                       #=  TODO! FIXME! we should change the type in the operator,
                       =#
                       #=  i.e. use Types.unliftArray on the type inside the operator
                       =#
                      op = inExp.operator
                      expl1 = expandExpression(inExp.exp1, expandRecord)
                      expl2 = expandExpression(inExp.exp2, expandRecord)
                       #=  TODO! FIXME! maybe we should also support (array op scalar)
                       =#
                       #=  make sure the lists have the same length
                       =#
                      if listLength(expl1) != listLength(expl2)
                        fail()
                      end
                      e1 = listGet(expl1, 1)
                      e2 = listGet(expl1, 2)
                      for i in 1:listLength(expl1)
                        e1 = listGet(expl1, i)
                        e2 = listGet(expl2, i)
                        expl = _cons(DAE.BINARY(e1, op, e2), expl)
                      end
                      expl = listReverse(expl)
                    expl
                  end
                  
                  DAE.ARRAY(_, _, expl)  => begin
                      expl = ListUtil.mapFlat(expl, (expandRecord) -> expandExpression(expandRecord = expandRecord))
                    expl
                  end
                  
                  _  => begin
                        msg = "- Expression.expandExpression failed for " + ExpressionDump.printExpStr(inExp)
                        Error.addMessage(Error.INTERNAL_ERROR, list(msg))
                      fail()
                  end
                end
              end
          outExps
        end

         #= author: Frenkel TUD 2010-07
          alternative name: vectorizeExp =#
        function extendArrExp(inExp::DAE.Exp, inExpanded::Bool = false #= True if something was expanded, otherwise false. =#) ::Tuple{DAE.Exp, Bool} 
              local outExpanded::Bool
              local outExp::DAE.Exp

              (outExp, outExpanded) = begin
                  local exp::DAE.Exp
                  local b::Bool
                @matchcontinue (inExp, inExpanded) begin
                  (outExp, _)  => begin
                      (exp, b) = traverseExpBottomUp(inExp, traversingextendArrExp, false)
                    (exp, b)
                  end
                  
                  _  => begin
                      (inExp, inExpanded)
                  end
                end
              end
          (outExp, outExpanded)
        end

         #= author: Frenkel TUD 2010-07.
          This function extend all array and record componentrefs to their
          elements. This is necessary for BLT and substitution of simple
          equations. =#
        function traversingextendArrExp(inExp::DAE.Exp, inExpanded::Bool) ::Tuple{DAE.Exp, Bool} 
              local outExpanded::Bool
              local outExp::DAE.Exp

              (outExp, outExpanded) = begin
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local id::DAE.Dimension
                  local jd::DAE.Dimension
                  local i::ModelicaInteger
                  local j::ModelicaInteger
                  local expl::List{DAE.Exp}
                  local e::DAE.Exp
                  local varLst::List{DAE.Var}
                  local name::Absyn.Path
                  local mat::List{List{DAE.Exp}}
                   #=  CASE for Matrix
                   =#
                @match inExp begin
                  DAE.CREF(ty = ty && DAE.T_ARRAY(dims = id <| jd <|  nil()))  => begin
                      i = dimensionSize(id)
                      j = dimensionSize(jd)
                      expl = expandExpression(inExp, expandRecord = false)
                      mat = makeMatrix(expl, j)
                      e = DAE.MATRIX(ty, i, mat)
                    (e, true)
                  end
                  
                  DAE.CREF(ty = ty && DAE.T_ARRAY(__))  => begin
                      expl = expandExpression(inExp, expandRecord = false)
                      e = DAE.ARRAY(ty, true, expl)
                    (e, true)
                  end
                  
                  DAE.CREF(componentRef = cr, ty = ty && DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD(name)))  => begin
                      expl = ListUtil.map1(varLst, generateCrefsExpFromExpVar, cr)
                      i = listLength(expl)
                      @match true = intGt(i, 0)
                      e = DAE.CALL(name, expl, DAE.CALL_ATTR(ty, false, false, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
                      (e, _) = traverseExpBottomUp(e, traversingextendArrExp, true)
                    (e, true)
                  end
                  
                  _  => begin
                      (inExp, inExpanded)
                  end
                end
              end
               #=  CASE for Array
               =#
               #=  CASE for Records
               =#
          (outExp, outExpanded)
        end

         #= traverses the subscripts of the templSubScript and searches for wholedim. the value replaces the wholedim.
        If there are multiple values, the templSubScript will be used for each of them and multiple new subScriptLsts are created.
        author:Waurich TUD 2014-04 =#
        function insertSubScripts(templSubScript::List{<:DAE.Subscript}, value::List{<:List{<:DAE.Subscript}}, lstIn::List{<:DAE.Subscript}) ::List{List{DAE.Subscript}} 
              local outSubScript::List{List{DAE.Subscript}}

              outSubScript = begin
                  local i::ModelicaInteger
                  local sub::DAE.Subscript
                  local rest::List{DAE.Subscript}
                  local lst::List{DAE.Subscript}
                  local val::List{DAE.Subscript}
                  local lsts::List{List{DAE.Subscript}}
                @matchcontinue (templSubScript, value, lstIn) begin
                  (DAE.WHOLEDIM(__) <| rest, _, _)  => begin
                      lsts = ListUtil.map1(value, listAppend, lstIn)
                      lsts = ListUtil.map1(lsts, ListUtil.append_reverser, rest)
                    lsts
                  end
                  
                  (DAE.INDEX(__) <| rest, _, _)  => begin
                      sub = listHead(templSubScript)
                      lsts = insertSubScripts(rest, value, _cons(sub, lstIn))
                    lsts
                  end
                  
                  _  => begin
                      value
                  end
                end
              end
               #=  found a wholedim, replace with value, insert in lst
               =#
          outSubScript
        end

        function makeMatrix(expl::List{<:DAE.Exp}, n::ModelicaInteger) ::List{List{DAE.Exp}} 
              local res::List{List{DAE.Exp}}

              local col::List{DAE.Exp}
              local r::ModelicaInteger
              listReverse = MetaModelica.Dangerous.listReverseInPlace

              res = nil
              col = nil
              r = n
              for e in expl
                r = r - 1
                col = _cons(e, col)
                if r == 0
                  res = _cons(listReverse(col), res)
                  col = nil
                  r = n
                end
              end
              Error.assertionOrAddSourceMessage(listEmpty(col), Error.INTERNAL_ERROR, list("Expression.makeMatrix failed"), sourceInfo())
              res = listReverse(res)
          res
        end

         #= This function takes a list of subscript ranges representing dimensions, e.g.
            {{1, 2, 3}, {1, 2}} which corresponds to dimensions [3, 2], and generates
            all subscript combinations, e.g. {{1, 1}, {1, 2}, {2, 1}, {2, 2}, {3, 1},
            {3, 2}}. =#
        function rangesToSubscripts(inRangelist::List{<:List{<:DAE.Subscript}}) ::List{List{DAE.Subscript}} 
              local outSubslst::List{List{DAE.Subscript}}

              outSubslst = ListUtil.allCombinations(inRangelist, NONE(), AbsynUtil.dummyInfo)
          outSubslst
        end

         #= Expands a subscript into a list of subscripts. Also takes a dimension to be
           able to evaluate : subscripts. =#
        function expandSubscript(inSubscript::DAE.Subscript, inDimension::DAE.Dimension) ::List{DAE.Subscript} 
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = begin
                  local exp::DAE.Exp
                   #=  An index subscript from range.
                   =#
                @match inSubscript begin
                  DAE.INDEX(exp = DAE.RANGE(__))  => begin
                    list(DAE.INDEX(e) for e in expandRange(inSubscript.exp))
                  end
                  
                  DAE.INDEX(exp = DAE.ARRAY(__))  => begin
                    expandSliceExp(inSubscript.exp)
                  end
                  
                  DAE.INDEX(__)  => begin
                    list(inSubscript)
                  end
                  
                  DAE.WHOLEDIM(__)  => begin
                    expandDimension(inDimension)
                  end
                  
                  DAE.SLICE(__)  => begin
                    expandSliceExp(inSubscript.exp)
                  end
                end
              end
               #=  An index subscript from array.
               =#
               #=  This really shouldn't be happening. But the backend creats things like this.
               =#
               #=  e.g. When finding Incidence Matrix entry for for-loops in Algorithm sections.
               =#
               #=  That whole creating IM should be done the way checkModel works. but it's not. :( so
               =#
               #=  we have this.
               =#
               #=  An index subscript, return it as an array.
               =#
               #=  A : subscript, use the dimension to generate all subscripts.
               =#
               #=  A slice subscript.
               =#
          outSubscripts
        end

         #= Generates a list of subscripts given an array dimension. =#
        function expandDimension(inDimension::DAE.Dimension) ::List{DAE.Subscript} 
              local outSubscript::List{DAE.Subscript}

              outSubscript = begin
                  local dim_int::ModelicaInteger
                  local enum_ty::Absyn.Path
                  local enum_lits::List{String}
                  local enum_expl::List{DAE.Exp}
                   #=  An integer dimension, generate a list of integer subscripts.
                   =#
                @match inDimension begin
                  DAE.DIM_INTEGER(integer = dim_int)  => begin
                    dimensionSizeSubscripts(dim_int)
                  end
                  
                  DAE.DIM_ENUM(enumTypeName = enum_ty, literals = enum_lits)  => begin
                      enum_expl = makeEnumLiterals(enum_ty, enum_lits)
                    ListUtil.map(enum_expl, makeIndexSubscript)
                  end
                  
                  DAE.DIM_BOOLEAN(__)  => begin
                    _cons(DAE.INDEX(DAE.BCONST(false)), _cons(DAE.INDEX(DAE.BCONST(true)), nil))
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
               #=  An enumeration dimension, construct all enumeration literals and make
               =#
               #=  subscript out of them.
               =#
          outSubscript
        end

         #= Expands a slice subscript expression. =#
        function expandSliceExp(inSliceExp::DAE.Exp) ::List{DAE.Subscript} 
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = begin
                  local expl::List{DAE.Exp}
                  local exp_str::String
                  local err_str::String
                @match inSliceExp begin
                  DAE.ARRAY(array = expl)  => begin
                    ListUtil.map(expl, makeIndexSubscript)
                  end
                  
                  DAE.RANGE(__)  => begin
                    ListUtil.map(Expression.expandRange(inSliceExp), makeIndexSubscript)
                  end
                end
              end
          outSubscripts
        end

        function dimensionSizesSubscripts(inDimSizes::List{<:ModelicaInteger}) ::List{List{DAE.Subscript}} 
              local outSubscripts::List{List{DAE.Subscript}}

              outSubscripts = ListUtil.map(inDimSizes, dimensionSizeSubscripts)
          outSubscripts
        end

        function dimensionSizesSubcriptsOpt(inDimSizes::List{<:Option{<:ModelicaInteger}}) ::List{List{DAE.Subscript}} 
              local outSubscripts::List{List{DAE.Subscript}}

              outSubscripts = ListUtil.mapOption(inDimSizes, dimensionSizeSubscripts)
          outSubscripts
        end

         #= Converts a dimension size in the form of an integer into a list of
           subscripts, e.g.: [3] => {1, 2, 3}. =#
        function dimensionSizeSubscripts(inDimSize::ModelicaInteger) ::List{DAE.Subscript} 
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = list(DAE.INDEX(DAE.ICONST(i)) for i in 1:inDimSize)
          outSubscripts
        end

         #= author: Frenkel TUD 2012-10
          do some numerical helpfull thinks like
          a = b/c - > a*c-b =#
        function createResidualExp(inExp1::DAE.Exp, inExp2::DAE.Exp) ::DAE.Exp 
              local resExp::DAE.Exp

              local iExp1::DAE.Exp
              local iExp2::DAE.Exp

              (iExp1, iExp2) = createResidualExp2(inExp1, inExp2)
              resExp = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local res::DAE.Exp
                  local res1::DAE.Exp
                  local res2::DAE.Exp
                  local N1::DAE.Exp
                  local D1::DAE.Exp
                  local N2::DAE.Exp
                  local D2::DAE.Exp
                  local N::DAE.Exp
                  local D::DAE.Exp
                  local explst::List{DAE.Exp}
                  local explst1::List{DAE.Exp}
                  local ty::DAE.Type
                @matchcontinue (iExp1, iExp2) begin
                  (_, DAE.RCONST(real = 0.0))  => begin
                    iExp1
                  end
                  
                  (_, DAE.ICONST(0))  => begin
                    iExp1
                  end
                  
                  (DAE.RCONST(real = 0.0), _)  => begin
                    iExp2
                  end
                  
                  (DAE.ICONST(0), _)  => begin
                    iExp2
                  end
                  
                  (_, _)  => begin
                      ty = typeof(iExp1)
                      @match true = Types.isIntegerOrRealOrSubTypeOfEither(ty)
                      (N1, D1) = makeFraction(iExp1)
                      (N2, D2) = makeFraction(iExp2)
                      res1 = ExpressionSimplify.simplifySumOperatorExpression(N1, DAE.MUL(ty), D2)
                      res2 = ExpressionSimplify.simplifySumOperatorExpression(N2, DAE.MUL(ty), D1)
                      explst = terms(iExp1)
                      explst1 = terms(iExp2)
                      if isConst(res1) || listLength(explst1) + 1 > listLength(explst)
                        res = expSub(res2, res1)
                      else
                        res = expSub(res1, res2)
                      end
                      (res, _) = ExpressionSimplify.simplify(res)
                    res
                  end
                  
                  (_, _)  => begin
                      ty = typeof(iExp1)
                      @match true = Types.isEnumeration(ty)
                      res = expSub(iExp1, iExp2)
                    res
                  end
                  
                  (_, _)  => begin
                      ty = typeof(iExp1)
                      @match true = Types.isBooleanOrSubTypeBoolean(ty)
                      res = DAE.LUNARY(DAE.NOT(ty), DAE.RELATION(iExp1, DAE.EQUAL(ty), iExp2, -1, NONE()))
                    res
                  end
                  
                  (_, _)  => begin
                      ty = typeof(iExp1)
                      @match true = Types.isStringOrSubTypeString(ty)
                      res = DAE.LUNARY(DAE.NOT(ty), DAE.RELATION(iExp1, DAE.EQUAL(ty), iExp2, -1, NONE()))
                    res
                  end
                  
                  _  => begin
                        res = expSub(iExp1, iExp2)
                        (res, _) = ExpressionSimplify.simplify(res)
                      res
                  end
                end
              end
               #= print(\"\\n\\niExp1:\\n\");print(ExpressionDump.printExpStr(iExp1));
               =#
               #= print(\"\\niExp2:\\n\");print(ExpressionDump.printExpStr(iExp2));
               =#
               #= print(\"\\nres:\\n\");print(ExpressionDump.printExpStr(res));
               =#
          resExp
        end

         #= 
        In: f(x) {+,-} g(x)
        Out: {N,D}

        where f(x) {+,-} g(x) = N/D

        author: Vitalij Ruge

         =#
        function makeFraction(iExp::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp} 
              local d::DAE.Exp #= denominator =#
              local n::DAE.Exp #= numerator =#

              local N::List{DAE.Exp}
              local D::List{DAE.Exp}
              local T::List{DAE.Exp}
              local tp::DAE.Type = typeof(iExp)

              T = terms(iExp)
              T = ExpressionSimplify.simplifyList(T)
              (N, D) = moveDivToMul(T, nil, nil)
              N = ExpressionSimplify.simplifyList(N)
              D = ExpressionSimplify.simplifyList(D)
              n = makeSum1(N)
              d = makeProductLst(D)
              (n, _) = ExpressionSimplify.simplify1(n)
              (d, _) = ExpressionSimplify.simplify1(d)
          (n #= numerator =#, d #= denominator =#)
        end

        function moveDivToMul(iExpLst::List{<:DAE.Exp}, iExpLstAcc::List{<:DAE.Exp}, iExpMuls::List{<:DAE.Exp}) ::Tuple{List{DAE.Exp}, List{DAE.Exp}} 
              local oExpMuls::List{DAE.Exp}
              local oExpLst::List{DAE.Exp}

              (oExpLst, oExpMuls) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local rest::List{DAE.Exp}
                  local acc::List{DAE.Exp}
                  local elst::List{DAE.Exp}
                  local elst1::List{DAE.Exp}
                @match (iExpLst, iExpLstAcc, iExpMuls) begin
                  ( nil(), _, _)  => begin
                    (iExpLstAcc, iExpMuls)
                  end
                  
                  (DAE.UNARY(_, DAE.BINARY(exp1 = e1, operator = DAE.DIV(__), exp2 = e2)) <| rest, _, _)  => begin
                      acc = ListUtil.map1(iExpLstAcc, Expression.expMul, e2)
                      rest = ListUtil.map1(rest, Expression.expMul, e2)
                      rest = ExpressionSimplify.simplifyList(rest)
                      (elst, elst1) = moveDivToMul(rest, _cons(negate(e1), acc), _cons(e2, iExpMuls))
                    (elst, elst1)
                  end
                  
                  (DAE.UNARY(_, DAE.BINARY(exp1 = e1, operator = DAE.DIV_ARRAY_SCALAR(__), exp2 = e2)) <| rest, _, _)  => begin
                      acc = ListUtil.map1(iExpLstAcc, Expression.expMul, e2)
                      rest = ListUtil.map1(rest, Expression.expMul, e2)
                      rest = ExpressionSimplify.simplifyList(rest)
                      (elst, elst1) = moveDivToMul(rest, _cons(negate(e1), acc), _cons(e2, iExpMuls))
                    (elst, elst1)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.DIV(__), exp2 = e2) <| rest, _, _)  => begin
                      acc = ListUtil.map1(iExpLstAcc, Expression.expMul, e2)
                      rest = ListUtil.map1(rest, Expression.expMul, e2)
                      rest = ExpressionSimplify.simplifyList(rest)
                      (elst, elst1) = moveDivToMul(rest, _cons(e1, acc), _cons(e2, iExpMuls))
                    (elst, elst1)
                  end
                  
                  (DAE.BINARY(exp1 = e1, operator = DAE.DIV_ARRAY_SCALAR(__), exp2 = e2) <| rest, _, _)  => begin
                      acc = ListUtil.map1(iExpLstAcc, Expression.expMul, e2)
                      rest = ListUtil.map1(rest, Expression.expMul, e2)
                      rest = ExpressionSimplify.simplifyList(rest)
                      (elst, elst1) = moveDivToMul(rest, _cons(e1, acc), _cons(e2, iExpMuls))
                    (elst, elst1)
                  end
                  
                  (e <| rest, _, _)  => begin
                      (elst, elst1) = moveDivToMul(rest, _cons(e, iExpLstAcc), iExpMuls)
                    (elst, elst1)
                  end
                end
              end
               #= -(a/b)
               =#
               #=  a/b
               =#
          (oExpLst, oExpMuls)
        end

         #= author: Vitalij
          do some numerical helpfull thinks on like
          sqrt(f()) - sqrt(g(.)) = 0 -> f(.) - g(.) =#
        function createResidualExp2(iExp1::DAE.Exp, iExp2::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp} 
              local oExp2::DAE.Exp = iExp2
              local oExp1::DAE.Exp = iExp1

              local con::Bool = true
              local con1::Bool
              local ii::ModelicaInteger = 1

              while con && ii < 15
                (oExp1, oExp2, con) = begin
                    local e::DAE.Exp
                    local e1::DAE.Exp
                    local e2::DAE.Exp
                  @matchcontinue (oExp1, oExp2) begin
                    (_, _)  => begin
                        @match (e1, e2, true) = createResidualExp3(oExp1, oExp2)
                        (e1, _) = ExpressionSimplify.simplify1(e1)
                        (e2, _) = ExpressionSimplify.simplify1(e2)
                      (e1, e2, true)
                    end
                    
                    (_, _)  => begin
                        @match (e2, e1, true) = createResidualExp3(oExp2, oExp1)
                        (e1, _) = ExpressionSimplify.simplify1(e1)
                        (e2, _) = ExpressionSimplify.simplify1(e2)
                      (e1, e2, true)
                    end
                    
                    _  => begin
                        (oExp1, oExp2, false)
                    end
                  end
                end
                (oExp1, oExp2, con1) = begin
                    local e::DAE.Exp
                    local e1::DAE.Exp
                    local e2::DAE.Exp
                  @matchcontinue (oExp1, oExp2) begin
                    (_, _)  => begin
                        @match true = isZero(oExp1)
                        (e1, e2) = makeFraction(oExp2)
                      (e1, oExp1, ! isOne(e2))
                    end
                    
                    (_, _)  => begin
                        @match true = isZero(oExp2)
                        (e1, e2) = makeFraction(oExp1)
                      (e1, oExp2, ! isOne(e2))
                    end
                    
                    (_, _)  => begin
                        @match true = isOne(oExp1)
                        (e1, e2) = makeFraction(oExp2)
                      (e1, e2, ! isOne(e2))
                    end
                    
                    (_, _)  => begin
                        @match true = isOne(oExp2)
                        (e1, e2) = makeFraction(oExp1)
                      (e1, e2, ! isOne(e2))
                    end
                    
                    _  => begin
                        (oExp1, oExp2, false)
                    end
                  end
                end
                con = con || con1
                ii = ii + 1
                if ! con
                  (oExp1, con) = ExpressionSimplify.simplify1(oExp1)
                  (oExp2, con1) = ExpressionSimplify.simplify1(oExp2)
                  con = con || con1
                  ii = ii + 3
                end
              end
               #=  else
               =#
               #=    print(\"\\niExp1\");print(ExpressionDump.printExpStr(iExp1));
               =#
               #=     print(\"\\te1\");print(ExpressionDump.printExpStr(oExp2));
               =#
               #=    print(\"\\niExp2\");print(ExpressionDump.printExpStr(iExp2));
               =#
               #=     print(\"\\te2\");print(ExpressionDump.printExpStr(oExp2));
               =#
              (oExp1, _) = ExpressionSimplify.simplify1(oExp1)
              (oExp2, _) = ExpressionSimplify.simplify1(oExp2)
          (oExp1, oExp2)
        end

         #= author: Vitalij
          helper function of createResidualExp3
          swaps args =#
        function createResidualExp3(iExp1::DAE.Exp, iExp2::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp, Bool} 
              local con::Bool
              local oExp2::DAE.Exp
              local oExp1::DAE.Exp

              (oExp1, oExp2, con) = begin
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e4::DAE.Exp
                  local e5::DAE.Exp
                  local res::DAE.Exp
                  local s1::String
                  local s2::String
                  local tp::DAE.Type
                  local r::ModelicaReal
                   #=  f(x) = f(y) -> x = y
                   =#
                @matchcontinue (iExp1, iExp2) begin
                  (DAE.CALL(path = Absyn.IDENT(s1), expLst = e1 <|  nil()), DAE.CALL(path = Absyn.IDENT(s2), expLst = e2 <|  nil())) where (s1 == s2 && createResidualExp4(s1))  => begin
                    (e1, e2, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()), DAE.RCONST(0.0))  => begin
                    (e1, iExp2, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("sqrt"), expLst = e1 <|  nil()), e2) where (Expression.isConst(e2))  => begin
                      e = Expression.expPow(iExp2, DAE.RCONST(2.0))
                    (e1, e, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("log"), expLst = e1 <|  nil()), e2) where (Expression.isConst(e2))  => begin
                      tp = Expression.typeof(iExp2)
                      e = Expression.makePureBuiltinCall("exp", list(iExp2), tp)
                    (e1, e, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("log10"), expLst = e1 <|  nil()), e2) where (Expression.isConst(e2))  => begin
                      e = Expression.expPow(DAE.RCONST(10.0), iExp2)
                    (e1, e, true)
                  end
                  
                  (DAE.CALL(path = Absyn.IDENT("semiLinear"), expLst = DAE.RCONST(0.0) <| e1 <| e2 <|  nil()), DAE.RCONST(0.0))  => begin
                    (e1, e2, true)
                  end
                  
                  (DAE.UNARY(operator = DAE.UMINUS(__), exp = e1), e2 && DAE.RCONST(0.0))  => begin
                    (e1, e2, true)
                  end
                  
                  (DAE.BINARY(DAE.CALL(path = Absyn.IDENT(s1), expLst = e1 <|  nil()), DAE.SUB(__), DAE.CALL(path = Absyn.IDENT(s2), expLst = e2 <|  nil())), DAE.RCONST(0.0)) where (s1 == s2 && createResidualExp4(s1))  => begin
                    (e1, e2, true)
                  end
                  
                  _  => begin
                      (iExp1, iExp2, false)
                  end
                end
              end
               #=  sqrt(f(x)) = 0.0 -> f(x) = 0
               =#
               #=  sqrt(f(x)) = c -> f(x) = c^2
               =#
               #=  log(f(x)) = c -> f(x) = exp(c)
               =#
               #=  log10(f(x)) = c -> f(x) = 10^(c)
               =#
               #= /*
                   f(x)^y = 0 -> x = 0
                  case(DAE.BINARY(e1,DAE.POW(_),e2),DAE.RCONST(0.0))
                    then (e1, iExp2, true);
                   abs(f(x)) = 0.0 -> f(x) = 0
                  case(DAE.CALL(path = Absyn.IDENT(\"abs\"), expLst={e1}), DAE.RCONST(0.0))
                    then (e1,iExp2,true);
              */ =#
               #=  semiLinear(0,e1,e2) = 0 -> e1 - e2 = 0
               =#
               #=  -f(.) = 0 -> f(.) = 0
               =#
               #=  f(x) - f(y) = 0 -> x = y
               =#
          (oExp1, oExp2, con)
        end

         #= 
         author: Vitalij
         helper function of createResidualExp3
         return true if f(x) = f(y), then it can be transformed into x = y.

         Beware: function is not complete, yet!
         =#
        function createResidualExp4(f::String) ::Bool 
              local resB::Bool

              resB = begin
                @match f begin
                  "sqrt"  => begin
                    true
                  end
                  
                  "exp"  => begin
                    true
                  end
                  
                  "log"  => begin
                    true
                  end
                  
                  "log10"  => begin
                    true
                  end
                  
                  "tanh"  => begin
                    true
                  end
                  
                  "sinh"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          resB
        end

        function isAsubExp(expIn::DAE.Exp) ::Bool 
              local isAsub::Bool

              isAsub = begin
                @match expIn begin
                  DAE.ASUB(_, _)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isAsub
        end

        function typeCast(inExp::DAE.Exp, inType::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = DAE.CAST(inType, inExp)
              outExp = ExpressionSimplify.simplify1(outExp)
          outExp
        end

        function typeCastElements(inExp::DAE.Exp, inType::DAE.Type) ::DAE.Exp 
              local outExp::DAE.Exp

              local ty::DAE.Type

              ty = typeof(inExp)
              ty = Types.setArrayElementType(ty, inType)
              outExp = typeCast(inExp, ty)
          outExp
        end

         #= Expands a range expression into its elements:
            expandRange(1:4) => {1, 2, 3, 4} =#
        function expandRange(inRange::DAE.Exp) ::List{DAE.Exp} 
              local outValues::List{DAE.Exp}

              local start_exp::DAE.Exp
              local stop_exp::DAE.Exp
              local ostep_exp::Option{DAE.Exp}
              local istep::ModelicaInteger
              local rstep::ModelicaReal
              local vals::List{DAE.Exp}
              local enum_names::List{String}
              local enum_type::Absyn.Path

              @match DAE.RANGE(start = start_exp, step = ostep_exp, stop = stop_exp) = inRange
              outValues = begin
                @match (start_exp, stop_exp) begin
                  (DAE.ICONST(__), DAE.ICONST(__))  => begin
                       #=  An integer range, with or without a step value.
                       =#
                      @match DAE.ICONST(istep) = Util.getOptionOrDefault(ostep_exp, DAE.ICONST(1))
                    list(DAE.ICONST(i) for i in ListUtil.intRange3(start_exp.integer, istep, stop_exp.integer))
                  end
                  
                  (DAE.RCONST(__), DAE.RCONST(__))  => begin
                       #=  A real range, with or without a step value.
                       =#
                      @match DAE.RCONST(rstep) = Util.getOptionOrDefault(ostep_exp, DAE.RCONST(1.0))
                    list(DAE.RCONST(r) for r in ExpressionSimplify.simplifyRangeReal(start_exp.real, rstep, stop_exp.real))
                  end
                  
                  (DAE.BCONST(false), DAE.BCONST(true))  => begin
                    list(start_exp, stop_exp)
                  end
                  
                  (DAE.BCONST(true), DAE.BCONST(false))  => begin
                    nil
                  end
                  
                  (DAE.BCONST(__), DAE.BCONST(__))  => begin
                    list(start_exp)
                  end
                  
                  (DAE.ENUM_LITERAL(__), DAE.ENUM_LITERAL(__))  => begin
                       #=  false:true => {false, true}
                       =#
                       #=  true:false => {}
                       =#
                       #=  true:true => true, false:false => false
                       =#
                       #=  An enumeration range, no step value allowed.
                       =#
                      if start_exp.index > stop_exp.index
                        vals = nil
                      elseif start_exp.index == stop_exp.index
                        vals = list(start_exp)
                      else
                        @match DAE.RANGE(ty = DAE.T_ENUMERATION(path = enum_type, names = enum_names)) = inRange
                        enum_names = ListUtil.sublist(enum_names, start_exp.index, stop_exp.index - start_exp.index + 1)
                        vals = makeEnumLiterals(enum_type, enum_names)
                      end
                    vals
                  end
                end
              end
          outValues
        end

        function isScalar(inExp::DAE.Exp) ::Bool 
              local outIsScalar::Bool

              outIsScalar = begin
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
                  
                  DAE.CLKCONST(__)  => begin
                    true
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  DAE.UNARY(__)  => begin
                    isScalar(inExp.exp)
                  end
                  
                  DAE.LUNARY(__)  => begin
                    isScalar(inExp.exp)
                  end
                  
                  DAE.RELATION(__)  => begin
                    true
                  end
                  
                  DAE.ARRAY(__)  => begin
                    false
                  end
                  
                  DAE.MATRIX(__)  => begin
                    false
                  end
                  
                  DAE.RANGE(__)  => begin
                    false
                  end
                  
                  DAE.CAST(__)  => begin
                    isScalar(inExp.exp)
                  end
                  
                  DAE.SIZE(__)  => begin
                    isSome(inExp.sz)
                  end
                  
                  _  => begin
                      Types.isSimpleType(typeof(inExp))
                  end
                end
              end
          outIsScalar
        end

         #= Returns true if the given expression contains any function calls,
           otherwise false. =#
        function containsAnyCall(inExp::DAE.Exp) ::Bool 
              local outContainsCall::Bool

              (_, outContainsCall) = traverseExpTopDown(inExp, containsAnyCall_traverser, false)
          outContainsCall
        end

        function containsAnyCall_traverser(inExp::DAE.Exp, inContainsCall::Bool) ::Tuple{DAE.Exp, Bool, Bool} 
              local outContainsCall::Bool
              local outContinue::Bool
              local outExp::DAE.Exp = inExp

              outContainsCall = begin
                @match inExp begin
                  DAE.CALL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      inContainsCall
                  end
                end
              end
              outContinue = ! outContainsCall
          (outExp, outContinue, outContainsCall)
        end

         #= Returns true if the given expression contains any function calls,
           otherwise false. =#
        function containsCallTo(inExp::DAE.Exp, path::Absyn.Path) ::Bool 
              local outContainsCall::Bool

              (_, (_, outContainsCall)) = traverseExpTopDown(inExp, containsCallTo_traverser, (path, false))
          outContainsCall
        end

        function containsCallTo_traverser(inExp::DAE.Exp, inTpl::Tuple{<:Absyn.Path, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{Absyn.Path, Bool}} 
              local outTpl::Tuple{Absyn.Path, Bool} = inTpl
              local outContinue::Bool = false
              local outExp::DAE.Exp = inExp

              local containsCall::Bool
              local path::Absyn.Path

              (path, containsCall) = outTpl
              if containsCall
                return (outExp, outContinue, outTpl)
              end
              outContinue = begin
                @match inExp begin
                  DAE.CALL(__)  => begin
                    AbsynUtil.pathEqual(path, inExp.path)
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
              if ! outContinue
                outTpl = (path, false)
              end
          (outExp, outContinue, outTpl)
        end

         #= Tries to figure out the size of a range expression. Either return the size or
           fails. =#
        function rangeSize(inRange::DAE.Exp) ::ModelicaInteger 
              local outSize::ModelicaInteger

              outSize = begin
                  local start::ModelicaInteger
                  local step::ModelicaInteger
                  local stop::ModelicaInteger
                @match inRange begin
                  DAE.RANGE(start = DAE.ICONST(start), step = NONE(), stop = DAE.ICONST(stop))  => begin
                    max(stop - start, 0)
                  end
                  
                  DAE.RANGE(start = DAE.ICONST(start), step = SOME(DAE.ICONST(step)), stop = DAE.ICONST(stop))  => begin
                      if step != 0
                        outSize = max(realInt(floor(realDiv(stop - start, step))) + 1, 0)
                      else
                        fail()
                      end
                    outSize
                  end
                end
              end
          outSize
        end

        function compare(inExp1::DAE.Exp, inExp2::DAE.Exp) ::ModelicaInteger 
              local comp::ModelicaInteger

               #=  Return true if the references are the same.
               =#
              if referenceEq(inExp1, inExp2)
                comp = 0
                return comp
              end
              comp = Util.intCompare(valueConstructor(inExp1), valueConstructor(inExp2))
               #=  Return false if the expressions are not of the same type.
               =#
              if comp != 0
                return comp
              end
               #=  Otherwise, check if the expressions are equal or not.
               =#
               #=  Since the expressions have already been verified to be of the same type
               =#
               #=  above we can match on only one of them to allow the pattern matching to
               =#
               #=  optimize this to jump directly to the correct case.
               =#
              comp = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local s::String
                  local b::Bool
                  local p::Absyn.Path
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local oe::Option{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local mexpl::List{List{DAE.Exp}}
                  local op::DAE.Operator
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                @match inExp1 begin
                  DAE.ICONST(__)  => begin
                      @match DAE.ICONST(integer = i) = inExp2
                    Util.intCompare(inExp1.integer, i)
                  end
                  
                  DAE.RCONST(__)  => begin
                      @match DAE.RCONST(real = r) = inExp2
                    Util.realCompare(inExp1.real, r)
                  end
                  
                  DAE.SCONST(__)  => begin
                      @match DAE.SCONST(string = s) = inExp2
                    stringCompare(inExp1.string, s)
                  end
                  
                  DAE.BCONST(__)  => begin
                      @match DAE.BCONST(bool = b) = inExp2
                    Util.boolCompare(inExp1.bool, b)
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                      @match DAE.ENUM_LITERAL(name = p) = inExp2
                    AbsynUtil.pathCompare(inExp1.name, p)
                  end
                  
                  DAE.CREF(__)  => begin
                      @match DAE.CREF(componentRef = cr) = inExp2
                    ComponentReference.crefCompareGeneric(inExp1.componentRef, cr)
                  end
                  
                  DAE.ARRAY(__)  => begin
                      @match DAE.ARRAY(ty = ty, array = expl) = inExp2
                      comp = valueCompare(inExp1.ty, ty)
                    if 0 == comp
                          compareList(inExp1.array, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.MATRIX(__)  => begin
                      @match DAE.MATRIX(ty = ty, matrix = mexpl) = inExp2
                      comp = valueCompare(inExp1.ty, ty)
                    if 0 == comp
                          compareListList(inExp1.matrix, mexpl)
                        else
                          comp
                        end
                  end
                  
                  DAE.BINARY(__)  => begin
                      @match DAE.BINARY(exp1 = e1, operator = op, exp2 = e2) = inExp2
                      comp = operatorCompare(inExp1.operator, op)
                      comp = if 0 == comp
                            compare(inExp1.exp1, e1)
                          else
                            comp
                          end
                    if 0 == comp
                          compare(inExp1.exp2, e2)
                        else
                          comp
                        end
                  end
                  
                  DAE.LBINARY(__)  => begin
                      @match DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2) = inExp2
                      comp = operatorCompare(inExp1.operator, op)
                      comp = if 0 == comp
                            compare(inExp1.exp1, e1)
                          else
                            comp
                          end
                    if 0 == comp
                          compare(inExp1.exp2, e2)
                        else
                          comp
                        end
                  end
                  
                  DAE.UNARY(__)  => begin
                      @match DAE.UNARY(exp = e, operator = op) = inExp2
                      comp = operatorCompare(inExp1.operator, op)
                    if 0 == comp
                          compare(inExp1.exp, e)
                        else
                          comp
                        end
                  end
                  
                  DAE.LUNARY(__)  => begin
                      @match DAE.LUNARY(exp = e, operator = op) = inExp2
                      comp = operatorCompare(inExp1.operator, op)
                    if 0 == comp
                          compare(inExp1.exp, e)
                        else
                          comp
                        end
                  end
                  
                  DAE.RELATION(__)  => begin
                      @match DAE.RELATION(exp1 = e1, operator = op, exp2 = e2) = inExp2
                      comp = operatorCompare(inExp1.operator, op)
                      comp = if 0 == comp
                            compare(inExp1.exp1, e1)
                          else
                            comp
                          end
                    if 0 == comp
                          compare(inExp1.exp2, e2)
                        else
                          comp
                        end
                  end
                  
                  DAE.IFEXP(__)  => begin
                      @match DAE.IFEXP(expCond = e, expThen = e1, expElse = e2) = inExp2
                      comp = compare(inExp1.expCond, e)
                      comp = if 0 == comp
                            compare(inExp1.expThen, e1)
                          else
                            comp
                          end
                    if 0 == comp
                          compare(inExp1.expElse, e2)
                        else
                          comp
                        end
                  end
                  
                  DAE.CALL(__)  => begin
                      @match DAE.CALL(path = p, expLst = expl) = inExp2
                      comp = AbsynUtil.pathCompare(inExp1.path, p)
                    if 0 == comp
                          compareList(inExp1.expLst, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.RECORD(__)  => begin
                      @match DAE.RECORD(path = p, exps = expl) = inExp2
                      comp = AbsynUtil.pathCompare(inExp1.path, p)
                    if 0 == comp
                          compareList(inExp1.exps, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.PARTEVALFUNCTION(__)  => begin
                      @match DAE.PARTEVALFUNCTION(path = p, expList = expl) = inExp2
                      comp = AbsynUtil.pathCompare(inExp1.path, p)
                    if 0 == comp
                          compareList(inExp1.expList, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.RANGE(__)  => begin
                      @match DAE.RANGE(start = e1, step = oe, stop = e2) = inExp2
                      comp = compare(inExp1.start, e1)
                      comp = if 0 == comp
                            compare(inExp1.stop, e2)
                          else
                            comp
                          end
                    if 0 == comp
                          compareOpt(inExp1.step, oe)
                        else
                          comp
                        end
                  end
                  
                  DAE.TUPLE(__)  => begin
                      @match DAE.TUPLE(PR = expl) = inExp2
                    compareList(inExp1.PR, expl)
                  end
                  
                  DAE.CAST(__)  => begin
                      @match DAE.CAST(ty = ty, exp = e) = inExp2
                      comp = valueCompare(inExp1.ty, ty)
                    if 0 == comp
                          compare(inExp1.exp, e)
                        else
                          comp
                        end
                  end
                  
                  DAE.ASUB(__)  => begin
                      @match DAE.ASUB(exp = e, sub = expl) = inExp2
                      comp = compare(inExp1.exp, e)
                    if comp == 0
                          compareList(inExp1.sub, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.RSUB(__)  => begin
                      @match DAE.RSUB(exp = e, ix = i, fieldName = s, ty = ty) = inExp2
                      comp = Util.intCompare(inExp1.ix, i)
                      comp = if comp == 0
                            valueCompare(inExp1.ty, ty)
                          else
                            comp
                          end
                      comp = if comp == 0
                            stringCompare(inExp1.fieldName, s)
                          else
                            comp
                          end
                    if comp == 0
                          compare(inExp1.exp, e)
                        else
                          comp
                        end
                  end
                  
                  DAE.TSUB(__)  => begin
                      @match DAE.TSUB(exp = e, ix = i, ty = ty) = inExp2
                      comp = Util.intCompare(inExp1.ix, i)
                      comp = if 0 == comp
                            valueCompare(inExp1.ty, ty)
                          else
                            comp
                          end
                    if 0 == comp
                          compare(inExp1.exp, e)
                        else
                          comp
                        end
                  end
                  
                  DAE.SIZE(__)  => begin
                      @match DAE.SIZE(exp = e, sz = oe) = inExp2
                      comp = compare(inExp1.exp, e)
                    if comp == 0
                          compareOpt(inExp1.sz, oe)
                        else
                          comp
                        end
                  end
                  
                  DAE.REDUCTION(__)  => begin
                    valueCompare(inExp1, inExp2)
                  end
                  
                  DAE.LIST(__)  => begin
                       #=  Reductions contain too much information to compare in a sane manner.
                       =#
                      @match DAE.LIST(valList = expl) = inExp2
                    compareList(inExp1.valList, expl)
                  end
                  
                  DAE.CONS(__)  => begin
                      @match DAE.CONS(car = e1, cdr = e2) = inExp2
                      comp = compare(inExp1.car, e1)
                    if 0 == comp
                          compare(inExp1.cdr, e2)
                        else
                          comp
                        end
                  end
                  
                  DAE.META_TUPLE(__)  => begin
                      @match DAE.META_TUPLE(listExp = expl) = inExp2
                    compareList(inExp1.listExp, expl)
                  end
                  
                  DAE.META_OPTION(__)  => begin
                      @match DAE.META_OPTION(exp = oe) = inExp2
                    compareOpt(inExp1.exp, oe)
                  end
                  
                  DAE.METARECORDCALL(__)  => begin
                      @match DAE.METARECORDCALL(path = p, args = expl) = inExp2
                      comp = AbsynUtil.pathCompare(inExp1.path, p)
                    if comp == 0
                          compareList(inExp1.args, expl)
                        else
                          comp
                        end
                  end
                  
                  DAE.MATCHEXPRESSION(__)  => begin
                    valueCompare(inExp1, inExp2)
                  end
                  
                  DAE.BOX(__)  => begin
                      @match DAE.BOX(exp = e) = inExp2
                    compare(inExp1.exp, e)
                  end
                  
                  DAE.UNBOX(__)  => begin
                      @match DAE.UNBOX(exp = e) = inExp2
                    compare(inExp1.exp, e)
                  end
                  
                  DAE.SHARED_LITERAL(__)  => begin
                      @match DAE.SHARED_LITERAL(index = i) = inExp2
                    Util.intCompare(inExp1.index, i)
                  end
                  
                  DAE.EMPTY(__)  => begin
                      @match DAE.EMPTY(name = cr) = inExp2
                    ComponentReference.crefCompareGeneric(inExp1.name, cr)
                  end
                  
                  DAE.CODE(__)  => begin
                    valueCompare(inExp1, inExp2)
                  end
                  
                  _  => begin
                        Error.addInternalError("Expression.compare failed: ctor:" + String(valueConstructor(inExp1)) + " " + printExpStr(inExp1) + " " + printExpStr(inExp2), sourceInfo())
                      fail()
                  end
                end
              end
          comp
        end

        function compareSubscripts(sub1::DAE.Subscript, sub2::DAE.Subscript) ::ModelicaInteger 
              local res::ModelicaInteger

              if referenceEq(sub1, sub2)
                res = 0
              else
                res = begin
                  @match (sub1, sub2) begin
                    (DAE.Subscript.WHOLEDIM(__), DAE.Subscript.WHOLEDIM(__))  => begin
                      0
                    end
                    
                    (DAE.Subscript.SLICE(__), DAE.Subscript.SLICE(__))  => begin
                      compare(sub1.exp, sub2.exp)
                    end
                    
                    (DAE.Subscript.INDEX(__), DAE.Subscript.INDEX(__))  => begin
                      compare(sub1.exp, sub2.exp)
                    end
                    
                    (DAE.Subscript.WHOLE_NONEXP(__), DAE.Subscript.WHOLE_NONEXP(__))  => begin
                      compare(sub1.exp, sub2.exp)
                    end
                    
                    _  => begin
                        Util.intCompare(valueConstructor(sub1), valueConstructor(sub2))
                    end
                  end
                end
              end
          res
        end

         #= For use with traverseExp =#
        function isInvariantExpNoTraverse(e::DAE.Exp, b::Bool) ::Tuple{DAE.Exp, Bool} 



              if ! b
                return (e, b)
              end
              b = begin
                @match e begin
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
                  
                  DAE.BINARY(__)  => begin
                    true
                  end
                  
                  DAE.UNARY(__)  => begin
                    true
                  end
                  
                  DAE.LBINARY(__)  => begin
                    true
                  end
                  
                  DAE.LUNARY(__)  => begin
                    true
                  end
                  
                  DAE.RELATION(__)  => begin
                    true
                  end
                  
                  DAE.IFEXP(__)  => begin
                    true
                  end
                  
                  DAE.CALL(path = Absyn.FULLYQUALIFIED(__))  => begin
                    true
                  end
                  
                  DAE.PARTEVALFUNCTION(path = Absyn.FULLYQUALIFIED(__))  => begin
                    true
                  end
                  
                  DAE.ARRAY(__)  => begin
                    true
                  end
                  
                  DAE.MATRIX(__)  => begin
                    true
                  end
                  
                  DAE.RANGE(__)  => begin
                    true
                  end
                  
                  DAE.CONS(__)  => begin
                    true
                  end
                  
                  DAE.LIST(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          (e, b)
        end

        function findCallIsInlineAfterIndexReduction(e::DAE.Exp, res::Bool) ::Tuple{DAE.Exp, Bool, Bool} 

              local cont::Bool


              if ! res
                res = begin
                  @match e begin
                    DAE.CALL(attr = DAE.CALL_ATTR(inlineType = DAE.AFTER_INDEX_RED_INLINE(__)))  => begin
                      true
                    end
                    
                    _  => begin
                        false
                    end
                  end
                end
              end
              cont = ! res
          (e, cont, res)
        end

        function tupleHead(exp::DAE.Exp, prop::DAE.Properties) ::Tuple{DAE.Exp, DAE.Properties} 
              local outProp::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProp) = begin
                  local ty::DAE.Type
                @match (exp, prop) begin
                  (DAE.Exp.TUPLE(_ <| _), DAE.Properties.PROP_TUPLE(__))  => begin
                    (listHead(exp.PR), Types.propTupleFirstProp(prop))
                  end
                  
                  (_, DAE.Properties.PROP_TUPLE(type_ = DAE.T_TUPLE(types = ty <| _)))  => begin
                    (DAE.Exp.TSUB(exp, 1, ty), Types.propTupleFirstProp(prop))
                  end
                  
                  _  => begin
                      (exp, prop)
                  end
                end
              end
          (outExp, outProp)
        end

         #= A value that requires nothing special during code generation. String literals are special and not included. =#
        function isSimpleLiteralValue(exp::DAE.Exp) ::Bool 
              local b::Bool

              b = begin
                @match exp begin
                  DAE.ICONST(__)  => begin
                    true
                  end
                  
                  DAE.RCONST(__)  => begin
                    true
                  end
                  
                  DAE.BCONST(__)  => begin
                    true
                  end
                  
                  DAE.ENUM_LITERAL(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function consToListIgnoreSharedLiteral(e::DAE.Exp) ::DAE.Exp 


              local exp::DAE.Exp

              if begin
                @match e begin
                  DAE.SHARED_LITERAL(__)  => begin
                    true
                  end
                  
                  DAE.LIST(__)  => begin
                    true
                  end
                  
                  DAE.CONS(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
                try
                  e = consToListIgnoreSharedLiteralWork(e)
                catch
                end
              end
          e
        end

        function consToListIgnoreSharedLiteralWork(e::DAE.Exp, acc::List{<:DAE.Exp} = nil) ::DAE.Exp 


              e = begin
                @match (e, acc) begin
                  (DAE.SHARED_LITERAL(__), _)  => begin
                    consToListIgnoreSharedLiteralWork(e.exp, acc)
                  end
                  
                  (DAE.LIST(__),  nil())  => begin
                    e
                  end
                  
                  (DAE.LIST(__), _)  => begin
                    DAE.LIST(ListUtil.append_reverse(acc, e.valList))
                  end
                  
                  (DAE.CONS(__), _)  => begin
                    consToListIgnoreSharedLiteralWork(e.cdr, _cons(e.car, acc))
                  end
                end
              end
          e
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
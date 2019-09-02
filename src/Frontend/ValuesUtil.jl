  module ValuesUtil 


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

        import DAE

        import Values

        import Debug

        import Dump

        import Error

        import Expression

        import ExpressionSimplify

        import ExpressionSimplifyTypes

        import Flags

        import ListUtil

        import Print

        import System

        import ClassInf

        import Types

         #= Apply type conversion on a list of Values =#
        function typeConvert(inType1::DAE.Type, inType2::DAE.Type, inValueLst3::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local vallst::List{Values.Value}
                  local vrest::List{Values.Value}
                  local vallst2::List{Values.Value}
                  local vals::List{Values.Value}
                  local rval::ModelicaReal
                  local r::ModelicaReal
                  local from::DAE.Type
                  local to::DAE.Type
                  local i::ModelicaInteger
                  local ival::ModelicaInteger
                  local dims::List{ModelicaInteger}
                @match (inType1, inType2, inValueLst3) begin
                  (_, _,  nil())  => begin
                    nil
                  end
                  
                  (from && DAE.T_INTEGER(__), to && DAE.T_REAL(__), Values.INTEGER(integer = i) <| vrest)  => begin
                      vallst = typeConvert(from, to, vrest)
                      rval = intReal(i)
                    _cons(Values.REAL(rval), vallst)
                  end
                  
                  (from && DAE.T_REAL(__), to && DAE.T_INTEGER(__), Values.REAL(real = r) <| vrest)  => begin
                      vallst = typeConvert(from, to, vrest)
                      ival = realInt(r)
                    _cons(Values.INTEGER(ival), vallst)
                  end
                  
                  (from, to, Values.ARRAY(valueLst = vals, dimLst = dims) <| vrest)  => begin
                      vallst = typeConvert(from, to, vals)
                      vallst2 = typeConvert(from, to, vrest)
                    _cons(Values.ARRAY(vallst, dims), vallst2)
                  end
                end
              end
          outValueLst
        end

         #= creates a DAE.Type from a Value =#
        function valueExpType(inValue::Values.Value) ::DAE.Type 
              local tp::DAE.Type

              tp = begin
                  local path::Absyn.Path
                  local indx::ModelicaInteger
                  local nameLst::List{String}
                  local eltTp::DAE.Type
                  local valLst::List{Values.Value}
                  local eltTps::List{DAE.Type}
                  local varLst::List{DAE.Var}
                  local int_dims::List{ModelicaInteger}
                  local dims::DAE.Dimensions
                @matchcontinue inValue begin
                  Values.INTEGER(_)  => begin
                    DAE.T_INTEGER_DEFAULT
                  end
                  
                  Values.REAL(_)  => begin
                    DAE.T_REAL_DEFAULT
                  end
                  
                  Values.BOOL(_)  => begin
                    DAE.T_BOOL_DEFAULT
                  end
                  
                  Values.STRING(_)  => begin
                    DAE.T_STRING_DEFAULT
                  end
                  
                  Values.ENUM_LITERAL(name = path)  => begin
                      path = AbsynUtil.pathPrefix(path)
                    DAE.T_ENUMERATION(NONE(), path, nil, nil, nil)
                  end
                  
                  Values.ARRAY(valLst, int_dims)  => begin
                      eltTp = valueExpType(listHead(valLst))
                      dims = ListUtil.map(int_dims, Expression.intDimension)
                    DAE.T_ARRAY(eltTp, dims)
                  end
                  
                  Values.RECORD(path, valLst, nameLst, _)  => begin
                      eltTps = ListUtil.map(valLst, valueExpType)
                      varLst = ListUtil.threadMap(eltTps, nameLst, valueExpTypeExpVar)
                    DAE.T_COMPLEX(ClassInf.RECORD(path), varLst, NONE())
                  end
                  
                  _  => begin
                      print("valueExpType on " + valString(inValue) + " not implemented yet\\n")
                    fail()
                  end
                end
              end
          tp
        end

         #= help function to valueExpType =#
        function valueExpTypeExpVar(etp::DAE.Type, name::String) ::DAE.Var 
              local expVar::DAE.Var

              expVar = DAE.TYPES_VAR(name, DAE.dummyAttrVar, etp, DAE.UNBOUND(), NONE())
          expVar
        end

         #= Returns true if value is zero =#
        function isZero(inValue::Values.Value) ::Bool 
              local isZero::Bool

              isZero = begin
                  local rval::ModelicaReal
                  local ival::ModelicaInteger
                @match inValue begin
                  Values.REAL(rval)  => begin
                    realEq(rval, 0.0)
                  end
                  
                  Values.INTEGER(ival)  => begin
                    intEq(ival, 0)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isZero
        end

         #= Returns a zero value based on a DAE.Type =#
        function makeZero(ty::DAE.Type) ::Values.Value 
              local zero::Values.Value

              zero = begin
                @match ty begin
                  DAE.T_REAL(__)  => begin
                    Values.REAL(0.0)
                  end
                  
                  DAE.T_INTEGER(__)  => begin
                    Values.INTEGER(0)
                  end
                end
              end
          zero
        end

         #= Return true if Value is an array. =#
        function isArray(inValue::Values.Value) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inValue begin
                  Values.ARRAY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if Value is an array. =#
        function isRecord(inValue::Values.Value) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                @match inValue begin
                  Values.RECORD(__)  => begin
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
          Return the nth value of an array, indexed from 1..n =#
        function nthArrayelt(inValue::Values.Value, inInteger::ModelicaInteger) ::Values.Value 
              local outValue::Values.Value

              local vlst::List{Values.Value}

              @match Values.ARRAY(valueLst = vlst) = inValue
              outValue = listGet(vlst, inInteger)
          outValue
        end

         #= Prints a list of Value to a string. =#
        function unparseValues(inValueLst::List{<:Values.Value}) ::String 
              local outString::String

              outString = begin
                  local s1::String
                  local s2::String
                  local s3::String
                  local str::String
                  local v::Values.Value
                  local vallst::List{Values.Value}
                @match inValueLst begin
                  v <| vallst  => begin
                      s1 = unparseDescription(list(v))
                      s2 = unparseValueNumbers(list(v))
                      s3 = unparseValues(vallst)
                      str = stringAppendList(list(s1, s2, "\\n", s3))
                    str
                  end
                  
                   nil()  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Helper function to unparse_values.
          Prints all the numbers of the values. =#
        function unparseValueNumbers(inValueLst::List{<:Values.Value}) ::String 
              local outString::String

              outString = begin
                  local s1::String
                  local s2::String
                  local res::String
                  local istr::String
                  local sval::String
                  local lst::List{Values.Value}
                  local xs::List{Values.Value}
                  local i::ModelicaInteger
                  local r::ModelicaReal
                @match inValueLst begin
                  Values.TUPLE(valueLst = lst) <| xs  => begin
                      s1 = unparseValueNumbers(lst)
                      s2 = unparseValueNumbers(xs)
                      res = stringAppend(s1, s2)
                    res
                  end
                  
                  Values.META_TUPLE(valueLst = lst) <| xs  => begin
                      s1 = unparseValueNumbers(lst)
                      s2 = unparseValueNumbers(xs)
                      res = stringAppend(s1, s2)
                    res
                  end
                  
                  Values.ARRAY(valueLst = lst) <| xs  => begin
                      s1 = unparseValueNumbers(lst)
                      s2 = unparseValueNumbers(xs)
                      res = stringAppend(s1, s2)
                    res
                  end
                  
                  Values.INTEGER(integer = i) <| xs  => begin
                      s1 = unparseValueNumbers(xs)
                      istr = intString(i)
                      s2 = stringAppend(istr, " ")
                      res = stringAppend(s2, s1)
                    res
                  end
                  
                  Values.REAL(real = r) <| xs  => begin
                      s1 = unparseValueNumbers(xs)
                      istr = realString(r)
                      s2 = stringAppend(istr, " ")
                      res = stringAppend(s2, s1)
                    res
                  end
                  
                  Values.STRING(string = sval) <| xs  => begin
                      s1 = unparseValueNumbers(xs)
                      s2 = stringAppend(sval, " ")
                      res = stringAppend(s2, s1)
                    res
                  end
                  
                   nil()  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Performs mul, div, sub, add and pow on integers and reals.
           If for example an integer multiplication does not fit in a
           integer, a real is returned instead. The is not the ideal way of
           handling this, since the types are decided in run-time. Currently,
           this is the simplest and best alternative for the moment though.

           In the future, we should introduce BIG-INTS, or maybe throw exceptions
           (when exceptions are available in the language).
           =#
        function safeIntRealOp(val1::Values.Value, val2::Values.Value, op::Values.IntRealOp) ::Values.Value 
              local outv::Values.Value

              outv = begin
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local rv3::ModelicaReal
                  local iv1::ModelicaInteger
                  local iv2::ModelicaInteger
                  local e::DAE.Exp
                   #= MUL
                   =#
                @matchcontinue (val1, val2, op) begin
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.MULOP(__))  => begin
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.MULOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.REAL(rv1), Values.INTEGER(iv2), Values.MULOP(__))  => begin
                      rv2 = intReal(iv2)
                      rv3 = rv1 * rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.MULOP(__))  => begin
                      rv1 = intReal(iv1)
                      rv3 = rv1 * rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.REAL(rv1), Values.REAL(rv2), Values.MULOP(__))  => begin
                      rv3 = rv1 * rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.DIVOP(__))  => begin
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.DIVOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.REAL(rv1), Values.INTEGER(iv2), Values.DIVOP(__))  => begin
                      rv2 = intReal(iv2)
                      rv3 = rv1 / rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.DIVOP(__))  => begin
                      rv1 = intReal(iv1)
                      rv3 = rv1 / rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.REAL(rv1), Values.REAL(rv2), Values.DIVOP(__))  => begin
                      rv3 = rv1 / rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.POWOP(__))  => begin
                      @match true = iv2 < 0
                      rv1 = intReal(iv1)
                      rv2 = intReal(iv2)
                      rv3 = realPow(rv1, rv2)
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.POWOP(__))  => begin
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.POWOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.REAL(rv1), Values.INTEGER(iv2), Values.POWOP(__))  => begin
                      rv2 = intReal(iv2)
                      rv3 = realPow(rv1, rv2)
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.POWOP(__))  => begin
                      iv2 = realInt(rv2)
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.POWOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.POWOP(__))  => begin
                      rv1 = intReal(iv1)
                      rv3 = realPow(rv1, rv2)
                    Values.REAL(rv3)
                  end
                  
                  (Values.REAL(rv1), Values.REAL(rv2), Values.POWOP(__))  => begin
                      rv3 = realPow(rv1, rv2)
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.ADDOP(__))  => begin
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.ADDOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.REAL(rv1), Values.INTEGER(iv2), Values.ADDOP(__))  => begin
                      rv2 = intReal(iv2)
                      rv3 = rv1 + rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.ADDOP(__))  => begin
                      rv1 = intReal(iv1)
                      rv3 = rv1 + rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.REAL(rv1), Values.REAL(rv2), Values.ADDOP(__))  => begin
                      rv3 = rv1 + rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.INTEGER(iv2), Values.SUBOP(__))  => begin
                      e = ExpressionSimplify.safeIntOp(iv1, iv2, ExpressionSimplifyTypes.SUBOP())
                      outv = expValue(e)
                    outv
                  end
                  
                  (Values.REAL(rv1), Values.INTEGER(iv2), Values.SUBOP(__))  => begin
                      rv2 = intReal(iv2)
                      rv3 = rv1 - rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.INTEGER(iv1), Values.REAL(rv2), Values.SUBOP(__))  => begin
                      rv1 = intReal(iv1)
                      rv3 = rv1 - rv2
                    Values.REAL(rv3)
                  end
                  
                  (Values.REAL(rv1), Values.REAL(rv2), Values.SUBOP(__))  => begin
                      rv3 = rv1 - rv2
                    Values.REAL(rv3)
                  end
                end
              end
               #= DIV
               =#
               #= POW
               =#
               #=  this means indirect that we are dealing with decimal numbers (a^(-b)) = 1/a^b
               =#
               #= ADD
               =#
               #= SUB
               =#
          outv
        end

         #= Checks if val1 is less or equal to val2. Val1 or val2 can be integers (or
          something that can be converted to integer) or reals. =#
        function safeLessEq(val1::Values.Value, val2::Values.Value) ::Bool 
              local outv::Bool

              outv = begin
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                @match (val1, val2) begin
                  (Values.REAL(r1), Values.REAL(r2))  => begin
                    r1 <= r2
                  end
                  
                  (Values.REAL(r1), _)  => begin
                      r2 = intReal(valueInteger(val2))
                    r1 <= r2
                  end
                  
                  (_, Values.REAL(r2))  => begin
                      r1 = intReal(valueInteger(val1))
                    r1 <= r2
                  end
                  
                  (_, _)  => begin
                      i1 = valueInteger(val1)
                      i2 = valueInteger(val2)
                    i1 <= i2
                  end
                end
              end
          outv
        end

         #= 
          Helper function to unparse_values. Creates a description string
          for the type of the value.
         =#
        function unparseDescription(inValueLst::List{<:Values.Value}) ::String 
              local outString::String

              outString = begin
                  local s1::String
                  local str::String
                  local slenstr::String
                  local sval::String
                  local s2::String
                  local s4::String
                  local xs::List{Values.Value}
                  local vallst::List{Values.Value}
                  local slen::ModelicaInteger
                @match inValueLst begin
                  Values.INTEGER(__) <| xs  => begin
                      s1 = unparseDescription(xs)
                      str = stringAppend("# i!\\n", s1)
                    str
                  end
                  
                  Values.REAL(__) <| xs  => begin
                      s1 = unparseDescription(xs)
                      str = stringAppend("# r!\\n", s1)
                    str
                  end
                  
                  Values.STRING(string = sval) <| xs  => begin
                      s1 = unparseDescription(xs)
                      slen = stringLength(sval)
                      slenstr = intString(slen)
                      str = stringAppendList(list("# s! 1 ", slenstr, "\\n", s1))
                    str
                  end
                  
                  Values.ARRAY(valueLst = vallst) <| xs  => begin
                      s1 = unparseDescription(xs)
                      s2 = unparseArrayDescription(vallst)
                      s4 = stringAppend(s2, s1)
                      str = stringAppend(s4, " \\n")
                    str
                  end
                  
                   nil()  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= 
          Helper function to unparse_description.
         =#
        function unparseArrayDescription(lst::List{<:Values.Value}) ::String 
              local str::String

              local pt::String
              local s1::String
              local s2::String
              local s3::String
              local s4::String
              local s5::String
              local s6::String
              local i1::ModelicaInteger

              pt = unparsePrimType(lst)
              s1 = stringAppend("# ", pt)
              s2 = stringAppend(s1, "[")
              i1 = unparseNumDims(lst, 0)
              s3 = intString(i1)
              s4 = stringAppend(s2, s3)
              s5 = stringAppend(s4, " ")
              s6 = unparseDimSizes(lst)
              str = stringAppend(s5, s6)
          str
        end

         #= 
          Helper function to unparse_array_description.
         =#
        function unparsePrimType(inValueLst::List{<:Values.Value}) ::String 
              local outString::String

              outString = begin
                  local res::String
                  local elts::List{Values.Value}
                @match inValueLst begin
                  Values.ARRAY(valueLst = elts) <| _  => begin
                      res = unparsePrimType(elts)
                    res
                  end
                  
                  Values.INTEGER(__) <| _  => begin
                    "i"
                  end
                  
                  Values.REAL(__) <| _  => begin
                    "r"
                  end
                  
                  Values.STRING(__) <| _  => begin
                    "s"
                  end
                  
                  Values.BOOL(__) <| _  => begin
                    "b"
                  end
                  
                   nil()  => begin
                    "{}"
                  end
                  
                  _  => begin
                      "error"
                  end
                end
              end
          outString
        end

         #= 
          Helper function to unparse_array_description.
         =#
        function unparseNumDims(inValueLst::List{<:Values.Value}, inInteger::ModelicaInteger) ::ModelicaInteger 
              local outInteger::ModelicaInteger

              outInteger = begin
                  local i1::ModelicaInteger
                  local vals::List{Values.Value}
                @match inValueLst begin
                  Values.ARRAY(valueLst = vals) <| _  => begin
                    unparseNumDims(vals, inInteger + 1)
                  end
                  
                  _  => begin
                      inInteger + 1
                  end
                end
              end
          outInteger
        end

         #= 
          Helper function to unparse_array_description.
         =#
        function unparseDimSizes(inValueLst::List{<:Values.Value}) ::String 
              local outString::String

              outString = begin
                  local i1::ModelicaInteger
                  local len::ModelicaInteger
                  local s1::String
                  local s2::String
                  local s3::String
                  local res::String
                  local lst::List{Values.Value}
                  local vals::List{Values.Value}
                @matchcontinue inValueLst begin
                  lst && Values.ARRAY(valueLst = vals) <| _  => begin
                      i1 = listLength(lst)
                      s1 = intString(i1)
                      s2 = stringAppend(s1, " ")
                      s3 = unparseDimSizes(vals)
                      res = stringAppend(s2, s3)
                    res
                  end
                  
                  lst  => begin
                      len = listLength(lst)
                      res = intString(len)
                    res
                  end
                end
              end
          outString
        end

         #= 
          Write a list of Values to a file. This function is used when
          writing the formal input arguments of a function call to a file before
          executing the function.
         =#
        function writeToFileAsArgs(vallst::List{<:Values.Value}, filename::String)  
              local str::String

              str = unparseValues(vallst)
              System.writeFile(filename, str)
        end

         #= 
          Perform elementwise addition of two arrays.
         =#
        function addElementwiseArrayelt(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local reslst::List{Values.Value}
                  local res2::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local rest2::List{Values.Value}
                  local res::ModelicaInteger
                  local v1::ModelicaInteger
                  local v2::ModelicaInteger
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local rres::ModelicaReal
                  local s1::String
                  local s2::String
                  local sres::String
                  local dims::List{ModelicaInteger}
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst, dimLst = dims) <| rest1, Values.ARRAY(valueLst = v2lst) <| rest2)  => begin
                      reslst = addElementwiseArrayelt(v1lst, v2lst)
                      res2 = addElementwiseArrayelt(rest1, rest2)
                    _cons(Values.ARRAY(reslst, dims), res2)
                  end
                  
                  (Values.INTEGER(integer = v1) <| rest1, Values.INTEGER(integer = v2) <| rest2)  => begin
                      res = v1 + v2
                      res2 = addElementwiseArrayelt(rest1, rest2)
                    _cons(Values.INTEGER(res), res2)
                  end
                  
                  (Values.REAL(real = r1) <| rest1, Values.REAL(real = r2) <| rest2)  => begin
                      rres = r1 + r2
                      res2 = addElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(rres), res2)
                  end
                  
                  (Values.STRING(string = s1) <| rest1, Values.STRING(string = s2) <| rest2)  => begin
                      sres = stringAppend(s1, s2)
                      res2 = addElementwiseArrayelt(rest1, rest2) #= Addition of strings is string concatenation =#
                    _cons(Values.STRING(sres), res2)
                  end
                  
                  ( nil(),  nil())  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= 
          Perform element subtraction of two arrays of values
         =#
        function subElementwiseArrayelt(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local reslst::List{Values.Value}
                  local res2::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local rest2::List{Values.Value}
                  local res::ModelicaInteger
                  local v1::ModelicaInteger
                  local v2::ModelicaInteger
                  local dims::List{ModelicaInteger}
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local rres::ModelicaReal
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst, dimLst = dims) <| rest1, Values.ARRAY(valueLst = v2lst) <| rest2)  => begin
                      reslst = subElementwiseArrayelt(v1lst, v2lst)
                      res2 = subElementwiseArrayelt(rest1, rest2)
                    _cons(Values.ARRAY(reslst, dims), res2)
                  end
                  
                  (Values.INTEGER(integer = v1) <| rest1, Values.INTEGER(integer = v2) <| rest2)  => begin
                      res = v1 - v2
                      res2 = subElementwiseArrayelt(rest1, rest2)
                    _cons(Values.INTEGER(res), res2)
                  end
                  
                  (Values.REAL(real = r1) <| rest1, Values.REAL(real = r2) <| rest2)  => begin
                      rres = r1 - r2
                      res2 = subElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(rres), res2)
                  end
                  
                  ( nil(),  nil())  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= 
          Perform elementwise multiplication of two arrays of values
         =#
        function mulElementwiseArrayelt(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local reslst::List{Values.Value}
                  local res2::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local rest2::List{Values.Value}
                  local res::ModelicaInteger
                  local v1::ModelicaInteger
                  local v2::ModelicaInteger
                  local dims::List{ModelicaInteger}
                  local rres::ModelicaReal
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst, dimLst = dims) <| rest1, Values.ARRAY(valueLst = v2lst) <| rest2)  => begin
                      reslst = mulElementwiseArrayelt(v1lst, v2lst)
                      res2 = mulElementwiseArrayelt(rest1, rest2)
                    _cons(Values.ARRAY(reslst, dims), res2)
                  end
                  
                  (Values.INTEGER(integer = v1) <| rest1, Values.INTEGER(integer = v2) <| rest2)  => begin
                      res = v1 * v2
                      res2 = mulElementwiseArrayelt(rest1, rest2)
                    _cons(Values.INTEGER(res), res2)
                  end
                  
                  (Values.REAL(real = r1) <| rest1, Values.REAL(real = r2) <| rest2)  => begin
                      rres = r1 * r2
                      res2 = mulElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(rres), res2)
                  end
                  
                  ( nil(),  nil())  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= 
          Perform elementwise division of two arrays of values
         =#
        function divElementwiseArrayelt(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local reslst::List{Values.Value}
                  local res2::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local rest2::List{Values.Value}
                  local res::ModelicaReal
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local dims::List{ModelicaInteger}
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst, dimLst = dims) <| rest1, Values.ARRAY(valueLst = v2lst) <| rest2)  => begin
                      reslst = divElementwiseArrayelt(v1lst, v2lst)
                      res2 = divElementwiseArrayelt(rest1, rest2)
                    _cons(Values.ARRAY(reslst, dims), res2)
                  end
                  
                  (Values.INTEGER(integer = i1) <| rest1, Values.INTEGER(integer = i2) <| rest2)  => begin
                      r1 = intReal(i1)
                      r2 = intReal(i2)
                      res = r1 / r2
                      res2 = divElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(res), res2)
                  end
                  
                  (Values.REAL(real = r1) <| rest1, Values.REAL(real = r2) <| rest2)  => begin
                      res = r1 / r2
                      res2 = divElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(res), res2)
                  end
                  
                  ( nil(),  nil())  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= 
          Computes elementwise powers of two arrays of values
         =#
        function powElementwiseArrayelt(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local reslst::List{Values.Value}
                  local res2::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local rest2::List{Values.Value}
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local res::ModelicaReal
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local dims::List{ModelicaInteger}
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst, dimLst = dims) <| rest1, Values.ARRAY(valueLst = v2lst) <| rest2)  => begin
                      reslst = powElementwiseArrayelt(v1lst, v2lst)
                      res2 = powElementwiseArrayelt(rest1, rest2)
                    _cons(Values.ARRAY(reslst, dims), res2)
                  end
                  
                  (Values.INTEGER(integer = i1) <| rest1, Values.INTEGER(integer = i2) <| rest2)  => begin
                      r1 = intReal(i1)
                      r2 = intReal(i2)
                      res = r1 ^ r2
                      res2 = powElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(res), res2)
                  end
                  
                  (Values.REAL(real = r1) <| rest1, Values.REAL(real = r2) <| rest2)  => begin
                      res = r1 ^ r2
                      res2 = powElementwiseArrayelt(rest1, rest2)
                    _cons(Values.REAL(res), res2)
                  end
                  
                  ( nil(),  nil())  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= Returns the value of constant expressions in DAE.Exp =#
        function expValue(inExp::DAE.Exp) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local b::Bool
                  local s::String
                @match inExp begin
                  DAE.ICONST(integer = i)  => begin
                    Values.INTEGER(i)
                  end
                  
                  DAE.RCONST(real = r)  => begin
                    Values.REAL(r)
                  end
                  
                  DAE.SCONST(string = s)  => begin
                    Values.STRING(s)
                  end
                  
                  DAE.BCONST(bool = b)  => begin
                    Values.BOOL(b)
                  end
                end
              end
          outValue
        end

         #= Transforms a Value into an Exp =#
        function valueExp(inValue::Values.Value) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local dim::ModelicaInteger
                  local explist::List{DAE.Exp}
                  local vt::DAE.Type
                  local t::DAE.Type
                  local e::DAE.Exp
                  local v::Values.Value
                  local xs::List{Values.Value}
                  local xs2::List{Values.Value}
                  local vallist::List{Values.Value}
                  local typelist::List{DAE.Type}
                  local int_dims::List{ModelicaInteger}
                  local dims::DAE.Dimensions
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local s::String
                  local scope::String
                  local name::String
                  local tyStr::String
                  local b::Bool
                  local expl::List{DAE.Exp}
                  local tpl::List{DAE.Type}
                  local namelst::List{String}
                  local varlst::List{DAE.Var}
                  local ix::ModelicaInteger
                  local path::Absyn.Path
                  local code::Absyn.CodeNode
                  local valType::Values.Value
                  local ety::DAE.Type
                @match inValue begin
                  Values.INTEGER(integer = i)  => begin
                    DAE.ICONST(i)
                  end
                  
                  Values.REAL(real = r)  => begin
                    DAE.RCONST(r)
                  end
                  
                  Values.STRING(string = s)  => begin
                    DAE.SCONST(s)
                  end
                  
                  Values.BOOL(boolean = b)  => begin
                    DAE.BCONST(b)
                  end
                  
                  Values.ENUM_LITERAL(name = path, index = i)  => begin
                    DAE.ENUM_LITERAL(path, i)
                  end
                  
                  Values.ARRAY(valueLst = vallist, dimLst = int_dims)  => begin
                    valueExpArray(vallist, int_dims)
                  end
                  
                  Values.TUPLE(valueLst = vallist)  => begin
                      explist = ListUtil.map(vallist, valueExp)
                    DAE.TUPLE(explist)
                  end
                  
                  Values.RECORD(path, vallist, namelst, #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#)  => begin
                      expl = ListUtil.map(vallist, valueExp)
                      tpl = ListUtil.map(expl, Expression.typeof)
                      varlst = ListUtil.threadMap(namelst, tpl, Expression.makeVar)
                      t = DAE.T_COMPLEX(ClassInf.RECORD(path), varlst, NONE())
                    DAE.RECORD(path, expl, namelst, t)
                  end
                  
                  Values.ENUM_LITERAL(name = path, index = ix)  => begin
                    DAE.ENUM_LITERAL(path, ix)
                  end
                  
                  Values.TUPLE(vallist)  => begin
                      explist = ListUtil.map(vallist, valueExp)
                    DAE.TUPLE(explist)
                  end
                  
                  Values.OPTION(SOME(v))  => begin
                      e = valueExp(v)
                      (e, _) = Types.matchType(e, Types.typeOfValue(v), DAE.T_METABOXED_DEFAULT, true)
                    DAE.META_OPTION(SOME(e))
                  end
                  
                  Values.OPTION(NONE())  => begin
                    DAE.META_OPTION(NONE())
                  end
                  
                  Values.META_TUPLE(vallist)  => begin
                      explist = ListUtil.map(vallist, valueExp)
                      typelist = ListUtil.map(vallist, Types.typeOfValue)
                      (explist, _) = Types.matchTypeTuple(explist, typelist, ListUtil.map(typelist, Types.boxIfUnboxedType), true)
                    DAE.META_TUPLE(explist)
                  end
                  
                  Values.LIST( nil())  => begin
                    DAE.LIST(nil)
                  end
                  
                  Values.LIST(vallist)  => begin
                      explist = ListUtil.map(vallist, valueExp)
                      typelist = ListUtil.map(vallist, Types.typeOfValue)
                      vt = Types.boxIfUnboxedType(ListUtil.reduce(typelist, Types.superType))
                      (explist, _) = Types.matchTypes(explist, typelist, vt, true)
                    DAE.LIST(explist)
                  end
                  
                  Values.META_ARRAY(vallist)  => begin
                      explist = ListUtil.map(vallist, valueExp)
                      typelist = ListUtil.map(vallist, Types.typeOfValue)
                      vt = Types.boxIfUnboxedType(ListUtil.reduce(typelist, Types.superType))
                      (explist, _) = Types.matchTypes(explist, typelist, vt, true)
                    Expression.makeBuiltinCall("listArrayLiteral", list(DAE.LIST(explist)), DAE.T_METAARRAY(vt), false)
                  end
                  
                  Values.RECORD(path, vallist, namelst, ix)  => begin
                      @match true = ix >= 0
                      explist = ListUtil.map(vallist, valueExp)
                      typelist = ListUtil.map(vallist, Types.typeOfValue)
                      (explist, _) = Types.matchTypeTuple(explist, typelist, ListUtil.map(typelist, Types.boxIfUnboxedType), true)
                    DAE.METARECORDCALL(path, explist, namelst, ix, nil)
                  end
                  
                  Values.META_FAIL(__)  => begin
                    DAE.CALL(Absyn.IDENT("fail"), nil, DAE.callAttrBuiltinOther)
                  end
                  
                  Values.META_BOX(v)  => begin
                      e = valueExp(v)
                    DAE.BOX(e)
                  end
                  
                  Values.CODE(A = code)  => begin
                    DAE.CODE(code, DAE.T_UNKNOWN_DEFAULT)
                  end
                  
                  Values.EMPTY(scope = scope, name = name, tyStr = tyStr, ty = valType)  => begin
                      ety = Types.simplifyType(Types.typeOfValue(valType))
                    DAE.EMPTY(scope, DAE.CREF_IDENT(name, ety, nil), ety, tyStr)
                  end
                  
                  Values.NORETCALL(__)  => begin
                    DAE.TUPLE(nil)
                  end
                  
                  v  => begin
                      s = "ValuesUtil.valueExp failed for " + valString(v)
                      Error.addMessage(Error.INTERNAL_ERROR, list(s))
                    fail()
                  end
                end
              end
               #= /* MetaModelica types */ =#
               #= /* MetaRecord */ =#
          outExp
        end

        function valueExpArray(values::List{<:Values.Value}, inDims::List{<:ModelicaInteger}) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local v::Values.Value
                  local xs::List{Values.Value}
                  local xs2::List{Values.Value}
                  local explist::List{DAE.Exp}
                  local dims::DAE.Dimensions
                  local int_dims::List{ModelicaInteger}
                  local t::DAE.Type
                  local vt::DAE.Type
                  local dim::ModelicaInteger
                  local i::ModelicaInteger
                  local b::Bool
                  local mexpl::List{List{DAE.Exp}}
                @matchcontinue (values, inDims) begin
                  ( nil(),  nil())  => begin
                    DAE.ARRAY(DAE.T_UNKNOWN_DEFAULT, false, nil)
                  end
                  
                  ( nil(), _)  => begin
                      dims = ListUtil.map(inDims, Expression.intDimension)
                    DAE.ARRAY(DAE.T_ARRAY(DAE.T_UNKNOWN_DEFAULT, dims), false, nil)
                  end
                  
                  (Values.ARRAY(valueLst = v <| xs) <| xs2, dim <| int_dims)  => begin
                      @shouldFail @match Values.ARRAY() = v
                      explist = ListUtil.map(_cons(v, xs), valueExp)
                      @match DAE.MATRIX(t, _, mexpl) = valueExp(Values.ARRAY(xs2, int_dims))
                      t = Expression.arrayDimensionSetFirst(t, DAE.DIM_INTEGER(dim))
                    DAE.MATRIX(t, dim, _cons(explist, mexpl))
                  end
                  
                  (Values.ARRAY(valueLst = v <| xs) <|  nil(), _)  => begin
                      @shouldFail @match Values.ARRAY() = v
                      dim = listLength(_cons(v, xs))
                      explist = ListUtil.map(_cons(v, xs), valueExp)
                      vt = Types.typeOfValue(v)
                      t = Types.simplifyType(vt)
                      dim = listLength(_cons(v, xs))
                      t = Expression.liftArrayR(t, DAE.DIM_INTEGER(dim))
                      t = Expression.liftArrayR(t, DAE.DIM_INTEGER(1))
                    DAE.MATRIX(t, dim, list(explist))
                  end
                  
                  (v <| xs, _)  => begin
                      explist = ListUtil.map(_cons(v, xs), valueExp)
                      vt = Types.typeOfValue(v)
                      t = Types.simplifyType(vt)
                      dim = listLength(_cons(v, xs))
                      t = Expression.liftArrayR(t, DAE.DIM_INTEGER(dim))
                      b = Types.isArray(vt)
                      b = boolNot(b)
                    DAE.ARRAY(t, b, explist)
                  end
                end
              end
               #=  Matrix
               =#
               #=  Matrix last row
               =#
               #=  Generic array
               =#
          outExp
        end

         #= 
          Return the real value of a Value. If the value is an integer,
          it is cast to a real.
         =#
        function valueReal(inValue::Values.Value) ::ModelicaReal 
              local outReal::ModelicaReal

              outReal = begin
                @match inValue begin
                  Values.REAL(__)  => begin
                    inValue.real
                  end
                  
                  Values.INTEGER(__)  => begin
                    intReal(inValue.integer)
                  end
                end
              end
          outReal
        end

         #= Author: BZ, 2008-09
          Return the bool value of a Value.
         =#
        function valueBool(inValue::Values.Value) ::Bool 
              local outBool::Bool

              @match Values.BOOL(boolean = outBool) = inValue
          outBool
        end

         #= 
          Return the real value of a Value. If the value is an integer,
          it is cast to a real.
         =#
        function valueReals(inValue::List{<:Values.Value}) ::List{ModelicaReal} 
              local outReal::List{ModelicaReal}

              outReal = begin
                  local r::ModelicaReal
                  local rest::List{Values.Value}
                  local res::List{ModelicaReal}
                  local i::ModelicaInteger
                @matchcontinue inValue begin
                   nil()  => begin
                    nil
                  end
                  
                  Values.REAL(real = r) <| rest  => begin
                      res = valueReals(rest)
                    _cons(r, res)
                  end
                  
                  Values.INTEGER(integer = i) <| rest  => begin
                      r = intReal(i)
                      res = valueReals(rest)
                    _cons(r, res)
                  end
                  
                  _ <| rest  => begin
                      res = valueReals(rest)
                    res
                  end
                end
              end
          outReal
        end

         #= Returns the integer values of a Values array. =#
        function arrayValueInts(inValue::Values.Value) ::List{ModelicaInteger} 
              local outReal::List{ModelicaInteger}

              local vals::List{Values.Value}

              @match Values.ARRAY(valueLst = vals) = inValue
              outReal = ListUtil.map(vals, valueInteger)
          outReal
        end

         #= 
          Return the real value of a Value. If the value is an integer,
          it is cast to a real.
         =#
        function arrayValueReals(inValue::Values.Value) ::List{ModelicaReal} 
              local outReal::List{ModelicaReal}

              local vals::List{Values.Value}

              @match Values.ARRAY(valueLst = vals) = inValue
              outReal = valueReals(vals)
          outReal
        end

         #= Returns the real values of a Values matrix. =#
        function matrixValueReals(inValue::Values.Value) ::List{List{ModelicaReal}} 
              local outReals::List{List{ModelicaReal}}

              outReals = begin
                  local vals::List{Values.Value}
                  local reals::List{ModelicaReal}
                   #=  A matrix.
                   =#
                @matchcontinue inValue begin
                  Values.ARRAY(valueLst = vals)  => begin
                    ListUtil.map(vals, arrayValueReals)
                  end
                  
                  Values.ARRAY(valueLst = vals)  => begin
                      reals = valueReals(vals)
                    ListUtil.map(reals, ListUtil.create)
                  end
                end
              end
               #=  A 1-dimensional array.
               =#
          outReals
        end

         #= author: PA

          Negates a Value
         =#
        function valueNeg(inValue::Values.Value) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local r_1::ModelicaReal
                  local r::ModelicaReal
                  local i_1::ModelicaInteger
                  local i::ModelicaInteger
                  local vlst_1::List{Values.Value}
                  local vlst::List{Values.Value}
                  local dims::List{ModelicaInteger}
                @match inValue begin
                  Values.REAL(real = r)  => begin
                      r_1 = -r
                    Values.REAL(r_1)
                  end
                  
                  Values.INTEGER(integer = i)  => begin
                      i_1 = -i
                    Values.INTEGER(i_1)
                  end
                  
                  Values.ARRAY(valueLst = vlst, dimLst = dims)  => begin
                      vlst_1 = ListUtil.map(vlst, valueNeg)
                    Values.ARRAY(vlst_1, dims)
                  end
                end
              end
          outValue
        end

         #= Calculates the sum of two scalar values. =#
        function valueSum(value1::Values.Value, value2::Values.Value) ::Values.Value 
              local result::Values.Value

              result = begin
                @match (value1, value2) begin
                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    Values.INTEGER(value1.integer + value2.integer)
                  end
                  
                  (Values.STRING(__), Values.STRING(__))  => begin
                    Values.STRING(value1.string + value2.string)
                  end
                  
                  _  => begin
                      Values.REAL(valueReal(value1) + valueReal(value2))
                  end
                end
              end
          result
        end

         #= Calculates the difference of two scalar values. =#
        function valueSubtract(value1::Values.Value, value2::Values.Value) ::Values.Value 
              local result::Values.Value

              result = begin
                @match (value1, value2) begin
                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    Values.INTEGER(value1.integer - value2.integer)
                  end
                  
                  _  => begin
                      Values.REAL(valueReal(value1) - valueReal(value2))
                  end
                end
              end
          result
        end

         #= Calculates the product of two scalar values. =#
        function valueMultiply(value1::Values.Value, value2::Values.Value) ::Values.Value 
              local result::Values.Value

              result = begin
                @match (value1, value2) begin
                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    Values.INTEGER(value1.integer * value2.integer)
                  end
                  
                  _  => begin
                      Values.REAL(valueReal(value1) * valueReal(value2))
                  end
                end
              end
          result
        end

         #= Calculates the quotient of two scalar values. =#
        function valueDivide(value1::Values.Value, value2::Values.Value) ::Values.Value 
              local result::Values.Value

              result = begin
                @match (value1, value2) begin
                  (_, Values.INTEGER(integer = 0))  => begin
                      Error.addMessage(Error.DIVISION_BY_ZERO, list("0", intString(value2.integer)))
                    fail()
                  end
                  
                  (_, Values.REAL(real = 0.0))  => begin
                      Error.addMessage(Error.DIVISION_BY_ZERO, list("0", realString(value2.real)))
                    fail()
                  end
                  
                  _  => begin
                      Values.REAL(valueReal(value1) / valueReal(value2))
                  end
                end
              end
          result
        end

         #= Calculates the power of two scalar values. =#
        function valuePow(value1::Values.Value, value2::Values.Value) ::Values.Value 
              local result::Values.Value

              result = Values.REAL(valueReal(value1) ^ valueReal(value2))
          result
        end

        function sumArray(value::Values.Value) ::Values.Value 
              local result::Values.Value

              result = begin
                @match value begin
                  Values.ARRAY(__)  => begin
                    sumArrayelt(value.valueLst)
                  end
                  
                  _  => begin
                      value
                  end
                end
              end
          result
        end

         #= Calculate the sum of a list of Values. =#
        function sumArrayelt(values::List{<:Values.Value}) ::Values.Value 
              local result::Values.Value

              result = sumArray(listHead(values))
              for v in listRest(values)
                result = valueSum(sumArray(v), result)
              end
          result
        end

         #= Multiply a scalar with an list of Values, i.e. array. =#
        function multScalarArrayelt(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(multScalarArrayelt(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueMultiply(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Adds a scalar to an list of Values, i.e. array. =#
        function addScalarArrayelt(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(addScalarArrayelt(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueSum(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Subtracts a list of Values, i.e. array, from a scalar. =#
        function subScalarArrayelt(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(subScalarArrayelt(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueSubtract(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Subtracts a scalar from a list of Values, i.e. array. =#
        function subArrayeltScalar(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(subArrayeltScalar(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueSubtract(v, scalarValue)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Divides a scalar with a list of Values, i.e. array. =#
        function divScalarArrayelt(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(divScalarArrayelt(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueDivide(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Divides each array element with a scalar. =#
        function divArrayeltScalar(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(divArrayeltScalar(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valueDivide(v, scalarValue)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Takes a power of a scalar with a list of Values, i.e. array. =#
        function powScalarArrayelt(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(powScalarArrayelt(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valuePow(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= Takes a power of a scalar with a list of Values, i.e. array. =#
        function powArrayeltScalar(scalarValue::Values.Value, arrayValues::List{<:Values.Value}) ::List{Values.Value} 
              local result::List{Values.Value}

              result = list(begin
                @match v begin
                  Values.ARRAY(__)  => begin
                    Values.ARRAY(powArrayeltScalar(scalarValue, v.valueLst), v.dimLst)
                  end
                  
                  _  => begin
                      valuePow(scalarValue, v)
                  end
                end
              end for v in arrayValues)
          result
        end

         #= 
          Calculate the scalar product of two vectors / arrays.
         =#
        function multScalarProduct(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local res::ModelicaInteger
                  local v1::ModelicaInteger
                  local v2::ModelicaInteger
                  local dim::ModelicaInteger
                  local v1lst::List{Values.Value}
                  local v2lst::List{Values.Value}
                  local vres::List{Values.Value}
                  local rest::List{Values.Value}
                  local vlst::List{Values.Value}
                  local col::List{Values.Value}
                  local mat_1::List{Values.Value}
                  local vals::List{Values.Value}
                  local mat::List{Values.Value}
                  local lst1::List{Values.Value}
                  local lst2::List{Values.Value}
                  local sres::Values.Value
                  local v::Values.Value
                  local dims::List{ModelicaInteger}
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local rres::ModelicaReal
                @matchcontinue (inValueLst1, inValueLst2) begin
                  (Values.INTEGER(integer = i1) <| v1lst && _ <| _, Values.INTEGER(integer = i2) <| v2lst && _ <| _)  => begin
                      i1 = i1 * i2
                      @match Values.INTEGER(i2) = multScalarProduct(v1lst, v2lst)
                      res = i1 + i2
                    Values.INTEGER(res)
                  end
                  
                  (Values.INTEGER(integer = v1) <|  nil(), Values.INTEGER(integer = v2) <|  nil())  => begin
                      res = v1 * v2
                    Values.INTEGER(res)
                  end
                  
                  (Values.REAL(real = r1) <| v1lst && _ <| _, Values.REAL(real = r2) <| v2lst && _ <| _)  => begin
                      r1 = r1 * r2
                      @match Values.REAL(r2) = multScalarProduct(v1lst, v2lst)
                      rres = r1 + r2
                    Values.REAL(rres)
                  end
                  
                  (Values.REAL(real = r1) <|  nil(), Values.REAL(real = r2) <|  nil())  => begin
                      rres = r1 * r2
                    Values.REAL(rres)
                  end
                  
                  (Values.ARRAY(valueLst = v2lst) <| rest, vlst && Values.INTEGER(__) <| _)  => begin
                      sres = multScalarProduct(v2lst, vlst)
                      @match Values.ARRAY(vres, _cons(dim, dims)) = multScalarProduct(rest, vlst)
                      dim = dim + 1
                    Values.ARRAY(_cons(sres, vres), _cons(dim, dims))
                  end
                  
                  ( nil(), Values.INTEGER(__) <| _)  => begin
                    makeArray(nil)
                  end
                  
                  (Values.ARRAY(valueLst = v2lst) <| rest, vlst && Values.REAL(__) <| _)  => begin
                      sres = multScalarProduct(v2lst, vlst)
                      @match Values.ARRAY(vres, _cons(dim, dims)) = multScalarProduct(rest, vlst)
                      dim = dim + 1
                    Values.ARRAY(_cons(sres, vres), _cons(dim, dims))
                  end
                  
                  ( nil(), Values.REAL(__) <| _)  => begin
                    makeArray(nil)
                  end
                  
                  (vlst && Values.INTEGER(__) <| _, mat && Values.ARRAY(valueLst = _ <| _ <| _) <| _)  => begin
                      @match (Values.ARRAY(valueLst = col), mat_1) = matrixStripFirstColumn(mat)
                      v = multScalarProduct(vlst, col)
                      @match Values.ARRAY(vals, _cons(dim, dims)) = multScalarProduct(vlst, mat_1)
                    Values.ARRAY(_cons(v, vals), _cons(dim, dims))
                  end
                  
                  (vlst && Values.INTEGER(__) <| _, mat && Values.ARRAY(valueLst = _ <|  nil()) <| _)  => begin
                      @match (Values.ARRAY(valueLst = col), _) = matrixStripFirstColumn(mat)
                      @match Values.INTEGER(i1) = multScalarProduct(vlst, col)
                    makeArray(list(Values.INTEGER(i1)))
                  end
                  
                  (vlst && Values.REAL(__) <| _, mat && Values.ARRAY(valueLst = _ <| _ <| _) <| _)  => begin
                      @match (Values.ARRAY(valueLst = col), mat_1) = matrixStripFirstColumn(mat)
                      v = multScalarProduct(vlst, col)
                      @match Values.ARRAY(valueLst = vals, dimLst = _cons(dim, dims)) = multScalarProduct(vlst, mat_1)
                      dim = dim + 1
                    Values.ARRAY(_cons(v, vals), _cons(dim, dims))
                  end
                  
                  (vlst && Values.REAL(__) <| _, mat && Values.ARRAY(valueLst = _ <|  nil()) <| _)  => begin
                      @match (Values.ARRAY(valueLst = col), _) = matrixStripFirstColumn(mat)
                      @match Values.REAL(r1) = multScalarProduct(vlst, col)
                    makeArray(list(Values.REAL(r1)))
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("Values.multScalarProduct failed\\n")
                      fail()
                  end
                end
              end
          outValue
        end

         #= 
          Calculate the cross product of two vectors.
          x,y => {x[2]*y[3]-x[3]*y[2],x[3]*y[1]-x[1]*y[3],x[1]*y[2]-x[2]*y[1]}
         =#
        function crossProduct(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local ix1::ModelicaInteger
                  local ix2::ModelicaInteger
                  local ix3::ModelicaInteger
                  local iy1::ModelicaInteger
                  local iy2::ModelicaInteger
                  local iy3::ModelicaInteger
                  local iz1::ModelicaInteger
                  local iz2::ModelicaInteger
                  local iz3::ModelicaInteger
                  local x1::ModelicaReal
                  local x2::ModelicaReal
                  local x3::ModelicaReal
                  local y1::ModelicaReal
                  local y2::ModelicaReal
                  local y3::ModelicaReal
                  local z1::ModelicaReal
                  local z2::ModelicaReal
                  local z3::ModelicaReal
                @match (inValueLst1, inValueLst2) begin
                  (Values.REAL(x1) <| Values.REAL(x2) <| Values.REAL(x3) <|  nil(), Values.REAL(y1) <| Values.REAL(y2) <| Values.REAL(y3) <|  nil())  => begin
                      z1 = realSub(realMul(x2, y3), realMul(x3, y2))
                      z2 = realSub(realMul(x3, y1), realMul(x1, y3))
                      z3 = realSub(realMul(x1, y2), realMul(x2, y1))
                    makeArray(list(Values.REAL(z1), Values.REAL(z2), Values.REAL(z3)))
                  end
                  
                  (Values.INTEGER(ix1) <| Values.INTEGER(ix2) <| Values.INTEGER(ix3) <|  nil(), Values.INTEGER(iy1) <| Values.INTEGER(iy2) <| Values.INTEGER(iy3) <|  nil())  => begin
                      iz1 = intSub(intMul(ix2, iy3), intMul(ix3, iy2))
                      iz2 = intSub(intMul(ix3, iy1), intMul(ix1, iy3))
                      iz3 = intSub(intMul(ix1, iy2), intMul(ix2, iy1))
                    makeArray(list(Values.INTEGER(iz1), Values.INTEGER(iz2), Values.INTEGER(iz3)))
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("ValuesUtil.crossProduct failed"))
                      fail()
                  end
                end
              end
          outValue
        end

         #= 
          Calculate a matrix multiplication of two matrices, i.e. two dimensional
          arrays.
         =#
        function multMatrix(inValueLst1::List{<:Values.Value}, inValueLst2::List{<:Values.Value}) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local res1::Values.Value
                  local res2::List{Values.Value}
                  local m1::List{Values.Value}
                  local v1lst::List{Values.Value}
                  local rest1::List{Values.Value}
                  local m2::List{Values.Value}
                @match (inValueLst1, inValueLst2) begin
                  (Values.ARRAY(valueLst = v1lst) <| rest1, m2 && Values.ARRAY(__) <| _)  => begin
                      res1 = multScalarProduct(v1lst, m2)
                      res2 = multMatrix(rest1, m2)
                    _cons(res1, res2)
                  end
                  
                  ( nil(), _)  => begin
                    nil
                  end
                end
              end
          outValueLst
        end

         #= This function takes a Value list representing a matrix and strips the
          first column of the matrix, i.e. for each sub list it removes the first
          element. Returning both the stripped column and the resulting matrix. =#
        function matrixStripFirstColumn(inValueLst::List{<:Values.Value}) ::Tuple{Values.Value, List{Values.Value}} 
              local outValueLst::List{Values.Value}
              local outValue::Values.Value

              (outValue, outValueLst) = begin
                  local resl::List{Values.Value}
                  local resl2::List{Values.Value}
                  local vrest::List{Values.Value}
                  local rest::List{Values.Value}
                  local v1::Values.Value
                  local i::ModelicaInteger
                  local dim::ModelicaInteger
                @match inValueLst begin
                  Values.ARRAY(valueLst = v1 <| vrest, dimLst = dim <|  nil()) <| rest  => begin
                      @match (Values.ARRAY(resl, list(i)), resl2) = matrixStripFirstColumn(rest)
                      i = i + 1
                      dim = dim - 1
                    (Values.ARRAY(_cons(v1, resl), list(i)), _cons(Values.ARRAY(vrest, list(dim)), resl2))
                  end
                  
                   nil()  => begin
                    (Values.ARRAY(nil, list(0)), nil)
                  end
                end
              end
          (outValue, outValueLst)
        end

         #= 
          Takes a list of integers and builds a Value from it, i.e. an
          array of integers.
         =#
        function intlistToValue(inIntegerLst::List{<:ModelicaInteger}) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local res::List{Values.Value}
                  local i::ModelicaInteger
                  local len::ModelicaInteger
                  local lst::List{ModelicaInteger}
                @match inIntegerLst begin
                   nil()  => begin
                    Values.ARRAY(nil, list(0))
                  end
                  
                  i <| lst  => begin
                      @match Values.ARRAY(res, list(len)) = intlistToValue(lst)
                      len = len + 1
                    Values.ARRAY(_cons(Values.INTEGER(i), res), list(len))
                  end
                end
              end
          outValue
        end

         #= 
          Return the values of an array.
         =#
        function arrayValues(inValue::Values.Value) ::List{Values.Value} 
              local outValueLst::List{Values.Value}

              outValueLst = begin
                  local v_lst::List{Values.Value}
                @match inValue begin
                  Values.ARRAY(valueLst = v_lst)  => begin
                    v_lst
                  end
                end
              end
          outValueLst
        end

         #= If an array contains only one value, returns that value. Otherwise fails. =#
        function arrayScalar(inValue::Values.Value) ::Values.Value 
              local outValue::Values.Value

              @match Values.ARRAY(valueLst = list(outValue)) = inValue
          outValue
        end

        function makeBoolean(b::Bool) ::Values.Value 
              local v::Values.Value

              v = Values.BOOL(b)
          v
        end

         #= Creates a real value  =#
        function makeReal(r::ModelicaReal) ::Values.Value 
              local v::Values.Value

              v = Values.REAL(r)
          v
        end

         #= Creates an integer value  =#
        function makeInteger(i::ModelicaInteger) ::Values.Value 
              local v::Values.Value

              v = Values.INTEGER(i)
          v
        end

         #= Creates a string value  =#
        function makeString(s::String) ::Values.Value 
              local v::Values.Value

              v = Values.STRING(s)
          v
        end

         #= Construct a tuple of a list of Values. =#
        function makeTuple(inValueLst::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = Values.TUPLE(inValueLst)
          outValue
        end

         #= Construct a list from a list of Values. =#
        function makeList(inValueLst::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = Values.LIST(inValueLst)
          outValue
        end

         #= 
          Construct an array of a list of Values.
         =#
        function makeArray(inValueLst::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local i1::ModelicaInteger
                  local il::List{ModelicaInteger}
                  local vlst::List{Values.Value}
                @matchcontinue inValueLst begin
                  vlst && Values.ARRAY(dimLst = il) <| _  => begin
                      i1 = listLength(vlst)
                    Values.ARRAY(vlst, _cons(i1, il))
                  end
                  
                  vlst  => begin
                      i1 = listLength(vlst)
                    Values.ARRAY(vlst, list(i1))
                  end
                end
              end
          outValue
        end

         #= Creates a Values.ARRAY from a list of Strings. =#
        function makeStringArray(inReals::List{<:String}) ::Values.Value 
              local outArray::Values.Value

              outArray = makeArray(ListUtil.map(inReals, makeString))
          outArray
        end

         #= Creates a Value.ARRAY from a list of integers. =#
        function makeIntArray(inInts::List{<:ModelicaInteger}) ::Values.Value 
              local outArray::Values.Value

              outArray = makeArray(ListUtil.map(inInts, makeInteger))
          outArray
        end

         #= Creates a Values.ARRAY from a list of reals. =#
        function makeRealArray(inReals::List{<:ModelicaReal}) ::Values.Value 
              local outArray::Values.Value

              outArray = makeArray(ListUtil.map(inReals, makeReal))
          outArray
        end

         #= Creates a matrix (ARRAY of ARRAY) from a list of list of reals. =#
        function makeRealMatrix(inReals::List{<:List{<:ModelicaReal}}) ::Values.Value 
              local outArray::Values.Value

              outArray = makeArray(ListUtil.map(inReals, makeRealArray))
          outArray
        end

         #= This function returns a textual representation of a value. =#
        function valString(inValue::Values.Value) ::String 
              local outString::String

              local handle::ModelicaInteger

              handle = Print.saveAndClearBuf()
              valString2(inValue)
              outString = Print.getString()
              Print.restoreBuf(handle)
          outString
        end

         #= This function returns a textual representation of a value.
          Uses an external buffer to store intermediate results. =#
        function valString2(inValue::Values.Value)  
              _ = begin
                  local s::String
                  local s_1::String
                  local recordName::String
                  local tyStr::String
                  local scope::String
                  local name::String
                  local n::ModelicaInteger
                  local x::ModelicaReal
                  local xs::List{Values.Value}
                  local vs::List{Values.Value}
                  local r::Values.Value
                  local c::Absyn.CodeNode
                  local p::Absyn.Path
                  local recordPath::Absyn.Path
                  local ids::List{String}
                  local cr::Absyn.ComponentRef
                  local path::Absyn.Path
                @matchcontinue inValue begin
                  Values.INTEGER(integer = n)  => begin
                      s = intString(n)
                      Print.printBuf(s)
                    ()
                  end
                  
                  Values.REAL(real = x)  => begin
                      s = realString(x)
                      Print.printBuf(s)
                    ()
                  end
                  
                  Values.STRING(string = s)  => begin
                      s = System.escapedString(s, false)
                      s_1 = stringAppendList(list("\\", s, "\\"))
                      Print.printBuf(s_1)
                    ()
                  end
                  
                  Values.BOOL(boolean = false)  => begin
                      Print.printBuf("false")
                    ()
                  end
                  
                  Values.BOOL(boolean = true)  => begin
                      Print.printBuf("true")
                    ()
                  end
                  
                  Values.ENUM_LITERAL(name = p)  => begin
                      s = AbsynUtil.pathString(p)
                      Print.printBuf(s)
                    ()
                  end
                  
                  Values.ARRAY(valueLst = vs)  => begin
                      Print.printBuf("{")
                      valListString(vs)
                      Print.printBuf("}")
                    ()
                  end
                  
                  Values.TUPLE(valueLst =  nil())  => begin
                    ()
                  end
                  
                  Values.TUPLE(valueLst = vs)  => begin
                      Print.printBuf("(")
                      valListString(vs)
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.META_TUPLE(valueLst =  nil())  => begin
                    ()
                  end
                  
                  Values.META_TUPLE(valueLst = vs)  => begin
                      Print.printBuf("(")
                      valListString(vs)
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.RECORD(record_ = Absyn.IDENT("SimulationResult"), orderd = xs, comp = ids)  => begin
                      Print.printBuf("record SimulationResult\\n")
                      (xs, ids) = filterSimulationResults(Flags.isSet(Flags.SHORT_OUTPUT), xs, ids, nil, nil)
                      valRecordString(xs, ids)
                      Print.printBuf("end SimulationResult;")
                    ()
                  end
                  
                  Values.RECORD(record_ = recordPath, orderd = xs, comp = ids)  => begin
                      recordName = AbsynUtil.pathStringNoQual(recordPath)
                      Print.printBuf("record " + recordName + "\\n")
                      valRecordString(xs, ids)
                      Print.printBuf("end " + recordName + ";")
                    ()
                  end
                  
                  Values.OPTION(SOME(r))  => begin
                      Print.printBuf("SOME(")
                      valString2(r)
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.OPTION(NONE())  => begin
                      Print.printBuf("NONE()")
                    ()
                  end
                  
                  Values.META_BOX(r)  => begin
                      Print.printBuf("#(")
                      valString2(r)
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.CODE(A = Absyn.C_TYPENAME(path))  => begin
                      Print.printBuf(AbsynUtil.pathString(path))
                    ()
                  end
                  
                  Values.CODE(A = Absyn.C_VARIABLENAME(cr))  => begin
                      Print.printBuf(AbsynUtil.printComponentRefStr(cr))
                    ()
                  end
                  
                  Values.CODE(A = c)  => begin
                      Print.printBuf("Code(")
                      Print.printBuf(Dump.printCodeStr(c))
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.LIST(valueLst = vs)  => begin
                      Print.printBuf("{")
                      valListString(vs)
                      Print.printBuf("}")
                    ()
                  end
                  
                  Values.META_ARRAY(valueLst = vs)  => begin
                      Print.printBuf("meta_array(")
                      valListString(vs)
                      Print.printBuf(")")
                    ()
                  end
                  
                  Values.ENUM_LITERAL(index = n, name = p)  => begin
                      s = intString(n) + " /* ENUM: " + AbsynUtil.pathString(p) + " */"
                      Print.printBuf(s)
                    ()
                  end
                  
                  Values.NORETCALL(__)  => begin
                    ()
                  end
                  
                  Values.META_FAIL(__)  => begin
                      Print.printBuf("fail()")
                    ()
                  end
                  
                  Values.EMPTY(scope = scope, name = name, tyStr = tyStr)  => begin
                      Print.printBuf("/* <EMPTY(scope: " + scope + ", name: " + name + ", ty: " + tyStr + ")> */")
                    ()
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("ValuesUtil.valString2 failed"))
                      fail()
                  end
                end
              end
               #=  MetaModelica list
               =#
               #=  MetaModelica array
               =#
               #= /* Until is it no able to get from an string Enumeration the C-Enumeration use the index value */ =#
               #= /* Example: This is yet not possible Enum.e1 \\\\ PEnum   ->  1 \\\\ PEnum  with enum Enum(e1,e2), Enum PEnum; */ =#
        end

        function filterSimulationResults(filter::Bool, inValues::List{<:Values.Value}, inIds::List{<:String}, valacc::List{<:Values.Value}, idacc::List{<:String}) ::Tuple{List{Values.Value}, List{String}} 
              local outIds::List{String}
              local outValues::List{Values.Value}

              (outValues, outIds) = begin
                  local v::Values.Value
                  local vrest::List{Values.Value}
                  local id::String
                  local str::String
                  local idrest::List{String}
                @match (filter, inValues, inIds, valacc, idacc) begin
                  (_,  nil(),  nil(), _, _)  => begin
                    (listReverse(valacc), listReverse(idacc))
                  end
                  
                  (true, v <| vrest, id && "messages" <| idrest, _, _)  => begin
                      (outValues, outIds) = filterSimulationResults(filter, vrest, idrest, _cons(v, valacc), _cons(id, idacc))
                    (outValues, outIds)
                  end
                  
                  (true, Values.STRING(str) <| vrest, id && "resultFile" <| idrest, _, _)  => begin
                      str = System.basename(str)
                      (outValues, outIds) = filterSimulationResults(filter, vrest, idrest, _cons(Values.STRING(str), valacc), _cons(id, idacc))
                    (outValues, outIds)
                  end
                  
                  (true, _ <| vrest, _ <| idrest, _, _)  => begin
                      (outValues, outIds) = filterSimulationResults(filter, vrest, idrest, valacc, idacc)
                    (outValues, outIds)
                  end
                  
                  (false, _, _, _, _)  => begin
                    (inValues, inIds)
                  end
                end
              end
          (outValues, outIds)
        end

         #= This function returns a textual representation of a record,
         separating each value with a comma. =#
        function valRecordString(inValues::List{<:Values.Value}, inIds::List{<:String})  
              _ = begin
                  local id::String
                  local x::Values.Value
                  local xs::List{Values.Value}
                  local ids::List{String}
                @matchcontinue (inValues, inIds) begin
                  ( nil(),  nil())  => begin
                    ()
                  end
                  
                  (x <| xs && _ <| _, id <| ids && _ <| _)  => begin
                      Print.printBuf("    ")
                      Print.printBuf(id)
                      Print.printBuf(" = ")
                      valString2(x)
                      Print.printBuf(",\\n")
                      valRecordString(xs, ids)
                    ()
                  end
                  
                  (x <|  nil(), id <|  nil())  => begin
                      Print.printBuf("    ")
                      Print.printBuf(id)
                      Print.printBuf(" = ")
                      valString2(x)
                      Print.printBuf("\\n")
                    ()
                  end
                  
                  (xs, ids)  => begin
                      print("ValuesUtil.valRecordString failed:\\nids: " + stringDelimitList(ids, ", ") + "\\nvals: " + stringDelimitList(ListUtil.map(xs, valString), ", ") + "\\n")
                    fail()
                  end
                end
              end
        end

         #= 
          This function returns a textual representation of a list of
          values, separating each value with a comman.
         =#
        function valListString(inValueLst::List{<:Values.Value})  
              _ = begin
                  local v::Values.Value
                  local vs::List{Values.Value}
                @match inValueLst begin
                   nil()  => begin
                    ()
                  end
                  
                  v <|  nil()  => begin
                      valString2(v)
                    ()
                  end
                  
                  v <| vs  => begin
                      valString2(v)
                      Print.printBuf(",")
                      valListString(vs)
                    ()
                  end
                end
              end
        end

         #= 
          This function writes a data set in the pltolemy plot format to a file.
          The first column of the dataset matrix should be the time variable.
          The message string will be displayed in the plot window of ptplot.
         =#
        function writePtolemyplotDataset(inString1::String, inValue2::Values.Value, inStringLst3::List{<:String}, inString4::String) ::ModelicaInteger 
              local outInteger::ModelicaInteger

              outInteger = begin
                  local str::String
                  local filename::String
                  local timevar::String
                  local message::String
                  local t::Values.Value
                  local rest::List{Values.Value}
                  local varnames::List{String}
                  local handle::ModelicaInteger
                @match (inString1, inValue2, inStringLst3, inString4) begin
                  (filename, Values.ARRAY(valueLst = t <| rest), _ <| varnames, message)  => begin
                      handle = Print.saveAndClearBuf()
                      Print.printBuf("#Ptolemy Plot generated by OpenModelica\\nTitleText: ")
                      Print.printBuf(message)
                      Print.printBuf("\\n")
                      unparsePtolemyValues(t, rest, varnames)
                      str = Print.getString()
                      Print.restoreBuf(handle)
                      System.writeFile(filename, str)
                    0
                  end
                end
              end
               #= /* filename values Variable names message string */ =#
          outInteger
        end

         #= Helper function to writePtolemyplotDataset. =#
        function unparsePtolemyValues(inValue::Values.Value, inValueLst::List{<:Values.Value}, inStringLst::List{<:String})  
              _ = begin
                  local v1::String
                  local t::Values.Value
                  local s1::Values.Value
                  local xs::List{Values.Value}
                  local vs::List{String}
                @match (inValue, inValueLst, inStringLst) begin
                  (_,  nil(), _)  => begin
                    ()
                  end
                  
                  (t, s1 <| xs, v1 <| vs)  => begin
                      unparsePtolemySet(t, s1, v1)
                      unparsePtolemyValues(t, xs, vs)
                    ()
                  end
                end
              end
        end

         #= Helper function to unparsePtolemyValues. =#
        function unparsePtolemySet(v1::Values.Value, v2::Values.Value, varname::String)  
              Print.printBuf(stringAppendList(list("DataSet: ", varname, "\\n")))
              unparsePtolemySet2(v1, v2)
        end

         #= Helper function to unparsePtolemySet =#
        function unparsePtolemySet2(inValue1::Values.Value, inValue2::Values.Value)  
              _ = begin
                  local v1::Values.Value
                  local v2::Values.Value
                  local v1s::List{Values.Value}
                  local v2s::List{Values.Value}
                @matchcontinue (inValue1, inValue2) begin
                  (Values.ARRAY(valueLst =  nil()), Values.ARRAY(valueLst =  nil()))  => begin
                    ()
                  end
                  
                  (Values.ARRAY(valueLst = v1 <| v1s), Values.ARRAY(valueLst = v2 <| v2s))  => begin
                      valString2(v1)
                      Print.printBuf(",")
                      valString2(v2)
                      Print.printBuf("\\n")
                      unparsePtolemySet2(Values.ARRAY(v1s, nil), Values.ARRAY(v2s, nil))
                    ()
                  end
                  
                  (v1, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- ValuesUtil.unparsePtolemySet2 failed on v1: " + printValStr(v1) + " and v2: " + printValStr(v1))
                    fail()
                  end
                end
              end
               #=  adrpo: ignore dimenstions here as we're just printing! otherwise it fails.
               =#
               #=         TODO! FIXME! see why the dimension list is wrong!
               =#
        end

         #= Reverses each line and each row of a matrix.
          Implementation reverses all dimensions... =#
        function reverseMatrix(inValue::Values.Value) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local lst_1::List{Values.Value}
                  local lst_2::List{Values.Value}
                  local lst::List{Values.Value}
                  local value::Values.Value
                  local dims::List{ModelicaInteger}
                @matchcontinue inValue begin
                  Values.ARRAY(valueLst = lst, dimLst = dims)  => begin
                      lst_1 = ListUtil.map(lst, reverseMatrix)
                      lst_2 = listReverse(lst_1)
                    Values.ARRAY(lst_2, dims)
                  end
                  
                  value  => begin
                    value
                  end
                end
              end
          outValue
        end

         #= This function prints a value. =#
        function printVal(v::Values.Value)  
              local s::String

              s = valString(v)
              Print.printBuf(s)
        end

         #= 
        more correct naming then valString =#
        function printValStr(v::Values.Value) ::String 
              local s::String

              s = valString(v)
          s
        end

         #= author: BZ

          Return the nth nth....nth value of an array, indexed from 1..n
         =#
        function nthnthArrayelt(inLst::List{<:Values.Value}, inValue::Values.Value, lastValue::Values.Value) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local b::Bool
                  local n::ModelicaInteger
                  local res::Values.Value
                  local preRes::Values.Value
                  local vlst::List{Values.Value}
                  local vlst2::List{Values.Value}
                @match (inLst, inValue, lastValue) begin
                  ( nil(), _, preRes)  => begin
                    preRes
                  end
                  
                  (Values.INTEGER(integer = n) <| vlst2, Values.ARRAY(valueLst = vlst), _)  => begin
                      res = listGet(vlst, n)
                      res = nthnthArrayelt(vlst2, res, res)
                    res
                  end
                  
                  (Values.ENUM_LITERAL(index = n) <| vlst2, Values.ARRAY(valueLst = vlst), _)  => begin
                      res = listGet(vlst, n)
                      res = nthnthArrayelt(vlst2, res, res)
                    res
                  end
                  
                  (Values.BOOL(boolean = b) <| vlst2, Values.ARRAY(valueLst = vlst), _)  => begin
                      res = listGet(vlst, if b
                            2
                          else
                            1
                          end)
                      res = nthnthArrayelt(vlst2, res, res)
                    res
                  end
                end
              end
          outValue
        end

         #= Converts a value to an Integer, or fails if that is not possible. =#
        function valueInteger(inValue::Values.Value) ::ModelicaInteger 
              local outInteger::ModelicaInteger

              outInteger = begin
                  local i::ModelicaInteger
                @match inValue begin
                  Values.INTEGER(integer = i)  => begin
                    i
                  end
                  
                  Values.ENUM_LITERAL(index = i)  => begin
                    i
                  end
                  
                  Values.BOOL(boolean = true)  => begin
                    1
                  end
                  
                  Values.BOOL(boolean = false)  => begin
                    0
                  end
                end
              end
          outInteger
        end

         #= Returns the dimensions of a value. =#
        function valueDimensions(inValue::Values.Value) ::List{ModelicaInteger} 
              local outDimensions::List{ModelicaInteger}

              outDimensions = begin
                  local dims::List{ModelicaInteger}
                @match inValue begin
                  Values.ARRAY(dimLst = dims)  => begin
                    dims
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outDimensions
        end

        function extractValueString(val::Values.Value) ::String 
              local str::String

              @match Values.STRING(str) = val
          str
        end

        function makeCodeTypeName(path::Absyn.Path) ::Values.Value 
              local val::Values.Value

              val = Values.CODE(Absyn.C_TYPENAME(path))
          val
        end

        function getCode(val::Values.Value) ::Absyn.CodeNode 
              local code::Absyn.CodeNode

              @match Values.CODE(code) = val
          code
        end

        function getPath(val::Values.Value) ::Absyn.Path 
              local path::Absyn.Path

              local code::Absyn.CodeNode

              @match Values.CODE(code) = val
              @match Absyn.C_TYPENAME(path) = code
          path
        end

        function printCodeVariableName(val::Values.Value) ::String 
              local str::String

              str = begin
                  local cr::Absyn.ComponentRef
                  local exp::Absyn.Exp
                   #=  der(x)
                   =#
                @match val begin
                  Values.CODE(Absyn.C_EXPRESSION(exp))  => begin
                    Dump.printExpStr(exp)
                  end
                  
                  Values.CODE(Absyn.C_VARIABLENAME(cr))  => begin
                    Dump.printComponentRefStr(cr)
                  end
                end
              end
               #=  x
               =#
          str
        end

        function boxIfUnboxedVal(v::Values.Value) ::Values.Value 
              local ov::Values.Value

              ov = begin
                @match v begin
                  Values.INTEGER(_)  => begin
                    Values.META_BOX(v)
                  end
                  
                  Values.REAL(_)  => begin
                    Values.META_BOX(v)
                  end
                  
                  Values.BOOL(_)  => begin
                    Values.META_BOX(v)
                  end
                  
                  _  => begin
                      v
                  end
                end
              end
          ov
        end

        function unboxIfBoxedVal(iv::Values.Value) ::Values.Value 
              local ov::Values.Value

              ov = begin
                  local v::Values.Value
                @match iv begin
                  Values.META_BOX(v)  => begin
                    v
                  end
                  
                  _  => begin
                      iv
                  end
                end
              end
          ov
        end

        function arrayOrListVals(v::Values.Value, boxIfUnboxed::Bool) ::List{Values.Value} 
              local vals::List{Values.Value}

              vals = begin
                @match (v, boxIfUnboxed) begin
                  (Values.ARRAY(valueLst = vals), _)  => begin
                    vals
                  end
                  
                  (Values.LIST(vals), true)  => begin
                    ListUtil.map(vals, boxIfUnboxedVal)
                  end
                  
                  (Values.LIST(vals), _)  => begin
                    vals
                  end
                end
              end
          vals
        end

        function containsEmpty(inValue::Values.Value) ::Option{Values.Value} 
              local outEmptyVal::Option{Values.Value}

              outEmptyVal = begin
                @match inValue begin
                  Values.EMPTY(__)  => begin
                    SOME(inValue)
                  end
                  
                  Values.ARRAY(__)  => begin
                    arrayContainsEmpty(inValue.valueLst)
                  end
                  
                  Values.RECORD(__)  => begin
                    arrayContainsEmpty(inValue.orderd)
                  end
                  
                  Values.TUPLE(__)  => begin
                    arrayContainsEmpty(inValue.valueLst)
                  end
                  
                  _  => begin
                      NONE()
                  end
                end
              end
          outEmptyVal
        end

         #= Searches for an EMPTY value in a list, and returns SOME(value) if found,
           otherwise NONE(). =#
        function arrayContainsEmpty(inValues::List{<:Values.Value}) ::Option{Values.Value} 
              local outOptValue::Option{Values.Value} = NONE()

              for val in inValues
                outOptValue = containsEmpty(val)
                if isSome(outOptValue)
                  break
                end
              end
          outOptValue
        end

        function liftValueList(inValue::Values.Value, inDimensions::List{<:DAE.Dimension}) ::Values.Value 
              local outValue::Values.Value = inValue

              for dim in listReverse(inDimensions)
                outValue = makeArray(ListUtil.fill(outValue, Expression.dimensionSize(dim)))
              end
          outValue
        end

        function isEmpty(inValue::Values.Value) ::Bool 
              local outIsEmpty::Bool

              outIsEmpty = begin
                @match inValue begin
                  Values.EMPTY(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsEmpty
        end

         #= Converts the component values of a record to the correct types. =#
        function typeConvertRecord(inValue::Values.Value, inType::DAE.Type) ::Values.Value 
              local outValue::Values.Value = inValue

              outValue = begin
                  local ty::DAE.Type
                @match (outValue, inType) begin
                  (Values.RECORD(__), DAE.T_COMPLEX(__))  => begin
                      outValue.orderd = list(@do_threaded_for typeConvertRecord(val, Types.getVarType(var)) (val, var) (outValue.orderd, inType.varLst))
                    outValue
                  end
                  
                  (Values.INTEGER(__), DAE.T_REAL(__))  => begin
                    Values.REAL(intReal(outValue.integer))
                  end
                  
                  (Values.ARRAY(__), DAE.T_ARRAY(__))  => begin
                      ty = Expression.unliftArray(inType)
                      outValue.valueLst = list(typeConvertRecord(v, ty) for v in outValue.valueLst)
                    outValue
                  end
                  
                  _  => begin
                      outValue
                  end
                end
              end
          outValue
        end

         #= Work-around for Values.ARRAY({}) becoming T_UNKNOWN in ValuesUtil.valueExp =#
        function fixZeroSizeArray(e::DAE.Exp, ty::DAE.Type) ::DAE.Exp 


              e = begin
                @match e begin
                  DAE.ARRAY(ty = DAE.T_ARRAY(ty = DAE.T_UNKNOWN(__)), scalar = false, array =  nil())  => begin
                    DAE.ARRAY(ty, ! Types.isArray(Types.unliftArray(ty)), nil)
                  end
                  
                  _  => begin
                      e
                  end
                end
              end
          e
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
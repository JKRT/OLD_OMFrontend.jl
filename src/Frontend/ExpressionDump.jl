  module ExpressionDump


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    FuncTypeType_aTo = Function

    FuncTypeType_aToString = Function

    printComponentRefStrFunc = Function
    printCallFunc = Function

    Type_a = Any

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

        @importDBG Absyn

        @importDBG AbsynUtil

        @importDBG DAE

        @importDBG Graphviz
         #=  protected @importDBGs
         =#

        @importDBG Config

        @importDBG Dump

        @importDBG ExpressionUtil

        @importDBG CrefForHashTable

        @importDBG ListUtil

        @importDBG Print

        @importDBG System

        @importDBG Tpl

        @importDBG Types
         #= /*
         * - Printing expressions
         *   This module provides some functions to print data to the standard
         *   output.  This is used for error messages, and for debugging the
         *   semantic description.
         */ =#

         #= Returns a string representation of a subscript. =#
        function subscriptString(subscript::DAE.Subscript) ::String
              local str::String

              str = begin
                  local i::ModelicaInteger
                  local res::String
                  local enum_lit::Absyn.Path
                @match subscript begin
                  DAE.INDEX(exp = DAE.ICONST(integer = i))  => begin
                      res = intString(i)
                    res
                  end

                  DAE.INDEX(exp = DAE.ENUM_LITERAL(name = enum_lit))  => begin
                      res = AbsynUtil.pathString(enum_lit)
                    res
                  end
                end
              end
          str
        end

         #=
        function: binopSymbol
          Return a string representation of the Operator. =#
        function binopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = if Config.typeinfo()
                    binopSymbol2(inOperator)
                  else
                    binopSymbol1(inOperator)
                  end
          outString
        end

         #= Helper function to binopSymbol =#
        function binopSymbol1(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.ADD(__)  => begin
                    " + "
                  end

                  DAE.SUB(__)  => begin
                    " - "
                  end

                  DAE.MUL(__)  => begin
                    " * "
                  end

                  DAE.DIV(__)  => begin
                    " / "
                  end

                  DAE.POW(__)  => begin
                    " ^ "
                  end

                  DAE.ADD_ARR(__)  => begin
                    " + "
                  end

                  DAE.SUB_ARR(__)  => begin
                    " - "
                  end

                  DAE.MUL_ARR(__)  => begin
                    " * "
                  end

                  DAE.DIV_ARR(__)  => begin
                    " / "
                  end

                  DAE.POW_ARR(__)  => begin
                    " ^ "
                  end

                  DAE.POW_ARR2(__)  => begin
                    " ^ "
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    " * "
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    " + "
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    " - "
                  end

                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    " ^ "
                  end

                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    " ^ "
                  end

                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    " * "
                  end

                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    " * "
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    " / "
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    " / "
                  end

                  _  => begin
                      " <UNKNOWN_SYMBOL> "
                  end
                end
              end
          outString
        end

         #= Helper function to binopSymbol =#
        function debugBinopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.ADD(__)  => begin
                    " + "
                  end

                  DAE.SUB(__)  => begin
                    " - "
                  end

                  DAE.MUL(__)  => begin
                    " * "
                  end

                  DAE.DIV(__)  => begin
                    " / "
                  end

                  DAE.POW(__)  => begin
                    " ^ "
                  end

                  DAE.EQUAL(__)  => begin
                    " = "
                  end

                  DAE.ADD_ARR(__)  => begin
                    " +ARR "
                  end

                  DAE.SUB_ARR(__)  => begin
                    " -ARR "
                  end

                  DAE.MUL_ARR(__)  => begin
                    " *ARR "
                  end

                  DAE.DIV_ARR(__)  => begin
                    " /ARR "
                  end

                  DAE.POW_ARR(__)  => begin
                    " ^ARR "
                  end

                  DAE.POW_ARR2(__)  => begin
                    " ^ARR2 "
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    " ARR*S "
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    " ARR+S "
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    " - "
                  end

                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    " S^ARR "
                  end

                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    " ARR^S "
                  end

                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    " Dot "
                  end

                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    " MatrixProd "
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    " S/ARR "
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    " ARR/S "
                  end
                end
              end
          outString
        end

         #= Helper function to binopSymbol. =#
        function binopSymbol2(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                  local ts::String
                  local s::String
                  local t::DAE.Type
                @match inOperator begin
                  DAE.ADD(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" +<", ts, "> "))
                    s
                  end

                  DAE.SUB(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" -<", ts, "> "))
                    s
                  end

                  DAE.MUL(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" *<", ts, "> "))
                    s
                  end

                  DAE.DIV(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" /<", ts, "> "))
                    s
                  end

                  DAE.POW(__)  => begin
                    " ^ "
                  end

                  DAE.ADD_ARR(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" +<ADD_ARR><", ts, "> "))
                    s
                  end

                  DAE.SUB_ARR(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" -<SUB_ARR><", ts, "> "))
                    s
                  end

                  DAE.MUL_ARR(__)  => begin
                    " *<MUL_ARRAY> "
                  end

                  DAE.DIV_ARR(ty = t)  => begin
                      ts = Types.unparseType(t)
                      s = stringAppendList(list(" /<DIV_ARR><", ts, "> "))
                    s
                  end

                  DAE.POW_ARR(__)  => begin
                    " ^<POW_ARR> "
                  end

                  DAE.POW_ARR2(__)  => begin
                    " ^<POW_ARR2> "
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    " *<MUL_ARRAY_SCALAR> "
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    " +<ADD_ARRAY_SCALAR> "
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    " -<SUB_SCALAR_ARRAY> "
                  end

                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    " ^<POW_SCALAR_ARRAY> "
                  end

                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    " ^<POW_ARRAY_SCALAR> "
                  end

                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    " *<MUL_SCALAR_PRODUCT> "
                  end

                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    " *<MUL_MATRIX_PRODUCT> "
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    " /<DIV_SCALAR_ARRAY> "
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    " /<DIV_ARRAY_SCALAR> "
                  end
                end
              end
          outString
        end

         #= Return string representation of unary operators. =#
        function unaryopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.UMINUS(__)  => begin
                    if Config.typeinfo()
                          "-<UMINUS>"
                        else
                          "-"
                        end
                  end

                  DAE.UMINUS_ARR(__)  => begin
                    if Config.typeinfo()
                          "-<UMINUS_ARR>"
                        else
                          "-"
                        end
                  end
                end
              end
          outString
        end

         #= Return string representation of logical binary operator. =#
        function lbinopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.AND(_)  => begin
                    " and "
                  end

                  DAE.OR(_)  => begin
                    " or "
                  end
                end
              end
          outString
        end

         #= Return string representation of logical unary operator. =#
        function lunaryopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.NOT(_)  => begin
                    "not "
                  end
                end
              end
          outString
        end

         #= Return string representation of function operator. =#
        function relopSymbol(inOperator::DAE.Operator) ::String
              local outString::String

              outString = begin
                @match inOperator begin
                  DAE.LESS(__)  => begin
                    " < "
                  end

                  DAE.LESSEQ(__)  => begin
                    " <= "
                  end

                  DAE.GREATER(__)  => begin
                    " > "
                  end

                  DAE.GREATEREQ(__)  => begin
                    " >= "
                  end

                  DAE.EQUAL(__)  => begin
                    " == "
                  end

                  DAE.NEQUAL(__)  => begin
                    " <> "
                  end
                end
              end
          outString
        end

         #= Print a list of values given a print
          function and a separator string. =#
        function printList(inTypeALst::List{<:Type_a}, inFuncTypeTypeATo::FuncTypeType_aTo, inString::String)
              _ = begin
                  local h::Type_a
                  local r::FuncTypeType_aTo
                  local t::List{Type_a}
                  local sep::String
                @matchcontinue (inTypeALst, inFuncTypeTypeATo, inString) begin
                  ( nil(), _, _)  => begin
                    ()
                  end

                  (h <|  nil(), r, _)  => begin
                      r(h)
                    ()
                  end

                  (h <| t, r, sep)  => begin
                      r(h)
                      Print.printBuf(sep)
                      printList(t, r, sep)
                    ()
                  end
                end
              end
        end

         #= Print a list of expressions to the Print buffer. =#
        function printRow(es_1::List{<:DAE.Exp})
              printList(es_1, printExp, ",")
        end

         #= Same as printList, except it returns
          a string instead of printing. =#
        function printListStr(inTypeALst::List{<:Type_a}, inFuncTypeTypeAToString::FuncTypeType_aToString, inString::String) ::String
              local outString::String

              outString = stringDelimitList(ListUtil.map(inTypeALst, inFuncTypeTypeAToString), inString)
          outString
        end

         #=
          Print a Subscript into a String. =#
        function debugPrintSubscriptStr(inSubscript::DAE.Subscript) ::String
              local outString::String

              outString = begin
                  local s::String
                  local e1::DAE.Exp
                @match inSubscript begin
                  DAE.WHOLEDIM(__)  => begin
                    ":"
                  end

                  DAE.INDEX(exp = e1)  => begin
                      s = dumpExpStr(e1, 0)
                      s = System.stringReplace(s, "\\n", "")
                    s
                  end

                  DAE.SLICE(exp = e1)  => begin
                      s = dumpExpStr(e1, 0)
                      s = System.stringReplace(s, "\\n", "")
                    s
                  end

                  DAE.WHOLE_NONEXP(exp = e1)  => begin
                      s = dumpExpStr(e1, 0)
                      s = System.stringReplace(s, "\\n", "")
                    "1:" + s
                  end
                end
              end
          outString
        end

         #=
          Print a Subscript into a String. =#
        function printSubscriptStr(sub::DAE.Subscript) ::String
              local outString::String

              outString = begin
                @match sub begin
                  DAE.WHOLEDIM(__)  => begin
                    ":"
                  end

                  DAE.INDEX(__)  => begin
                    printExpStr(sub.exp)
                  end

                  DAE.SLICE(__)  => begin
                    printExpStr(sub.exp)
                  end

                  DAE.WHOLE_NONEXP(__)  => begin
                    "1:" + printExpStr(sub.exp)
                  end
                end
              end
          outString
        end

         #= Print a list of Subscripts into a String. =#
        function printSubscriptLstStr(inSubscriptLst::List{<:DAE.Subscript}) ::String
              local outString::String

              outString = stringDelimitList(ListUtil.map(inSubscriptLst, printSubscriptStr), " , ")
          outString
        end

         #=  prints a list of expressions with commas between expressions. =#
        function printExpListStr(expl::List{<:DAE.Exp}) ::String
              local res::String

              res = stringDelimitList(ListUtil.map(expl, printExpStr), ", ")
          res
        end

         #=  stefan
         =#

         #= same as printExpListStr, but the string will not have any spaces or commas between expressions =#
        function printExpListStrNoSpace(expl::List{<:DAE.Exp}) ::String
              local res::String

              res = stringAppendList(ListUtil.map(expl, printExpStr))
          res
        end

         #=
        Returns a string if SOME otherwise '' =#
        function printOptExpStr(oexp::Option{<:DAE.Exp}) ::String
              local str::String

              str = begin
                  local e::DAE.Exp
                @match oexp begin
                  SOME(e)  => begin
                    printExpStr(e)
                  end

                  _  => begin
                      ""
                  end
                end
              end
          str
        end

         #= This function prints a complete expression. =#
        function printExpStr(e::DAE.Exp) ::String
          CrefForHashTable.printExpStr(e)
        end

        function printCrefsFromExpStr(e::DAE.Exp) ::String
           CrefForHashTable.printCrefsFromExpStr(e)
        end


        function printComponentRefStr(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = begin
                  local s::DAE.Ident
                  local str::DAE.Ident
                  local strrest::DAE.Ident
                  local strseb::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local b::Bool
                  local ix::ModelicaInteger
                   #=  Optimize -- a function call less
                   =#
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = s, subscriptLst =  nil())  => begin
                    s
                  end

                  DAE.CREF_IDENT(ident = s, subscriptLst = subs)  => begin
                      str = printComponentRef2Str(s, subs)
                    str
                  end

                  DAE.CREF_ITER(ident = s, index = ix, subscriptLst =  nil())  => begin
                    s + "/* iter index " + intString(ix) + " */"
                  end

                  DAE.CREF_ITER(ident = s, index = ix, subscriptLst = subs)  => begin
                      str = printComponentRef2Str(s, subs)
                    str + "/* iter index " + intString(ix) + " */"
                  end

                  DAE.CREF_QUAL(ident = s, subscriptLst = subs, componentRef = cr)  => begin
                      b = Config.modelicaOutput()
                      str = printComponentRef2Str(s, subs)
                      strrest = printComponentRefStr(cr)
                      strseb = if b
                            "__"
                          else
                            "."
                          end
                      str = stringAppendList(list(str, strseb, strrest))
                    str
                  end

                  DAE.WILD(__)  => begin
                    "_"
                  end
                end
              end
               #=  idents with subscripts
               =#
               #=  Optimize -- a function call less
               =#
               #=  idents with subscripts
               =#
               #=  Qualified - Modelica output - does not handle names with underscores
               =#
               #=  Qualified - non Modelica output
               =#
               #=  Wild
               =#
          outString
        end


        #= Helper function to printComponentRefStr. =#
       function printComponentRef2Str(inIdent::DAE.Ident, inSubscriptLst::List{<:DAE.Subscript}) ::String
             local outString::String

             outString = begin
                 local s::DAE.Ident
                 local str::DAE.Ident
                 local strseba::DAE.Ident
                 local strsebb::DAE.Ident
                 local l::List{DAE.Subscript}
                 local b::Bool
                  #=  no subscripts
                  =#
               @match (inIdent, inSubscriptLst) begin
                 (s,  nil())  => begin
                   s
                 end

                 (s, l)  => begin
                     b = Config.modelicaOutput()
                     str = ExpressionDump.printListStr(l, ExpressionDump.printSubscriptStr, ",")
                     (strseba, strsebb) = if b
                           ("_L", "_R")
                         else
                           ("[", "]")
                         end
                     str = stringAppendList(list(s, strseba, str, strsebb))
                   str
                 end
               end
             end
              #=  some subscripts, Modelica output
              =#
              #=  some subscripts, non Modelica output
              =#
         outString
       end

       #= Pattern to String unparsing =#
      function patternStr(pattern::DAE.Pattern) ::String
            local str::String

            str = begin
                local pats::List{DAE.Pattern}
                local fields::List{String}
                local patsStr::List{String}
                local exp::DAE.Exp
                local pat::DAE.Pattern
                local head::DAE.Pattern
                local tail::DAE.Pattern
                local id::String
                local namedpats::List{Tuple{DAE.Pattern, String, DAE.Type}}
                local name::Absyn.Path
              @matchcontinue pattern begin
                DAE.PAT_WILD(__)  => begin
                  "_"
                end

                DAE.PAT_AS(id = id, pat = DAE.PAT_WILD(__))  => begin
                  id
                end

                DAE.PAT_AS_FUNC_PTR(id, DAE.PAT_WILD(__))  => begin
                  id
                end

                DAE.PAT_SOME(pat)  => begin
                    str = patternStr(pat)
                  "SOME(" + str + ")"
                end

                DAE.PAT_META_TUPLE(pats)  => begin
                    str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                  "(" + str + ")"
                end

                DAE.PAT_CALL_TUPLE(pats)  => begin
                    str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                  "(" + str + ")"
                end

                DAE.PAT_CALL(name = name, patterns = pats)  => begin
                    id = AbsynUtil.pathString(name)
                    str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                  stringAppendList(list(id, "(", str, ")"))
                end

                DAE.PAT_CALL_NAMED(name = name, patterns = namedpats)  => begin
                    id = AbsynUtil.pathString(name)
                    fields = ListUtil.map(namedpats, Util.tuple32)
                    patsStr = ListUtil.map1r(ListUtil.mapMap(namedpats, Util.tuple31, patternStr), stringAppend, "=")
                    str = stringDelimitList(ListUtil.threadMap(fields, patsStr, stringAppend), ",")
                  stringAppendList(list(id, "(", str, ")"))
                end

                DAE.PAT_CONS(head, tail)  => begin
                  patternStr(head) + "::" + patternStr(tail)
                end

                DAE.PAT_CONSTANT(exp = exp)  => begin
                  #TODO
                  #ExpressionDump.printExpStr(exp)
                  throw("TODO error")
                end

                DAE.PAT_AS(id = id, pat = pat)  => begin
                  id + " as " + patternStr(pat)
                end

                DAE.PAT_AS_FUNC_PTR(id, pat)  => begin
                  id + " as " + patternStr(pat)
                end

                _  => begin
                      Error.addMessage(Error.INTERNAL_ERROR, list("patternStr not implemented correctly"))
                    "*PATTERN*"
                end
              end
            end
             #=  case DAE.PAT_CONSTANT(SOME(et),exp) then \"(\" + Types.unparseType(et) + \")\" + ExpressionDump.printExpStr(exp);
             =#
        str
      end

         #= Helper function to printExpStr. =#
        function printExp2Str(inExp::DAE.Exp, stringDelimiter::String, opcreffunc::Option{<:Tuple{<:printComponentRefStrFunc, Type_a}} #= tuple of function that prints component references and an extra parameter passed through to the function =#, opcallfunc::Option{<:printCallFunc} #= function that prints function calls =#) ::String
              local outString::String

              outString = begin
                  local s::String
                  local s_1::String
                  local s_2::String
                  local sym::String
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local res::String
                  local fs::String
                  local argstr::String
                  local s_4::String
                  local str::String
                  local crstr::String
                  local dimstr::String
                  local expstr::String
                  local iterstr::String
                  local s1_1::String
                  local s2_1::String
                  local cs::String
                  local ts::String
                  local cs_1::String
                  local ts_1::String
                  local fs_1::String
                  local s3_1::String
                  local i::ModelicaInteger
                  local pe1::ModelicaInteger
                  local p1::ModelicaInteger
                  local p2::ModelicaInteger
                  local pc::ModelicaInteger
                  local pt::ModelicaInteger
                  local pf::ModelicaInteger
                  local p::ModelicaInteger
                  local pstop::ModelicaInteger
                  local pstart::ModelicaInteger
                  local pstep::ModelicaInteger
                  local r::ModelicaReal
                  local c::DAE.ComponentRef
                  local name::DAE.ComponentRef
                  local t::DAE.Type
                  local tp::DAE.Type
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local start::DAE.Exp
                  local stop::DAE.Exp
                  local step::DAE.Exp
                  local cr::DAE.Exp
                  local dim::DAE.Exp
                  local exp::DAE.Exp
                  local cond::DAE.Exp
                  local tb::DAE.Exp
                  local fb::DAE.Exp
                  local op::DAE.Operator
                  local fcn::Absyn.Path
                  local lit::Absyn.Path
                  local args::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local pcreffunc::printComponentRefStrFunc
                  local creffuncparam::Type_a
                  local pcallfunc::printCallFunc
                  local b::Bool
                  local aexpl::List{DAE.Exp}
                  local lstes::List{List{DAE.Exp}}
                  local matchTy::DAE.MatchType
                  local et::DAE.Type
                  local cases::List{DAE.MatchCase}
                  local pat::DAE.Pattern
                  local code::Absyn.CodeNode
                  local riters::DAE.ReductionIterators
                  local scope::String
                  local tyStr::String
                @matchcontinue (inExp, stringDelimiter, opcreffunc, opcallfunc) begin
                  (DAE.EMPTY(scope = scope, name = name, tyStr = tyStr), _, _, _)  => begin
                    "<EMPTY(scope: " + scope + ", name: " + printComponentRefStr(name) + ", ty: " + tyStr + ")>"
                  end

                  (DAE.ICONST(integer = i), _, _, _)  => begin
                      s = intString(i)
                    s
                  end

                  (DAE.RCONST(real = r), _, _, _)  => begin
                      s = realString(r)
                    s
                  end

                  (DAE.SCONST(string = s), _, _, _)  => begin
                      s = System.escapedString(s, false)
                      s = stringAppendList(list(stringDelimiter, s, stringDelimiter))
                    s
                  end

                  (DAE.BCONST(bool = b), _, _, _)  => begin
                    boolString(b)
                  end

                  (DAE.CREF(componentRef = c), _, SOME((pcreffunc, creffuncparam)), _)  => begin
                      s = pcreffunc(c, creffuncparam)
                    s
                  end

                  (DAE.CREF(componentRef = c), _, _, _)  => begin
                      s = printComponentRefStr(c)
                    s
                  end

                  (DAE.ENUM_LITERAL(name = lit), _, _, _)  => begin
                      s = AbsynUtil.pathString(lit)
                    s
                  end

                  (e && DAE.BINARY(e1, op, e2), _, _, _)  => begin
                      sym = binopSymbol(op)
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s2 = printExp2Str(e2, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      p1 = expPriority(e1)
                      p2 = expPriority(e2)
                      s1_1 = parenthesize(s1, p1, p, false)
                      s2_1 = parenthesize(s2, p2, p, true)
                      s = stringAppendList(list(s1_1, sym, s2_1))
                    s
                  end

                  (e && DAE.UNARY(op, e1), _, _, _)  => begin
                      sym = unaryopSymbol(op)
                      s = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      p1 = expPriority(e1)
                      s_1 = parenthesize(s, p1, p, true)
                      s_2 = stringAppend(sym, s_1)
                    s_2
                  end

                  (e && DAE.LBINARY(e1, op, e2), _, _, _)  => begin
                      sym = lbinopSymbol(op)
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s2 = printExp2Str(e2, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      p1 = expPriority(e1)
                      p2 = expPriority(e2)
                      s1_1 = parenthesize(s1, p1, p, false)
                      s2_1 = parenthesize(s2, p2, p, true)
                      s = stringAppendList(list(s1_1, sym, s2_1))
                    s
                  end

                  (e && DAE.LUNARY(op, e1), _, _, _)  => begin
                      sym = lunaryopSymbol(op)
                      s = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      p1 = expPriority(e1)
                      s_1 = parenthesize(s, p1, p, false)
                      s_2 = stringAppend(sym, s_1)
                    s_2
                  end

                  (e && DAE.RELATION(exp1 = e1, operator = op, exp2 = e2), _, _, _)  => begin
                      sym = relopSymbol(op)
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s2 = printExp2Str(e2, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      p1 = expPriority(e1)
                      p2 = expPriority(e2)
                      s1_1 = parenthesize(s1, p1, p, false)
                      s2_1 = parenthesize(s2, p2, p, true)
                      s = stringAppendList(list(s1_1, sym, s2_1))
                    s
                  end

                  (e && DAE.IFEXP(cond, tb, fb), _, _, _)  => begin
                      cs = printExp2Str(cond, stringDelimiter, opcreffunc, opcallfunc)
                      ts = printExp2Str(tb, stringDelimiter, opcreffunc, opcallfunc)
                      fs = printExp2Str(fb, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      pc = expPriority(cond)
                      pt = expPriority(tb)
                      pf = expPriority(fb)
                      cs_1 = parenthesize(cs, pc, p, false)
                      ts_1 = parenthesize(ts, pt, p, false)
                      fs_1 = parenthesize(fs, pf, p, false)
                      str = stringAppendList(list("if ", cs_1, " then ", ts_1, " else ", fs_1))
                    str
                  end

                  (e && DAE.CALL(__), _, _, SOME(pcallfunc))  => begin
                      s_2 = pcallfunc(e, stringDelimiter, opcreffunc)
                    s_2
                  end

                  (DAE.CALL(path = fcn, expLst = args), _, _, _)  => begin
                      fs = AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(fcn))
                      argstr = stringDelimitList(ListUtil.map3(args, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list(fs, "(", argstr, ")"))
                    s
                  end

                  (DAE.PARTEVALFUNCTION(path = fcn, expList = args), _, _, _)  => begin
                      fs = AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(fcn))
                      argstr = stringDelimitList(ListUtil.map3(args, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list("function ", fs, "(", argstr, ")"))
                    s
                  end

                  (DAE.ARRAY(array = es), _, _, _)  => begin
                      s = stringDelimitList(ListUtil.map3(es, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list("{", s, "}"))
                    s
                  end

                  (DAE.TUPLE(PR = es), _, _, _)  => begin
                      s = stringDelimitList(ListUtil.map3(es, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list("(", s, ")"))
                    s
                  end

                  (DAE.MATRIX(matrix = lstes), _, _, _)  => begin
                      s = stringDelimitList(ListUtil.map1(lstes, printRowStr, stringDelimiter), "},{")
                      s = stringAppendList(list("{{", s, "}}"))
                    s
                  end

                  (e && DAE.RANGE(_, start, NONE(), stop), _, _, _)  => begin
                      s1 = printExp2Str(start, stringDelimiter, opcreffunc, opcallfunc)
                      s3 = printExp2Str(stop, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      pstart = expPriority(start)
                      pstop = expPriority(stop)
                      s1_1 = parenthesize(s1, pstart, p, false)
                      s3_1 = parenthesize(s3, pstop, p, false)
                      s = stringAppendList(list(s1_1, ":", s3_1))
                    s
                  end

                  (e && DAE.RANGE(_, start, SOME(step), stop), _, _, _)  => begin
                      s1 = printExp2Str(start, stringDelimiter, opcreffunc, opcallfunc)
                      s2 = printExp2Str(step, stringDelimiter, opcreffunc, opcallfunc)
                      s3 = printExp2Str(stop, stringDelimiter, opcreffunc, opcallfunc)
                      p = expPriority(e)
                      pstart = expPriority(start)
                      pstop = expPriority(stop)
                      pstep = expPriority(step)
                      s1_1 = parenthesize(s1, pstart, p, false)
                      s3_1 = parenthesize(s3, pstop, p, false)
                      s2_1 = parenthesize(s2, pstep, p, false)
                      s = stringAppendList(list(s1_1, ":", s2_1, ":", s3_1))
                    s
                  end

                  (DAE.CAST(ty = tp, exp = e), _, _, _)  => begin
                      str = Types.unparseType(tp)
                      s = printExp2Str(e, stringDelimiter, opcreffunc, opcallfunc)
                      res = stringAppendList(list("DAE.CAST(", str, ", ", s, ")"))
                    res
                  end

                  (e && DAE.ASUB(exp = e1, sub = aexpl), _, _, _)  => begin
                      p = expPriority(e)
                      pe1 = expPriority(e1)
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s1_1 = parenthesize(s1, pe1, p, false)
                      s4 = stringDelimitList(ListUtil.map3(aexpl, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s_4 = s1_1 + "[" + s4 + "]"
                    s_4
                  end

                  (DAE.SIZE(exp = cr, sz = SOME(dim)), _, _, _)  => begin
                      crstr = printExp2Str(cr, stringDelimiter, opcreffunc, opcallfunc)
                      dimstr = printExp2Str(dim, stringDelimiter, opcreffunc, opcallfunc)
                      str = stringAppendList(list("size(", crstr, ",", dimstr, ")"))
                    str
                  end

                  (DAE.SIZE(exp = cr, sz = NONE()), _, _, _)  => begin
                      crstr = printExp2Str(cr, stringDelimiter, opcreffunc, opcallfunc)
                      str = stringAppendList(list("size(", crstr, ")"))
                    str
                  end

                  (DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = fcn), expr = exp, iterators = riters), _, _, _)  => begin
                      fs = AbsynUtil.pathStringNoQual(fcn)
                      expstr = printExp2Str(exp, stringDelimiter, opcreffunc, opcallfunc)
                      iterstr = stringDelimitList(ListUtil.map(riters, reductionIteratorStr), ",")
                      str = stringAppendList(list("<reduction>", fs, "(", expstr, " for ", iterstr, ")"))
                    str
                  end

                  (DAE.META_TUPLE(es), _, _, _)  => begin
                      s = "Tuple" + printExp2Str(DAE.TUPLE(es), stringDelimiter, opcreffunc, opcallfunc)
                    s
                  end

                  (DAE.LIST(valList = es), _, _, _)  => begin
                      s = stringDelimitList(ListUtil.map3(es, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list("List(", s, ")"))
                    s
                  end

                  (DAE.CONS(car = e1, cdr = e2), _, _, _)  => begin
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s2 = printExp2Str(e2, stringDelimiter, opcreffunc, opcallfunc)
                      s_2 = stringAppendList(list("listCons(", s1, ",", s2, ")"))
                    s_2
                  end

                  (DAE.META_OPTION(NONE()), _, _, _)  => begin
                    "NONE()"
                  end

                  (DAE.META_OPTION(SOME(e1)), _, _, _)  => begin
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s_1 = stringAppendList(list("SOME(", s1, ")"))
                    s_1
                  end

                  (DAE.BOX(e1), _, _, _)  => begin
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s_1 = stringAppendList(list("#(", s1, ")"))
                    s_1
                  end

                  (DAE.UNBOX(e1, _), _, _, _)  => begin
                      s1 = printExp2Str(e1, stringDelimiter, opcreffunc, opcallfunc)
                      s_1 = stringAppendList(list("unbox(", s1, ")"))
                    s_1
                  end

                  (DAE.METARECORDCALL(path = fcn, args = args), _, _, _)  => begin
                      fs = AbsynUtil.pathString(fcn)
                      argstr = stringDelimitList(ListUtil.map3(args, printExp2Str, stringDelimiter, opcreffunc, opcallfunc), ",")
                      s = stringAppendList(list(fs, "(", argstr, ")"))
                    s
                  end

                  (DAE.MATCHEXPRESSION(matchType = matchTy, inputs = es, cases = cases), _, _, _)  => begin
                      s1 = printMatchType(matchTy)
                      s2 = printExp2Str(DAE.TUPLE(es), stringDelimiter, opcreffunc, opcallfunc)
                      s3 = stringAppendList(ListUtil.map(cases, printCase2Str))
                      s = stringAppendList(list(s1, s2, "\\n", s3, "  end ", s1))
                    s
                  end

                  (DAE.SHARED_LITERAL(exp = e), _, _, _)  => begin
                    printExp2Str(e, stringDelimiter, opcreffunc, opcallfunc)
                  end

                  (DAE.PATTERN(pattern = pat), _, _, _)  => begin
                    patternStr(pat)
                  end

                  (DAE.CODE(code = code), _, _, _)  => begin
                    "Code(" + Dump.printCodeStr(code) + ")"
                  end

                  _  => begin
                      printExpTypeStr(inExp)
                  end
                end
              end
               #=  s3 = Types.unparseType(tp);  adrpo: not used!
               =#
               #=  s3 = Types.unparseType(tp);  adrpo: not used!
               =#
               #=  MetaModelica tuple
               =#
               #=  MetaModelica list
               =#
               #=  MetaModelica list cons
               =#
               #=  MetaModelica Option
               =#
               #=  MetaModelica Uniontype Constructor
               =#
          outString
        end

         #= Prints out the name of the expression uniontype to a string. =#
        function printExpTypeStr(inExp::DAE.Exp) ::String
              local outString::String

              outString = begin
                @match inExp begin
                  DAE.ICONST(_)  => begin
                    "ICONST"
                  end

                  DAE.RCONST(_)  => begin
                    "RCONST"
                  end

                  DAE.SCONST(_)  => begin
                    "SCONST"
                  end

                  DAE.BCONST(_)  => begin
                    "BCONST"
                  end

                  DAE.ENUM_LITERAL(__)  => begin
                    "ENUM_LITERAL"
                  end

                  DAE.CREF(__)  => begin
                    "CREF"
                  end

                  DAE.BINARY(__)  => begin
                    "BINARY"
                  end

                  DAE.UNARY(__)  => begin
                    "UNARY"
                  end

                  DAE.LBINARY(__)  => begin
                    "LBINARY"
                  end

                  DAE.LUNARY(__)  => begin
                    "LUNARY"
                  end

                  DAE.RELATION(__)  => begin
                    "RELATION"
                  end

                  DAE.IFEXP(__)  => begin
                    "IFEXP"
                  end

                  DAE.CALL(__)  => begin
                    "CALL"
                  end

                  DAE.PARTEVALFUNCTION(__)  => begin
                    "PARTEVALFUNCTION"
                  end

                  DAE.ARRAY(__)  => begin
                    "ARRAY"
                  end

                  DAE.MATRIX(__)  => begin
                    "MATRIX"
                  end

                  DAE.RANGE(__)  => begin
                    "RANGE"
                  end

                  DAE.TUPLE(__)  => begin
                    "TUPLE"
                  end

                  DAE.CAST(__)  => begin
                    "CAST"
                  end

                  DAE.ASUB(__)  => begin
                    "ASUB"
                  end

                  DAE.TSUB(__)  => begin
                    "TSUB"
                  end

                  DAE.SIZE(__)  => begin
                    "SIZE"
                  end

                  DAE.CODE(__)  => begin
                    "CODE"
                  end

                  DAE.EMPTY(__)  => begin
                    "EMPTY"
                  end

                  DAE.REDUCTION(__)  => begin
                    "REDUCTION"
                  end

                  DAE.LIST(__)  => begin
                    "LIST"
                  end

                  DAE.CONS(__)  => begin
                    "CAR"
                  end

                  DAE.META_TUPLE(__)  => begin
                    "META_TUPLE"
                  end

                  DAE.META_OPTION(__)  => begin
                    "META_OPTION"
                  end

                  DAE.METARECORDCALL(__)  => begin
                    "METARECORDCALL"
                  end

                  DAE.MATCHEXPRESSION(__)  => begin
                    "MATCHEXPRESSION"
                  end

                  DAE.BOX(__)  => begin
                    "BOX"
                  end

                  DAE.UNBOX(__)  => begin
                    "UNBOX"
                  end

                  DAE.SHARED_LITERAL(__)  => begin
                    "SHARED_LITERAL"
                  end

                  DAE.PATTERN(__)  => begin
                    "PATTERN"
                  end

                  _  => begin
                      "#UNKNOWN EXPRESSION#"
                  end
                end
              end
          outString
        end

        function reductionIteratorStr(riter::DAE.ReductionIterator) ::String
              local str::String

              str = begin
                  local id::String
                  local exp::DAE.Exp
                  local gexp::DAE.Exp
                @match riter begin
                  DAE.REDUCTIONITER(id = id, exp = exp, guardExp = NONE())  => begin
                      str = id + " in " + printExpStr(exp)
                    str
                  end

                  DAE.REDUCTIONITER(id = id, exp = exp, guardExp = SOME(gexp))  => begin
                      str = id + " guard " + printExpStr(gexp) + " in " + printExpStr(exp)
                    str
                  end
                end
              end
          str
        end

        function printMatchType(ty::DAE.MatchType) ::String
              local str::String

              str = begin
                @match ty begin
                  DAE.MATCHCONTINUE(__)  => begin
                    "matchcontinue"
                  end

                  DAE.MATCH(NONE())  => begin
                    "match"
                  end

                  DAE.MATCH(SOME(_))  => begin
                    "match /* switch */"
                  end
                end
              end
          str
        end

         #= Prints a matchcase as string =#
        function printCase2Str(matchCase::DAE.MatchCase) ::String
              local str::String

              str = begin
                  local patterns::List{DAE.Pattern}
                  local body::List{DAE.Statement}
                  local result::DAE.Exp
                  local resultStr::String
                  local patternsStr::String
                  local bodyStr::String
                @match matchCase begin
                  DAE.CASE(patterns = patterns, body =  nil(), result = SOME(result))  => begin
                      patternsStr = patternStr(DAE.PAT_META_TUPLE(patterns))
                      resultStr = printExpStr(result)
                    stringAppendList(list("    case ", patternsStr, " then ", resultStr, ";\\n"))
                  end

                  DAE.CASE(patterns = patterns, body =  nil(), result = NONE())  => begin
                      patternsStr = patternStr(DAE.PAT_META_TUPLE(patterns))
                    stringAppendList(list("    case ", patternsStr, " then fail();\\n"))
                  end

                  DAE.CASE(patterns = patterns, body = body, result = SOME(result))  => begin
                      patternsStr = patternStr(DAE.PAT_META_TUPLE(patterns))
                      resultStr = printExpStr(result)
                      bodyStr = stringAppendList(ListUtil.map1(body, ExpressionUtil.ppStmtStr, 8))
                    stringAppendList(list("    case ", patternsStr, "\\n      algorithm\\n", bodyStr, "      then ", resultStr, ";\\n"))
                  end

                  DAE.CASE(patterns = patterns, body = body, result = NONE())  => begin
                      patternsStr = patternStr(DAE.PAT_META_TUPLE(patterns))
                      bodyStr = stringAppendList(ListUtil.map1(body, ExpressionUtil.ppStmtStr, 8))
                    stringAppendList(list("    case ", patternsStr, "\\n      algorithm\\n", bodyStr, "      then fail();\\n"))
                  end
                end
              end
          str
        end

         #=  Returns a priority number for an expression.
         This function is used to output parenthesis
         when needed, e.g., 3(1+2) should output 3(1+2)
         and not 31+2. =#
        function expPriority(inExp::DAE.Exp) ::ModelicaInteger
              local outInteger::ModelicaInteger

              outInteger = begin
                @match inExp begin
                  DAE.ICONST(_)  => begin
                    0
                  end

                  DAE.RCONST(_)  => begin
                    0
                  end

                  DAE.SCONST(_)  => begin
                    0
                  end

                  DAE.BCONST(_)  => begin
                    0
                  end

                  DAE.ENUM_LITERAL(__)  => begin
                    0
                  end

                  DAE.CREF(_, _)  => begin
                    0
                  end

                  DAE.ASUB(_, _)  => begin
                    0
                  end

                  DAE.CAST(_, _)  => begin
                    0
                  end

                  DAE.CALL(__)  => begin
                    0
                  end

                  DAE.PARTEVALFUNCTION(__)  => begin
                    0
                  end

                  DAE.ARRAY(__)  => begin
                    0
                  end

                  DAE.MATRIX(__)  => begin
                    0
                  end

                  DAE.BINARY(operator = DAE.POW(_))  => begin
                    3
                  end

                  DAE.BINARY(operator = DAE.POW_ARR(_))  => begin
                    3
                  end

                  DAE.BINARY(operator = DAE.POW_ARR2(_))  => begin
                    3
                  end

                  DAE.BINARY(operator = DAE.POW_SCALAR_ARRAY(_))  => begin
                    3
                  end

                  DAE.BINARY(operator = DAE.POW_ARRAY_SCALAR(_))  => begin
                    3
                  end

                  DAE.BINARY(operator = DAE.DIV(_))  => begin
                    5
                  end

                  DAE.BINARY(operator = DAE.DIV_ARR(_))  => begin
                    5
                  end

                  DAE.BINARY(operator = DAE.DIV_SCALAR_ARRAY(_))  => begin
                    5
                  end

                  DAE.BINARY(operator = DAE.DIV_ARRAY_SCALAR(_))  => begin
                    5
                  end

                  DAE.BINARY(operator = DAE.MUL(_))  => begin
                    7
                  end

                  DAE.BINARY(operator = DAE.MUL_ARR(_))  => begin
                    7
                  end

                  DAE.BINARY(operator = DAE.MUL_ARRAY_SCALAR(_))  => begin
                    7
                  end

                  DAE.BINARY(operator = DAE.MUL_SCALAR_PRODUCT(_))  => begin
                    7
                  end

                  DAE.BINARY(operator = DAE.MUL_MATRIX_PRODUCT(_))  => begin
                    7
                  end

                  DAE.UNARY(operator = DAE.UMINUS(_))  => begin
                    8
                  end

                  DAE.UNARY(operator = DAE.UMINUS_ARR(_))  => begin
                    8
                  end

                  DAE.BINARY(operator = DAE.ADD(_))  => begin
                    9
                  end

                  DAE.BINARY(operator = DAE.ADD_ARR(_))  => begin
                    9
                  end

                  DAE.BINARY(operator = DAE.ADD_ARRAY_SCALAR(_))  => begin
                    9
                  end

                  DAE.BINARY(operator = DAE.SUB(_))  => begin
                    9
                  end

                  DAE.BINARY(operator = DAE.SUB_ARR(_))  => begin
                    9
                  end

                  DAE.BINARY(operator = DAE.SUB_SCALAR_ARRAY(_))  => begin
                    9
                  end

                  DAE.RELATION(operator = DAE.LESS(_))  => begin
                    11
                  end

                  DAE.RELATION(operator = DAE.LESSEQ(_))  => begin
                    11
                  end

                  DAE.RELATION(operator = DAE.GREATER(_))  => begin
                    11
                  end

                  DAE.RELATION(operator = DAE.GREATEREQ(_))  => begin
                    11
                  end

                  DAE.RELATION(operator = DAE.EQUAL(_))  => begin
                    11
                  end

                  DAE.RELATION(operator = DAE.NEQUAL(_))  => begin
                    11
                  end

                  DAE.LUNARY(operator = DAE.NOT(_))  => begin
                    13
                  end

                  DAE.LBINARY(operator = DAE.AND(_))  => begin
                    15
                  end

                  DAE.LBINARY(operator = DAE.OR(_))  => begin
                    17
                  end

                  DAE.RANGE(__)  => begin
                    19
                  end

                  DAE.IFEXP(__)  => begin
                    21
                  end

                  DAE.TUPLE(_)  => begin
                    23
                  end

                  _  => begin
                      25
                  end
                end
              end
               #= /* Not valid in inner expressions, only included here for completeness */ =#
          outInteger
        end

         #= Prints a list of expressions to a string. =#
        function printRowStr(es_1::List{<:DAE.Exp}, stringDelimiter::String) ::String
              local s::String

              s = stringDelimitList(ListUtil.map3(es_1, printExp2Str, stringDelimiter, NONE(), NONE()), ",")
          s
        end

         #= Creates a Graphviz Node from an Expression. =#
        function dumpExpGraphviz(inExp::DAE.Exp) ::Graphviz.Node
              local outNode::Graphviz.Node

              outNode = begin
                  local s::String
                  local s_1::String
                  local s_2::String
                  local sym::String
                  local fs::String
                  local tystr::String
                  local istr::String
                  local id::String
                  local i::ModelicaInteger
                  local c::DAE.ComponentRef
                  local lt::Graphviz.Node
                  local rt::Graphviz.Node
                  local ct::Graphviz.Node
                  local tt::Graphviz.Node
                  local ft::Graphviz.Node
                  local t1::Graphviz.Node
                  local t2::Graphviz.Node
                  local t3::Graphviz.Node
                  local crt::Graphviz.Node
                  local dimt::Graphviz.Node
                  local expt::Graphviz.Node
                  local itert::Graphviz.Node
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local t::DAE.Exp
                  local f::DAE.Exp
                  local start::DAE.Exp
                  local stop::DAE.Exp
                  local step::DAE.Exp
                  local cr::DAE.Exp
                  local dim::DAE.Exp
                  local exp::DAE.Exp
                  local iterexp::DAE.Exp
                  local cond::DAE.Exp
                  local ae1::DAE.Exp
                  local op::DAE.Operator
                  local argnodes::List{Graphviz.Node}
                  local nodes::List{Graphviz.Node}
                  local fcn::Absyn.Path
                  local args::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local ty::DAE.Type
                  local r::ModelicaReal
                  local b::Bool
                  local lstes::List{List{DAE.Exp}}
                @matchcontinue inExp begin
                  DAE.ICONST(integer = i)  => begin
                      s = intString(i)
                    Graphviz.LNODE("ICONST", list(s), nil, nil)
                  end

                  DAE.RCONST(real = r)  => begin
                      s = realString(r)
                    Graphviz.LNODE("RCONST", list(s), nil, nil)
                  end

                  DAE.SCONST(string = s)  => begin
                      s = System.escapedString(s, true)
                      s = stringAppendList(list("\\", s, "\\"))
                    Graphviz.LNODE("SCONST", list(s), nil, nil)
                  end

                  DAE.BCONST(bool = b)  => begin
                      s = boolString(b)
                    Graphviz.LNODE("BCONST", list(s), nil, nil)
                  end

                  DAE.CREF(componentRef = c)  => begin
                      s = printComponentRefStr(c)
                    Graphviz.LNODE("CREF", list(s), nil, nil)
                  end

                  DAE.BINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      sym = binopSymbol(op)
                      lt = dumpExpGraphviz(e1)
                      rt = dumpExpGraphviz(e2)
                    Graphviz.LNODE("BINARY", list(sym), nil, list(lt, rt))
                  end

                  DAE.UNARY(operator = op, exp = e)  => begin
                      sym = unaryopSymbol(op)
                      ct = dumpExpGraphviz(e)
                    Graphviz.LNODE("UNARY", list(sym), nil, list(ct))
                  end

                  DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2)  => begin
                      sym = lbinopSymbol(op)
                      lt = dumpExpGraphviz(e1)
                      rt = dumpExpGraphviz(e2)
                    Graphviz.LNODE("LBINARY", list(sym), nil, list(lt, rt))
                  end

                  DAE.LUNARY(operator = op, exp = e)  => begin
                      sym = lunaryopSymbol(op)
                      ct = dumpExpGraphviz(e)
                    Graphviz.LNODE("LUNARY", list(sym), nil, list(ct))
                  end

                  DAE.RELATION(exp1 = e1, operator = op, exp2 = e2)  => begin
                      sym = relopSymbol(op)
                      lt = dumpExpGraphviz(e1)
                      rt = dumpExpGraphviz(e2)
                    Graphviz.LNODE("RELATION", list(sym), nil, list(lt, rt))
                  end

                  DAE.IFEXP(expCond = cond, expThen = t, expElse = f)  => begin
                      ct = dumpExpGraphviz(cond)
                      tt = dumpExpGraphviz(t)
                      ft = dumpExpGraphviz(f)
                    Graphviz.NODE("IFEXP", nil, list(ct, tt, ft))
                  end

                  DAE.CALL(path = fcn, expLst = args)  => begin
                      fs = AbsynUtil.pathString(fcn)
                      argnodes = ListUtil.map(args, dumpExpGraphviz)
                    Graphviz.LNODE("CALL", list(fs), nil, argnodes)
                  end

                  DAE.PARTEVALFUNCTION(expList = args)  => begin
                      argnodes = ListUtil.map(args, dumpExpGraphviz)
                    Graphviz.NODE("PARTEVALFUNCTION", nil, argnodes)
                  end

                  DAE.ARRAY(array = es)  => begin
                      nodes = ListUtil.map(es, dumpExpGraphviz)
                    Graphviz.NODE("ARRAY", nil, nodes)
                  end

                  DAE.TUPLE(PR = es)  => begin
                      nodes = ListUtil.map(es, dumpExpGraphviz)
                    Graphviz.NODE("TUPLE", nil, nodes)
                  end

                  DAE.MATRIX(matrix = lstes)  => begin
                      s = stringDelimitList(ListUtil.map1(lstes, printRowStr, "\\"), "},{")
                      s = stringAppendList(list("{{", s, "}}"))
                    Graphviz.LNODE("MATRIX", list(s), nil, nil)
                  end

                  DAE.RANGE(start = start, step = NONE(), stop = stop)  => begin
                      t1 = dumpExpGraphviz(start)
                      t2 = Graphviz.NODE(":", nil, nil)
                      t3 = dumpExpGraphviz(stop)
                    Graphviz.NODE("RANGE", nil, list(t1, t2, t3))
                  end

                  DAE.RANGE(start = start, step = SOME(step), stop = stop)  => begin
                      t1 = dumpExpGraphviz(start)
                      t2 = dumpExpGraphviz(step)
                      t3 = dumpExpGraphviz(stop)
                    Graphviz.NODE("RANGE", nil, list(t1, t2, t3))
                  end

                  DAE.CAST(ty = ty, exp = e)  => begin
                      tystr = Types.unparseType(ty)
                      ct = dumpExpGraphviz(e)
                    Graphviz.LNODE("CAST", list(tystr), nil, list(ct))
                  end

                  DAE.ASUB(exp = e, sub = DAE.ICONST(i) <|  nil())  => begin
                      ct = dumpExpGraphviz(e)
                      istr = intString(i)
                      s = stringAppendList(list("[", istr, "]"))
                    Graphviz.LNODE("ASUB", list(s), nil, list(ct))
                  end

                  DAE.SIZE(exp = cr, sz = SOME(dim))  => begin
                      crt = dumpExpGraphviz(cr)
                      dimt = dumpExpGraphviz(dim)
                    Graphviz.NODE("SIZE", nil, list(crt, dimt))
                  end

                  DAE.SIZE(exp = cr, sz = NONE())  => begin
                      crt = dumpExpGraphviz(cr)
                    Graphviz.NODE("SIZE", nil, list(crt))
                  end

                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = fcn), expr = exp, iterators = DAE.REDUCTIONITER(exp = iterexp) <|  nil())  => begin
                      fs = AbsynUtil.pathString(fcn)
                      expt = dumpExpGraphviz(exp)
                      itert = dumpExpGraphviz(iterexp)
                    Graphviz.LNODE("REDUCTION", list(fs), nil, list(expt, itert))
                  end

                  _  => begin
                    Graphviz.NODE("#UNKNOWN EXPRESSION# ----eeestr ", nil, nil)
                  end
                end
              end
          outNode
        end

        #= Function: debugPrintComponentRefTypeStr
       This function is equal to debugPrintComponentRefTypeStr with the extra feature that it
       prints the base type of each ComponentRef.
       NOTE Only used for debugging. =#
       function debugPrintComponentRefTypeStr(inComponentRef::DAE.ComponentRef) ::String
             local outString::String

             outString = begin
                 local s::DAE.Ident
                 local str::DAE.Ident
                 local str2::DAE.Ident
                 local strrest::DAE.Ident
                 local str_1::DAE.Ident
                 local subs::List{DAE.Subscript}
                 local cr::DAE.ComponentRef
                 local ty::DAE.Type
               @match inComponentRef begin
                 DAE.WILD(__)  => begin
                   "_"
                 end

                 DAE.CREF_IDENT(ident = s, identType = ty, subscriptLst = subs)  => begin
                     str_1 = ExpressionDump.printListStr(subs, ExpressionDump.debugPrintSubscriptStr, ", ")
                     str = s + (if stringLength(str_1) > 0
                           "[" + str_1 + "]"
                         else
                           ""
                         end)
                     str2 = Types.unparseType(ty)
                     str = stringAppendList(list(str, " [", str2, "]"))
                   str
                 end

                 DAE.CREF_QUAL(ident = s, identType = ty, subscriptLst = subs, componentRef = cr)  => begin
                     if Config.modelicaOutput()
                       str = printComponentRef2Str(s, subs)
                       str2 = Types.unparseType(ty)
                       strrest = debugPrintComponentRefTypeStr(cr)
                       str = stringAppendList(list(str, " [", str2, "] ", "__", strrest))
                     else
                       str_1 = ExpressionDump.printListStr(subs, ExpressionDump.debugPrintSubscriptStr, ", ")
                       str = s + (if stringLength(str_1) > 0
                             "[" + str_1 + "]"
                           else
                             ""
                           end)
                       str2 = Types.unparseType(ty)
                       strrest = debugPrintComponentRefTypeStr(cr)
                       str = stringAppendList(list(str, " [", str2, "] ", ".", strrest))
                     end
                   str
                 end
               end
             end
         outString
       end

         #= Dumps expression to a string. =#
        function dumpExpStr(inExp::DAE.Exp, inInteger::ModelicaInteger) ::String
              local outString::String

              outString = begin
                  local gen_str::String
                  local res_str::String
                  local s::String
                  local sym::String
                  local lt::String
                  local rt::String
                  local ct::String
                  local tt::String
                  local ft::String
                  local fs::String
                  local argnodes_1::String
                  local nodes_1::String
                  local t1::String
                  local t2::String
                  local t3::String
                  local tystr::String
                  local istr::String
                  local crt::String
                  local dimt::String
                  local expt::String
                  local itert::String
                  local id::String
                  local tpStr::String
                  local str::String
                  local level::ModelicaInteger
                  local x::ModelicaInteger
                  local new_level1::ModelicaInteger
                  local new_level2::ModelicaInteger
                  local new_level3::ModelicaInteger
                  local i::ModelicaInteger
                  local c::DAE.ComponentRef
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local t::DAE.Exp
                  local f::DAE.Exp
                  local start::DAE.Exp
                  local stop::DAE.Exp
                  local step::DAE.Exp
                  local cr::DAE.Exp
                  local dim::DAE.Exp
                  local exp::DAE.Exp
                  local iterexp::DAE.Exp
                  local cond::DAE.Exp
                  local ae1::DAE.Exp
                  local op::DAE.Operator
                  local clk::DAE.ClockKind
                  local argnodes::List{String}
                  local nodes::List{String}
                  local fcn::Absyn.Path
                  local args::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local tp::DAE.Type
                  local ty::DAE.Type
                  local r::ModelicaReal
                  local lstes::List{List{DAE.Exp}}
                  local b::Bool
                @matchcontinue (inExp, inInteger) begin
                  (DAE.ICONST(integer = x), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = intString(x)
                      res_str = stringAppendList(list(gen_str, "ICONST ", s, "\\n"))
                    res_str
                  end

                  (DAE.RCONST(real = r), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = realString(r)
                      res_str = stringAppendList(list(gen_str, "RCONST ", s, "\\n"))
                    res_str
                  end

                  (DAE.SCONST(string = s), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = System.escapedString(s, true)
                      res_str = stringAppendList(list(gen_str, "SCONST ", "\\", s, "\\\\n"))
                    res_str
                  end

                  (DAE.BCONST(bool = false), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      res_str = stringAppendList(list(gen_str, "BCONST ", "false", "\\n"))
                    res_str
                  end

                  (DAE.BCONST(bool = true), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      res_str = stringAppendList(list(gen_str, "BCONST ", "true", "\\n"))
                    res_str
                  end

                  (DAE.CLKCONST(clk = clk), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = clockKindString(clk)
                      res_str = stringAppendList(list(gen_str, "CLKCONST ", s, "\\n"))
                    res_str
                  end

                  (DAE.ENUM_LITERAL(name = fcn, index = i), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = AbsynUtil.pathString(fcn)
                      istr = intString(i)
                      res_str = stringAppendList(list(gen_str, "ENUM_LITERAL ", s, " [", istr, "]", "\\n"))
                    res_str
                  end

                  (DAE.CREF(componentRef = c, ty = ty), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = debugPrintComponentRefTypeStr(c)
                      tpStr = Types.unparseType(ty)
                      res_str = stringAppendList(list(gen_str, "CREF ", s, " CREFTYPE:", tpStr, "\\n"))
                    res_str
                  end

                  (exp && DAE.BINARY(exp1 = e1, operator = op, exp2 = e2), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      sym = debugBinopSymbol(op)
                      tp = ExpressionUtil.typeof(exp)
                      str = Types.unparseType(tp)
                      lt = dumpExpStr(e1, new_level1)
                      rt = dumpExpStr(e2, new_level2)
                      res_str = stringAppendList(list(gen_str, "BINARY ", sym, " ", str, "\\n", lt, rt, ""))
                    res_str
                  end

                  (DAE.UNARY(operator = op, exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      sym = unaryopSymbol(op)
                      ct = dumpExpStr(e, new_level1)
                      str = "expType:" + Types.unparseType(ExpressionUtil.typeof(e)) + " optype:" + Types.unparseType(ExpressionUtil.typeofOp(op))
                      res_str = stringAppendList(list(gen_str, "UNARY ", sym, " ", str, "\\n", ct, ""))
                    res_str
                  end

                  (DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      sym = lbinopSymbol(op)
                      lt = dumpExpStr(e1, new_level1)
                      rt = dumpExpStr(e2, new_level2)
                      res_str = stringAppendList(list(gen_str, "LBINARY ", sym, "\\n", lt, rt, ""))
                    res_str
                  end

                  (DAE.LUNARY(operator = op, exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      sym = lunaryopSymbol(op)
                      ct = dumpExpStr(e, new_level1)
                      res_str = stringAppendList(list(gen_str, "LUNARY ", sym, "\\n", ct, ""))
                    res_str
                  end

                  (DAE.RELATION(exp1 = e1, operator = op, exp2 = e2), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      sym = relopSymbol(op)
                      lt = dumpExpStr(e1, new_level1)
                      rt = dumpExpStr(e2, new_level2)
                      res_str = stringAppendList(list(gen_str, "RELATION ", sym, "\\n", lt, rt, ""))
                    res_str
                  end

                  (DAE.IFEXP(expCond = cond, expThen = t, expElse = f), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      new_level3 = level + 1
                      ct = dumpExpStr(cond, new_level1)
                      tt = dumpExpStr(t, new_level2)
                      ft = dumpExpStr(f, new_level3)
                      res_str = stringAppendList(list(gen_str, "IFEXP ", "\\n", ct, tt, ft, ""))
                    res_str
                  end

                  (DAE.CALL(path = fcn, expLst = args), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      fs = AbsynUtil.pathString(fcn)
                      new_level1 = level + 1
                      argnodes = ListUtil.map1(args, dumpExpStr, new_level1)
                      argnodes_1 = stringAppendList(argnodes)
                      res_str = stringAppendList(list(gen_str, "CALL ", fs, "\\n", argnodes_1, ""))
                    res_str
                  end

                  (DAE.PARTEVALFUNCTION(path = fcn, expList = args), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      fs = AbsynUtil.pathString(fcn)
                      new_level1 = level + 1
                      argnodes = ListUtil.map1(args, dumpExpStr, new_level1)
                      argnodes_1 = stringAppendList(argnodes)
                      res_str = stringAppendList(list(gen_str, "CALL ", fs, "\\n", argnodes_1, ""))
                    res_str
                  end

                  (DAE.ARRAY(array = es, scalar = b, ty = tp), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      nodes = ListUtil.map1(es, dumpExpStr, new_level1)
                      nodes_1 = stringAppendList(nodes)
                      s = boolString(b)
                      tpStr = Types.unparseType(tp)
                      res_str = stringAppendList(list(gen_str, "ARRAY scalar:", s, " tp: ", tpStr, "\\n", nodes_1))
                    res_str
                  end

                  (DAE.TUPLE(PR = es), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      nodes = ListUtil.map1(es, dumpExpStr, new_level1)
                      nodes_1 = stringAppendList(nodes)
                      res_str = stringAppendList(list(gen_str, "TUPLE ", nodes_1, "\\n"))
                    res_str
                  end

                  (DAE.MATRIX(matrix = lstes), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      s = stringDelimitList(ListUtil.map1(lstes, printRowStr, "\\"), "},{")
                      res_str = stringAppendList(list(gen_str, "MATRIX ", "\\n", "{{", s, "}}", "\\n"))
                    res_str
                  end

                  (DAE.RANGE(start = start, step = NONE(), stop = stop), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      t1 = dumpExpStr(start, new_level1)
                      t2 = ":"
                      t3 = dumpExpStr(stop, new_level2)
                      res_str = stringAppendList(list(gen_str, "RANGE ", "\\n", t1, t2, t3, ""))
                    res_str
                  end

                  (DAE.RANGE(start = start, step = SOME(step), stop = stop), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      new_level3 = level + 1
                      t1 = dumpExpStr(start, new_level1)
                      t2 = dumpExpStr(step, new_level2)
                      t3 = dumpExpStr(stop, new_level3)
                      res_str = stringAppendList(list(gen_str, "RANGE ", "\\n", t1, t2, t3, ""))
                    res_str
                  end

                  (DAE.CAST(exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      res_str = stringAppendList(list(gen_str, "CAST ", "\\n", ct, ""))
                    res_str
                  end

                  (DAE.ASUB(exp = e, sub = DAE.ICONST(i) <|  nil()), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      istr = intString(i)
                      s = stringAppendList(list("[", istr, "]"))
                      res_str = stringAppendList(list(gen_str, "ASUB ", s, "\\n", ct, ""))
                    res_str
                  end

                  (DAE.ASUB(exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      res_str = stringAppendList(list(gen_str, "ASUB ", "\\n", ct, ""))
                    res_str
                  end

                  (DAE.SIZE(exp = cr, sz = SOME(dim)), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      crt = dumpExpStr(cr, new_level1)
                      dimt = dumpExpStr(dim, new_level2)
                      res_str = stringAppendList(list(gen_str, "SIZE ", "\\n", crt, dimt, ""))
                    res_str
                  end

                  (DAE.SIZE(exp = cr, sz = NONE()), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      crt = dumpExpStr(cr, new_level1)
                      res_str = stringAppendList(list(gen_str, "SIZE ", "\\n", crt, ""))
                    res_str
                  end

                  (DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(__), expr = exp, iterators = DAE.REDUCTIONITER(exp = iterexp) <|  nil()), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      new_level2 = level + 1
                      expt = dumpExpStr(exp, new_level1)
                      itert = dumpExpStr(iterexp, new_level2)
                      res_str = stringAppendList(list(gen_str, "REDUCTION ", "\\n", expt, itert, ""))
                    res_str
                  end

                  (DAE.RECORD(path = fcn, exps = args), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      fs = AbsynUtil.pathString(fcn)
                      new_level1 = level + 1
                      argnodes = ListUtil.map1(args, dumpExpStr, new_level1)
                      argnodes_1 = stringAppendList(argnodes)
                      res_str = stringAppendList(list(gen_str, "RECORD ", fs, "\\n", argnodes_1, ""))
                    res_str
                  end

                  (DAE.RSUB(exp = e, ix = i, fieldName = fs, ty = tp), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      istr = intString(i)
                      s = stringAppendList(list("[", istr, "]"))
                      tpStr = Types.unparseType(tp)
                      res_str = stringAppendList(list(gen_str, "RSUB ", s, " fieldName: ", fs, " tp: ", tpStr, "\\n", ct, ""))
                    res_str
                  end

                  (DAE.BOX(exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      res_str = stringAppendList(list(gen_str, "BOX ", "\\n", ct, ""))
                    res_str
                  end

                  (DAE.UNBOX(exp = e), level)  => begin
                      gen_str = genStringNTime("   |", level)
                      new_level1 = level + 1
                      ct = dumpExpStr(e, new_level1)
                      res_str = stringAppendList(list(gen_str, "UNBOX ", "\\n", ct, ""))
                    res_str
                  end

                  (_, level)  => begin
                      gen_str = genStringNTime("   |", level)
                      res_str = stringAppendList(list(gen_str, " UNKNOWN EXPRESSION (" + printExpTypeStr(inExp) + ")", "\\n"))
                    res_str
                  end
                end
              end
               #=  BTH TODO
               =#
               #= /*printComponentRefStr*/ =#
          outString
        end

         #= function:getStringNTime
          Appends the string to itself n times. =#
        function genStringNTime(inString::String, inInteger::ModelicaInteger) ::String
              local outString::String

              outString = begin
                  local str::String
                  local new_str::String
                  local res_str::String
                  local new_level::ModelicaInteger
                  local level::ModelicaInteger
                @matchcontinue (inString, inInteger) begin
                  (_, 0)  => begin
                    ""
                  end

                  (str, level)  => begin
                      new_level = level + (-1)
                      new_str = genStringNTime(str, new_level)
                      res_str = stringAppend(str, new_str)
                    res_str
                  end
                end
              end
               #= /* n */ =#
          outString
        end

         #=  =#
        function printExpIfDiff(e1::DAE.Exp, e2::DAE.Exp) ::String
              local s::String

              s = if ExpressionUtil.expEqual(e1, e2)
                    ""
                  else
                    printExpStr(e1) + " =!= " + printExpStr(e2) + "\\n"
                  end
          s
        end

         #= Function: printArraySizes =#
        function printArraySizes(inLst::List{<:Option{<:ModelicaInteger}}) ::String
              local out::String

              out = begin
                  local x::ModelicaInteger
                  local lst::List{Option{ModelicaInteger}}
                  local s::String
                  local s2::String
                @matchcontinue inLst begin
                   nil()  => begin
                    ""
                  end

                  SOME(x) <| lst  => begin
                      s = printArraySizes(lst)
                      s2 = intString(x)
                      s = stringAppendList(list(s2, s))
                    s
                  end

                  _ <| lst  => begin
                      s = printArraySizes(lst)
                    s
                  end
                end
              end
          out
        end

         #= Retrieves the Type of the Expression as a String =#
        function typeOfString(inExp::DAE.Exp) ::String
              local str::String

              local ty::DAE.Type

              ty = ExpressionUtil.typeof(inExp)
              str = Types.unparseType(ty)
          str
        end

         #=
        This function takes an DAE.Exp and tries to print ComponentReferences.
        Uses debugPrint.ComponentRefTypeStr, which gives type information to stdout.
        NOTE Only used for debugging.
         =#
        function debugPrintComponentRefExp(inExp::DAE.Exp) ::String
              local str::String

              str = begin
                  local cr::DAE.ComponentRef
                  local s1::String
                  local expl::List{DAE.Exp}
                @matchcontinue inExp begin
                  DAE.CREF(cr, _)  => begin
                    debugPrintComponentRefTypeStr(cr)
                  end

                  DAE.ARRAY(_, _, expl)  => begin
                      s1 = "{" + stringAppendList(ListUtil.map(expl, debugPrintComponentRefExp)) + "}"
                    s1
                  end

                  _  => begin
                      printExpStr(inExp)
                  end
                end
              end
               #=  when not cref, print expression anyways since it is used for some debugging.
               =#
          str
        end

         #= Returns a string representation of an array dimension. =#
        function dimensionString(dim::DAE.Dimension) ::String
              local str::String

              str = begin
                  local s::String
                  local x::ModelicaInteger
                  local p::Absyn.Path
                  local e::DAE.Exp
                  local size::ModelicaInteger
                @match dim begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    ":"
                  end

                  DAE.DIM_ENUM(enumTypeName = p)  => begin
                      s = AbsynUtil.pathString(p)
                    s
                  end

                  DAE.DIM_BOOLEAN(__)  => begin
                    "Boolean"
                  end

                  DAE.DIM_INTEGER(integer = x)  => begin
                      s = intString(x)
                    s
                  end

                  DAE.DIM_EXP(exp = e)  => begin
                      s = printExpStr(e)
                    s
                  end
                end
              end
          str
        end

         #= Returns a string representation of an array dimension. =#
        function dimensionsString(dims::DAE.Dimensions) ::String
              local str::String

              str = stringDelimitList(ListUtil.map(dims, dimensionString), ",")
          str
        end

         #= Returns a integer string representation of an array dimension. =#
        function dimensionIntString(dim::DAE.Dimension) ::String
              local str::String

              str = begin
                  local s::String
                  local x::ModelicaInteger
                  local size::ModelicaInteger
                  local e::DAE.Exp
                @match dim begin
                  DAE.DIM_UNKNOWN(__)  => begin
                    ":"
                  end

                  DAE.DIM_ENUM(size = size)  => begin
                    intString(size)
                  end

                  DAE.DIM_BOOLEAN(__)  => begin
                    "1"
                  end

                  DAE.DIM_INTEGER(integer = x)  => begin
                    intString(x)
                  end

                  DAE.DIM_EXP(exp = e)  => begin
                      s = printExpStr(e)
                    s
                  end
                end
              end
          str
        end

        function dumpExpWithTitle(title::String, exp::DAE.Exp)
              local str::String

              str = dumpExpStr(exp, 0)
              print(title)
              print(str)
              print("\\n")
        end

        function dumpExp(exp::DAE.Exp)
              local str::String

              str = dumpExpStr(exp, 0)
              print(str)
              print("--------------------\\n")
        end

         #= Print a Subscript. =#
        function printSubscript(inSubscript::DAE.Subscript)
              _ = begin
                  local e1::DAE.Exp
                @match inSubscript begin
                  DAE.WHOLEDIM(__)  => begin
                      Print.printBuf(":")
                    ()
                  end

                  DAE.INDEX(exp = e1)  => begin
                      printExp(e1)
                    ()
                  end

                  DAE.SLICE(exp = e1)  => begin
                      printExp(e1)
                    ()
                  end

                  DAE.WHOLE_NONEXP(exp = e1)  => begin
                      Print.printBuf("1:")
                      printExp(e1)
                    ()
                  end
                end
              end
        end

         #= This function prints a complete expression. =#
        function printExp(e::DAE.Exp)
        end

         #= Adds parentheisis to a string if expression
          and parent expression priorities requires it. =#
        function parenthesize(inString1::String, inInteger2::ModelicaInteger, inInteger3::ModelicaInteger, rightOpParenthesis::Bool #= true for right hand side operators =#) ::String
              local outString::String

              outString = begin
                  local str_1::String
                  local str::String
                  local pparent::ModelicaInteger
                  local pexpr::ModelicaInteger
                   #=  expr, prio. parent expr, prio. expr
                   =#
                @matchcontinue (inString1, inInteger2, inInteger3, rightOpParenthesis) begin
                  (str, pparent, pexpr, _)  => begin
                      if ! pparent > pexpr
                        fail()
                      end
                      str_1 = stringAppendList(list("(", str, ")"))
                    str_1
                  end

                  (str, pparent, pexpr, true)  => begin
                      if ! pparent == pexpr
                        fail()
                      end
                      str_1 = stringAppendList(list("(", str, ")"))
                    str_1
                  end

                  (str, _, _, _)  => begin
                    str
                  end
                end
              end
               #=  If priorites are equal and str is from right hand side, parenthesize to make left associative
               =#
          outString
        end

         #=
        Author: BTH
        Return textual representation of a ClockKind. =#
        function clockKindString(inClockKind::DAE.ClockKind) ::String
              local outString::String

              outString = begin
                  local c::DAE.Exp
                  local intervalCounter::DAE.Exp
                  local interval::DAE.Exp
                  local condition::DAE.Exp
                  local resolution::DAE.Exp
                  local startInterval::DAE.Exp
                  local solverMethod::DAE.Exp
                @match inClockKind begin
                  DAE.INFERRED_CLOCK(__)  => begin
                    "Clock()"
                  end

                  DAE.INTEGER_CLOCK(intervalCounter = intervalCounter, resolution = resolution)  => begin
                    "Clock(" + dumpExpStr(intervalCounter, 0) + ", " + dumpExpStr(resolution, 0) + ")"
                  end

                  DAE.REAL_CLOCK(interval = interval)  => begin
                    "Clock(" + dumpExpStr(interval, 0) + ")"
                  end

                  DAE.BOOLEAN_CLOCK(condition = condition, startInterval = startInterval)  => begin
                    "Clock(" + dumpExpStr(condition, 0) + ", " + dumpExpStr(startInterval, 0) + ")"
                  end

                  DAE.SOLVER_CLOCK(c = c, solverMethod = solverMethod)  => begin
                    "Clock(" + dumpExpStr(c, 0) + ", " + dumpExpStr(solverMethod, 0) + ")"
                  end
                end
              end
          outString
        end

         #=
        author: ptaeuber
        Converts DAE.CONSTRAINT_DT to string. =#
        function constraintDTtoString(con::DAE.Constraint) ::String
              local str::String

              local c::DAE.Exp
              local localCon::Bool

              @match DAE.CONSTRAINT_DT(constraint = c, localCon = localCon) = con
              str = printExpStr(c)
              str = if localCon
                    str + " (local)"
                  else
                    str + " (global)"
                  end
          str
        end

         #=
        author: ptaeuber
        Converts list of DAE.CONSTRAINT_DT to string. =#
        function constraintDTlistToString(cons::List{<:DAE.Constraint}, delim::String) ::String
              local str::String = ""

              local c::DAE.Exp
              local localCon::Bool
              local con::DAE.Constraint

              for con in cons
                str = str + delim + constraintDTtoString(con)
              end
          str
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

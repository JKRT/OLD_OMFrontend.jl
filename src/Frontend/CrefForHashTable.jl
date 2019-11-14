

module CrefForHashTable

    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

@importDBG Absyn
@importDBG AbsynUtil
@importDBG DAE
@importDBG Tpl
@importDBG Print
import MetaModelica.Dangerous

FuncCrefTypeA = Function
FuncExpType = Function
FuncExpType2 = Function
FuncType = Function
MapFunc = Function
Argument = Any
Type_a = Any
FuncTypeType_aToString = Function
FuncTypeType_aTo = Function


module LocalExpressionDumpTpl


  using MetaModelica
  #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
  using ExportAll

      @importDBG Tpl

      @importDBG Absyn

      @importDBG ClassInf

      @importDBG DAE

      @importDBG Dump

      @importDBG ExpressionPriority

      @importDBG System

      @importDBG Config

      @importDBG Flags

      @importDBG AbsynDumpTpl

      function local_unparseType(inType::DAE.Type) ::String
            local outString::String

            outString = begin
                local s1::String
                local s2::String
                local str::String
                local dims::String
                local res::String
                local vstr::String
                local name::String
                local st_str::String
                local bc_tp_str::String
                local paramstr::String
                local restypestr::String
                local tystr::String
                local funcstr::String
                local l::List{String}
                local vars::List{String}
                local paramstrs::List{String}
                local tystrs::List{String}
                local ty::Type
                local bc_tp::Type
                local restype::Type
                local dimlst::DAE.Dimensions
                local vs::List{DAE.Var}
                local ci_state::ClassInf.SMNode
                local params::List{DAE.FuncArg}
                local path::Absyn.Path
                local p::Absyn.Path
                local tys::List{DAE.Type}
                local codeType::DAE.CodeType
                local b::Bool
              @match inType begin
                DAE.T_INTEGER(varLst =  nil())  => begin
                  "Integer"
                end

                DAE.T_REAL(varLst =  nil())  => begin
                  "Real"
                end

                DAE.T_STRING(varLst =  nil())  => begin
                  "String"
                end

                DAE.T_BOOL(varLst =  nil())  => begin
                  "Boolean"
                end

                DAE.T_CLOCK(__)  => begin
                  "Clock"
                end

                DAE.T_INTEGER(varLst = vs)  => begin
                    s1 = stringDelimitList(ListUtil.map(vs, unparseVarAttr), ", ")
                    s2 = "Integer(" + s1 + ")"
                  s2
                end

                DAE.T_REAL(varLst = vs)  => begin
                    s1 = stringDelimitList(ListUtil.map(vs, unparseVarAttr), ", ")
                    s2 = "Real(" + s1 + ")"
                  s2
                end

                DAE.T_STRING(varLst = vs)  => begin
                    s1 = stringDelimitList(ListUtil.map(vs, unparseVarAttr), ", ")
                    s2 = "String(" + s1 + ")"
                  s2
                end

                DAE.T_BOOL(varLst = vs)  => begin
                    s1 = stringDelimitList(ListUtil.map(vs, unparseVarAttr), ", ")
                    s2 = "Boolean(" + s1 + ")"
                  s2
                end

                DAE.T_ENUMERATION(path = path, names = l)  => begin
                    s1 = if Config.typeinfo()
                          " /*" + AbsynUtil.pathString(path) + "*/ ("
                        else
                          "("
                        end
                    s2 = stringDelimitList(l, ", ")
                    str = stringAppendList(list("enumeration", s1, s2, ")"))
                  str
                end

                ty && DAE.T_ARRAY(__)  => begin
                    (ty, dimlst) = flattenArrayType(ty)
                    tystr = local_unparseType(ty)
                    dims = printDimensionsStr(dimlst)
                    res = stringAppendList(list(tystr, "[", dims, "]"))
                  res
                end

                DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path), varLst = vs)  => begin
                    name = AbsynUtil.pathStringNoQual(path)
                    vars = ListUtil.map(vs, unparseVar)
                    vstr = stringAppendList(vars)
                    res = stringAppendList(list("record ", name, "\\n", vstr, "end ", name, ";"))
                  res
                end

                DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(path, b), varLst = vs)  => begin
                    name = AbsynUtil.pathStringNoQual(path)
                    vars = ListUtil.map(vs, unparseVar)
                    vstr = stringAppendList(vars)
                    str = if b
                          "expandable "
                        else
                          ""
                        end
                    res = stringAppendList(list(str, "connector ", name, "\\n", vstr, "end ", name, ";"))
                  res
                end

                DAE.T_SUBTYPE_BASIC(complexClassType = ci_state, complexType = bc_tp)  => begin
                    st_str = AbsynUtil.pathString(ClassInf.getStateName(ci_state))
                    res = ClassInf.printStateStr(ci_state)
                    bc_tp_str = local_unparseType(bc_tp)
                    res = stringAppendList(list("(", res, " ", st_str, " bc:", bc_tp_str, ")"))
                  res
                end

                DAE.T_COMPLEX(complexClassType = ci_state)  => begin
                    st_str = AbsynUtil.pathString(ClassInf.getStateName(ci_state))
                    res = ClassInf.printStateStr(ci_state)
                    res = stringAppendList(list(res, " ", st_str))
                  res
                end

                DAE.T_FUNCTION(funcArg = params, funcResultType = restype, path = path)  => begin
                    funcstr = AbsynUtil.pathString(path)
                    paramstrs = ListUtil.map(params, unparseParam)
                    paramstr = stringDelimitList(paramstrs, ", ")
                    restypestr = local_unparseType(restype)
                    res = stringAppendList(list(funcstr, "<function>(", paramstr, ") => ", restypestr))
                  res
                end

                DAE.T_TUPLE(types = tys)  => begin
                    tystrs = begin
                         #=  BTH
                         =#
                         #= /* s2 = stringAppendList(List.map(vs, unparseVar));
                                s2 = if_(s2 == \"\", \"\", \"(\" + s2 + \")\"); */ =#
                        local names::List{String}
                      @match inType.names begin
                        SOME(names)  => begin
                          list(@do_threaded_for local_unparseType(t) + " " + n (t, n) (tys, names))
                        end

                        _  => begin
                            list(local_unparseType(t) for t in tys)
                        end
                      end
                    end
                    tystr = stringDelimitList(tystrs, ", ")
                    res = stringAppendList(list("(", tystr, ")"))
                  res
                end

                DAE.T_METATUPLE(types = tys)  => begin
                    tystrs = ListUtil.map(tys, local_unparseType)
                    tystr = stringDelimitList(tystrs, ", ")
                    res = stringAppendList(list("tuple<", tystr, ">"))
                  res
                end

                DAE.T_METALIST(ty = ty)  => begin
                    tystr = local_unparseType(ty)
                    res = stringAppendList(list("list<", tystr, ">"))
                  res
                end

                DAE.T_METAARRAY(ty = ty)  => begin
                    tystr = local_unparseType(ty)
                    res = stringAppendList(list("array<", tystr, ">"))
                  res
                end

                DAE.T_METAPOLYMORPHIC(name = tystr)  => begin
                    res = stringAppendList(list("polymorphic<", tystr, ">"))
                  res
                end

                DAE.T_METAUNIONTYPE(__)  => begin
                    res = AbsynUtil.pathStringNoQual(inType.path)
                  if listEmpty(inType.typeVars)
                        res
                      else
                        res + "<" + stringDelimitList(list(local_unparseType(tv) for tv in inType.typeVars), ",") + ">"
                      end
                end

                DAE.T_METARECORD(__)  => begin
                    res = AbsynUtil.pathStringNoQual(inType.path)
                  if listEmpty(inType.typeVars)
                        res
                      else
                        res + "<" + stringDelimitList(list(local_unparseType(tv) for tv in inType.typeVars), ",") + ">"
                      end
                end

                DAE.T_METABOXED(ty = ty)  => begin
                    res = local_unparseType(ty)
                    res = "#" + res
                  res
                end

                DAE.T_METAOPTION(ty = DAE.T_UNKNOWN(__))  => begin
                  "Option<Any>"
                end

                DAE.T_METAOPTION(ty = ty)  => begin
                    tystr = local_unparseType(ty)
                    res = stringAppendList(list("Option<", tystr, ">"))
                  res
                end

                DAE.T_METATYPE(ty = ty)  => begin
                  local_unparseType(ty)
                end

                DAE.T_NORETCALL(__)  => begin
                  "#NORETCALL#"
                end

                DAE.T_UNKNOWN(__)  => begin
                  "#T_UNKNOWN#"
                end

                DAE.T_ANYTYPE(__)  => begin
                  "#ANYTYPE#"
                end

                DAE.T_CODE(ty = codeType)  => begin
                  printCodeTypeStr(codeType)
                end

                DAE.T_FUNCTION_REFERENCE_VAR(functionType = ty)  => begin
                  "#FUNCTION_REFERENCE_VAR#" + local_unparseType(ty)
                end

                DAE.T_FUNCTION_REFERENCE_FUNC(functionType = ty)  => begin
                  "#FUNCTION_REFERENCE_FUNC#" + local_unparseType(ty)
                end

                _  => begin
                    "Internal error local_unparseType: not implemented yet\\n"
                end
              end
            end
             #=  MetaModelica tuple
             =#
             #=  MetaModelica list
             =#
             #=  MetaModelica list
             =#
             #=  MetaModelica uniontype
             =#
             #=  MetaModelica uniontype (but we know which record in the UT it is)
             =#
             #= /*
                case (DAE.T_METARECORD(utPath=_, fields = vs, source = {p}))
                  equation
                    str = AbsynUtil.pathStringNoQual(p);
                    vars = List.map(vs, unparseVar);
                    vstr = stringAppendList(vars);
                    res = stringAppendList({\"metarecord \",str,\"\\n\",vstr,\"end \", str, \";\"});
                  then res;
            */ =#
             #=  MetaModelica boxed type
             =#
             #= /* this is a box */ =#
             #=  MetaModelica Option type
             =#
        outString
      end

      function fun_12(in_txt::Tpl.Text, in_mArg::Bool, in_a_index::ModelicaInteger) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_index::ModelicaInteger
              @match (in_txt, in_mArg, in_a_index) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_index)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* "))
                    txt = Tpl.writeStr(txt, intString(a_index))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_13(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_0::String
              @match (in_txt, in_mArg, in_a_ty) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*"))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/ "))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_14(in_txt::Tpl.Text, in_mArg::Bool, in_a_attr_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_attr_ty::DAE.Type
                local ret_0::String
              @match (in_txt, in_mArg, in_a_attr_ty) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_attr_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*"))
                    ret_0 = local_unparseType(a_attr_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/ "))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_15(in_txt::Tpl.Text, in_a_scalar::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_1::String
                local ret_0::String
              @match (in_txt, in_a_scalar, in_a_ty) begin
                (txt, false, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* non-scalar "))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* scalar "))
                    ret_1 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_1)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_16(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type, in_a_scalar::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local a_scalar::Bool
              @match (in_txt, in_mArg, in_a_ty, in_a_scalar) begin
                (txt, false, _, _)  => begin
                  txt
                end

                (txt, _, a_ty, a_scalar)  => begin
                    txt = fun_15(txt, a_scalar, a_ty)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_17(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type, in_a_scalar::Bool, in_a_stringDelimiter::String, in_a_array::List{<:DAE.Exp}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local a_scalar::Bool
                local a_stringDelimiter::String
                local a_array::List{DAE.Exp}
                local ret_1::Bool
                local l_expl::Tpl.Text
              @match (in_txt, in_mArg, in_a_ty, in_a_scalar, in_a_stringDelimiter, in_a_array) begin
                (txt, false, a_ty, a_scalar, a_stringDelimiter, a_array)  => begin
                    l_expl = dumpExpList(Tpl.emptyTxt, a_array, a_stringDelimiter, ", ")
                    ret_1 = Config.typeinfo()
                    txt = fun_16(txt, ret_1, a_ty, a_scalar)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("{"))
                    txt = Tpl.writeText(txt, l_expl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("}"))
                  txt
                end

                (txt, _, _, _, _, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("fill(0,0)"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_18(in_txt::Tpl.Text, in_a_scalar::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_1::String
                local ret_0::String
              @match (in_txt, in_a_scalar, in_a_ty) begin
                (txt, false, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* non-scalar "))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* scalar "))
                    ret_1 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_1)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_19(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type, in_a_scalar::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local a_scalar::Bool
              @match (in_txt, in_mArg, in_a_ty, in_a_scalar) begin
                (txt, false, _, _)  => begin
                  txt
                end

                (txt, _, a_ty, a_scalar)  => begin
                    txt = fun_18(txt, a_scalar, a_ty)
                  txt
                end
              end
            end
        out_txt
      end

      function lm_20(in_txt::Tpl.Text, in_items::List{<:List{<:DAE.Exp}}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{List{DAE.Exp}}
                local a_stringDelimiter::String
                local i_row::List{DAE.Exp}
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_row <| rest, a_stringDelimiter)  => begin
                    txt = dumpExpList(txt, i_row, a_stringDelimiter, ", ")
                    txt = Tpl.nextIter(txt)
                    txt = lm_20(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_21(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_0::String
              @match (in_txt, in_mArg, in_a_ty) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* matrix "))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_22(in_txt::Tpl.Text, in_a_step::Option{<:DAE.Exp}, in_a_e::DAE.Exp) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_e::DAE.Exp
                local i_step::DAE.Exp
              @match (in_txt, in_a_step, in_a_e) begin
                (txt, SOME(i_step), a_e)  => begin
                    txt = dumpOperand(txt, i_step, a_e, false)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function fun_23(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_24(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_25(in_txt::Tpl.Text, in_mArg::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_mArg) begin
                (txt, false)  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*ASUB*/"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_26(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_27(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_28(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_29(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_30(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_0::String
              @match (in_txt, in_mArg, in_a_ty) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*RSUB: "))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_31(in_txt::Tpl.Text, in_a_sz::Option{<:DAE.Exp}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_dim::DAE.Exp
              @match (in_txt, in_a_sz, in_a_stringDelimiter) begin
                (txt, SOME(i_dim), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = dumpExp(txt, i_dim, a_stringDelimiter)
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_32(in_txt::Tpl.Text, in_items::DAE.ReductionIterators, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::DAE.ReductionIterators
                local a_stringDelimiter::String
                local i_it::DAE.ReductionIterator
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_it <| rest, a_stringDelimiter)  => begin
                    txt = dumpReductionIterator(txt, i_it, a_stringDelimiter)
                    txt = Tpl.nextIter(txt)
                    txt = lm_32(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_33(in_txt::Tpl.Text, in_a_ri_iterType::Absyn.ReductionIterType) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_ri_iterType) begin
                (txt, Absyn.THREAD(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("threaded "))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_34(in_txt::Tpl.Text, in_items::List{<:DAE.MatchCase}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.MatchCase}
                local i_c::DAE.MatchCase
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_c <| rest)  => begin
                    txt = dumpMatchCase(txt, i_c)
                    txt = Tpl.nextIter(txt)
                    txt = lm_34(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_35(in_txt::Tpl.Text, in_mArg::Bool, in_a_index::ModelicaInteger, in_a_stringDelimiter::String, in_a_exp::DAE.Exp) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_index::ModelicaInteger
                local a_stringDelimiter::String
                local a_exp::DAE.Exp
              @match (in_txt, in_mArg, in_a_index, in_a_stringDelimiter, in_a_exp) begin
                (txt, false, _, a_stringDelimiter, a_exp)  => begin
                    txt = dumpExp(txt, a_exp, a_stringDelimiter)
                  txt
                end

                (txt, _, a_index, a_stringDelimiter, a_exp)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* Shared literal "))
                    txt = Tpl.writeStr(txt, intString(a_index))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                    txt = dumpExp(txt, a_exp, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_36(in_txt::Tpl.Text, in_mArg::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_mArg) begin
                (txt, false)  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*pattern*/"))
                  txt
                end
              end
            end
        out_txt
      end

      function dumpExp(in_txt::Tpl.Text, in_a_exp::DAE.Exp, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_pattern::DAE.Pattern
                local i_cases::List{DAE.MatchCase}
                local i_inputs::List{DAE.Exp}
                local i_matchType::DAE.MatchType
                local i_args::List{DAE.Exp}
                local i_listExp::List{DAE.Exp}
                local i_cdr::DAE.Exp
                local i_car::DAE.Exp
                local i_valList::List{DAE.Exp}
                local i_ri_iterType::Absyn.ReductionIterType
                local i_iterators::DAE.ReductionIterators
                local i_expr::DAE.Exp
                local i_ri_path::Absyn.Path
                local i_tyStr::String
                local i_scope::String
                local i_name_1::DAE.ComponentRef
                local i_code::Absyn.CodeNode
                local i_sz::Option{DAE.Exp}
                local i_fieldName::String
                local i_ix::ModelicaInteger
                local i_sub::List{DAE.Exp}
                local i_PR::List{DAE.Exp}
                local i_stop::DAE.Exp
                local i_step::Option{DAE.Exp}
                local i_start::DAE.Exp
                local i_matrix::List{List{DAE.Exp}}
                local i_scalar::Bool
                local i_array::List{DAE.Exp}
                local i_expList::List{DAE.Exp}
                local i_exps::List{DAE.Exp}
                local i_attr_ty::DAE.Type
                local i_expLst::List{DAE.Exp}
                local i_path::Absyn.Path
                local i_expElse::DAE.Exp
                local i_expThen::DAE.Exp
                local i_expCond::DAE.Exp
                local i_exp::DAE.Exp
                local i_operator::DAE.Operator
                local i_exp2::DAE.Exp
                local i_e::DAE.Exp
                local i_exp1::DAE.Exp
                local i_componentRef::DAE.ComponentRef
                local i_ty::DAE.Type
                local i_name::Absyn.Path
                local i_index::ModelicaInteger
                local i_clk::DAE.ClockKind
                local i_bool::Bool
                local i_string::String
                local i_real::ModelicaReal
                local i_integer::ModelicaInteger
                local ret_43::Bool
                local ret_42::Bool
                local l_case__str::Tpl.Text
                local l_inputs__str::Tpl.Text
                local l_match__ty::Tpl.Text
                local l_args__str::Tpl.Text
                local l_cdr__str::Tpl.Text
                local l_car__str::Tpl.Text
                local l_expl__str::Tpl.Text
                local l_iter__str::Tpl.Text
                local l_name__str::Tpl.Text
                local ret_32::String
                local l_code__str::Tpl.Text
                local l_dim__str::Tpl.Text
                local ret_29::Bool
                local ret_28::Bool
                local l_sub__str::Tpl.Text
                local l_rparen::Tpl.Text
                local l_lparen::Tpl.Text
                local l_needs__paren::Tpl.Text
                local l_ty__str::Tpl.Text
                local l_tuple__str::Tpl.Text
                local l_stop__str::Tpl.Text
                local l_step__str::Tpl.Text
                local l_start__str::Tpl.Text
                local ret_18::Bool
                local l_mat__str::Tpl.Text
                local ret_16::Bool
                local l_expl::Tpl.Text
                local ret_14::Bool
                local ret_13::Bool
                local l_argl::Tpl.Text
                local l_func__str::Tpl.Text
                local l_else__str::Tpl.Text
                local l_then__str::Tpl.Text
                local l_cond__str::Tpl.Text
                local l_exp__str::Tpl.Text
                local l_op__str::Tpl.Text
                local l_rhs__str::Tpl.Text
                local l_lhs__str::Tpl.Text
                local ret_3::Bool
                local ret_2::Bool
                local ret_1::String
                local l_str::Tpl.Text
              @match (in_txt, in_a_exp, in_a_stringDelimiter) begin
                (txt, DAE.ICONST(integer = i_integer), _)  => begin
                    txt = Tpl.writeStr(txt, intString(i_integer))
                  txt
                end

                (txt, DAE.RCONST(real = i_real), _)  => begin
                    txt = Tpl.writeStr(txt, realString(i_real))
                  txt
                end

                (txt, DAE.SCONST(string = i_string), a_stringDelimiter)  => begin
                    ret_1 = System.escapedString(i_string, false)
                    l_str = Tpl.writeStr(Tpl.emptyTxt, ret_1)
                    txt = Tpl.writeStr(txt, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_str)
                    txt = Tpl.writeStr(txt, a_stringDelimiter)
                  txt
                end

                (txt, DAE.BCONST(bool = i_bool), _)  => begin
                    txt = Tpl.writeStr(txt, Tpl.booleanString(i_bool))
                  txt
                end

                (txt, DAE.CLKCONST(clk = i_clk), a_stringDelimiter)  => begin
                    txt = dumpClockKind(txt, i_clk, a_stringDelimiter)
                  txt
                end

                (txt, DAE.ENUM_LITERAL(index = i_index, name = i_name), _)  => begin
                    ret_2 = Config.typeinfo()
                    txt = fun_12(txt, ret_2, i_index)
                    txt = AbsynDumpTpl.dumpPath(txt, i_name)
                  txt
                end

                (txt, DAE.CREF(ty = i_ty, componentRef = i_componentRef), _)  => begin
                    ret_3 = Config.typeinfo()
                    txt = fun_13(txt, ret_3, i_ty)
                    txt = dumpCref(txt, i_componentRef)
                  txt
                end

                (txt, i_e && DAE.BINARY(exp1 = i_exp1, exp2 = i_exp2, operator = i_operator), _)  => begin
                    l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e, true)
                    l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e, false)
                    l_op__str = dumpBinOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, i_e && DAE.UNARY(exp = i_exp, operator = i_operator), _)  => begin
                    l_exp__str = dumpOperand(Tpl.emptyTxt, i_exp, i_e, false)
                    l_op__str = dumpUnaryOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeText(txt, l_exp__str)
                  txt
                end

                (txt, i_e && DAE.LBINARY(exp1 = i_exp1, exp2 = i_exp2, operator = i_operator), _)  => begin
                    l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e, true)
                    l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e, false)
                    l_op__str = dumpLogicalBinOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, i_e && DAE.LUNARY(exp = i_exp, operator = i_operator), _)  => begin
                    l_exp__str = dumpOperand(Tpl.emptyTxt, i_exp, i_e, false)
                    l_op__str = dumpLogicalUnaryOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_exp__str)
                  txt
                end

                (txt, i_e && DAE.RELATION(exp1 = i_exp1, exp2 = i_exp2, operator = i_operator), _)  => begin
                    l_lhs__str = dumpOperand(Tpl.emptyTxt, i_exp1, i_e, true)
                    l_rhs__str = dumpOperand(Tpl.emptyTxt, i_exp2, i_e, false)
                    l_op__str = dumpRelationOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, DAE.IFEXP(expCond = i_expCond, expThen = i_expThen, expElse = i_expElse), a_stringDelimiter)  => begin
                    l_cond__str = dumpExp(Tpl.emptyTxt, i_expCond, a_stringDelimiter)
                    l_then__str = dumpExp(Tpl.emptyTxt, i_expThen, a_stringDelimiter)
                    l_else__str = dumpExp(Tpl.emptyTxt, i_expElse, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("if "))
                    txt = Tpl.writeText(txt, l_cond__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" then "))
                    txt = Tpl.writeText(txt, l_then__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" else "))
                    txt = Tpl.writeText(txt, l_else__str)
                  txt
                end

                (txt, DAE.CALL(attr = DAE.CALL_ATTR(builtin = true, ty = i_attr_ty), path = i_path, expLst = i_expLst), a_stringDelimiter)  => begin
                    l_func__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_path)
                    l_argl = dumpExpList(Tpl.emptyTxt, i_expLst, a_stringDelimiter, ", ")
                    ret_13 = Config.typeinfo()
                    txt = fun_14(txt, ret_13, i_attr_ty)
                    txt = Tpl.writeText(txt, l_func__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_argl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CALL(path = i_path, expLst = i_expLst), a_stringDelimiter)  => begin
                    l_func__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_path)
                    l_argl = dumpExpList(Tpl.emptyTxt, i_expLst, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_func__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_argl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.RECORD(path = i_path, exps = i_exps), a_stringDelimiter)  => begin
                    l_func__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_path)
                    l_argl = dumpExpList(Tpl.emptyTxt, i_exps, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_func__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_argl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PARTEVALFUNCTION(path = i_path, expList = i_expList), a_stringDelimiter)  => begin
                    l_func__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_path)
                    l_argl = dumpExpList(Tpl.emptyTxt, i_expList, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("function "))
                    txt = Tpl.writeText(txt, l_func__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_argl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.ARRAY(array = i_array &&  nil(), scalar = i_scalar, ty = i_ty), a_stringDelimiter)  => begin
                    ret_14 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                    txt = fun_17(txt, ret_14, i_ty, i_scalar, a_stringDelimiter, i_array)
                  txt
                end

                (txt, DAE.ARRAY(array = i_array, scalar = i_scalar, ty = i_ty), a_stringDelimiter)  => begin
                    l_expl = dumpExpList(Tpl.emptyTxt, i_array, a_stringDelimiter, ", ")
                    ret_16 = Config.typeinfo()
                    txt = fun_19(txt, ret_16, i_ty, i_scalar)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("{"))
                    txt = Tpl.writeText(txt, l_expl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("}"))
                  txt
                end

                (txt, DAE.MATRIX(matrix = i_matrix, ty = i_ty), a_stringDelimiter)  => begin
                    l_mat__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING("}, {")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_mat__str = lm_20(l_mat__str, i_matrix, a_stringDelimiter)
                    l_mat__str = Tpl.popIter(l_mat__str)
                    ret_18 = Config.typeinfo()
                    txt = fun_21(txt, ret_18, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("{{"))
                    txt = Tpl.writeText(txt, l_mat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("}}"))
                  txt
                end

                (txt, i_e && DAE.RANGE(start = i_start, step = i_step, stop = i_stop), _)  => begin
                    l_start__str = dumpOperand(Tpl.emptyTxt, i_start, i_e, false)
                    l_step__str = fun_22(Tpl.emptyTxt, i_step, i_e)
                    l_stop__str = dumpOperand(Tpl.emptyTxt, i_stop, i_e, false)
                    txt = Tpl.writeText(txt, l_start__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                    txt = Tpl.writeText(txt, l_step__str)
                    txt = Tpl.writeText(txt, l_stop__str)
                  txt
                end

                (txt, DAE.TUPLE(PR = i_PR), a_stringDelimiter)  => begin
                    l_tuple__str = dumpExpList(Tpl.emptyTxt, i_PR, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_tuple__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CAST(exp = i_exp, ty = i_ty), a_stringDelimiter)  => begin
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_ty__str = dumpType(Tpl.emptyTxt, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/*"))
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*/("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.ASUB(exp = i_exp, sub = i_sub), a_stringDelimiter)  => begin
                    l_needs__paren = parenthesizeSubExp(Tpl.emptyTxt, i_exp)
                    l_lparen = fun_23(Tpl.emptyTxt, l_needs__paren)
                    l_rparen = fun_24(Tpl.emptyTxt, l_needs__paren)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_sub__str = dumpExpList(Tpl.emptyTxt, i_sub, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_lparen)
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_rparen)
                    ret_28 = Config.typeinfo()
                    txt = fun_25(txt, ret_28)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeText(txt, l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, DAE.TSUB(exp = i_exp, ix = i_ix), a_stringDelimiter)  => begin
                    l_needs__paren = parenthesizeSubExp(Tpl.emptyTxt, i_exp)
                    l_lparen = fun_26(Tpl.emptyTxt, l_needs__paren)
                    l_rparen = fun_27(Tpl.emptyTxt, l_needs__paren)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lparen)
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_rparen)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeStr(txt, intString(i_ix))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, DAE.RSUB(exp = i_exp, ty = i_ty, fieldName = i_fieldName), a_stringDelimiter)  => begin
                    l_needs__paren = parenthesizeSubExp(Tpl.emptyTxt, i_exp)
                    l_lparen = fun_28(Tpl.emptyTxt, l_needs__paren)
                    l_rparen = fun_29(Tpl.emptyTxt, l_needs__paren)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    ret_29 = Config.typeinfo()
                    txt = fun_30(txt, ret_29, i_ty)
                    txt = Tpl.writeText(txt, l_lparen)
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_rparen)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("."))
                    txt = Tpl.writeStr(txt, i_fieldName)
                  txt
                end

                (txt, DAE.SIZE(exp = i_exp, sz = i_sz), a_stringDelimiter)  => begin
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_dim__str = fun_31(Tpl.emptyTxt, i_sz, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("size("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_dim__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CODE(code = i_code), _)  => begin
                    ret_32 = Dump.printCodeStr(i_code)
                    l_code__str = Tpl.writeStr(Tpl.emptyTxt, ret_32)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Code("))
                    txt = Tpl.writeText(txt, l_code__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.EMPTY(name = i_name_1, scope = i_scope, tyStr = i_tyStr), _)  => begin
                    l_name__str = dumpCref(Tpl.emptyTxt, i_name_1)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<EMPTY(scope: "))
                    txt = Tpl.writeStr(txt, i_scope)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", name: "))
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", ty: "))
                    txt = Tpl.writeStr(txt, i_tyStr)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")>"))
                  txt
                end

                (txt, DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = i_ri_path, iterType = i_ri_iterType), expr = i_expr, iterators = i_iterators), a_stringDelimiter)  => begin
                    l_name__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_ri_path)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_expr, a_stringDelimiter)
                    l_iter__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_iter__str = lm_32(l_iter__str, i_iterators, a_stringDelimiter)
                    l_iter__str = Tpl.popIter(l_iter__str)
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" for "))
                    txt = fun_33(txt, i_ri_iterType)
                    txt = Tpl.writeText(txt, l_iter__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.LIST(valList = i_valList), a_stringDelimiter)  => begin
                    l_expl__str = dumpExpList(Tpl.emptyTxt, i_valList, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("List("))
                    txt = Tpl.writeText(txt, l_expl__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CONS(car = i_car, cdr = i_cdr), a_stringDelimiter)  => begin
                    l_car__str = dumpExp(Tpl.emptyTxt, i_car, a_stringDelimiter)
                    l_cdr__str = dumpExp(Tpl.emptyTxt, i_cdr, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("listCons("))
                    txt = Tpl.writeText(txt, l_car__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = Tpl.writeText(txt, l_cdr__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_TUPLE(listExp = i_listExp), a_stringDelimiter)  => begin
                    l_tuple__str = dumpExpList(Tpl.emptyTxt, i_listExp, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Tuple("))
                    txt = Tpl.writeText(txt, l_tuple__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_OPTION(exp = SOME(i_exp)), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("SOME("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_OPTION(exp = _), _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("NONE()"))
                  txt
                end

                (txt, DAE.METARECORDCALL(path = i_path, args = i_args), a_stringDelimiter)  => begin
                    l_name__str = AbsynDumpTpl.dumpPath(Tpl.emptyTxt, i_path)
                    l_args__str = dumpExpList(Tpl.emptyTxt, i_args, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_args__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.MATCHEXPRESSION(matchType = i_matchType, inputs = i_inputs, cases = i_cases), a_stringDelimiter)  => begin
                    l_match__ty = dumpMatchType(Tpl.emptyTxt, i_matchType)
                    l_inputs__str = dumpExpList(Tpl.emptyTxt, i_inputs, a_stringDelimiter, ", ")
                    l_case__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_case__str = lm_34(l_case__str, i_cases)
                    l_case__str = Tpl.popIter(l_case__str)
                    txt = Tpl.writeText(txt, l_match__ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" ("))
                    txt = Tpl.writeText(txt, l_inputs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_LINE(")\\n"))
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(4))
                    txt = Tpl.writeText(txt, l_case__str)
                    txt = Tpl.softNewLine(txt)
                    txt = Tpl.popBlock(txt)
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                    txt = Tpl.writeText(txt, l_match__ty)
                    txt = Tpl.popBlock(txt)
                  txt
                end

                (txt, DAE.BOX(exp = i_exp), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("#("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.UNBOX(exp = i_exp), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("unbox("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.SHARED_LITERAL(exp = i_exp, index = i_index), a_stringDelimiter)  => begin
                    ret_42 = Config.typeinfo()
                    txt = fun_35(txt, ret_42, i_index, a_stringDelimiter, i_exp)
                  txt
                end

                (txt, DAE.PATTERN(pattern = i_pattern), _)  => begin
                    ret_43 = Config.typeinfo()
                    txt = fun_36(txt, ret_43)
                    txt = dumpPattern(txt, i_pattern)
                  txt
                end

                (txt, _, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpExp: Unknown expression.")
                  txt
                end
              end
            end
        out_txt
      end

      function parenthesizeSubExp(in_txt::Tpl.Text, in_a_exp::DAE.Exp) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_exp) begin
                (txt, DAE.ICONST(integer = _))  => begin
                  txt
                end

                (txt, DAE.RCONST(real = _))  => begin
                  txt
                end

                (txt, DAE.SCONST(string = _))  => begin
                  txt
                end

                (txt, DAE.BCONST(bool = _))  => begin
                  txt
                end

                (txt, DAE.ENUM_LITERAL(name = _))  => begin
                  txt
                end

                (txt, DAE.CREF(componentRef = _))  => begin
                  txt
                end

                (txt, DAE.CALL(path = _))  => begin
                  txt
                end

                (txt, DAE.ARRAY(ty = _))  => begin
                  txt
                end

                (txt, DAE.MATRIX(ty = _))  => begin
                  txt
                end

                (txt, DAE.TUPLE(PR = _))  => begin
                  txt
                end

                (txt, DAE.CAST(ty = _))  => begin
                  txt
                end

                (txt, DAE.SIZE(exp = _))  => begin
                  txt
                end

                (txt, DAE.REDUCTION(reductionInfo = _))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("y"))
                  txt
                end
              end
            end
        out_txt
      end

      function lm_39(in_txt::Tpl.Text, in_items::List{<:DAE.Exp}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Exp}
                local a_stringDelimiter::String
                local i_exp::DAE.Exp
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_exp <| rest, a_stringDelimiter)  => begin
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.nextIter(txt)
                    txt = lm_39(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpExpList(txt::Tpl.Text, a_expl::List{<:DAE.Exp}, a_stringDelimiter::String, a_expDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(a_expDelimiter)), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
            out_txt = lm_39(out_txt, a_expl, a_stringDelimiter)
            out_txt = Tpl.popIter(out_txt)
        out_txt
      end

      function lm_41(in_txt::Tpl.Text, in_items::List{<:DAE.Exp}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Exp}
                local a_stringDelimiter::String
                local i_exp::DAE.Exp
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_exp <| rest, a_stringDelimiter)  => begin
                    txt = dumpExpCrefs(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.nextIter(txt)
                    txt = lm_41(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpExpListCrefs(txt::Tpl.Text, a_expl::List{<:DAE.Exp}, a_stringDelimiter::String, a_expDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(a_expDelimiter)), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
            out_txt = lm_41(out_txt, a_expl, a_stringDelimiter)
            out_txt = Tpl.popIter(out_txt)
        out_txt
      end

      function dumpClockKind(in_txt::Tpl.Text, in_a_clk::DAE.ClockKind, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_solverMethod::DAE.Exp
                local i_c::DAE.Exp
                local i_startInterval::DAE.Exp
                local i_condition::DAE.Exp
                local i_interval::DAE.Exp
                local i_resolution::DAE.Exp
                local i_intervalCounter::DAE.Exp
                local l_sm__str::Tpl.Text
                local l_clk__str::Tpl.Text
                local l_si__str::Tpl.Text
                local l_condition__str::Tpl.Text
                local l_interval__str::Tpl.Text
                local l_re__str::Tpl.Text
                local l_ic__str::Tpl.Text
              @match (in_txt, in_a_clk, in_a_stringDelimiter) begin
                (txt, DAE.INFERRED_CLOCK(__), _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock()"))
                  txt
                end

                (txt, DAE.INTEGER_CLOCK(intervalCounter = i_intervalCounter, resolution = i_resolution), a_stringDelimiter)  => begin
                    l_ic__str = dumpExp(Tpl.emptyTxt, i_intervalCounter, a_stringDelimiter)
                    l_re__str = dumpExp(Tpl.emptyTxt, i_resolution, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock("))
                    txt = Tpl.writeText(txt, l_ic__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = Tpl.writeText(txt, l_re__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.REAL_CLOCK(interval = i_interval), a_stringDelimiter)  => begin
                    l_interval__str = dumpExp(Tpl.emptyTxt, i_interval, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock("))
                    txt = Tpl.writeText(txt, l_interval__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.BOOLEAN_CLOCK(condition = i_condition, startInterval = i_startInterval), a_stringDelimiter)  => begin
                    l_condition__str = dumpExp(Tpl.emptyTxt, i_condition, a_stringDelimiter)
                    l_si__str = dumpExp(Tpl.emptyTxt, i_startInterval, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock("))
                    txt = Tpl.writeText(txt, l_condition__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = Tpl.writeText(txt, l_si__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.SOLVER_CLOCK(c = i_c, solverMethod = i_solverMethod), a_stringDelimiter)  => begin
                    l_clk__str = dumpExp(Tpl.emptyTxt, i_c, a_stringDelimiter)
                    l_sm__str = dumpExp(Tpl.emptyTxt, i_solverMethod, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock("))
                    txt = Tpl.writeText(txt, l_clk__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = Tpl.writeText(txt, l_sm__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function fun_44(in_txt::Tpl.Text, in_mArg::Bool, in_a_cref__str::Tpl.Text, in_a_sub__str::Tpl.Text, in_a_ident::DAE.Ident) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_cref__str::Tpl.Text
                local a_sub__str::Tpl.Text
                local a_ident::DAE.Ident
              @match (in_txt, in_mArg, in_a_cref__str, in_a_sub__str, in_a_ident) begin
                (txt, false, a_cref__str, a_sub__str, a_ident)  => begin
                    txt = Tpl.writeStr(txt, a_ident)
                    txt = Tpl.writeText(txt, a_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("."))
                    txt = Tpl.writeText(txt, a_cref__str)
                  txt
                end

                (txt, _, a_cref__str, a_sub__str, a_ident)  => begin
                    txt = Tpl.writeStr(txt, a_ident)
                    txt = Tpl.writeText(txt, a_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("__"))
                    txt = Tpl.writeText(txt, a_cref__str)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpCref(in_txt::Tpl.Text, in_a_cref::DAE.ComponentRef) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_instant::String
                local i_componentRef::DAE.ComponentRef
                local i_index::ModelicaInteger
                local i_ident::DAE.Ident
                local i_subscriptLst::List{DAE.Subscript}
                local ret_2::Bool
                local l_cref__str::Tpl.Text
                local l_sub__str::Tpl.Text
              @match (in_txt, in_a_cref) begin
                (txt, DAE.CREF_IDENT(subscriptLst = i_subscriptLst, ident = i_ident))  => begin
                    l_sub__str = dumpSubscripts(Tpl.emptyTxt, i_subscriptLst)
                    txt = Tpl.writeStr(txt, i_ident)
                    txt = Tpl.writeText(txt, l_sub__str)
                  txt
                end

                (txt, DAE.CREF_ITER(subscriptLst = i_subscriptLst, ident = i_ident, index = i_index))  => begin
                    l_sub__str = dumpSubscripts(Tpl.emptyTxt, i_subscriptLst)
                    txt = Tpl.writeStr(txt, i_ident)
                    txt = Tpl.writeText(txt, l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" /* iter index "))
                    txt = Tpl.writeStr(txt, intString(i_index))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */"))
                  txt
                end

                (txt, DAE.CREF_QUAL(subscriptLst = i_subscriptLst, componentRef = i_componentRef, ident = i_ident))  => begin
                    l_sub__str = dumpSubscripts(Tpl.emptyTxt, i_subscriptLst)
                    l_cref__str = dumpCref(Tpl.emptyTxt, i_componentRef)
                    ret_2 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                    txt = fun_44(txt, ret_2, l_cref__str, l_sub__str, i_ident)
                  txt
                end

                (txt, DAE.WILD(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("_"))
                  txt
                end

                (txt, DAE.OPTIMICA_ATTR_INST_CREF(componentRef = i_componentRef, instant = i_instant))  => begin
                    txt = dumpCref(txt, i_componentRef)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeStr(txt, i_instant)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpCref: unknown cref")
                  txt
                end
              end
            end
        out_txt
      end

      function lm_46(in_txt::Tpl.Text, in_items::List{<:DAE.Subscript}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Subscript}
                local i_sub::DAE.Subscript
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_sub <| rest)  => begin
                    txt = dumpSubscript(txt, i_sub)
                    txt = Tpl.nextIter(txt)
                    txt = lm_46(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function lm_47(in_txt::Tpl.Text, in_items::List{<:DAE.Subscript}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Subscript}
                local i_sub::DAE.Subscript
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_sub <| rest)  => begin
                    txt = dumpSubscript(txt, i_sub)
                    txt = Tpl.nextIter(txt)
                    txt = lm_47(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_48(in_txt::Tpl.Text, in_mArg::Bool, in_a_subscripts::List{<:DAE.Subscript}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_subscripts::List{DAE.Subscript}
                local l_sub__str::Tpl.Text
              @match (in_txt, in_mArg, in_a_subscripts) begin
                (txt, false, a_subscripts)  => begin
                    l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(",")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_sub__str = lm_46(l_sub__str, a_subscripts)
                    l_sub__str = Tpl.popIter(l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeText(txt, l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, _, a_subscripts)  => begin
                    l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING("_")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_sub__str = lm_47(l_sub__str, a_subscripts)
                    l_sub__str = Tpl.popIter(l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("_"))
                    txt = Tpl.writeText(txt, l_sub__str)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpSubscripts(in_txt::Tpl.Text, in_a_subscripts::List{<:DAE.Subscript}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_subscripts::List{DAE.Subscript}
                local ret_0::Bool
              @match (in_txt, in_a_subscripts) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_subscripts)  => begin
                    ret_0 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                    txt = fun_48(txt, ret_0, i_subscripts)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpSubscript(in_txt::Tpl.Text, in_a_subscript::DAE.Subscript) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_exp::DAE.Exp
              @match (in_txt, in_a_subscript) begin
                (txt, DAE.WHOLEDIM(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                  txt
                end

                (txt, DAE.SLICE(exp = i_exp))  => begin
                    txt = dumpExp(txt, i_exp, "\\")
                  txt
                end

                (txt, DAE.INDEX(exp = i_exp))  => begin
                    txt = dumpExp(txt, i_exp, "\\")
                  txt
                end

                (txt, DAE.WHOLE_NONEXP(exp = i_exp))  => begin
                    txt = dumpExp(txt, i_exp, "\\")
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function dumpReductionIterator(in_txt::Tpl.Text, in_a_iterator::DAE.ReductionIterator, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_gexp::DAE.Exp
                local i_id::String
                local i_exp::DAE.Exp
                local l_guard__str::Tpl.Text
                local l_exp__str::Tpl.Text
              @match (in_txt, in_a_iterator, in_a_stringDelimiter) begin
                (txt, DAE.REDUCTIONITER(guardExp = NONE(), exp = i_exp, id = i_id), a_stringDelimiter)  => begin
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeStr(txt, i_id)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" in "))
                    txt = Tpl.writeText(txt, l_exp__str)
                  txt
                end

                (txt, DAE.REDUCTIONITER(guardExp = SOME(i_gexp), exp = i_exp, id = i_id), a_stringDelimiter)  => begin
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_guard__str = dumpExp(Tpl.emptyTxt, i_gexp, a_stringDelimiter)
                    txt = Tpl.writeStr(txt, i_id)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" guard "))
                    txt = Tpl.writeText(txt, l_guard__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" in "))
                    txt = Tpl.writeText(txt, l_exp__str)
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function fun_52(in_txt::Tpl.Text, in_mArg::Bool, in_a_op__str::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_op__str::Tpl.Text
              @match (in_txt, in_mArg, in_a_op__str) begin
                (txt, false, a_op__str)  => begin
                    txt = Tpl.writeText(txt, a_op__str)
                  txt
                end

                (txt, _, a_op__str)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, a_op__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function dumpOperand(txt::Tpl.Text, a_operand::DAE.Exp, a_operation::DAE.Exp, a_lhs::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            local ret_1::Bool
            local l_op__str::Tpl.Text

            l_op__str = dumpExp(Tpl.emptyTxt, a_operand, "\\")
            ret_1 = ExpressionPriority.shouldParenthesize(a_operand, a_operation, a_lhs)
            out_txt = fun_52(txt, ret_1, l_op__str)
        out_txt
      end

      function fun_54(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.ADD(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"))
                  txt
                end

                (txt, DAE.SUB(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"))
                  txt
                end

                (txt, DAE.MUL(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"))
                  txt
                end

                (txt, DAE.DIV(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/"))
                  txt
                end

                (txt, DAE.POW(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("^"))
                  txt
                end

                (txt, DAE.ADD_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"))
                  txt
                end

                (txt, DAE.SUB_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"))
                  txt
                end

                (txt, DAE.MUL_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".*"))
                  txt
                end

                (txt, DAE.DIV_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("./"))
                  txt
                end

                (txt, DAE.POW_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("^"))
                  txt
                end

                (txt, DAE.POW_ARR2(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^"))
                  txt
                end

                (txt, DAE.MUL_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"))
                  txt
                end

                (txt, DAE.ADD_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".+"))
                  txt
                end

                (txt, DAE.SUB_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".-"))
                  txt
                end

                (txt, DAE.POW_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^"))
                  txt
                end

                (txt, DAE.POW_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^"))
                  txt
                end

                (txt, DAE.MUL_SCALAR_PRODUCT(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"))
                  txt
                end

                (txt, DAE.MUL_MATRIX_PRODUCT(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"))
                  txt
                end

                (txt, DAE.DIV_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("./"))
                  txt
                end

                (txt, DAE.DIV_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpBinOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function fun_55(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.ADD(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"))
                  txt
                end

                (txt, DAE.SUB(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"))
                  txt
                end

                (txt, DAE.MUL(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*"))
                  txt
                end

                (txt, DAE.DIV(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/"))
                  txt
                end

                (txt, DAE.POW(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("^"))
                  txt
                end

                (txt, DAE.ADD_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("+ /* ADD_ARR */"))
                  txt
                end

                (txt, DAE.SUB_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("- /* SUB_ARR */"))
                  txt
                end

                (txt, DAE.MUL_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".* /* MUL_ARR */"))
                  txt
                end

                (txt, DAE.DIV_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("./ /* DIV_ARR */"))
                  txt
                end

                (txt, DAE.POW_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("^ /* POW_ARR */"))
                  txt
                end

                (txt, DAE.POW_ARR2(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^ /* POW_ARR2 */"))
                  txt
                end

                (txt, DAE.MUL_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("* /* MUL_ARR_SCA */"))
                  txt
                end

                (txt, DAE.ADD_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".+ /* ADD_ARR_SCA */"))
                  txt
                end

                (txt, DAE.SUB_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".- /* SUB_SCA_ARR */"))
                  txt
                end

                (txt, DAE.POW_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^ /* POW_SCA_ARR */"))
                  txt
                end

                (txt, DAE.POW_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(".^ /* POW_ARR_SCA */"))
                  txt
                end

                (txt, DAE.MUL_SCALAR_PRODUCT(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("* /* MUL_SCA_PRO */"))
                  txt
                end

                (txt, DAE.MUL_MATRIX_PRODUCT(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("* /* MUL_MAT_PRO */"))
                  txt
                end

                (txt, DAE.DIV_SCALAR_ARRAY(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/ /* DIV_SCA_ARR */"))
                  txt
                end

                (txt, DAE.DIV_ARRAY_SCALAR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/ /* DIV_ARR_SCA */"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpBinOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function fun_56(in_txt::Tpl.Text, in_mArg::Bool, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_op::DAE.Operator
              @match (in_txt, in_mArg, in_a_op) begin
                (txt, false, a_op)  => begin
                    txt = fun_54(txt, a_op)
                  txt
                end

                (txt, _, a_op)  => begin
                    txt = fun_55(txt, a_op)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpBinOp(txt::Tpl.Text, a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            local ret_0::Bool

            ret_0 = Config.typeinfo()
            out_txt = fun_56(txt, ret_0, a_op)
        out_txt
      end

      function dumpUnaryOp(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.UMINUS(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"))
                  txt
                end

                (txt, DAE.UMINUS_ARR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("-"))
                  txt
                end

                (txt, DAE.ADD(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("+"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpUnaryOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function dumpLogicalBinOp(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.AND(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("and"))
                  txt
                end

                (txt, DAE.OR(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("or"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpLogicalBinOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function dumpLogicalUnaryOp(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.NOT(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("not"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpLogicalUnaryOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function dumpRelationOp(in_txt::Tpl.Text, in_a_op::DAE.Operator) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_op) begin
                (txt, DAE.LESS(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<"))
                  txt
                end

                (txt, DAE.LESSEQ(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<="))
                  txt
                end

                (txt, DAE.GREATER(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.GREATEREQ(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">="))
                  txt
                end

                (txt, DAE.EQUAL(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("=="))
                  txt
                end

                (txt, DAE.NEQUAL(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<>"))
                  txt
                end

                (txt, DAE.USERDEFINED(fqName = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("USERDEFINED"))
                  txt
                end

                (txt, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpRelationOp: Unknown operator.")
                  txt
                end
              end
            end
        out_txt
      end

      function lm_62(in_txt::Tpl.Text, in_items::List{<:DAE.FuncArg}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.FuncArg}
                local i_arg::DAE.FuncArg
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_arg <| rest)  => begin
                    txt = dumpFuncArg(txt, i_arg)
                    txt = Tpl.nextIter(txt)
                    txt = lm_62(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function lm_63(in_txt::Tpl.Text, in_items::List{<:DAE.Type}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Type}
                local i_ty::DAE.Type
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_ty <| rest)  => begin
                    txt = dumpType(txt, i_ty)
                    txt = Tpl.nextIter(txt)
                    txt = lm_63(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function lm_64(in_txt::Tpl.Text, in_items::List{<:DAE.Type}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Type}
                local i_ty::DAE.Type
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_ty <| rest)  => begin
                    txt = dumpType(txt, i_ty)
                    txt = Tpl.nextIter(txt)
                    txt = lm_64(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpType(in_txt::Tpl.Text, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_name::String
                local i_types::List{DAE.Type}
                local i_functionType::DAE.Type
                local i_funcResultType::DAE.Type
                local i_funcArg::List{DAE.FuncArg}
                local i_complexClassType::ClassInf.SMNode
                local i_ty::DAE.Type
                local i_dims::DAE.Dimensions
                local i_path::Absyn.Path
                local l_ret__str::Tpl.Text
                local l_arg__str::Tpl.Text
                local l_ty__str::Tpl.Text
                local l_dim__str::Tpl.Text
              @match (in_txt, in_a_ty) begin
                (txt, DAE.T_INTEGER(varLst = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Integer"))
                  txt
                end

                (txt, DAE.T_REAL(varLst = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Real"))
                  txt
                end

                (txt, DAE.T_BOOL(varLst = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Bool"))
                  txt
                end

                (txt, DAE.T_STRING(varLst = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("String"))
                  txt
                end

                (txt, DAE.T_ENUMERATION(path = i_path))  => begin
                    txt = AbsynDumpTpl.dumpPath(txt, i_path)
                  txt
                end

                (txt, DAE.T_ARRAY(dims = i_dims, ty = i_ty))  => begin
                    l_dim__str = dumpDimensions(Tpl.emptyTxt, i_dims)
                    l_ty__str = dumpType(Tpl.emptyTxt, i_ty)
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeText(txt, l_dim__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, DAE.T_COMPLEX(complexClassType = i_complexClassType))  => begin
                    txt = dumpClassState(txt, i_complexClassType)
                  txt
                end

                (txt, DAE.T_SUBTYPE_BASIC(complexClassType = i_complexClassType))  => begin
                    txt = dumpClassState(txt, i_complexClassType)
                  txt
                end

                (txt, DAE.T_FUNCTION(funcArg = i_funcArg, funcResultType = i_funcResultType))  => begin
                    l_arg__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_arg__str = lm_62(l_arg__str, i_funcArg)
                    l_arg__str = Tpl.popIter(l_arg__str)
                    l_ret__str = dumpType(Tpl.emptyTxt, i_funcResultType)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<function>("))
                    txt = Tpl.writeText(txt, l_arg__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(") => "))
                    txt = Tpl.writeText(txt, l_ret__str)
                  txt
                end

                (txt, DAE.T_FUNCTION_REFERENCE_VAR(functionType = i_functionType))  => begin
                    txt = dumpType(txt, i_functionType)
                  txt
                end

                (txt, DAE.T_FUNCTION_REFERENCE_FUNC(functionType = i_functionType))  => begin
                    txt = dumpType(txt, i_functionType)
                  txt
                end

                (txt, DAE.T_TUPLE(types = i_types))  => begin
                    l_ty__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_ty__str = lm_63(l_ty__str, i_types)
                    l_ty__str = Tpl.popIter(l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_ty__str)
                  txt
                end

                (txt, DAE.T_CODE(ty = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_CODE#"))
                  txt
                end

                (txt, DAE.T_METALIST(ty = i_ty))  => begin
                    l_ty__str = dumpType(Tpl.emptyTxt, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("list<"))
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.T_METATUPLE(types = i_types))  => begin
                    l_ty__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_ty__str = lm_64(l_ty__str, i_types)
                    l_ty__str = Tpl.popIter(l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("tuple<"))
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.T_METAOPTION(ty = i_ty))  => begin
                    l_ty__str = dumpType(Tpl.emptyTxt, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Option<"))
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.T_METAUNIONTYPE(path = i_path))  => begin
                    txt = AbsynDumpTpl.dumpPath(txt, i_path)
                  txt
                end

                (txt, DAE.T_METARECORD(path = i_path))  => begin
                    txt = AbsynDumpTpl.dumpPath(txt, i_path)
                  txt
                end

                (txt, DAE.T_METAARRAY(ty = i_ty))  => begin
                    l_ty__str = dumpType(Tpl.emptyTxt, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("array<"))
                    txt = Tpl.writeText(txt, l_ty__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.T_METABOXED(ty = i_ty))  => begin
                    txt = dumpType(txt, i_ty)
                  txt
                end

                (txt, DAE.T_METAPOLYMORPHIC(name = i_name))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("polymorphic<"))
                    txt = Tpl.writeStr(txt, i_name)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                  txt
                end

                (txt, DAE.T_METATYPE(ty = i_ty))  => begin
                    txt = dumpType(txt, i_ty)
                  txt
                end

                (txt, DAE.T_UNKNOWN(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_UNKNOWN#"))
                  txt
                end

                (txt, DAE.T_ANYTYPE(anyClassType = _))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Any"))
                  txt
                end

                (txt, DAE.T_NORETCALL(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_NORETCALL#"))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function dumpFuncArg(in_txt::Tpl.Text, in_a_arg::DAE.FuncArg) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_arg_name::String
              @match (in_txt, in_a_arg) begin
                (txt, DAE.FUNCARG(name = i_arg_name))  => begin
                    txt = Tpl.writeStr(txt, i_arg_name)
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_67(in_txt::Tpl.Text, in_items::DAE.Dimensions) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::DAE.Dimensions
                local i_dim::DAE.Dimension
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_dim <| rest)  => begin
                    txt = dumpDimension(txt, i_dim)
                    txt = Tpl.nextIter(txt)
                    txt = lm_67(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpDimensions(txt::Tpl.Text, a_dims::DAE.Dimensions) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
            out_txt = lm_67(out_txt, a_dims)
            out_txt = Tpl.popIter(out_txt)
        out_txt
      end

      function dumpDimension(in_txt::Tpl.Text, in_a_dim::DAE.Dimension) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_exp::DAE.Exp
                local i_enumTypeName::Absyn.Path
                local i_integer::ModelicaInteger
              @match (in_txt, in_a_dim) begin
                (txt, DAE.DIM_INTEGER(integer = i_integer))  => begin
                    txt = Tpl.writeStr(txt, intString(i_integer))
                  txt
                end

                (txt, DAE.DIM_ENUM(enumTypeName = i_enumTypeName))  => begin
                    txt = AbsynDumpTpl.dumpPath(txt, i_enumTypeName)
                  txt
                end

                (txt, DAE.DIM_EXP(exp = i_exp))  => begin
                    txt = dumpExp(txt, i_exp, "\\")
                  txt
                end

                (txt, DAE.DIM_UNKNOWN(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function dumpClassState(txt::Tpl.Text, a_state::ClassInf.SMNode) ::Tpl.Text
            local out_txt::Tpl.Text

            local ret_0::Absyn.Path

            ret_0 = ClassInf.getStateName(a_state)
            out_txt = AbsynDumpTpl.dumpPath(txt, ret_0)
        out_txt
      end

      function dumpMatchType(in_txt::Tpl.Text, in_a_ty::DAE.MatchType) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_ty) begin
                (txt, DAE.MATCHCONTINUE(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("matchcontinue"))
                  txt
                end

                (txt, DAE.MATCH(switch = NONE()))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("match"))
                  txt
                end

                (txt, DAE.MATCH(switch = SOME(_)))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("match /* switch */"))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function dumpMatchCase(in_txt::Tpl.Text, in_a_mcase::DAE.MatchCase) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_body::List{DAE.Statement}
                local i_result::DAE.Exp
                local i_patterns::List{DAE.Pattern}
                local l_body__str::Tpl.Text
                local l_res__str::Tpl.Text
                local l_pat__str::Tpl.Text
              @match (in_txt, in_a_mcase) begin
                (txt, DAE.CASE(body =  nil(), result = SOME(i_result), patterns = i_patterns))  => begin
                    l_pat__str = dumpPatterns(Tpl.emptyTxt, i_patterns)
                    l_res__str = dumpExp(Tpl.emptyTxt, i_result, "\\")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("case ("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(") then "))
                    txt = Tpl.writeText(txt, l_res__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                  txt
                end

                (txt, DAE.CASE(body =  nil(), result = NONE(), patterns = i_patterns))  => begin
                    l_pat__str = dumpPatterns(Tpl.emptyTxt, i_patterns)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("case ("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(") then fail();"))
                  txt
                end

                (txt, DAE.CASE(result = SOME(i_result), patterns = i_patterns, body = i_body))  => begin
                    l_pat__str = dumpPatterns(Tpl.emptyTxt, i_patterns)
                    l_res__str = dumpExp(Tpl.emptyTxt, i_result, "\\")
                    l_body__str = "NO STATEMENTS!" # DAEDumpTpl.dumpStatements(Tpl.emptyTxt, i_body)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("case ("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST(list(")\\n", "  algorithm\\n"), true))
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(4))
                    txt = Tpl.writeText(txt, l_body__str)
                    txt = Tpl.softNewLine(txt)
                    txt = Tpl.popBlock(txt)
                    txt = Tpl.writeTok(txt, Tpl.ST_LINE("  then\\n"))
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(4))
                    txt = Tpl.writeText(txt, l_res__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt = Tpl.popBlock(txt)
                  txt
                end

                (txt, DAE.CASE(patterns = i_patterns, body = i_body))  => begin
                    l_pat__str = dumpPatterns(Tpl.emptyTxt, i_patterns)
                    l_body__str = "NO STATEMENTS!" # DAEDumpTpl.dumpStatements(Tpl.emptyTxt, i_body)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("case ("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST(list(")\\n", "  algorithm\\n"), true))
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(4))
                    txt = Tpl.writeText(txt, l_body__str)
                    txt = Tpl.softNewLine(txt)
                    txt = Tpl.popBlock(txt)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST(list("  then\\n", "    fail();"), false))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_73(in_txt::Tpl.Text, in_items::List{<:DAE.Pattern}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Pattern}
                local i_pat::DAE.Pattern
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_pat <| rest)  => begin
                    txt = dumpPattern(txt, i_pat)
                    txt = Tpl.nextIter(txt)
                    txt = lm_73(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpPatterns(txt::Tpl.Text, a_patterns::List{<:DAE.Pattern}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
            out_txt = lm_73(out_txt, a_patterns)
            out_txt = Tpl.popIter(out_txt)
        out_txt
      end

      function lm_75(in_txt::Tpl.Text, in_items::List{<:Tuple{<:DAE.Pattern, String, DAE.Type}}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{Tuple{DAE.Pattern, String, DAE.Type}}
                local i_pat::Tuple{DAE.Pattern, String, DAE.Type}
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_pat <| rest)  => begin
                    txt = dumpNamedPattern(txt, i_pat)
                    txt = Tpl.nextIter(txt)
                    txt = lm_75(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpPattern(in_txt::Tpl.Text, in_a_pattern::DAE.Pattern) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_exp::DAE.Exp
                local i_tail::DAE.Pattern
                local i_head::DAE.Pattern
                local i_patterns_1::List{Tuple{DAE.Pattern, String, DAE.Type}}
                local i_name::Absyn.Path
                local i_patterns::List{DAE.Pattern}
                local i_pat::DAE.Pattern
                local i_id::String
                local l_pat__str::Tpl.Text
                local l_name__str::Tpl.Text
              @match (in_txt, in_a_pattern) begin
                (txt, DAE.PAT_WILD(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("_"))
                  txt
                end

                (txt, DAE.PAT_AS(pat = DAE.PAT_WILD(__), id = i_id))  => begin
                    txt = Tpl.writeStr(txt, i_id)
                  txt
                end

                (txt, DAE.PAT_AS_FUNC_PTR(pat = DAE.PAT_WILD(__), id = i_id))  => begin
                    txt = Tpl.writeStr(txt, i_id)
                  txt
                end

                (txt, DAE.PAT_SOME(pat = i_pat))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("SOME("))
                    txt = dumpPattern(txt, i_pat)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PAT_META_TUPLE(patterns = i_patterns))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = dumpPatterns(txt, i_patterns)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PAT_CALL_TUPLE(patterns = i_patterns))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = dumpPatterns(txt, i_patterns)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PAT_CALL(name = i_name, patterns = i_patterns))  => begin
                    l_name__str = AbsynDumpTpl.dumpPath(Tpl.emptyTxt, i_name)
                    l_pat__str = dumpPatterns(Tpl.emptyTxt, i_patterns)
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PAT_CALL_NAMED(name = i_name, patterns = i_patterns_1))  => begin
                    l_name__str = AbsynDumpTpl.dumpPath(Tpl.emptyTxt, i_name)
                    l_pat__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_pat__str = lm_75(l_pat__str, i_patterns_1)
                    l_pat__str = Tpl.popIter(l_pat__str)
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_pat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.PAT_CONS(head = i_head, tail = i_tail))  => begin
                    txt = dumpPattern(txt, i_head)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("::"))
                    txt = dumpPattern(txt, i_tail)
                  txt
                end

                (txt, DAE.PAT_CONSTANT(exp = i_exp))  => begin
                    txt = dumpExp(txt, i_exp, "\\")
                  txt
                end

                (txt, DAE.PAT_AS(id = i_id, pat = i_pat))  => begin
                    txt = Tpl.writeStr(txt, i_id)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" as "))
                    txt = dumpPattern(txt, i_pat)
                  txt
                end

                (txt, DAE.PAT_AS_FUNC_PTR(id = i_id, pat = i_pat))  => begin
                    txt = Tpl.writeStr(txt, i_id)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" as "))
                    txt = dumpPattern(txt, i_pat)
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("*PATTERN*"))
                  txt
                end
              end
            end
        out_txt
      end

      function dumpNamedPattern(in_txt::Tpl.Text, in_a_pattern::Tuple{<:DAE.Pattern, String, DAE.Type}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_pat::DAE.Pattern
                local i_id::String
              @match (in_txt, in_a_pattern) begin
                (txt, (i_pat, i_id, _))  => begin
                    txt = Tpl.writeStr(txt, i_id)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" = "))
                    txt = dumpPattern(txt, i_pat)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_78(in_txt::Tpl.Text, in_a_scalar::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_scalar) begin
                (txt, false)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* non-scalar */ "))
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* scalar */ "))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_79(in_txt::Tpl.Text, in_mArg::Bool, in_a_scalar::Bool) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_scalar::Bool
              @match (in_txt, in_mArg, in_a_scalar) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_scalar)  => begin
                    txt = fun_78(txt, a_scalar)
                  txt
                end
              end
            end
        out_txt
      end

      function lm_80(in_txt::Tpl.Text, in_items::List{<:List{<:DAE.Exp}}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{List{DAE.Exp}}
                local a_stringDelimiter::String
                local i_row::List{DAE.Exp}
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_row <| rest, a_stringDelimiter)  => begin
                    txt = dumpExpList(txt, i_row, a_stringDelimiter, ", ")
                    txt = Tpl.nextIter(txt)
                    txt = lm_80(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_81(in_txt::Tpl.Text, in_mArg::Bool, in_a_ty::DAE.Type) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_ty::DAE.Type
                local ret_0::String
              @match (in_txt, in_mArg, in_a_ty) begin
                (txt, false, _)  => begin
                  txt
                end

                (txt, _, a_ty)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* matrix "))
                    ret_0 = local_unparseType(a_ty)
                    txt = Tpl.writeStr(txt, ret_0)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_82(in_txt::Tpl.Text, in_a_step::Option{<:DAE.Exp}, in_a_e::DAE.Exp) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_e::DAE.Exp
                local i_step::DAE.Exp
              @match (in_txt, in_a_step, in_a_e) begin
                (txt, SOME(i_step), a_e)  => begin
                    txt = dumpOperand(txt, i_step, a_e, false)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function fun_83(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_84(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_85(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_86(in_txt::Tpl.Text, in_a_needs__paren::Tpl.Text) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_needs__paren) begin
                (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                  txt
                end

                (txt, _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end
              end
            end
        out_txt
      end

      function fun_87(in_txt::Tpl.Text, in_a_sz::Option{<:DAE.Exp}, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_dim::DAE.Exp
              @match (in_txt, in_a_sz, in_a_stringDelimiter) begin
                (txt, SOME(i_dim), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = dumpExp(txt, i_dim, a_stringDelimiter)
                  txt
                end

                (txt, _, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_88(in_txt::Tpl.Text, in_items::DAE.ReductionIterators, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::DAE.ReductionIterators
                local a_stringDelimiter::String
                local i_it::DAE.ReductionIterator
              @match (in_txt, in_items, in_a_stringDelimiter) begin
                (txt,  nil(), _)  => begin
                  txt
                end

                (txt, i_it <| rest, a_stringDelimiter)  => begin
                    txt = dumpReductionIterator(txt, i_it, a_stringDelimiter)
                    txt = Tpl.nextIter(txt)
                    txt = lm_88(txt, rest, a_stringDelimiter)
                  txt
                end
              end
            end
        out_txt
      end

      function fun_89(in_txt::Tpl.Text, in_a_ri_iterType::Absyn.ReductionIterType) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
              @match (in_txt, in_a_ri_iterType) begin
                (txt, Absyn.THREAD(__))  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("threaded "))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_90(in_txt::Tpl.Text, in_items::List{<:DAE.MatchCase}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.MatchCase}
                local i_c::DAE.MatchCase
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_c <| rest)  => begin
                    txt = dumpMatchCase(txt, i_c)
                    txt = Tpl.nextIter(txt)
                    txt = lm_90(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpExpCrefs(in_txt::Tpl.Text, in_a_exp::DAE.Exp, in_a_stringDelimiter::String) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local a_stringDelimiter::String
                local i_pattern::DAE.Pattern
                local i_cases::List{DAE.MatchCase}
                local i_inputs::List{DAE.Exp}
                local i_matchType::DAE.MatchType
                local i_args::List{DAE.Exp}
                local i_listExp::List{DAE.Exp}
                local i_cdr::DAE.Exp
                local i_car::DAE.Exp
                local i_valList::List{DAE.Exp}
                local i_ri_iterType::Absyn.ReductionIterType
                local i_iterators::DAE.ReductionIterators
                local i_expr::DAE.Exp
                local i_tyStr::String
                local i_scope::String
                local i_name_1::DAE.ComponentRef
                local i_code::Absyn.CodeNode
                local i_sz::Option{DAE.Exp}
                local i_ix::ModelicaInteger
                local i_sub::List{DAE.Exp}
                local i_PR::List{DAE.Exp}
                local i_stop::DAE.Exp
                local i_step::Option{DAE.Exp}
                local i_start::DAE.Exp
                local i_ty::DAE.Type
                local i_matrix::List{List{DAE.Exp}}
                local i_scalar::Bool
                local i_array::List{DAE.Exp}
                local i_expList::List{DAE.Exp}
                local i_path::Absyn.Path
                local i_expLst::List{DAE.Exp}
                local i_expElse::DAE.Exp
                local i_expThen::DAE.Exp
                local i_expCond::DAE.Exp
                local i_operator::DAE.Operator
                local i_e::DAE.Exp
                local i_exp::DAE.Exp
                local i_exp2::DAE.Exp
                local i_exp1::DAE.Exp
                local i_componentRef::DAE.ComponentRef
                local i_name::Absyn.Path
                local l_case__str::Tpl.Text
                local l_inputs__str::Tpl.Text
                local l_match__ty::Tpl.Text
                local l_args__str::Tpl.Text
                local l_cdr__str::Tpl.Text
                local l_car__str::Tpl.Text
                local l_expl__str::Tpl.Text
                local l_iter__str::Tpl.Text
                local l_name__str::Tpl.Text
                local ret_23::String
                local l_code__str::Tpl.Text
                local l_dim__str::Tpl.Text
                local l_sub__str::Tpl.Text
                local l_rparen::Tpl.Text
                local l_lparen::Tpl.Text
                local l_needs__paren::Tpl.Text
                local l_tuple__str::Tpl.Text
                local l_stop__str::Tpl.Text
                local l_step__str::Tpl.Text
                local l_start__str::Tpl.Text
                local ret_12::Bool
                local l_mat__str::Tpl.Text
                local ret_10::Bool
                local l_expl::Tpl.Text
                local l_func__str::Tpl.Text
                local l_argl::Tpl.Text
                local l_else__str::Tpl.Text
                local l_then__str::Tpl.Text
                local l_cond__str::Tpl.Text
                local l_op__str::Tpl.Text
                local l_exp__str::Tpl.Text
                local l_rhs__str::Tpl.Text
                local l_lhs__str::Tpl.Text
              @match (in_txt, in_a_exp, in_a_stringDelimiter) begin
                (txt, DAE.ICONST(integer = _), _)  => begin
                  txt
                end

                (txt, DAE.RCONST(real = _), _)  => begin
                  txt
                end

                (txt, DAE.SCONST(string = _), _)  => begin
                  txt
                end

                (txt, DAE.BCONST(bool = _), _)  => begin
                  txt
                end

                (txt, DAE.ENUM_LITERAL(name = i_name), _)  => begin
                    txt = AbsynDumpTpl.dumpPath(txt, i_name)
                  txt
                end

                (txt, DAE.CREF(componentRef = i_componentRef), _)  => begin
                    txt = dumpCref(txt, i_componentRef)
                  txt
                end

                (txt, DAE.BINARY(exp1 = i_exp1, exp2 = i_exp2), a_stringDelimiter)  => begin
                    l_lhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp1, a_stringDelimiter)
                    l_rhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp2, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, i_e && DAE.UNARY(exp = i_exp, operator = i_operator), _)  => begin
                    l_exp__str = dumpOperand(Tpl.emptyTxt, i_exp, i_e, false)
                    l_op__str = dumpUnaryOp(Tpl.emptyTxt, i_operator)
                    txt = Tpl.writeText(txt, l_op__str)
                    txt = Tpl.writeText(txt, l_exp__str)
                  txt
                end

                (txt, DAE.LBINARY(exp1 = i_exp1, exp2 = i_exp2), a_stringDelimiter)  => begin
                    l_lhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp1, a_stringDelimiter)
                    l_rhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp2, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, DAE.LUNARY(exp = i_exp), a_stringDelimiter)  => begin
                    l_lhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lhs__str)
                  txt
                end

                (txt, DAE.RELATION(exp1 = i_exp1, exp2 = i_exp2), a_stringDelimiter)  => begin
                    l_lhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp1, a_stringDelimiter)
                    l_rhs__str = dumpExpCrefs(Tpl.emptyTxt, i_exp2, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lhs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_rhs__str)
                  txt
                end

                (txt, DAE.IFEXP(expCond = i_expCond, expThen = i_expThen, expElse = i_expElse), a_stringDelimiter)  => begin
                    l_cond__str = dumpExpCrefs(Tpl.emptyTxt, i_expCond, a_stringDelimiter)
                    l_then__str = dumpExpCrefs(Tpl.emptyTxt, i_expThen, a_stringDelimiter)
                    l_else__str = dumpExpCrefs(Tpl.emptyTxt, i_expElse, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_cond__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_then__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                    txt = Tpl.writeText(txt, l_else__str)
                  txt
                end

                (txt, DAE.CALL(attr = DAE.CALL_ATTR(builtin = true), expLst = i_expLst), a_stringDelimiter)  => begin
                    l_argl = dumpExpListCrefs(Tpl.emptyTxt, i_expLst, a_stringDelimiter, " ")
                    txt = Tpl.writeText(txt, l_argl)
                  txt
                end

                (txt, DAE.CALL(expLst = i_expLst), a_stringDelimiter)  => begin
                    l_argl = dumpExpListCrefs(Tpl.emptyTxt, i_expLst, a_stringDelimiter, " ")
                    txt = Tpl.writeText(txt, l_argl)
                  txt
                end

                (txt, DAE.PARTEVALFUNCTION(path = i_path, expList = i_expList), a_stringDelimiter)  => begin
                    l_func__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_path)
                    l_argl = dumpExpList(Tpl.emptyTxt, i_expList, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("function "))
                    txt = Tpl.writeText(txt, l_func__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_argl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.ARRAY(array = i_array, scalar = i_scalar), a_stringDelimiter)  => begin
                    l_expl = dumpExpList(Tpl.emptyTxt, i_array, a_stringDelimiter, ", ")
                    ret_10 = Config.typeinfo()
                    txt = fun_79(txt, ret_10, i_scalar)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("{"))
                    txt = Tpl.writeText(txt, l_expl)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("}"))
                  txt
                end

                (txt, DAE.MATRIX(matrix = i_matrix, ty = i_ty), a_stringDelimiter)  => begin
                    l_mat__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING("}, {")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_mat__str = lm_80(l_mat__str, i_matrix, a_stringDelimiter)
                    l_mat__str = Tpl.popIter(l_mat__str)
                    ret_12 = Config.typeinfo()
                    txt = fun_81(txt, ret_12, i_ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("{{"))
                    txt = Tpl.writeText(txt, l_mat__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("}}"))
                  txt
                end

                (txt, i_e && DAE.RANGE(start = i_start, step = i_step, stop = i_stop), _)  => begin
                    l_start__str = dumpOperand(Tpl.emptyTxt, i_start, i_e, false)
                    l_step__str = fun_82(Tpl.emptyTxt, i_step, i_e)
                    l_stop__str = dumpOperand(Tpl.emptyTxt, i_stop, i_e, false)
                    txt = Tpl.writeText(txt, l_start__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(":"))
                    txt = Tpl.writeText(txt, l_step__str)
                    txt = Tpl.writeText(txt, l_stop__str)
                  txt
                end

                (txt, DAE.TUPLE(PR =  nil()), _)  => begin
                  txt
                end

                (txt, DAE.TUPLE(PR = i_PR), a_stringDelimiter)  => begin
                    l_tuple__str = dumpExpList(Tpl.emptyTxt, i_PR, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_tuple__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CAST(exp = i_exp), a_stringDelimiter)  => begin
                    l_exp__str = dumpExpCrefs(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.ASUB(exp = i_exp, sub = i_sub), a_stringDelimiter)  => begin
                    l_needs__paren = parenthesizeSubExp(Tpl.emptyTxt, i_exp)
                    l_lparen = fun_83(Tpl.emptyTxt, l_needs__paren)
                    l_rparen = fun_84(Tpl.emptyTxt, l_needs__paren)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_sub__str = dumpExpList(Tpl.emptyTxt, i_sub, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_lparen)
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_rparen)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeText(txt, l_sub__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, DAE.TSUB(exp = i_exp, ix = i_ix), a_stringDelimiter)  => begin
                    l_needs__paren = parenthesizeSubExp(Tpl.emptyTxt, i_exp)
                    l_lparen = fun_85(Tpl.emptyTxt, l_needs__paren)
                    l_rparen = fun_86(Tpl.emptyTxt, l_needs__paren)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeText(txt, l_lparen)
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_rparen)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                    txt = Tpl.writeStr(txt, intString(i_ix))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                  txt
                end

                (txt, DAE.SIZE(exp = i_exp, sz = i_sz), a_stringDelimiter)  => begin
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_exp, a_stringDelimiter)
                    l_dim__str = fun_87(Tpl.emptyTxt, i_sz, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("size("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeText(txt, l_dim__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CODE(code = i_code), _)  => begin
                    ret_23 = Dump.printCodeStr(i_code)
                    l_code__str = Tpl.writeStr(Tpl.emptyTxt, ret_23)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Code("))
                    txt = Tpl.writeText(txt, l_code__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.EMPTY(name = i_name_1, scope = i_scope, tyStr = i_tyStr), _)  => begin
                    l_name__str = dumpCref(Tpl.emptyTxt, i_name_1)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("<EMPTY(scope: "))
                    txt = Tpl.writeStr(txt, i_scope)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", name: "))
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", ty: "))
                    txt = Tpl.writeStr(txt, i_tyStr)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")>"))
                  txt
                end

                (txt, DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = i_name, iterType = i_ri_iterType), expr = i_expr, iterators = i_iterators), a_stringDelimiter)  => begin
                    l_name__str = AbsynDumpTpl.dumpPathNoQual(Tpl.emptyTxt, i_name)
                    l_exp__str = dumpExp(Tpl.emptyTxt, i_expr, a_stringDelimiter)
                    l_iter__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_iter__str = lm_88(l_iter__str, i_iterators, a_stringDelimiter)
                    l_iter__str = Tpl.popIter(l_iter__str)
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_exp__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" for "))
                    txt = fun_89(txt, i_ri_iterType)
                    txt = Tpl.writeText(txt, l_iter__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.LIST(valList = i_valList), a_stringDelimiter)  => begin
                    l_expl__str = dumpExpList(Tpl.emptyTxt, i_valList, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("List("))
                    txt = Tpl.writeText(txt, l_expl__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.CONS(car = i_car, cdr = i_cdr), a_stringDelimiter)  => begin
                    l_car__str = dumpExp(Tpl.emptyTxt, i_car, a_stringDelimiter)
                    l_cdr__str = dumpExp(Tpl.emptyTxt, i_cdr, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("listCons("))
                    txt = Tpl.writeText(txt, l_car__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                    txt = Tpl.writeText(txt, l_cdr__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_TUPLE(listExp = i_listExp), a_stringDelimiter)  => begin
                    l_tuple__str = dumpExpList(Tpl.emptyTxt, i_listExp, a_stringDelimiter, ", ")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("Tuple("))
                    txt = Tpl.writeText(txt, l_tuple__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_OPTION(exp = SOME(i_exp)), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("SOME("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.META_OPTION(exp = _), _)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("NONE()"))
                  txt
                end

                (txt, DAE.METARECORDCALL(path = i_path, args = i_args), a_stringDelimiter)  => begin
                    l_name__str = AbsynDumpTpl.dumpPath(Tpl.emptyTxt, i_path)
                    l_args__str = dumpExpList(Tpl.emptyTxt, i_args, a_stringDelimiter, ", ")
                    txt = Tpl.writeText(txt, l_name__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                    txt = Tpl.writeText(txt, l_args__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.MATCHEXPRESSION(matchType = i_matchType, inputs = i_inputs, cases = i_cases), a_stringDelimiter)  => begin
                    l_match__ty = dumpMatchType(Tpl.emptyTxt, i_matchType)
                    l_inputs__str = dumpExpList(Tpl.emptyTxt, i_inputs, a_stringDelimiter, ", ")
                    l_case__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                    l_case__str = lm_90(l_case__str, i_cases)
                    l_case__str = Tpl.popIter(l_case__str)
                    txt = Tpl.writeText(txt, l_match__ty)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" ("))
                    txt = Tpl.writeText(txt, l_inputs__str)
                    txt = Tpl.writeTok(txt, Tpl.ST_LINE(")\\n"))
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(4))
                    txt = Tpl.writeText(txt, l_case__str)
                    txt = Tpl.softNewLine(txt)
                    txt = Tpl.popBlock(txt)
                    txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                    txt = Tpl.writeText(txt, l_match__ty)
                    txt = Tpl.popBlock(txt)
                  txt
                end

                (txt, DAE.BOX(exp = i_exp), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("#("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.UNBOX(exp = i_exp), a_stringDelimiter)  => begin
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING("unbox("))
                    txt = dumpExp(txt, i_exp, a_stringDelimiter)
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                  txt
                end

                (txt, DAE.SHARED_LITERAL(exp = i_exp), a_stringDelimiter)  => begin
                    txt = dumpExpCrefs(txt, i_exp, a_stringDelimiter)
                  txt
                end

                (txt, DAE.PATTERN(pattern = i_pattern), _)  => begin
                    txt = dumpPattern(txt, i_pattern)
                  txt
                end

                (txt, _, _)  => begin
                    txt = errorMsg(txt, "ExpressionDumpTpl.dumpExp: Unknown expression.")
                  txt
                end
              end
            end
        out_txt
      end

      function errorMsg(txt::Tpl.Text, a_errMessage::String) ::Tpl.Text
            local out_txt::Tpl.Text

            Tpl.addTemplateError(a_errMessage)
            out_txt = Tpl.writeStr(txt, a_errMessage)
        out_txt
      end

      function fun_93(in_txt::Tpl.Text, in_a_con::DAE.Constraint) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local i_c::DAE.Exp
              @match (in_txt, in_a_con) begin
                (txt, DAE.CONSTRAINT_DT(constraint = i_c, localCon = true))  => begin
                    txt = dumpExp(txt, i_c, "\\")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" (local)"))
                  txt
                end

                (txt, DAE.CONSTRAINT_DT(constraint = i_c, localCon = false))  => begin
                    txt = dumpExp(txt, i_c, "\\")
                    txt = Tpl.writeTok(txt, Tpl.ST_STRING(" (global)"))
                  txt
                end

                (txt, _)  => begin
                  txt
                end
              end
            end
        out_txt
      end

      function lm_94(in_txt::Tpl.Text, in_items::List{<:DAE.Constraint}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = begin
                local txt::Tpl.Text
                local rest::List{DAE.Constraint}
                local i_con::DAE.Constraint
              @match (in_txt, in_items) begin
                (txt,  nil())  => begin
                  txt
                end

                (txt, i_con <| rest)  => begin
                    txt = fun_93(txt, i_con)
                    txt = Tpl.nextIter(txt)
                    txt = lm_94(txt, rest)
                  txt
                end
              end
            end
        out_txt
      end

      function dumpConstraints(txt::Tpl.Text, a_cons::List{<:DAE.Constraint}) ::Tpl.Text
            local out_txt::Tpl.Text

            out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
            out_txt = lm_94(out_txt, a_cons)
            out_txt = Tpl.popIter(out_txt)
        out_txt
      end

  #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
  @exportAll()
end

#########################

function crefStr(inComponentRef::DAE.ComponentRef) ::String
      local outString::String

      outString = stringDelimitList(toStringList(inComponentRef), if Flags.getConfigBool(Flags.MODELICA_OUTPUT)
            "__"
          else
            "."
          end)
  outString
end

function toStringList(inCref::DAE.ComponentRef) ::List{String}
      local outStringList::List{String}

      outStringList = Dangerous.listReverseInPlace(toStringList_tail(inCref, nil))
  outStringList
end

 #= Tail-recursive implementation of toStringList. =#
function toStringList_tail(inCref::DAE.ComponentRef, inAccumStrings::List{<:String}) ::List{String}
      local outStringList::List{String}

      outStringList = begin
          local id::String
          local cref::DAE.ComponentRef
        @match (inCref, inAccumStrings) begin
          (DAE.CREF_QUAL(ident = id, componentRef = cref), _)  => begin
            toStringList_tail(cref, _cons(id, inAccumStrings))
          end

          (DAE.CREF_IDENT(ident = id), _)  => begin
            _cons(id, inAccumStrings)
          end

          _  => begin
              nil
          end
        end
      end
  outStringList
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

function crefPrefixOf(prefixCref::DAE.ComponentRef, fullCref::DAE.ComponentRef) ::Bool
      local outPrefixOf::Bool

      outPrefixOf = begin
        @match (prefixCref, fullCref) begin
          (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
            prefixCref.ident == fullCref.ident && subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst) && crefPrefixOf(prefixCref.componentRef, fullCref.componentRef)
          end

          (DAE.CREF_IDENT(subscriptLst =  nil()), DAE.CREF_QUAL(__))  => begin
            prefixCref.ident == fullCref.ident
          end

          (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
            prefixCref.ident == fullCref.ident && subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst)
          end

          (DAE.CREF_IDENT(subscriptLst =  nil()), DAE.CREF_IDENT(__))  => begin
            stringEq(prefixCref.ident, fullCref.ident)
          end

          (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
            prefixCref.ident == fullCref.ident && subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst)
          end

          _  => begin
              false
          end
        end
      end
       #=  both are qualified, dive into
       =#
       #=  adrpo: 2010-10-07: first is an ID, second is qualified, see if one is prefix of the other
       =#
       #=                     even if the first one DOESN'T HAVE SUBSCRIPTS!
       =#
       #=  first is an ID, second is qualified, see if one is prefix of the other
       =#
       #=  adrpo: 2010-10-07: first is an ID, second is an ID, see if one is prefix of the other
       =#
       #=                     even if the first one DOESN'T HAVE SUBSCRIPTS!
       =#
       #=  they are not a prefix of one-another
       =#
  outPrefixOf
end

#= This function prints a complete expression. =#
function printExpStr(e::DAE.Exp) ::String
     local s::String

     s = Tpl.tplString2(LocalExpressionDumpTpl.dumpExp, e, "\"")
 s
end

function printExp(e::DAE.Exp)
  local s::String
  Tpl.tplPrint2(LocalExpressionDumpTpl.dumpExp, e, "\"")
end

function printCrefsFromExpStr(e::DAE.Exp) ::String
      local s::String = "NO EXP"
      s = Tpl.tplString2(LocalExpressionDumpTpl.dumpExpCrefs, e, "")
  s
end


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

#= Same as printList, except it returns
 a string instead of printing. =#
function printListStr(inTypeALst::List{<:Type_a}, inFuncTypeTypeAToString::FuncTypeType_aToString, inString::String) ::String
     local outString::String

     outString = stringDelimitList(ListUtil.map(inTypeALst, inFuncTypeTypeAToString), inString)
 outString
end

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
              str = printListStr(l, printSubscriptStr, ",")
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
            CREF_LOCAL.hashComponentRef(cr)
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
              stringHashDjb2(printExpStr(e))
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

function hashComponentRefMod(cr::DAE.ComponentRef, mod::ModelicaInteger) ::ModelicaInteger
      local res::ModelicaInteger

      local h::ModelicaInteger

       #=  hash might overflow => force positive
       =#
      h = intAbs(hashComponentRef(cr))
      res = intMod(h, mod)
  res
end

function hashComponentRef(cr::DAE.ComponentRef) ::ModelicaInteger
      local hash::ModelicaInteger

      hash = begin
          local id::DAE.Ident
          local tp::DAE.Type
          local subs::List{DAE.Subscript}
          local cr1::DAE.ComponentRef
        @match cr begin
          DAE.CREF_IDENT(id, tp, subs)  => begin
            stringHashDjb2(id) + hashSubscripts(tp, subs)
          end

          DAE.CREF_QUAL(id, tp, subs, cr1)  => begin
            stringHashDjb2(id) + hashSubscripts(tp, subs) + hashComponentRef(cr1)
          end

          DAE.CREF_ITER(id, _, tp, subs)  => begin
            stringHashDjb2(id) + hashSubscripts(tp, subs)
          end

          _  => begin
              0
          end
        end
      end
       #= print(\"IDENT, \"+id+\" hashed to \"+intString(stringHashDjb2(id))+\", subs hashed to \"+intString(hashSubscripts(tp,subs))+\"\\n\");
       =#
       #= print(\"QUAL, \"+id+\" hashed to \"+intString(stringHashDjb2(id))+\", subs hashed to \"+intString(hashSubscripts(tp,subs))+\"\\n\");
       =#
  hash
end

 #= help function, hashing subscripts making sure [1,2] and [2,1] doesn't match to the same number =#
function hashSubscripts(tp::DAE.Type, subs::List{<:DAE.Subscript}) ::ModelicaInteger
      local hash::ModelicaInteger

      hash = begin
        @match (tp, subs) begin
          (_,  nil())  => begin
            0
          end

          _  => begin
              hashSubscripts2(ListUtil.fill(1, listLength(subs)), subs, 1)
          end
        end
      end
       #=  TODO: Currently, the types of component references are wrong, they consider the subscripts but they should not.
       =#
       #=  For example, given Real a[10,10];  the component reference 'a[1,2]' should have type Real[10,10] but it has type Real.
       =#
       #= /*DAEUtil.expTypeArrayDimensions(tp),*/ =#
  hash
end

 #= help function =#
function hashSubscripts2(dims::List{<:ModelicaInteger}, subs::List{<:DAE.Subscript}, factor::ModelicaInteger) ::ModelicaInteger
      local hash::ModelicaInteger

      hash = begin
          local i1::ModelicaInteger
          local s::DAE.Subscript
          local rest_dims::List{ModelicaInteger}
          local rest_subs::List{DAE.Subscript}
        @match (dims, subs, factor) begin
          ( nil(),  nil(), _)  => begin
            0
          end

          (_ <| rest_dims, s <| rest_subs, _)  => begin
            hashSubscript(s) * factor + hashSubscripts2(rest_dims, rest_subs, factor * 1000)
          end
        end
      end
       #=  TODO: change to using dimensions once cref types has been fixed.
       =#
       #= /* *i1 */ =#
  hash
end

 #= help function =#
function hashSubscript(sub::DAE.Subscript) ::ModelicaInteger
      local hash::ModelicaInteger

      hash = begin
          local exp::DAE.Exp
          local i::ModelicaInteger
        @match sub begin
          DAE.WHOLEDIM(__)  => begin
            0
          end

          DAE.INDEX(DAE.ICONST(i))  => begin
            i
          end

          DAE.SLICE(exp)  => begin
            hashExp(exp)
          end

          DAE.INDEX(exp)  => begin
            hashExp(exp)
          end

          DAE.WHOLE_NONEXP(exp)  => begin
            hashExp(exp)
          end
        end
      end
  hash
end

function crefEqualNoStringCompare(inCref1::DAE.ComponentRef, inCref2::DAE.ComponentRef) ::Bool
      local outEqual::Bool

      if referenceEq(inCref1, inCref2)
        outEqual = true
        return outEqual
      end
      outEqual = begin
        @match (inCref1, inCref2) begin
          (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
            inCref1.ident == inCref2.ident && subscriptEqual(inCref1.subscriptLst, inCref2.subscriptLst)
          end

          (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
            inCref1.ident == inCref2.ident && crefEqualNoStringCompare(inCref1.componentRef, inCref2.componentRef) && subscriptEqual(inCref1.subscriptLst, inCref2.subscriptLst)
          end

          _  => begin
              false
          end
        end
      end
  outEqual
end


#= Returns true if two component references are equal.
 No string comparison of unparsed crefs is performed! =#
function crefEqual(inComponentRef1::DAE.ComponentRef, inComponentRef2::DAE.ComponentRef) ::Bool
     local outBoolean::Bool

     outBoolean = crefEqualNoStringCompare(inComponentRef1, inComponentRef2)
 outBoolean
end


#= Strips the last subscripts of a ComponentRef =#
function crefStripLastSubs(inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
     local outComponentRef::DAE.ComponentRef

     outComponentRef = begin
         local id::DAE.Ident
         local subs::List{DAE.Subscript}
         local s::List{DAE.Subscript}
         local cr_1::DAE.ComponentRef
         local cr::DAE.ComponentRef
         local t2::DAE.Type
       @match inComponentRef begin
         DAE.CREF_IDENT(ident = id, identType = t2)  => begin
           makeCrefIdent(id, t2, nil)
         end

         DAE.CREF_QUAL(ident = id, identType = t2, subscriptLst = s, componentRef = cr)  => begin
             cr_1 = crefStripLastSubs(cr)
           makeCrefQual(id, t2, s, cr_1)
         end
       end
     end
 outComponentRef
end

#= @author: adrpo
 This function creates a DAE.CREF_IDENT(ident, identType, subscriptLst) =#
function makeCrefIdent(ident::DAE.Ident, identType::DAE.Type #= type of the identifier, without considering the subscripts =#, subscriptLst::List{<:DAE.Subscript}) ::DAE.ComponentRef
     local outCrefIdent::DAE.ComponentRef

     outCrefIdent = DAE.CREF_IDENT(ident, identType, subscriptLst)
 outCrefIdent
end

function makeUntypedCrefIdent(ident::DAE.Ident) ::DAE.ComponentRef
     local outCrefIdent::DAE.ComponentRef

     outCrefIdent = DAE.CREF_IDENT(ident, DAE.T_UNKNOWN_DEFAULT, nil)
 outCrefIdent
end

#= @author: adrpo
 This function creates a DAE.CREF_QUAL(ident, identType, subscriptLst, componentRef) =#
function makeCrefQual(ident::DAE.Ident, identType::DAE.Type #= type of the identifier, without considering the subscripts =#, subscriptLst::List{<:DAE.Subscript}, componentRef::DAE.ComponentRef) ::DAE.ComponentRef
     local outCrefQual::DAE.ComponentRef

     local subCref::DAE.ComponentRef

      #=  subCref := shareCref(componentRef);
      =#
      #=  outCrefQual := shareCref(DAE.CREF_QUAL(ident, identType, subscriptLst, subCref));
      =#
     outCrefQual = DAE.CREF_QUAL(ident, identType, subscriptLst, componentRef)
 outCrefQual
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
             ts = local_unparseType(t)
             s = stringAppendList(list(" +<", ts, "> "))
           s
         end

         DAE.SUB(ty = t)  => begin
             ts = local_unparseType(t)
             s = stringAppendList(list(" -<", ts, "> "))
           s
         end

         DAE.MUL(ty = t)  => begin
             ts = local_unparseType(t)
             s = stringAppendList(list(" *<", ts, "> "))
           s
         end

         DAE.DIV(ty = t)  => begin
             ts = local_unparseType(t)
             s = stringAppendList(list(" /<", ts, "> "))
           s
         end

         DAE.POW(__)  => begin
           " ^ "
         end

         DAE.ADD_ARR(ty = t)  => begin
             ts = local_unparseType(t)
             s = stringAppendList(list(" +<ADD_ARR><", ts, "> "))
           s
         end

         DAE.SUB_ARR(ty = t)  => begin
             ts = local_unparseType(t)
             s = stringAppendList(list(" -<SUB_ARR><", ts, "> "))
           s
         end

         DAE.MUL_ARR(__)  => begin
           " *<MUL_ARRAY> "
         end

         DAE.DIV_ARR(ty = t)  => begin
             ts = local_unparseType(t)
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

#= Joins two component references by concatenating them.
 alternative names: crefAppend
  =#
function joinCrefs(inComponentRef1::DAE.ComponentRef #=  first part of the new componentref =#, inComponentRef2::DAE.ComponentRef #=  last part of the new componentref =#) ::DAE.ComponentRef
     local outComponentRef::DAE.ComponentRef

     outComponentRef = begin
         local id::DAE.Ident
         local sub::List{DAE.Subscript}
         local cr2::DAE.ComponentRef
         local cr_1::DAE.ComponentRef
         local cr::DAE.ComponentRef
         local t2::DAE.Type
       @match (inComponentRef1, inComponentRef2) begin
         (DAE.CREF_IDENT(ident = id, identType = t2, subscriptLst = sub), cr2)  => begin
           makeCrefQual(id, t2, sub, cr2)
         end

         (DAE.CREF_QUAL(ident = id, identType = t2, subscriptLst = sub, componentRef = cr), cr2)  => begin
             cr_1 = joinCrefs(cr, cr2)
           makeCrefQual(id, t2, sub, cr_1)
         end
       end
     end
 outComponentRef
end

#= Returns the first identifier of a component reference. =#
function crefFirstIdent(inComponentRef::DAE.ComponentRef) ::DAE.Ident
     local outIdent::DAE.Ident

     outIdent = begin
         local id::DAE.Ident
       @match inComponentRef begin
         DAE.CREF_IDENT(ident = id)  => begin
           id
         end

         DAE.CREF_QUAL(ident = id)  => begin
           id
         end
       end
     end
 outIdent
end

#= This function converts a Absyn.Path to a ComponentRef. =#
function pathToCref(inPath::Absyn.Path) ::DAE.ComponentRef
     local outComponentRef::DAE.ComponentRef

     outComponentRef = begin
         local i::DAE.Ident
         local c::DAE.ComponentRef
         local p::Absyn.Path
       @match inPath begin
         Absyn.IDENT(name = i)  => begin
           makeCrefIdent(i, DAE.T_UNKNOWN_DEFAULT, nil)
         end

         Absyn.FULLYQUALIFIED(p)  => begin
           pathToCref(p)
         end

         Absyn.QUALIFIED(name = i, path = p)  => begin
             c = pathToCref(p)
           makeCrefQual(i, DAE.T_UNKNOWN_DEFAULT, nil, c)
         end
       end
     end
 outComponentRef
end

#= /***************************************************/ =#
#= /* Change  */ =#
#= /***************************************************/ =#

#= prepends (e..g as a suffix) an identifier to a component reference, given the identifier, subscript and the type
author: PA

 The crefPrependIdent function extends a ComponentRef by appending
 an identifier and a (possibly empty) list of subscripts.  Adding
 the identifier A to the component reference x.y[10] would
 produce the component reference x.y[10].A, for instance.

Example
crefPrependIdent(a.b,c,{},Real) => a.b.c [Real]
crefPrependIdent(a,c,{1},Integer[1]) => a.c[1] [Integer[1]]

alternative names: crefAddSuffix, crefAddIdent
=#
function crefPrependIdent(icr::DAE.ComponentRef, ident::String, subs::List{<:DAE.Subscript}, tp::DAE.Type) ::DAE.ComponentRef
     local newCr::DAE.ComponentRef

     newCr = begin
         local tp1::DAE.Type
         local id1::String
         local subs1::List{DAE.Subscript}
         local cr::DAE.ComponentRef
       @match (icr, ident, subs, tp) begin
         (DAE.CREF_IDENT(id1, tp1, subs1), _, _, _)  => begin
           makeCrefQual(id1, tp1, subs1, makeCrefIdent(ident, tp, subs))
         end

         (DAE.CREF_QUAL(id1, tp1, subs1, cr), _, _, _)  => begin
             cr = crefPrependIdent(cr, ident, subs, tp)
           makeCrefQual(id1, tp1, subs1, cr)
         end
       end
     end
 newCr
end


#= Helper function to ppStatementStr =#
function ppStmtStr(inStatement::DAE.Statement, inInteger::ModelicaInteger) ::String
     local outString::String

     outString = begin
         local s1::String
         local s2::String
         local s3::String
         local s4::String
         local s5::String
         local s6::String
         local str::String
         local s7::String
         local s8::String
         local s9::String
         local s10::String
         local s11::String
         local id::String
         local cond_str::String
         local msg_str::String
         local e1_str::String
         local e2_str::String
         local c::DAE.ComponentRef
         local e::DAE.Exp
         local cond::DAE.Exp
         local msg::DAE.Exp
         local e1::DAE.Exp
         local e2::DAE.Exp
         local i::ModelicaInteger
         local i_1::ModelicaInteger
         local index::ModelicaInteger
         local es::List{String}
         local expl::List{DAE.Exp}
         local then_::List{DAE.Statement}
         local stmts::List{DAE.Statement}
         local stmt::DAE.Statement
         local else_::DAE.Else
         local source::DAE.ElementSource
       @matchcontinue (inStatement, inInteger) begin
         (DAE.STMT_ASSIGN(exp1 = e2, exp = e), i)  => begin
             s1 = indentStr(i)
             s2 = CrefForHashTable.printExpStr(e2)
             s3 = CrefForHashTable.printExpStr(e)
             str = stringAppendList(list(s1, s2, " := ", s3, ";\\n"))
           str
         end

         (DAE.STMT_ASSIGN_ARR(lhs = e2, exp = e), i)  => begin
             s1 = indentStr(i)
             s2 = CrefForHashTable.printExpStr(e2)
             s3 = CrefForHashTable.printExpStr(e)
             str = stringAppendList(list(s1, s2, " := ", s3, ";\\n"))
           str
         end

         (DAE.STMT_TUPLE_ASSIGN(expExpLst = expl, exp = e), i)  => begin
             s1 = indentStr(i)
             s2 = CrefForHashTable.printExpStr(e)
             es = ListUtil.map(expl, CrefForHashTable.printExpStr)
             s3 = stringDelimitList(es, ", ")
             str = stringAppendList(list(s1, "(", s3, ") := ", s2, ";\\n"))
           str
         end

         (DAE.STMT_IF(exp = e, statementLst = then_, else_ = else_), i)  => begin
             s1 = indentStr(i)
             s2 = stringAppend(s1, "if ")
             s3 = CrefForHashTable.printExpStr(e)
             s4 = stringAppend(s2, s3)
             s5 = stringAppend(s4, " then\\n")
             i_1 = i + 2
             s6 = ppStmtListStr(then_, i_1)
             s7 = stringAppend(s5, s6)
             s8 = ppElseStr(else_, i)
             s9 = stringAppend(s7, s8)
             s10 = indentStr(i)
             s11 = stringAppend(s9, s10)
             str = stringAppend(s11, "end if;\\n")
           str
         end

         (DAE.STMT_FOR(iter = id, index = index, range = e, statementLst = stmts), i)  => begin
             s1 = indentStr(i)
             s2 = if index == (-1)
                   ""
                 else
                   "/* iter index " + intString(index) + " */"
                 end
             s3 = CrefForHashTable.printExpStr(e)
             i_1 = i + 2
             s4 = ppStmtListStr(stmts, i_1)
             s5 = indentStr(i)
             str = stringAppendList(list(s1, "for ", id, s2, " in ", s3, " loop\\n", s4, s5, "end for;\\n"))
           str
         end

         (DAE.STMT_PARFOR(iter = id, index = index, range = e, statementLst = stmts), i)  => begin
             s1 = indentStr(i)
             s2 = if index == (-1)
                   ""
                 else
                   "/* iter index " + intString(index) + " */"
                 end
             s3 = CrefForHashTable.printExpStr(e)
             i_1 = i + 2
             s4 = ppStmtListStr(stmts, i_1)
             s5 = indentStr(i)
             str = stringAppendList(list(s1, "parfor ", id, s2, " in ", s3, " loop\\n", s4, s5, "end for;\\n"))
           str
         end

         (DAE.STMT_WHILE(exp = e, statementLst = stmts), i)  => begin
             s1 = indentStr(i)
             s2 = stringAppend(s1, "while ")
             s3 = CrefForHashTable.printExpStr(e)
             s4 = stringAppend(s2, s3)
             s5 = stringAppend(s4, " loop\\n")
             i_1 = i + 2
             s6 = ppStmtListStr(stmts, i_1)
             s7 = stringAppend(s5, s6)
             s8 = indentStr(i)
             s9 = stringAppend(s7, s8)
             str = stringAppend(s9, "end while;\\n")
           str
         end

         (stmt && DAE.STMT_WHEN(__), i)  => begin
             s1 = indentStr(i)
             s2 = ppWhenStmtStr(stmt, i)
             str = stringAppend(s1, s2)
           str
         end

         (DAE.STMT_ASSERT(cond = cond, msg = msg), i)  => begin
             s1 = indentStr(i)
             cond_str = CrefForHashTable.printExpStr(cond)
             msg_str = CrefForHashTable.printExpStr(msg)
             str = stringAppendList(list(s1, "assert(", cond_str, ", ", msg_str, ");\\n"))
           str
         end

         (DAE.STMT_TERMINATE(msg = msg), i)  => begin
             s1 = indentStr(i)
             msg_str = CrefForHashTable.printExpStr(msg)
             str = stringAppendList(list(s1, "terminate(", msg_str, ");\\n"))
           str
         end

         (DAE.STMT_NORETCALL(exp = e), i)  => begin
             s1 = indentStr(i)
             s2 = begin
               @match e begin
                 DAE.CALL(attr = DAE.CALL_ATTR(tailCall = DAE.TAIL(__)))  => begin
                   "return "
                 end

                 _  => begin
                     ""
                 end
               end
             end
             s3 = CrefForHashTable.printExpStr(e)
             str = stringAppendList(list(s1, s2, s3, ";\\n"))
           str
         end

         (DAE.STMT_RETURN(__), i)  => begin
             s1 = indentStr(i)
             str = stringAppend(s1, "return;\\n")
           str
         end

         (DAE.STMT_BREAK(__), i)  => begin
             s1 = indentStr(i)
             str = stringAppend(s1, "break;\\n")
           str
         end

         (DAE.STMT_REINIT(var = e1, value = e2), i)  => begin
             s1 = indentStr(i)
             e1_str = CrefForHashTable.printExpStr(e1)
             e2_str = CrefForHashTable.printExpStr(e2)
             str = stringAppendList(list(s1, "reinit(", e1_str, ", ", e2_str, ");\\n"))
           str
         end

         (DAE.STMT_FAILURE(body = stmts), i)  => begin
             s1 = indentStr(i)
             s2 = ppStmtListStr(stmts, i + 2)
             str = stringAppendList(list(s1, "failure(\\n", s2, s1, ");\\n"))
           str
         end

         (DAE.STMT_ARRAY_INIT(name = s2), i)  => begin
             s1 = indentStr(i)
             str = stringAppendList(list(s1, "arrayInit(\\n", s2, s1, ");\\n"))
           str
         end

         (_, i)  => begin
             s1 = indentStr(i)
             str = stringAppend(s1, "**ALGORITHM COULD NOT BE GENERATED(DAE.mo)**;\\n")
           str
         end
       end
     end
 outString
end

#=
 Helper function to pp_stmt
=#
function ppStmtList(inAlgorithmStatementLst::List{<:DAE.Statement}, inInteger::ModelicaInteger)
     _ = begin
         local stmt::DAE.Statement
         local stmts::List{DAE.Statement}
         local i::ModelicaInteger
       @match (inAlgorithmStatementLst, inInteger) begin
         ( nil(), _)  => begin
           ()
         end

         (stmt <| stmts, i)  => begin
             ppStmt(stmt, i)
             ppStmtList(stmts, i)
           ()
         end
       end
     end
end

#=
 Helper function to pp_stmt_str
=#
function ppStmtListStr(inAlgorithmStatementLst::List{<:DAE.Statement}, inInteger::ModelicaInteger = 0) ::String
     local outString::String

     outString = begin
         local s1::String
         local s2::String
         local str::String
         local stmt::DAE.Statement
         local stmts::List{DAE.Statement}
         local i::ModelicaInteger
       @match (inAlgorithmStatementLst, inInteger) begin
         ( nil(), _)  => begin
           ""
         end

         (stmt <| stmts, i)  => begin
             s1 = ppStmtStr(stmt, i)
             s2 = ppStmtListStr(stmts, i)
             str = stringAppend(s1, s2)
           str
         end
       end
     end
 outString
end

#=
 Helper function to pp_stmt
=#
function ppElse(inElse::DAE.Else, inInteger::ModelicaInteger)
     _ = begin
         local i_1::ModelicaInteger
         local i::ModelicaInteger
         local e::DAE.Exp
         local then_::List{DAE.Statement}
         local stmts::List{DAE.Statement}
         local else_::DAE.Else
       @match (inElse, inInteger) begin
         (DAE.NOELSE(__), _)  => begin
           ()
         end

         (DAE.ELSEIF(exp = e, statementLst = then_, else_ = else_), i)  => begin
             indent(i)
             Print.printBuf("elseif ")
             CrefForHashTable.printExp(e)
             Print.printBuf(" then\\n")
             i_1 = i + 2
             ppStmtList(then_, i_1)
             ppElse(else_, i)
           ()
         end

         (DAE.ELSE(statementLst = stmts), i)  => begin
             indent(i)
             Print.printBuf("else\\n")
             i_1 = i + 2
             ppStmtList(stmts, i_1)
           ()
         end
       end
     end
end

#=
 Helper function to ppElseStr
=#
function ppElseStr(inElse::DAE.Else, inInteger::ModelicaInteger) ::String
     local outString::String

     outString = begin
         local s1::String
         local s2::String
         local s3::String
         local s4::String
         local s5::String
         local s6::String
         local s7::String
         local s8::String
         local str::String
         local i_1::ModelicaInteger
         local i::ModelicaInteger
         local e::DAE.Exp
         local then_::List{DAE.Statement}
         local stmts::List{DAE.Statement}
         local else_::DAE.Else
       @match (inElse, inInteger) begin
         (DAE.NOELSE(__), _)  => begin
           ""
         end

         (DAE.ELSEIF(exp = e, statementLst = then_, else_ = else_), i)  => begin
             s1 = indentStr(i)
             s2 = stringAppend(s1, "elseif ")
             s3 = CrefForHashTable.printExpStr(e)
             s4 = stringAppend(s2, s3)
             s5 = stringAppend(s4, " then\\n")
             i_1 = i + 2
             s6 = ppStmtListStr(then_, i_1)
             s7 = stringAppend(s5, s6)
             s8 = ppElseStr(else_, i)
             str = stringAppend(s7, s8)
           str
         end

         (DAE.ELSE(statementLst = stmts), i)  => begin
             s1 = indentStr(i)
             s2 = stringAppend(s1, "else\\n")
             i_1 = i + 2
             s3 = ppStmtListStr(stmts, i_1)
             str = stringAppend(s2, s3)
           str
         end
       end
     end
 outString
end

#=
 Print an indentation, given an indent level.
=#
function indent(inInteger::ModelicaInteger)
     _ = begin
         local i_1::ModelicaInteger
         local i::ModelicaInteger
       @matchcontinue inInteger begin
         0  => begin
           ()
         end

         i  => begin
             Print.printBuf(" ")
             i_1 = i - 1
             indent(i_1)
           ()
         end
       end
     end
end

#=
 Print an indentation to a string, given an indent level.
=#
function indentStr(inInteger::ModelicaInteger) ::String
     local outString::String

     outString = begin
         local i_1::ModelicaInteger
         local i::ModelicaInteger
         local s1::String
         local str::String
       @matchcontinue inInteger begin
         0  => begin
           ""
         end

         i  => begin
             i_1 = i - 1
             s1 = indentStr(i_1)
             str = stringAppend(" ", s1)
           str
         end
       end
     end
 outString
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
            crefCompareGeneric(inExp1.componentRef, cr)
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
            crefCompareGeneric(inExp1.name, cr)
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


######################################################

module CompareWithSubsType
  using ExportAll

  const WithoutSubscripts = 1
  const WithGenericSubscript = 2
  const WithGenericSubscriptNotAlphabetic = 3
  const WithIntSubscript = 4

  @exportAll()
end

module CompareWithGenericSubscript

  using MetaModelica
  #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
  using ExportAll

      import ..CompareWithSubsType
      import DAE

      compareSubscript = CompareWithSubsType.WithGenericSubscript::Int64

      function cref_compare(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
            local res::ModelicaInteger

            res = begin
              @match (cr1, cr2) begin
                (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
                    res = stringCompare(cr1.ident, cr2.ident)
                    if compareSubscript == CompareWithSubsType.WithoutSubscripts || res != 0
                      return
                    end
                  compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                end

                (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
                    res = stringCompare(cr1.ident, cr2.ident)
                    if res != 0
                      return
                    end
                    if compareSubscript != CompareWithSubsType.WithoutSubscripts
                      res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                      if res != 0
                        return
                      end
                    end
                  cref_compare(cr1.componentRef, cr2.componentRef)
                end

                (DAE.CREF_QUAL(__), DAE.CREF_IDENT(__))  => begin
                    res = stringCompare(cr1.ident, cr2.ident)
                    if res != 0
                      return
                    end
                    if compareSubscript != CompareWithSubsType.WithoutSubscripts
                      res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                    end
                    if res != 0
                      return
                    end
                  1
                end

                (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
                    res = stringCompare(cr1.ident, cr2.ident)
                    if res != 0
                      return
                    end
                    if compareSubscript != CompareWithSubsType.WithoutSubscripts
                      res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                    end
                    if res != 0
                      return
                    end
                  -1
                end
              end
            end
        res
      end

      #= Returns the expression in a subscript index.
       If the subscript is not an index the function fails. =#
     function subscriptIndexExp(inSubscript::DAE.Subscript) ::DAE.Exp
           local outExp::DAE.Exp

           @match DAE.INDEX(exp = outExp) = inSubscript
       outExp
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

      function subscriptInt(inSubscript::DAE.Subscript) ::ModelicaInteger
            local outInteger::ModelicaInteger = expArrayIndex(subscriptIndexExp(inSubscript))
        outInteger
      end

      function compareSubs(ss1::List{<:DAE.Subscript}, ss2::List{<:DAE.Subscript}) ::ModelicaInteger
            local res::ModelicaInteger = 0

            local ss::List{DAE.Subscript} = ss2
            local s2::DAE.Subscript
            local i1::ModelicaInteger
            local i2::ModelicaInteger
            local e1::DAE.Exp
            local e2::DAE.Exp

            for s1 in ss1
              if listEmpty(ss)
                res = -1
                return res
              end
              @match _cons(s2, ss) = ss
              if compareSubscript == CompareWithSubsType.WithGenericSubscript
                res = stringCompare(printSubscriptStr(s1), printSubscriptStr(s2))
              elseif compareSubscript == CompareWithSubsType.WithGenericSubscriptNotAlphabetic
                res = compareSubscripts(s1, s2)
              else
                i1 = subscriptInt(s1)
                i2 = subscriptInt(s2)
                res = if i1 < i2
                      -1
                    elseif (i1 > i2)
                          1
                    else
                      0
                    end
              end
              if res != 0
                return res
              end
            end
            if ! listEmpty(ss)
              res = 1
            end
        res
      end

  #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
  @exportAll()
end

module CompareWithGenericSubscriptNotAlphabetic


  using MetaModelica
  #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
  using ExportAll


  using ..CompareWithGenericSubscript
  import ..CompareWithSubsType

  compareSubscript = CompareWithSubsType.WithGenericSubscriptNotAlphabetic

  #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
  @exportAll()
end

module CompareWithoutSubscripts


  using MetaModelica
  #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
  using ExportAll

  using ..CompareWithGenericSubscript
  import ..CompareWithSubsType

  compareSubscript = CompareWithSubsType.WithoutSubscripts

  #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
  @exportAll()
end

module CompareWithIntSubscript


  using MetaModelica
  #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
  using ExportAll

  using ..CompareWithGenericSubscript
  import ..CompareWithSubsType

  compareSubscript = CompareWithSubsType.WithIntSubscript

  #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
  @exportAll()
end

 #= A sorting function (greatherThan) for crefs =#
function crefSortFunc(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
      local greaterThan::Bool
      greaterThan = CompareWithGenericSubscript.cref_compare(cr1, cr2) > 0
  greaterThan
end

 #= A sorting function for crefs =#
function crefCompareGeneric(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
      local comp::ModelicaInteger
      comp = CompareWithGenericSubscript.cref_compare(cr1, cr2)
  comp
end

 #= A sorting function for crefs =#
function crefCompareIntSubscript(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
      local comp::ModelicaInteger

      comp = CompareWithIntSubscript.cref_compare(cr1, cr2)
  comp
end

 #= A sorting function for crefs =#
function crefCompareGenericNotAlphabetic(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
      local comp::ModelicaInteger

      comp = CompareWithGenericSubscriptNotAlphabetic.cref_compare(cr1, cr2)
  comp
end

 #= mahge:
  Compares two crefs lexically. Subscripts are treated as if they are
  they are at the end of the whole component reference.
  e.g. r[1].i is greater than r[2].a.
  returns true if the first cref is greater than the second =#
function crefLexicalGreaterSubsAtEnd(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
      local isGreater::Bool

      isGreater = crefLexicalCompareSubsAtEnd(cr1, cr2) > 0
  isGreater
end

 #= mahge:
  Compares two crefs lexically. Subscripts are treated as if they are
  they are at the end of the whole component reference.
  e.g. r[1].i is greater than r[2].a.
  returns value is same as C strcmp. 0 if equal, 1 if first is greater, -1 otherwise =#
function crefLexicalCompareSubsAtEnd(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
      local res::ModelicaInteger

      local subs1::List{ModelicaInteger}
      local subs2::List{ModelicaInteger}

      res = CompareWithoutSubscripts.cref_compare(cr1, cr2)
      if res != 0
        return res
      end
      subs1 = subscriptsInt(crefSubs(cr1))
      subs2 = subscriptsInt(crefSubs(cr2))
      res = crefLexicalCompareSubsAtEnd2(subs1, subs2)
  res
end

 #= mahge:
  Helper function for crefLexicalCompareubsAtEnd
  compares subs. However only if the crefs with out subs are equal.
  (i.e. identsCompared is 0)
  otherwise just returns =#
function crefLexicalCompareSubsAtEnd2(inSubs1::List{<:ModelicaInteger}, inSubs2::List{<:ModelicaInteger}) ::ModelicaInteger
      local res::ModelicaInteger = 0

      local rest::List{ModelicaInteger} = inSubs2

      for i in inSubs1
        @match _cons(res, rest) = rest
        res = if i > res
              1
            elseif (i < res)
                  -1
            else
              0
            end
        if res != 0
          return res
        end
      end
  res
end

#= The subscriptCref function adds a subscript to the ComponentRef
 For instance a.b with subscript 10 becomes a.b[10] and c.d[1,2]
 with subscript 3,4 becomes c.d[1,2,3,4] =#
function subscriptCref(inComponentRef::DAE.ComponentRef, inSubscriptLst::List{<:DAE.Subscript}) ::DAE.ComponentRef
     local outComponentRef::DAE.ComponentRef

     outComponentRef = begin
         local newsub_1::List{DAE.Subscript}
         local sub::List{DAE.Subscript}
         local newsub::List{DAE.Subscript}
         local id::DAE.Ident
         local cref_1::DAE.ComponentRef
         local cref::DAE.ComponentRef
         local t2::DAE.Type
       @match (inComponentRef, inSubscriptLst) begin
         (DAE.CREF_IDENT(ident = id, subscriptLst = sub, identType = t2), newsub)  => begin
             newsub_1 = listAppend(sub, newsub)
           makeCrefIdent(id, t2, newsub_1)
         end

         (DAE.CREF_QUAL(ident = id, subscriptLst = sub, componentRef = cref, identType = t2), newsub)  => begin
             cref_1 = subscriptCref(cref, newsub)
           makeCrefQual(id, t2, sub, cref_1)
         end
       end
     end
 outComponentRef
end

#= Removes all subscript of a componentref =#
function crefStripSubs(inCref::DAE.ComponentRef) ::DAE.ComponentRef
      local outCref::DAE.ComponentRef

      outCref = begin
          local id::DAE.Ident
          local cr::DAE.ComponentRef
          local ty::DAE.Type
        @match inCref begin
          DAE.CREF_IDENT(ident = id, identType = ty)  => begin
            makeCrefIdent(id, ty, nil)
          end

          DAE.CREF_QUAL(componentRef = cr, identType = ty, ident = id)  => begin
              outCref = crefStripSubs(cr)
            makeCrefQual(id, ty, nil, outCref)
          end
        end
      end
  outCref
end

#= Strips the first part of a component reference,
i.e the identifier and eventual subscripts =#
function crefStripFirstIdent(inCr::DAE.ComponentRef) ::DAE.ComponentRef
     local outCr::DAE.ComponentRef

     outCr = begin
         local cr::DAE.ComponentRef
       @match inCr begin
         DAE.CREF_QUAL(componentRef = cr)  => begin
           cr
         end
       end
     end
 outCr
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

#= Constructs a cref from a list of CREF_IDENTs. =#
function implode(inParts::List{<:DAE.ComponentRef}) ::DAE.ComponentRef
     local outCref::DAE.ComponentRef

     local first::DAE.ComponentRef
     local rest::List{DAE.ComponentRef}

     outCref = implode_reverse(listReverse(inParts))
 outCref
end

#= Constructs a cref from a reversed list of CREF_IDENTs. =#
function implode_reverse(inParts::List{<:DAE.ComponentRef}) ::DAE.ComponentRef
     local outCref::DAE.ComponentRef

     local first::DAE.ComponentRef
     local rest::List{DAE.ComponentRef}

     @match _cons(first, rest) = inParts
     outCref = implode_tail(rest, first)
 outCref
end

function implode_tail(inParts::List{<:DAE.ComponentRef}, inAccumCref::DAE.ComponentRef) ::DAE.ComponentRef
     local outCref::DAE.ComponentRef

     outCref = begin
         local id::DAE.Ident
         local ty::DAE.Type
         local subs::List{DAE.Subscript}
         local rest::List{DAE.ComponentRef}
         local cr::DAE.ComponentRef
       @match (inParts, inAccumCref) begin
         (DAE.CREF_IDENT(id, ty, subs) <| rest, _)  => begin
             cr = DAE.CREF_QUAL(id, ty, subs, inAccumCref)
           implode_tail(rest, cr)
         end

         ( nil(), _)  => begin
           inAccumCref
         end
       end
     end
 outCref
end

    @exportAll()
end

  module ExpressionDumpTpl 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import Tpl

        import Absyn

        import ClassInf

        import DAE

        import Dump

        import Expression

        import System

        import Config

        import Types

        import Flags

        import AbsynDumpTpl

        import DAEDumpTpl

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
                      ret_0 = Types.unparseType(a_ty)
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
                      ret_0 = Types.unparseType(a_attr_ty)
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
                      ret_0 = Types.unparseType(a_ty)
                      txt = Tpl.writeStr(txt, ret_0)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                    txt
                  end
                  
                  (txt, _, a_ty)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* scalar "))
                      ret_1 = Types.unparseType(a_ty)
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
                      ret_0 = Types.unparseType(a_ty)
                      txt = Tpl.writeStr(txt, ret_0)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" */ "))
                    txt
                  end
                  
                  (txt, _, a_ty)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("/* scalar "))
                      ret_1 = Types.unparseType(a_ty)
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
                      ret_0 = Types.unparseType(a_ty)
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
                      ret_0 = Types.unparseType(a_ty)
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
              ret_1 = Expression.shouldParenthesize(a_operand, a_operation, a_lhs)
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
                      l_body__str = DAEDumpTpl.dumpStatements(Tpl.emptyTxt, i_body)
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
                      l_body__str = DAEDumpTpl.dumpStatements(Tpl.emptyTxt, i_body)
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
                      ret_0 = Types.unparseType(a_ty)
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
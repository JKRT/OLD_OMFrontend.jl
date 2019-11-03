  module DAEDumpTpl 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import Tpl

        import ExpressionDumpTpl

        import ClassInf

        import Config

        import Absyn

        import SCode

        import DAEDump

        import DAE

        import SCodeDump

        import System

        import Flags

        # import Connect

        import AbsynDumpTpl

        import SCodeDumpTpl

        function lm_14(in_txt::Tpl.Text, in_items::List{<:DAEDump.compWithSplitElements}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAEDump.compWithSplitElements}
                  local i_dae::DAEDump.compWithSplitElements
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_dae <| rest)  => begin
                      txt = dumpComp(txt, i_dae)
                      txt = Tpl.nextIter(txt)
                      txt = lm_14(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_15(in_txt::Tpl.Text, in_a_funLists::DAEDump.functionList) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_funcs::List{DAE.Function}
                @match (in_txt, in_a_funLists) begin
                  (txt, DAEDump.FUNCTION_LIST(funcs = i_funcs))  => begin
                      txt = dumpFunctions(txt, i_funcs)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_16(in_txt::Tpl.Text, in_a_fun__str::Tpl.Text, in_a_comp__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_comp__str::Tpl.Text
                  local i_fun__str::Tpl.Text
                @match (in_txt, in_a_fun__str, in_a_comp__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()), a_comp__str)  => begin
                      txt = Tpl.writeText(txt, a_comp__str)
                    txt
                  end
                  
                  (txt, i_fun__str, a_comp__str)  => begin
                      txt = Tpl.writeText(txt, i_fun__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING_LIST(list("\\n", "\\n"), true))
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, a_comp__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpDAE(txt::Tpl.Text, a_fixedDaeList::List{<:DAEDump.compWithSplitElements}, a_funLists::DAEDump.functionList) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_fun__str::Tpl.Text
              local l_comp__str::Tpl.Text

              l_comp__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              l_comp__str = lm_14(l_comp__str, a_fixedDaeList)
              l_comp__str = Tpl.popIter(l_comp__str)
              l_fun__str = fun_15(Tpl.emptyTxt, a_funLists)
              out_txt = fun_16(txt, l_fun__str, l_comp__str)
          out_txt
        end

        function fun_18(in_txt::Tpl.Text, in_mArg::Bool, in_a_name::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_name::String
                  local ret_0::String
                @match (in_txt, in_mArg, in_a_name) begin
                  (txt, false, a_name)  => begin
                      txt = Tpl.writeStr(txt, a_name)
                    txt
                  end
                  
                  (txt, _, a_name)  => begin
                      ret_0 = System.stringReplace(a_name, ".", "__")
                      txt = Tpl.writeStr(txt, ret_0)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_19(in_txt::Tpl.Text, in_a_ann__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_ann__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("  "))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpComp(in_txt::Tpl.Text, in_a_fixedDae::DAEDump.compWithSplitElements) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_spltElems::DAEDump.splitElements
                  local i_name::String
                  local i_comment::Option{SCode.Comment}
                  local ret_3::Bool
                  local l_name__rep::Tpl.Text
                  local l_ann__str::Tpl.Text
                  local l_cmt__str::Tpl.Text
                @match (in_txt, in_a_fixedDae) begin
                  (txt, DAEDump.COMP_WITH_SPLIT(comment = i_comment, name = i_name, spltElems = i_spltElems))  => begin
                      l_cmt__str = dumpCommentOpt(Tpl.emptyTxt, i_comment)
                      l_ann__str = dumpClassAnnotation(Tpl.emptyTxt, i_comment)
                      ret_3 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                      l_name__rep = fun_18(Tpl.emptyTxt, ret_3, i_name)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("class "))
                      txt = Tpl.writeText(txt, l_name__rep)
                      txt = Tpl.writeText(txt, l_cmt__str)
                      txt = Tpl.softNewLine(txt)
                      txt = dumpCompStream(txt, i_spltElems)
                      txt = Tpl.softNewLine(txt)
                      txt = fun_19(txt, l_ann__str)
                      txt = Tpl.writeText(txt, l_ann__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                      txt = Tpl.writeText(txt, l_name__rep)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                      txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE())
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_21(in_txt::Tpl.Text, in_items::List{<:DAEDump.compWithSplitElements}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAEDump.compWithSplitElements}
                  local i_flatSM::DAEDump.compWithSplitElements
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_flatSM <| rest)  => begin
                      txt = dumpStateMachineSection(txt, i_flatSM)
                      txt = Tpl.nextIter(txt)
                      txt = lm_21(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCompStream(in_txt::Tpl.Text, in_a_elems::DAEDump.splitElements) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_sm::List{DAEDump.compWithSplitElements}
                  local i_a::List{DAE.Element}
                  local i_e::List{DAE.Element}
                  local i_ia::List{DAE.Element}
                  local i_ie::List{DAE.Element}
                  local i_v::List{DAE.Element}
                  local l_sm__str::Tpl.Text
                  local l_al__str::Tpl.Text
                  local l_eq__str::Tpl.Text
                  local l_ial__str::Tpl.Text
                  local l_ieq__str::Tpl.Text
                  local l_var__str::Tpl.Text
                @match (in_txt, in_a_elems) begin
                  (txt, DAEDump.SPLIT_ELEMENTS(v = i_v, ie = i_ie, ia = i_ia, e = i_e, a = i_a, sm = i_sm))  => begin
                      l_var__str = dumpVars(Tpl.emptyTxt, i_v)
                      l_ieq__str = dumpInitialEquationSection(Tpl.emptyTxt, i_ie)
                      l_ial__str = dumpInitialAlgorithmSection(Tpl.emptyTxt, i_ia)
                      l_eq__str = dumpEquationSection(Tpl.emptyTxt, i_e)
                      l_al__str = dumpAlgorithmSection(Tpl.emptyTxt, i_a)
                      l_sm__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_sm__str = lm_21(l_sm__str, i_sm)
                      l_sm__str = Tpl.popIter(l_sm__str)
                      txt = Tpl.writeText(txt, l_var__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_sm__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_ieq__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_ial__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_eq__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_al__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_23(in_txt::Tpl.Text, in_items::List{<:DAE.Function}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Function}
                  local i_func::DAE.Function
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_func <| rest)  => begin
                      txt = dumpFunction(txt, i_func)
                      txt = Tpl.nextIter(txt)
                      txt = lm_23(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctions(txt::Tpl.Text, a_funcs::List{<:DAE.Function}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING_LIST(list("\\n", "\\n"), true)), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_23(out_txt, a_funcs)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function fun_25(in_txt::Tpl.Text, in_a_isImpure::Bool) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_isImpure) begin
                  (txt, false)  => begin
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("impure "))
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_26(in_txt::Tpl.Text, in_a_ann__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_ann__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("  "))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunction(in_txt::Tpl.Text, in_a_function::DAE.Function) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_type__::DAE.Type
                  local i_functions::List{DAE.FunctionDefinition}
                  local i_path::Absyn.Path
                  local i_isImpure::Bool
                  local i_comment::Option{SCode.Comment}
                  local i_inlineType::DAE.InlineType
                  local l_impure__str::Tpl.Text
                  local l_ann__str::Tpl.Text
                  local l_cmt__str::Tpl.Text
                  local l_inline__str::Tpl.Text
                @match (in_txt, in_a_function) begin
                  (txt, DAE.FUNCTION(inlineType = i_inlineType, comment = i_comment, isImpure = i_isImpure, path = i_path, functions = i_functions))  => begin
                      l_inline__str = dumpInlineType(Tpl.emptyTxt, i_inlineType)
                      l_cmt__str = dumpCommentOpt(Tpl.emptyTxt, i_comment)
                      l_ann__str = dumpClassAnnotation(Tpl.emptyTxt, i_comment)
                      l_impure__str = fun_25(Tpl.emptyTxt, i_isImpure)
                      txt = Tpl.writeText(txt, l_impure__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("function "))
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                      txt = Tpl.writeText(txt, l_inline__str)
                      txt = Tpl.writeText(txt, l_cmt__str)
                      txt = Tpl.softNewLine(txt)
                      txt = dumpFunctionDefinitions(txt, i_functions)
                      txt = Tpl.softNewLine(txt)
                      txt = fun_26(txt, l_ann__str)
                      txt = Tpl.writeText(txt, l_ann__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, DAE.RECORD_CONSTRUCTOR(path = i_path, type_ = i_type__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("function "))
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" \\Automatically generated record constructor for "))
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE("\\\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = dumpRecordInputVarStr(txt, i_type__)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("output "))
                      txt = dumpPathLastIndent(txt, i_path)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" res;\\n"))
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_28(in_txt::Tpl.Text, in_items::List{<:DAE.FunctionDefinition}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.FunctionDefinition}
                  local i_func::DAE.FunctionDefinition
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_func <| rest)  => begin
                      txt = dumpFunctionDefinition(txt, i_func)
                      txt = Tpl.nextIter(txt)
                      txt = lm_28(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctionDefinitions(txt::Tpl.Text, a_functions::List{<:DAE.FunctionDefinition}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_28(out_txt, a_functions)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpFunctionDefinition(in_txt::Tpl.Text, in_a_functions::DAE.FunctionDefinition) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_externalDecl::DAE.ExternalDecl
                  local i_body::List{DAE.Element}
                @match (in_txt, in_a_functions) begin
                  (txt, DAE.FUNCTION_DEF(body = i_body))  => begin
                      txt = dumpFunctionBody(txt, i_body)
                    txt
                  end
                  
                  (txt, DAE.FUNCTION_EXT(body = i_body, externalDecl = i_externalDecl))  => begin
                      txt = dumpFunctionBody(txt, i_body)
                      txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE())
                      txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE())
                      txt = dumpExternalDecl(txt, i_externalDecl)
                    txt
                  end
                  
                  (txt, DAE.FUNCTION_DER_MAPPER(derivedFunction = _))  => begin
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_31(in_txt::Tpl.Text, in_a_func__name__str::Tpl.Text, in_a_func__args__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_func__args__str::Tpl.Text
                  local i_func__name__str::Tpl.Text
                @match (in_txt, in_a_func__name__str, in_a_func__args__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()), _)  => begin
                    txt
                  end
                  
                  (txt, i_func__name__str, a_func__args__str)  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeText(txt, i_func__name__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, a_func__args__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_32(in_txt::Tpl.Text, in_a_ext__output__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ext__output__str::Tpl.Text
                @match (in_txt, in_a_ext__output__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_ext__output__str)  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeText(txt, i_ext__output__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" ="))
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_33(in_txt::Tpl.Text, in_a_ann::Option{<:SCode.Annotation}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_annotation::SCode.Annotation
                @match (in_txt, in_a_ann) begin
                  (txt, SOME(i_annotation))  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = dumpAnnotation(txt, i_annotation)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpExternalDecl(in_txt::Tpl.Text, in_a_externalDecl::DAE.ExternalDecl) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ann::Option{SCode.Annotation}
                  local i_language::String
                  local i_returnArg::DAE.ExtArg
                  local i_args::List{DAE.ExtArg}
                  local i_name::String
                  local l_ann__str::Tpl.Text
                  local l_lang__str::Tpl.Text
                  local l_output__str::Tpl.Text
                  local l_ext__output__str::Tpl.Text
                  local l_func__str::Tpl.Text
                  local l_func__args__str::Tpl.Text
                  local l_func__name__str::Tpl.Text
                @match (in_txt, in_a_externalDecl) begin
                  (txt, DAE.EXTERNALDECL(name = i_name, args = i_args, returnArg = i_returnArg, language = i_language, ann = i_ann))  => begin
                      l_func__name__str = Tpl.writeStr(Tpl.emptyTxt, i_name)
                      l_func__args__str = dumpExtArgs(Tpl.emptyTxt, i_args)
                      l_func__str = fun_31(Tpl.emptyTxt, l_func__name__str, l_func__args__str)
                      l_ext__output__str = dumpExtArg(Tpl.emptyTxt, i_returnArg)
                      l_output__str = fun_32(Tpl.emptyTxt, l_ext__output__str)
                      l_lang__str = Tpl.writeStr(Tpl.emptyTxt, i_language)
                      l_ann__str = fun_33(Tpl.emptyTxt, i_ann)
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("external \\"))
                      txt = Tpl.writeText(txt, l_lang__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("\\"))
                      txt = Tpl.writeText(txt, l_output__str)
                      txt = Tpl.writeText(txt, l_func__str)
                      txt = Tpl.writeText(txt, l_ann__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_35(in_txt::Tpl.Text, in_items::List{<:DAE.ExtArg}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.ExtArg}
                  local i_arg::DAE.ExtArg
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_arg <| rest)  => begin
                      txt = dumpExtArg(txt, i_arg)
                      txt = Tpl.nextIter(txt)
                      txt = lm_35(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpExtArgs(txt::Tpl.Text, a_args::List{<:DAE.ExtArg}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_35(out_txt, a_args)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpExtArg(in_txt::Tpl.Text, in_a_arg::DAE.ExtArg) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_exp::DAE.Exp
                  local i_componentRef::DAE.ComponentRef
                @match (in_txt, in_a_arg) begin
                  (txt, DAE.EXTARG(componentRef = i_componentRef))  => begin
                      txt = dumpCref(txt, i_componentRef)
                    txt
                  end
                  
                  (txt, DAE.EXTARGEXP(exp = i_exp))  => begin
                      txt = dumpExp(txt, i_exp)
                    txt
                  end
                  
                  (txt, DAE.EXTARGSIZE(componentRef = i_componentRef, exp = i_exp))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("size("))
                      txt = dumpCref(txt, i_componentRef)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                      txt = dumpExp(txt, i_exp)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpRecordInputVarStr(in_txt::Tpl.Text, in_a_type__::DAE.Type) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_funcResultType::DAE.Type
                  local i_varLst::List{DAE.Var}
                @match (in_txt, in_a_type__) begin
                  (txt, DAE.T_COMPLEX(varLst = i_varLst))  => begin
                      txt = dumpRecordVars(txt, i_varLst)
                    txt
                  end
                  
                  (txt, DAE.T_FUNCTION(funcResultType = i_funcResultType))  => begin
                      txt = dumpRecordInputVarStr(txt, i_funcResultType)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_39(in_txt::Tpl.Text, in_items::List{<:DAE.Var}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Var}
                  local i_v::DAE.Var
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_v <| rest)  => begin
                      txt = dumpRecordVar(txt, i_v)
                      txt = Tpl.nextIter(txt)
                      txt = lm_39(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpRecordVars(txt::Tpl.Text, a_varLst::List{<:DAE.Var}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_39(out_txt, a_varLst)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpRecordVar(in_txt::Tpl.Text, in_a_v::DAE.Var) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_name::DAE.Ident
                  local i_ty::DAE.Type
                  local i_binding::DAE.Binding
                  local i_attributes::DAE.Attributes
                  local l_ty__str::Tpl.Text
                  local l_attr::Tpl.Text
                  local l_binding__str::Tpl.Text
                  local l_attr__str::Tpl.Text
                @match (in_txt, in_a_v) begin
                  (txt, DAE.TYPES_VAR(attributes = i_attributes, binding = i_binding, ty = i_ty, name = i_name))  => begin
                      l_attr__str = dumpRecordConstructorInputAttr(Tpl.emptyTxt, i_attributes)
                      l_binding__str = dumpRecordConstructorBinding(Tpl.emptyTxt, i_binding)
                      l_attr = Tpl.emptyTxt
                      (l_ty__str, l_attr) = dumpType(Tpl.emptyTxt, i_ty, l_attr)
                      txt = Tpl.writeText(txt, l_attr__str)
                      txt = Tpl.writeText(txt, l_ty__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.writeText(txt, l_attr)
                      txt = Tpl.writeText(txt, l_binding__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpRecordConstructorInputAttr(in_txt::Tpl.Text, in_a_attr::DAE.Attributes) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_attr) begin
                  (txt, DAE.ATTR(visibility = SCode.PROTECTED(__)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("protected "))
                    txt
                  end
                  
                  (txt, DAE.ATTR(variability = SCode.CONST(__)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("constant "))
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("input "))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpRecordConstructorBinding(in_txt::Tpl.Text, in_a_binding::DAE.Binding) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_exp::DAE.Exp
                @match (in_txt, in_a_binding) begin
                  (txt, DAE.UNBOUND(__))  => begin
                    txt
                  end
                  
                  (txt, DAE.EQBOUND(exp = i_exp))  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("= "))
                      txt = dumpExp(txt, i_exp)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpRecordVarBinding(in_txt::Tpl.Text, in_a_binding::DAE.Binding) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_exp::DAE.Exp
                @match (in_txt, in_a_binding) begin
                  (txt, DAE.UNBOUND(__))  => begin
                    txt
                  end
                  
                  (txt, DAE.EQBOUND(exp = i_exp))  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("= "))
                      txt = dumpExp(txt, i_exp)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, DAE.VALBOUND(valBound = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("value bound***** check what to display"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_45(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_lst::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_lst <| rest)  => begin
                      txt = dumpFunctionElement(txt, i_lst)
                      txt = Tpl.nextIter(txt)
                      txt = lm_45(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_46(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_lst::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_lst <| rest)  => begin
                      txt = dumpFunctionAnnotation(txt, i_lst)
                      txt = lm_46(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctionBody(txt::Tpl.Text, a_dAElist::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_45(out_txt, a_dAElist)
              out_txt = Tpl.popIter(out_txt)
              out_txt = lm_46(out_txt, a_dAElist)
          out_txt
        end

        function dumpFunctionElement(in_txt::Tpl.Text, in_a_lst::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_algorithm__::DAE.Algorithm
                  local i_lst::DAE.Element
                @match (in_txt, in_a_lst) begin
                  (txt, i_lst && DAE.VAR(componentRef = _))  => begin
                      txt = dumpVar(txt, i_lst, true)
                    txt
                  end
                  
                  (txt, DAE.INITIALALGORITHM(algorithm_ = i_algorithm__))  => begin
                      txt = dumpFunctionAlgorithm(txt, i_algorithm__, "initial algorithm")
                    txt
                  end
                  
                  (txt, DAE.ALGORITHM(algorithm_ = i_algorithm__))  => begin
                      txt = dumpFunctionAlgorithm(txt, i_algorithm__, "algorithm")
                    txt
                  end
                  
                  (txt, DAE.COMMENT(cmt = _))  => begin
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Element not found"))
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_49(in_txt::Tpl.Text, in_a_x::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_x::Tpl.Text
                @match (in_txt, in_a_x) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_x)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE())
                      txt = Tpl.writeText(txt, i_x)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctionAnnotation(in_txt::Tpl.Text, in_a_lst::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt::SCode.Comment
                  local l_x::Tpl.Text
                @match (in_txt, in_a_lst) begin
                  (txt, DAE.COMMENT(cmt = i_cmt))  => begin
                      l_x = dumpCommentAnnotationNoOpt(Tpl.emptyTxt, i_cmt)
                      txt = fun_49(txt, l_x)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctionAlgorithm(in_txt::Tpl.Text, in_a_algorithm__::DAE.Algorithm, in_a_label::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_label::String
                  local i_statementLst::List{DAE.Statement}
                @match (in_txt, in_a_algorithm__, in_a_label) begin
                  (txt, DAE.ALGORITHM_STMTS(statementLst = i_statementLst), a_label)  => begin
                      txt = Tpl.writeStr(txt, a_label)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = dumpStatements(txt, i_statementLst)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpInlineType(in_txt::Tpl.Text, in_a_it::DAE.InlineType) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_it) begin
                  (txt, DAE.AFTER_INDEX_RED_INLINE(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" \\Inline after index reduction\\"))
                    txt
                  end
                  
                  (txt, DAE.NORM_INLINE(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" \\Inline before index reduction\\"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_53(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_var::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_var <| rest)  => begin
                      txt = dumpVar(txt, i_var, false)
                      txt = Tpl.nextIter(txt)
                      txt = lm_53(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVars(txt::Tpl.Text, a_v::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_53(out_txt, a_v)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function fun_55(in_txt::Tpl.Text, in_a_variableAttributesOption::Option{<:DAE.VariableAttributes}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_VariableAttributes::DAE.VariableAttributes
                @match (in_txt, in_a_variableAttributesOption) begin
                  (txt, SOME(i_VariableAttributes))  => begin
                      txt = dumpFinalPrefix(txt, i_VariableAttributes)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_56(in_txt::Tpl.Text, in_a_printTypeDimension::Bool, in_a_dims::DAE.InstDims) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_dims::DAE.InstDims
                @match (in_txt, in_a_printTypeDimension, in_a_dims) begin
                  (txt, false, _)  => begin
                    txt
                  end
                  
                  (txt, _, a_dims)  => begin
                      txt = dumpTypeDimensions(txt, a_dims)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_57(in_txt::Tpl.Text, in_a_binding::Option{<:DAE.Exp}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_exp::DAE.Exp
                @match (in_txt, in_a_binding) begin
                  (txt, SOME(i_exp))  => begin
                      txt = dumpExp(txt, i_exp)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_58(in_txt::Tpl.Text, in_a_variableAttributesOption::Option{<:DAE.VariableAttributes}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_VariableAttributes::DAE.VariableAttributes
                @match (in_txt, in_a_variableAttributesOption) begin
                  (txt, SOME(i_VariableAttributes))  => begin
                      txt = dumpVariableAttributes(txt, i_VariableAttributes)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_59(in_txt::Tpl.Text, in_a_bindingExp::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_bindingExp::Tpl.Text
                @match (in_txt, in_a_bindingExp) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_bindingExp)  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("= "))
                      txt = Tpl.writeText(txt, i_bindingExp)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVar(in_txt::Tpl.Text, in_a_lst::DAE.Element, in_a_printTypeDimension::Bool) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_printTypeDimension::Bool
                  local i_comment::Option{SCode.Comment}
                  local i_binding::Option{DAE.Exp}
                  local i_componentRef::DAE.ComponentRef
                  local i_dims::DAE.InstDims
                  local i_ty::DAE.Type
                  local i_direction::DAE.VarDirection
                  local i_kind::DAE.VarKind
                  local i_parallelism::DAE.VarParallelism
                  local i_protection::DAE.VarVisibility
                  local i_variableAttributesOption::Option{DAE.VariableAttributes}
                  local l_binding__str::Tpl.Text
                  local l_ann__str::Tpl.Text
                  local l_cmt__str::Tpl.Text
                  local l_varAttr::Tpl.Text
                  local l_bindingExp::Tpl.Text
                  local l_varName::Tpl.Text
                  local l_dim__str::Tpl.Text
                  local l_varType::Tpl.Text
                  local l_attr::Tpl.Text
                  local l_varDirection::Tpl.Text
                  local l_varKind::Tpl.Text
                  local l_varParallelism::Tpl.Text
                  local l_varVisibility::Tpl.Text
                  local l_final::Tpl.Text
                @match (in_txt, in_a_lst, in_a_printTypeDimension) begin
                  (txt, DAE.VAR(variableAttributesOption = i_variableAttributesOption, protection = i_protection, parallelism = i_parallelism, kind = i_kind, direction = i_direction, ty = i_ty, dims = i_dims, componentRef = i_componentRef, binding = i_binding, comment = i_comment), a_printTypeDimension)  => begin
                      l_final = fun_55(Tpl.emptyTxt, i_variableAttributesOption)
                      l_varVisibility = dumpVarVisibility(Tpl.emptyTxt, i_protection)
                      l_varParallelism = dumpVarParallelism(Tpl.emptyTxt, i_parallelism)
                      l_varKind = dumpVarKind(Tpl.emptyTxt, i_kind)
                      l_varDirection = dumpVarDirection(Tpl.emptyTxt, i_direction)
                      l_attr = Tpl.emptyTxt
                      (l_varType, l_attr) = dumpType(Tpl.emptyTxt, i_ty, l_attr)
                      l_dim__str = fun_56(Tpl.emptyTxt, a_printTypeDimension, i_dims)
                      l_varName = dumpCref(Tpl.emptyTxt, i_componentRef)
                      l_bindingExp = fun_57(Tpl.emptyTxt, i_binding)
                      l_varAttr = fun_58(Tpl.emptyTxt, i_variableAttributesOption)
                      l_cmt__str = dumpCommentOpt(Tpl.emptyTxt, i_comment)
                      l_ann__str = dumpCompAnnotation(Tpl.emptyTxt, i_comment)
                      l_binding__str = fun_59(Tpl.emptyTxt, l_bindingExp)
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeText(txt, l_varVisibility)
                      txt = Tpl.writeText(txt, l_final)
                      txt = Tpl.writeText(txt, l_varParallelism)
                      txt = Tpl.writeText(txt, l_varKind)
                      txt = Tpl.writeText(txt, l_varDirection)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeText(txt, l_varType)
                      txt = Tpl.writeText(txt, l_dim__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeText(txt, l_varName)
                      txt = Tpl.writeText(txt, l_attr)
                      txt = Tpl.writeText(txt, l_varAttr)
                      txt = Tpl.writeText(txt, l_binding__str)
                      txt = Tpl.writeText(txt, l_cmt__str)
                      txt = Tpl.writeText(txt, l_ann__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFinalPrefix(in_txt::Tpl.Text, in_a_varAttr::DAE.VariableAttributes) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_varAttr) begin
                  (txt, DAE.VAR_ATTR_REAL(finalPrefix = SOME(true)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" final"))
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_INT(finalPrefix = SOME(true)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" final"))
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_BOOL(finalPrefix = SOME(true)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" final"))
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_STRING(finalPrefix = SOME(true)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" final"))
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_ENUMERATION(finalPrefix = SOME(true)))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" final"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarVisibility(in_txt::Tpl.Text, in_a_protection::DAE.VarVisibility) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_protection) begin
                  (txt, DAE.PROTECTED(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" protected"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarParallelism(in_txt::Tpl.Text, in_a_parallelism::DAE.VarParallelism) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_parallelism) begin
                  (txt, DAE.PARGLOBAL(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" parglobal"))
                    txt
                  end
                  
                  (txt, DAE.PARLOCAL(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" parlocal"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarKind(in_txt::Tpl.Text, in_a_kind::DAE.VarKind) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_kind) begin
                  (txt, DAE.CONST(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" constant"))
                    txt
                  end
                  
                  (txt, DAE.PARAM(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" parameter"))
                    txt
                  end
                  
                  (txt, DAE.DISCRETE(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" discrete"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarDirection(in_txt::Tpl.Text, in_a_direction::DAE.VarDirection) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_direction) begin
                  (txt, DAE.INPUT(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" input"))
                    txt
                  end
                  
                  (txt, DAE.OUTPUT(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" output"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_66(in_txt::Tpl.Text, in_items::List{<:String}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{String}
                  local i_it::String
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_it <| rest)  => begin
                      txt = Tpl.writeStr(txt, i_it)
                      txt = Tpl.nextIter(txt)
                      txt = lm_66(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpType(in_txt::Tpl.Text, in_a_ty::DAE.Type, in_a_attributes::Tpl.Text) ::Tuple{Tpl.Text, Tpl.Text} 
              local out_a_attributes::Tpl.Text
              local out_txt::Tpl.Text

              (out_txt, out_a_attributes) = begin
                  local txt::Tpl.Text
                  local a_attributes::Tpl.Text
                  local i_path::Absyn.Path
                  local i_name::String
                  local i_types::List{DAE.Type}
                  local i_complexType::DAE.Type
                  local i_complexClassType::ClassInf.SMNode
                  local i_rname::Absyn.Path
                  local i_dims::DAE.Dimensions
                  local i_ty::DAE.Type
                  local i_names::List{String}
                  local i_varLst::List{DAE.Var}
                  local ret_2::Absyn.Path
                  local txt_1::Tpl.Text
                  local l_lit__str::Tpl.Text
                @match (in_txt, in_a_ty, in_a_attributes) begin
                  (txt, DAE.T_INTEGER(varLst = i_varLst), a_attributes)  => begin
                      a_attributes = dumpVarAttributes(a_attributes, i_varLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Integer"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_REAL(varLst = i_varLst), a_attributes)  => begin
                      a_attributes = dumpVarAttributes(a_attributes, i_varLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Real"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_STRING(varLst = i_varLst), a_attributes)  => begin
                      a_attributes = dumpVarAttributes(a_attributes, i_varLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("String"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_BOOL(varLst = i_varLst), a_attributes)  => begin
                      a_attributes = dumpVarAttributes(a_attributes, i_varLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Boolean"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_CLOCK(varLst = i_varLst), a_attributes)  => begin
                      a_attributes = dumpVarAttributes(a_attributes, i_varLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Clock"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_ENUMERATION(names = i_names), a_attributes)  => begin
                      l_lit__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_lit__str = lm_66(l_lit__str, i_names)
                      l_lit__str = Tpl.popIter(l_lit__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("enumeration("))
                      txt = Tpl.writeText(txt, l_lit__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_ARRAY(ty = i_ty, dims = i_dims), a_attributes)  => begin
                      txt_1 = dumpDimensions(Tpl.emptyTxt, i_dims)
                      (txt, a_attributes) = dumpArrayType(txt, i_ty, Tpl.textString(txt_1), a_attributes)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = i_rname)), a_attributes)  => begin
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_rname)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_COMPLEX(complexClassType = i_complexClassType), a_attributes)  => begin
                      ret_2 = ClassInf.getStateName(i_complexClassType)
                      txt = AbsynDumpTpl.dumpPath(txt, ret_2)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_SUBTYPE_BASIC(complexType = i_complexType), a_attributes)  => begin
                      (txt, a_attributes) = dumpType(txt, i_complexType, a_attributes)
                    (txt, a_attributes)
                  end
                  
                  (txt, i_ty && DAE.T_FUNCTION(funcArg = _), a_attributes)  => begin
                      txt = dumpFunctionType(txt, i_ty)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_TUPLE(types = i_types), a_attributes)  => begin
                      txt = dumpTupleType(txt, i_types, "(", ")")
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METATUPLE(types = i_types), a_attributes)  => begin
                      txt = dumpTupleType(txt, i_types, "tuple<", ">")
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METALIST(ty = i_ty), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("list<"))
                      (txt, a_attributes) = dumpType(txt, i_ty, a_attributes)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METAARRAY(ty = i_ty), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("array<"))
                      (txt, a_attributes) = dumpType(txt, i_ty, a_attributes)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METAPOLYMORPHIC(name = i_name), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("polymorphic<"))
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METAUNIONTYPE(path = i_path), a_attributes)  => begin
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METARECORD(path = i_path), a_attributes)  => begin
                      txt = AbsynDumpTpl.dumpPathNoQual(txt, i_path)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METABOXED(ty = i_ty), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("#"))
                      (txt, a_attributes) = dumpType(txt, i_ty, a_attributes)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METAOPTION(ty = DAE.T_UNKNOWN(__)), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Option<Any>"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METAOPTION(ty = i_ty), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Option<"))
                      (txt, a_attributes) = dumpType(txt, i_ty, a_attributes)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(">"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_METATYPE(ty = i_ty), a_attributes)  => begin
                      (txt, a_attributes) = dumpType(txt, i_ty, a_attributes)
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_NORETCALL(__), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_NORETCALL#"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_UNKNOWN(__), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_UNKNOWN#"))
                    (txt, a_attributes)
                  end
                  
                  (txt, DAE.T_ANYTYPE(anyClassType = _), a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("#T_ANYTYPE#"))
                    (txt, a_attributes)
                  end
                  
                  (txt, _, a_attributes)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("DAEDumpTpl.dumpType: Not yet implemented"))
                    (txt, a_attributes)
                  end
                end
              end
          (out_txt, out_a_attributes)
        end

        function fun_68(in_txt::Tpl.Text, in_a_dims__accum::String, in_a_dims__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_dims__str::Tpl.Text
                  local i_dims__accum::String
                @match (in_txt, in_a_dims__accum, in_a_dims__str) begin
                  (txt, "", a_dims__str)  => begin
                      txt = Tpl.writeText(txt, a_dims__str)
                    txt
                  end
                  
                  (txt, i_dims__accum, a_dims__str)  => begin
                      txt = Tpl.writeStr(txt, i_dims__accum)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                      txt = Tpl.writeText(txt, a_dims__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_69(in_txt::Tpl.Text, in_a_dims__accum::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_dims__accum::String
                @match (in_txt, in_a_dims__accum) begin
                  (txt, "")  => begin
                    txt
                  end
                  
                  (txt, i_dims__accum)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                      txt = Tpl.writeStr(txt, i_dims__accum)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpArrayType(in_txt::Tpl.Text, in_a_ty::DAE.Type, in_a_dims__accum::String, in_a_attributes::Tpl.Text) ::Tuple{Tpl.Text, Tpl.Text} 
              local out_a_attributes::Tpl.Text
              local out_txt::Tpl.Text

              (out_txt, out_a_attributes) = begin
                  local txt::Tpl.Text
                  local a_dims__accum::String
                  local a_attributes::Tpl.Text
                  local i_ty::DAE.Type
                  local i_dims::DAE.Dimensions
                  local l_ty__str::Tpl.Text
                  local l_dims__accum__str::Tpl.Text
                  local l_dims__str::Tpl.Text
                @match (in_txt, in_a_ty, in_a_dims__accum, in_a_attributes) begin
                  (txt, DAE.T_ARRAY(dims = i_dims, ty = i_ty), a_dims__accum, a_attributes)  => begin
                      l_dims__str = dumpDimensions(Tpl.emptyTxt, i_dims)
                      l_dims__accum__str = fun_68(Tpl.emptyTxt, a_dims__accum, l_dims__str)
                      (txt, a_attributes) = dumpArrayType(txt, i_ty, Tpl.textString(l_dims__accum__str), a_attributes)
                    (txt, a_attributes)
                  end
                  
                  (txt, i_ty, a_dims__accum, a_attributes)  => begin
                      (l_ty__str, a_attributes) = dumpType(Tpl.emptyTxt, i_ty, a_attributes)
                      l_dims__str = fun_69(Tpl.emptyTxt, a_dims__accum)
                      txt = Tpl.writeText(txt, l_ty__str)
                      txt = Tpl.writeText(txt, l_dims__str)
                    (txt, a_attributes)
                  end
                end
              end
          (out_txt, out_a_attributes)
        end

        function lm_71(in_txt::Tpl.Text, in_items::List{<:DAE.Type}, in_a_attr::Tpl.Text) ::Tuple{Tpl.Text, Tpl.Text} 
              local out_a_attr::Tpl.Text
              local out_txt::Tpl.Text

              (out_txt, out_a_attr) = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Type}
                  local a_attr::Tpl.Text
                  local i_ty::DAE.Type
                @match (in_txt, in_items, in_a_attr) begin
                  (txt,  nil(), a_attr)  => begin
                    (txt, a_attr)
                  end
                  
                  (txt, i_ty <| rest, a_attr)  => begin
                      (txt, a_attr) = dumpType(txt, i_ty, a_attr)
                      txt = Tpl.nextIter(txt)
                      (txt, a_attr) = lm_71(txt, rest, a_attr)
                    (txt, a_attr)
                  end
                end
              end
          (out_txt, out_a_attr)
        end

        function dumpTupleType(txt::Tpl.Text, a_tys::List{<:DAE.Type}, a_ty__begin::String, a_ty__end::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_attr::Tpl.Text

              l_attr = Tpl.emptyTxt
              out_txt = Tpl.writeStr(txt, a_ty__begin)
              out_txt = Tpl.pushIter(out_txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              (out_txt, l_attr) = lm_71(out_txt, a_tys, l_attr)
              out_txt = Tpl.popIter(out_txt)
              out_txt = Tpl.writeStr(out_txt, a_ty__end)
          out_txt
        end

        function lm_73(in_txt::Tpl.Text, in_items::List{<:DAE.FuncArg}) ::Tpl.Text 
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
                      txt = lm_73(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpFunctionType(in_txt::Tpl.Text, in_a_ty::DAE.Type) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_funcResultType::DAE.Type
                  local i_path::Absyn.Path
                  local i_funcArg::List{DAE.FuncArg}
                  local l_res__str::Tpl.Text
                  local l_attr::Tpl.Text
                  local l_src__str::Tpl.Text
                  local l_args__str::Tpl.Text
                @match (in_txt, in_a_ty) begin
                  (txt, DAE.T_FUNCTION(funcArg = i_funcArg, path = i_path, funcResultType = i_funcResultType))  => begin
                      l_args__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_args__str = lm_73(l_args__str, i_funcArg)
                      l_args__str = Tpl.popIter(l_args__str)
                      l_src__str = AbsynDumpTpl.dumpPath(Tpl.emptyTxt, i_path)
                      l_attr = Tpl.emptyTxt
                      (l_res__str, l_attr) = dumpType(Tpl.emptyTxt, i_funcResultType, l_attr)
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("<function>("))
                      txt = Tpl.writeText(txt, l_args__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(") => "))
                      txt = Tpl.writeText(txt, l_res__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_75(in_txt::Tpl.Text, in_a_defaultBinding::Option{<:DAE.Exp}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_bexp::DAE.Exp
                @match (in_txt, in_a_defaultBinding) begin
                  (txt, SOME(i_bexp))  => begin
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(1))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(":= "))
                      txt = dumpExp(txt, i_bexp)
                      txt = Tpl.popBlock(txt)
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
                  local i_name::String
                  local i_defaultBinding::Option{DAE.Exp}
                  local i_par::DAE.VarParallelism
                  local i_const::DAE.Const
                  local i_ty::DAE.Type
                  local l_binding__str::Tpl.Text
                  local l_p__str::Tpl.Text
                  local l_c__str::Tpl.Text
                  local l_ty__str::Tpl.Text
                  local l_attr::Tpl.Text
                @match (in_txt, in_a_arg) begin
                  (txt, DAE.FUNCARG(ty = i_ty, isConst = i_const, par = i_par, defaultBinding = i_defaultBinding, name = i_name))  => begin
                      l_attr = Tpl.emptyTxt
                      (l_ty__str, l_attr) = dumpType(Tpl.emptyTxt, i_ty, l_attr)
                      l_c__str = dumpConst(Tpl.emptyTxt, i_const)
                      l_p__str = dumpParallelism(Tpl.emptyTxt, i_par)
                      l_binding__str = fun_75(Tpl.emptyTxt, i_defaultBinding)
                      txt = Tpl.writeText(txt, l_ty__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeText(txt, l_c__str)
                      txt = Tpl.writeText(txt, l_p__str)
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.writeText(txt, l_binding__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpConst(in_txt::Tpl.Text, in_a_c::DAE.Const) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_c) begin
                  (txt, DAE.C_PARAM(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("parameter "))
                    txt
                  end
                  
                  (txt, DAE.C_CONST(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("constant "))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpParallelism(in_txt::Tpl.Text, in_a_p::DAE.VarParallelism) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_p) begin
                  (txt, DAE.PARGLOBAL(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("parglobal "))
                    txt
                  end
                  
                  (txt, DAE.PARLOCAL(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("parlocal "))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_79(in_txt::Tpl.Text, in_items::List{<:DAE.Var}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Var}
                  local i_var::DAE.Var
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_var <| rest)  => begin
                      txt = dumpVarAttribute(txt, i_var)
                      txt = Tpl.nextIter(txt)
                      txt = lm_79(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarAttributes(in_txt::Tpl.Text, in_a_literalVarLst::List{<:DAE.Var}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_literalVarLst::List{DAE.Var}
                @match (in_txt, in_a_literalVarLst) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_literalVarLst)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_79(txt, i_literalVarLst)
                      txt = Tpl.popIter(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVarAttribute(in_txt::Tpl.Text, in_a_var::DAE.Var) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_e::DAE.Exp
                  local i_name::DAE.Ident
                @match (in_txt, in_a_var) begin
                  (txt, DAE.TYPES_VAR(binding = DAE.EQBOUND(exp = i_e), name = i_name))  => begin
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" = "))
                      txt = dumpExp(txt, i_e)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_82(in_txt::Tpl.Text, in_items::List{<:DAE.Dimension}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Dimension}
                  local i_dim::DAE.Dimension
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_dim <| rest)  => begin
                      txt = dumpDimension(txt, i_dim)
                      txt = Tpl.nextIter(txt)
                      txt = lm_82(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpDimensions(in_txt::Tpl.Text, in_a_dims::List{<:DAE.Dimension}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_dims::List{DAE.Dimension}
                @match (in_txt, in_a_dims) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_dims)  => begin
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_82(txt, i_dims)
                      txt = Tpl.popIter(txt)
                    txt
                  end
                end
              end
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
                      txt = dumpExp(txt, i_exp)
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

        function smf_85(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_86(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_87(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_88(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_89(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_90(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_91(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_92(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_93(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_94(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_95(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_96(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_97(in_txt::Tpl.Text, in_a_attrs__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_attrs__str::Tpl.Text
                @match (in_txt, in_a_attrs__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_attrs__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, i_attrs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_98(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_99(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_100(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_101(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_102(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_103(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_104(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_105(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_106(in_txt::Tpl.Text, in_a_attrs__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_attrs__str::Tpl.Text
                @match (in_txt, in_a_attrs__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_attrs__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, i_attrs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_107(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_108(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_109(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_110(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_111(in_txt::Tpl.Text, in_a_attrs__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_attrs__str::Tpl.Text
                @match (in_txt, in_a_attrs__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_attrs__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, i_attrs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_112(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_113(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_114(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_115(in_txt::Tpl.Text, in_a_attrs__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_attrs__str::Tpl.Text
                @match (in_txt, in_a_attrs__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_attrs__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, i_attrs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_116(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_117(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_118(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_119(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_120(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function smf_121(in_txt::Tpl.Text, in_it::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_it::Tpl.Text
                @match (in_txt, in_it) begin
                  (txt, i_it)  => begin
                      txt = Tpl.writeText(txt, i_it)
                      txt = Tpl.nextIter(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_122(in_txt::Tpl.Text, in_a_attrs__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_attrs__str::Tpl.Text
                @match (in_txt, in_a_attrs__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_attrs__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, i_attrs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpVariableAttributes(in_txt::Tpl.Text, in_a_variableAttributesOption::DAE.VariableAttributes) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_startOrigin::Option{DAE.Exp}
                  local i_distributionOption::Option{DAE.Distribution}
                  local i_uncertainOption::Option{DAE.Uncertainty}
                  local i_stateSelectOption::Option{DAE.StateSelect}
                  local i_nominal::Option{DAE.Exp}
                  local i_fixed::Option{DAE.Exp}
                  local i_start::Option{DAE.Exp}
                  local i_max::Option{DAE.Exp}
                  local i_min::Option{DAE.Exp}
                  local i_displayUnit::Option{DAE.Exp}
                  local i_unit::Option{DAE.Exp}
                  local i_quantity::Option{DAE.Exp}
                  local l_attrs__str::Tpl.Text
                  local l_so__str::Tpl.Text
                  local l_dist__str::Tpl.Text
                  local l_uncert__str::Tpl.Text
                  local l_statesel__str::Tpl.Text
                  local l_nominal__str::Tpl.Text
                  local l_fixed__str::Tpl.Text
                  local l_start__str::Tpl.Text
                  local l_max__str::Tpl.Text
                  local l_min__str::Tpl.Text
                  local l_displayunit__str::Tpl.Text
                  local l_unit__str::Tpl.Text
                  local l_quantity__str::Tpl.Text
                @match (in_txt, in_a_variableAttributesOption) begin
                  (txt, DAE.VAR_ATTR_REAL(quantity = i_quantity, unit = i_unit, displayUnit = i_displayUnit, min = i_min, max = i_max, start = i_start, fixed = i_fixed, nominal = i_nominal, stateSelectOption = i_stateSelectOption, uncertainOption = i_uncertainOption, distributionOption = i_distributionOption, startOrigin = i_startOrigin))  => begin
                      l_quantity__str = dumpExpAttrOpt(Tpl.emptyTxt, i_quantity, "quantity")
                      l_unit__str = dumpExpAttrOpt(Tpl.emptyTxt, i_unit, "unit")
                      l_displayunit__str = dumpExpAttrOpt(Tpl.emptyTxt, i_displayUnit, "displayUnit")
                      l_min__str = dumpExpAttrOpt(Tpl.emptyTxt, i_min, "min")
                      l_max__str = dumpExpAttrOpt(Tpl.emptyTxt, i_max, "max")
                      l_start__str = dumpExpAttrOpt(Tpl.emptyTxt, i_start, "start")
                      l_fixed__str = dumpExpAttrOpt(Tpl.emptyTxt, i_fixed, "fixed")
                      l_nominal__str = dumpExpAttrOpt(Tpl.emptyTxt, i_nominal, "nominal")
                      l_statesel__str = dumpStateSelectAttrOpt(Tpl.emptyTxt, i_stateSelectOption)
                      l_uncert__str = dumpUncertaintyAttrOpt(Tpl.emptyTxt, i_uncertainOption)
                      l_dist__str = dumpDistributionAttrOpt(Tpl.emptyTxt, i_distributionOption)
                      l_so__str = dumpStartOriginAttrOpt(Tpl.emptyTxt, i_startOrigin)
                      l_attrs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_attrs__str = smf_85(l_attrs__str, l_quantity__str)
                      l_attrs__str = smf_86(l_attrs__str, l_unit__str)
                      l_attrs__str = smf_87(l_attrs__str, l_displayunit__str)
                      l_attrs__str = smf_88(l_attrs__str, l_min__str)
                      l_attrs__str = smf_89(l_attrs__str, l_max__str)
                      l_attrs__str = smf_90(l_attrs__str, l_start__str)
                      l_attrs__str = smf_91(l_attrs__str, l_fixed__str)
                      l_attrs__str = smf_92(l_attrs__str, l_nominal__str)
                      l_attrs__str = smf_93(l_attrs__str, l_statesel__str)
                      l_attrs__str = smf_94(l_attrs__str, l_uncert__str)
                      l_attrs__str = smf_95(l_attrs__str, l_dist__str)
                      l_attrs__str = smf_96(l_attrs__str, l_so__str)
                      l_attrs__str = Tpl.popIter(l_attrs__str)
                      txt = fun_97(txt, l_attrs__str)
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_INT(quantity = i_quantity, min = i_min, max = i_max, start = i_start, fixed = i_fixed, uncertainOption = i_uncertainOption, distributionOption = i_distributionOption, startOrigin = i_startOrigin))  => begin
                      l_quantity__str = dumpExpAttrOpt(Tpl.emptyTxt, i_quantity, "quantity")
                      l_min__str = dumpExpAttrOpt(Tpl.emptyTxt, i_min, "min")
                      l_max__str = dumpExpAttrOpt(Tpl.emptyTxt, i_max, "max")
                      l_start__str = dumpExpAttrOpt(Tpl.emptyTxt, i_start, "start")
                      l_fixed__str = dumpExpAttrOpt(Tpl.emptyTxt, i_fixed, "fixed")
                      l_uncert__str = dumpUncertaintyAttrOpt(Tpl.emptyTxt, i_uncertainOption)
                      l_dist__str = dumpDistributionAttrOpt(Tpl.emptyTxt, i_distributionOption)
                      l_so__str = dumpStartOriginAttrOpt(Tpl.emptyTxt, i_startOrigin)
                      l_attrs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_attrs__str = smf_98(l_attrs__str, l_quantity__str)
                      l_attrs__str = smf_99(l_attrs__str, l_min__str)
                      l_attrs__str = smf_100(l_attrs__str, l_max__str)
                      l_attrs__str = smf_101(l_attrs__str, l_start__str)
                      l_attrs__str = smf_102(l_attrs__str, l_fixed__str)
                      l_attrs__str = smf_103(l_attrs__str, l_uncert__str)
                      l_attrs__str = smf_104(l_attrs__str, l_dist__str)
                      l_attrs__str = smf_105(l_attrs__str, l_so__str)
                      l_attrs__str = Tpl.popIter(l_attrs__str)
                      txt = fun_106(txt, l_attrs__str)
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_BOOL(quantity = i_quantity, start = i_start, fixed = i_fixed, startOrigin = i_startOrigin))  => begin
                      l_quantity__str = dumpExpAttrOpt(Tpl.emptyTxt, i_quantity, "quantity")
                      l_start__str = dumpExpAttrOpt(Tpl.emptyTxt, i_start, "start")
                      l_fixed__str = dumpExpAttrOpt(Tpl.emptyTxt, i_fixed, "fixed")
                      l_so__str = dumpStartOriginAttrOpt(Tpl.emptyTxt, i_startOrigin)
                      l_attrs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_attrs__str = smf_107(l_attrs__str, l_quantity__str)
                      l_attrs__str = smf_108(l_attrs__str, l_start__str)
                      l_attrs__str = smf_109(l_attrs__str, l_fixed__str)
                      l_attrs__str = smf_110(l_attrs__str, l_so__str)
                      l_attrs__str = Tpl.popIter(l_attrs__str)
                      txt = fun_111(txt, l_attrs__str)
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_STRING(quantity = i_quantity, start = i_start, startOrigin = i_startOrigin))  => begin
                      l_quantity__str = dumpExpAttrOpt(Tpl.emptyTxt, i_quantity, "quantity")
                      l_start__str = dumpExpAttrOpt(Tpl.emptyTxt, i_start, "start")
                      l_so__str = dumpStartOriginAttrOpt(Tpl.emptyTxt, i_startOrigin)
                      l_attrs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_attrs__str = smf_112(l_attrs__str, l_quantity__str)
                      l_attrs__str = smf_113(l_attrs__str, l_start__str)
                      l_attrs__str = smf_114(l_attrs__str, l_so__str)
                      l_attrs__str = Tpl.popIter(l_attrs__str)
                      txt = fun_115(txt, l_attrs__str)
                    txt
                  end
                  
                  (txt, DAE.VAR_ATTR_ENUMERATION(quantity = i_quantity, min = i_min, max = i_max, start = i_start, fixed = i_fixed, startOrigin = i_startOrigin))  => begin
                      l_quantity__str = dumpExpAttrOpt(Tpl.emptyTxt, i_quantity, "quantity")
                      l_min__str = dumpExpAttrOpt(Tpl.emptyTxt, i_min, "min")
                      l_max__str = dumpExpAttrOpt(Tpl.emptyTxt, i_max, "max")
                      l_start__str = dumpExpAttrOpt(Tpl.emptyTxt, i_start, "start")
                      l_fixed__str = dumpExpAttrOpt(Tpl.emptyTxt, i_fixed, "fixed")
                      l_so__str = dumpStartOriginAttrOpt(Tpl.emptyTxt, i_startOrigin)
                      l_attrs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_attrs__str = smf_116(l_attrs__str, l_quantity__str)
                      l_attrs__str = smf_117(l_attrs__str, l_min__str)
                      l_attrs__str = smf_118(l_attrs__str, l_max__str)
                      l_attrs__str = smf_119(l_attrs__str, l_start__str)
                      l_attrs__str = smf_120(l_attrs__str, l_fixed__str)
                      l_attrs__str = smf_121(l_attrs__str, l_so__str)
                      l_attrs__str = Tpl.popIter(l_attrs__str)
                      txt = fun_122(txt, l_attrs__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpExpAttrOpt(in_txt::Tpl.Text, in_a_exp::Option{<:DAE.Exp}, in_a_attr::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_attr::String
                  local i_e::DAE.Exp
                @match (in_txt, in_a_exp, in_a_attr) begin
                  (txt, SOME(i_e), a_attr)  => begin
                      txt = Tpl.writeStr(txt, a_attr)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" = "))
                      txt = dumpExp(txt, i_e)
                    txt
                  end
                  
                  (txt, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStateSelectAttrOpt(in_txt::Tpl.Text, in_a_stateSelect::Option{<:DAE.StateSelect}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ss::DAE.StateSelect
                @match (in_txt, in_a_stateSelect) begin
                  (txt, SOME(i_ss))  => begin
                      txt = dumpStateSelectAttr(txt, i_ss)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStateSelectAttr(txt::Tpl.Text, a_stateSelect::DAE.StateSelect) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("stateSelect = "))
              out_txt = dumpStateSelect(out_txt, a_stateSelect)
          out_txt
        end

        function dumpStateSelect(in_txt::Tpl.Text, in_a_stateSelect::DAE.StateSelect) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_stateSelect) begin
                  (txt, DAE.NEVER(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("StateSelect.never"))
                    txt
                  end
                  
                  (txt, DAE.AVOID(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("StateSelect.avoid"))
                    txt
                  end
                  
                  (txt, DAE.DEFAULT(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("StateSelect.default"))
                    txt
                  end
                  
                  (txt, DAE.PREFER(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("StateSelect.prefer"))
                    txt
                  end
                  
                  (txt, DAE.ALWAYS(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("StateSelect.always"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpUncertaintyAttrOpt(in_txt::Tpl.Text, in_a_uncertainty::Option{<:DAE.Uncertainty}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_u::DAE.Uncertainty
                @match (in_txt, in_a_uncertainty) begin
                  (txt, SOME(i_u))  => begin
                      txt = dumpUncertaintyAttr(txt, i_u)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpUncertaintyAttr(txt::Tpl.Text, a_uncertainty::DAE.Uncertainty) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("uncertainty = "))
              out_txt = dumpUncertainty(out_txt, a_uncertainty)
          out_txt
        end

        function dumpUncertainty(in_txt::Tpl.Text, in_a_uncertainty::DAE.Uncertainty) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_uncertainty) begin
                  (txt, DAE.GIVEN(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Uncertainty.given"))
                    txt
                  end
                  
                  (txt, DAE.SOUGHT(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Uncertainty.sought"))
                    txt
                  end
                  
                  (txt, DAE.REFINE(__))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Uncertainty.refine"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpDistributionAttrOpt(in_txt::Tpl.Text, in_a_distribution::Option{<:DAE.Distribution}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_d::DAE.Distribution
                @match (in_txt, in_a_distribution) begin
                  (txt, SOME(i_d))  => begin
                      txt = dumpDistributionAttr(txt, i_d)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpDistributionAttr(txt::Tpl.Text, a_distribution::DAE.Distribution) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("distribution = "))
              out_txt = dumpDistribution(out_txt, a_distribution)
          out_txt
        end

        function dumpDistribution(in_txt::Tpl.Text, in_a_distribution::DAE.Distribution) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_paramNames::DAE.Exp
                  local i_params::DAE.Exp
                  local i_name::DAE.Exp
                  local l_paramnames__str::Tpl.Text
                  local l_params__str::Tpl.Text
                  local l_name__str::Tpl.Text
                @match (in_txt, in_a_distribution) begin
                  (txt, DAE.DISTRIBUTION(name = i_name, params = i_params, paramNames = i_paramNames))  => begin
                      l_name__str = dumpExp(Tpl.emptyTxt, i_name)
                      l_params__str = dumpExp(Tpl.emptyTxt, i_params)
                      l_paramnames__str = dumpExp(Tpl.emptyTxt, i_paramNames)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("Distribution(name = "))
                      txt = Tpl.writeText(txt, l_name__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", params = "))
                      txt = Tpl.writeText(txt, l_params__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", paramNames = "))
                      txt = Tpl.writeText(txt, l_paramnames__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_134(in_txt::Tpl.Text, in_mArg::Bool, in_a_startOrigin::Option{<:DAE.Exp}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_startOrigin::Option{DAE.Exp}
                @match (in_txt, in_mArg, in_a_startOrigin) begin
                  (txt, false, _)  => begin
                    txt
                  end
                  
                  (txt, _, a_startOrigin)  => begin
                      txt = dumpExpAttrOpt(txt, a_startOrigin, "startOrigin")
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStartOriginAttrOpt(txt::Tpl.Text, a_startOrigin::Option{<:DAE.Exp}) ::Tpl.Text 
              local out_txt::Tpl.Text

              local ret_0::Bool

              ret_0 = Config.showStartOrigin()
              out_txt = fun_134(txt, ret_0, a_startOrigin)
          out_txt
        end

        function fun_136(in_txt::Tpl.Text, in_mArg::Bool, in_a_componentRef::DAE.ComponentRef, in_a_subscriptLst::List{<:DAE.Subscript}, in_a_ident::DAE.Ident) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_componentRef::DAE.ComponentRef
                  local a_subscriptLst::List{DAE.Subscript}
                  local a_ident::DAE.Ident
                @match (in_txt, in_mArg, in_a_componentRef, in_a_subscriptLst, in_a_ident) begin
                  (txt, false, a_componentRef, a_subscriptLst, a_ident)  => begin
                      txt = Tpl.writeStr(txt, a_ident)
                      txt = dumpSubscripts(txt, a_subscriptLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("."))
                      txt = dumpCref(txt, a_componentRef)
                    txt
                  end
                  
                  (txt, _, a_componentRef, a_subscriptLst, a_ident)  => begin
                      txt = Tpl.writeStr(txt, a_ident)
                      txt = dumpSubscripts(txt, a_subscriptLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("__"))
                      txt = dumpCref(txt, a_componentRef)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCref(in_txt::Tpl.Text, in_a_c::DAE.ComponentRef) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_componentRef::DAE.ComponentRef
                  local i_subscriptLst::List{DAE.Subscript}
                  local i_ident::DAE.Ident
                  local ret_0::Bool
                @match (in_txt, in_a_c) begin
                  (txt, DAE.CREF_QUAL(ident = i_ident, subscriptLst = i_subscriptLst, componentRef = i_componentRef))  => begin
                      ret_0 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                      txt = fun_136(txt, ret_0, i_componentRef, i_subscriptLst, i_ident)
                    txt
                  end
                  
                  (txt, DAE.CREF_IDENT(ident = i_ident && "\$DER", subscriptLst = i_subscriptLst))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("der("))
                      txt = Tpl.writeStr(txt, i_ident)
                      txt = dumpSubscripts(txt, i_subscriptLst)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                  
                  (txt, DAE.CREF_IDENT(ident = i_ident, subscriptLst = i_subscriptLst))  => begin
                      txt = Tpl.writeStr(txt, i_ident)
                      txt = dumpSubscripts(txt, i_subscriptLst)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_138(in_txt::Tpl.Text, in_items::List{<:DAE.Dimension}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Dimension}
                  local i_s::DAE.Dimension
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_s <| rest)  => begin
                      txt = dumpDimension(txt, i_s)
                      txt = Tpl.nextIter(txt)
                      txt = lm_138(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpTypeDimensions(in_txt::Tpl.Text, in_a_dimensionLst::List{<:DAE.Dimension}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_dimensionLst::List{DAE.Dimension}
                  local l_sub__str::Tpl.Text
                @match (in_txt, in_a_dimensionLst) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_dimensionLst)  => begin
                      l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_sub__str = lm_138(l_sub__str, i_dimensionLst)
                      l_sub__str = Tpl.popIter(l_sub__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                      txt = Tpl.writeText(txt, l_sub__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_140(in_txt::Tpl.Text, in_items::List{<:DAE.Subscript}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Subscript}
                  local i_s::DAE.Subscript
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_s <| rest)  => begin
                      txt = dumpSubscript(txt, i_s)
                      txt = Tpl.nextIter(txt)
                      txt = lm_140(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_141(in_txt::Tpl.Text, in_items::List{<:DAE.Subscript}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Subscript}
                  local i_s::DAE.Subscript
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_s <| rest)  => begin
                      txt = dumpSubscript(txt, i_s)
                      txt = Tpl.nextIter(txt)
                      txt = lm_141(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_142(in_txt::Tpl.Text, in_mArg::Bool, in_a_subscriptLst::List{<:DAE.Subscript}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_subscriptLst::List{DAE.Subscript}
                  local l_sub__str::Tpl.Text
                @match (in_txt, in_mArg, in_a_subscriptLst) begin
                  (txt, false, a_subscriptLst)  => begin
                      l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(",")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_sub__str = lm_140(l_sub__str, a_subscriptLst)
                      l_sub__str = Tpl.popIter(l_sub__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("["))
                      txt = Tpl.writeText(txt, l_sub__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("]"))
                    txt
                  end
                  
                  (txt, _, a_subscriptLst)  => begin
                      l_sub__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING("_")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_sub__str = lm_141(l_sub__str, a_subscriptLst)
                      l_sub__str = Tpl.popIter(l_sub__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("_"))
                      txt = Tpl.writeText(txt, l_sub__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpSubscripts(in_txt::Tpl.Text, in_a_subscriptLst::List{<:DAE.Subscript}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_subscriptLst::List{DAE.Subscript}
                  local ret_0::Bool
                @match (in_txt, in_a_subscriptLst) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_subscriptLst)  => begin
                      ret_0 = Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                      txt = fun_142(txt, ret_0, i_subscriptLst)
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
                      txt = dumpExp(txt, i_exp)
                    txt
                  end
                  
                  (txt, DAE.INDEX(exp = i_exp))  => begin
                      txt = dumpExp(txt, i_exp)
                    txt
                  end
                  
                  (txt, DAE.WHOLE_NONEXP(exp = i_exp))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("1:"))
                      txt = dumpExp(txt, i_exp)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_145(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_ineq::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_ineq <| rest)  => begin
                      txt = dumpEquationElement(txt, i_ineq)
                      txt = Tpl.nextIter(txt)
                      txt = lm_145(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpInitialEquationSection(in_txt::Tpl.Text, in_a_ie::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ie::List{DAE.Element}
                @match (in_txt, in_a_ie) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_ie)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE("initial equation\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_145(txt, i_ie)
                      txt = Tpl.popIter(txt)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_147(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_eq::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_eq <| rest)  => begin
                      txt = dumpEquationElement(txt, i_eq)
                      txt = Tpl.nextIter(txt)
                      txt = lm_147(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpEquationSection(in_txt::Tpl.Text, in_a_e::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_e::List{DAE.Element}
                @match (in_txt, in_a_e) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE("equation\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_147(txt, i_e)
                      txt = Tpl.popIter(txt)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpEquationElement(in_txt::Tpl.Text, in_a_lst::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_exp2::DAE.Exp
                  local i_exp1::DAE.Exp
                  local i_level::DAE.Exp
                  local i_message::DAE.Exp
                  local i_condition::DAE.Exp
                  local i_equations3::List{DAE.Element}
                  local i_equations2::List{List{DAE.Element}}
                  local i_condition1::List{DAE.Exp}
                  local i_lst::DAE.Element
                  local i_componentRef::DAE.ComponentRef
                  local i_rhs::DAE.Exp
                  local i_lhs::DAE.Exp
                  local i_array::DAE.Exp
                  local i_cr2::DAE.ComponentRef
                  local i_cr1::DAE.ComponentRef
                  local i_source::DAE.ElementSource
                  local i_scalar::DAE.Exp
                  local i_exp::DAE.Exp
                @match (in_txt, in_a_lst) begin
                  (txt, DAE.EQUATION(exp = i_exp, scalar = i_scalar, source = i_source))  => begin
                      txt = dumpEquation(txt, i_exp, i_scalar, i_source)
                    txt
                  end
                  
                  (txt, DAE.EQUEQUATION(cr1 = i_cr1, cr2 = i_cr2, source = i_source))  => begin
                      txt = dumpEquEquation(txt, i_cr1, i_cr2, i_source)
                    txt
                  end
                  
                  (txt, DAE.ARRAY_EQUATION(exp = i_exp, array = i_array, source = i_source))  => begin
                      txt = dumpEquation(txt, i_exp, i_array, i_source)
                    txt
                  end
                  
                  (txt, DAE.COMPLEX_EQUATION(lhs = i_lhs, rhs = i_rhs, source = i_source))  => begin
                      txt = dumpEquation(txt, i_lhs, i_rhs, i_source)
                    txt
                  end
                  
                  (txt, DAE.DEFINE(componentRef = i_componentRef, exp = i_exp, source = i_source))  => begin
                      txt = dumpDefine(txt, i_componentRef, i_exp, i_source)
                    txt
                  end
                  
                  (txt, i_lst && DAE.WHEN_EQUATION(condition = _))  => begin
                      txt = dumpWhenEquation(txt, i_lst)
                    txt
                  end
                  
                  (txt, i_lst && DAE.FOR_EQUATION(type_ = _))  => begin
                      txt = dumpForEquation(txt, i_lst)
                    txt
                  end
                  
                  (txt, DAE.IF_EQUATION(condition1 = i_condition1, equations2 = i_equations2, equations3 = i_equations3, source = i_source))  => begin
                      txt = dumpIfEquation(txt, i_condition1, i_equations2, i_equations3, i_source)
                    txt
                  end
                  
                  (txt, DAE.ASSERT(condition = i_condition, message = i_message, level = i_level, source = i_source))  => begin
                      txt = dumpAssert(txt, i_condition, i_message, i_level, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_ASSERT(condition = i_condition, message = i_message, level = i_level, source = i_source))  => begin
                      txt = dumpAssert(txt, i_condition, i_message, i_level, i_source)
                    txt
                  end
                  
                  (txt, DAE.TERMINATE(message = i_message, source = i_source))  => begin
                      txt = dumpTerminate(txt, i_message, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_TERMINATE(message = i_message, source = i_source))  => begin
                      txt = dumpTerminate(txt, i_message, i_source)
                    txt
                  end
                  
                  (txt, DAE.REINIT(componentRef = i_componentRef, exp = i_exp, source = i_source))  => begin
                      txt = dumpReinit(txt, i_componentRef, i_exp, i_source)
                    txt
                  end
                  
                  (txt, DAE.NORETCALL(exp = i_exp, source = i_source))  => begin
                      txt = dumpNoRetCall(txt, i_exp, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_NORETCALL(exp = i_exp, source = i_source))  => begin
                      txt = dumpNoRetCall(txt, i_exp, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIALDEFINE(componentRef = i_componentRef, exp = i_exp, source = i_source))  => begin
                      txt = dumpDefine(txt, i_componentRef, i_exp, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_ARRAY_EQUATION(exp = i_exp, array = i_array, source = i_source))  => begin
                      txt = dumpEquation(txt, i_exp, i_array, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_COMPLEX_EQUATION(lhs = i_lhs, rhs = i_rhs, source = i_source))  => begin
                      txt = dumpEquation(txt, i_lhs, i_rhs, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIAL_IF_EQUATION(condition1 = i_condition1, equations2 = i_equations2, equations3 = i_equations3, source = i_source))  => begin
                      txt = dumpIfEquation(txt, i_condition1, i_equations2, i_equations3, i_source)
                    txt
                  end
                  
                  (txt, DAE.INITIALEQUATION(exp1 = i_exp1, exp2 = i_exp2, source = i_source))  => begin
                      txt = dumpEquation(txt, i_exp1, i_exp2, i_source)
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("UNKNOWN EQUATION TYPE"))
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_150(in_txt::Tpl.Text, in_a_lhs::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_lhs::DAE.Exp
                @match (in_txt, in_a_lhs) begin
                  (txt, i_lhs && DAE.IFEXP(expCond = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = dumpExp(txt, i_lhs)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                  
                  (txt, i_lhs)  => begin
                      txt = dumpExp(txt, i_lhs)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpEquation(txt::Tpl.Text, a_lhs::DAE.Exp, a_rhs::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_rhs__str::Tpl.Text
              local l_lhs__str::Tpl.Text

              l_lhs__str = fun_150(Tpl.emptyTxt, a_lhs)
              l_rhs__str = dumpExp(Tpl.emptyTxt, a_rhs)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeText(txt, l_lhs__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(" = "))
              out_txt = Tpl.writeText(out_txt, l_rhs__str)
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function dumpEquEquation(txt::Tpl.Text, a_lhs::DAE.ComponentRef, a_rhs::DAE.ComponentRef, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_rhs__str::Tpl.Text
              local l_lhs__str::Tpl.Text

              l_lhs__str = dumpCref(Tpl.emptyTxt, a_lhs)
              l_rhs__str = dumpCref(Tpl.emptyTxt, a_rhs)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeText(txt, l_lhs__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(" = "))
              out_txt = Tpl.writeText(out_txt, l_rhs__str)
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function dumpDefine(txt::Tpl.Text, a_lhs::DAE.ComponentRef, a_rhs::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_rhs__str::Tpl.Text
              local l_lhs__str::Tpl.Text

              l_lhs__str = dumpCref(Tpl.emptyTxt, a_lhs)
              l_rhs__str = dumpExp(Tpl.emptyTxt, a_rhs)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeText(txt, l_lhs__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(" = "))
              out_txt = Tpl.writeText(out_txt, l_rhs__str)
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function fun_154(in_txt::Tpl.Text, in_a_lvl::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_lvl) begin
                  (txt, DAE.ENUM_LITERAL(index = 2))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", AssertionLevel.warning"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAssert(txt::Tpl.Text, a_cond::DAE.Exp, a_msg::DAE.Exp, a_lvl::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_lvl__str::Tpl.Text
              local l_msg__str::Tpl.Text
              local l_cond__str::Tpl.Text

              l_cond__str = dumpExp(Tpl.emptyTxt, a_cond)
              l_msg__str = dumpExp(Tpl.emptyTxt, a_msg)
              l_lvl__str = fun_154(Tpl.emptyTxt, a_lvl)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("assert("))
              out_txt = Tpl.writeText(out_txt, l_cond__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(", "))
              out_txt = Tpl.writeText(out_txt, l_msg__str)
              out_txt = Tpl.writeText(out_txt, l_lvl__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(")"))
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function dumpTerminate(txt::Tpl.Text, a_msg::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_msg__str::Tpl.Text

              l_msg__str = dumpExp(Tpl.emptyTxt, a_msg)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("terminate("))
              out_txt = Tpl.writeText(out_txt, l_msg__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(")"))
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function dumpReinit(txt::Tpl.Text, a_cref::DAE.ComponentRef, a_exp::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_exp__str::Tpl.Text
              local l_cref__str::Tpl.Text

              l_cref__str = dumpCref(Tpl.emptyTxt, a_cref)
              l_exp__str = dumpExp(Tpl.emptyTxt, a_exp)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeTok(txt, Tpl.ST_STRING("reinit("))
              out_txt = Tpl.writeText(out_txt, l_cref__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(", "))
              out_txt = Tpl.writeText(out_txt, l_exp__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(")"))
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function fun_158(in_txt::Tpl.Text, in_a_call__exp::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                @match (in_txt, in_a_call__exp) begin
                  (txt, DAE.CALL(attr = DAE.CALL_ATTR(tailCall = DAE.TAIL(__))))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("return "))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpNoRetCall(txt::Tpl.Text, a_call__exp::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_tail__str::Tpl.Text
              local l_src__str::Tpl.Text
              local l_call__str::Tpl.Text

              l_call__str = dumpExp(Tpl.emptyTxt, a_call__exp)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              l_tail__str = fun_158(Tpl.emptyTxt, a_call__exp)
              out_txt = Tpl.writeText(txt, l_tail__str)
              out_txt = Tpl.writeText(out_txt, l_call__str)
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function lm_160(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_e::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpEquationElement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_160(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_161(in_txt::Tpl.Text, in_a_elsewhen__::Option{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_el::DAE.Element
                @match (in_txt, in_a_elsewhen__) begin
                  (txt, SOME(i_el))  => begin
                      txt = dumpWhenEquation(txt, i_el)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_162(in_txt::Tpl.Text, in_a_elsewhen__str::Tpl.Text, in_a_src__str::Tpl.Text, in_a_body__str::Tpl.Text, in_a_when__cond__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_src__str::Tpl.Text
                  local a_body__str::Tpl.Text
                  local a_when__cond__str::Tpl.Text
                  local i_elsewhen__str::Tpl.Text
                @match (in_txt, in_a_elsewhen__str, in_a_src__str, in_a_body__str, in_a_when__cond__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()), a_src__str, a_body__str, a_when__cond__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("when "))
                      txt = Tpl.writeText(txt, a_when__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, a_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end when"))
                      txt = Tpl.writeText(txt, a_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, i_elsewhen__str, _, a_body__str, a_when__cond__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("when "))
                      txt = Tpl.writeText(txt, a_when__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, a_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("else"))
                      txt = Tpl.writeText(txt, i_elsewhen__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpWhenEquation(in_txt::Tpl.Text, in_a_lst::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_elsewhen__::Option{DAE.Element}
                  local i_equations::List{DAE.Element}
                  local i_condition::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_elsewhen__str::Tpl.Text
                  local l_body__str::Tpl.Text
                  local l_when__cond__str::Tpl.Text
                @match (in_txt, in_a_lst) begin
                  (txt, DAE.WHEN_EQUATION(condition = i_condition, equations = i_equations, elsewhen_ = i_elsewhen__, source = i_source))  => begin
                      l_when__cond__str = dumpExp(Tpl.emptyTxt, i_condition)
                      l_body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_body__str = lm_160(l_body__str, i_equations)
                      l_body__str = Tpl.popIter(l_body__str)
                      l_elsewhen__str = fun_161(Tpl.emptyTxt, i_elsewhen__)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = fun_162(txt, l_elsewhen__str, l_src__str, l_body__str, l_when__cond__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_164(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_e::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpEquationElement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_164(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpForEquation(in_txt::Tpl.Text, in_a_lst::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_iter::DAE.Ident
                  local i_source::DAE.ElementSource
                  local i_equations::List{DAE.Element}
                  local i_range::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_body__str::Tpl.Text
                  local l_range__str::Tpl.Text
                @match (in_txt, in_a_lst) begin
                  (txt, DAE.FOR_EQUATION(range = i_range, equations = i_equations, source = i_source, iter = i_iter))  => begin
                      l_range__str = dumpExp(Tpl.emptyTxt, i_range)
                      l_body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_body__str = lm_164(l_body__str, i_equations)
                      l_body__str = Tpl.popIter(l_body__str)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("for "))
                      txt = Tpl.writeStr(txt, i_iter)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" in "))
                      txt = Tpl.writeText(txt, l_range__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" loop\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end for"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_166(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_e::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpEquationElement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_166(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_167(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_e::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpEquationElement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_167(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_168(in_txt::Tpl.Text, in_a_else__branch::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_else__branch::List{DAE.Element}
                @match (in_txt, in_a_else__branch) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_else__branch)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE("else\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_167(txt, i_else__branch)
                      txt = Tpl.popIter(txt)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_169(in_txt::Tpl.Text, in_a_branches::List{<:List{<:DAE.Element}}, in_a_src::DAE.ElementSource, in_a_else__branch::List{<:DAE.Element}, in_a_elseif__conds::List{<:DAE.Exp}, in_a_if__cond::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_src::DAE.ElementSource
                  local a_else__branch::List{DAE.Element}
                  local a_elseif__conds::List{DAE.Exp}
                  local a_if__cond::DAE.Exp
                  local i_elseif__branches::List{List{DAE.Element}}
                  local i_if__branch::List{DAE.Element}
                  local l_src__str::Tpl.Text
                  local l_else__str::Tpl.Text
                  local l_elseif__str::Tpl.Text
                  local l_if__branch__str::Tpl.Text
                  local l_if__cond__str::Tpl.Text
                @match (in_txt, in_a_branches, in_a_src, in_a_else__branch, in_a_elseif__conds, in_a_if__cond) begin
                  (txt, i_if__branch <| i_elseif__branches, a_src, a_else__branch, a_elseif__conds, a_if__cond)  => begin
                      l_if__cond__str = dumpExp(Tpl.emptyTxt, a_if__cond)
                      l_if__branch__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_if__branch__str = lm_166(l_if__branch__str, i_if__branch)
                      l_if__branch__str = Tpl.popIter(l_if__branch__str)
                      l_elseif__str = dumpElseIfEquation(Tpl.emptyTxt, a_elseif__conds, i_elseif__branches)
                      l_else__str = fun_168(Tpl.emptyTxt, a_else__branch)
                      l_src__str = dumpSource(Tpl.emptyTxt, a_src)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("if "))
                      txt = Tpl.writeText(txt, l_if__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_if__branch__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeText(txt, l_elseif__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeText(txt, l_else__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end if"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _, _, _, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpIfEquation(in_txt::Tpl.Text, in_a_conds::List{<:DAE.Exp}, in_a_branches::List{<:List{<:DAE.Element}}, in_a_else__branch::List{<:DAE.Element}, in_a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_branches::List{List{DAE.Element}}
                  local a_else__branch::List{DAE.Element}
                  local a_src::DAE.ElementSource
                  local i_elseif__conds::List{DAE.Exp}
                  local i_if__cond::DAE.Exp
                @match (in_txt, in_a_conds, in_a_branches, in_a_else__branch, in_a_src) begin
                  (txt, i_if__cond <| i_elseif__conds, a_branches, a_else__branch, a_src)  => begin
                      txt = fun_169(txt, a_branches, a_src, a_else__branch, i_elseif__conds, i_if__cond)
                    txt
                  end
                  
                  (txt, _, _, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_171(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_e::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpEquationElement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_171(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_172(in_txt::Tpl.Text, in_a_equations::List{<:List{<:DAE.Element}}, in_a_rest__conds::List{<:DAE.Exp}, in_a_cond::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_rest__conds::List{DAE.Exp}
                  local a_cond::DAE.Exp
                  local i_rest__branches::List{List{DAE.Element}}
                  local i_branch::List{DAE.Element}
                  local l_rest__str::Tpl.Text
                  local l_branch__str::Tpl.Text
                  local l_cond__str::Tpl.Text
                @match (in_txt, in_a_equations, in_a_rest__conds, in_a_cond) begin
                  (txt, i_branch <| i_rest__branches, a_rest__conds, a_cond)  => begin
                      l_cond__str = dumpExp(Tpl.emptyTxt, a_cond)
                      l_branch__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_branch__str = lm_171(l_branch__str, i_branch)
                      l_branch__str = Tpl.popIter(l_branch__str)
                      l_rest__str = dumpElseIfEquation(Tpl.emptyTxt, a_rest__conds, i_rest__branches)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("elseif "))
                      txt = Tpl.writeText(txt, l_cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_branch__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeText(txt, l_rest__str)
                    txt
                  end
                  
                  (txt, _, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpElseIfEquation(in_txt::Tpl.Text, in_a_condition1::List{<:DAE.Exp}, in_a_equations::List{<:List{<:DAE.Element}}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_equations::List{List{DAE.Element}}
                  local i_rest__conds::List{DAE.Exp}
                  local i_cond::DAE.Exp
                @match (in_txt, in_a_condition1, in_a_equations) begin
                  (txt, i_cond <| i_rest__conds, a_equations)  => begin
                      txt = fun_172(txt, a_equations, i_rest__conds, i_cond)
                    txt
                  end
                  
                  (txt, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_174(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_alg::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_alg <| rest)  => begin
                      txt = dumpInitialAlgorithm(txt, i_alg)
                      txt = Tpl.nextIter(txt)
                      txt = lm_174(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpInitialAlgorithmSection(txt::Tpl.Text, a_ia::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_174(out_txt, a_ia)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpInitialAlgorithm(in_txt::Tpl.Text, in_a_alg::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_algorithm__::DAE.Algorithm
                @match (in_txt, in_a_alg) begin
                  (txt, DAE.INITIALALGORITHM(algorithm_ = i_algorithm__))  => begin
                      txt = dumpAlgorithm(txt, i_algorithm__, "initial algorithm")
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_177(in_txt::Tpl.Text, in_items::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Element}
                  local i_alg::DAE.Element
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_alg <| rest)  => begin
                      txt = dumpAlgorithmElement(txt, i_alg)
                      txt = Tpl.nextIter(txt)
                      txt = lm_177(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAlgorithmSection(txt::Tpl.Text, a_a::List{<:DAE.Element}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_177(out_txt, a_a)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpAlgorithmElement(in_txt::Tpl.Text, in_a_alg::DAE.Element) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_algorithm__::DAE.Algorithm
                @match (in_txt, in_a_alg) begin
                  (txt, DAE.ALGORITHM(algorithm_ = i_algorithm__))  => begin
                      txt = dumpAlgorithm(txt, i_algorithm__, "algorithm")
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAlgorithm(in_txt::Tpl.Text, in_a_algorithm__::DAE.Algorithm, in_a_header::String) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_header::String
                  local i_statementLst::List{DAE.Statement}
                @match (in_txt, in_a_algorithm__, in_a_header) begin
                  (txt, DAE.ALGORITHM_STMTS(statementLst = i_statementLst), a_header)  => begin
                      txt = Tpl.writeStr(txt, a_header)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = dumpStatements(txt, i_statementLst)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_181(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_stmt::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_stmt <| rest)  => begin
                      txt = dumpStatement(txt, i_stmt)
                      txt = Tpl.nextIter(txt)
                      txt = lm_181(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStatements(txt::Tpl.Text, a_stmts::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
              out_txt = lm_181(out_txt, a_stmts)
              out_txt = Tpl.popIter(out_txt)
          out_txt
        end

        function dumpStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_level::DAE.Exp
                  local i_msg::DAE.Exp
                  local i_cond::DAE.Exp
                  local i_stmt::DAE.Statement
                  local i_source::DAE.ElementSource
                  local i_exp::DAE.Exp
                  local i_exp1::DAE.Exp
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_ASSIGN(exp1 = i_exp1, exp = i_exp, source = i_source))  => begin
                      txt = dumpAssignment(txt, i_exp1, i_exp, i_source)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_TUPLE_ASSIGN(expExpLst = _))  => begin
                      txt = dumpTupleAssignStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_ASSIGN_ARR(lhs = _))  => begin
                      txt = dumpArrayAssignStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_IF(exp = _))  => begin
                      txt = dumpIfStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_FOR(iterIsArray = _))  => begin
                      txt = dumpForStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_WHILE(exp = _))  => begin
                      txt = dumpWhileStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_WHEN(exp = _))  => begin
                      txt = dumpWhenStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, DAE.STMT_ASSERT(cond = i_cond, msg = i_msg, level = i_level, source = i_source))  => begin
                      txt = dumpAssert(txt, i_cond, i_msg, i_level, i_source)
                    txt
                  end
                  
                  (txt, DAE.STMT_TERMINATE(msg = i_msg, source = i_source))  => begin
                      txt = dumpTerminate(txt, i_msg, i_source)
                    txt
                  end
                  
                  (txt, i_stmt && DAE.STMT_REINIT(var = _))  => begin
                      txt = dumpReinitStatement(txt, i_stmt)
                    txt
                  end
                  
                  (txt, DAE.STMT_NORETCALL(exp = i_exp, source = i_source))  => begin
                      txt = dumpNoRetCall(txt, i_exp, i_source)
                    txt
                  end
                  
                  (txt, DAE.STMT_RETURN(source = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("return;"))
                    txt
                  end
                  
                  (txt, DAE.STMT_BREAK(source = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("break;"))
                    txt
                  end
                  
                  (txt, DAE.STMT_CONTINUE(source = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("continue;"))
                    txt
                  end
                  
                  (txt, DAE.STMT_FAILURE(body = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("fail();"))
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = errorMsg(txt, "DAEDump.dumpStatement: Unknown statement.")
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_184(in_txt::Tpl.Text, in_a_lhs::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_lhs::DAE.Exp
                @match (in_txt, in_a_lhs) begin
                  (txt, i_lhs && DAE.IFEXP(expCond = _))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = dumpExp(txt, i_lhs)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                    txt
                  end
                  
                  (txt, i_lhs)  => begin
                      txt = dumpExp(txt, i_lhs)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAssignment(txt::Tpl.Text, a_lhs::DAE.Exp, a_rhs::DAE.Exp, a_src::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_src__str::Tpl.Text
              local l_rhs__str::Tpl.Text
              local l_lhs__str::Tpl.Text

              l_lhs__str = fun_184(Tpl.emptyTxt, a_lhs)
              l_rhs__str = dumpExp(Tpl.emptyTxt, a_rhs)
              l_src__str = dumpSource(Tpl.emptyTxt, a_src)
              out_txt = Tpl.writeText(txt, l_lhs__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(" := "))
              out_txt = Tpl.writeText(out_txt, l_rhs__str)
              out_txt = Tpl.writeText(out_txt, l_src__str)
              out_txt = Tpl.writeTok(out_txt, Tpl.ST_STRING(";"))
          out_txt
        end

        function lm_186(in_txt::Tpl.Text, in_items::List{<:DAE.Exp}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Exp}
                  local i_e::DAE.Exp
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpExp(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_186(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpTupleAssignStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_exp::DAE.Exp
                  local i_expExpLst::List{DAE.Exp}
                  local l_src__str::Tpl.Text
                  local l_rhs__str::Tpl.Text
                  local l_lhs__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_TUPLE_ASSIGN(expExpLst = i_expExpLst, exp = i_exp, source = i_source))  => begin
                      l_lhs__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(", ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_lhs__str = lm_186(l_lhs__str, i_expExpLst)
                      l_lhs__str = Tpl.popIter(l_lhs__str)
                      l_rhs__str = dumpExp(Tpl.emptyTxt, i_exp)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("("))
                      txt = Tpl.writeText(txt, l_lhs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(") := "))
                      txt = Tpl.writeText(txt, l_rhs__str)
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpArrayAssignStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_exp::DAE.Exp
                  local i_lhs::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_rhs__str::Tpl.Text
                  local l_lhs__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_ASSIGN_ARR(lhs = i_lhs, exp = i_exp, source = i_source))  => begin
                      l_lhs__str = dumpExp(Tpl.emptyTxt, i_lhs)
                      l_rhs__str = dumpExp(Tpl.emptyTxt, i_exp)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeText(txt, l_lhs__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" := "))
                      txt = Tpl.writeText(txt, l_rhs__str)
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_189(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_189(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpIfStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_else__::DAE.Else
                  local i_statementLst::List{DAE.Statement}
                  local i_exp::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_else__if__str::Tpl.Text
                  local l_true__branch__str::Tpl.Text
                  local l_if__cond__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_IF(exp = i_exp, statementLst = i_statementLst, else_ = i_else__, source = i_source))  => begin
                      l_if__cond__str = dumpExp(Tpl.emptyTxt, i_exp)
                      l_true__branch__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_true__branch__str = lm_189(l_true__branch__str, i_statementLst)
                      l_true__branch__str = Tpl.popIter(l_true__branch__str)
                      l_else__if__str = dumpElseIfStatements(Tpl.emptyTxt, i_else__)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("if "))
                      txt = Tpl.writeText(txt, l_if__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_true__branch__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeText(txt, l_else__if__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end if"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_191(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_191(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_192(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_192(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpElseIfStatements(in_txt::Tpl.Text, in_a_else__::DAE.Else) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_else__::DAE.Else
                  local i_statementLst::List{DAE.Statement}
                  local i_exp::DAE.Exp
                  local l_else__body__str::Tpl.Text
                  local l_else__str::Tpl.Text
                  local l_elseif__body__str::Tpl.Text
                  local l_elseif__cond__str::Tpl.Text
                @match (in_txt, in_a_else__) begin
                  (txt, DAE.ELSEIF(exp = i_exp, statementLst = i_statementLst, else_ = i_else__))  => begin
                      l_elseif__cond__str = dumpExp(Tpl.emptyTxt, i_exp)
                      l_elseif__body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_elseif__body__str = lm_191(l_elseif__body__str, i_statementLst)
                      l_elseif__body__str = Tpl.popIter(l_elseif__body__str)
                      l_else__str = dumpElseIfStatements(Tpl.emptyTxt, i_else__)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("elseif "))
                      txt = Tpl.writeText(txt, l_elseif__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_elseif__body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeText(txt, l_else__str)
                    txt
                  end
                  
                  (txt, DAE.ELSE(statementLst = i_statementLst))  => begin
                      l_else__body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_else__body__str = lm_192(l_else__body__str, i_statementLst)
                      l_else__body__str = Tpl.popIter(l_else__body__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE("else\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_else__body__str)
                      txt = Tpl.popBlock(txt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_194(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_194(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpForStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_iter::DAE.Ident
                  local i_source::DAE.ElementSource
                  local i_statementLst::List{DAE.Statement}
                  local i_range::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_alg__str::Tpl.Text
                  local l_range__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_FOR(range = i_range, statementLst = i_statementLst, source = i_source, iter = i_iter))  => begin
                      l_range__str = dumpExp(Tpl.emptyTxt, i_range)
                      l_alg__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_alg__str = lm_194(l_alg__str, i_statementLst)
                      l_alg__str = Tpl.popIter(l_alg__str)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("for "))
                      txt = Tpl.writeStr(txt, i_iter)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" in "))
                      txt = Tpl.writeText(txt, l_range__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" loop\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_alg__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end for"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_196(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_196(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpWhileStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_statementLst::List{DAE.Statement}
                  local i_exp::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_body__str::Tpl.Text
                  local l_while__cond::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_WHILE(exp = i_exp, statementLst = i_statementLst, source = i_source))  => begin
                      l_while__cond = dumpExp(Tpl.emptyTxt, i_exp)
                      l_body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_body__str = lm_196(l_body__str, i_statementLst)
                      l_body__str = Tpl.popIter(l_body__str)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("while "))
                      txt = Tpl.writeText(txt, l_while__cond)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" loop\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, l_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end while"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_198(in_txt::Tpl.Text, in_items::List{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{DAE.Statement}
                  local i_e::DAE.Statement
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_e <| rest)  => begin
                      txt = dumpStatement(txt, i_e)
                      txt = Tpl.nextIter(txt)
                      txt = lm_198(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_199(in_txt::Tpl.Text, in_a_elseWhen::Option{<:DAE.Statement}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ew::DAE.Statement
                @match (in_txt, in_a_elseWhen) begin
                  (txt, SOME(i_ew))  => begin
                      txt = dumpWhenStatement(txt, i_ew)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_200(in_txt::Tpl.Text, in_a_elsewhen__str::Tpl.Text, in_a_src__str::Tpl.Text, in_a_body__str::Tpl.Text, in_a_when__cond__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_src__str::Tpl.Text
                  local a_body__str::Tpl.Text
                  local a_when__cond__str::Tpl.Text
                  local i_elsewhen__str::Tpl.Text
                @match (in_txt, in_a_elsewhen__str, in_a_src__str, in_a_body__str, in_a_when__cond__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()), a_src__str, a_body__str, a_when__cond__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("when "))
                      txt = Tpl.writeText(txt, a_when__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, a_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end when"))
                      txt = Tpl.writeText(txt, a_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, i_elsewhen__str, _, a_body__str, a_when__cond__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("when "))
                      txt = Tpl.writeText(txt, a_when__cond__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_LINE(" then\\n"))
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = Tpl.writeText(txt, a_body__str)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("else"))
                      txt = Tpl.writeText(txt, i_elsewhen__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpWhenStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_elseWhen::Option{DAE.Statement}
                  local i_statementLst::List{DAE.Statement}
                  local i_exp::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_elsewhen__str::Tpl.Text
                  local l_body__str::Tpl.Text
                  local l_when__cond__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_WHEN(exp = i_exp, statementLst = i_statementLst, elseWhen = i_elseWhen, source = i_source))  => begin
                      l_when__cond__str = dumpExp(Tpl.emptyTxt, i_exp)
                      l_body__str = Tpl.pushIter(Tpl.emptyTxt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_NEW_LINE()), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      l_body__str = lm_198(l_body__str, i_statementLst)
                      l_body__str = Tpl.popIter(l_body__str)
                      l_elsewhen__str = fun_199(Tpl.emptyTxt, i_elseWhen)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = fun_200(txt, l_elsewhen__str, l_src__str, l_body__str, l_when__cond__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpReinitStatement(in_txt::Tpl.Text, in_a_stmt::DAE.Statement) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_source::DAE.ElementSource
                  local i_value::DAE.Exp
                  local i_var::DAE.Exp
                  local l_src__str::Tpl.Text
                  local l_new__exp__str::Tpl.Text
                  local l_exp__str::Tpl.Text
                @match (in_txt, in_a_stmt) begin
                  (txt, DAE.STMT_REINIT(var = i_var, value = i_value, source = i_source))  => begin
                      l_exp__str = dumpExp(Tpl.emptyTxt, i_var)
                      l_new__exp__str = dumpExp(Tpl.emptyTxt, i_value)
                      l_src__str = dumpSource(Tpl.emptyTxt, i_source)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("reinit("))
                      txt = Tpl.writeText(txt, l_exp__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(", "))
                      txt = Tpl.writeText(txt, l_new__exp__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(")"))
                      txt = Tpl.writeText(txt, l_src__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_203(in_txt::Tpl.Text, in_a_comment::Option{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_co::SCode.Comment
                @match (in_txt, in_a_comment) begin
                  (txt, SOME(i_co))  => begin
                      txt = dumpStateMachineComment(txt, i_co)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStateMachineSection(in_txt::Tpl.Text, in_a_fixedDae::DAEDump.compWithSplitElements) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_spltElems::DAEDump.splitElements
                  local i_name::String
                  local i_comment::Option{SCode.Comment}
                  local l_kind::Tpl.Text
                @match (in_txt, in_a_fixedDae) begin
                  (txt, DAEDump.COMP_WITH_SPLIT(comment = i_comment, name = i_name, spltElems = i_spltElems))  => begin
                      l_kind = fun_203(Tpl.emptyTxt, i_comment)
                      txt = Tpl.writeText(txt, l_kind)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.pushBlock(txt, Tpl.BT_INDENT(2))
                      txt = dumpCompStream(txt, i_spltElems)
                      txt = Tpl.softNewLine(txt)
                      txt = Tpl.popBlock(txt)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("end "))
                      txt = Tpl.writeStr(txt, i_name)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                      txt = Tpl.writeTok(txt, Tpl.ST_NEW_LINE())
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_205(in_txt::Tpl.Text, in_a_comment::Option{<:String}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_co::String
                @match (in_txt, in_a_comment) begin
                  (txt, SOME(i_co))  => begin
                      txt = Tpl.writeStr(txt, i_co)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpStateMachineComment(in_txt::Tpl.Text, in_a_cmt::SCode.Comment) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_comment::Option{String}
                  local l_kind__str::Tpl.Text
                @match (in_txt, in_a_cmt) begin
                  (txt, SCode.COMMENT(comment = i_comment))  => begin
                      l_kind__str = fun_205(Tpl.emptyTxt, i_comment)
                      txt = Tpl.writeText(txt, l_kind__str)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpExp(txt::Tpl.Text, a_exp::DAE.Exp) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = ExpressionDumpTpl.dumpExp(txt, a_exp, "\\")
          out_txt
        end

        function fun_208(in_txt::Tpl.Text, in_a_cmt__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt__str::Tpl.Text
                @match (in_txt, in_a_cmt__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_cmt__str)  => begin
                      txt = Tpl.writeText(txt, i_cmt__str)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(";"))
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpClassAnnotation(txt::Tpl.Text, a_comment::Option{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_cmt__str::Tpl.Text

              l_cmt__str = dumpCommentAnnotation(Tpl.emptyTxt, a_comment)
              out_txt = fun_208(txt, l_cmt__str)
          out_txt
        end

        function fun_210(in_txt::Tpl.Text, in_a_cmt__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt__str::Tpl.Text
                @match (in_txt, in_a_cmt__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_cmt__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeText(txt, i_cmt__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCompAnnotation(txt::Tpl.Text, a_comment::Option{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              local l_cmt__str::Tpl.Text

              l_cmt__str = dumpCommentAnnotation(Tpl.emptyTxt, a_comment)
              out_txt = fun_210(txt, l_cmt__str)
          out_txt
        end

        function dumpCommentAnnotation(in_txt::Tpl.Text, in_a_comment::Option{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt::SCode.Comment
                @match (in_txt, in_a_comment) begin
                  (txt, SOME(i_cmt))  => begin
                      txt = dumpCommentAnnotationNoOpt(txt, i_cmt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCommentAnnotationNoOpt(in_txt::Tpl.Text, in_a_comment::SCode.Comment) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ann::SCode.Annotation
                @match (in_txt, in_a_comment) begin
                  (txt, SCode.COMMENT(annotation_ = SOME(i_ann)))  => begin
                      txt = dumpAnnotation(txt, i_ann)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCommentOpt(in_txt::Tpl.Text, in_a_comment::Option{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt::SCode.Comment
                @match (in_txt, in_a_comment) begin
                  (txt, SOME(i_cmt))  => begin
                      txt = dumpComment(txt, i_cmt)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpComment(in_txt::Tpl.Text, in_a_comment::SCode.Comment) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_comment::Option{String}
                @match (in_txt, in_a_comment) begin
                  (txt, SCode.COMMENT(comment = i_comment))  => begin
                      txt = dumpCommentStr(txt, i_comment)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpCommentStr(in_txt::Tpl.Text, in_a_comment::Option{<:String}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_cmt::String
                  local ret_0::String
                @match (in_txt, in_a_comment) begin
                  (txt, SOME(i_cmt))  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING(" "))
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("\\"))
                      ret_0 = System.escapedString(i_cmt, false)
                      txt = Tpl.writeStr(txt, ret_0)
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("\\"))
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAnnotationOpt(in_txt::Tpl.Text, in_a_annotation::Option{<:SCode.Annotation}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ann::SCode.Annotation
                @match (in_txt, in_a_annotation) begin
                  (txt, SOME(i_ann))  => begin
                      txt = dumpAnnotation(txt, i_ann)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_218(in_txt::Tpl.Text, in_a_ann__str::Tpl.Text) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ann__str::Tpl.Text
                @match (in_txt, in_a_ann__str) begin
                  (txt, Tpl.MEM_TEXT(tokens =  nil()))  => begin
                    txt
                  end
                  
                  (txt, i_ann__str)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("annotation"))
                      txt = Tpl.writeText(txt, i_ann__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_219(in_txt::Tpl.Text, in_mArg::Bool, in_a_ann__mod::SCode.Mod) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_ann__mod::SCode.Mod
                  local ret_1::SCode.Mod
                  local l_ann__str::Tpl.Text
                @match (in_txt, in_mArg, in_a_ann__mod) begin
                  (txt, false, _)  => begin
                    txt
                  end
                  
                  (txt, _, a_ann__mod)  => begin
                      ret_1 = DAEDump.filterStructuralMods(a_ann__mod)
                      l_ann__str = SCodeDumpTpl.dumpModifier(Tpl.emptyTxt, ret_1, SCodeDump.defaultOptions)
                      txt = fun_218(txt, l_ann__str)
                    txt
                  end
                end
              end
          out_txt
        end

        function fun_220(in_txt::Tpl.Text, in_mArg::Bool, in_a_ann__mod::SCode.Mod) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local a_ann__mod::SCode.Mod
                  local ret_0::Bool
                @match (in_txt, in_mArg, in_a_ann__mod) begin
                  (txt, false, a_ann__mod)  => begin
                      ret_0 = Config.showStructuralAnnotations()
                      txt = fun_219(txt, ret_0, a_ann__mod)
                    txt
                  end
                  
                  (txt, _, a_ann__mod)  => begin
                      txt = Tpl.writeTok(txt, Tpl.ST_STRING("annotation"))
                      txt = SCodeDumpTpl.dumpModifier(txt, a_ann__mod, SCodeDump.defaultOptions)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpAnnotation(in_txt::Tpl.Text, in_a_annotation::SCode.Annotation) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_ann__mod::SCode.Mod
                  local ret_0::Bool
                @match (in_txt, in_a_annotation) begin
                  (txt, SCode.ANNOTATION(modification = i_ann__mod))  => begin
                      ret_0 = Config.showAnnotations()
                      txt = fun_220(txt, ret_0, i_ann__mod)
                    txt
                  end
                  
                  (txt, _)  => begin
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpPathLastIndent(in_txt::Tpl.Text, in_a_path::Absyn.Path) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_name::Absyn.Ident
                  local i_path::Absyn.Path
                @match (in_txt, in_a_path) begin
                  (txt, Absyn.FULLYQUALIFIED(path = i_path))  => begin
                      txt = dumpPathLastIndent(txt, i_path)
                    txt
                  end
                  
                  (txt, Absyn.QUALIFIED(path = i_path))  => begin
                      txt = dumpPathLastIndent(txt, i_path)
                    txt
                  end
                  
                  (txt, Absyn.IDENT(name = i_name))  => begin
                      txt = Tpl.writeStr(txt, i_name)
                    txt
                  end
                  
                  (txt, _)  => begin
                      txt = errorMsg(txt, "dumpPathLastIndent: Unknown path.")
                    txt
                  end
                end
              end
          out_txt
        end

        function lm_223(in_txt::Tpl.Text, in_items::List{<:SCode.Comment}) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local rest::List{SCode.Comment}
                  local i_c::SCode.Comment
                @match (in_txt, in_items) begin
                  (txt,  nil())  => begin
                    txt
                  end
                  
                  (txt, i_c <| rest)  => begin
                      txt = dumpComment(txt, i_c)
                      txt = Tpl.nextIter(txt)
                      txt = lm_223(txt, rest)
                    txt
                  end
                end
              end
          out_txt
        end

        function dumpSource(in_txt::Tpl.Text, in_a_source::DAE.ElementSource) ::Tpl.Text 
              local out_txt::Tpl.Text

              out_txt = begin
                  local txt::Tpl.Text
                  local i_comment::List{SCode.Comment}
                @match (in_txt, in_a_source) begin
                  (txt, DAE.SOURCE(comment = i_comment))  => begin
                      txt = Tpl.pushIter(txt, Tpl.ITER_OPTIONS(0, NONE(), SOME(Tpl.ST_STRING(" + ")), 0, 0, Tpl.ST_NEW_LINE(), 0, Tpl.ST_NEW_LINE()))
                      txt = lm_223(txt, i_comment)
                      txt = Tpl.popIter(txt)
                    txt
                  end
                  
                  (txt, _)  => begin
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

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
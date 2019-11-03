  module DAEDump


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    Type_a = Any

    FuncTypeType_aToString = Function

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

        import DAE

        import Graphviz

        import IOStream

        import SCode
         #=  protected imports
         =#

        import ComponentReference

        import Config

        import DAEUtil

        compWithSplitElements = DAEUtil.compWithSplitElements
        functionList = DAEUtil.functionList
        splitElements = DAEUtil.splitElements

        import ElementSource

        import Error

        import Print

        import Util

        import Expression

        import ExpressionDump

        import Absyn

        import AbsynUtil

        import Dump

        import ValuesUtil

        import Values

        import Types

        import ClassInf

        import SCodeDump
        import SCodeUtil

        import ListUtil

        import Flags

        import DAEDumpTpl

        import Tpl

        import System

         #= This function prints the DAE in the standard output format to the Print buffer.
          For printing to the stdout use print(dumpStr(dae)) instead. =#
        function dump(dae::DAE.DAElist, functionTree::DAE.FunctionTree)
              _ = begin
                  local daelist::List{DAE.Element}
                @match (dae, functionTree) begin
                  (DAE.DAE(daelist), _)  => begin
                      ListUtil.map_0(sortFunctions(DAEUtil.getFunctionList(functionTree)), dumpFunction)
                      ListUtil.map_0(daelist, dumpExtObjectClass)
                      ListUtil.map_0(daelist, dumpCompElement)
                    ()
                  end
                end
              end
        end

         #= return all function names in a string  (comma separated) =#
        function dumpFunctionNamesStr(funcs::DAE.FunctionTree) ::String
              local str::String

              str = stringDelimitList(ListUtil.map(sortFunctions(DAEUtil.getFunctionList(funcs)), functionNameStr), ",")
          str
        end

         #= return the name of a function, if element is not function return  empty string =#
        function functionNameStr(inElement::DAE.Function) ::String
              local res::String

              res = begin
                  local fpath::Absyn.Path
                @matchcontinue inElement begin
                  DAE.FUNCTION(path = fpath)  => begin
                      res = AbsynUtil.pathStringNoQual(fpath)
                    res
                  end

                  DAE.RECORD_CONSTRUCTOR(path = fpath)  => begin
                      res = AbsynUtil.pathStringNoQual(fpath)
                    res
                  end

                  _  => begin
                      ""
                  end
                end
              end
          res
        end

         #= sorts the functions and record constructors in alphabetical order =#
        function sortFunctions(funcs::List{<:DAE.Function}) ::List{DAE.Function}
              local sortedFuncs::List{DAE.Function}

              sortedFuncs = ListUtil.sort(funcs, funcGreaterThan)
          sortedFuncs
        end

         #= sorting function for two DAE.Element that are functions or record constuctors =#
        function funcGreaterThan(func1::DAE.Function, func2::DAE.Function) ::Bool
              local res::Bool

              res = begin
                @matchcontinue (func1, func2) begin
                  (_, _)  => begin
                      res = stringCompare(functionNameStr(func1), functionNameStr(func2)) > 0
                    res
                  end

                  _  => begin
                      true
                  end
                end
              end
          res
        end

         #=
        Author bz  printOperator
        Dump operator to a string. =#
        function dumpOperatorString(op::DAE.Operator) ::String
              local str::String

              str = begin
                  local p::Absyn.Path
                  local ty::DAE.Type
                @match op begin
                  DAE.ADD(__)  => begin
                    " ADD "
                  end

                  DAE.SUB(__)  => begin
                    " SUB "
                  end

                  DAE.MUL(__)  => begin
                    " MUL "
                  end

                  DAE.DIV(__)  => begin
                    " DIV "
                  end

                  DAE.POW(__)  => begin
                    " POW "
                  end

                  DAE.UMINUS(__)  => begin
                    " UMINUS "
                  end

                  DAE.UMINUS_ARR(__)  => begin
                    " UMINUS_ARR "
                  end

                  DAE.ADD_ARR(__)  => begin
                    " ADD_ARR "
                  end

                  DAE.SUB_ARR(__)  => begin
                    " SUB_ARR "
                  end

                  DAE.MUL_ARR(__)  => begin
                    " MUL_ARR "
                  end

                  DAE.DIV_ARR(__)  => begin
                    " DIV_ARR "
                  end

                  DAE.MUL_ARRAY_SCALAR(__)  => begin
                    " MUL_ARRAY_SCALAR "
                  end

                  DAE.ADD_ARRAY_SCALAR(__)  => begin
                    " ADD_ARRAY_SCALAR "
                  end

                  DAE.SUB_SCALAR_ARRAY(__)  => begin
                    " SUB_SCALAR_ARRAY "
                  end

                  DAE.MUL_SCALAR_PRODUCT(__)  => begin
                    " MUL_SCALAR_PRODUCT "
                  end

                  DAE.MUL_MATRIX_PRODUCT(__)  => begin
                    " MUL_MATRIX_PRODUCT "
                  end

                  DAE.DIV_ARRAY_SCALAR(__)  => begin
                    " DIV_ARRAY_SCALAR "
                  end

                  DAE.DIV_SCALAR_ARRAY(__)  => begin
                    " DIV_SCALAR_ARRAY "
                  end

                  DAE.POW_ARRAY_SCALAR(__)  => begin
                    " POW_ARRAY_SCALAR "
                  end

                  DAE.POW_SCALAR_ARRAY(__)  => begin
                    " POW_SCALAR_ARRAY "
                  end

                  DAE.POW_ARR(__)  => begin
                    " POW_ARR "
                  end

                  DAE.POW_ARR2(__)  => begin
                    " POW_ARR2 "
                  end

                  DAE.OR(_)  => begin
                    " OR "
                  end

                  DAE.AND(_)  => begin
                    " AND "
                  end

                  DAE.NOT(_)  => begin
                    " NOT "
                  end

                  DAE.LESSEQ(__)  => begin
                    " LESSEQ "
                  end

                  DAE.GREATER(__)  => begin
                    " GREATER "
                  end

                  DAE.GREATEREQ(__)  => begin
                    " GREATEREQ "
                  end

                  DAE.LESS(__)  => begin
                    " LESS "
                  end

                  DAE.EQUAL(__)  => begin
                    " EQUAL "
                  end

                  DAE.NEQUAL(__)  => begin
                    " NEQUAL "
                  end

                  DAE.USERDEFINED(p)  => begin
                    " Userdefined:" + AbsynUtil.pathString(p) + " "
                  end

                  _  => begin
                      " --UNDEFINED-- "
                  end
                end
              end
          str
        end

         #=
        Author bz  printOperator
        Dump operator to a string. =#
        function dumpOperatorSymbol(op::DAE.Operator) ::String
              local str::String

              str = begin
                  local p::Absyn.Path
                @match op begin
                  DAE.ADD(_)  => begin
                    " + "
                  end

                  DAE.SUB(_)  => begin
                    " - "
                  end

                  DAE.MUL(_)  => begin
                    " .* "
                  end

                  DAE.DIV(_)  => begin
                    " / "
                  end

                  DAE.POW(_)  => begin
                    " ^ "
                  end

                  DAE.UMINUS(_)  => begin
                    " - "
                  end

                  DAE.UMINUS_ARR(_)  => begin
                    " - "
                  end

                  DAE.ADD_ARR(_)  => begin
                    " + "
                  end

                  DAE.SUB_ARR(_)  => begin
                    " - "
                  end

                  DAE.MUL_ARR(_)  => begin
                    " .* "
                  end

                  DAE.DIV_ARR(_)  => begin
                    " ./ "
                  end

                  DAE.MUL_ARRAY_SCALAR(_)  => begin
                    " * "
                  end

                  DAE.ADD_ARRAY_SCALAR(_)  => begin
                    " .+ "
                  end

                  DAE.SUB_SCALAR_ARRAY(_)  => begin
                    " .- "
                  end

                  DAE.MUL_SCALAR_PRODUCT(_)  => begin
                    " * "
                  end

                  DAE.MUL_MATRIX_PRODUCT(_)  => begin
                    " * "
                  end

                  DAE.DIV_ARRAY_SCALAR(_)  => begin
                    " / "
                  end

                  DAE.DIV_SCALAR_ARRAY(_)  => begin
                    " ./ "
                  end

                  DAE.POW_ARRAY_SCALAR(_)  => begin
                    " .^ "
                  end

                  DAE.POW_SCALAR_ARRAY(_)  => begin
                    " .^ "
                  end

                  DAE.POW_ARR(_)  => begin
                    " ^ "
                  end

                  DAE.POW_ARR2(_)  => begin
                    " .^ "
                  end

                  DAE.OR(_)  => begin
                    " or "
                  end

                  DAE.AND(_)  => begin
                    " and "
                  end

                  DAE.NOT(_)  => begin
                    " not "
                  end

                  DAE.LESSEQ(_)  => begin
                    " <= "
                  end

                  DAE.GREATER(_)  => begin
                    " > "
                  end

                  DAE.GREATEREQ(_)  => begin
                    " >= "
                  end

                  DAE.LESS(_)  => begin
                    " < "
                  end

                  DAE.EQUAL(_)  => begin
                    " == "
                  end

                  DAE.NEQUAL(_)  => begin
                    " <> "
                  end

                  DAE.USERDEFINED(p)  => begin
                    " Userdefined:" + AbsynUtil.pathString(p) + " "
                  end

                  _  => begin
                      " --UNDEFINED-- "
                  end
                end
              end
          str
        end

         #= Dumps the StartValue for a variable. =#
        function dumpStartValue(inStartValue::DAE.StartValue)
              _ = begin
                  local e::DAE.Exp
                @matchcontinue inStartValue begin
                  SOME(e)  => begin
                      Print.printBuf("(start=")
                      ExpressionDump.printExp(e)
                      Print.printBuf(")")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Dumps the start value for a variable to a string. =#
        function dumpStartValueStr(inStartValue::DAE.StartValue) ::String
              local outString::String

              outString = begin
                  local s::String
                  local res::String
                  local e::DAE.Exp
                @matchcontinue inStartValue begin
                  SOME(e)  => begin
                      s = ExpressionDump.printExpStr(e)
                      res = stringAppendList(list("(start=", s, ")"))
                    res
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= Dumps the external declaration to a string. =#
        function dumpExtDeclStr(inExternalDecl::DAE.ExternalDecl) ::String
              local outString::String

              outString = begin
                  local extargsstr::String
                  local rettystr::String
                  local str::String
                  local id::String
                  local lang::String
                  local extargs::List{DAE.ExtArg}
                  local retty::DAE.ExtArg
                @match inExternalDecl begin
                  DAE.EXTERNALDECL(name = id, args = extargs, returnArg = retty, language = lang)  => begin
                      extargsstr = Dump.getStringList(extargs, dumpExtArgStr, ", ")
                      rettystr = dumpExtArgStr(retty)
                      rettystr = if stringEq(rettystr, "")
                            rettystr
                          else
                            rettystr + " = "
                          end
                      str = stringAppendList(list("external \\", lang, "\\ ", rettystr, id, "(", extargsstr, ");"))
                    str
                  end
                end
              end
          outString
        end

         #= Helper function to dumpExtDeclStr =#
        function dumpExtArgStr(inExtArg::DAE.ExtArg) ::String
              local outString::String

              outString = begin
                  local crstr::String
                  local str::String
                  local dimstr::String
                  local cr::DAE.ComponentRef
                  local ct::SCode.ConnectorType
                  local var::SCode.Variability
                  local dir::Absyn.Direction
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local dim::DAE.Exp
                  local attr::DAE.Attributes
                @match inExtArg begin
                  DAE.NOEXTARG(__)  => begin
                    ""
                  end

                  DAE.EXTARG(componentRef = cr)  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                    crstr
                  end

                  DAE.EXTARGEXP(exp = exp)  => begin
                      crstr = ExpressionDump.printExpStr(exp)
                    crstr
                  end

                  DAE.EXTARGSIZE(componentRef = cr, exp = dim)  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                      dimstr = ExpressionDump.printExpStr(dim)
                      str = stringAppendList(list("size(", crstr, ", ", dimstr, ")"))
                    str
                  end
                end
              end
          outString
        end

         #= Dumps Component elements. =#
        function dumpCompElement(inElement::DAE.Element)
              _ = begin
                  local n::String
                  local l::List{DAE.Element}
                  local c::Option{SCode.Comment}
                @matchcontinue inElement begin
                  DAE.COMP(ident = n, dAElist = l, comment = c)  => begin
                      Print.printBuf("class ")
                      Print.printBuf(n)
                      dumpCommentOption(c)
                      Print.printBuf("\\n")
                      dumpElements(l)
                      Print.printBuf("end ")
                      Print.printBuf(n)
                      Print.printBuf(";\\n")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
               #= /* LS: for non-COMPS, which are only FUNCTIONS at the moment */ =#
        end

         #= Dump elements. =#
        function dumpElements(l::List{<:DAE.Element})
              dumpVars(l, false)
              ListUtil.map_0(l, dumpExtObjectClass)
              Print.printBuf("initial equation\\n")
              ListUtil.map_0(l, dumpInitialEquation)
              Print.printBuf("equation\\n")
              ListUtil.map_0(l, dumpEquation)
              ListUtil.map_0(l, dumpInitialAlgorithm)
              ListUtil.map_0(l, dumpAlgorithm)
              ListUtil.map_0(l, dumpCompElement)
        end

         #= Dump function elements. =#
        function dumpFunctionElements(l::List{<:DAE.Element})
              dumpVars(l, true)
              ListUtil.map_0(l, dumpAlgorithm)
        end

         #= Dump variables to Print buffer. =#
        function dumpVars(lst::List{<:DAE.Element}, printTypeDimension::Bool #= use true here when printing components in functions as these are not vectorized! Otherwise, use false =#)
              local str::String
              local myStream::IOStream.IOStreamType

              myStream = IOStream.create("", IOStream.LIST())
              myStream = dumpVarsStream(lst, printTypeDimension, myStream)
              str = IOStream.string(myStream)
              Print.printBuf(str)
        end

         #= Dump VarKind. =#
        function dumpKind(inVarKind::DAE.VarKind)
              _ = begin
                @match inVarKind begin
                  DAE.CONST(__)  => begin
                      Print.printBuf(" constant  ")
                    ()
                  end

                  DAE.PARAM(__)  => begin
                      Print.printBuf(" parameter ")
                    ()
                  end

                  DAE.DISCRETE(__)  => begin
                      Print.printBuf(" discrete  ")
                    ()
                  end

                  DAE.VARIABLE(__)  => begin
                      Print.printBuf("           ")
                    ()
                  end
                end
              end
        end

         #= Dump VarKind to a string. =#
        function dumpKindStr(inVarKind::DAE.VarKind) ::String
              local outString::String

              outString = begin
                @match inVarKind begin
                  DAE.CONST(__)  => begin
                    "constant "
                  end

                  DAE.PARAM(__)  => begin
                    "parameter "
                  end

                  DAE.DISCRETE(__)  => begin
                    "discrete "
                  end

                  DAE.VARIABLE(__)  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Dump VarDirection. =#
        function dumpDirection(inVarDirection::DAE.VarDirection)
              _ = begin
                @match inVarDirection begin
                  DAE.INPUT(__)  => begin
                      Print.printBuf(" input  ")
                    ()
                  end

                  DAE.OUTPUT(__)  => begin
                      Print.printBuf(" output ")
                    ()
                  end

                  DAE.BIDIR(__)  => begin
                      Print.printBuf("        ")
                    ()
                  end
                end
              end
        end

         #= Dump VarParallelism. =#
        function dumpParallelism(inVarParallelism::DAE.VarParallelism)
              _ = begin
                @match inVarParallelism begin
                  DAE.NON_PARALLEL(__)  => begin
                      Print.printBuf("        ")
                    ()
                  end

                  DAE.PARGLOBAL(__)  => begin
                      Print.printBuf(" parglobal ")
                    ()
                  end

                  DAE.PARLOCAL(__)  => begin
                      Print.printBuf(" parlocal ")
                    ()
                  end
                end
              end
        end

         #= Dump VarDirection to a string =#
        function dumpDirectionStr(inVarDirection::DAE.VarDirection) ::String
              local outString::String

              outString = begin
                @match inVarDirection begin
                  DAE.INPUT(__)  => begin
                    "input "
                  end

                  DAE.OUTPUT(__)  => begin
                    "output "
                  end

                  DAE.BIDIR(__)  => begin
                    ""
                  end
                end
              end
          outString
        end

         #= Dump StateSelect to a string. =#
        function dumpStateSelectStr(inStateSelect::DAE.StateSelect) ::String
              local outString::String

              outString = begin
                @match inStateSelect begin
                  DAE.NEVER(__)  => begin
                    "StateSelect.never"
                  end

                  DAE.AVOID(__)  => begin
                    "StateSelect.avoid"
                  end

                  DAE.PREFER(__)  => begin
                    "StateSelect.prefer"
                  end

                  DAE.ALWAYS(__)  => begin
                    "StateSelect.always"
                  end

                  DAE.DEFAULT(__)  => begin
                    "StateSelect.default"
                  end
                end
              end
          outString
        end

         #=
          Author: Daniel Hedberg 2011-01

          Dump Uncertainty to a string.
         =#
        function dumpUncertaintyStr(uncertainty::DAE.Uncertainty) ::String
              local out::String

              out = begin
                @match uncertainty begin
                  DAE.GIVEN(__)  => begin
                    "Uncertainty.given"
                  end

                  DAE.SOUGHT(__)  => begin
                    "Uncertainty.sought"
                  end

                  DAE.REFINE(__)  => begin
                    "Uncertainty.refine"
                  end
                end
              end
          out
        end

         #=
          Author: Peter Aronsson 2012

          Dump Distribution to a string.
         =#
        function dumpDistributionStr(distribution::DAE.Distribution) ::String
              local out::String

              out = begin
                  local name::DAE.Exp
                  local params::DAE.Exp
                  local paramNames::DAE.Exp
                  local name_str::String
                  local params_str::String
                  local paramNames_str::String
                @match distribution begin
                  DAE.DISTRIBUTION(name = name, params = params, paramNames = paramNames)  => begin
                      name_str = ExpressionDump.printExpStr(name)
                      params_str = ExpressionDump.printExpStr(params)
                      paramNames_str = ExpressionDump.printExpStr(paramNames)
                    "Distribution(name = " + name_str + ", params = " + params_str + ", paramNames= " + paramNames_str + ")"
                  end
                end
              end
          out
        end

         #= Dump VariableAttributes option. =#
        function dumpVariableAttributes(attr::Option{<:DAE.VariableAttributes})
              local res::String

              res = dumpVariableAttributesStr(attr)
              Print.printBuf(res)
        end

         #= Dump VariableAttributes option to a string. =#
        function dumpVariableAttributesStr(inVariableAttributesOption::Option{<:DAE.VariableAttributes}) ::String
              local outString::String

              outString = begin
                  local quantity::String
                  local unit_str::String
                  local displayUnit_str::String
                  local stateSel_str::String
                  local min_str::String
                  local max_str::String
                  local nominal_str::String
                  local initial_str::String
                  local fixed_str::String
                  local uncertainty_str::String
                  local dist_str::String
                  local res_1::String
                  local res1::String
                  local res::String
                  local startOriginStr::String
                  local quant::Option{DAE.Exp}
                  local unit::Option{DAE.Exp}
                  local displayUnit::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local initialExp::Option{DAE.Exp}
                  local nominal::Option{DAE.Exp}
                  local fixed::Option{DAE.Exp}
                  local startOrigin::Option{DAE.Exp}
                  local stateSel::Option{DAE.StateSelect}
                  local uncertainty::Option{DAE.Uncertainty}
                  local dist::Option{DAE.Distribution}
                @matchcontinue inVariableAttributesOption begin
                  SOME(DAE.VAR_ATTR_REAL(quant, unit, displayUnit, min, max, initialExp, fixed, nominal, stateSel, uncertainty, dist, _, _, _, startOrigin))  => begin
                      quantity = Dump.getOptionWithConcatStr(quant, ExpressionDump.printExpStr, "quantity = ")
                      unit_str = Dump.getOptionWithConcatStr(unit, ExpressionDump.printExpStr, "unit = ")
                      displayUnit_str = Dump.getOptionWithConcatStr(displayUnit, ExpressionDump.printExpStr, "displayUnit = ")
                      stateSel_str = Dump.getOptionWithConcatStr(stateSel, dumpStateSelectStr, "stateSelect = ")
                      min_str = Dump.getOptionWithConcatStr(min, ExpressionDump.printExpStr, "min = ")
                      max_str = Dump.getOptionWithConcatStr(max, ExpressionDump.printExpStr, "max = ")
                      nominal_str = Dump.getOptionWithConcatStr(nominal, ExpressionDump.printExpStr, "nominal = ")
                      initial_str = Dump.getOptionWithConcatStr(initialExp, ExpressionDump.printExpStr, "start = ")
                      fixed_str = Dump.getOptionWithConcatStr(fixed, ExpressionDump.printExpStr, "fixed = ")
                      uncertainty_str = Dump.getOptionWithConcatStr(uncertainty, dumpUncertaintyStr, "uncertainty = ")
                      dist_str = Dump.getOptionWithConcatStr(dist, dumpDistributionStr, "distribution = ")
                      startOriginStr = getStartOrigin(startOrigin)
                      res_1 = Util.stringDelimitListNonEmptyElts(list(quantity, unit_str, displayUnit_str, min_str, max_str, initial_str, fixed_str, nominal_str, stateSel_str, uncertainty_str, dist_str, startOriginStr), ", ")
                      res = if stringEmpty(res_1)
                            ""
                          else
                            stringAppendList(list("(", res_1, ")"))
                          end
                    res
                  end

                  SOME(DAE.VAR_ATTR_INT(quant, min, max, initialExp, fixed, uncertainty, dist, _, _, _, startOrigin))  => begin
                      quantity = Dump.getOptionWithConcatStr(quant, ExpressionDump.printExpStr, "quantity = ")
                      min_str = Dump.getOptionWithConcatStr(min, ExpressionDump.printExpStr, "min = ")
                      max_str = Dump.getOptionWithConcatStr(max, ExpressionDump.printExpStr, "max = ")
                      initial_str = Dump.getOptionWithConcatStr(initialExp, ExpressionDump.printExpStr, "start = ")
                      fixed_str = Dump.getOptionWithConcatStr(fixed, ExpressionDump.printExpStr, "fixed = ")
                      uncertainty_str = Dump.getOptionWithConcatStr(uncertainty, dumpUncertaintyStr, "uncertainty = ")
                      dist_str = Dump.getOptionWithConcatStr(dist, dumpDistributionStr, "distribution = ")
                      startOriginStr = getStartOrigin(startOrigin)
                      res_1 = Util.stringDelimitListNonEmptyElts(list(quantity, min_str, max_str, initial_str, fixed_str, uncertainty_str, dist_str, startOriginStr), ", ")
                      res = if stringEmpty(res_1)
                            ""
                          else
                            stringAppendList(list("(", res_1, ")"))
                          end
                    res
                  end

                  SOME(DAE.VAR_ATTR_BOOL(quant, initialExp, fixed, _, _, _, startOrigin))  => begin
                      quantity = Dump.getOptionWithConcatStr(quant, ExpressionDump.printExpStr, "quantity = ")
                      initial_str = Dump.getOptionWithConcatStr(initialExp, ExpressionDump.printExpStr, "start = ")
                      fixed_str = Dump.getOptionWithConcatStr(fixed, ExpressionDump.printExpStr, "fixed = ")
                      startOriginStr = getStartOrigin(startOrigin)
                      res_1 = Util.stringDelimitListNonEmptyElts(list(quantity, initial_str, fixed_str, startOriginStr), ", ")
                      res = if stringEmpty(res_1)
                            ""
                          else
                            stringAppendList(list("(", res_1, ")"))
                          end
                    res
                  end

                  SOME(DAE.VAR_ATTR_STRING(quant, initialExp, fixed, _, _, _, startOrigin))  => begin
                      quantity = Dump.getOptionWithConcatStr(quant, ExpressionDump.printExpStr, "quantity = ")
                      initial_str = Dump.getOptionWithConcatStr(initialExp, ExpressionDump.printExpStr, "start = ")
                      fixed_str = Dump.getOptionWithConcatStr(fixed, ExpressionDump.printExpStr, "fixed = ")
                      startOriginStr = getStartOrigin(startOrigin)
                      res_1 = Util.stringDelimitListNonEmptyElts(list(quantity, initial_str, fixed_str, startOriginStr), ", ")
                      res = if stringEmpty(res_1)
                            ""
                          else
                            stringAppendList(list("(", res_1, ")"))
                          end
                    res
                  end

                  SOME(DAE.VAR_ATTR_ENUMERATION(quant, min, max, initialExp, fixed, _, _, _, startOrigin))  => begin
                      quantity = Dump.getOptionWithConcatStr(quant, ExpressionDump.printExpStr, "quantity = ")
                      min_str = Dump.getOptionWithConcatStr(min, ExpressionDump.printExpStr, "min = ")
                      max_str = Dump.getOptionWithConcatStr(max, ExpressionDump.printExpStr, "max = ")
                      initial_str = Dump.getOptionWithConcatStr(initialExp, ExpressionDump.printExpStr, "start = ")
                      fixed_str = Dump.getOptionWithConcatStr(fixed, ExpressionDump.printExpStr, "fixed = ")
                      startOriginStr = getStartOrigin(startOrigin)
                      res_1 = Util.stringDelimitListNonEmptyElts(list(quantity, min_str, max_str, initial_str, fixed_str, startOriginStr), ", ")
                      res = if stringEmpty(res_1)
                            ""
                          else
                            stringAppendList(list("(", res_1, ")"))
                          end
                    res
                  end

                  NONE()  => begin
                    ""
                  end

                  _  => begin
                      "(unknown VariableAttributes)"
                  end
                end
              end
          outString
        end

        function getStartOrigin(inStartOrigin::Option{<:DAE.Exp}) ::String
              local outStartOrigin::String

              outStartOrigin = begin
                  local str::String
                @match inStartOrigin begin
                  NONE()  => begin
                    ""
                  end

                  _  => begin
                      if Flags.isSet(Flags.SHOW_START_ORIGIN)
                        str = Dump.getOptionWithConcatStr(inStartOrigin, ExpressionDump.printExpStr, "startOrigin = ")
                      else
                        str = ""
                      end
                    str
                  end
                end
              end
          outStartOrigin
        end

         #= Prints 'protected' to a string for protected variables =#
        function dumpVarVisibilityStr(prot::DAE.VarVisibility) ::String
              local str::String

              str = begin
                @match prot begin
                  DAE.PUBLIC(__)  => begin
                    ""
                  end

                  DAE.PROTECTED(__)  => begin
                    "protected "
                  end
                end
              end
          str
        end

         #= Dump VarParallelism to a string =#
        function dumpVarParallelismStr(inVarParallelism::DAE.VarParallelism) ::String
              local outString::String

              outString = begin
                @match inVarParallelism begin
                  DAE.NON_PARALLEL(__)  => begin
                    ""
                  end

                  DAE.PARGLOBAL(__)  => begin
                    "parglobal "
                  end

                  DAE.PARLOCAL(__)  => begin
                    "parlocal "
                  end
                end
              end
          outString
        end

         #= Dumps a comment to a string. =#
        function dumpCommentStr(inComment::Option{<:SCode.Comment}) ::String
              local outString::String

              outString = begin
                  local cmt::String
                @match inComment begin
                  SOME(SCode.COMMENT(comment = SOME(cmt)))  => begin
                      cmt = System.escapedString(cmt, false)
                    stringAppendList(list(" \\", cmt, "\\"))
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

        function dumpClassAnnotationStr(inComment::Option{<:SCode.Comment}) ::String
              local outString::String

              outString = dumpAnnotationStr(inComment, "  ", ";\\n")
          outString
        end

        function dumpCompAnnotationStr(inComment::Option{<:SCode.Comment}) ::String
              local outString::String

              outString = dumpAnnotationStr(inComment, " ", "")
          outString
        end

        function dumpAnnotationStr(inComment::Option{<:SCode.Comment}, inPrefix::String, inSuffix::String) ::String
              local outString::String

              outString = begin
                  local ann::String
                  local ann_mod::SCode.Mod
                @matchcontinue (inComment, inPrefix, inSuffix) begin
                  (SOME(SCode.COMMENT(annotation_ = SOME(SCode.ANNOTATION(ann_mod)))), _, _)  => begin
                      if Config.showAnnotations()
                        ann = inPrefix + "annotation" + SCodeDump.printModStr(ann_mod, SCodeDump.defaultOptions) + inSuffix
                      elseif Config.showStructuralAnnotations()
                        ann_mod = filterStructuralMods(ann_mod)
                        if ! SCodeUtil.isEmptyMod(ann_mod)
                          ann = inPrefix + "annotation" + SCodeDump.printModStr(ann_mod, SCodeDump.defaultOptions) + inSuffix
                        end
                      else
                        ann = ""
                      end
                    ann
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

        function filterStructuralMods(mod::SCode.Mod) ::SCode.Mod


              mod = SCodeUtil.filterSubMods(mod, filterStructuralMod)
          mod
        end

        function filterStructuralMod(mod::SCode.SubMod) ::Bool
              local keep::Bool

              keep = begin
                @match mod.ident begin
                  "Evaluate"  => begin
                    true
                  end

                  "Inline"  => begin
                    true
                  end

                  "LateInline"  => begin
                    true
                  end

                  "derivative"  => begin
                    true
                  end

                  "inverse"  => begin
                    true
                  end

                  "smoothOrder"  => begin
                    true
                  end

                  "InlineAfterIndexReduction"  => begin
                    true
                  end

                  "GenerateEvents"  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          keep
        end

        function dumpCommentAnnotationStr(inComment::Option{<:SCode.Comment}) ::String
              local outString::String

              outString = begin
                @match inComment begin
                  NONE()  => begin
                    ""
                  end

                  _  => begin
                      dumpCommentStr(inComment) + dumpCompAnnotationStr(inComment)
                  end
                end
              end
          outString
        end

         #= Dump Comment option. =#
        function dumpCommentOption(comment::Option{<:SCode.Comment})
              local str::String

              str = dumpCommentAnnotationStr(comment)
              Print.printBuf(str)
        end

         #= Dump equation. =#
        function dumpEquation(inElement::DAE.Element)
              _ = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local c::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local functionName::Absyn.Path
                  local functionArgs::List{DAE.Exp}
                  local src::DAE.ElementSource
                  local sourceStr::String
                @matchcontinue inElement begin
                  DAE.EQUATION(exp = e1, scalar = e2, source = src)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2, source = src)  => begin
                      Print.printBuf("  ")
                      ComponentReference.printComponentRef(cr1)
                      Print.printBuf(" = ")
                      ComponentReference.printComponentRef(cr2)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2, source = src)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2, source = src)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.DEFINE(componentRef = c, exp = e, source = src)  => begin
                      Print.printBuf("  ")
                      ComponentReference.printComponentRef(c)
                      Print.printBuf(" ::= ")
                      ExpressionDump.printExp(e)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.ASSERT(condition = e1, message = e2, source = src)  => begin
                      Print.printBuf("assert(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(") ")
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.NORETCALL(exp = e1, source = src)  => begin
                      ExpressionDump.printExp(e1)
                      sourceStr = getSourceInformationStr(src)
                      Print.printBuf(sourceStr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  _  => begin
                      Print.printBuf("/* FIXME: UNHANDLED_EQUATION in DAEDump.dumpEquation */;\\n")
                    ()
                  end
                end
              end
        end

         #= Dump initial equation. =#
        function dumpInitialEquation(inElement::DAE.Element)
              _ = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local c::DAE.ComponentRef
                  local xs1::List{DAE.Element}
                  local xs2::List{DAE.Element}
                  local trueBranches::List{List{DAE.Element}}
                  local conds::List{DAE.Exp}
                  local s::String
                  local s1::String
                  local s2::String
                  local sourceStr::String
                  local str::IOStream.IOStreamType
                  local src::DAE.ElementSource
                  local cmt::List{SCode.Comment}
                @matchcontinue inElement begin
                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.INITIALDEFINE(componentRef = c, exp = e)  => begin
                      Print.printBuf("  ")
                      ComponentReference.printComponentRef(c)
                      Print.printBuf(" ::= ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      Print.printBuf("  ")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(" = ")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(";\\n")
                    ()
                  end

                  DAE.INITIAL_IF_EQUATION(condition1 = e <| conds, equations2 = xs1 <| trueBranches, equations3 = xs2)  => begin
                      Print.printBuf("  if ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(" then\\n")
                      ListUtil.map_0(xs1, dumpInitialEquation)
                      str = dumpIfEquationsStream(conds, trueBranches, IOStream.emptyStreamOfTypeList)
                      s = IOStream.string(str)
                      Print.printBuf(s)
                      Print.printBuf("  else\\n")
                      ListUtil.map_0(xs2, dumpInitialEquation)
                      Print.printBuf("end if;\\n")
                    ()
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      s = stringAppendList(list("  assert(", s1, ",", s2, ") ", sourceStr, ";\\n"))
                      Print.printBuf(s)
                    ()
                  end

                  DAE.INITIAL_TERMINATE(message = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s = stringAppendList(list("  terminate(", s1, ") ", sourceStr, ";\\n"))
                      Print.printBuf(s)
                    ()
                  end

                  DAE.INITIAL_NORETCALL(exp = e1)  => begin
                      ExpressionDump.printExp(e1)
                      Print.printBuf(";\\n")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Dump equation to a string. =#
        function dumpEquationStr(inElement::DAE.Element) ::String
              local outString::String

              outString = begin
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local s5::String
                  local str::String
                  local sourceStr::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local c::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local es::List{DAE.Exp}
                  local path::Absyn.Path
                  local src::DAE.ElementSource
                  local cmt::List{SCode.Comment}
                @matchcontinue inElement begin
                  DAE.EQUATION(exp = e1, scalar = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                    str
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ComponentReference.printComponentRefStr(cr1)
                      s2 = ComponentReference.printComponentRefStr(cr2)
                      str = stringAppendList(list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                    str
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.DEFINE(componentRef = c, exp = e, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ComponentReference.printComponentRefStr(c)
                      s2 = stringAppend("  ", s1)
                      s3 = stringAppend(" ::= ", s2)
                      s4 = ExpressionDump.printExpStr(e)
                      s5 = stringAppend(s3, s4)
                      str = stringAppend(s5, sourceStr + ";\\n")
                    str
                  end

                  DAE.ASSERT(condition = e1, message = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("  assert(", s1, ",", s2, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.TERMINATE(message = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("  terminate(", s1, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.NORETCALL(exp = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("  ", s1, sourceStr, ";\\n"))
                    str
                  end

                  _  => begin
                      "#UNKNOWN_EQUATION#"
                  end
                end
              end
               #=  adrpo: TODO! FIXME! should we say UNKNOWN equation here? we don't handle all cases!
               =#
          outString
        end

         #= Dump algorithm. =#
        function dumpAlgorithm(inElement::DAE.Element)
              _ = begin
                  local stmts::List{DAE.Statement}
                @matchcontinue inElement begin
                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts))  => begin
                      Print.printBuf("algorithm\\n")
                      Dump.printList(stmts, ppStatement, "")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Dump initial algorithm. =#
        function dumpInitialAlgorithm(inElement::DAE.Element)
              _ = begin
                  local stmts::List{DAE.Statement}
                @matchcontinue inElement begin
                  DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts))  => begin
                      Print.printBuf("initial algorithm\\n")
                      Dump.printList(stmts, ppStatement, "")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Dump External Object class =#
        function dumpExtObjectClass(inElement::DAE.Element)
              _ = begin
                  local fstr::String
                  local fpath::Absyn.Path
                @matchcontinue inElement begin
                  DAE.EXTOBJECTCLASS(path = fpath)  => begin
                      Print.printBuf("class ")
                      fstr = AbsynUtil.pathString(fpath)
                      Print.printBuf(fstr)
                      Print.printBuf("\\n extends ExternalObject;\\n")
                      Print.printBuf("end ")
                      Print.printBuf(fstr)
                      Print.printBuf(";\\n")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #=
          Author BZ
          Function for printing conditions =#
        function derivativeCondStr(dc::DAE.derivativeCond) ::String
              local str::String

              str = begin
                  local e::DAE.Exp
                @match dc begin
                  DAE.NO_DERIVATIVE(e)  => begin
                      str = "noDerivative(" + ExpressionDump.printExpStr(e) + ")"
                    str
                  end

                  DAE.ZERO_DERIVATIVE(__)  => begin
                    "zeroDerivative"
                  end
                end
              end
          str
        end

         #= Dump function =#
        function dumpFunction(inElement::DAE.Function)
              _ = begin
                  local fstr::String
                  local inlineTypeStr::String
                  local ext_decl_str::String
                  local parallelism_str::String
                  local impureStr::String
                  local typeStr::String
                  local fpath::Absyn.Path
                  local daeElts::List{DAE.Element}
                  local t::DAE.Type
                  local inlineType::DAE.InlineType
                  local c::Option{SCode.Comment}
                  local ext_decl::DAE.ExternalDecl
                  local isImpure::Bool
                @matchcontinue inElement begin
                  DAE.FUNCTION(path = fpath, inlineType = inlineType, functions = DAE.FUNCTION_DEF(body = daeElts) <| _, type_ = t, isImpure = isImpure, comment = c)  => begin
                      typeStr = Types.printTypeStr(t)
                      Print.printBuf(typeStr)
                      parallelism_str = dumpParallelismStr(t)
                      Print.printBuf(parallelism_str)
                      impureStr = if isImpure
                            "impure "
                          else
                            ""
                          end
                      Print.printBuf(impureStr)
                      Print.printBuf("function ")
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      Print.printBuf(fstr)
                      inlineTypeStr = dumpInlineTypeStr(inlineType)
                      Print.printBuf(inlineTypeStr)
                      Print.printBuf(dumpCommentStr(c))
                      Print.printBuf("\\n")
                      dumpFunctionElements(daeElts)
                      Print.printBuf(dumpClassAnnotationStr(c))
                      Print.printBuf("end ")
                      Print.printBuf(fstr)
                      Print.printBuf(";\\n\\n")
                    ()
                  end

                  DAE.FUNCTION(functions = DAE.FUNCTION_EXT(externalDecl = DAE.EXTERNALDECL(language = "builtin")) <| _)  => begin
                    ()
                  end

                  DAE.FUNCTION(path = fpath, inlineType = inlineType, functions = DAE.FUNCTION_EXT(body = daeElts, externalDecl = ext_decl) <| _, isImpure = isImpure, comment = c)  => begin
                      impureStr = if isImpure
                            "impure "
                          else
                            ""
                          end
                      Print.printBuf(impureStr)
                      Print.printBuf("function ")
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      Print.printBuf(fstr)
                      inlineTypeStr = dumpInlineTypeStr(inlineType)
                      Print.printBuf(inlineTypeStr)
                      Print.printBuf(dumpCommentStr(c))
                      Print.printBuf("\\n")
                      dumpFunctionElements(daeElts)
                      ext_decl_str = dumpExtDeclStr(ext_decl)
                      Print.printBuf("\\n  " + ext_decl_str + "\\n")
                      Print.printBuf(dumpClassAnnotationStr(c))
                      Print.printBuf("end ")
                      Print.printBuf(fstr)
                      Print.printBuf(";\\n\\n")
                    ()
                  end

                  DAE.RECORD_CONSTRUCTOR(path = fpath, type_ = t)  => begin
                      @match false = Flags.isSet(Flags.DISABLE_RECORD_CONSTRUCTOR_OUTPUT)
                      Print.printBuf("function ")
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      Print.printBuf(fstr)
                      Print.printBuf(" \\Automatically generated record constructor for " + fstr + "\\\\n")
                      Print.printBuf(printRecordConstructorInputsStr(t))
                      Print.printBuf("  output " + AbsynUtil.pathLastIdent(fpath) + " res;\\n")
                      Print.printBuf("end ")
                      Print.printBuf(fstr)
                      Print.printBuf(";\\n\\n")
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

        function dumpParallelismStr(inType::DAE.Type) ::String
              local outString::String

              outString = begin
                @match inType begin
                  DAE.T_FUNCTION(_, _, DAE.FUNCTION_ATTRIBUTES(functionParallelism = DAE.FP_NON_PARALLEL(__)), _)  => begin
                    ""
                  end

                  DAE.T_FUNCTION(_, _, DAE.FUNCTION_ATTRIBUTES(functionParallelism = DAE.FP_PARALLEL_FUNCTION(__)), _)  => begin
                    "parallel "
                  end

                  DAE.T_FUNCTION(_, _, DAE.FUNCTION_ATTRIBUTES(functionParallelism = DAE.FP_KERNEL_FUNCTION(__)), _)  => begin
                    "kernel "
                  end

                  _  => begin
                      "#dumpParallelismStr failed#"
                  end
                end
              end
          outString
        end

        function dumpInlineTypeStr(inlineType::DAE.InlineType) ::String
              local str::String

              str = begin
                @match inlineType begin
                  DAE.NO_INLINE(__)  => begin
                    "\\Inline never\\"
                  end

                  DAE.AFTER_INDEX_RED_INLINE(__)  => begin
                    " \\Inline after index reduction\\"
                  end

                  DAE.NORM_INLINE(__)  => begin
                    " \\Inline before index reduction\\"
                  end

                  DAE.DEFAULT_INLINE(__)  => begin
                    "\\Inline if necessary\\"
                  end

                  _  => begin
                      "\\unknown\\"
                  end
                end
              end
          str
        end

         #= Helper function to dumpFunction. Prints the inputs of a record constructor. =#
        function printRecordConstructorInputsStr(itp::DAE.Type) ::String
              local str::String

              str = begin
                  local var_strl::List{String}
                  local vars::List{DAE.Var}
                  local tp::DAE.Type
                @match itp begin
                  DAE.T_COMPLEX(varLst = vars)  => begin
                      var_strl = ListUtil.map(vars, printRecordConstructorInputStr)
                    stringAppendList(var_strl)
                  end

                  DAE.T_FUNCTION(funcResultType = tp)  => begin
                    printRecordConstructorInputsStr(tp)
                  end
                end
              end
          str
        end

        function printRecordConstructorInputStr(inVar::DAE.Var) ::String
              local outString::String

              local name::String
              local attr_str::String
              local binding_str::String
              local ty_str::String
              local ty_vars_str::String
              local attr::DAE.Attributes
              local ty::DAE.Type
              local binding::DAE.Binding

              @match DAE.TYPES_VAR(name = name, attributes = attr, ty = ty, binding = binding) = inVar
              attr_str = printRecordConstructorInputAttrStr(attr)
              binding_str = printRecordConstructorBinding(binding)
              (ty_str, ty_vars_str) = printTypeStr(ty)
              outString = stringAppendList(list("  ", attr_str, ty_str, " ", name, ty_vars_str, binding_str, ";\\n"))
          outString
        end

        function printRecordConstructorInputAttrStr(inAttributes::DAE.Attributes) ::String
              local outString::String

              outString = begin
                @match inAttributes begin
                  DAE.ATTR(visibility = SCode.PROTECTED(__))  => begin
                    "protected "
                  end

                  DAE.ATTR(variability = SCode.CONST(__))  => begin
                    "constant "
                  end

                  _  => begin
                      "input "
                  end
                end
              end
               #=  protected vars are not input!, see Modelica Spec 3.2, Section 12.6, Record Constructor Functions, page 140
               =#
               #=  constants are not input! see Modelica Spec 3.2, Section 12.6, Record Constructor Functions, page 140
               =#
          outString
        end

         #= prints the binding of a record constructor input =#
        function printRecordConstructorBinding(binding::DAE.Binding) ::String
              local str::String

              str = begin
                  local e::DAE.Exp
                  local v::Values.Value
                @match binding begin
                  DAE.UNBOUND(__)  => begin
                    ""
                  end

                  DAE.EQBOUND(exp = e, source = DAE.BINDING_FROM_DEFAULT_VALUE(__))  => begin
                      str = " = " + ExpressionDump.printExpStr(e)
                    str
                  end

                  DAE.VALBOUND(valBound = v, source = DAE.BINDING_FROM_DEFAULT_VALUE(__))  => begin
                      str = " = " + ValuesUtil.valString(v)
                    str
                  end
                end
              end
          str
        end

         #= Prettyprint an algorithm statement =#
        function ppStatement(alg::DAE.Statement)
              ppStmt(alg, 2)
        end

         #= Prettyprint an algorithm statement to a string. =#
        function ppStatementStr(alg::DAE.Statement) ::String
              local str::String

              str = ppStmtStr(alg, 2)
          str
        end

         #= Helper function to ppStatement. =#
        function ppStmt(inStatement::DAE.Statement, inInteger::ModelicaInteger)
              _ = begin
                  local c::DAE.ComponentRef
                  local e::DAE.Exp
                  local cond::DAE.Exp
                  local msg::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local i::ModelicaInteger
                  local i_1::ModelicaInteger
                  local index::ModelicaInteger
                  local s1::String
                  local s2::String
                  local s3::String
                  local str::String
                  local id::String
                  local name::String
                  local es::List{String}
                  local expl::List{DAE.Exp}
                  local then_::List{DAE.Statement}
                  local stmts::List{DAE.Statement}
                  local stmt::DAE.Statement
                  local ty::DAE.Type
                  local else_::DAE.Else
                  local source::DAE.ElementSource
                @matchcontinue (inStatement, inInteger) begin
                  (DAE.STMT_ASSIGN(exp1 = e2, exp = e, source = source), i)  => begin
                      indent(i)
                      ExpressionDump.printExp(e2)
                      Print.printBuf(" := ")
                      ExpressionDump.printExp(e)
                      if Config.typeinfo()
                        Print.printBuf(" /* " + Error.infoStr(ElementSource.getElementSourceFileInfo(source)) + " */")
                      end
                      Print.printBuf(";\\n")
                    ()
                  end

                  (DAE.STMT_ASSIGN_ARR(lhs = e2, exp = e), i)  => begin
                      indent(i)
                      ExpressionDump.printExp(e2)
                      Print.printBuf(" := ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(";\\n")
                    ()
                  end

                  (DAE.STMT_TUPLE_ASSIGN(expExpLst = expl, exp = e), i)  => begin
                      s1 = indentStr(i)
                      s2 = ExpressionDump.printExpStr(e)
                      es = ListUtil.map(expl, ExpressionDump.printExpStr)
                      s3 = stringDelimitList(es, ", ")
                      str = stringAppendList(list(s1, "(", s3, ") := ", s2, ";\\n"))
                      Print.printBuf(str)
                    ()
                  end

                  (DAE.STMT_IF(exp = e, statementLst = then_, else_ = else_), i)  => begin
                      indent(i)
                      Print.printBuf("if ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(" then\\n")
                      i_1 = i + 2
                      ppStmtList(then_, i_1)
                      ppElse(else_, i)
                      indent(i)
                      Print.printBuf("end if;\\n")
                    ()
                  end

                  (DAE.STMT_FOR(iter = id, index = index, range = e, statementLst = stmts), i)  => begin
                      indent(i)
                      Print.printBuf("for ")
                      Print.printBuf(id)
                      if index != (-1)
                        Print.printBuf(" /* iter index " + intString(index) + " */")
                      end
                      Print.printBuf(" in ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(" loop\\n")
                      i_1 = i + 2
                      ppStmtList(stmts, i_1)
                      indent(i)
                      Print.printBuf("end for;\\n")
                    ()
                  end

                  (DAE.STMT_PARFOR(iter = id, index = index, range = e, statementLst = stmts), i)  => begin
                      indent(i)
                      Print.printBuf("parfor ")
                      Print.printBuf(id)
                      if index != (-1)
                        Print.printBuf(" /* iter index " + intString(index) + " */")
                      end
                      Print.printBuf(" in ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(" loop\\n")
                      i_1 = i + 2
                      ppStmtList(stmts, i_1)
                      indent(i)
                      Print.printBuf("end parfor;\\n")
                    ()
                  end

                  (DAE.STMT_WHILE(exp = e, statementLst = stmts), i)  => begin
                      indent(i)
                      Print.printBuf("while ")
                      ExpressionDump.printExp(e)
                      Print.printBuf(" loop\\n")
                      i_1 = i + 2
                      ppStmtList(stmts, i_1)
                      indent(i)
                      Print.printBuf("end while;\\n")
                    ()
                  end

                  (DAE.STMT_NORETCALL(exp = e1), i)  => begin
                      indent(i)
                      _ = begin
                        @match e1 begin
                          DAE.CALL(attr = DAE.CALL_ATTR(tailCall = DAE.TAIL(__)))  => begin
                              Print.printBuf("return ")
                            ()
                          end

                          _  => begin
                              ()
                          end
                        end
                      end
                      ExpressionDump.printExp(e1)
                      Print.printBuf(";\\n")
                    ()
                  end

                  (stmt && DAE.STMT_WHEN(__), i)  => begin
                      indent(i)
                      Print.printBuf(ppWhenStmtStr(stmt, 1))
                    ()
                  end

                  (DAE.STMT_ASSERT(cond = cond, msg = msg), i)  => begin
                      indent(i)
                      Print.printBuf("assert(")
                      ExpressionDump.printExp(cond)
                      Print.printBuf(", ")
                      ExpressionDump.printExp(msg)
                      Print.printBuf(");\\n")
                    ()
                  end

                  (DAE.STMT_RETURN(__), i)  => begin
                      indent(i)
                      Print.printBuf("return;\\n")
                    ()
                  end

                  (DAE.STMT_BREAK(__), i)  => begin
                      indent(i)
                      Print.printBuf("break;\\n")
                    ()
                  end

                  (DAE.STMT_REINIT(var = e1, value = e2), i)  => begin
                      indent(i)
                      Print.printBuf("reinit(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(");\\n")
                    ()
                  end

                  (DAE.STMT_FAILURE(body = stmts), i)  => begin
                      indent(i)
                      Print.printBuf("begin failure\\n")
                      ppStmtList(stmts, i + 2)
                      Print.printBuf("end try;\\n")
                    ()
                  end

                  (DAE.STMT_ARRAY_INIT(name = name, ty = ty), i)  => begin
                      indent(i)
                      Print.printBuf("/* ")
                      Print.printBuf(name)
                      Print.printBuf(" := array_alloc(")
                      Print.printBuf(Types.unparseType(ty))
                      Print.printBuf(") */;\\n")
                    ()
                  end

                  (_, i)  => begin
                      indent(i)
                      Print.printBuf("**ALGORITHM**;\\n")
                    ()
                  end
                end
              end
        end

        function ppWhenStmtStr(inStatement::DAE.Statement, inInteger::ModelicaInteger) ::String
              local outString::String

              outString = begin
                  local s3::String
                  local s4::String
                  local s5::String
                  local s6::String
                  local str::String
                  local s7::String
                  local s8::String
                  local s9::String
                  local s10::String
                  local e::DAE.Exp
                  local i::ModelicaInteger
                  local i_1::ModelicaInteger
                  local stmts::List{DAE.Statement}
                  local stmt::DAE.Statement
                @match (inStatement, inInteger) begin
                  (DAE.STMT_WHEN(exp = e, statementLst = stmts, elseWhen = NONE()), i)  => begin
                      s3 = stringAppend("when ", ExpressionDump.printExpStr(e))
                      s5 = stringAppend(s3, " then\\n")
                      i_1 = i + 2
                      s6 = ppStmtListStr(stmts, i_1)
                      s7 = stringAppend(s5, s6)
                      s8 = indentStr(i)
                      s9 = stringAppend(s7, s8)
                      str = stringAppend(s9, "end when;\\n")
                    str
                  end

                  (DAE.STMT_WHEN(exp = e, statementLst = stmts, elseWhen = SOME(stmt)), i)  => begin
                      s3 = ExpressionDump.printExpStr(e)
                      s4 = stringAppend("when ", s3)
                      s5 = stringAppend(s4, " then\\n")
                      i_1 = i + 2
                      s6 = ppStmtListStr(stmts, i_1)
                      s7 = stringAppend(s5, s6)
                      s8 = ppWhenStmtStr(stmt, i)
                      s9 = stringAppend(indentStr(i), "else")
                      s10 = stringAppend(s7, s9)
                      str = stringAppend(s10, s8)
                    str
                  end
                end
              end
          outString
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
                      s2 = ExpressionDump.printExpStr(e2)
                      s3 = ExpressionDump.printExpStr(e)
                      str = stringAppendList(list(s1, s2, " := ", s3, ";\\n"))
                    str
                  end

                  (DAE.STMT_ASSIGN_ARR(lhs = e2, exp = e), i)  => begin
                      s1 = indentStr(i)
                      s2 = ExpressionDump.printExpStr(e2)
                      s3 = ExpressionDump.printExpStr(e)
                      str = stringAppendList(list(s1, s2, " := ", s3, ";\\n"))
                    str
                  end

                  (DAE.STMT_TUPLE_ASSIGN(expExpLst = expl, exp = e), i)  => begin
                      s1 = indentStr(i)
                      s2 = ExpressionDump.printExpStr(e)
                      es = ListUtil.map(expl, ExpressionDump.printExpStr)
                      s3 = stringDelimitList(es, ", ")
                      str = stringAppendList(list(s1, "(", s3, ") := ", s2, ";\\n"))
                    str
                  end

                  (DAE.STMT_IF(exp = e, statementLst = then_, else_ = else_), i)  => begin
                      s1 = indentStr(i)
                      s2 = stringAppend(s1, "if ")
                      s3 = ExpressionDump.printExpStr(e)
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
                      s3 = ExpressionDump.printExpStr(e)
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
                      s3 = ExpressionDump.printExpStr(e)
                      i_1 = i + 2
                      s4 = ppStmtListStr(stmts, i_1)
                      s5 = indentStr(i)
                      str = stringAppendList(list(s1, "parfor ", id, s2, " in ", s3, " loop\\n", s4, s5, "end for;\\n"))
                    str
                  end

                  (DAE.STMT_WHILE(exp = e, statementLst = stmts), i)  => begin
                      s1 = indentStr(i)
                      s2 = stringAppend(s1, "while ")
                      s3 = ExpressionDump.printExpStr(e)
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
                      cond_str = ExpressionDump.printExpStr(cond)
                      msg_str = ExpressionDump.printExpStr(msg)
                      str = stringAppendList(list(s1, "assert(", cond_str, ", ", msg_str, ");\\n"))
                    str
                  end

                  (DAE.STMT_TERMINATE(msg = msg), i)  => begin
                      s1 = indentStr(i)
                      msg_str = ExpressionDump.printExpStr(msg)
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
                      s3 = ExpressionDump.printExpStr(e)
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
                      e1_str = ExpressionDump.printExpStr(e1)
                      e2_str = ExpressionDump.printExpStr(e2)
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
                      ExpressionDump.printExp(e)
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
                      s3 = ExpressionDump.printExpStr(e)
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

         #=

         Dump the data structures in a
         paranthesised way

         =#
        function dumpDebug(inDAElist::DAE.DAElist)
              _ = begin
                  local elist::List{DAE.Element}
                @match inDAElist begin
                  DAE.DAE(elementLst = elist)  => begin
                      Print.printBuf("DAE(")
                      dumpDebugElist(elist)
                      Print.printBuf(")")
                    ()
                  end
                end
              end
        end

         #=
          Helper function to dump_debug.
         =#
        function dumpDebugElist(inElementLst::List{<:DAE.Element})
              _ = begin
                  local first::DAE.Element
                  local rest::List{DAE.Element}
                @match inElementLst begin
                   nil()  => begin
                    ()
                  end

                  first <| rest  => begin
                      dumpDebugElement(first)
                      Print.printBuf("\\n")
                      dumpDebugElist(rest)
                    ()
                  end
                end
              end
        end

         #=  =#
        function dumpDebugDAE(dae::DAE.DAElist) ::String
              local str::String

              str = begin
                  local elems::List{DAE.Element}
                @match dae begin
                  DAE.DAE(elementLst = elems)  => begin
                      Print.clearBuf()
                      dumpDebugElist(elems)
                      str = Print.getString()
                    str
                  end
                end
              end
          str
        end

         #=
          Dump element using parenthesis.
         =#
        function dumpDebugElement(inElement::DAE.Element)
              _ = begin
                  local comment_str::String
                  local tmp_str::String
                  local n::String
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local vd::DAE.VarDirection
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local e::DAE.Exp
                  local exp::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local l::List{DAE.Element}
                @matchcontinue inElement begin
                  DAE.VAR(componentRef = cr, kind = vk, binding = NONE(), variableAttributesOption = dae_var_attr, comment = comment)  => begin
                      Print.printBuf("VAR(")
                      ComponentReference.printComponentRef(cr)
                      Print.printBuf(", ")
                      dumpKind(vk)
                      comment_str = dumpCommentAnnotationStr(comment)
                      Print.printBuf("  comment:")
                      Print.printBuf(comment_str)
                      tmp_str = dumpVariableAttributesStr(dae_var_attr)
                      Print.printBuf(tmp_str)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.VAR(componentRef = cr, kind = vk, binding = SOME(e), variableAttributesOption = dae_var_attr, comment = comment)  => begin
                      Print.printBuf("VAR(")
                      ComponentReference.printComponentRef(cr)
                      Print.printBuf(", ")
                      dumpKind(vk)
                      Print.printBuf(", binding: ")
                      ExpressionDump.printExp(e)
                      comment_str = dumpCommentAnnotationStr(comment)
                      Print.printBuf("  comment:")
                      Print.printBuf(comment_str)
                      tmp_str = dumpVariableAttributesStr(dae_var_attr)
                      Print.printBuf(tmp_str)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.DEFINE(componentRef = cr, exp = exp)  => begin
                      Print.printBuf("DEFINE(")
                      ComponentReference.printComponentRef(cr)
                      Print.printBuf(", ")
                      ExpressionDump.printExp(exp)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIALDEFINE(componentRef = cr, exp = exp)  => begin
                      Print.printBuf("INITIALDEFINE(")
                      ComponentReference.printComponentRef(cr)
                      Print.printBuf(", ")
                      ExpressionDump.printExp(exp)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.EQUATION(exp = e1, scalar = e2)  => begin
                      Print.printBuf("EQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2)  => begin
                      Print.printBuf("EQUATION(")
                      ComponentReference.printComponentRef(cr1)
                      Print.printBuf(",")
                      ComponentReference.printComponentRef(cr2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2)  => begin
                      Print.printBuf("INITIALEQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.ALGORITHM(__)  => begin
                      Print.printBuf("ALGORITHM()")
                    ()
                  end

                  DAE.INITIALALGORITHM(__)  => begin
                      Print.printBuf("INITIALALGORITHM()")
                    ()
                  end

                  DAE.COMP(ident = n, dAElist = l)  => begin
                      Print.printBuf("COMP(")
                      Print.printBuf(n)
                      Print.printBuf(",")
                      dumpDebugElist(l)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      Print.printBuf("ARRAY_EQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      Print.printBuf("INITIAL_ARRAY_EQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      Print.printBuf("COMPLEX_EQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      Print.printBuf("INITIAL_COMPLEX_EQUATION(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.IF_EQUATION(__)  => begin
                      Print.printBuf("IF_EQUATION()")
                    ()
                  end

                  DAE.INITIAL_IF_EQUATION(__)  => begin
                      Print.printBuf("INITIAL_IF_EQUATION()")
                    ()
                  end

                  DAE.WHEN_EQUATION(__)  => begin
                      Print.printBuf("WHEN_EQUATION()")
                    ()
                  end

                  DAE.EXTOBJECTCLASS(__)  => begin
                      Print.printBuf("EXTOBJECTCLASS()")
                    ()
                  end

                  DAE.ASSERT(condition = e1, message = e2)  => begin
                      Print.printBuf("ASSERT(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2)  => begin
                      Print.printBuf("INITIAL_ASSERT(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(",")
                      ExpressionDump.printExp(e2)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.TERMINATE(message = e1)  => begin
                      Print.printBuf("TERMINATE(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.INITIAL_TERMINATE(message = e1)  => begin
                      Print.printBuf("INITIAL_TERMINATE(")
                      ExpressionDump.printExp(e1)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.REINIT(__)  => begin
                      Print.printBuf("REINIT()")
                    ()
                  end

                  DAE.NORETCALL(__)  => begin
                      Print.printBuf("NORETCALL()")
                    ()
                  end

                  DAE.SM_COMP(componentRef = cr, dAElist = l)  => begin
                      Print.printBuf("SM_COMP(")
                      ComponentReference.printComponentRef(cr)
                      Print.printBuf(",")
                      dumpDebugElist(l)
                      Print.printBuf(")")
                    ()
                  end

                  DAE.FLAT_SM(ident = n, dAElist = l)  => begin
                      Print.printBuf("FLAT_SM(")
                      Print.printBuf(n)
                      Print.printBuf(",")
                      dumpDebugElist(l)
                      Print.printBuf(")")
                    ()
                  end

                  _  => begin
                      Print.printBuf("UNKNOWN ")
                    ()
                  end
                end
              end
        end

         #=
        Author BZ 2008-07, dump flow properties to string. =#
        function dumpFlow(var::DAE.ConnectorType) ::String
              local flowString::String

              flowString = begin
                @match var begin
                  DAE.FLOW(__)  => begin
                    "flow"
                  end

                  DAE.POTENTIAL(__)  => begin
                    "effort"
                  end

                  DAE.NON_CONNECTOR(__)  => begin
                    "non_connector"
                  end
                end
              end
          flowString
        end

        function dumpConnectorType(inConnectorType::DAE.ConnectorType) ::String
              local outString::String

              outString = begin
                @match inConnectorType begin
                  DAE.FLOW(__)  => begin
                    "flow"
                  end

                  DAE.STREAM(__)  => begin
                    "stream"
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #=
         Graphviz functions to visualize
         the dae
         =#
        function dumpGraphviz(dae::DAE.DAElist)
              local r::Graphviz.Node

              r = buildGraphviz(dae)
              Graphviz.dump(r)
        end

         #=
          Builds the graphviz node from a dae list.
         =#
        function buildGraphviz(inDAElist::DAE.DAElist) ::Graphviz.Node
              local outNode::Graphviz.Node

              outNode = begin
                  local vars::List{DAE.Element}
                  local nonvars::List{DAE.Element}
                  local els::List{DAE.Element}
                  local nonvarnodes::List{Graphviz.Node}
                  local varnodes::List{Graphviz.Node}
                  local nodelist::List{Graphviz.Node}
                @match inDAElist begin
                  DAE.DAE(elementLst = els)  => begin
                      vars = DAEUtil.getMatchingElements(els, DAEUtil.isVar)
                      nonvars = DAEUtil.getMatchingElements(els, DAEUtil.isNotVar)
                      nonvarnodes = buildGrList(nonvars)
                      varnodes = buildGrVars(vars)
                      nodelist = listAppend(nonvarnodes, varnodes)
                    Graphviz.NODE("DAE", nil, nodelist)
                  end
                end
              end
          outNode
        end

         #= Helper function to build_graphviz.
         =#
        function buildGrList(inElementLst::List{<:DAE.Element}) ::List{Graphviz.Node}
              local outGraphvizNodeLst::List{Graphviz.Node}

              outGraphvizNodeLst = begin
                  local node::Graphviz.Node
                  local nodelist::List{Graphviz.Node}
                  local el::DAE.Element
                  local rest::List{DAE.Element}
                @match inElementLst begin
                   nil()  => begin
                    nil
                  end

                  el <| rest  => begin
                      node = buildGrElement(el)
                      nodelist = buildGrList(rest)
                    _cons(node, nodelist)
                  end
                end
              end
          outGraphvizNodeLst
        end

         #= Helper function to build_graphviz.
         =#
        function buildGrVars(inElementLst::List{<:DAE.Element}) ::List{Graphviz.Node}
              local outGraphvizNodeLst::List{Graphviz.Node}

              outGraphvizNodeLst = begin
                  local strlist::List{String}
                  local vars::List{DAE.Element}
                @matchcontinue inElementLst begin
                   nil()  => begin
                    nil
                  end

                  vars  => begin
                      (strlist, _) = buildGrStrlist(vars, buildGrVarStr, 10)
                    list(Graphviz.LNODE("VARS", strlist, list(Graphviz.box), nil))
                  end
                end
              end
          outGraphvizNodeLst
        end

         #= Helper function to build_graphviz.
         =#
        function buildGrStrlist(inTypeALst::List{<:Type_a}, inFuncTypeTypeAToString::FuncTypeType_aToString, inInteger::ModelicaInteger) ::Tuple{List{String}, List{Type_a}}
              local outTypeALst::List{Type_a}
              local outStringLst::List{String}

              (outStringLst, outTypeALst) = begin
                  local ignored::List{Type_a}
                  local rest::List{Type_a}
                  local printer::FuncTypeType_aToString
                  local count::ModelicaInteger
                  local count_1::ModelicaInteger
                  local strlist::List{String}
                  local str::String
                  local var::Type_a
                @matchcontinue (inTypeALst, inFuncTypeTypeAToString, inInteger) begin
                  ( nil(), _, _)  => begin
                    (nil, nil)
                  end

                  (ignored, _, count)  => begin
                      if ! count <= 0
                        fail()
                      end
                    (list("..."), ignored)
                  end

                  (var <| rest, printer, count)  => begin
                      if ! count > 0
                        fail()
                      end
                      count_1 = count - 1
                      (strlist, ignored) = buildGrStrlist(rest, printer, count_1)
                      str = printer(var)
                    (_cons(str, strlist), ignored)
                  end
                end
              end
          (outStringLst, outTypeALst)
        end

         #= Helper function to build_graphviz.
         =#
        function buildGrVarStr(inElement::DAE.Element) ::String
              local outString::String

              outString = begin
                  local str::String
                  local expstr::String
                  local str_1::String
                  local str_2::String
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                @match inElement begin
                  DAE.VAR(componentRef = cr, binding = NONE())  => begin
                      str = ComponentReference.printComponentRefStr(cr)
                    str
                  end

                  DAE.VAR(componentRef = cr, binding = SOME(exp))  => begin
                      str = ComponentReference.printComponentRefStr(cr)
                      expstr = printExpStrSpecial(exp)
                      str_1 = stringAppend(str, " = ")
                      str_2 = stringAppend(str_1, expstr)
                    str_2
                  end
                end
              end
          outString
        end

         #=
          Prints an expression to a string suitable for graphviz.
         =#
        function printExpStrSpecial(inExp::DAE.Exp) ::String
              local outString::String

              outString = begin
                  local s_1::String
                  local s_2::String
                  local s::String
                  local str::String
                  local exp::DAE.Exp
                @matchcontinue inExp begin
                  DAE.SCONST(string = s)  => begin
                      s_1 = stringAppend("\\\\\\", s)
                      s_2 = stringAppend(s_1, "\\\\\\")
                    s_2
                  end

                  exp  => begin
                      str = ExpressionDump.printExpStr(exp)
                    str
                  end
                end
              end
          outString
        end

         #=
          Builds a Graphviz.Node from an element.
         =#
        function buildGrElement(inElement::DAE.Element) ::Graphviz.Node
              local outNode::Graphviz.Node

              outNode = begin
                  local crstr::String
                  local vkstr::String
                  local expstr::String
                  local expstr_1::String
                  local e1str::String
                  local e2str::String
                  local n::String
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local vd::DAE.VarDirection
                  local exp::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local nodes::List{Graphviz.Node}
                  local elts::List{DAE.Element}
                @match inElement begin
                  DAE.VAR(componentRef = cr, kind = vk, binding = NONE())  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                      vkstr = dumpKindStr(vk)
                    Graphviz.LNODE("VAR", list(crstr, vkstr), nil, nil)
                  end

                  DAE.VAR(componentRef = cr, kind = vk, binding = SOME(exp))  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                      vkstr = dumpKindStr(vk)
                      expstr = printExpStrSpecial(exp)
                      expstr_1 = stringAppend("= ", expstr)
                    Graphviz.LNODE("VAR", list(crstr, vkstr, expstr_1), nil, nil)
                  end

                  DAE.DEFINE(componentRef = cr, exp = exp)  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                      expstr = printExpStrSpecial(exp)
                      expstr_1 = stringAppend("= ", expstr)
                    Graphviz.LNODE("DEFINE", list(crstr, expstr_1), nil, nil)
                  end

                  DAE.EQUATION(exp = e1, scalar = e2)  => begin
                      e1str = printExpStrSpecial(e1)
                      e2str = printExpStrSpecial(e2)
                    Graphviz.LNODE("EQUATION", list(e1str, "=", e2str), nil, nil)
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2)  => begin
                      e1str = printExpStrSpecial(Expression.crefExp(cr1))
                      e2str = printExpStrSpecial(Expression.crefExp(cr2))
                    Graphviz.LNODE("EQUEQUATION", list(e1str, "=", e2str), nil, nil)
                  end

                  DAE.ALGORITHM(__)  => begin
                    Graphviz.NODE("ALGORITHM", nil, nil)
                  end

                  DAE.INITIALDEFINE(componentRef = cr, exp = exp)  => begin
                      crstr = ComponentReference.printComponentRefStr(cr)
                      expstr = printExpStrSpecial(exp)
                      expstr_1 = stringAppend("= ", expstr)
                    Graphviz.LNODE("INITIALDEFINE", list(crstr, expstr_1), nil, nil)
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2)  => begin
                      e1str = printExpStrSpecial(e1)
                      e2str = printExpStrSpecial(e2)
                    Graphviz.LNODE("INITIALEQUATION", list(e1str, "=", e2str), nil, nil)
                  end

                  DAE.INITIALALGORITHM(__)  => begin
                    Graphviz.NODE("INITIALALGORITHM", nil, nil)
                  end

                  DAE.COMP(ident = n, dAElist = elts)  => begin
                      nodes = buildGrList(elts)
                    Graphviz.LNODE("COMP", list(n), nil, nodes)
                  end
                end
              end
          outNode
        end

         #= wrapper function for Types.unparseType, so records and enumerations can be output properly =#
        function unparseType(tp::DAE.Type) ::String
              local str::String

              str = begin
                  local name::String
                  local dim_str::String
                  local path::Absyn.Path
                  local bc_tp::DAE.Type
                  local ty::DAE.Type
                  local dims::List{DAE.Dimension}
                @matchcontinue tp begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path))  => begin
                      name = AbsynUtil.pathStringNoQual(path)
                    name
                  end

                  DAE.T_ARRAY(ty = ty)  => begin
                      @match DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path)) = Types.arrayElementType(ty)
                      dims = Types.getDimensions(tp)
                      name = AbsynUtil.pathStringNoQual(path)
                      dim_str = ListUtil.toString(dims, ExpressionDump.dimensionString, "", "[", ", ", "]", false)
                    name + dim_str
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty && DAE.T_SUBTYPE_BASIC(__))  => begin
                    unparseType(ty)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = bc_tp)  => begin
                    Types.unparseType(bc_tp)
                  end

                  _  => begin
                      Types.unparseType(tp)
                  end
                end
              end
          str
        end

         #= prints dimensions to a string =#
        function unparseDimensions(dims::DAE.InstDims, printTypeDimension::Bool #= use true here when printing components in functions as these are not vectorized! Otherwise, use false =#) ::String
              local dimsStr::String

              dimsStr = begin
                  local str::String
                   #=  false gives nothing
                   =#
                @matchcontinue (dims, printTypeDimension) begin
                  (_, false)  => begin
                    ""
                  end

                  ( nil(), true)  => begin
                    ""
                  end

                  (_, true)  => begin
                      str = "[" + stringDelimitList(ListUtil.map(dims, ExpressionDump.dimensionString), ", ") + "]"
                    str
                  end
                end
              end
               #=  nothing gives nothing
               =#
               #=  dims give something
               =#
          dimsStr
        end

         #= This function prints the DAE to a string. =#
        function dumpStr(inDAElist::DAE.DAElist, functionTree::DAE.FunctionTree) ::String
              local outString::String

              local daelist::List{DAE.Element}
              local funList::functionList
              local fixedDae::List{compWithSplitElements}

              @match DAE.DAE(elementLst = daelist) = inDAElist
              funList = dumpFunctionList(functionTree)
              fixedDae = ListUtil.map(daelist, DAEUtil.splitComponent)
              outString = Tpl.tplString2(DAEDumpTpl.dumpDAE, fixedDae, funList)
          outString
        end

         #= This function prints the DAE to a string. =#
        function dumpElementsStr(els::List{<:DAE.Element}) ::String
              local outString::String

              outString = begin
                  local myStream::IOStream.IOStreamType
                  local str::String
                @match els begin
                  _  => begin
                      myStream = IOStream.create("dae", IOStream.LIST())
                      myStream = dumpElementsStream(els, myStream)
                      str = IOStream.string(myStream)
                    str
                  end
                end
              end
          outString
        end

         #= This function prints the algorithms to a string. =#
        function dumpAlgorithmsStr(algs::List{<:DAE.Element}) ::String
              local outString::String

              outString = begin
                  local myStream::IOStream.IOStreamType
                  local str::String
                @match algs begin
                  _  => begin
                      myStream = IOStream.create("algs", IOStream.LIST())
                      myStream = dumpAlgorithmsStream(algs, myStream)
                      str = IOStream.string(myStream)
                    str
                  end
                end
              end
          outString
        end

         #= This function prints the constraints to a string. =#
        function dumpConstraintsStr(constrs::List{<:DAE.Element}) ::String
              local outString::String

              outString = begin
                  local myStream::IOStream.IOStreamType
                  local str::String
                @match constrs begin
                  _  => begin
                      myStream = IOStream.create("constrs", IOStream.LIST())
                      myStream = dumpConstraintStream(constrs, myStream)
                      str = IOStream.string(myStream)
                    str
                  end
                end
              end
          outString
        end

         #= /************ IOStream based implementation ***************/ =#
         #= /************ IOStream based implementation ***************/ =#
         #= /************ IOStream based implementation ***************/ =#
         #= /************ IOStream based implementation ***************/ =#

         #= This function prints the DAE to a stream. =#
        function dumpStream(dae::DAE.DAElist, functionTree::DAE.FunctionTree, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local daelist::List{DAE.Element}
                  local funcs::List{DAE.Function}
                  local str::IOStream.IOStreamType
                @match (dae, functionTree, inStream) begin
                  (DAE.DAE(daelist), _, str)  => begin
                      funcs = DAEUtil.getFunctionList(functionTree)
                      funcs = sortFunctions(funcs)
                      str = ListUtil.fold(funcs, dumpFunctionStream, str)
                      str = IOStream.appendList(str, ListUtil.map(daelist, dumpExtObjClassStr))
                      str = ListUtil.fold(daelist, dumpCompElementStream, str)
                    str
                  end
                end
              end
          outStream
        end

         #=  returns sorted functions and record constructors in alphabetical order
          (mainly important for template based DAE unparser). =#
        function dumpFunctionList(functionTree::DAE.FunctionTree) ::functionList
              local funList::functionList

              funList = begin
                  local funcs::List{DAE.Function}
                @match functionTree begin
                  _  => begin
                      funcs = DAEUtil.getFunctionList(functionTree)
                      funcs = ListUtil.filter2OnTrue(funcs, isVisibleFunction, Flags.isSet(Flags.DISABLE_RECORD_CONSTRUCTOR_OUTPUT), Flags.isSet(Flags.INLINE_FUNCTIONS))
                      funcs = sortFunctions(funcs)
                      funList = DAEUtil.FUNCTION_LIST(funcs)
                    funList
                  end
                end
              end
          funList
        end

         #= Returns true if the given function should be visible in the flattened output. =#
        function isVisibleFunction(inFunc::DAE.Function, inHideRecordCons::Bool #= Hides record constructors if true. =#, inInliningEnabled::Bool #= Hides early inlined functions if true. =#) ::Bool
              local outIsVisible::Bool

              outIsVisible = begin
                  local cmt::Option{SCode.Comment}
                   #=  Hide functions with 'external \"builtin\"'.
                   =#
                @match (inFunc, inHideRecordCons, inInliningEnabled) begin
                  (DAE.FUNCTION(functions = DAE.FUNCTION_EXT(externalDecl = DAE.EXTERNALDECL(language = "builtin")) <| _), _, _)  => begin
                    false
                  end

                  (DAE.FUNCTION(path = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED(name = "OpenModelica"))), _, _)  => begin
                    false
                  end

                  (DAE.FUNCTION(inlineType = DAE.BUILTIN_EARLY_INLINE(__)), _, _)  => begin
                    false
                  end

                  (DAE.FUNCTION(inlineType = DAE.EARLY_INLINE(__)), _, true)  => begin
                    false
                  end

                  (DAE.FUNCTION(comment = cmt), _, _)  => begin
                    ! SCodeUtil.optCommentHasBooleanNamedAnnotation(cmt, "__OpenModelica_builtin")
                  end

                  (DAE.RECORD_CONSTRUCTOR(__), true, _)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  Hide functions in package OpenModelica.
               =#
               #=  Hide functions which should always be inlined.
               =#
               #=  Hide functions which should be inlined unless inlining is disabled.
               =#
               #=  Hide functions with annotation __OpenModelica_builtin = true.
               =#
               #=  Hide record constructors if requested.
               =#
          outIsVisible
        end

         #= Dumps components to a stream. =#
        function dumpCompElementStream(inElement::DAE.Element, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local n::String
                  local l::List{DAE.Element}
                  local c::Option{SCode.Comment}
                  local str::IOStream.IOStreamType
                @matchcontinue (inElement, inStream) begin
                  (DAE.COMP(ident = n, dAElist = l, comment = c), str)  => begin
                      str = IOStream.append(str, "class ")
                      str = IOStream.append(str, n)
                      str = IOStream.append(str, dumpCommentStr(c))
                      str = IOStream.append(str, "\\n")
                      str = dumpElementsStream(l, str)
                      str = IOStream.append(str, dumpClassAnnotationStr(c))
                      str = IOStream.append(str, "end ")
                      str = IOStream.append(str, n)
                      str = IOStream.append(str, ";\\n")
                    str
                  end

                  (_, str)  => begin
                    str
                  end
                end
              end
               #= /* LS: for non-COMPS, which are only FUNCTIONS at the moment */ =#
          outStream
        end

         #= Dump elements to a stream =#
        function dumpElementsStream(l::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local v::List{DAE.Element}
                  local o::List{DAE.Element}
                  local ie::List{DAE.Element}
                  local ia::List{DAE.Element}
                  local e::List{DAE.Element}
                  local a::List{DAE.Element}
                  local ca::List{DAE.Element}
                  local co::List{DAE.Element}
                  local sm::List{compWithSplitElements}
                  local comments::List{SCode.Comment}
                  local ann::Option{SCode.Annotation}
                @match (l, inStream) begin
                  (_, str)  => begin
                      (v, ie, ia, e, a, _, co, _, sm, comments) = DAEUtil.splitElements(l)
                      str = dumpCompWithSplitElementsStream(sm, str)
                      str = dumpVarsStream(v, false, str)
                      str = IOStream.append(str, if listEmpty(ie)
                            ""
                          else
                            "initial equation\\n"
                          end)
                      str = dumpInitialEquationsStream(ie, str)
                      str = dumpInitialAlgorithmsStream(ia, str)
                      str = IOStream.append(str, if listEmpty(e)
                            ""
                          else
                            "equation\\n"
                          end)
                      str = dumpEquationsStream(e, str)
                      str = dumpAlgorithmsStream(a, str)
                      str = IOStream.append(str, if listEmpty(co)
                            ""
                          else
                            "constraint\\n"
                          end)
                      str = dumpConstraintStream(co, str)
                      str = IOStream.append(str, stringAppendList(list(begin
                        @match cmt begin
                          SCode.COMMENT(annotation_ = ann && SOME(_))  => begin
                            SCodeDump.printCommentStr(SCode.COMMENT(ann, NONE()))
                          end

                          _  => begin
                              ""
                          end
                        end
                      end for cmt in comments)))
                    str
                  end
                end
              end
               #=  classify DAE
               =#
               #=  dump components with split elements (e.g., state machines)
               =#
               #=  dump variables
               =#
          outStream
        end

         #= Dump components with split elements (e.g., state machines) to a stream. =#
        function dumpCompWithSplitElementsStream(inCompLst::List{<:compWithSplitElements}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local name::String
                  local spltElems::splitElements
                  local comment::Option{SCode.Comment}
                  local cstr::String
                  local str::IOStream.IOStreamType
                  local xs::List{compWithSplitElements}
                  local v::List{DAE.Element}
                  local o::List{DAE.Element}
                  local ie::List{DAE.Element}
                  local ia::List{DAE.Element}
                  local e::List{DAE.Element}
                  local a::List{DAE.Element}
                  local ca::List{DAE.Element}
                  local co::List{DAE.Element}
                  local sm::List{compWithSplitElements}
                @match (inCompLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAEUtil.COMP_WITH_SPLIT(name = name, spltElems = spltElems, comment = comment) <| xs, str)  => begin
                      try
                        @match SOME(SCode.COMMENT(comment = SOME(cstr))) = comment
                        cstr = " \\" + cstr + "\\"
                      catch
                        cstr = ""
                      end
                      @match DAEUtil.SPLIT_ELEMENTS(v, ie, ia, e, a, co, _, _, sm) = spltElems
                      str = IOStream.append(str, name + cstr + "\\n")
                      str = dumpCompWithSplitElementsStream(sm, str)
                      str = dumpVarsStream(v, false, str)
                      str = IOStream.append(str, if listEmpty(ie)
                            ""
                          else
                            "initial equation\\n"
                          end)
                      str = dumpInitialEquationsStream(ie, str)
                      str = dumpInitialAlgorithmsStream(ia, str)
                      str = IOStream.append(str, if listEmpty(e)
                            ""
                          else
                            "equation\\n"
                          end)
                      str = dumpEquationsStream(e, str)
                      str = dumpAlgorithmsStream(a, str)
                      str = IOStream.append(str, if listEmpty(co)
                            ""
                          else
                            "constraint\\n"
                          end)
                      str = dumpConstraintStream(co, str)
                      str = IOStream.append(str, "end " + name + cstr + ";\\n")
                      str = dumpCompWithSplitElementsStream(xs, str)
                    str
                  end
                end
              end
          outStream
        end

         #= Dump algorithms to a stream. =#
        function dumpAlgorithmsStream(inElementLst::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local stmts::List{DAE.Statement}
                  local xs::List{DAE.Element}
                @matchcontinue (inElementLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts)) <| xs, str)  => begin
                      str = IOStream.append(str, "algorithm\\n")
                      str = IOStream.appendList(str, ListUtil.map(stmts, ppStatementStr))
                      str = dumpAlgorithmsStream(xs, str)
                    str
                  end

                  (_ <| xs, str)  => begin
                      str = dumpAlgorithmsStream(xs, str)
                    str
                  end
                end
              end
          outStream
        end

         #= Dump initialalgorithms to a stream. =#
        function dumpInitialAlgorithmsStream(inElementLst::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local stmts::List{DAE.Statement}
                  local xs::List{DAE.Element}
                @matchcontinue (inElementLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts)) <| xs, str)  => begin
                      str = IOStream.append(str, "initial algorithm\\n")
                      str = IOStream.appendList(str, ListUtil.map(stmts, ppStatementStr))
                      str = dumpInitialAlgorithmsStream(xs, str)
                    str
                  end

                  (_ <| xs, str)  => begin
                      str = dumpInitialAlgorithmsStream(xs, str)
                    str
                  end
                end
              end
          outStream
        end

         #= Dump equations to a stream. =#
        function dumpEquationsStream(inElementLst::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local s1::String
                  local s2::String
                  local s3::String
                  local s::String
                  local sourceStr::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e::DAE.Exp
                  local conds::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local xs::List{DAE.Element}
                  local xs1::List{DAE.Element}
                  local xs2::List{DAE.Element}
                  local tb::List{List{DAE.Element}}
                  local c::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local str::IOStream.IOStreamType
                  local el::DAE.Element
                  local path::Absyn.Path
                  local dims::DAE.Dimensions
                  local src::DAE.ElementSource
                @match (inElementLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAE.EQUATION(exp = e1, scalar = e2, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      str = IOStream.append(str, "  " + ComponentReference.printComponentRefStr(cr1) + " = " + ComponentReference.printComponentRefStr(cr2) + sourceStr + ";\\n")
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.ARRAY_EQUATION(dimension = dims, exp = e1, array = e2, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      s3 = if Config.typeinfo()
                            Types.printDimensionsStr(dims)
                          else
                            ""
                          end
                      s3 = if Config.typeinfo()
                            " /* array equation [" + s3 + "] */"
                          else
                            ""
                          end
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, s3, sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.DEFINE(componentRef = c, exp = e, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ComponentReference.printComponentRefStr(c)
                      s2 = ExpressionDump.printExpStr(e)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.ASSERT(condition = e1, message = e2, level = DAE.ENUM_LITERAL(index = 1), source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  assert(", s1, ",", s2, ")", sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.TERMINATE(message = e1, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = IOStream.appendList(str, list("  terminate(", s1, ")", sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.FOR_EQUATION(iter = s, range = e1, equations = xs1, source = src) <| xs, str)  => begin
                      _ = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = IOStream.appendList(str, list("  for ", s, " in ", s1, " loop\\n"))
                      str = dumpEquationsStream(xs1, str)
                      str = IOStream.appendList(str, list("  end for;\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.IF_EQUATION(condition1 =  nil(), equations2 =  nil(), equations3 =  nil()) <| _, str)  => begin
                    str
                  end

                  (DAE.IF_EQUATION(condition1 = e <| conds, equations2 = xs1 <| tb, equations3 =  nil(), source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      str = IOStream.append(str, "  if ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(e))
                      str = IOStream.append(str, " then\\n")
                      str = dumpEquationsStream(xs1, str)
                      str = dumpIfEquationsStream(conds, tb, str)
                      str = IOStream.append(str, "  end if")
                      str = IOStream.append(str, sourceStr + ";\\n")
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.IF_EQUATION(condition1 = e <| conds, equations2 = xs1 <| tb, equations3 = xs2, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      str = IOStream.append(str, "  if ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(e))
                      str = IOStream.append(str, " then\\n")
                      str = dumpEquationsStream(xs1, str)
                      str = dumpIfEquationsStream(conds, tb, str)
                      str = IOStream.append(str, "  else\\n")
                      str = dumpEquationsStream(xs2, str)
                      str = IOStream.append(str, "  end if" + sourceStr + ";\\n")
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.WHEN_EQUATION(condition = e, equations = xs1, elsewhen_ = SOME(el), source = src) <| xs, str)  => begin
                      _ = getSourceInformationStr(src)
                      str = IOStream.append(str, "when ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(e))
                      str = IOStream.append(str, " then\\n")
                      str = dumpEquationsStream(xs1, str)
                      str = IOStream.append(str, " else")
                      str = dumpEquationsStream(_cons(el, xs), str)
                    str
                  end

                  (DAE.WHEN_EQUATION(condition = e, equations = xs1, elsewhen_ = NONE(), source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      str = IOStream.append(str, "  when ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(e))
                      str = IOStream.append(str, " then\\n")
                      str = dumpEquationsStream(xs1, str)
                      str = IOStream.append(str, "  end when" + sourceStr + ";\\n")
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.REINIT(componentRef = cr, exp = e, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s = ComponentReference.printComponentRefStr(cr)
                      s1 = ExpressionDump.printExpStr(e)
                      str = IOStream.appendList(str, list("  reinit(", s, ",", s1, ")", sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.NORETCALL(exp = e, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e)
                      str = IOStream.appendList(str, list("  ", s1, sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (_ <| xs, str)  => begin
                      str = IOStream.append(str, "  /* unhandled equation in DAEDump.dumpEquationsStream FIXME! */\\n")
                      str = dumpEquationsStream(xs, str)
                    str
                  end
                end
              end
          outStream
        end

         #=  =#
        function dumpIfEquationsStream(iconds::List{<:DAE.Exp}, itbs::List{<:List{<:DAE.Element}}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local c::DAE.Exp
                  local tb::List{DAE.Element}
                  local str::IOStream.IOStreamType
                  local conds::List{DAE.Exp}
                  local tbs::List{List{DAE.Element}}
                @match (iconds, itbs, inStream) begin
                  ( nil(),  nil(), str)  => begin
                    str
                  end

                  (c <| conds, tb <| tbs, str)  => begin
                      str = IOStream.append(str, "  elseif ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(c))
                      str = IOStream.append(str, " then\\n")
                      str = dumpEquationsStream(tb, str)
                      str = dumpIfEquationsStream(conds, tbs, str)
                    str
                  end
                end
              end
          outStream
        end

         #= Dump initial equations to a stream. =#
        function dumpInitialEquationsStream(inElementLst::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local s1::String
                  local s2::String
                  local sourceStr::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local xs::List{DAE.Element}
                  local xs1::List{DAE.Element}
                  local xs2::List{DAE.Element}
                  local trueBranches::List{List{DAE.Element}}
                  local c::DAE.ComponentRef
                  local str::IOStream.IOStreamType
                  local conds::List{DAE.Exp}
                  local src::DAE.ElementSource
                @matchcontinue (inElementLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAE.INITIALEQUATION(exp1 = e1, exp2 = e2) <| xs, str)  => begin
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, ";\\n"))
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2) <| xs, str)  => begin
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, ";\\n"))
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2) <| xs, str)  => begin
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, ";\\n"))
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIALDEFINE(componentRef = c, exp = e) <| xs, str)  => begin
                      s1 = ComponentReference.printComponentRefStr(c)
                      s2 = ExpressionDump.printExpStr(e)
                      str = IOStream.appendList(str, list("  ", s1, " = ", s2, ";\\n"))
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_IF_EQUATION(condition1 = e <| conds, equations2 = xs1 <| trueBranches, equations3 = xs2) <| xs, str)  => begin
                      str = IOStream.append(str, "  if ")
                      str = IOStream.append(str, ExpressionDump.printExpStr(e))
                      str = IOStream.append(str, " then\\n")
                      str = dumpInitialEquationsStream(xs1, str)
                      str = dumpIfEquationsStream(conds, trueBranches, str)
                      str = IOStream.append(str, "  else\\n")
                      str = dumpInitialEquationsStream(xs2, str)
                      str = IOStream.append(str, "  end if;\\n")
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_NORETCALL(exp = e) <| xs, str)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                      str = IOStream.appendList(str, list("  ", s1, ";\\n"))
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_ASSERT(condition = e1, message = e2, level = DAE.ENUM_LITERAL(index = 1), source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = IOStream.appendList(str, list("  assert(", s1, ",", s2, ")", sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (DAE.INITIAL_TERMINATE(message = e1, source = src) <| xs, str)  => begin
                      sourceStr = getSourceInformationStr(src)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = IOStream.appendList(str, list("  terminate(", s1, ")", sourceStr, ";\\n"))
                      str = dumpEquationsStream(xs, str)
                    str
                  end

                  (_ <| xs, str)  => begin
                      str = dumpInitialEquationsStream(xs, str)
                    str
                  end
                end
              end
          outStream
        end

         #= Dump constraints to a stream. =#
        function dumpConstraintStream(inElementLst::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local exps::List{DAE.Exp}
                  local xs::List{DAE.Element}
                @matchcontinue (inElementLst, inStream) begin
                  ( nil(), str)  => begin
                    str
                  end

                  (DAE.CONSTRAINT(constraints = DAE.CONSTRAINT_EXPS(constraintLst = exps)) <| xs, str)  => begin
                      str = IOStream.append(str, "  ")
                      str = IOStream.append(str, stringDelimitList(ListUtil.map(exps, ExpressionDump.printExpStr), ";\\n  "))
                      str = IOStream.append(str, ";\\n")
                      str = dumpConstraintStream(xs, str)
                    str
                  end

                  (_ <| xs, str)  => begin
                      str = dumpConstraintStream(xs, str)
                    str
                  end
                end
              end
               #=  initial indenttion.
               =#
               #= add the delimiter to the last element too. also if there is just 1 element in the 'exps' list.
               =#
          outStream
        end

         #=
        Author BZ
        print a DAE.DAEList to a string =#
        function dumpDAEElementsStr(d::DAE.DAElist) ::String
              local str::String

              str = begin
                  local l::List{DAE.Element}
                  local myStream::IOStream.IOStreamType
                @match d begin
                  DAE.DAE(elementLst = l)  => begin
                      myStream = IOStream.create("", IOStream.LIST())
                      myStream = dumpElementsStream(l, myStream)
                      str = IOStream.string(myStream)
                    str
                  end
                end
              end
          str
        end

         #= Dump variables to a string. =#
        function dumpVarsStream(inElementLst::List{<:DAE.Element}, printTypeDimension::Bool #= use true here when printing components in functions as these are not vectorized! Otherwise, use false =#, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local first::DAE.Element
                  local rest::List{DAE.Element}
                   #=  handle nothingness
                   =#
                @match (inElementLst, printTypeDimension, inStream) begin
                  ( nil(), _, _)  => begin
                    inStream
                  end

                  (first <| rest, _, str)  => begin
                      str = dumpVarStream(first, printTypeDimension, str)
                      str = dumpVarsStream(rest, printTypeDimension, str)
                    str
                  end
                end
              end
               #=  the usual case
               =#
          outStream
        end

        function daeTypeStr(inType::DAE.Type) ::String
              local outTypeStr::String

              local typeAttrStr::String

              (outTypeStr, typeAttrStr) = printTypeStr(inType)
              if typeAttrStr != ""
                outTypeStr = outTypeStr + " " + typeAttrStr
              end
          outTypeStr
        end

        function printTypeStr(inType::DAE.Type) ::Tuple{String, String}
              local outTypeAttrStr::String
              local outTypeStr::String

              local ty::DAE.Type
              local ty_vars::List{DAE.Var}

              (ty, ty_vars) = Types.stripTypeVars(inType)
              outTypeStr = unparseType(ty)
              outTypeAttrStr = ListUtil.toString(ty_vars, Types.unparseVarAttr, "", "(", ", ", ")", false)
          (outTypeStr, outTypeAttrStr)
        end

         #= dumps the DAE.CallAttributes =#
        function dumpCallAttr(ca::DAE.CallAttributes)
              local tpl::Bool
              local bi::Bool
              local impure_::Bool
              local isFunc::Bool
              local iType::DAE.InlineType
              local ty::DAE.Type
              local tailCall::DAE.TailCall
              local s1::String
              local s2::String

              @match DAE.CALL_ATTR(ty = ty, tuple_ = tpl, builtin = bi, isImpure = impure_, isFunctionPointerCall = isFunc, inlineType = iType, tailCall = tailCall) = ca
              print("Call attributes: \\n----------------------\\n")
              (s1, s2) = printTypeStr(ty)
              print("DAE-type: " + s1 + "\\n")
              print("DAE-type attributes :" + s2 + "\\n")
              print("tuple_: " + boolString(tpl) + " builtin: " + boolString(bi) + " impure: " + boolString(impure_) + " isFunctionPointerCall: " + boolString(isFunc) + "\\n\\n")
        end

        function dumpVarBindingStr(inBinding::Option{<:DAE.Exp}) ::String
              local outString::String

              outString = begin
                  local exp::DAE.Exp
                  local bind_str::String
                @match inBinding begin
                  SOME(exp)  => begin
                      bind_str = ExpressionDump.printExpStr(exp)
                    " = " + bind_str
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= Dump var to a stream. =#
        function dumpVarStream(inElement::DAE.Element, printTypeDimension::Bool #= use true here when printing components in functions as these are not vectorized! Otherwise, use false =#, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local final_str::String
                  local kind_str::String
                  local dir_str::String
                  local ty_str::String
                  local ty_vars_str::String
                  local dim_str::String
                  local name_str::String
                  local vis_str::String
                  local par_str::String
                  local cmt_str::String
                  local attr_str::String
                  local binding_str::String
                  local id::DAE.ComponentRef
                  local kind::DAE.VarKind
                  local dir::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local vis::DAE.VarVisibility
                  local ty::DAE.Type
                  local attr::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local binding::Option{DAE.Exp}
                  local dims::DAE.InstDims
                  local str::IOStream.IOStreamType
                  local ty_vars::List{DAE.Var}
                @matchcontinue (inElement, printTypeDimension, inStream) begin
                  (DAE.VAR(componentRef = id, kind = kind, direction = dir, parallelism = prl, protection = vis, ty = ty, dims = dims, binding = binding, variableAttributesOption = attr, comment = cmt), _, str)  => begin
                      final_str = if DAEUtil.getFinalAttr(attr)
                            "final "
                          else
                            ""
                          end
                      kind_str = dumpKindStr(kind)
                      dir_str = dumpDirectionStr(dir)
                      (ty_str, ty_vars_str) = printTypeStr(ty)
                      dim_str = unparseDimensions(dims, printTypeDimension)
                      name_str = ComponentReference.printComponentRefStr(id)
                      vis_str = dumpVarVisibilityStr(vis)
                      par_str = dumpVarParallelismStr(prl)
                      cmt_str = dumpCommentAnnotationStr(cmt)
                      attr_str = dumpVariableAttributesStr(attr)
                      binding_str = dumpVarBindingStr(binding)
                      str = IOStream.appendList(str, list("  ", vis_str, final_str, par_str, kind_str, dir_str, ty_str, dim_str, " ", name_str, ty_vars_str, attr_str, binding_str, cmt_str, ";\\n"))
                    str
                  end

                  _  => begin
                      inStream
                  end
                end
              end
          outStream
        end

         #= Dump algorithm to a stream =#
        function dumpAlgorithmStream(inElement::DAE.Element, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local stmts::List{DAE.Statement}
                @matchcontinue (inElement, inStream) begin
                  (DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts)), str)  => begin
                      str = IOStream.append(str, "algorithm\\n")
                      str = ListUtil.fold(stmts, ppStatementStream, str)
                    str
                  end

                  (_, str)  => begin
                    str
                  end
                end
              end
          outStream
        end

         #= Dump algorithm to a stream =#
        function dumpInitialAlgorithmStream(inElement::DAE.Element, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local str::IOStream.IOStreamType
                  local stmts::List{DAE.Statement}
                @matchcontinue (inElement, inStream) begin
                  (DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = stmts)), str)  => begin
                      str = IOStream.append(str, "initial algorithm\\n")
                      str = ListUtil.fold(stmts, ppStatementStream, str)
                    str
                  end

                  (_, str)  => begin
                    str
                  end
                end
              end
          outStream
        end

         #= Prettyprint an algorithm statement to a string. =#
        function ppStatementStream(alg::DAE.Statement, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              local tmp::String
              local hnd::ModelicaInteger

              hnd = Print.saveAndClearBuf()
              ppStatement(alg)
              outStream = IOStream.append(inStream, Print.getString())
              Print.restoreBuf(hnd)
          outStream
        end

        function dumpFunctionTree(inFunctionTree::DAE.FunctionTree, inHeading::String)
              print("\\n" + inHeading + "\\n========================================\\n")
              for fnc in sortFunctions(DAEUtil.getFunctionList(inFunctionTree))
                print(dumpFunctionStr(fnc))
              end
        end

         #= Dump function to a string. =#
        function dumpFunctionStr(inElement::DAE.Function) ::String
              local outString::String

              outString = begin
                  local s::String
                  local hnd::ModelicaInteger
                @matchcontinue inElement begin
                  _  => begin
                      hnd = Print.saveAndClearBuf()
                      dumpFunction(inElement)
                      s = Print.getString()
                      Print.restoreBuf(hnd)
                    s
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= Dump external object class to a string. =#
        function dumpExtObjClassStr(inElement::DAE.Element) ::String
              local outString::String

              outString = begin
                  local s::String
                  local hnd::ModelicaInteger
                @matchcontinue inElement begin
                  DAE.EXTOBJECTCLASS(__)  => begin
                      hnd = Print.saveAndClearBuf()
                      dumpExtObjectClass(inElement)
                      s = Print.getString()
                      Print.restoreBuf(hnd)
                    s
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= Dump function to a stream =#
        function dumpFunctionStream(inElement::DAE.Function, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = begin
                  local fstr::String
                  local ext_decl_str::String
                  local impureStr::String
                  local ann_str::String
                  local fpath::Absyn.Path
                  local daeElts::List{DAE.Element}
                  local t::DAE.Type
                  local tp::DAE.Type
                  local inlineType::DAE.InlineType
                  local str::IOStream.IOStreamType
                  local c::Option{SCode.Comment}
                  local ext_decl::DAE.ExternalDecl
                  local isImpure::Bool
                @matchcontinue (inElement, inStream) begin
                  (DAE.FUNCTION(path = fpath, inlineType = inlineType, functions = DAE.FUNCTION_DEF(body = daeElts) <| _, type_ = t, isImpure = isImpure, comment = c), str)  => begin
                      str = IOStream.append(str, dumpParallelismStr(t))
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      impureStr = if isImpure
                            "impure "
                          else
                            ""
                          end
                      str = IOStream.append(str, impureStr)
                      str = IOStream.append(str, "function ")
                      str = IOStream.append(str, fstr)
                      str = IOStream.append(str, dumpInlineTypeStr(inlineType))
                      str = IOStream.append(str, dumpCommentStr(c))
                      str = IOStream.append(str, "\\n")
                      str = dumpFunctionElementsStream(daeElts, str)
                      str = IOStream.append(str, dumpClassAnnotationStr(c))
                      str = IOStream.append(str, "end ")
                      str = IOStream.append(str, fstr)
                      str = IOStream.append(str, ";\\n\\n")
                    str
                  end

                  (DAE.FUNCTION(functions = DAE.FUNCTION_EXT(externalDecl = DAE.EXTERNALDECL(language = "builtin")) <| _), str)  => begin
                    str
                  end

                  (DAE.FUNCTION(path = fpath, inlineType = inlineType, functions = DAE.FUNCTION_EXT(body = daeElts, externalDecl = ext_decl) <| _, isImpure = isImpure, comment = c), str)  => begin
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      impureStr = if isImpure
                            "impure "
                          else
                            ""
                          end
                      str = IOStream.append(str, impureStr)
                      str = IOStream.append(str, "function ")
                      str = IOStream.append(str, fstr)
                      str = IOStream.append(str, dumpInlineTypeStr(inlineType))
                      str = IOStream.append(str, dumpCommentStr(c))
                      str = IOStream.append(str, "\\n")
                      str = dumpFunctionElementsStream(daeElts, str)
                      ext_decl_str = dumpExtDeclStr(ext_decl)
                      ann_str = dumpClassAnnotationStr(c)
                      str = IOStream.appendList(str, list("\\n  ", ext_decl_str, "\\n", ann_str, "end ", fstr, ";\\n\\n"))
                    str
                  end

                  (DAE.RECORD_CONSTRUCTOR(path = fpath, type_ = tp), str)  => begin
                      @match false = Flags.isSet(Flags.DISABLE_RECORD_CONSTRUCTOR_OUTPUT)
                      fstr = AbsynUtil.pathStringNoQual(fpath)
                      str = IOStream.append(str, "function ")
                      str = IOStream.append(str, fstr)
                      str = IOStream.append(str, " \\Automatically generated record constructor for " + fstr + "\\\\n")
                      str = IOStream.append(str, printRecordConstructorInputsStr(tp))
                      str = IOStream.append(str, "  output " + AbsynUtil.pathLastIdent(fpath) + " res;\\n")
                      str = IOStream.append(str, "end ")
                      str = IOStream.append(str, fstr)
                      str = IOStream.append(str, ";\\n\\n")
                    str
                  end

                  (_, str)  => begin
                    str
                  end
                end
              end
          outStream
        end

         #= Dump function elements to a stream. =#
        function dumpFunctionElementsStream(l::List{<:DAE.Element}, inStream::IOStream.IOStreamType) ::IOStream.IOStreamType
              local outStream::IOStream.IOStreamType

              outStream = dumpVarsStream(l, true, inStream)
              outStream = ListUtil.fold(l, dumpAlgorithmStream, outStream)
          outStream
        end

        function unparseVarKind(inVarKind::DAE.VarKind) ::String
              local outString::String

              outString = begin
                @match inVarKind begin
                  DAE.VARIABLE(__)  => begin
                    ""
                  end

                  DAE.PARAM(__)  => begin
                    "parameter"
                  end

                  DAE.CONST(__)  => begin
                    "const"
                  end

                  DAE.DISCRETE(__)  => begin
                    "discrete"
                  end
                end
              end
          outString
        end

        function unparseVarDirection(inVarDirection::DAE.VarDirection) ::String
              local outString::String

              outString = begin
                @match inVarDirection begin
                  DAE.BIDIR(__)  => begin
                    ""
                  end

                  DAE.INPUT(__)  => begin
                    "input"
                  end

                  DAE.OUTPUT(__)  => begin
                    "output"
                  end
                end
              end
          outString
        end

        function unparseVarInnerOuter(io::DAE.VarInnerOuter) ::String
              local str::String

              str = begin
                @match io begin
                  DAE.VarInnerOuter.INNER(__)  => begin
                    "inner"
                  end

                  DAE.VarInnerOuter.OUTER(__)  => begin
                    "outer"
                  end

                  DAE.VarInnerOuter.INNER_OUTER(__)  => begin
                    "inner outer"
                  end

                  _  => begin
                      ""
                  end
                end
              end
          str
        end

         #= @author: adrpo
         display the source information as string =#
        function getSourceInformationStr(inSource::DAE.ElementSource) ::String
              local outStr::String

              outStr = begin
                  local i::SourceInfo
                  local po::List{Absyn.Within}
                  local iol::List{Option{DAE.ComponentRef}}
                  local ceol::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local tl::List{Absyn.Path}
                  local op::List{DAE.SymbolicOperation}
                  local cmt::List{SCode.Comment}
                  local str::String
                @matchcontinue inSource begin
                  _  => begin
                      @match false = Flags.isSet(Flags.SHOW_EQUATION_SOURCE)
                    ""
                  end

                  DAE.SOURCE(_, po, _, ceol, _, _, cmt)  => begin
                      str = cmtListToString(cmt)
                      str = str + " /* models: {" + stringDelimitList(ListUtil.map(po, withinString), ", ") + "}" + " connects: {" + stringDelimitList(connectsStr(ceol), ", ") + "} */"
                    str
                  end
                end
              end
          outStr
        end

        function connectsStr(inLst::List{<:Tuple{<:DAE.ComponentRef, DAE.ComponentRef}}) ::List{String}
              local outStr::List{String}

              outStr = begin
                  local rest::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
                  local slst::List{String}
                  local str::String
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                @matchcontinue inLst begin
                   nil()  => begin
                    nil
                  end

                  (c1, c2) <|  nil()  => begin
                      str = ComponentReference.printComponentRefStr(c1) + "," + ComponentReference.printComponentRefStr(c2)
                      str = "connect(" + str + ")"
                    list(str)
                  end

                  (c1, c2) <| rest  => begin
                      str = ComponentReference.printComponentRefStr(c1) + "," + ComponentReference.printComponentRefStr(c2)
                      str = "connect(" + str + ")"
                      slst = connectsStr(rest)
                    _cons(str, slst)
                  end
                end
              end
          outStr
        end

        function withinString(w::Absyn.Within) ::String
              local str::String

              str = begin
                  local p1::Absyn.Path
                @match w begin
                  Absyn.TOP(__)  => begin
                    "TOP"
                  end

                  Absyn.WITHIN(p1)  => begin
                    AbsynUtil.pathString(p1)
                  end
                end
              end
          str
        end

        function cmtListToString(inCmtLst::List{<:SCode.Comment}) ::String
              local outStr::String

              outStr = begin
                  local c::SCode.Comment
                  local rest::List{SCode.Comment}
                  local str::String
                @matchcontinue inCmtLst begin
                   nil()  => begin
                    ""
                  end

                  c <|  nil()  => begin
                      str = dumpCommentAnnotationStr(SOME(c))
                    str
                  end

                  c <| rest  => begin
                      str = dumpCommentAnnotationStr(SOME(c))
                      str = str + " " + cmtListToString(rest)
                    str
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outStr
        end

        function clockKindString(cK::DAE.ClockKind) ::String
              local sOut::String

              sOut = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                @match cK begin
                  DAE.INFERRED_CLOCK(__)  => begin
                    "Inferred Clock"
                  end

                  DAE.INTEGER_CLOCK(intervalCounter = e1, resolution = e2)  => begin
                    "Integer Clock(" + ExpressionDump.printExpStr(e1) + "; " + ExpressionDump.printExpStr(e2) + ")"
                  end

                  DAE.REAL_CLOCK(interval = e1)  => begin
                    "Real Clock(" + ExpressionDump.printExpStr(e1) + ")"
                  end

                  DAE.BOOLEAN_CLOCK(condition = e1, startInterval = e2)  => begin
                    "Boolean Clock(" + ExpressionDump.printExpStr(e1) + "; " + ExpressionDump.printExpStr(e2) + ")"
                  end

                  DAE.SOLVER_CLOCK(c = e1, solverMethod = e2)  => begin
                    "Solver Clock(" + ExpressionDump.printExpStr(e1) + "; " + ExpressionDump.printExpStr(e2) + ")"
                  end
                end
              end
          sOut
        end

         #= Dump equation to a string.For debug purposes. =#
        function dumpDebugElementStr(inElement::DAE.Element) ::String
              local outString::String

              outString = begin
                  local path::Absyn.Path
                  local s1::String
                  local s2::String
                  local s3::String
                  local s4::String
                  local s5::String
                  local str::String
                  local sourceStr::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local c::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local es::List{DAE.Exp}
                  local elst::List{DAE.Element}
                  local src::DAE.ElementSource
                  local cmt::List{SCode.Comment}
                @matchcontinue inElement begin
                  DAE.VAR(componentRef = c)  => begin
                      s1 = ComponentReference.printComponentRefStr(c)
                      str = stringAppendList(list("VAR:  ", s1, ";\\n"))
                    str
                  end

                  DAE.DEFINE(componentRef = c, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ComponentReference.printComponentRefStr(c)
                      str = stringAppend(s1, sourceStr + ";\\n")
                    str
                  end

                  DAE.INITIALDEFINE(componentRef = c, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ComponentReference.printComponentRefStr(c)
                      str = stringAppend(s1, sourceStr + ";\\n")
                    str
                  end

                  DAE.EQUATION(exp = e1, scalar = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("  ", s1, " = ", s2, sourceStr, ";\\n"))
                    str
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ComponentReference.printComponentRefStr(cr1)
                      s2 = ComponentReference.printComponentRefStr(cr2)
                      str = stringAppendList(list("EQUEQUATION  ", s1, " = ", s2, sourceStr, ";\\n"))
                    str
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "ARRAY_EQUATION  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "INITIAL_ARRAY_EQUATION  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "COMPLEX_EQUATION  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = "INITIAL_COMPLEX_EQUATION  " + s1 + " = " + s2 + sourceStr + ";\\n"
                    str
                  end

                  DAE.WHEN_EQUATION(condition = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("WHEN_EQUATION:  ", s1, sourceStr, ";\\n"))
                    str
                  end

                  DAE.IF_EQUATION(source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      str = stringAppendList(list("IF_EQUATION:  ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.INITIAL_IF_EQUATION(source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      str = stringAppendList(list("INITIAL_IF_EQUATION:  ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("INITIALEQUATION  ", s1, " = ", s2, sourceStr, ";\\n"))
                    str
                  end

                  DAE.ALGORITHM(source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      str = stringAppendList(list("ALGO  ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.INITIALALGORITHM(source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      str = stringAppendList(list("INITIALALGORITHM  ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.COMP(source = src, dAElist = elst)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = stringDelimitList(ListUtil.map(elst, DAEDump.dumpDebugElementStr), "\\n")
                      str = stringAppendList(list("COMP  ", s1, sourceStr, ";\\n"))
                    str
                  end

                  DAE.EXTOBJECTCLASS(path = path, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = AbsynUtil.pathString(path)
                      str = stringAppendList(list("EXTOBJ  ", s1, "  ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.ASSERT(condition = e1, message = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("  assert(", s1, ",", s2, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      s2 = ExpressionDump.printExpStr(e2)
                      str = stringAppendList(list("  /* initial */ assert(", s1, ",", s2, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.TERMINATE(message = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("  terminate(", s1, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.INITIAL_TERMINATE(message = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("  /* initial */ terminate(", s1, ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.REINIT(source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      str = stringAppendList(list("  reinit(", ") ", sourceStr, ";\\n"))
                    str
                  end

                  DAE.NORETCALL(exp = e1, source = src)  => begin
                      cmt = ElementSource.getCommentsFromSource(src)
                      sourceStr = cmtListToString(cmt)
                      s1 = ExpressionDump.printExpStr(e1)
                      str = stringAppendList(list("  ", s1, sourceStr, ";\\n"))
                    str
                  end

                  _  => begin
                      "#UNKNOWN_EQUATION#"
                  end
                end
              end
          outString
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

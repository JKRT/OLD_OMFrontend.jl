module Ceval


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    ReductionOperator = Function

    HandlerFunc = Function

    HandlerFunc = Function

    Func = Function

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

        @importDBG Absyn

        @importDBG AbsynUtil

        @importDBG DAE

        @importDBG FCore

        @importDBG FCoreUtil

        @importDBG FGraphUtil

        @importDBG FNode

        @importDBG InstTypes

        @importDBG Values

        @importDBG Lookup
         #=  protected @importDBGs
         =#

        @importDBG AvlTreeStringString

        #@importDBG BackendInterface

        @importDBG CrefForHashTable

        @importDBG Config

        @importDBG Debug

        @importDBG Error

        @importDBG Expression

        @importDBG ExpressionSimplify

        @importDBG Flags

        @importDBG InstBinding

        @importDBG InstUtil

        @importDBG ListUtil

        @importDBG ModelicaExternalC

        @importDBG Prefix

        @importDBG Print

        @importDBG SCode
        @importDBG SCodeUtil

        @importDBG Static

        @importDBG System

        @importDBG Types

        @importDBG Util

        @importDBG ValuesUtil

        @importDBG ClassInf

        @importDBG Global

        import MetaModelica.Dangerous.listReverseInPlace

         #=
          This function is used when the value of a constant expression is
          needed.  It takes an environment and an expression and calculates
          its value.
          The third argument indicates whether the evaluation is performed in the
          interactive environment (implicit instantiation), in which case function
          calls are evaluated.
          The last argument is an optional dimension. =#
        function ceval(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg = Absyn.NO_MSG(), numIter::ModelicaInteger = 0 #= Maximum recursion depth =#) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = cevalWork1(inCache, inEnv, inExp, inBoolean, inMsg, numIter, numIter > Global.recursionDepthLimit)
          (outCache, outValue)
        end

        function cevalWork1(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger #= Maximum recursion depth =#, iterReached::Bool) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local info::SourceInfo
                  local str1::String
                  local str2::String
                  local str3::String
                @match (inCache, inEnv, inExp, inBoolean, inMsg, numIter, iterReached) begin
                  (_, _, _, _, _, _, false)  => begin
                      (outCache, outValue) = cevalWork2(inCache, inEnv, inExp, inBoolean, inMsg, numIter)
                    (outCache, outValue)
                  end

                  (_, _, _, _, Absyn.MSG(info = info), _, true)  => begin
                      str1 = intString(Global.recursionDepthLimit)
                      str2 = CrefForHashTable.printExpStr(inExp)
                      Error.addSourceMessage(Error.RECURSION_DEPTH_WARNING, list(str1, str2, FGraphUtil.printGraphPathStr(inEnv)), info)
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #=
          This function is used when the value of a constant expression is
          needed.  It takes an environment and an expression and calculates
          its value.
          The third argument indicates whether the evaluation is performed in the
          interactive environment (implicit instantiation), in which case function
          calls are evaluated.
          The last argument is an optional dimension. =#
        function cevalWork2(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local start_1::ModelicaInteger
                  local stop_1::ModelicaInteger
                  local step_1::ModelicaInteger
                  local i::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local indx::ModelicaInteger
                  local index::ModelicaInteger
                  local lhvReal::ModelicaReal
                  local rhvReal::ModelicaReal
                  local sum::ModelicaReal
                  local r::ModelicaReal
                  local realStart1::ModelicaReal
                  local realStop1::ModelicaReal
                  local realStep1::ModelicaReal
                  local str::String
                  local lhvStr::String
                  local rhvStr::String
                  local s::String
                  local foldName::String
                  local resultName::String
                  local impl::Bool
                  local b::Bool
                  local b_1::Bool
                  local lhvBool::Bool
                  local rhvBool::Bool
                  local resBool::Bool
                  local bstart::Bool
                  local bstop::Bool
                  local exp_1::Absyn.Exp
                  local exp::Absyn.Exp
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local elt_1::Absyn.Element
                  local elt::Absyn.Element
                  local c::Absyn.CodeNode
                  local es_1::List{Values.Value}
                  local elts::List{Values.Value}
                  local vallst::List{Values.Value}
                  local vlst1::List{Values.Value}
                  local vlst2::List{Values.Value}
                  local reslst::List{Values.Value}
                  local aval::List{Values.Value}
                  local rhvals::List{Values.Value}
                  local lhvals::List{Values.Value}
                  local arr::List{Values.Value}
                  local arr_1::List{Values.Value}
                  local ivals::List{Values.Value}
                  local rvals::List{Values.Value}
                  local vals::List{Values.Value}
                  local es::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local expll::List{List{DAE.Exp}}
                  local v::Values.Value
                  local newval::Values.Value
                  local value::Values.Value
                  local sval::Values.Value
                  local elt1::Values.Value
                  local elt2::Values.Value
                  local v_1::Values.Value
                  local lhs_1::Values.Value
                  local rhs_1::Values.Value
                  local resVal::Values.Value
                  local lhvVal::Values.Value
                  local rhvVal::Values.Value
                  local lh::DAE.Exp
                  local rh::DAE.Exp
                  local e::DAE.Exp
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local start::DAE.Exp
                  local stop::DAE.Exp
                  local step::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local cond::DAE.Exp
                  local funcpath::Absyn.Path
                  local name::Absyn.Path
                  local recName::Absyn.Path
                  local relop::DAE.Operator
                  local cache::FCore.Cache
                  local expExp::DAE.Exp
                  local dims::List{ModelicaInteger}
                  local arrayDims::DAE.Dimensions
                  local cr::DAE.ComponentRef
                  local fieldNames::List{String}
                  local n::List{String}
                  local names::List{String}
                  local t::DAE.Type
                  local daeExp::DAE.Exp
                  local path::Absyn.Path
                  local ov::Option{Values.Value}
                  local foldExp::Option{DAE.Exp}
                  local ty::DAE.Type
                  local tys::List{DAE.Type}
                  local iterators::DAE.ReductionIterators
                  local valMatrix::List{List{Values.Value}}
                  local info::SourceInfo
                  local orderd::List{Values.Value}
                  local comp::List{String}
                  local ck::DAE.ClockKind
                  local iterType::Absyn.ReductionIterType
                   #=  uncomment for debugging
                   =#
                   #=  case (cache,env,inExp,_,_,_)
                   =#
                   #=    equation print(\"Ceval.ceval: \" + CrefForHashTable.printExpStr(inExp) + \" in env: \" + FGraphUtil.printGraphPathStr(env) + \"\\n\");
                   =#
                   #=    then fail();
                   =#
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inMsg, numIter) begin
                  (cache, _, DAE.ICONST(integer = i), _, _, _)  => begin
                    (cache, Values.INTEGER(i))
                  end

                  (cache, _, DAE.RCONST(real = r), _, _, _)  => begin
                    (cache, Values.REAL(r))
                  end

                  (cache, _, DAE.SCONST(string = s), _, _, _)  => begin
                    (cache, Values.STRING(s))
                  end

                  (cache, _, DAE.BCONST(bool = b), _, _, _)  => begin
                    (cache, Values.BOOL(b))
                  end

                  (cache, _, DAE.ENUM_LITERAL(name = name, index = i), _, _, _)  => begin
                    (cache, Values.ENUM_LITERAL(name, i))
                  end

                  (cache, env, DAE.CODE(code = Absyn.C_EXPRESSION(exp = exp)), impl, msg, _)  => begin
                      (cache, exp_1) = cevalAstExp(cache, env, exp, impl, msg, AbsynUtil.dummyInfo)
                    (cache, Values.CODE(Absyn.C_EXPRESSION(exp_1)))
                  end

                  (cache, env, DAE.CODE(code = Absyn.C_ELEMENT(element = elt)), impl, msg, _)  => begin
                      (cache, elt_1) = cevalAstElt(cache, env, elt, impl, msg)
                    (cache, Values.CODE(Absyn.C_ELEMENT(elt_1)))
                  end

                  (cache, _, DAE.CODE(code = c), _, _, _)  => begin
                    (cache, Values.CODE(c))
                  end

                  (cache, env, DAE.ARRAY(array = es, ty = DAE.T_ARRAY(dims = arrayDims)), impl, msg, _)  => begin
                      (cache, es_1) = cevalList(cache, env, es, impl, msg, numIter)
                      v = begin
                        @matchcontinue () begin
                          ()  => begin
                              dims = ListUtil.map(arrayDims, Expression.dimensionSize)
                              v = Values.ARRAY(es_1, dims)
                            v
                          end

                          _  => begin
                                v = ValuesUtil.makeArray(es_1)
                              v
                          end
                        end
                      end
                    (cache, v)
                  end

                  (cache, env, DAE.MATRIX(matrix = expll, ty = DAE.T_ARRAY(dims = arrayDims)), impl, msg, _)  => begin
                      dims = ListUtil.map(arrayDims, Expression.dimensionSize)
                      (cache, elts) = cevalMatrixElt(cache, env, expll, impl, msg, numIter + 1)
                    (cache, Values.ARRAY(elts, dims))
                  end

                  (cache, env, DAE.LIST(valList = expl), impl, msg, _)  => begin
                      (cache, es_1) = cevalList(cache, env, expl, impl, msg, numIter)
                    (cache, Values.LIST(es_1))
                  end

                  (cache, env, DAE.BOX(exp = e1), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, e1, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, DAE.UNBOX(exp = e1), impl, msg, _)  => begin
                      @match (cache, Values.META_BOX(v)) = ceval(cache, env, e1, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, DAE.CONS(car = e1, cdr = e2), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, e1, impl, msg, numIter + 1)
                      @match (cache, Values.LIST(vallst)) = ceval(cache, env, e2, impl, msg, numIter)
                    (cache, Values.LIST(_cons(v, vallst)))
                  end

                  (_, _, DAE.CREF(componentRef = cr, ty = DAE.T_FUNCTION_REFERENCE_VAR(__)), _, Absyn.MSG(info = info), _)  => begin
                      str = CrefForHashTable.crefStr(cr)
                      Error.addSourceMessage(Error.META_CEVAL_FUNCTION_REFERENCE, list(str), info)
                    fail()
                  end

                  (_, _, DAE.CREF(componentRef = cr, ty = DAE.T_FUNCTION_REFERENCE_FUNC(__)), _, Absyn.MSG(info = info), _)  => begin
                      str = CrefForHashTable.crefStr(cr)
                      Error.addSourceMessage(Error.META_CEVAL_FUNCTION_REFERENCE, list(str), info)
                    fail()
                  end

                  (cache, env, DAE.METARECORDCALL(path = funcpath, args = expl, fieldNames = fieldNames, index = index), impl, msg, _)  => begin
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                    (cache, Values.RECORD(funcpath, vallst, fieldNames, index))
                  end

                  (cache, _, DAE.META_OPTION(NONE()), _, _, _)  => begin
                    (cache, Values.OPTION(NONE()))
                  end

                  (cache, env, DAE.META_OPTION(SOME(expExp)), impl, msg, _)  => begin
                      (cache, value) = ceval(cache, env, expExp, impl, msg, numIter + 1)
                    (cache, Values.OPTION(SOME(value)))
                  end

                  (cache, env, DAE.META_TUPLE(expl), impl, msg, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                    (cache, Values.META_TUPLE(vallst))
                  end

                  (cache, env, DAE.TUPLE(expl), impl, msg, _)  => begin
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                    (cache, Values.TUPLE(vallst))
                  end

                  (cache, env, DAE.CREF(componentRef = cr), false, msg, _)  => begin
                      (cache, v) = cevalCref(cache, env, cr, false, msg, numIter + 1) #= When in interactive mode, always evaluate crefs, i.e non-implicit mode.. =#
                    (cache, v)
                  end

                  (cache, env, DAE.CREF(componentRef = cr), impl, msg, _)  => begin
                      (cache, v) = cevalCref(cache, env, cr, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, expExp, impl, msg, _)  => begin
                      (cache, v) = cevalBuiltin(cache, env, expExp, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, DAE.CALL(path = funcpath, expLst = DAE.ICONST(0) <| expExp <|  nil(), attr = DAE.CALL_ATTR(isImpure = false)), impl, msg, _)  => begin
                      @match Absyn.IDENT("smooth") = AbsynUtil.makeNotFullyQualified(funcpath)
                      (cache, value) = ceval(cache, env, expExp, impl, msg, numIter + 1)
                    (cache, value)
                  end

                  (cache, env, e && DAE.CALL(path = funcpath, expLst = expl, attr = DAE.CALL_ATTR(isImpure = false)), impl, msg, _)  => begin
                      @match false = AbsynUtil.pathEqual(Absyn.QUALIFIED("Connection", Absyn.IDENT("isRoot")), funcpath)
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                      @assert(false, "BackendInterface.cevalCallFunction not supported yet!")
                      #(cache, newval) = BackendInterface.cevalCallFunction(cache, env, e, vallst, impl, msg, numIter + 1)
                    (cache, newval)
                  end

                  (cache, env, DAE.CAST(ty = ty, exp = e), impl, msg, _)  => begin
                      @match true = Types.isRecord(ty)
                      (cache, value) = ceval(cache, env, e, impl, msg, numIter + 1)
                    (cache, value)
                  end

                  (cache, env, e && DAE.CALL(__), true, msg, _)  => begin
                      @assert(false, "BackendInterface.cevalInteractiveFunctions not supported yet!")
                      #(cache, value) = BackendInterface.cevalInteractiveFunctions(cache, env, e, msg, numIter + 1)
                    (cache, value)
                  end

                  (_, _, e && DAE.CALL(__), _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Ceval.ceval DAE.CALL failed: ")
                      str = CrefForHashTable.printExpStr(e)
                      Debug.traceln(str)
                    fail()
                  end

                  (cache, env, DAE.RECORD(path = funcpath, exps = expl, comp = fieldNames), impl, msg, _)  => begin
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                    (cache, Values.RECORD(funcpath, vallst, fieldNames, -1))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.ADD(ty = DAE.T_STRING(__)), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.STRING(lhvStr)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.STRING(rhvStr)) = ceval(cache, env, rh, impl, msg, numIter)
                      str = stringAppend(lhvStr, rhvStr)
                    (cache, Values.STRING(str))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.ADD(ty = DAE.T_REAL(__)), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.REAL(lhvReal)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.REAL(rhvReal)) = ceval(cache, env, rh, impl, msg, numIter)
                      sum = lhvReal + rhvReal
                    (cache, Values.REAL(sum))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.ADD_ARR(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vlst1, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(vlst2, _)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.addElementwiseArrayelt(vlst1, vlst2)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.SUB_ARR(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vlst1, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(vlst2, _)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.subElementwiseArrayelt(vlst1, vlst2)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_ARR(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vlst1, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(vlst2, _)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.mulElementwiseArrayelt(vlst1, vlst2)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.DIV_ARR(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vlst1, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(vlst2, _)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.divElementwiseArrayelt(vlst1, vlst2)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.POW_ARR2(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vlst1, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(vlst2, _)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.powElementwiseArrayelt(vlst1, vlst2)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_ARRAY_SCALAR(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, rh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      reslst = ValuesUtil.multScalarArrayelt(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.ADD_ARRAY_SCALAR(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, rh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      reslst = ValuesUtil.addScalarArrayelt(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.SUB_SCALAR_ARRAY(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.subScalarArrayelt(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.POW_SCALAR_ARRAY(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.powScalarArrayelt(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.POW_ARRAY_SCALAR(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, rh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      reslst = ValuesUtil.powArrayeltScalar(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.DIV_SCALAR_ARRAY(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, lh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, rh, impl, msg, numIter)
                      reslst = ValuesUtil.divScalarArrayelt(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.DIV_ARRAY_SCALAR(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, sval) = ceval(cache, env, rh, impl, msg, numIter + 1)
                      @match (cache, Values.ARRAY(aval, dims)) = ceval(cache, env, lh, impl, msg, numIter)
                      reslst = ValuesUtil.divArrayeltScalar(sval, aval)
                    (cache, Values.ARRAY(reslst, dims))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_SCALAR_PRODUCT(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = rhvals)) = ceval(cache, env, rh, impl, msg, numIter)
                      @match (cache, Values.ARRAY(valueLst = lhvals)) = ceval(cache, env, lh, impl, msg, numIter)
                      resVal = ValuesUtil.multScalarProduct(rhvals, lhvals)
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_MATRIX_PRODUCT(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = (@match _cons(elt1, _) = lhvals))) = ceval(cache, env, lh, impl, msg, numIter) #= {{..}..{..}}  {...} =#
                      @match (cache, Values.ARRAY(valueLst = (@match _cons(elt2, _) = rhvals))) = ceval(cache, env, rh, impl, msg, numIter)
                      @match true = ValuesUtil.isArray(elt1)
                      @match false = ValuesUtil.isArray(elt2)
                      resVal = ValuesUtil.multScalarProduct(lhvals, rhvals)
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_MATRIX_PRODUCT(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = (@match _cons(elt1, _) = rhvals))) = ceval(cache, env, rh, impl, msg, numIter) #= {...}  {{..}..{..}} =#
                      @match (cache, Values.ARRAY(valueLst = (@match _cons(elt2, _) = lhvals))) = ceval(cache, env, lh, impl, msg, numIter)
                      @match true = ValuesUtil.isArray(elt1)
                      @match false = ValuesUtil.isArray(elt2)
                      resVal = ValuesUtil.multScalarProduct(lhvals, rhvals)
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL_MATRIX_PRODUCT(__), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY((@match _cons(elt1, _) = rhvals), _)) = ceval(cache, env, rh, impl, msg, numIter + 1) #= {{..}..{..}}  {{..}..{..}} =#
                      @match (cache, Values.ARRAY((@match _cons(elt2, _) = lhvals), _)) = ceval(cache, env, lh, impl, msg, numIter + 1)
                      @match true = ValuesUtil.isArray(elt1)
                      @match true = ValuesUtil.isArray(elt2)
                      vallst = ValuesUtil.multMatrix(lhvals, rhvals)
                    (cache, ValuesUtil.makeArray(vallst))
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.POW(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, lhvVal) = ceval(cache, env, lh, impl, msg, numIter)
                      (cache, rhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      resVal = ValuesUtil.safeIntRealOp(lhvVal, rhvVal, Values.POWOP())
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.MUL(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, lhvVal) = ceval(cache, env, lh, impl, msg, numIter)
                      (cache, rhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      resVal = ValuesUtil.safeIntRealOp(lhvVal, rhvVal, Values.MULOP())
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.DIV(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, lhvVal) = ceval(cache, env, lh, impl, msg, numIter)
                      (cache, rhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      resVal = ValuesUtil.safeIntRealOp(lhvVal, rhvVal, Values.DIVOP())
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.DIV(__), exp2 = rh), impl, msg && Absyn.MSG(info = info), _)  => begin
                      (_, lhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      @match true = ValuesUtil.isZero(lhvVal)
                      lhvStr = CrefForHashTable.printExpStr(lh)
                      rhvStr = CrefForHashTable.printExpStr(rh)
                      Error.addSourceMessage(Error.DIVISION_BY_ZERO, list(lhvStr, rhvStr), info)
                    fail()
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.ADD(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, lhvVal) = ceval(cache, env, lh, impl, msg, numIter)
                      (cache, rhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      resVal = ValuesUtil.safeIntRealOp(lhvVal, rhvVal, Values.ADDOP())
                    (cache, resVal)
                  end

                  (cache, env, DAE.BINARY(exp1 = lh, operator = DAE.SUB(__), exp2 = rh), impl, msg, _)  => begin
                      (cache, lhvVal) = ceval(cache, env, lh, impl, msg, numIter)
                      (cache, rhvVal) = ceval(cache, env, rh, impl, msg, numIter)
                      resVal = ValuesUtil.safeIntRealOp(lhvVal, rhvVal, Values.SUBOP())
                    (cache, resVal)
                  end

                  (cache, env, DAE.UNARY(operator = DAE.UMINUS_ARR(__), exp = daeExp), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(arr, dims)) = ceval(cache, env, daeExp, impl, msg, numIter + 1)
                      arr_1 = ListUtil.map(arr, ValuesUtil.valueNeg)
                    (cache, Values.ARRAY(arr_1, dims))
                  end

                  (cache, env, DAE.UNARY(operator = DAE.UMINUS(__), exp = daeExp), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, daeExp, impl, msg, numIter + 1)
                      v_1 = ValuesUtil.valueNeg(v)
                    (cache, v_1)
                  end

                  (cache, env, DAE.LBINARY(exp1 = lh, operator = DAE.AND(_), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.BOOL(lhvBool)) = ceval(cache, env, lh, impl, msg, numIter)
                      if ! lhvBool
                        v = Values.BOOL(false)
                      else
                        @match (cache, Values.BOOL(rhvBool)) = ceval(cache, env, rh, impl, msg, numIter)
                        resBool = boolAnd(lhvBool, rhvBool)
                        v = Values.BOOL(resBool)
                      end
                    (cache, v)
                  end

                  (cache, env, DAE.LBINARY(exp1 = lh, operator = DAE.OR(_), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, Values.BOOL(lhvBool)) = ceval(cache, env, lh, impl, msg, numIter)
                      if lhvBool
                        v = Values.BOOL(true)
                      else
                        @match (cache, Values.BOOL(rhvBool)) = ceval(cache, env, rh, impl, msg, numIter)
                        resBool = boolOr(lhvBool, rhvBool)
                        v = Values.BOOL(resBool)
                      end
                    (cache, v)
                  end

                  (cache, env, DAE.LBINARY(exp1 = lh, operator = DAE.OR(_), exp2 = rh), impl, msg, _)  => begin
                      @match (cache, (@match Values.BOOL(_) = v)) = ceval(cache, env, lh, impl, msg, numIter)
                      @shouldFail ceval(cache, env, rh, impl, msg, numIter)
                    (cache, v)
                  end

                  (cache, env, DAE.LUNARY(operator = DAE.NOT(_), exp = e), impl, msg, _)  => begin
                      @match (cache, Values.BOOL(b)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      b_1 = boolNot(b)
                    (cache, Values.BOOL(b_1))
                  end

                  (cache, env, DAE.RELATION(exp1 = lhs, operator = relop, exp2 = rhs), impl, msg, _)  => begin
                      (cache, lhs_1) = ceval(cache, env, lhs, impl, msg, numIter)
                      (cache, rhs_1) = ceval(cache, env, rhs, impl, msg, numIter)
                      v = cevalRelation(lhs_1, relop, rhs_1)
                    (cache, v)
                  end

                  (cache, env, DAE.RANGE(ty = DAE.T_BOOL(__), start = start, step = NONE(), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.BOOL(bstart)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.BOOL(bstop)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      arr = ListUtil.map(ExpressionSimplify.simplifyRangeBool(bstart, bstop), ValuesUtil.makeBoolean)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.RANGE(ty = DAE.T_INTEGER(__), start = start, step = NONE(), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(start_1)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(stop_1)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      arr = ListUtil.map(ExpressionSimplify.simplifyRange(start_1, 1, stop_1), ValuesUtil.makeInteger)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.RANGE(ty = DAE.T_INTEGER(__), start = start, step = SOME(step), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(start_1)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(step_1)) = ceval(cache, env, step, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(stop_1)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      arr = ListUtil.map(ExpressionSimplify.simplifyRange(start_1, step_1, stop_1), ValuesUtil.makeInteger)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.RANGE(ty = t && DAE.T_ENUMERATION(__), start = start, step = NONE(), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.ENUM_LITERAL(index = start_1)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.ENUM_LITERAL(index = stop_1)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      arr = cevalRangeEnum(start_1, stop_1, t)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.RANGE(ty = DAE.T_REAL(__), start = start, step = NONE(), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.REAL(realStart1)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(realStop1)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      realStep1 = intReal(1)
                      arr = ListUtil.map(ExpressionSimplify.simplifyRangeReal(realStart1, realStep1, realStop1), ValuesUtil.makeReal)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.RANGE(ty = DAE.T_REAL(__), start = start, step = SOME(step), stop = stop), impl, msg, _)  => begin
                      @match (cache, Values.REAL(realStart1)) = ceval(cache, env, start, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(realStep1)) = ceval(cache, env, step, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(realStop1)) = ceval(cache, env, stop, impl, msg, numIter + 1)
                      arr = ListUtil.map(ExpressionSimplify.simplifyRangeReal(realStart1, realStep1, realStop1), ValuesUtil.makeReal)
                    (cache, ValuesUtil.makeArray(arr))
                  end

                  (cache, env, DAE.CAST(ty = DAE.T_REAL(__), exp = e), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(i)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      r = intReal(i)
                    (cache, Values.REAL(r))
                  end

                  (cache, env, DAE.CAST(ty = DAE.T_INTEGER(__), exp = e), impl, msg, _)  => begin
                      @match (cache, Values.REAL(r)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      i = realInt(r)
                    (cache, Values.INTEGER(i))
                  end

                  (cache, env, DAE.CAST(ty = DAE.T_ENUMERATION(path = path, names = n), exp = e), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(i)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      str = listGet(n, i)
                      path = AbsynUtil.joinPaths(path, Absyn.IDENT(str))
                    (cache, Values.ENUM_LITERAL(path, i))
                  end

                  (cache, env, DAE.CAST(ty = DAE.T_ARRAY(ty = DAE.T_REAL(__)), exp = e), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(ivals, dims)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      rvals = ValuesUtil.typeConvert(DAE.T_INTEGER_DEFAULT, DAE.T_REAL_DEFAULT, ivals)
                    (cache, Values.ARRAY(rvals, dims))
                  end

                  (cache, env, DAE.IFEXP(expCond = cond, expThen = e1, expElse = e2), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, cond, impl, msg, numIter + 1)
                      @match Values.BOOL(resBool) = v
                      (cache, v) = ceval(cache, env, if resBool
                            e1
                          else
                            e2
                          end, impl, msg, numIter)
                    (cache, v)
                  end

                  (cache, env, DAE.ASUB(exp = e, sub = DAE.ICONST(indx) <|  nil()), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vals, _)) = ceval(cache, env, e, impl, msg, numIter + 1) #= asub =#
                      v = listGet(vals, indx)
                    (cache, v)
                  end

                  (cache, env, DAE.ASUB(exp = e, sub = expl), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(vals, dims)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      (cache, es_1) = cevalList(cache, env, expl, impl, msg, numIter)
                      v = listHead(es_1)
                      v = ValuesUtil.nthnthArrayelt(es_1, Values.ARRAY(vals, dims), v)
                    (cache, v)
                  end

                  (cache, env, DAE.TSUB(exp = e, ix = indx), impl, msg, _)  => begin
                      @match (cache, Values.TUPLE(vals)) = ceval(cache, env, e, impl, msg, numIter + 1)
                      v = listGet(vals, indx)
                    (cache, v)
                  end

                  (cache, env, DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(iterType = iterType, path = path, foldName = foldName, resultName = resultName, foldExp = foldExp, defaultValue = ov, exprType = ty), expr = daeExp, iterators = iterators), impl, msg, _)  => begin
                      env = FGraphUtil.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE())
                      (cache, valMatrix, names, dims, tys) = cevalReductionIterators(cache, env, iterators, impl, msg, numIter + 1)
                      valMatrix = makeReductionAllCombinations(valMatrix, iterType)
                      (cache, ov) = cevalReduction(cache, env, path, ov, daeExp, ty, foldName, resultName, foldExp, names, listReverse(valMatrix), tys, impl, msg, numIter + 1)
                      value = Util.getOptionOrDefault(ov, Values.META_FAIL())
                      value = backpatchArrayReduction(path, iterType, value, dims)
                    (cache, value)
                  end

                  (_, _, DAE.EMPTY(__), _, _, _)  => begin
                       #=  Special case for a boolean expression like if( expression or ARRAY_IDEX_OUT_OF_BOUNDS_ERROR)
                       =#
                       #=  \"expression\" in this case we return the lh expression to be equall to
                       =#
                       #=  the previous c-code generation.
                       =#
                       #=  NOT
                       =#
                       #=  relations <, >, <=, >=, <>
                       =#
                       #=  range first:last for integers
                       =#
                       #=  range first:step:last for integers
                       =#
                       #=  range first:last for enumerations.
                       =#
                       #=  range first:last for reals
                       =#
                       #=  diff = realStop1 - realStart1;
                       =#
                       #=  range first:step:last for reals
                       =#
                       #=  cast integer to real
                       =#
                       #=  cast real to integer
                       =#
                       #=  cast integer to enum
                       =#
                       #=  cast integer array to real array
                       =#
                       #=  if expressions, select then/else branch if condition is true/false
                       =#
                       #=  ifexp true then then branch, else else branch\"
                       =#
                       #=  indexing for array[integer index]
                       =#
                       #=  indexing for array[subscripts]
                       =#
                       #=  indexing for tuple[index]
                       =#
                       #=  print(\"Before:\\n\");print(stringDelimitList(List.map1(List.mapList(valMatrix, ValuesUtil.valString), stringDelimitList, \",\"), \"\\n\") + \"\\n\");
                       =#
                       #=  print(\"After:\\n\");print(stringDelimitList(List.map1(List.mapList(valMatrix, ValuesUtil.valString), stringDelimitList, \",\"), \"\\n\") + \"\\n\");
                       =#
                       #=  print(\"Start cevalReduction: \" + AbsynUtil.pathString(path) + \" \" + CrefForHashTable.printExpStr(daeExp) + \"\\n\");
                       =#
                      s = CrefForHashTable.printComponentRefStr(inExp.name)
                      v = Types.typeToValue(inExp.ty)
                    (inCache, Values.EMPTY(inExp.scope, s, v, inExp.tyStr))
                  end

                  (_, _, _, _, _, _) where (Config.getGraphicsExpMode())  => begin
                      ty = Expression.typeof(inExp)
                      v = Types.typeToValue(ty)
                    (inCache, Values.EMPTY("#graphicsExp#", CrefForHashTable.printExpStr(inExp), v, Types.unparseType(ty)))
                  end

                  (_, env, e, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.CEVAL)
                      Debug.traceln("- Ceval.ceval failed: " + CrefForHashTable.printExpStr(e))
                      Debug.traceln("  Scope: " + FGraphUtil.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #=  ceval can fail and that is ok, caught by other rules...
               =#
               #=  Absyn.MSG())
               =#
               #=  Debug.traceln(\"  Env:\" + FGraphUtil.printGraphStr(env));
               =#
          (outCache, outValue)
        end

         #= This function constant evaluates an expression if the expression is constant,
           or if the expression is a call of parameter constness whose return type
           contains unknown dimensions (in which case we need to determine the size of
           those dimensions). =#
        function cevalIfConstant(cache::FCore.Cache, inEnv::FCore.Graph, exp::DAE.Exp, prop::DAE.Properties, impl::Bool, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}




              if Expression.isEvaluatedConst(exp)
                return (cache, exp, prop)
              end
               #=  Don't mess up the dimensions, etc by using the Values module
               =#
              (cache, exp, prop) = begin
                  local v::Values.Value
                  local tp::DAE.Type
                @matchcontinue prop begin
                  DAE.PROP(constFlag = DAE.C_PARAM(__), type_ = tp) where (! Flags.getConfigBool(Flags.CEVAL_EQUATION))  => begin
                    (cache, exp, DAE.PROP(tp, DAE.C_VAR()))
                  end

                  DAE.PROP(constFlag = DAE.C_CONST(__), type_ = tp)  => begin
                       #=  BoschRexroth specifics
                       =#
                      (cache, v) = ceval(cache, inEnv, exp, impl, Absyn.NO_MSG(), 0)
                      exp = ValuesUtil.valueExp(v)
                      exp = ValuesUtil.fixZeroSizeArray(exp, tp)
                    (cache, exp, prop)
                  end

                  DAE.PROP_TUPLE(__)  => begin
                      @match DAE.C_CONST() = Types.propAllConst(prop)
                      (cache, v) = ceval(cache, inEnv, exp, false, Absyn.NO_MSG(), 0)
                      exp = ValuesUtil.valueExp(v)
                    (cache, exp, prop)
                  end

                  DAE.PROP_TUPLE(__) where (! Flags.getConfigBool(Flags.CEVAL_EQUATION))  => begin
                       #=  BoschRexroth specifics
                       =#
                      @match DAE.C_PARAM() = Types.propAllConst(prop)
                      print(" tuple non constant evaluation not implemented yet\\n")
                    fail()
                  end

                  _ where (Expression.isConst(exp) && ! Config.acceptMetaModelicaGrammar())  => begin
                       #=  Structural parameters and the like... we can ceval them if we want to
                       =#
                      (_, v) = ceval(cache, inEnv, exp, impl, Absyn.NO_MSG(), 0)
                      exp = ValuesUtil.valueExp(v)
                      exp = ValuesUtil.fixZeroSizeArray(exp, Types.getPropType(prop))
                    (cache, exp, prop)
                  end

                  _  => begin
                         #=  If we fail to evaluate, at least we should simplify the expression
                         =#
                        (exp, _) = ExpressionSimplify.simplify1(exp)
                      (cache, exp, prop)
                  end
                end
              end
          (cache, exp, prop)
        end

         #= Helper function to cevalIfConstant. Determines the size of any unknown
           dimensions in a function calls return type. =#
        function cevalWholedimRetCall(inExp::DAE.Exp, inCache::FCore.Cache, inEnv::FCore.Graph, inInfo::SourceInfo, numIter::ModelicaInteger) ::Tuple{DAE.Exp, DAE.Properties}
              local outProp::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProp) = begin
                  local e::DAE.Exp
                  local p::Absyn.Path
                  local el::List{DAE.Exp}
                  local t::Bool
                  local b::Bool
                  local isImpure::Bool
                  local isFunctionPointerCall::Bool
                  local i::DAE.InlineType
                  local dims::DAE.Dimensions
                  local v::Values.Value
                  local cevalType::DAE.Type
                  local ty::DAE.Type
                  local tc::DAE.TailCall
                  local attr::DAE.CallAttributes
                @match (inExp, inCache, inEnv, inInfo, numIter) begin
                  (e && DAE.CALL(path = p, expLst = el, attr = attr && DAE.CALL_ATTR(ty = DAE.T_ARRAY(dims = dims))), _, _, _, _)  => begin
                      @match true = Expression.arrayContainWholeDimension(dims)
                      (_, v) = ceval(inCache, inEnv, e, true, Absyn.MSG(inInfo), numIter + 1)
                      ty = Types.typeOfValue(v)
                      cevalType = Types.simplifyType(ty)
                      attr.ty = cevalType
                    (DAE.CALL(p, el, attr), DAE.PROP(ty, DAE.C_PARAM()))
                  end
                end
              end
          (outExp, outProp)
        end

         #= Constant evaluates the limits of a range if they are constant. =#
        function cevalRangeIfConstant(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inProp::DAE.Properties, impl::Bool, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp}
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp) = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::Option{DAE.Exp}
                  local ty::DAE.Type
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inExp, inProp, impl, inInfo) begin
                  (_, _, DAE.RANGE(ty = ty, start = e1, stop = e2, step = e3), _, _, _)  => begin
                      (cache, e1, _) = cevalIfConstant(inCache, inEnv, e1, inProp, impl, inInfo)
                      (_, e2, _) = cevalIfConstant(cache, inEnv, e2, inProp, impl, inInfo)
                    (inCache, DAE.RANGE(ty, e1, e3, e2))
                  end

                  _  => begin
                      (inCache, inExp)
                  end
                end
              end
          (outCache, outExp)
        end

         #= Helper for ceval. Parts for builtin calls are moved here, for readability.
          See ceval for documentation.
          NOTE:    It\\'s ok if cevalBuiltin fails. Just means the call was not a builtin function =#
        function cevalBuiltin(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local v::Values.Value
                  local newval::Values.Value
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local dim::DAE.Exp
                  local e::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local handler::HandlerFunc
                  local id::String
                  local args::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local vallst::List{Values.Value}
                  local funcpath::Absyn.Path
                  local path::Absyn.Path
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inMsg, numIter) begin
                  (cache, env, DAE.SIZE(exp = exp, sz = SOME(dim)), impl, msg, _)  => begin
                      (cache, v) = cevalBuiltinSize(cache, env, exp, dim, impl, msg, numIter + 1) #= Handle size separately =#
                    (cache, v)
                  end

                  (cache, env, DAE.SIZE(exp = exp, sz = NONE()), impl, msg, _)  => begin
                      (cache, v) = cevalBuiltinSizeMatrix(cache, env, exp, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, DAE.CALL(path = path, expLst = args, attr = DAE.CALL_ATTR(builtin = true)), impl, msg, _)  => begin
                      id = AbsynUtil.pathString(path)
                      handler = cevalBuiltinHandler(id)
                      (cache, v) = handler(cache, env, args, impl, msg, numIter + 1)
                    (cache, v)
                  end

                  (cache, env, e && DAE.CALL(expLst = expl, attr = DAE.CALL_ATTR(builtin = true)), impl, msg, _)  => begin
                      (cache, vallst) = cevalList(cache, env, expl, impl, msg, numIter)
                      @assert(false, "BackendInterface.cevaCallFunction not supported yet!")
                      #(cache, newval) = BackendInterface.cevalCallFunction(cache, env, e, vallst, impl, msg, numIter + 1)
                    (cache, newval)
                  end
                end
              end
          (outCache, outValue)
        end

         #= This function dispatches builtin functions and operators to a dedicated
          function that evaluates that particular function.
          It takes an identifier as input and returns a function that evaluates that
          function or operator.
          NOTE: size handled specially. see cevalBuiltin:
                removed: case (\\\"size\\\") => cevalBuiltinSize =#
        function cevalBuiltinHandler(inIdent::Absyn.Ident) ::HandlerFunc
              local handler::HandlerFunc

              handler = begin
                  local id::String
                @match inIdent begin
                  "floor"  => begin
                    cevalBuiltinFloor
                  end

                  "ceil"  => begin
                    cevalBuiltinCeil
                  end

                  "abs"  => begin
                    cevalBuiltinAbs
                  end

                  "sqrt"  => begin
                    cevalBuiltinSqrt
                  end

                  "div"  => begin
                    cevalBuiltinDiv
                  end

                  "sin"  => begin
                    cevalBuiltinSin
                  end

                  "cos"  => begin
                    cevalBuiltinCos
                  end

                  "tan"  => begin
                    cevalBuiltinTan
                  end

                  "sinh"  => begin
                    cevalBuiltinSinh
                  end

                  "cosh"  => begin
                    cevalBuiltinCosh
                  end

                  "tanh"  => begin
                    cevalBuiltinTanh
                  end

                  "asin"  => begin
                    cevalBuiltinAsin
                  end

                  "acos"  => begin
                    cevalBuiltinAcos
                  end

                  "atan"  => begin
                    cevalBuiltinAtan
                  end

                  "atan2"  => begin
                    cevalBuiltinAtan2
                  end

                  "log"  => begin
                    cevalBuiltinLog
                  end

                  "log10"  => begin
                    cevalBuiltinLog10
                  end

                  "integer"  => begin
                    cevalBuiltinInteger
                  end

                  "boolean"  => begin
                    cevalBuiltinBoolean
                  end

                  "mod"  => begin
                    cevalBuiltinMod
                  end

                  "max"  => begin
                    cevalBuiltinMax
                  end

                  "min"  => begin
                    cevalBuiltinMin
                  end

                  "rem"  => begin
                    cevalBuiltinRem
                  end

                  "sum"  => begin
                    cevalBuiltinSum
                  end

                  "diagonal"  => begin
                    cevalBuiltinDiagonal
                  end

                  "sign"  => begin
                    cevalBuiltinSign
                  end

                  "exp"  => begin
                    cevalBuiltinExp
                  end

                  "noEvent"  => begin
                    cevalBuiltinNoevent
                  end

                  "cat"  => begin
                    cevalBuiltinCat
                  end

                  "identity"  => begin
                    cevalBuiltinIdentity
                  end

                  "promote"  => begin
                    cevalBuiltinPromote
                  end

                  "String"  => begin
                    cevalBuiltinString
                  end

                  "Integer"  => begin
                    cevalBuiltinIntegerEnumeration
                  end

                  "rooted"  => begin
                    cevalBuiltinRooted
                  end

                  "cross"  => begin
                    cevalBuiltinCross
                  end

                  "fill"  => begin
                    cevalBuiltinFill
                  end

                  "Modelica.Utilities.Strings.substring"  => begin
                    cevalBuiltinSubstring
                  end

                  "print"  => begin
                    cevalBuiltinPrint
                  end

                  "fail"  => begin
                    cevalBuiltinFail
                  end

                  "intString" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntString
                  end

                  "realString" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalRealString
                  end

                  "stringCharInt" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringCharInt
                  end

                  "intStringChar" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntStringChar
                  end

                  "stringLength" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringLength
                  end

                  "stringInt" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringInt
                  end

                  "stringListStringChar" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringListStringChar
                  end

                  "listStringCharString" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListStringCharString
                  end

                  "stringAppendList" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringAppendList
                  end

                  "stringDelimitList" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalStringDelimitList
                  end

                  "listLength" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListLength
                  end

                  "listAppend" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListAppend
                  end

                  "listReverse" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListReverse
                  end

                  "listHead" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListFirst
                  end

                  "listRest" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListRest
                  end

                  "listMember" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListMember
                  end

                  "anyString" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalAnyString
                  end

                  "listArrayLiteral" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalListArrayLiteral
                  end

                  "intBitAnd" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntBitAnd
                  end

                  "intBitOr" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntBitOr
                  end

                  "intBitXor" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntBitXor
                  end

                  "intBitLShift" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntBitLShift
                  end

                  "intBitRShift" where (Config.acceptMetaModelicaGrammar())  => begin
                    cevalIntBitRShift
                  end

                  "numBits"  => begin
                    cevalNumBits
                  end

                  "integerMax"  => begin
                    cevalIntegerMax
                  end

                  id  => begin
                      @match true = Flags.isSet(Flags.CEVAL)
                      Debug.traceln("No cevalBuiltinHandler found for " + id)
                    fail()
                  end
                end
              end
               #=
               =#
               #=  BTH
               =#
               #= /*
                  case \"Clock\"
                    equation
                      true = Config.synchronousFeaturesAllowed();
                    then cevalBuiltinClock; */ =#
               #=  MetaModelica type conversions
               =#
               #= case \"semiLinear\" then cevalBuiltinSemiLinear;
               =#
               #= case \"delay\" then cevalBuiltinDelay;
               =#
          handler
        end

         #= Evaluates external functions that are known, e.g. all math functions. =#
        function cevalKnownExternalFuncs(inCache::FCore.Cache, env::FCore.Graph, funcpath::Absyn.Path, vals::List{<:Values.Value}, msg::Absyn.Msg) ::Tuple{FCore.Cache, Values.Value}
              local res::Values.Value
              local outCache::FCore.Cache

              local cdef::SCode.Element
              local env_1::FCore.Graph
              local fid::String
              local id::String
              local oid::Option{String}
              local extdecl::Option{SCode.ExternalDecl}
              local lan::Option{String}
              local out::Option{Absyn.ComponentRef}
              local args::List{Absyn.Exp}
              local funcRest::SCode.FunctionRestriction

              (outCache, cdef, env_1) = Lookup.lookupClass(inCache, env, funcpath)
              @match SCode.CLASS(name = fid, restriction = SCode.R_FUNCTION(funcRest), classDef = SCode.PARTS(externalDecl = extdecl)) = cdef
              @match SCode.FR_EXTERNAL_FUNCTION(_) = funcRest
              @match SOME(SCode.EXTERNALDECL(oid, _, _, _, _)) = extdecl
               #=  oid=NONE() is more safe, but most of the functions are declared is a certain way =/
               =#
              id = Util.getOptionOrDefault(oid, fid)
              isKnownExternalFunc(id)
              res = cevalKnownExternalFuncs2(id, vals, msg)
          (outCache, res)
        end

         #= \\\"known\\\", i.e. no compilation required. =#
        function isKnownExternalFunc(id::String)
              _ = begin
                @match id begin
                  "acos"  => begin
                    ()
                  end

                  "asin"  => begin
                    ()
                  end

                  "atan"  => begin
                    ()
                  end

                  "atan2"  => begin
                    ()
                  end

                  "cos"  => begin
                    ()
                  end

                  "cosh"  => begin
                    ()
                  end

                  "exp"  => begin
                    ()
                  end

                  "log"  => begin
                    ()
                  end

                  "log10"  => begin
                    ()
                  end

                  "sin"  => begin
                    ()
                  end

                  "sinh"  => begin
                    ()
                  end

                  "tan"  => begin
                    ()
                  end

                  "tanh"  => begin
                    ()
                  end

                  "print"  => begin
                    ()
                  end

                  "ModelicaStreams_closeFile"  => begin
                    ()
                  end

                  "ModelicaStrings_substring"  => begin
                    ()
                  end

                  "ModelicaStrings_length"  => begin
                    ()
                  end

                  "ModelicaInternal_print"  => begin
                    ()
                  end

                  "ModelicaInternal_countLines"  => begin
                    ()
                  end

                  "ModelicaInternal_readLine"  => begin
                    ()
                  end

                  "ModelicaInternal_stat"  => begin
                    ()
                  end

                  "ModelicaInternal_fullPathName"  => begin
                    ()
                  end

                  "ModelicaStrings_compare"  => begin
                    ()
                  end

                  "ModelicaStrings_scanReal"  => begin
                    ()
                  end

                  "ModelicaStrings_skipWhiteSpace"  => begin
                    ()
                  end

                  "ModelicaError"  => begin
                    ()
                  end

                  "OpenModelica_regex"  => begin
                    ()
                  end
                end
              end
        end

         #= Helper function to cevalKnownExternalFuncs, does the evaluation. =#
        function cevalKnownExternalFuncs2(id::String, inValuesValueLst::List{<:Values.Value}, inMsg::Absyn.Msg) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local rv_1::ModelicaReal
                  local rv::ModelicaReal
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local r::ModelicaReal
                  local str::String
                  local fileName::String
                  local re::String
                  local str1::String
                  local str2::String
                  local start::ModelicaInteger
                  local stop::ModelicaInteger
                  local i::ModelicaInteger
                  local lineNumber::ModelicaInteger
                  local n::ModelicaInteger
                  local b::Bool
                  local extended::Bool
                  local insensitive::Bool
                  local strs::List{String}
                  local vals::List{Values.Value}
                  local v::Values.Value
                  local p::Absyn.Path
                @match (id, inValuesValueLst, inMsg) begin
                  ("acos", Values.REAL(real = rv) <|  nil(), _)  => begin
                      @match true = rv >= (-1.0) && rv <= 1.0
                      rv_1 = acos(rv)
                    Values.REAL(rv_1)
                  end

                  ("asin", Values.REAL(real = rv) <|  nil(), _)  => begin
                      @match true = rv >= (-1.0) && rv <= 1.0
                      rv_1 = asin(rv)
                    Values.REAL(rv_1)
                  end

                  ("atan", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = atan(rv)
                    Values.REAL(rv_1)
                  end

                  ("atan2", Values.REAL(real = rv1) <| Values.REAL(real = rv2) <|  nil(), _)  => begin
                      rv_1 = atan2(rv1, rv2)
                    Values.REAL(rv_1)
                  end

                  ("cos", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = cos(rv)
                    Values.REAL(rv_1)
                  end

                  ("cosh", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = cosh(rv)
                    Values.REAL(rv_1)
                  end

                  ("exp", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = exp(rv)
                    Values.REAL(rv_1)
                  end

                  ("log", Values.REAL(real = rv) <|  nil(), _)  => begin
                      @match true = rv > 0
                      rv_1 = log(rv)
                    Values.REAL(rv_1)
                  end

                  ("log10", Values.REAL(real = rv) <|  nil(), _)  => begin
                      @match true = rv > 0
                      rv_1 = log10(rv)
                    Values.REAL(rv_1)
                  end

                  ("sin", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = sin(rv)
                    Values.REAL(rv_1)
                  end

                  ("sinh", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = sinh(rv)
                    Values.REAL(rv_1)
                  end

                  ("tan", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = tan(rv)
                    Values.REAL(rv_1)
                  end

                  ("tanh", Values.REAL(real = rv) <|  nil(), _)  => begin
                      rv_1 = tanh(rv)
                    Values.REAL(rv_1)
                  end

                  ("ModelicaStrings_substring", Values.STRING(string = str) <| Values.INTEGER(integer = start) <| Values.INTEGER(integer = stop) <|  nil(), _)  => begin
                      str = System.substring(str, start, stop)
                    Values.STRING(str)
                  end

                  ("ModelicaStrings_length", Values.STRING(str) <|  nil(), _)  => begin
                      i = stringLength(str)
                    Values.INTEGER(i)
                  end

                  ("print", Values.STRING(str) <|  nil(), _)  => begin
                      print(str)
                    Values.NORETCALL()
                  end

                  ("ModelicaStreams_closeFile", Values.STRING(fileName) <|  nil(), _)  => begin
                      ModelicaExternalC.Streams_close(fileName)
                    Values.NORETCALL()
                  end

                  ("ModelicaInternal_print", Values.STRING(str) <| Values.STRING(fileName) <|  nil(), _)  => begin
                      ModelicaExternalC.Streams_print(str, fileName)
                    Values.NORETCALL()
                  end

                  ("ModelicaInternal_countLines", Values.STRING(fileName) <|  nil(), _)  => begin
                      i = ModelicaExternalC.Streams_countLines(fileName)
                    Values.INTEGER(i)
                  end

                  ("ModelicaInternal_readLine", Values.STRING(fileName) <| Values.INTEGER(lineNumber) <|  nil(), _)  => begin
                      (str, b) = ModelicaExternalC.Streams_readLine(fileName, lineNumber)
                    Values.TUPLE(list(Values.STRING(str), Values.BOOL(b)))
                  end

                  ("ModelicaInternal_fullPathName", Values.STRING(fileName) <|  nil(), _)  => begin
                      fileName = ModelicaExternalC.File_fullPathName(fileName)
                    Values.STRING(fileName)
                  end

                  ("ModelicaInternal_stat", Values.STRING(str) <|  nil(), _)  => begin
                      i = ModelicaExternalC.File_stat(str)
                      str = listGet(list("NoFile", "RegularFile", "Directory", "SpecialFile"), i)
                      p = AbsynUtil.stringListPath(list("OpenModelica", "Scripting", "Internal", "FileType", str))
                      v = Values.ENUM_LITERAL(p, i)
                    v
                  end

                  ("ModelicaStrings_compare", Values.STRING(str1) <| Values.STRING(str2) <| Values.BOOL(b) <|  nil(), _)  => begin
                      i = ModelicaExternalC.Strings_compare(str1, str2, b)
                      p = listGet(list(EnumCompareLess, EnumCompareEqual, EnumCompareGreater), i)
                    Values.ENUM_LITERAL(p, i)
                  end

                  ("ModelicaStrings_scanReal", Values.STRING(str) <| Values.INTEGER(i) <| Values.BOOL(b) <|  nil(), _)  => begin
                      (i, r) = ModelicaExternalC.Strings_advanced_scanReal(str, i, b)
                    Values.TUPLE(list(Values.INTEGER(i), Values.REAL(r)))
                  end

                  ("ModelicaStrings_skipWhiteSpace", Values.STRING(str) <| Values.INTEGER(i) <|  nil(), _)  => begin
                      i = ModelicaExternalC.Strings_advanced_skipWhiteSpace(str, i)
                    Values.INTEGER(i)
                  end

                  ("OpenModelica_regex", Values.STRING(str) <| Values.STRING(re) <| Values.INTEGER(i) <| Values.BOOL(extended) <| Values.BOOL(insensitive) <|  nil(), _)  => begin
                      (n, strs) = System.regex(str, re, i, extended, insensitive)
                      vals = ListUtil.map(strs, ValuesUtil.makeString)
                      v = Values.ARRAY(vals, list(i))
                    Values.TUPLE(list(Values.INTEGER(n), v))
                  end
                end
              end
          outValue
        end

         const EnumCompareLess = Absyn.QUALIFIED("Modelica", Absyn.QUALIFIED("Utilities", Absyn.QUALIFIED("Types", Absyn.QUALIFIED("Compare", Absyn.IDENT("Less")))))::Absyn.Path

         const EnumCompareEqual = Absyn.QUALIFIED("Modelica", Absyn.QUALIFIED("Utilities", Absyn.QUALIFIED("Types", Absyn.QUALIFIED("Compare", Absyn.IDENT("Equal")))))::Absyn.Path

         const EnumCompareGreater = Absyn.QUALIFIED("Modelica", Absyn.QUALIFIED("Utilities", Absyn.QUALIFIED("Types", Absyn.QUALIFIED("Compare", Absyn.IDENT("Greater")))))::Absyn.Path

         #= Evaluates the expression of a matrix constructor, e.g. {1,2;3,4} =#
        function cevalMatrixElt(inCache::FCore.Cache, inEnv::FCore.Graph, inMatrix::List{<:List{<:DAE.Exp}} #= matrix constr. elts =#, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{Values.Value}}
              local outValues::List{Values.Value} = nil
              local outCache::FCore.Cache = inCache

              local v::Values.Value
              local vl::List{Values.Value}

              for expl in inMatrix
                (outCache, vl) = cevalList(outCache, inEnv, expl, inBoolean, inMsg, numIter)
                v = ValuesUtil.makeArray(vl)
                outValues = _cons(v, outValues)
              end
              outValues = listReverseInPlace(outValues)
          (outCache, outValues)
        end

         #= Evaluates the size operator. =#
        function cevalBuiltinSize(inCache::FCore.Cache, inEnv1::FCore.Graph, inExp2::DAE.Exp, inDimExp::DAE.Exp, inBoolean4::Bool, inMsg6::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local attr::DAE.Attributes
                  local tp::DAE.Type
                  local bind::DAE.Binding
                  local binding::DAE.Binding
                  local sizelst::List{ModelicaInteger}
                  local adims::List{ModelicaInteger}
                  local dim::ModelicaInteger
                  local dim_1::ModelicaInteger
                  local dimv::ModelicaInteger
                  local len::ModelicaInteger
                  local i::ModelicaInteger
                  local env::FCore.Graph
                  local cr::DAE.ComponentRef
                  local impl::Bool
                  local bl::Bool
                  local msg::Absyn.Msg
                  local dims::DAE.Dimensions
                  local v2::Values.Value
                  local val::Values.Value
                  local crtp::DAE.Type
                  local expTp::DAE.Type
                  local exp::DAE.Exp
                  local e::DAE.Exp
                  local dimExp::DAE.Exp
                  local cr_str::String
                  local dim_str::String
                  local size_str::String
                  local expstr::String
                  local es::List{DAE.Exp}
                  local cache::FCore.Cache
                  local mat::List{List{DAE.Exp}}
                  local info::SourceInfo
                  local ddim::DAE.Dimension
                @matchcontinue (inCache, inEnv1, inExp2, inDimExp, inBoolean4, inMsg6, numIter) begin
                  (cache, _, DAE.MATRIX(matrix = mat), DAE.ICONST(1), _, _, _)  => begin
                      i = listLength(mat)
                    (cache, Values.INTEGER(i))
                  end

                  (cache, _, DAE.MATRIX(matrix = mat), DAE.ICONST(2), _, _, _)  => begin
                      i = listLength(listHead(mat))
                    (cache, Values.INTEGER(i))
                  end

                  (cache, env, DAE.MATRIX(matrix = mat), DAE.ICONST(dim), impl, msg, _)  => begin
                      bl = dim > 2
                      @match true = bl
                      dim_1 = dim - 2
                      e = listHead(listHead(mat))
                      @match (cache, Values.INTEGER(i)) = cevalBuiltinSize(cache, env, e, DAE.ICONST(dim_1), impl, msg, numIter + 1)
                    (cache, Values.INTEGER(i))
                  end

                  (cache, env, DAE.CREF(componentRef = cr), dimExp, impl, msg, _)  => begin
                      (cache, _, tp, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr) #= If dimensions known, always ceval =#
                      @match true = Types.dimensionsKnown(tp)
                      @match (@match _cons(_, _) = sizelst) = Types.getDimensionSizes(tp)
                      @match (cache, Values.INTEGER(dim)) = ceval(cache, env, dimExp, impl, msg, numIter + 1)
                      i = listGet(sizelst, dim)
                    (cache, Values.INTEGER(i))
                  end

                  (cache, env, DAE.CREF(componentRef = cr), dimExp, impl && false, msg, _)  => begin
                      (cache, dims) = InstUtil.elabComponentArraydimFromEnv(cache, env, cr, AbsynUtil.dummyInfo) #= If component not instantiated yet, recursive definition.
                               For example,
                                 Real x[:](min=fill(1.0,size(x,1))) = {1.0}
                               When size(x,1) should be determined, x must be instantiated, but
                               that is not done yet. Solution: Examine Element to find modifier
                               which will determine dimension size. =#
                      @match (cache, Values.INTEGER(dimv)) = ceval(cache, env, dimExp, impl, msg, numIter + 1)
                      ddim = listGet(dims, dimv)
                      (cache, v2) = cevalDimension(cache, env, ddim, impl, msg, numIter + 1)
                    (cache, v2)
                  end

                  (cache, env, DAE.CREF(componentRef = cr), dimExp, false, Absyn.MSG(info = info), _)  => begin
                      (_, _, tp, binding, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr) #= If dimensions not known and impl=false, error message =#
                      if ! Types.dimensionsKnown(tp)
                        cr_str = CrefForHashTable.printComponentRefStr(cr)
                        dim_str = CrefForHashTable.printExpStr(dimExp)
                        size_str = stringAppendList(list("size(", cr_str, ", ", dim_str, ")"))
                        Error.addSourceMessage(Error.DIMENSION_NOT_KNOWN, list(size_str), info)
                      else
                        _ = begin
                          @match binding begin
                            DAE.UNBOUND(__)  => begin
                                expstr = CrefForHashTable.printExpStr(inExp2)
                                Error.addSourceMessage(Error.UNBOUND_VALUE, list(expstr), info)
                              fail()
                            end
                          end
                        end
                      end
                    fail()
                  end

                  (cache, env, DAE.CREF(componentRef = cr), dimExp, impl, msg, _)  => begin
                      (cache, _, _, binding, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr)
                      @match (cache, Values.INTEGER(dimv)) = ceval(cache, env, dimExp, impl, msg, numIter + 1)
                      (cache, val) = cevalCrefBinding(cache, env, cr, binding, impl, msg, numIter + 1)
                      v2 = cevalBuiltinSize2(val, dimv)
                    (cache, v2)
                  end

                  (cache, env, DAE.ARRAY(array = exp <| es), dimExp, impl, msg, _)  => begin
                      _ = Expression.typeof(exp) #= Special case for array expressions with nonconstant
                                                              values For now: only arrays of scalar elements:
                                                              TODO generalize to arbitrary dimensions =#
                      @match (cache, Values.INTEGER(1)) = ceval(cache, env, dimExp, impl, msg, numIter + 1)
                      len = listLength(_cons(exp, es))
                    (cache, Values.INTEGER(len))
                  end

                  (cache, env, exp, dimExp, impl, msg, _)  => begin
                      (cache, val) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(dimv)) = ceval(cache, env, dimExp, impl, msg, numIter + 1)
                      v2 = begin
                        @match val begin
                          Values.ARRAY( nil(), adims)  => begin
                            Values.INTEGER(listGet(adims, dimv))
                          end

                          _  => begin
                              cevalBuiltinSize2(val, dimv)
                          end
                        end
                      end
                    (cache, v2)
                  end

                  (_, _, exp, _, _, Absyn.MSG(__), _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Print.printErrorBuf("#-- Ceval.cevalBuiltinSize failed: ")
                      expstr = CrefForHashTable.printExpStr(exp)
                      Print.printErrorBuf(expstr)
                      Print.printErrorBuf("\\n")
                    fail()
                  end
                end
              end
               #=  For crefs with value binding e.g. size(x,1) when Real x[:]=fill(0,1);
               =#
               #=  For expressions with value binding that can not determine type
               =#
               #=  e.g. size(x,2) when Real x[:,:]=fill(0.0,0,2); empty array with second dimension == 2, no way of
               =#
               #=  knowing that from the value. Must investigate the expression itself.
               =#
          (outCache, outValue)
        end

         #= Helper function to cevalBuiltinSize =#
        function cevalBuiltinSize2(inValue::Values.Value, inInteger::ModelicaInteger) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local dim::ModelicaInteger
                  local ind_1::ModelicaInteger
                  local ind::ModelicaInteger
                  local lst::List{Values.Value}
                  local l::Values.Value
                  local dimVal::Values.Value
                @matchcontinue (inValue, inInteger) begin
                  (Values.ARRAY(valueLst = lst), 1)  => begin
                      dim = listLength(lst)
                    Values.INTEGER(dim)
                  end

                  (Values.ARRAY(valueLst = l <| _), ind)  => begin
                      ind_1 = ind - 1
                      dimVal = cevalBuiltinSize2(l, ind_1)
                    dimVal
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Ceval.cevalBuiltinSize2 failed\\n")
                      fail()
                  end
                end
              end
          outValue
        end

         #= author: PA
          Helper function to cevalBuiltinSize.
          Used when recursive definition (attribute modifiers using size) is used. =#
        function cevalBuiltinSize3(inDims::DAE.Dimensions, inIndex::ModelicaInteger) ::Values.Value
              local outValue::Values.Value

              local v::ModelicaInteger

              @match DAE.DIM_INTEGER(v) = listGet(inDims, inIndex)
              outValue = Values.INTEGER(v)
          outValue
        end

         #= author: LP
          Evaluates the abs operator. =#
        function cevalBuiltinAbs(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local iv::ModelicaInteger
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = realAbs(rv)
                    (cache, Values.REAL(rv_1))
                  end

                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(iv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      iv = intAbs(iv)
                    (cache, Values.INTEGER(iv))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the sign operator. =#
        function cevalBuiltinSign(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local impl::Bool
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local msg::Absyn.Msg
                  local iv::ModelicaInteger
                  local iv_1::ModelicaInteger
                  local cache::FCore.Cache
                  local v::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      (b1, b2, b3) = begin
                        @match v begin
                          Values.REAL(rv)  => begin
                            (rv > 0.0, rv < 0.0, rv == 0.0)
                          end

                          Values.INTEGER(iv)  => begin
                            (iv > 0, iv < 0, iv == 0)
                          end
                        end
                      end
                      @match list((_, iv_1)) = ListUtil.select(list((b1, 1), (b2, -1), (b3, 0)), Util.tuple21)
                    (cache, Values.INTEGER(iv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the exp function =#
        function cevalBuiltinExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = exp(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the noEvent operator. During constant evaluation events are not
          considered, so evaluation will simply remove the operator and evaluate the
          operand. =#
        function cevalBuiltinNoevent(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local v::Values.Value
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the cat operator, for matrix concatenation. =#
        function cevalBuiltinCat(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local dim_int::ModelicaInteger
                  local mat_lst::List{Values.Value}
                  local v::Values.Value
                  local env::FCore.Graph
                  local dim::DAE.Exp
                  local matrices::List{DAE.Exp}
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, dim <| matrices, impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(dim_int)) = ceval(cache, env, dim, impl, msg, numIter + 1)
                      (cache, mat_lst) = cevalList(cache, env, matrices, impl, msg, numIter)
                      v = cevalCat(mat_lst, dim_int)
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the identity operator. =#
        function cevalBuiltinIdentity(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local dimension::ModelicaInteger
                  local expl::List{DAE.Exp}
                  local retExp::List{Values.Value}
                  local env::FCore.Graph
                  local dim::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local res::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, dim <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(dimension)) = ceval(cache, env, dim, impl, msg, numIter + 1)
                      res = Values.ARRAY(list(Values.ARRAY(list(if i == j
                            Values.INTEGER(1)
                          else
                            Values.INTEGER(0)
                          end for i in 1:dimension), list(dimension)) for j in 1:dimension), list(dimension, dimension))
                    (cache, res)
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the internal promote operator, for promotion of arrays =#
        function cevalBuiltinPromote(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local arr_val::Values.Value
                  local res::Values.Value
                  local dim_val::ModelicaInteger
                  local env::FCore.Graph
                  local arr::DAE.Exp
                  local dim::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local dims::List{ModelicaInteger}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, arr <| dim <|  nil(), impl, msg, _)  => begin
                      @match (cache, (@match Values.ARRAY(dimLst = dims) = arr_val)) = ceval(cache, env, arr, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(dim_val)) = ceval(cache, env, dim, impl, msg, numIter + 1)
                      res = cevalBuiltinPromote2(arr_val, dim_val - listLength(dims))
                    (cache, res)
                  end
                end
              end
          (outCache, outValue)
        end

         #= Helper function to cevalBuiltinPromote =#
        function cevalBuiltinPromote2(inValue::Values.Value, inInteger::ModelicaInteger) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local v::Values.Value
                  local n_1::ModelicaInteger
                  local n::ModelicaInteger
                  local i::ModelicaInteger
                  local vs_1::List{Values.Value}
                  local vs::List{Values.Value}
                  local il::List{ModelicaInteger}
                @matchcontinue (inValue, inInteger) begin
                  (v, 0)  => begin
                    Values.ARRAY(list(v), list(1))
                  end

                  (Values.ARRAY(valueLst = vs, dimLst = i <| _), n)  => begin
                      n_1 = n - 1
                      @match (@match _cons(Values.ARRAY(dimLst = il), _) = vs_1) = ListUtil.map1(vs, cevalBuiltinPromote2, n_1)
                    Values.ARRAY(vs_1, _cons(i, il))
                  end

                  (v, n)  => begin
                      @shouldFail @match Values.ARRAY() = v
                      n_1 = n - 1
                      @match (@match Values.ARRAY(dimLst = il) = v) = cevalBuiltinPromote2(v, n_1)
                    Values.ARRAY(list(v), _cons(1, il))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Ceval.cevalBuiltinPromote2 failed\\n")
                      fail()
                  end
                end
              end
          outValue
        end

         #=
          author: PA
          Evaluates the String operator String(r), String(i), String(b), String(e).
          TODO: Also evaluate String(r, significantDigits=d), and String(r, format=s). =#
        function cevalBuiltinSubstring(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local str_exp::DAE.Exp
                  local start_exp::DAE.Exp
                  local stop_exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local start::ModelicaInteger
                  local stop::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, str_exp <| start_exp <| stop_exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, str_exp, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(start)) = ceval(cache, env, start_exp, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(stop)) = ceval(cache, env, stop_exp, impl, msg, numIter + 1)
                      str = System.substring(str, start, stop)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

         #=
          author: PA
          Evaluates the String operator String(r), String(i), String(b), String(e).
          TODO: Also evaluate String(r, significantDigits=d), and String(r, format=s). =#
        function cevalBuiltinString(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local len_exp::DAE.Exp
                  local justified_exp::DAE.Exp
                  local sig_dig::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local format::String
                  local i::ModelicaInteger
                  local len::ModelicaInteger
                  local sig::ModelicaInteger
                  local r::ModelicaReal
                  local b::Bool
                  local left_just::Bool
                  local p::Absyn.Path
                  local v::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <| len_exp <| justified_exp <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      str = begin
                        @match v begin
                          Values.INTEGER(i)  => begin
                            intString(i)
                          end

                          Values.BOOL(b)  => begin
                            boolString(b)
                          end

                          Values.ENUM_LITERAL(name = p)  => begin
                            AbsynUtil.pathLastIdent(p)
                          end
                        end
                      end
                      (cache, str) = cevalBuiltinStringFormat(cache, env, str, len_exp, justified_exp, impl, msg, numIter + 1)
                    (cache, Values.STRING(str))
                  end

                  (cache, env, exp <| sig_dig <| len_exp <| justified_exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(r)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(len)) = ceval(cache, env, len_exp, impl, msg, numIter + 1)
                      @match (cache, Values.BOOL(left_just)) = ceval(cache, env, justified_exp, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(sig)) = ceval(cache, env, sig_dig, impl, msg, numIter + 1)
                      format = "%" + (if left_just
                            "-"
                          else
                            ""
                          end) + intString(len) + "." + intString(sig) + "g"
                      str = System.snprintff(format, len + 20, r)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

         #= This function formats a string by using the minimumLength and leftJustified
          arguments to the String function. =#
        function cevalBuiltinStringFormat(inCache::FCore.Cache, inEnv::FCore.Graph, inString::String, lengthExp::DAE.Exp, justifiedExp::DAE.Exp, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, String}
              local outString::String
              local outCache::FCore.Cache

              (outCache, outString) = begin
                  local cache::FCore.Cache
                  local min_length::ModelicaInteger
                  local left_justified::Bool
                  local str::String
                @match (inCache, inEnv, inString, lengthExp, justifiedExp, inBoolean, inMsg, numIter) begin
                  (cache, _, _, _, _, _, _, _)  => begin
                      @match (cache, Values.INTEGER(integer = min_length)) = ceval(cache, inEnv, lengthExp, inBoolean, inMsg, numIter + 1)
                      @match (cache, Values.BOOL(boolean = left_justified)) = ceval(cache, inEnv, justifiedExp, inBoolean, inMsg, numIter + 1)
                      str = ExpressionSimplify.cevalBuiltinStringFormat(inString, stringLength(inString), min_length, left_justified)
                    (cache, str)
                  end
                end
              end
          (outCache, outString)
        end

         #= Prints a String to stdout =#
        function cevalBuiltinPrint(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      print(str)
                    (cache, Values.NORETCALL())
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalIntString(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(i)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      str = intString(i)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalRealString(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local r::ModelicaReal
                  local v::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match Values.REAL(r) = v
                      str = realString(r)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalStringCharInt(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      i = stringCharInt(str)
                    (cache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalIntStringChar(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(i)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      str = intStringChar(i)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalStringInt(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      i = stringInt(str)
                    (cache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalStringLength(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      i = stringLength(str)
                    (cache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalStringListStringChar(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local chList::List{String}
                  local valList::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      chList = stringListStringChar(str)
                      valList = ListUtil.map(chList, generateValueString)
                    (cache, Values.LIST(valList))
                  end
                end
              end
          (outCache, outValue)
        end

        function generateValueString(str::String) ::Values.Value
              local val::Values.Value

              val = Values.STRING(str)
          val
        end

        function cevalListStringCharString(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local chList::List{String}
                  local valList::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      chList = ListUtil.map(valList, extractValueStringChar)
                      str = stringAppendList(chList)
                    (cache, Values.STRING(str))
                  end
                end
              end
               #=  Note that the RML version of the function has a weird name, but is also not implemented yet!
               =#
               #=  The work-around is to check that each String has length 1 and append all the Strings together
               =#
               #=  WARNING: This can be very, very slow for long lists - it grows as O(n^2)
               =#
               #=  TODO: When implemented, use listStringCharString (OMC name) or stringCharListString (RML name) directly
               =#
          (outCache, outValue)
        end

        function cevalStringAppendList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local chList::List{String}
                  local valList::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      chList = ListUtil.map(valList, ValuesUtil.extractValueString)
                      str = stringAppendList(chList)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalStringDelimitList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local chList::List{String}
                  local valList::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.STRING(str)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      chList = ListUtil.map(valList, ValuesUtil.extractValueString)
                      str = stringDelimitList(chList, str)
                    (cache, Values.STRING(str))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListLength(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local i::ModelicaInteger
                  local valList::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      i = listLength(valList)
                    (cache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListAppend(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local valList::List{Values.Value}
                  local valList1::List{Values.Value}
                  local valList2::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.LIST(valList2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      valList = listAppend(valList1, valList2)
                    (cache, Values.LIST(valList))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListReverse(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local valList::List{Values.Value}
                  local valList1::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(valList1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      valList = listReverse(valList1)
                    (cache, Values.LIST(valList))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListRest(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local valList1::List{Values.Value}
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(_cons(_, valList1))) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                    (cache, Values.LIST(valList1))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListMember(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local vals::List{Values.Value}
                  local val::Values.Value
                  local b::Bool
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      (cache, val) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.LIST(vals)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      b = listMember(val, vals)
                    (cache, Values.BOOL(b))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalListArrayLiteral(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local vals::List{Values.Value}
                  local val::Values.Value
                  local b::Bool
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(vals)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                    (cache, Values.META_ARRAY(vals))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalAnyString(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local v::Values.Value
                  local s::String
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      s = ValuesUtil.valString(v)
                    (cache, Values.STRING(s))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalNumBits(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (_, _,  nil(), _, _, _)  => begin
                      i = System.numBits()
                    (inCache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalIntegerMax(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local i::ModelicaInteger
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (_, _,  nil(), _, _, _)  => begin
                      i = System.intMaxLit()
                    (inCache, Values.INTEGER(i))
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalIntBitAnd(cache::FCore.Cache, env::FCore.Graph, args::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local result::Values.Value


              local e1::DAE.Exp
              local e2::DAE.Exp
              local i1::ModelicaInteger
              local i2::ModelicaInteger

              @match _cons(e1, _cons(e2, _)) = args
              @match (cache, Values.INTEGER(i1)) = ceval(cache, env, e1, impl, msg, numIter + 1)
              @match (cache, Values.INTEGER(i2)) = ceval(cache, env, e2, impl, msg, numIter + 1)
              result = Values.INTEGER(intBitAnd(i1, i2))
          (cache, result)
        end

        function cevalIntBitOr(cache::FCore.Cache, env::FCore.Graph, args::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local result::Values.Value


              local e1::DAE.Exp
              local e2::DAE.Exp
              local i1::ModelicaInteger
              local i2::ModelicaInteger

              @match _cons(e1, _cons(e2, _)) = args
              @match (cache, Values.INTEGER(i1)) = ceval(cache, env, e1, impl, msg, numIter + 1)
              @match (cache, Values.INTEGER(i2)) = ceval(cache, env, e2, impl, msg, numIter + 1)
              result = Values.INTEGER(intBitOr(i1, i2))
          (cache, result)
        end

        function cevalIntBitXor(cache::FCore.Cache, env::FCore.Graph, args::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local result::Values.Value


              local e1::DAE.Exp
              local e2::DAE.Exp
              local i1::ModelicaInteger
              local i2::ModelicaInteger

              @match _cons(e1, _cons(e2, _)) = args
              @match (cache, Values.INTEGER(i1)) = ceval(cache, env, e1, impl, msg, numIter + 1)
              @match (cache, Values.INTEGER(i2)) = ceval(cache, env, e2, impl, msg, numIter + 1)
              result = Values.INTEGER(intBitXor(i1, i2))
          (cache, result)
        end

        function cevalIntBitLShift(cache::FCore.Cache, env::FCore.Graph, args::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local result::Values.Value


              local e1::DAE.Exp
              local e2::DAE.Exp
              local i::ModelicaInteger
              local s::ModelicaInteger

              @match _cons(e1, _cons(e2, _)) = args
              @match (cache, Values.INTEGER(i)) = ceval(cache, env, e1, impl, msg, numIter + 1)
              @match (cache, Values.INTEGER(s)) = ceval(cache, env, e2, impl, msg, numIter + 1)
              result = Values.INTEGER(intBitLShift(i, s))
          (cache, result)
        end

        function cevalIntBitRShift(cache::FCore.Cache, env::FCore.Graph, args::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local result::Values.Value


              local e1::DAE.Exp
              local e2::DAE.Exp
              local i::ModelicaInteger
              local s::ModelicaInteger

              @match _cons(e1, _cons(e2, _)) = args
              @match (cache, Values.INTEGER(i)) = ceval(cache, env, e1, impl, msg, numIter + 1)
              @match (cache, Values.INTEGER(s)) = ceval(cache, env, e2, impl, msg, numIter + 1)
              result = Values.INTEGER(intBitRShift(i, s))
          (cache, result)
        end

         #= Needed to be able to resolve modelica: during runtime, etc.
        Should not be part of CevalScript since ModelicaServices needs this feature and the frontend needs to take care of it. =#
        function makeLoadLibrariesEntry(cl::SCode.Element, acc::List{<:Values.Value}) ::List{Values.Value}
              local out::List{Values.Value}

              out = begin
                  local name::String
                  local fileName::String
                  local dir::String
                  local v::Values.Value
                  local b::Bool
                @match (cl, acc) begin
                  (SCode.CLASS(info = SOURCEINFO(fileName = "<interactive>")), _)  => begin
                    acc
                  end

                  (SCode.CLASS(name = name, info = SOURCEINFO(fileName = fileName)), _)  => begin
                      dir = System.dirname(fileName)
                      fileName = System.basename(fileName)
                      v = ValuesUtil.makeArray(list(Values.STRING(name), Values.STRING(dir)))
                      b = stringEq(fileName, "ModelicaBuiltin.mo") || stringEq(fileName, "MetaModelicaBuiltin.mo") || stringEq(dir, ".")
                    ListUtil.consOnTrue(! b, v, acc)
                  end
                end
              end
          out
        end

        function cevalListFirst(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local v::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.LIST(_cons(v, _))) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                    (cache, ValuesUtil.boxIfUnboxedVal(v))
                  end
                end
              end
          (outCache, outValue)
        end

        function extractValueStringChar(val::Values.Value) ::String
              local str::String

              str = begin
                @match val begin
                  Values.STRING(str)  => begin
                      @match 1 = stringLength(str)
                    str
                  end
                end
              end
          str
        end

         #= evaluates the cat operator given a list of
          array values and a concatenation dimension. =#
        function cevalCat(v_lst::List{<:Values.Value}, dim::ModelicaInteger) ::Values.Value
              local outValue::Values.Value

              local v_lst_1::List{Values.Value}

              v_lst_1 = catDimension(v_lst, dim)
              outValue = ValuesUtil.makeArray(v_lst_1)
          outValue
        end

         #= Helper function to cevalCat, concatenates a list
          arrays as Values, given a dimension as integer. =#
        function catDimension(inValuesValueLst::List{<:Values.Value}, inInteger::ModelicaInteger) ::List{Values.Value}
              local outValuesValueLst::List{Values.Value}

              outValuesValueLst = begin
                  local vlst_lst::List{List{Values.Value}}
                  local v_lst_lst::List{List{Values.Value}}
                  local v_lst_lst_1::List{List{Values.Value}}
                  local v_lst_1::List{Values.Value}
                  local vlst::List{Values.Value}
                  local vlst2::List{Values.Value}
                  local dim_1::ModelicaInteger
                  local dim::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local il::List{ModelicaInteger}
                @matchcontinue (inValuesValueLst, inInteger) begin
                  (vlst, 1)  => begin
                      vlst_lst = ListUtil.map(vlst, ValuesUtil.arrayValues)
                      v_lst_1 = ListUtil.flatten(vlst_lst)
                    v_lst_1
                  end

                  (vlst, dim)  => begin
                      v_lst_lst = ListUtil.map(vlst, ValuesUtil.arrayValues)
                      dim_1 = dim - 1
                      v_lst_lst_1 = catDimension2(v_lst_lst, dim_1)
                      v_lst_1 = ListUtil.map(v_lst_lst_1, ValuesUtil.makeArray)
                      @match _cons(Values.ARRAY(dimLst = _cons(i2, il)), _) = v_lst_1
                      i1 = listLength(v_lst_1)
                      v_lst_1 = cevalBuiltinTranspose2(v_lst_1, 1, _cons(i2, _cons(i1, il)))
                    v_lst_1
                  end
                end
              end
               #= /* base case for first dimension */ =#
          outValuesValueLst
        end

         #= author: PA
          Helper function to catDimension. =#
        function catDimension2(inValuesValueLstLst::List{<:List{<:Values.Value}}, inInteger::ModelicaInteger) ::List{List{Values.Value}}
              local outValuesValueLstLst::List{List{Values.Value}}

              outValuesValueLstLst = begin
                  local l_lst::List{Values.Value}
                  local first_lst::List{Values.Value}
                  local first_lst_1::List{Values.Value}
                  local first_lst_2::List{List{Values.Value}}
                  local lst::List{List{Values.Value}}
                  local rest::List{List{Values.Value}}
                  local rest_1::List{List{Values.Value}}
                  local res::List{List{Values.Value}}
                  local dim::ModelicaInteger
                @matchcontinue (inValuesValueLstLst, inInteger) begin
                  (lst, dim)  => begin
                      l_lst = listHead(lst)
                      @match 1 = listLength(l_lst)
                      first_lst = ListUtil.map(lst, listHead)
                      first_lst_1 = catDimension(first_lst, dim)
                      first_lst_2 = ListUtil.map(first_lst_1, ListUtil.create)
                    first_lst_2
                  end

                  (lst, dim)  => begin
                      first_lst = ListUtil.map(lst, listHead)
                      rest = ListUtil.map(lst, ListUtil.rest)
                      first_lst_1 = catDimension(first_lst, dim)
                      rest_1 = catDimension2(rest, dim)
                      res = ListUtil.threadMap(rest_1, first_lst_1, ListUtil.consr)
                    res
                  end
                end
              end
          outValuesValueLstLst
        end

         #= author: LP
          evaluates the floor operator. =#
        function cevalBuiltinFloor(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = floor(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          evaluates the ceil operator. =#
        function cevalBuiltinCeil(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local rvt::ModelicaReal
                  local realRet::ModelicaReal
                  local ri::ModelicaInteger
                  local ri_1::ModelicaInteger
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local v::Values.Value
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = floor(rv)
                      ri = realInt(rv_1)
                      rvt = intReal(ri)
                      ri_1 = ri + 1
                      realRet = intReal(ri_1)
                      v = if rvt == rv
                            Values.REAL(rvt)
                          else
                            Values.REAL(realRet)
                          end
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin sqrt operator. =#
        function cevalBuiltinSqrt(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local info::SourceInfo
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      if rv < 0.0
                        @match Absyn.MSG(info = info) = msg
                        Error.addSourceMessage(Error.NEGATIVE_SQRT, nil, info)
                        fail()
                      else
                        rv_1 = sqrt(rv)
                      end
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin sin function. =#
        function cevalBuiltinSin(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = sin(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin sinh function. =#
        function cevalBuiltinSinh(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = sinh(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin cos function. =#
        function cevalBuiltinCos(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = cos(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin cosh function. =#
        function cevalBuiltinCosh(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = cosh(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin Log function. =#
        function cevalBuiltinLog(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match true = rv > 0
                      rv_1 = log(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
               #=  TODO: Print error-message?
               =#
          (outCache, outValue)
        end

        function cevalBuiltinLog10(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match true = rv > 0
                      rv_1 = log10(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
               #=  TODO: Print error-message?
               =#
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin tan function. =#
        function cevalBuiltinTan(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst) begin
                  (cache, env, exp <|  nil())  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = tan(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin tanh function. =#
        function cevalBuiltinTanh(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = tanh(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin asin function. =#
        function cevalBuiltinAsin(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match true = rv >= (-1.0) && rv <= 1.0
                      rv_1 = asin(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin acos function. =#
        function cevalBuiltinAcos(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      @match true = rv >= (-1.0) && rv <= 1.0
                      rv_1 = acos(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Evaluates the builtin atan function. =#
        function cevalBuiltinAtan(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      rv_1 = atan(rv)
                    (cache, Values.REAL(rv_1))
                  end
                end
              end
               #= /* atan is not implemented in MetaModelica Compiler (MMC) for some strange reason. */ =#
          (outCache, outValue)
        end

        function cevalBuiltinAtan2(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local rv_1::ModelicaReal
                  local rv_2::ModelicaReal
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv_1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(rv_2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      rv = atan2(rv_1, rv_2)
                    (cache, Values.REAL(rv))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin div operator. =#
        function cevalBuiltinDiv(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local rv_1::ModelicaReal
                  local rv_2::ModelicaReal
                  local ri::ModelicaInteger
                  local ri_1::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local exp1_str::String
                  local exp2_str::String
                  local lh_str::String
                  local rh_str::String
                  local cache::FCore.Cache
                  local b::Bool
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      rv_1 = rv1 / rv2
                      b = rv_1 < 0.0
                      rv_2 = if b
                            ceil(rv_1)
                          else
                            floor(rv_1)
                          end
                    (cache, Values.REAL(rv_2))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(ri)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      rv1 = intReal(ri)
                      @match (cache, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      Error.addInternalError("cevalBuiltinDiv got Integer and Real (type error)\\n", sourceInfo())
                      rv_1 = rv1 / rv2
                      b = rv_1 < 0.0
                      rv_2 = if b
                            ceil(rv_1)
                          else
                            floor(rv_1)
                          end
                    (cache, Values.REAL(rv_2))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(ri)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      Error.addInternalError("cevalBuiltinDiv got Real and Integer (type error)\\n", sourceInfo())
                      rv2 = intReal(ri)
                      rv_1 = rv1 / rv2
                      b = rv_1 < 0.0
                      rv_2 = if b
                            ceil(rv_1)
                          else
                            floor(rv_1)
                          end
                    (cache, Values.REAL(rv_2))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(ri1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(ri2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      ri_1 = intDiv(ri1, ri2)
                    (cache, Values.INTEGER(ri_1))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, Absyn.MSG(info = info), _)  => begin
                      @match (_, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, inMsg, numIter + 1)
                      if ! rv2 == 0.0
                        fail()
                      end
                      exp1_str = CrefForHashTable.printExpStr(exp1)
                      exp2_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.DIVISION_BY_ZERO, list(exp1_str, exp2_str), info)
                    fail()
                  end

                  (cache, env, _ <| exp2 <|  nil(), impl, Absyn.NO_MSG(__), _)  => begin
                      @match (_, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, Absyn.NO_MSG(), numIter + 1)
                      if ! rv2 == 0.0
                        fail()
                      end
                    fail()
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, Absyn.MSG(info = info), _)  => begin
                      @match (_, Values.INTEGER(ri2)) = ceval(cache, env, exp2, impl, inMsg, numIter + 1)
                      if ! ri2 == 0
                        fail()
                      end
                      lh_str = CrefForHashTable.printExpStr(exp1)
                      rh_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.DIVISION_BY_ZERO, list(lh_str, rh_str), info)
                    fail()
                  end

                  (cache, env, _ <| exp2 <|  nil(), impl, Absyn.NO_MSG(__), _)  => begin
                      @match (_, Values.INTEGER(ri2)) = ceval(cache, env, exp2, impl, Absyn.NO_MSG(), numIter + 1)
                      if ! ri2 == 0
                        fail()
                      end
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin mod operator. =#
        function cevalBuiltinMod(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local cache::FCore.Cache = inCache

              local v1::Values.Value
              local v2::Values.Value
              local exp1::DAE.Exp
              local exp2::DAE.Exp

              @match list(exp1, exp2) = inExpExpLst
              (cache, v1) = ceval(cache, inEnv, exp1, impl, msg, numIter + 1)
              (cache, v2) = ceval(cache, inEnv, exp2, impl, msg, numIter + 1)
              outValue = begin
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local ri::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local lhs_str::String
                  local rhs_str::String
                  local info::SourceInfo
                @match (v1, v2, msg) begin
                  (Values.REAL(rv1), Values.REAL(rv2), _)  => begin
                    Values.REAL(mod(rv1, rv2))
                  end

                  (Values.INTEGER(ri), Values.REAL(rv2), _)  => begin
                    Values.REAL(mod(ri, rv2))
                  end

                  (Values.REAL(rv1), Values.INTEGER(ri), _)  => begin
                    Values.REAL(mod(rv1, ri))
                  end

                  (Values.INTEGER(ri1), Values.INTEGER(ri2), _)  => begin
                    Values.INTEGER(mod(ri1, ri2))
                  end

                  (_, Values.REAL(rv2), Absyn.MSG(info = info)) where (rv2 == 0.0)  => begin
                      lhs_str = CrefForHashTable.printExpStr(exp1)
                      rhs_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.MODULO_BY_ZERO, list(lhs_str, rhs_str), info)
                    fail()
                  end

                  (_, Values.INTEGER(0), Absyn.MSG(info = info))  => begin
                      lhs_str = CrefForHashTable.printExpStr(exp1)
                      rhs_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.MODULO_BY_ZERO, list(lhs_str, rhs_str), info)
                    fail()
                  end
                end
              end
          (cache, outValue)
        end

         #= Evaluates the builtin sum function. =#
        function cevalBuiltinSum(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local v::Values.Value
                  local vals::List{Values.Value}
                  local env::FCore.Graph
                  local arr::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, arr <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = vals)) = ceval(cache, env, arr, impl, msg, numIter + 1)
                      if Types.isInteger(Expression.typeof(arr))
                        if listEmpty(vals)
                          v = Values.INTEGER(0)
                        else
                          @match (@match Values.INTEGER() = v) = ValuesUtil.sumArrayelt(vals)
                        end
                      else
                        if listEmpty(vals)
                          v = Values.REAL(0.0)
                        else
                          @match (@match Values.REAL() = v) = ValuesUtil.sumArrayelt(vals)
                        end
                      end
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin max function. =#
        function cevalBuiltinMax(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local v::Values.Value
                  local v1::Values.Value
                  local v2::Values.Value
                  local v_1::Values.Value
                  local env::FCore.Graph
                  local arr::DAE.Exp
                  local s1::DAE.Exp
                  local s2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, arr <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, arr, impl, msg, numIter + 1)
                      v_1 = cevalBuiltinMaxArr(v)
                    (cache, v_1)
                  end

                  (cache, env, s1 <| s2 <|  nil(), impl, msg, _)  => begin
                      (cache, v1) = ceval(cache, env, s1, impl, msg, numIter + 1)
                      (cache, v2) = ceval(cache, env, s2, impl, msg, numIter + 1)
                      v = cevalBuiltinMax2(v1, v2)
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalBuiltinMax2(v1::Values.Value, v2::Values.Value) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local b1::Bool
                  local b2::Bool
                  local s1::String
                  local s2::String
                @match (v1, v2) begin
                  (Values.INTEGER(i1), Values.INTEGER(i2))  => begin
                    Values.INTEGER(max(i1, i2))
                  end

                  (Values.REAL(r1), Values.REAL(r2))  => begin
                    Values.REAL(max(r1, r2))
                  end

                  (Values.BOOL(b1), Values.BOOL(b2))  => begin
                    Values.BOOL(b1 || b2)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    if v1.index > v2.index
                          v1
                        else
                          v2
                        end
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        s1 = ValuesUtil.valString(v1)
                        s2 = ValuesUtil.valString(v2)
                        Debug.traceln("- Ceval.cevalBuiltinMin2 failed: min(" + s1 + ", " + s2 + ")")
                      fail()
                  end
                end
              end
          outValue
        end

         #= Helper function to cevalBuiltinMax. =#
        function cevalBuiltinMaxArr(inValue::Values.Value) ::Values.Value
              local outValue::Values.Value

              local vals::List{Values.Value}

              @match Values.ARRAY(valueLst = vals) = inValue
              outValue = cevalBuiltinMax2(v for v in vals)
          outValue
        end

         #= author: PA
          Constant evaluation of builtin min function. =#
        function cevalBuiltinMin(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local v::Values.Value
                  local v1::Values.Value
                  local v2::Values.Value
                  local v_1::Values.Value
                  local env::FCore.Graph
                  local arr::DAE.Exp
                  local s1::DAE.Exp
                  local s2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, arr <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, arr, impl, msg, numIter + 1)
                      v_1 = cevalBuiltinMinArr(v)
                    (cache, v_1)
                  end

                  (cache, env, s1 <| s2 <|  nil(), impl, msg, _)  => begin
                      (cache, v1) = ceval(cache, env, s1, impl, msg, numIter + 1)
                      (cache, v2) = ceval(cache, env, s2, impl, msg, numIter + 1)
                      v = cevalBuiltinMin2(v1, v2)
                    (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalBuiltinMin2(v1::Values.Value, v2::Values.Value) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local b1::Bool
                  local b2::Bool
                  local s1::String
                  local s2::String
                  local info::SourceInfo
                @match (v1, v2) begin
                  (Values.INTEGER(i1), Values.INTEGER(i2))  => begin
                    Values.INTEGER(min(i1, i2))
                  end

                  (Values.REAL(r1), Values.REAL(r2))  => begin
                    Values.REAL(min(r1, r2))
                  end

                  (Values.BOOL(b1), Values.BOOL(b2))  => begin
                    Values.BOOL(b1 && b2)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    if v1.index < v2.index
                          v1
                        else
                          v2
                        end
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        s1 = ValuesUtil.valString(v1)
                        s2 = ValuesUtil.valString(v2)
                        Debug.traceln("- Ceval.cevalBuiltinMin2 failed: min(" + s1 + ", " + s2 + ")")
                      fail()
                  end
                end
              end
          outValue
        end

         #= Helper function to cevalBuiltinMin. =#
        function cevalBuiltinMinArr(inValue::Values.Value) ::Values.Value
              local outValue::Values.Value

              local vals::List{Values.Value}

              @match Values.ARRAY(valueLst = vals) = inValue
              outValue = cevalBuiltinMin2(v for v in vals)
          outValue
        end

         #= author: LP
          Evaluates the builtin rem operator =#
        function cevalBuiltinRem(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv1::ModelicaReal
                  local rv2::ModelicaReal
                  local rvd::ModelicaReal
                  local dr::ModelicaReal
                  local ri::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local ri_1::ModelicaInteger
                  local di::ModelicaInteger
                  local env::FCore.Graph
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local exp1_str::String
                  local exp2_str::String
                  local cache::FCore.Cache
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(dr)) = cevalBuiltinDiv(cache, env, list(exp1, exp2), impl, msg, numIter + 1)
                      rvd = rv1 - rv2 * dr
                    (cache, Values.REAL(rvd))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(ri)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      rv1 = intReal(ri)
                      @match (cache, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      @match (cache, Values.REAL(dr)) = cevalBuiltinDiv(cache, env, list(exp1, exp2), impl, msg, numIter + 1)
                      rvd = rv1 - rv2 * dr
                    (cache, Values.REAL(rvd))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(ri)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      rv2 = intReal(ri)
                      @match (cache, Values.REAL(dr)) = cevalBuiltinDiv(cache, env, list(exp1, exp2), impl, msg, numIter + 1)
                      rvd = rv1 - rv2 * dr
                    (cache, Values.REAL(rvd))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.INTEGER(ri1)) = ceval(cache, env, exp1, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(ri2)) = ceval(cache, env, exp2, impl, msg, numIter + 1)
                      @match (cache, Values.INTEGER(di)) = cevalBuiltinDiv(cache, env, list(exp1, exp2), impl, msg, numIter + 1)
                      ri_1 = ri1 - ri2 * di
                    (cache, Values.INTEGER(ri_1))
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, Absyn.MSG(info = info), _)  => begin
                      @match (_, Values.REAL(rv2)) = ceval(cache, env, exp2, impl, inMsg, numIter + 1)
                      if ! rv2 == 0.0
                        fail()
                      end
                      exp1_str = CrefForHashTable.printExpStr(exp1)
                      exp2_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.REM_ARG_ZERO, list(exp1_str, exp2_str), info)
                    fail()
                  end

                  (cache, env, exp1 <| exp2 <|  nil(), impl, Absyn.MSG(info = info), _)  => begin
                      @match (_, Values.INTEGER(ri2)) = ceval(cache, env, exp2, impl, inMsg, numIter + 1)
                      if ! ri2 == 0
                        fail()
                      end
                      exp1_str = CrefForHashTable.printExpStr(exp1)
                      exp2_str = CrefForHashTable.printExpStr(exp2)
                      Error.addSourceMessage(Error.REM_ARG_ZERO, list(exp1_str, exp2_str), info)
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin integer operator =#
        function cevalBuiltinInteger(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local ri::ModelicaInteger
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.REAL(rv)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      ri = realInt(rv)
                    (cache, Values.INTEGER(ri))
                  end
                end
              end
          (outCache, outValue)
        end

         #=  @author: adrpo
          Evaluates the builtin boolean operator =#
        function cevalBuiltinBoolean(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local rv::ModelicaReal
                  local iv::ModelicaInteger
                  local bv::Bool
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local b::Bool
                  local v::Values.Value
                   #=  real/integer/bool -> bool
                   =#
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      b = begin
                        @match v begin
                          Values.REAL(rv)  => begin
                            ! realEq(rv, 0.0)
                          end

                          Values.INTEGER(iv)  => begin
                            ! intEq(iv, 0)
                          end

                          Values.BOOL(bv)  => begin
                            bv
                          end
                        end
                      end
                    (cache, Values.BOOL(b))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: adrpo
          Evaluates the builtin rooted operator from MultiBody =#
        function cevalBuiltinRooted(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      (cache, _) = ceval(cache, env, exp, impl, msg, numIter + 1)
                    (cache, Values.BOOL(true))
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: LP
          Evaluates the builtin Integer operator =#
        function cevalBuiltinIntegerEnumeration(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local ri::ModelicaInteger
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.ENUM_LITERAL(index = ri)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                    (cache, Values.INTEGER(ri))
                  end
                end
              end
          (outCache, outValue)
        end

         #= This function generates a matrix{n,n} (A) of the vector {a,b,...,n}
          where the diagonal of A is the vector {a,b,...,n}
          ie A{1,1} == a, A{2,2} == b ... =#
        function cevalBuiltinDiagonal(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local vals::List{Values.Value}
                  local retExp::List{Values.Value}
                  local dimension::ModelicaInteger
                  local correctDimension::ModelicaInteger
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local res::Values.Value
                  local info::SourceInfo
                  local zero::Values.Value
                  local ty::DAE.Type
                @matchcontinue (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, exp <|  nil(), impl, msg, _)  => begin
                      @match DAE.T_ARRAY(ty = ty) = Expression.typeof(exp)
                      @match (cache, Values.ARRAY(vals, list(dimension))) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      zero = ValuesUtil.makeZero(ty)
                      res = Values.ARRAY(list(Values.ARRAY(list(if i == j
                            listGet(vals, i)
                          else
                            zero
                          end for i in 1:dimension), list(dimension)) for j in 1:dimension), list(dimension, dimension))
                    (cache, res)
                  end

                  (_, _, _, _, Absyn.MSG(info = info), _)  => begin
                      Error.addSourceMessage(Error.COMPILER_ERROR, list("Could not evaluate diagonal. Ceval.cevalBuiltinDiagonal failed."), info)
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #=
          x,y => {x[2]*y[3]-x[3]*y[2],x[3]*y[1]-x[1]*y[3],x[1]*y[2]-x[2]*y[1]} =#
        function cevalBuiltinCross(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local xv::List{Values.Value}
                  local yv::List{Values.Value}
                  local res::Values.Value
                  local env::FCore.Graph
                  local xe::DAE.Exp
                  local ye::DAE.Exp
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local str::String
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inExpExpLst, inBoolean, inMsg, numIter) begin
                  (cache, env, xe <| ye <|  nil(), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(xv, list(3))) = ceval(cache, env, xe, impl, msg, numIter + 1)
                      @match (cache, Values.ARRAY(yv, list(3))) = ceval(cache, env, ye, impl, msg, numIter + 1)
                      res = ValuesUtil.crossProduct(xv, yv)
                    (cache, res)
                  end

                  (_, _, _, _, Absyn.MSG(info = info), _)  => begin
                      str = "cross" + CrefForHashTable.printExpStr(DAE.TUPLE(inExpExpLst))
                      Error.addSourceMessage(Error.FAILED_TO_EVALUATE_EXPRESSION, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #= author: PA
          Helper function to cevalBuiltinTranspose =#
        function cevalBuiltinTranspose2(inValuesValueLst1::List{<:Values.Value}, inInteger2::ModelicaInteger #= index =#, inDims::List{<:ModelicaInteger} #= dimension =#) ::List{Values.Value}
              local outValuesValueLst::List{Values.Value}

              outValuesValueLst = begin
                  local transposed_row::List{Values.Value}
                  local rest::List{Values.Value}
                  local vlst::List{Values.Value}
                  local indx_1::ModelicaInteger
                  local indx::ModelicaInteger
                  local dim1::ModelicaInteger
                @matchcontinue (inValuesValueLst1, inInteger2, inDims) begin
                  (vlst, indx, dim1 <| _)  => begin
                      if ! indx <= dim1
                        fail()
                      end
                      transposed_row = ListUtil.map1(vlst, ValuesUtil.nthArrayelt, indx)
                      indx_1 = indx + 1
                      rest = cevalBuiltinTranspose2(vlst, indx_1, inDims)
                    _cons(Values.ARRAY(transposed_row, inDims), rest)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outValuesValueLst
        end

         #= Helper function for cevalBuiltinSize, for size(A) where A is a matrix. =#
        function cevalBuiltinSizeMatrix(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local tp::DAE.Type
                  local sizelst::List{ModelicaInteger}
                  local v::Values.Value
                  local env::FCore.Graph
                  local cr::DAE.ComponentRef
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local exp::DAE.Exp
                  local dims::DAE.Dimensions
                   #=  size(cr)
                   =#
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inMsg, numIter) begin
                  (cache, env, DAE.CREF(componentRef = cr), _, _, _)  => begin
                      (cache, _, tp, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr)
                      sizelst = Types.getDimensionSizes(tp)
                      v = ValuesUtil.intlistToValue(sizelst)
                    (cache, v)
                  end

                  (cache, _, DAE.MATRIX(ty = DAE.T_ARRAY(dims = dims)), _, _, _)  => begin
                      sizelst = ListUtil.map(dims, Expression.dimensionSize)
                      v = ValuesUtil.intlistToValue(sizelst)
                    (cache, v)
                  end

                  (cache, env, exp, impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(dimLst = sizelst)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      v = ValuesUtil.intlistToValue(sizelst)
                    (cache, v)
                  end
                end
              end
               #=  For matrix expressions: [1,2;3,4]
               =#
               #=  For other matrix expressions e.g. on array form: {{1,2},{3,4}}
               =#
          (outCache, outValue)
        end

         #= This function constant evaluates calls to the fail() function. =#
        function cevalBuiltinFail(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:DAE.Exp}, inImpl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              outCache = inCache
              outValue = Values.META_FAIL()
          (outCache, outValue)
        end

         #= This function constant evaluates calls to the fill function. =#
        function cevalBuiltinFill(inCache::FCore.Cache, inEnv::FCore.Graph, inExpl::List{<:DAE.Exp}, inImpl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local fill_exp::DAE.Exp
                  local dims::List{DAE.Exp}
                  local fill_val::Values.Value
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpl, inImpl, inMsg, numIter) begin
                  (cache, _, fill_exp <| dims, _, _, _)  => begin
                      (cache, fill_val) = ceval(cache, inEnv, fill_exp, inImpl, inMsg, numIter + 1)
                      (cache, fill_val) = cevalBuiltinFill2(cache, inEnv, fill_val, dims, inImpl, inMsg, numIter)
                    (cache, fill_val)
                  end
                end
              end
          (outCache, outValue)
        end

        function cevalBuiltinFill2(inCache::FCore.Cache, inEnv::FCore.Graph, inFillValue::Values.Value, inDims::List{<:DAE.Exp}, inImpl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local dim::DAE.Exp
                  local rest_dims::List{DAE.Exp}
                  local int_dim::ModelicaInteger
                  local array_dims::List{ModelicaInteger}
                  local fill_value::Values.Value
                  local fill_vals::List{Values.Value}
                  local cache::FCore.Cache
                @match (inCache, inEnv, inFillValue, inDims, inImpl, inMsg, numIter) begin
                  (cache, _, _,  nil(), _, _, _)  => begin
                    (cache, inFillValue)
                  end

                  (cache, _, _, dim <| rest_dims, _, _, _)  => begin
                      (cache, fill_value) = cevalBuiltinFill2(cache, inEnv, inFillValue, rest_dims, inImpl, inMsg, numIter)
                      @match (cache, Values.INTEGER(int_dim)) = ceval(cache, inEnv, dim, inImpl, inMsg, numIter + 1)
                      fill_vals = ListUtil.fill(fill_value, int_dim)
                      array_dims = ValuesUtil.valueDimensions(fill_value)
                      array_dims = _cons(int_dim, array_dims)
                    (cache, Values.ARRAY(fill_vals, array_dims))
                  end
                end
              end
          (outCache, outValue)
        end

         #= Performs the arithmetic relation check and gives a boolean result. =#
        function cevalRelation(inValue1::Values.Value, inOperator::DAE.Operator, inValue2::Values.Value) ::Values.Value
              local outValue::Values.Value

              local result::Bool

              result = begin
                @matchcontinue inOperator begin
                  DAE.GREATER(__)  => begin
                    cevalRelationLess(inValue2, inValue1)
                  end

                  DAE.LESS(__)  => begin
                    cevalRelationLess(inValue1, inValue2)
                  end

                  DAE.LESSEQ(__)  => begin
                    cevalRelationLessEq(inValue1, inValue2)
                  end

                  DAE.GREATEREQ(__)  => begin
                    cevalRelationGreaterEq(inValue1, inValue2)
                  end

                  DAE.EQUAL(__)  => begin
                    cevalRelationEqual(inValue1, inValue2)
                  end

                  DAE.NEQUAL(__)  => begin
                    cevalRelationNotEqual(inValue1, inValue2)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Ceval.cevalRelation failed on: " + ValuesUtil.printValStr(inValue1) + CrefForHashTable.relopSymbol(inOperator) + ValuesUtil.printValStr(inValue2))
                      fail()
                  end
                end
              end
              outValue = Values.BOOL(result)
          outValue
        end

         #= Returns whether the first value is less than the second value. =#
        function cevalRelationLess(inValue1::Values.Value, inValue2::Values.Value) ::Bool
              local result::Bool

              result = begin
                @match (inValue1, inValue2) begin
                  (Values.STRING(__), Values.STRING(__))  => begin
                    stringCompare(inValue1.string, inValue2.string) < 0
                  end

                  (Values.BOOL(__), Values.BOOL(__))  => begin
                    inValue1.boolean < inValue2.boolean
                  end

                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    inValue1.integer < inValue2.integer
                  end

                  (Values.REAL(__), Values.REAL(__))  => begin
                    inValue1.real < inValue2.real
                  end

                  (Values.INTEGER(__), Values.REAL(__))  => begin
                    intReal(inValue1.integer) < inValue2.real
                  end

                  (Values.REAL(__), Values.INTEGER(__))  => begin
                    inValue1.real < intReal(inValue2.integer)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.index < inValue2.index
                  end

                  (Values.ENUM_LITERAL(__), Values.INTEGER(__))  => begin
                    inValue1.index < inValue2.integer
                  end

                  (Values.INTEGER(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.integer < inValue2.index
                  end
                end
              end
          result
        end

         #= Returns whether the first value is less than or equal to the second value. =#
        function cevalRelationLessEq(inValue1::Values.Value, inValue2::Values.Value) ::Bool
              local result::Bool

              result = begin
                @match (inValue1, inValue2) begin
                  (Values.STRING(__), Values.STRING(__))  => begin
                    stringCompare(inValue1.string, inValue2.string) <= 0
                  end

                  (Values.BOOL(__), Values.BOOL(__))  => begin
                    inValue1.boolean <= inValue2.boolean
                  end

                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    inValue1.integer <= inValue2.integer
                  end

                  (Values.REAL(__), Values.REAL(__))  => begin
                    inValue1.real <= inValue2.real
                  end

                  (Values.INTEGER(__), Values.REAL(__))  => begin
                    intReal(inValue1.integer) <= inValue2.real
                  end

                  (Values.REAL(__), Values.INTEGER(__))  => begin
                    inValue1.real <= intReal(inValue2.integer)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.index <= inValue2.index
                  end

                  (Values.ENUM_LITERAL(__), Values.INTEGER(__))  => begin
                    inValue1.index <= inValue2.integer
                  end

                  (Values.INTEGER(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.integer <= inValue2.index
                  end
                end
              end
          result
        end

         #= Returns whether the first value is greater than or equal to the second value. =#
        function cevalRelationGreaterEq(inValue1::Values.Value, inValue2::Values.Value) ::Bool
              local result::Bool

              result = begin
                @match (inValue1, inValue2) begin
                  (Values.STRING(__), Values.STRING(__))  => begin
                    stringCompare(inValue1.string, inValue2.string) >= 0
                  end

                  (Values.BOOL(__), Values.BOOL(__))  => begin
                    inValue1.boolean >= inValue2.boolean
                  end

                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    inValue1.integer >= inValue2.integer
                  end

                  (Values.REAL(__), Values.REAL(__))  => begin
                    inValue1.real >= inValue2.real
                  end

                  (Values.INTEGER(__), Values.REAL(__))  => begin
                    intReal(inValue1.integer) >= inValue2.real
                  end

                  (Values.REAL(__), Values.INTEGER(__))  => begin
                    inValue1.real >= intReal(inValue2.integer)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.index >= inValue2.index
                  end

                  (Values.ENUM_LITERAL(__), Values.INTEGER(__))  => begin
                    inValue1.index >= inValue2.integer
                  end

                  (Values.INTEGER(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.integer >= inValue2.index
                  end
                end
              end
          result
        end

         #= Returns whether the first value is equal to the second value. =#
        function cevalRelationEqual(inValue1::Values.Value, inValue2::Values.Value) ::Bool
              local result::Bool

              result = begin
                @match (inValue1, inValue2) begin
                  (Values.STRING(__), Values.STRING(__))  => begin
                    stringCompare(inValue1.string, inValue2.string) == 0
                  end

                  (Values.BOOL(__), Values.BOOL(__))  => begin
                    inValue1.boolean == inValue2.boolean
                  end

                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    inValue1.integer == inValue2.integer
                  end

                  (Values.REAL(__), Values.REAL(__))  => begin
                    inValue1.real == inValue2.real
                  end

                  (Values.INTEGER(__), Values.REAL(__))  => begin
                    intReal(inValue1.integer) == inValue2.real
                  end

                  (Values.REAL(__), Values.INTEGER(__))  => begin
                    inValue1.real == intReal(inValue2.integer)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.index == inValue2.index
                  end

                  (Values.ENUM_LITERAL(__), Values.INTEGER(__))  => begin
                    inValue1.index == inValue2.integer
                  end

                  (Values.INTEGER(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.integer == inValue2.index
                  end
                end
              end
          result
        end

         #= Returns whether the first value is not equal to the second value. =#
        function cevalRelationNotEqual(inValue1::Values.Value, inValue2::Values.Value) ::Bool
              local result::Bool

              result = begin
                @match (inValue1, inValue2) begin
                  (Values.STRING(__), Values.STRING(__))  => begin
                    stringCompare(inValue1.string, inValue2.string) != 0
                  end

                  (Values.BOOL(__), Values.BOOL(__))  => begin
                    inValue1.boolean != inValue2.boolean
                  end

                  (Values.INTEGER(__), Values.INTEGER(__))  => begin
                    inValue1.integer != inValue2.integer
                  end

                  (Values.REAL(__), Values.REAL(__))  => begin
                    inValue1.real != inValue2.real
                  end

                  (Values.INTEGER(__), Values.REAL(__))  => begin
                    intReal(inValue1.integer) != inValue2.real
                  end

                  (Values.REAL(__), Values.INTEGER(__))  => begin
                    inValue1.real != intReal(inValue2.integer)
                  end

                  (Values.ENUM_LITERAL(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.index != inValue2.index
                  end

                  (Values.ENUM_LITERAL(__), Values.INTEGER(__))  => begin
                    inValue1.index != inValue2.integer
                  end

                  (Values.INTEGER(__), Values.ENUM_LITERAL(__))  => begin
                    inValue1.integer != inValue2.index
                  end
                end
              end
          result
        end

         #= Evaluates a range expression on the form enum.lit1 : enum.lit2 =#
        function cevalRangeEnum(startIndex::ModelicaInteger, stopIndex::ModelicaInteger, enumType::DAE.Type) ::List{Values.Value}
              local enumValList::List{Values.Value}

              enumValList = begin
                  local enum_type::Absyn.Path
                  local enum_names::List{String}
                  local enum_paths::List{Absyn.Path}
                  local enum_values::List{Values.Value}
                @match (startIndex, stopIndex, enumType) begin
                  (_, _, DAE.T_ENUMERATION(path = enum_type, names = enum_names))  => begin
                      if ! startIndex <= stopIndex
                        fail()
                      end
                      enum_names = ListUtil.sublist(enum_names, startIndex, stopIndex - startIndex + 1)
                      enum_paths = ListUtil.map(enum_names, AbsynUtil.makeIdentPathFromString)
                      enum_paths = ListUtil.map1r(enum_paths, AbsynUtil.joinPaths, enum_type)
                      (enum_values, _) = ListUtil.mapFold(enum_paths, makeEnumValue, startIndex)
                    enum_values
                  end
                end
              end
          enumValList
        end

        function makeEnumValue(name::Absyn.Path, index::ModelicaInteger) ::Tuple{Values.Value, ModelicaInteger}
              local newIndex::ModelicaInteger
              local enumValue::Values.Value

              enumValue = Values.ENUM_LITERAL(name, index)
              newIndex = index + 1
          (enumValue, newIndex)
        end

         #= This function does constant
          evaluation on a list of expressions. =#
        function cevalList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpExpLst::List{<:DAE.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{Values.Value}}
              local outValuesValueLst::List{Values.Value} = nil
              local outCache::FCore.Cache = inCache

              local expLstNew::List{DAE.Exp} = inExpExpLst
              local v::Values.Value

              for exp in expLstNew
                (outCache, v) = ceval(outCache, inEnv, exp, inBoolean, inMsg, numIter + 1)
                outValuesValueLst = _cons(v, outValuesValueLst)
              end
              outValuesValueLst = listReverseInPlace(outValuesValueLst)
          (outCache, outValuesValueLst)
        end

         #= Evaluates ComponentRef, i.e. variables, by
          looking up variables in the environment. =#
        function cevalCref(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local binding::DAE.Binding
                  local v::Values.Value
                  local env::FCore.Graph
                  local classEnv::FCore.Graph
                  local componentEnv::FCore.Graph
                  local c::DAE.ComponentRef
                  local impl::Bool
                  local msg::Absyn.Msg
                  local scope_str::String
                  local str::String
                  local name::String
                  local cache::FCore.Cache
                  local const_for_range::Option{DAE.Const}
                  local ty::DAE.Type
                  local attr::DAE.Attributes
                  local splicedExpData::InstTypes.SplicedExpData
                  local info::SourceInfo
                   #=  Try to lookup the variables binding and constant evaluate it.
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, inBoolean, inMsg, numIter) begin
                  (cache, env, c, impl, msg, _)  => begin
                      (cache, attr, ty, binding, const_for_range, splicedExpData, classEnv, componentEnv, name) = Lookup.lookupVar(cache, env, c)
                      (cache, v) = cevalCref_dispatch(cache, env, c, attr, ty, binding, const_for_range, splicedExpData, classEnv, componentEnv, name, impl, msg, numIter)
                    (cache, v)
                  end

                  (cache, env, c, false, Absyn.MSG(info = info), _)  => begin
                      @shouldFail (_, _, _, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, c)
                      scope_str = FGraphUtil.printGraphPathStr(env)
                      str = CrefForHashTable.printComponentRefStr(c)
                      Error.addSourceMessage(Error.LOOKUP_VARIABLE_ERROR, list(str, scope_str), info)
                    fail()
                  end
                end
              end
               #=  send the entire shebang to cevalCref2 so we don't have to do lookup var again!
               =#
               #=  failure in lookup and we have the MSG go-ahead to print the error
               =#
               #=  failure in lookup but NO_MSG, silently fail and move along
               =#
               #= /*case (cache,env,c,(impl as false),Absyn.NO_MSG(),_)
                    equation
                      failure((_,_,_,_,_,_,_,_,_) = Lookup.lookupVar(cache,env, c));
                    then
                      fail();*/ =#
          (outCache, outValue)
        end

         #= Helper function to cevalCref =#
        function cevalCref_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::DAE.ComponentRef, inAttr::DAE.Attributes, inType::DAE.Type, inBinding::DAE.Binding, constForRange::Option{<:DAE.Const}, inSplicedExpData::InstTypes.SplicedExpData, inClassEnv::FCore.Graph, inComponentEnv::FCore.Graph, inFQName::String, inImpl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local cache::FCore.Cache
                  local v::Values.Value
                  local str::String
                  local scope_str::String
                  local s1::String
                  local s2::String
                  local s3::String
                  local info::SourceInfo
                  local variability::SCode.Variability
                   #=  A variable with no binding and SOME for range constness -> a for iterator
                   =#
                @match (inCache, inEnv, inCref, inAttr, inType, inBinding, constForRange, inSplicedExpData, inClassEnv, inComponentEnv, inFQName, inImpl, inMsg, numIter) begin
                  (_, _, _, _, _, DAE.UNBOUND(__), SOME(_), _, _, _, _, _, _, _)  => begin
                    fail()
                  end

                  (_, _, _, _, _, DAE.UNBOUND(__), NONE(), _, _, _, _, false, Absyn.MSG(__), _)  => begin
                      str = CrefForHashTable.printComponentRefStr(inCref)
                      scope_str = FGraphUtil.printGraphPathStr(inEnv)
                      if Flags.isSet(Flags.CEVAL)
                        Debug.traceln("- Ceval.cevalCref on: " + str + " failed with no constant binding in scope: " + scope_str)
                      end
                      s1 = FGraphUtil.printGraphPathStr(inEnv)
                      s2 = CrefForHashTable.printComponentRefStr(inCref)
                      s3 = Types.printTypeStr(inType)
                      v = Types.typeToValue(inType)
                      v = Values.EMPTY(s1, s2, v, s3)
                    (inCache, v)
                  end

                  (_, _, _, DAE.ATTR(variability = variability), _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = SCodeUtil.isParameterOrConst(variability) || inImpl || FGraphUtil.inForLoopScope(inEnv)
                      @match false = crefEqualValue(inCref, inBinding)
                      (cache, v) = cevalCrefBinding(inCache, inEnv, inCref, inBinding, inImpl, inMsg, numIter)
                      cache = FCore.addEvaluatedCref(cache, variability, CrefForHashTable.crefStripLastSubs(inCref))
                    (cache, v)
                  end
                end
              end
               #=  build a default binding for it!
               =#
               #=  i would really like to have SourceInfo to put in Values.EMPTY here!
               =#
               #=  to easier report errors later on and also to have DAE.ComponentRef and DAE.Type
               =#
               #=  but unfortunately DAE depends on Values and they should probably be myMerged !
               =#
               #=  Actually, at a second thought we SHOULD NOT HAVE VALUES AT ALL, WE SHOULD HAVE
               =#
               #=  JUST ONE DAE.Exp.CONSTANT_EXPRESSION(exp, constantness, type)!
               =#
               #=  A variable with a binding -> constant evaluate the binding
               =#
               #=  We might try to ceval variables in reduction scope... but it can't be helped since we do things in a ***** way in Inst/Static
               =#
               #=  print(\"Eval cref: \" + CrefForHashTable.printComponentRefStr(inCref) + \"\\n  in scope \" + FGraphUtil.printGraphPathStr(inEnv) + \"\\n\");
               =#
          (outCache, outValue)
        end

         #= Helper function to cevalCref.
          Evaluates variables by evaluating their bindings. =#
        function cevalCrefBinding(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inBinding::DAE.Binding, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local cr::DAE.ComponentRef
                  local e1::DAE.ComponentRef
                  local subsc::List{DAE.Subscript}
                  local res::Values.Value
                  local v::Values.Value
                  local e_val::Values.Value
                  local env::FCore.Graph
                  local impl::Bool
                  local msg::Absyn.Msg
                  local rfn::String
                  local iter::String
                  local expstr::String
                  local s1::String
                  local s2::String
                  local str::String
                  local elexp::DAE.Exp
                  local iterexp::DAE.Exp
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                  local vl::List{DAE.Var}
                  local tpath::Absyn.Path
                  local ty::DAE.Type
                  local id::Absyn.Ident
                  local info::SourceInfo
                  local binding::DAE.Binding
                   #= /*
                      case (cache,env,cr,_,impl,msg)
                        equation
                          print(\"Ceval: \" +
                            CrefForHashTable.printComponentRefStr(cr) + \" | \" +
                            FGraphUtil.printGraphPathStr(env) + \" | \" +
                            DAEUtil.printBindingExpStr(inBinding) +
                            \"\\n\");
                        then
                          fail();*/ =#
                @matchcontinue (inCache, inEnv, inComponentRef, inBinding, inBoolean, inMsg, numIter) begin
                  (cache, env, cr, DAE.VALBOUND(valBound = v), impl, msg, _)  => begin
                      subsc = CrefForHashTable.crefLastSubs(cr)
                      (cache, res) = cevalSubscriptValue(cache, env, subsc, v, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (cache, env, DAE.CREF_IDENT(_, ty,  nil()), DAE.UNBOUND(__), _, Absyn.MSG(info), _)  => begin
                      @match DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = tpath), varLst = vl) = Types.arrayElementType(ty)
                      @match true = Types.allHaveBindings(vl)
                      binding = InstBinding.makeRecordBinding(cache, env, tpath, ty, vl, nil, info)
                      (cache, res) = cevalCrefBinding(cache, env, inComponentRef, binding, inBoolean, inMsg, numIter + 1)
                    (cache, res)
                  end

                  (_, _, _, DAE.UNBOUND(__), false, Absyn.MSG(_), _)  => begin
                    fail()
                  end

                  (_, _, _, DAE.UNBOUND(__), true, Absyn.MSG(_), _)  => begin
                      @match true = Flags.isSet(Flags.CEVAL)
                      Debug.trace("#- Ceval.cevalCrefBinding: Ignoring unbound when implicit\\n")
                    fail()
                  end

                  (cache, env, cr, DAE.EQBOUND(exp = exp, constant_ = DAE.C_CONST(__)), impl, msg, _)  => begin
                      @match DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = Absyn.IDENT()), iterators = list(DAE.REDUCTIONITER())) = exp
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      subsc = CrefForHashTable.crefLastSubs(cr)
                      (cache, res) = cevalSubscriptValue(cache, env, subsc, v, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (cache, env, cr, DAE.EQBOUND(evaluatedExp = SOME(e_val)), impl, msg, _)  => begin
                      subsc = CrefForHashTable.crefLastSubs(cr)
                      (cache, res) = cevalSubscriptValue(cache, env, subsc, e_val, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (cache, env, cr, DAE.EQBOUND(exp = exp, constant_ = DAE.C_CONST(__)), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      subsc = CrefForHashTable.crefLastSubs(cr)
                      (cache, res) = cevalSubscriptValue(cache, env, subsc, v, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (cache, env, cr, DAE.EQBOUND(exp = exp, constant_ = DAE.C_PARAM(__)), impl, msg, _)  => begin
                      @match false = isRecursiveBinding(cr, exp)
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      subsc = CrefForHashTable.crefLastSubs(cr)
                      (cache, res) = cevalSubscriptValue(cache, env, subsc, v, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (_, _, _, DAE.EQBOUND(exp = exp, constant_ = DAE.C_VAR(__)), _, Absyn.MSG(_), _)  => begin
                      @match true = Flags.isSet(Flags.CEVAL)
                      Debug.trace("#- Ceval.cevalCrefBinding failed (nonconstant EQBOUND(")
                      expstr = CrefForHashTable.printExpStr(exp)
                      Debug.trace(expstr)
                      Debug.traceln("))")
                    fail()
                  end

                  (_, env, e1, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.CEVAL)
                      s1 = CrefForHashTable.printComponentRefStr(e1)
                      s2 = Types.printBindingStr(inBinding)
                      str = FGraphUtil.printGraphPathStr(env)
                      str = stringAppendList(list("- Ceval.cevalCrefBinding: ", s1, " = [", s2, "] in env:", str, " failed"))
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
               #=  take the bindings form the cref type if is a record that has bindings for everything!
               =#
               #=  REDUCTION bindings
               =#
               #=  arbitrary expressions, value exists.
               =#
               #=  arbitrary expressions. When binding has optional value.
               =#
               #=  arbitrary expressions. When binding has optional value.
               =#
               #=  TODO: Ugly hack to prevent infinite recursion. If we have a binding r = r that
               =#
               #=  can for instance come from a modifier, this can cause an infinite loop here if r has no value.
               =#
               #=  if the binding has constant-ness DAE.C_VAR we cannot constant evaluate.
               =#
               #= print(\"ENV: \" + FGraphUtil.printGraphStr(inEnv) + \"\\n\");
               =#
          (outCache, outValue)
        end

         #=  help function to cevalCrefBinding =#
        function isRecursiveBinding(cr::DAE.ComponentRef, exp::DAE.Exp) ::Bool
              local res::Bool

              res = begin
                @matchcontinue (cr, exp) begin
                  (_, _)  => begin
                      res = ListUtil.map1BoolOr(Expression.extractCrefsFromExp(exp), CrefForHashTable.crefEqual, cr)
                    res
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Helper function to cevalCrefBinding. It applies
          subscripts to array values to extract array elements. =#
        function cevalSubscriptValue(inCache::FCore.Cache, inEnv::FCore.Graph, inExpSubscriptLst::List{<:DAE.Subscript} #= subscripts to extract =#, inValue::Values.Value, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local n::ModelicaInteger
                  local subval::Values.Value
                  local res::Values.Value
                  local v::Values.Value
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local subs::List{DAE.Subscript}
                  local lst::List{Values.Value}
                  local sliceLst::List{Values.Value}
                  local subvals::List{Values.Value}
                  local slice::List{ModelicaInteger}
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                   #=  we have a subscript which is an index or an enumeration literal scalar, try to constant evaluate it
                   =#
                @match (inCache, inEnv, inExpSubscriptLst, inValue, inBoolean, inMsg, numIter) begin
                  (cache, env, DAE.INDEX(exp = exp) <| subs, Values.ARRAY(valueLst = lst), impl, msg, _)  => begin
                      (cache, v) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      n = begin
                        @match v begin
                          Values.INTEGER(n)  => begin
                            n
                          end

                          Values.ENUM_LITERAL(index = n)  => begin
                            n
                          end
                        end
                      end
                      subval = listGet(lst, n)
                      (cache, res) = cevalSubscriptValue(cache, env, subs, subval, impl, msg, numIter + 1)
                    (cache, res)
                  end

                  (cache, env, DAE.SLICE(exp = exp) <| subs, Values.ARRAY(valueLst = lst), impl, msg, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = sliceLst)) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      slice = ListUtil.map(sliceLst, ValuesUtil.valueInteger)
                      subvals = ListUtil.map1r(slice, listGet, lst)
                      (cache, lst) = cevalSubscriptValueList(cache, env, subs, subvals, impl, msg, numIter)
                      res = ValuesUtil.makeArray(lst)
                    (cache, res)
                  end

                  (cache, env, DAE.WHOLEDIM(__) <| subs, subval && Values.ARRAY(__), impl, msg, _)  => begin
                       #=  slices
                       =#
                       #=  we have a wholedim, apply the rest of the subscripts to each element of the array.
                       =#
                      if listEmpty(subs)
                        res = subval
                      else
                        (cache, lst) = cevalSubscriptValueList(cache, env, subs, subval.valueLst, impl, msg, numIter + 1)
                        res = ValuesUtil.makeArray(lst)
                      end
                       #=  If the wholedim is the last subscript we can just return the value as it is.
                       =#
                    (cache, res)
                  end

                  (cache, _,  nil(), v, _, _, _)  => begin
                    (cache, v)
                  end
                end
              end
               #=  we have no subscripts but we have a value, return it
               =#
               #= /* failtrace
                  case (cache, env, subs, inValue, dims, _, _, _)
                    equation
                      true = Flags.isSet(Flags.FAILTRACE);
                      Debug.traceln(\"- Ceval.cevalSubscriptValue failed on:\" +
                        \"\\n env: \" + FGraphUtil.printGraphPathStr(env) +
                        \"\\n subs: \" + stringDelimitList(List.map(subs, CrefForHashTable.printSubscriptStr), \", \") +
                        \"\\n value: \" + ValuesUtil.printValStr(inValue) +
                        \"\\n dim sizes: \" + stringDelimitList(List.map(dims, intString), \", \")
                      );
                    then
                      fail();*/ =#
          (outCache, outValue)
        end

         #= Applies subscripts to array values to extract array elements. =#
        function cevalSubscriptValueList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpSubscriptLst::List{<:DAE.Subscript} #= subscripts to extract =#, inValue::List{<:Values.Value}, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{Values.Value}}
              local outValue::List{Values.Value}
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local subval::Values.Value
                  local res::Values.Value
                  local env::FCore.Graph
                  local lst::List{Values.Value}
                  local subvals::List{Values.Value}
                  local impl::Bool
                  local msg::Absyn.Msg
                  local subs::List{DAE.Subscript}
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpSubscriptLst, inValue, inBoolean, inMsg, numIter) begin
                  (cache, _, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, subs, subval <| subvals, impl, msg, _)  => begin
                      (cache, res) = cevalSubscriptValue(cache, env, subs, subval, impl, msg, numIter + 1)
                      (cache, lst) = cevalSubscriptValueList(cache, env, subs, subvals, impl, msg, numIter)
                    (cache, _cons(res, lst))
                  end
                end
              end
          (outCache, outValue)
        end

         #= This function relates a list of subscripts to their canonical
          forms, which is when all expressions are evaluated to constant
          values. For instance
          the subscript list {1,p,q} (as in x[1,p,q]) where p and q have constant values 2,3 respectively will become
          {1,2,3} (resulting in x[1,2,3]).
          adrpo: do not fail if you cannot evaluate one, just move to the next one! =#
        function cevalSubscripts(inCache::FCore.Cache, inEnv::FCore.Graph, inExpSubscriptLst::List{<:DAE.Subscript}, inIntegerLst::List{<:ModelicaInteger}, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{DAE.Subscript}}
              local outExpSubscriptLst::List{DAE.Subscript}
              local outCache::FCore.Cache

              (outCache, outExpSubscriptLst) = begin
                  local sub_1::DAE.Subscript
                  local sub::DAE.Subscript
                  local subs_1::List{DAE.Subscript}
                  local subs::List{DAE.Subscript}
                  local env::FCore.Graph
                  local dim::ModelicaInteger
                  local dims::List{ModelicaInteger}
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                   #=  empty case
                   =#
                @matchcontinue (inCache, inEnv, inExpSubscriptLst, inIntegerLst, inBoolean, inMsg, numIter) begin
                  (cache, _,  nil(), _, _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, sub <| subs, dim <| dims, impl, msg, _)  => begin
                      (cache, sub_1) = cevalSubscript(cache, env, sub, dim, impl, msg, numIter + 1)
                      (cache, subs_1) = cevalSubscripts(cache, env, subs, dims, impl, msg, numIter)
                    (cache, _cons(sub_1, subs_1))
                  end

                  (cache, env, sub <| subs, dim <| dims, impl, msg, _)  => begin
                      @shouldFail (_, _) = cevalSubscript(cache, env, sub, dim, impl, msg, numIter + 1)
                      (cache, subs_1) = cevalSubscripts(cache, env, subs, dims, impl, msg, numIter)
                    (cache, _cons(sub, subs_1))
                  end
                end
              end
               #=  we have subscripts and we can evaluate the first
               =#
               #=  we have subscripts and we CANNOT evaluate the first, move to next
               =#
          (outCache, outExpSubscriptLst)
        end

         #= This function relates a subscript to its canonical forms, which
          is when all expressions are evaluated to constant values. =#
        function cevalSubscript(inCache::FCore.Cache, inEnv::FCore.Graph, inSubscript::DAE.Subscript, inInteger::ModelicaInteger, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, DAE.Subscript}
              local outSubscript::DAE.Subscript
              local outCache::FCore.Cache

              (outCache, outSubscript) = begin
                  local env::FCore.Graph
                  local v1::Values.Value
                  local e1_1::DAE.Exp
                  local e1::DAE.Exp
                  local dim::ModelicaInteger
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local indx::ModelicaInteger
                   #=  the entire dimension, nothing to do
                   =#
                @matchcontinue (inCache, inEnv, inSubscript, inInteger, inBoolean, inMsg, numIter) begin
                  (cache, _, DAE.WHOLEDIM(__), _, _, _, _)  => begin
                    (cache, DAE.WHOLEDIM())
                  end

                  (cache, _, DAE.INDEX(exp = DAE.ENUM_LITERAL(__)), _, _, _, _)  => begin
                    (cache, inSubscript)
                  end

                  (cache, env, DAE.INDEX(exp = e1), _, impl, msg, _)  => begin
                      (cache, v1) = ceval(cache, env, e1, impl, msg, numIter + 1)
                      e1_1 = begin
                        @match v1 begin
                          Values.INTEGER(_)  => begin
                            ValuesUtil.valueExp(v1)
                          end

                          Values.ENUM_LITERAL(__)  => begin
                            ValuesUtil.valueExp(v1)
                          end

                          Values.BOOL(_)  => begin
                            ValuesUtil.valueExp(v1)
                          end
                        end
                      end
                    (cache, DAE.INDEX(e1_1))
                  end

                  (cache, env, DAE.SLICE(exp = e1), _, impl, msg, _)  => begin
                      (cache, v1) = ceval(cache, env, e1, impl, msg, numIter + 1)
                      e1_1 = ValuesUtil.valueExp(v1)
                    (cache, DAE.SLICE(e1_1))
                  end
                end
              end
               #=  An enumeration literal is already constant
               =#
               #=  an expression index that can be constant evaluated, indexing using enum or bool
               =#
               #=  an expression slice that can be constant evaluated
               =#
          (outCache, outSubscript)
        end

         #=  =#
        function crefEqualValue(c::DAE.ComponentRef, v::DAE.Binding) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local cr::DAE.ComponentRef
                @match (c, v) begin
                  (_, DAE.EQBOUND(DAE.CREF(cr, _), NONE(), _, _))  => begin
                    CrefForHashTable.crefEqual(c, cr)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #=
        Checks that the values of a dimension slice is all in the range 1 to dim size
        if so returns true, else returns false =#
        function dimensionSliceInRange(arr::Values.Value, dimSize::ModelicaInteger) ::Bool
              local inRange::Bool

              inRange = begin
                  local indx::ModelicaInteger
                  local dim::ModelicaInteger
                  local vlst::List{Values.Value}
                  local dims::List{ModelicaInteger}
                @matchcontinue (arr, dimSize) begin
                  (Values.ARRAY(valueLst =  nil()), _)  => begin
                    true
                  end

                  (Values.ARRAY(valueLst = Values.INTEGER(indx) <| vlst, dimLst = dim <| dims), _)  => begin
                      dim = dim - 1
                      dims = _cons(dim, dims)
                      @match true = indx <= dimSize
                      @match true = dimensionSliceInRange(Values.ARRAY(vlst, dims), dimSize)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          inRange
        end

         #= Help function to ceval. Evaluates reductions calls, such as
            'sum(i for i in 1:5)' =#
        function cevalReduction(inCache::FCore.Cache, inEnv::FCore.Graph, opPath::Absyn.Path, inCurValue::Option{<:Values.Value}, exp::DAE.Exp, exprType::DAE.Type, foldName::String, resultName::String, foldExp::Option{<:DAE.Exp}, iteratorNames::List{<:String}, inValueMatrix::List{<:List{<:Values.Value}}, iterTypes::List{<:DAE.Type}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Option{Values.Value}}
              local result::Option{Values.Value}
              local newCache::FCore.Cache

              (newCache, result) = begin
                  local vals::List{Values.Value}
                  local new_env::FCore.Graph
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local dims::List{ModelicaInteger}
                  local valueMatrix::List{List{Values.Value}}
                  local curValue::Option{Values.Value}
                @match (inCache, inEnv, opPath, inCurValue, exp, exprType, foldName, resultName, foldExp, iteratorNames, inValueMatrix, iterTypes, impl, msg, numIter) begin
                  (cache, _, Absyn.IDENT("list"), SOME(Values.LIST(vals)), _, _, _, _, _, _,  nil(), _, _, _, _)  => begin
                      vals = listReverse(vals)
                    (cache, SOME(Values.LIST(vals)))
                  end

                  (cache, _, Absyn.IDENT("listReverse"), SOME(Values.LIST(_)), _, _, _, _, _, _,  nil(), _, _, _, _)  => begin
                    (cache, inCurValue)
                  end

                  (cache, _, Absyn.IDENT("array"), SOME(Values.ARRAY(vals, dims)), _, _, _, _, _, _,  nil(), _, _, _, _)  => begin
                      vals = listReverse(vals)
                    (cache, SOME(Values.ARRAY(vals, dims)))
                  end

                  (cache, _, _, curValue, _, _, _, _, _, _,  nil(), _, _, _, _)  => begin
                    (cache, curValue)
                  end

                  (cache, env, _, curValue, _, _, _, _, _, _, vals <| valueMatrix, _, _, _, _)  => begin
                      new_env = extendFrameForIterators(env, iteratorNames, vals, iterTypes)
                      (cache, curValue) = cevalReductionEvalAndFold(cache, new_env, opPath, curValue, exp, exprType, foldName, resultName, foldExp, impl, msg, numIter + 1)
                      (cache, curValue) = cevalReduction(cache, env, opPath, curValue, exp, exprType, foldName, resultName, foldExp, iteratorNames, valueMatrix, iterTypes, impl, msg, numIter)
                    (cache, curValue)
                  end
                end
              end
               #=  Bind the iterator
               =#
               #=  print(\"iterators: \" + stringDelimitList(list(ValuesUtil.valString(v) for v in vals), \",\") + \"\\n\");
               =#
               #=  Calculate var1 of the folding function
               =#
               #=  Fold the rest of the reduction
               =#
          (newCache, result)
        end

         #= Evaluate the reduction body and fold =#
        function cevalReductionEvalAndFold(inCache::FCore.Cache, inEnv::FCore.Graph, opPath::Absyn.Path, inCurValue::Option{<:Values.Value}, exp::DAE.Exp, exprType::DAE.Type, foldName::String, resultName::String, foldExp::Option{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Option{Values.Value}}
              local result::Option{Values.Value}
              local newCache::FCore.Cache

              (newCache, result) = begin
                  local value::Values.Value
                  local curValue::Option{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inCache, inEnv, opPath, inCurValue, exp, exprType, foldName, resultName, foldExp, impl, msg, numIter) begin
                  (cache, env, _, curValue, _, _, _, _, _, _, _, _)  => begin
                      (cache, value) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      (cache, result) = cevalReductionFold(cache, env, opPath, curValue, value, foldName, resultName, foldExp, exprType, impl, msg, numIter)
                    (cache, result)
                  end
                end
              end
               #=  print(\"cevalReductionEval: \" + CrefForHashTable.printExpStr(exp) + \" => \" + ValuesUtil.valString(value) + \"\\n\");
               =#
               #=  print(\"cevalReductionEval => \" + Util.applyOptionOrDefault(result, ValuesUtil.valString, \"\") + \"\\n\");
               =#
          (newCache, result)
        end

         #= Fold the reduction body =#
        function cevalReductionFold(inCache::FCore.Cache, inEnv::FCore.Graph, opPath::Absyn.Path, inCurValue::Option{<:Values.Value}, inValue::Values.Value, foldName::String, resultName::String, foldExp::Option{<:DAE.Exp}, exprType::DAE.Type, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Option{Values.Value}}
              local result::Option{Values.Value}
              local newCache::FCore.Cache

              (newCache, result) = begin
                  local exp::DAE.Exp
                  local value::Values.Value
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inCache, opPath, inCurValue, foldExp) begin
                  (cache, Absyn.IDENT("array"), SOME(value), _)  => begin
                      value = valueArrayCons(ValuesUtil.unboxIfBoxedVal(inValue), value)
                    (cache, SOME(value))
                  end

                  (cache, Absyn.IDENT("list"), SOME(value), _)  => begin
                      value = valueCons(ValuesUtil.unboxIfBoxedVal(inValue), value)
                    (cache, SOME(value))
                  end

                  (cache, Absyn.IDENT("listReverse"), SOME(value), _)  => begin
                      value = valueCons(ValuesUtil.unboxIfBoxedVal(inValue), value)
                    (cache, SOME(value))
                  end

                  (cache, _, NONE(), _)  => begin
                    (cache, SOME(inValue))
                  end

                  (cache, _, SOME(value), SOME(exp))  => begin
                      env = FGraphUtil.addForIterator(inEnv, foldName, exprType, DAE.VALBOUND(inValue, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.VAR(), SOME(DAE.C_CONST()))
                      env = FGraphUtil.addForIterator(env, resultName, exprType, DAE.VALBOUND(value, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.VAR(), SOME(DAE.C_CONST()))
                      (cache, value) = ceval(cache, env, exp, impl, msg, numIter + 1)
                    (cache, SOME(value))
                  end
                end
              end
               #=  print(\"cevalReductionFold \" + ExpressionDump.printExpStr(exp) + \", \" + ValuesUtil.valString(inValue) + \", \" + ValuesUtil.valString(value) + \"\\n\");
               =#
               #= /* TODO: Store the actual types somewhere... */ =#
          (newCache, result)
        end

         #= Returns the cons of two values. Used by cevalReduction for array reductions. =#
        function valueArrayCons(v1::Values.Value, v2::Values.Value) ::Values.Value
              local res::Values.Value

              res = begin
                  local vals::List{Values.Value}
                  local dim_size::ModelicaInteger
                  local rest_dims::List{ModelicaInteger}
                @match (v1, v2) begin
                  (_, Values.ARRAY(valueLst = vals, dimLst = dim_size <| rest_dims))  => begin
                      dim_size = dim_size + 1
                    Values.ARRAY(_cons(v1, vals), _cons(dim_size, rest_dims))
                  end

                  _  => begin
                      Values.ARRAY(list(v1, v2), list(2))
                  end
                end
              end
          res
        end

         #= Returns the cons of two values. Used by cevalReduction for list reductions. =#
        function valueCons(inV1::Values.Value, inV2::Values.Value) ::Values.Value
              local res::Values.Value

              res = begin
                  local vals::List{Values.Value}
                  local v1::Values.Value
                @match (inV1, inV2) begin
                  (Values.META_BOX(v1), Values.LIST(vals))  => begin
                    Values.LIST(_cons(v1, vals))
                  end

                  (v1, Values.LIST(vals))  => begin
                    Values.LIST(_cons(v1, vals))
                  end
                end
              end
          res
        end

        function cevalReductionIterators(inCache::FCore.Cache, inEnv::FCore.Graph, inIterators::List{<:DAE.ReductionIterator}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{List{Values.Value}}, List{String}, List{ModelicaInteger}, List{DAE.Type}}
              local tys::List{DAE.Type}
              local dims::List{ModelicaInteger}
              local names::List{String}
              local vals::List{List{Values.Value}}
              local outCache::FCore.Cache

              (outCache, vals, names, dims, tys) = begin
                  local val::Values.Value
                  local iterVals::List{Values.Value}
                  local dim::ModelicaInteger
                  local ty::DAE.Type
                  local id::String
                  local exp::DAE.Exp
                  local guardExp::Option{DAE.Exp}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local iterators::List{DAE.ReductionIterator}
                @match (inCache, inEnv, inIterators, impl, msg, numIter) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil, nil, nil, nil)
                  end

                  (cache, env, DAE.REDUCTIONITER(id, exp, guardExp, ty) <| iterators, _, _, _)  => begin
                      (cache, val) = ceval(cache, env, exp, impl, msg, numIter + 1)
                      iterVals = ValuesUtil.arrayOrListVals(val, true)
                      (cache, iterVals) = filterReductionIterator(cache, env, id, ty, iterVals, guardExp, impl, msg, numIter)
                      dim = listLength(iterVals)
                      (cache, vals, names, dims, tys) = cevalReductionIterators(cache, env, iterators, impl, msg, numIter)
                    (cache, _cons(iterVals, vals), _cons(id, names), _cons(dim, dims), _cons(ty, tys))
                  end
                end
              end
          (outCache, vals, names, dims, tys)
        end

        function filterReductionIterator(inCache::FCore.Cache, inEnv::FCore.Graph, id::String, ty::DAE.Type, inVals::List{<:Values.Value}, guardExp::Option{<:DAE.Exp}, impl::Bool, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, List{Values.Value}}
              local outVals::List{Values.Value}
              local outCache::FCore.Cache

              (outCache, outVals) = begin
                  local exp::DAE.Exp
                  local val::Values.Value
                  local b::Bool
                  local new_env::FCore.Graph
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local vals::List{Values.Value}
                @match (inCache, inEnv, id, ty, inVals, guardExp, impl, msg, numIter) begin
                  (cache, _, _, _,  nil(), _, _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, _, _, val <| vals, SOME(exp), _, _, _)  => begin
                      new_env = FGraphUtil.addForIterator(env, id, ty, DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.VAR(), SOME(DAE.C_CONST()))
                      @match (cache, Values.BOOL(b)) = ceval(cache, new_env, exp, impl, msg, numIter + 1)
                      (cache, vals) = filterReductionIterator(cache, env, id, ty, vals, guardExp, impl, msg, numIter)
                      vals = if b
                            _cons(val, vals)
                          else
                            vals
                          end
                    (cache, vals)
                  end

                  (cache, _, _, _, vals, NONE(), _, _, _)  => begin
                    (cache, vals)
                  end
                end
              end
          (outCache, outVals)
        end

        function extendFrameForIterators(inEnv::FCore.Graph, inNames::List{<:String}, inVals::List{<:Values.Value}, inTys::List{<:DAE.Type}) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                  local name::String
                  local val::Values.Value
                  local ty::DAE.Type
                  local env::FCore.Graph
                  local names::List{String}
                  local vals::List{Values.Value}
                  local tys::List{DAE.Type}
                @match (inEnv, inNames, inVals, inTys) begin
                  (env,  nil(),  nil(),  nil())  => begin
                    env
                  end

                  (env, name <| names, val <| vals, ty <| tys)  => begin
                      env = FGraphUtil.addForIterator(env, name, ty, DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.VAR(), SOME(DAE.C_CONST()))
                      env = extendFrameForIterators(env, names, vals, tys)
                    env
                  end
                end
              end
          outEnv
        end

        function backpatchArrayReduction(path::Absyn.Path, iterType::Absyn.ReductionIterType, inValue::Values.Value, dims::List{<:ModelicaInteger}) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local vals::List{Values.Value}
                  local value::Values.Value
                @match (path, iterType, inValue, dims) begin
                  (_, _, value, _ <|  nil())  => begin
                    value
                  end

                  (Absyn.IDENT("array"), Absyn.COMBINE(__), Values.ARRAY(valueLst = vals), _)  => begin
                      value = backpatchArrayReduction3(vals, listReverse(dims), ValuesUtil.makeArray)
                    value
                  end

                  (Absyn.IDENT("list"), Absyn.COMBINE(__), Values.LIST(vals), _)  => begin
                      value = backpatchArrayReduction3(vals, listReverse(dims), ValuesUtil.makeList)
                    value
                  end

                  (Absyn.IDENT("listReverse"), Absyn.COMBINE(__), Values.LIST(vals), _)  => begin
                      value = backpatchArrayReduction3(vals, listReverse(dims), ValuesUtil.makeList)
                    value
                  end

                  _  => begin
                      inValue
                  end
                end
              end
               #=  print(ValuesUtil.valString(value));print(\"\\n\");
               =#
               #=  print(ValuesUtil.valString(value));print(\"\\n\");
               =#
               #=  print(ValuesUtil.valString(value));print(\"\\n\");
               =#
          outValue
        end

        function backpatchArrayReduction3(inVals::List{<:Values.Value}, inDims::List{<:ModelicaInteger}, makeSequence::Func) ::Values.Value
              local outValue::Values.Value

              outValue = begin
                  local dim::ModelicaInteger
                  local valMatrix::List{List{Values.Value}}
                  local value::Values.Value
                  local vals::List{Values.Value}
                  local dims::List{ModelicaInteger}
                @match (inVals, inDims, makeSequence) begin
                  (vals, _ <|  nil(), _)  => begin
                      value = makeSequence(vals)
                    value
                  end

                  (vals, dim <| dims, _)  => begin
                      valMatrix = ListUtil.partition(vals, dim)
                      vals = ListUtil.map(valMatrix, makeSequence)
                      value = backpatchArrayReduction3(vals, dims, makeSequence)
                    value
                  end
                end
              end
               #=  Split into the smallest of the arrays
               =#
               #=  print(\"into sublists of length: \" + intString(dim) + \" from length=\" + intString(listLength(vals)) + \"\\n\");
               =#
               #=  print(\"output has length=\" + intString(listLength(valMatrix)) + \"\\n\");
               =#
          outValue
        end

         #= A simple expression does not need cache, etc =#
        function cevalSimple(exp::DAE.Exp) ::Values.Value
              local val::Values.Value

              (_, val) = ceval(FCoreUtil.emptyCache(), FCore.emptyGraph, exp, false, Absyn.MSG(AbsynUtil.dummyInfo), 0)
          val
        end

         #= A simple expression does not need cache, etc =#
        function cevalSimpleWithFunctionTreeReturnExp(exp::DAE.Exp, functions::DAE.FunctionTree) ::DAE.Exp
              local oexp::DAE.Exp

              local val::Values.Value
              local cache::FCore.Cache
              local structuralParameters::FCore.StructuralParameters
              local functionTree::MutableType #= {DAE.FunctionTree} =#

              structuralParameters = (AvlSetCR.EMPTY(), nil)
              functionTree = Mutable.create(functions)
              cache = FCore.CACHE(NONE(), functionTree, structuralParameters, Absyn.IDENT(""))
              (_, val) = ceval(cache, FCore.emptyGraph, exp, false, Absyn.NO_MSG(), 0)
              oexp = ValuesUtil.valueExp(val)
          oexp
        end

         #= Part of meta-programming using CODE.
          This function evaluates a piece of Expression AST, replacing Eval(variable)
          with the value of the variable, given that it is of type \\\"Expression\\\".

          Example: y = Code(1 + x)
                   2 + 5  ( x + Eval(y) )  =>   2 + 5  ( x + 1 + x ) =#
        function cevalAstExp(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::Absyn.Exp, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, Absyn.Exp}
              local outExp::Absyn.Exp
              local outCache::FCore.Cache

              (outCache, outExp) = begin
                  local e::Absyn.Exp
                  local e1_1::Absyn.Exp
                  local e2_1::Absyn.Exp
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                  local e_1::Absyn.Exp
                  local cond_1::Absyn.Exp
                  local then_1::Absyn.Exp
                  local else_1::Absyn.Exp
                  local cond::Absyn.Exp
                  local then_::Absyn.Exp
                  local else_::Absyn.Exp
                  local exp::Absyn.Exp
                  local e3_1::Absyn.Exp
                  local e3::Absyn.Exp
                  local env::FCore.Graph
                  local op::Absyn.Operator
                  local impl::Bool
                  local msg::Absyn.Msg
                  local nest_1::List{Tuple{Absyn.Exp, Absyn.Exp}}
                  local nest::List{Tuple{Absyn.Exp, Absyn.Exp}}
                  local cr::Absyn.ComponentRef
                  local fa::Absyn.FunctionArgs
                  local expl_1::List{Absyn.Exp}
                  local expl::List{Absyn.Exp}
                  local cache::FCore.Cache
                  local daeExp::DAE.Exp
                  local lstExpl_1::List{List{Absyn.Exp}}
                  local lstExpl::List{List{Absyn.Exp}}
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inMsg, info) begin
                  (cache, _, e && Absyn.INTEGER(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, _, e && Absyn.REAL(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, _, e && Absyn.CREF(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, _, e && Absyn.STRING(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, _, e && Absyn.BOOL(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, env, Absyn.BINARY(exp1 = e1, op = op, exp2 = e2), impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e2_1) = cevalAstExp(cache, env, e2, impl, msg, info)
                    (cache, Absyn.BINARY(e1_1, op, e2_1))
                  end

                  (cache, env, Absyn.UNARY(op = op, exp = e), impl, msg, _)  => begin
                      (cache, e_1) = cevalAstExp(cache, env, e, impl, msg, info)
                    (cache, Absyn.UNARY(op, e_1))
                  end

                  (cache, env, Absyn.LBINARY(exp1 = e1, op = op, exp2 = e2), impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e2_1) = cevalAstExp(cache, env, e2, impl, msg, info)
                    (cache, Absyn.LBINARY(e1_1, op, e2_1))
                  end

                  (cache, env, Absyn.LUNARY(op = op, exp = e), impl, msg, _)  => begin
                      (cache, e_1) = cevalAstExp(cache, env, e, impl, msg, info)
                    (cache, Absyn.LUNARY(op, e_1))
                  end

                  (cache, env, Absyn.RELATION(exp1 = e1, op = op, exp2 = e2), impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e2_1) = cevalAstExp(cache, env, e2, impl, msg, info)
                    (cache, Absyn.RELATION(e1_1, op, e2_1))
                  end

                  (cache, env, Absyn.IFEXP(ifExp = cond, trueBranch = then_, elseBranch = else_, elseIfBranch = nest), impl, msg, _)  => begin
                      (cache, cond_1) = cevalAstExp(cache, env, cond, impl, msg, info)
                      (cache, then_1) = cevalAstExp(cache, env, then_, impl, msg, info)
                      (cache, else_1) = cevalAstExp(cache, env, else_, impl, msg, info)
                      (cache, nest_1) = cevalAstExpexpList(cache, env, nest, impl, msg, info)
                    (cache, Absyn.IFEXP(cond_1, then_1, else_1, nest_1))
                  end

                  (cache, env, Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "Eval", subscripts =  nil()), functionArgs = Absyn.FUNCTIONARGS(args = e <|  nil(), argNames =  nil())), impl, msg, _)  => begin
                      (cache, daeExp, _) = Static.elabExp(cache, env, e, impl, true, Prefix.NOPRE(), info)
                      @match (cache, Values.CODE(Absyn.C_EXPRESSION(exp))) = ceval(cache, env, daeExp, impl, msg, 0)
                    (cache, exp)
                  end

                  (cache, _, e && Absyn.CALL(__), _, _, _)  => begin
                    (cache, e)
                  end

                  (cache, env, Absyn.ARRAY(arrayExp = expl), impl, msg, _)  => begin
                      (cache, expl_1) = cevalAstExpList(cache, env, expl, impl, msg, info)
                    (cache, Absyn.ARRAY(expl_1))
                  end

                  (cache, env, Absyn.MATRIX(matrix = lstExpl), impl, msg, _)  => begin
                      (cache, lstExpl_1) = cevalAstExpListList(cache, env, lstExpl, impl, msg, info)
                    (cache, Absyn.MATRIX(lstExpl_1))
                  end

                  (cache, env, Absyn.RANGE(start = e1, step = SOME(e2), stop = e3), impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e2_1) = cevalAstExp(cache, env, e2, impl, msg, info)
                      (cache, e3_1) = cevalAstExp(cache, env, e3, impl, msg, info)
                    (cache, Absyn.RANGE(e1_1, SOME(e2_1), e3_1))
                  end

                  (cache, env, Absyn.RANGE(start = e1, step = NONE(), stop = e3), impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e3_1) = cevalAstExp(cache, env, e3, impl, msg, info)
                    (cache, Absyn.RANGE(e1_1, NONE(), e3_1))
                  end

                  (cache, env, Absyn.TUPLE(expressions = expl), impl, msg, _)  => begin
                      (cache, expl_1) = cevalAstExpList(cache, env, expl, impl, msg, info)
                    (cache, Absyn.TUPLE(expl_1))
                  end

                  (cache, _, Absyn.END(__), _, _, _)  => begin
                    (cache, Absyn.END())
                  end

                  (cache, _, e && Absyn.CODE(__), _, _, _)  => begin
                    (cache, e)
                  end
                end
              end
          (outCache, outExp)
        end

         #= List version of cevalAstExp =#
        function cevalAstExpList(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLst::List{<:Absyn.Exp}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, List{Absyn.Exp}}
              local outAbsynExpLst::List{Absyn.Exp}
              local outCache::FCore.Cache

              (outCache, outAbsynExpLst) = begin
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local e_1::Absyn.Exp
                  local e::Absyn.Exp
                  local res::List{Absyn.Exp}
                  local es::List{Absyn.Exp}
                  local impl::Bool
                  local cache::FCore.Cache
                @match (inCache, inEnv, inAbsynExpLst, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, e <| es, impl, msg, _)  => begin
                      (cache, _) = cevalAstExp(cache, env, e, impl, msg, info)
                      (cache, res) = cevalAstExpList(cache, env, es, impl, msg, info)
                    (cache, _cons(e, res))
                  end
                end
              end
          (outCache, outAbsynExpLst)
        end

         #= function: cevalAstExpListList =#
        function cevalAstExpListList(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynExpLstLst::List{<:List{<:Absyn.Exp}}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, List{List{Absyn.Exp}}}
              local outAbsynExpLstLst::List{List{Absyn.Exp}}
              local outCache::FCore.Cache

              (outCache, outAbsynExpLstLst) = begin
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local e_1::List{Absyn.Exp}
                  local e::List{Absyn.Exp}
                  local res::List{List{Absyn.Exp}}
                  local es::List{List{Absyn.Exp}}
                  local impl::Bool
                  local cache::FCore.Cache
                @match (inCache, inEnv, inAbsynExpLstLst, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, e <| es, impl, msg, _)  => begin
                      (cache, _) = cevalAstExpList(cache, env, e, impl, msg, info)
                      (cache, res) = cevalAstExpListList(cache, env, es, impl, msg, info)
                    (cache, _cons(e, res))
                  end
                end
              end
          (outCache, outAbsynExpLstLst)
        end

         #= Evaluates an ast constructor for Element nodes, e.g.
          Code(parameter Real x=1;) =#
        function cevalAstElt(inCache::FCore.Cache, inEnv::FCore.Graph, inElement::Absyn.Element, inBoolean::Bool, inMsg::Absyn.Msg) ::Tuple{FCore.Cache, Absyn.Element}
              local outElement::Absyn.Element
              local outCache::FCore.Cache

              (outCache, outElement) = begin
                  local citems_1::List{Absyn.ComponentItem}
                  local citems::List{Absyn.ComponentItem}
                  local env::FCore.Graph
                  local f::Bool
                  local isReadOnly::Bool
                  local impl::Bool
                  local r::Option{Absyn.RedeclareKeywords}
                  local io::Absyn.InnerOuter
                  local file::String
                  local attr::Absyn.ElementAttributes
                  local tp::Absyn.TypeSpec
                  local info::SourceInfo
                  local sline::ModelicaInteger
                  local scolumn::ModelicaInteger
                  local eline::ModelicaInteger
                  local ecolumn::ModelicaInteger
                  local c::Option{Absyn.ConstrainClass}
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inElement, inBoolean, inMsg) begin
                  (cache, env, Absyn.ELEMENT(finalPrefix = f, redeclareKeywords = r, innerOuter = io, specification = Absyn.COMPONENTS(attributes = attr, typeSpec = tp, components = citems), info = info && SOURCEINFO(__), constrainClass = c), impl, msg)  => begin
                      (cache, citems_1) = cevalAstCitems(cache, env, citems, impl, msg, info)
                    (cache, Absyn.ELEMENT(f, r, io, Absyn.COMPONENTS(attr, tp, citems_1), info, c))
                  end
                end
              end
          (outCache, outElement)
        end

         #= Helper function to cevalAstElt. =#
        function cevalAstCitems(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynComponentItemLst::List{<:Absyn.ComponentItem}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, List{Absyn.ComponentItem}}
              local outAbsynComponentItemLst::List{Absyn.ComponentItem}
              local outCache::FCore.Cache

              (outCache, outAbsynComponentItemLst) = begin
                  local msg::Absyn.Msg
                  local res::List{Absyn.ComponentItem}
                  local xs::List{Absyn.ComponentItem}
                  local modopt_1::Option{Absyn.Modification}
                  local modopt::Option{Absyn.Modification}
                  local ad_1::List{Absyn.Subscript}
                  local ad::List{Absyn.Subscript}
                  local env::FCore.Graph
                  local id::String
                  local cond::Option{Absyn.Exp}
                  local cmt::Option{Absyn.Comment}
                  local impl::Bool
                  local x::Absyn.ComponentItem
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inAbsynComponentItemLst, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, Absyn.COMPONENTITEM(component = Absyn.COMPONENT(name = id, arrayDim = ad, modification = modopt), condition = cond, comment = cmt) <| xs, impl, msg, _)  => begin
                      (cache, res) = cevalAstCitems(cache, env, xs, impl, msg, info)
                      (cache, modopt_1) = cevalAstModopt(cache, env, modopt, impl, msg, info)
                      (cache, ad_1) = cevalAstArraydim(cache, env, ad, impl, msg, info)
                    (cache, _cons(Absyn.COMPONENTITEM(Absyn.COMPONENT(id, ad_1, modopt_1), cond, cmt), res))
                  end

                  (cache, env, x <| xs, impl, msg, _)  => begin
                      (cache, res) = cevalAstCitems(cache, env, xs, impl, msg, info)
                    (cache, _cons(x, res))
                  end
                end
              end
               #= /* If one component fails, the rest should still succeed */ =#
               #= /* If one component fails, the rest should still succeed */ =#
          (outCache, outAbsynComponentItemLst)
        end

         #= function: cevalAstModopt =#
        function cevalAstModopt(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynModificationOption::Option{<:Absyn.Modification}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, Option{Absyn.Modification}}
              local outAbsynModificationOption::Option{Absyn.Modification}
              local outCache::FCore.Cache

              (outCache, outAbsynModificationOption) = begin
                  local res::Absyn.Modification
                  local mod::Absyn.Modification
                  local env::FCore.Graph
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                @match (inCache, inEnv, inAbsynModificationOption, inBoolean, inMsg, info) begin
                  (cache, env, SOME(mod), impl, msg, _)  => begin
                      (cache, res) = cevalAstModification(cache, env, mod, impl, msg, info)
                    (cache, SOME(res))
                  end

                  (cache, _, NONE(), _, _, _)  => begin
                    (cache, NONE())
                  end
                end
              end
          (outCache, outAbsynModificationOption)
        end

         #= This function evaluates Eval(variable) inside an AST Modification  and replaces
          the Eval operator with the value of the variable if it has a type \\\"Expression\\\" =#
        function cevalAstModification(inCache::FCore.Cache, inEnv::FCore.Graph, inModification::Absyn.Modification, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, Absyn.Modification}
              local outModification::Absyn.Modification
              local outCache::FCore.Cache

              (outCache, outModification) = begin
                  local e_1::Absyn.Exp
                  local e::Absyn.Exp
                  local eltargs_1::List{Absyn.ElementArg}
                  local eltargs::List{Absyn.ElementArg}
                  local env::FCore.Graph
                  local impl::Bool
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local info2::SourceInfo
                @match (inCache, inEnv, inModification, inBoolean, inMsg, info) begin
                  (cache, env, Absyn.CLASSMOD(elementArgLst = eltargs, eqMod = Absyn.EQMOD(e, info2)), impl, msg, _)  => begin
                      (cache, e_1) = cevalAstExp(cache, env, e, impl, msg, info)
                      (cache, eltargs_1) = cevalAstEltargs(cache, env, eltargs, impl, msg, info)
                    (cache, Absyn.CLASSMOD(eltargs_1, Absyn.EQMOD(e_1, info2)))
                  end

                  (cache, env, Absyn.CLASSMOD(elementArgLst = eltargs, eqMod = Absyn.NOMOD(__)), impl, msg, _)  => begin
                      (cache, eltargs_1) = cevalAstEltargs(cache, env, eltargs, impl, msg, info)
                    (cache, Absyn.CLASSMOD(eltargs_1, Absyn.NOMOD()))
                  end
                end
              end
          (outCache, outModification)
        end

         #= Helper function to cevalAstModification. =#
        function cevalAstEltargs(inCache::FCore.Cache, inEnv::FCore.Graph, inAbsynElementArgLst::List{<:Absyn.ElementArg}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, List{Absyn.ElementArg}}
              local outAbsynElementArgLst::List{Absyn.ElementArg}
              local outCache::FCore.Cache

              (outCache, outAbsynElementArgLst) = begin
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local mod_1::Absyn.Modification
                  local mod::Absyn.Modification
                  local res::List{Absyn.ElementArg}
                  local args::List{Absyn.ElementArg}
                  local b::Bool
                  local impl::Bool
                  local e::Absyn.Each
                  local stropt::Option{String}
                  local m::Absyn.ElementArg
                  local cache::FCore.Cache
                  local mod_info::SourceInfo
                  local p::Absyn.Path
                @matchcontinue (inCache, inEnv, inAbsynElementArgLst, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, Absyn.MODIFICATION(finalPrefix = b, eachPrefix = e, path = p, modification = SOME(mod), comment = stropt, info = mod_info) <| args, impl, msg, _)  => begin
                      (cache, mod_1) = cevalAstModification(cache, env, mod, impl, msg, info)
                      (cache, res) = cevalAstEltargs(cache, env, args, impl, msg, info)
                    (cache, _cons(Absyn.MODIFICATION(b, e, p, SOME(mod_1), stropt, mod_info), res))
                  end

                  (cache, env, m <| args, impl, msg, _)  => begin
                      (cache, res) = cevalAstEltargs(cache, env, args, impl, msg, info)
                    (cache, _cons(m, res))
                  end
                end
              end
               #= /* TODO: look through redeclarations for Eval(var) as well */ =#
               #= /* TODO: look through redeclarations for Eval(var) as well */ =#
          (outCache, outAbsynElementArgLst)
        end

         #= Helper function to cevaAstCitems =#
        function cevalAstArraydim(inCache::FCore.Cache, inEnv::FCore.Graph, inArrayDim::Absyn.ArrayDim, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, Absyn.ArrayDim}
              local outArrayDim::Absyn.ArrayDim
              local outCache::FCore.Cache

              (outCache, outArrayDim) = begin
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local res::List{Absyn.Subscript}
                  local xs::List{Absyn.Subscript}
                  local impl::Bool
                  local e_1::Absyn.Exp
                  local e::Absyn.Exp
                  local cache::FCore.Cache
                @match (inCache, inEnv, inArrayDim, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, Absyn.NOSUB(__) <| xs, impl, msg, _)  => begin
                      (cache, res) = cevalAstArraydim(cache, env, xs, impl, msg, info)
                    (cache, _cons(Absyn.NOSUB(), res))
                  end

                  (cache, env, Absyn.SUBSCRIPT(subscript = e) <| xs, impl, msg, _)  => begin
                      (cache, res) = cevalAstArraydim(cache, env, xs, impl, msg, info)
                      (cache, _) = cevalAstExp(cache, env, e, impl, msg, info)
                    (cache, _cons(Absyn.SUBSCRIPT(e), res))
                  end
                end
              end
          (outCache, outArrayDim)
        end

         #= For IFEXP =#
        function cevalAstExpexpList(inCache::FCore.Cache, inEnv::FCore.Graph, inExpTpls::List{<:Tuple{<:Absyn.Exp, Absyn.Exp}}, inBoolean::Bool, inMsg::Absyn.Msg, info::SourceInfo) ::Tuple{FCore.Cache, List{Tuple{Absyn.Exp, Absyn.Exp}}}
              local outExpTpls::List{Tuple{Absyn.Exp, Absyn.Exp}}
              local outCache::FCore.Cache

              (outCache, outExpTpls) = begin
                  local msg::Absyn.Msg
                  local e1_1::Absyn.Exp
                  local e2_1::Absyn.Exp
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                  local res::List{Tuple{Absyn.Exp, Absyn.Exp}}
                  local xs::List{Tuple{Absyn.Exp, Absyn.Exp}}
                  local env::FCore.Graph
                  local impl::Bool
                  local cache::FCore.Cache
                @match (inCache, inEnv, inExpTpls, inBoolean, inMsg, info) begin
                  (cache, _,  nil(), _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, (e1, e2) <| xs, impl, msg, _)  => begin
                      (cache, e1_1) = cevalAstExp(cache, env, e1, impl, msg, info)
                      (cache, e2_1) = cevalAstExp(cache, env, e2, impl, msg, info)
                      (cache, res) = cevalAstExpexpList(cache, env, xs, impl, msg, info)
                    (cache, _cons((e1_1, e2_1), res))
                  end
                end
              end
          (outCache, outExpTpls)
        end

         #= Constant evaluates a dimension, returning the size of the dimension as a value. =#
        function cevalDimension(inCache::FCore.Cache, inEnv::FCore.Graph, inDimension::DAE.Dimension, inImpl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value}
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local dim_int::ModelicaInteger
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                  local res::Values.Value
                   #=  Integer dimension, already constant.
                   =#
                @match (inCache, inEnv, inDimension, inImpl, inMsg, numIter) begin
                  (_, _, DAE.DIM_INTEGER(integer = dim_int), _, _, _)  => begin
                    (inCache, Values.INTEGER(dim_int))
                  end

                  (_, _, DAE.DIM_ENUM(size = dim_int), _, _, _)  => begin
                    (inCache, Values.INTEGER(dim_int))
                  end

                  (_, _, DAE.DIM_BOOLEAN(__), _, _, _)  => begin
                    (inCache, Values.INTEGER(2))
                  end

                  (_, _, DAE.DIM_EXP(exp = exp), _, _, _)  => begin
                      (cache, res) = ceval(inCache, inEnv, exp, inImpl, inMsg, numIter + 1)
                    (cache, res)
                  end
                end
              end
               #=  Enumeration dimension, already constant.
               =#
               #=  Dimension given by expression, evaluate the expression.
               =#
          (outCache, outValue)
        end

        function makeReductionAllCombinations(inValMatrix::List{<:List{<:Values.Value}}, rtype::Absyn.ReductionIterType) ::List{List{Values.Value}}
              local valMatrix::List{List{Values.Value}}

              valMatrix = begin
                @match (inValMatrix, rtype) begin
                  (_, Absyn.COMBINE(__))  => begin
                    listReverse(ListUtil.allCombinations(inValMatrix, SOME(100000), AbsynUtil.dummyInfo))
                  end

                  (_, Absyn.THREAD(__))  => begin
                    listReverse(ListUtil.transposeList(inValMatrix))
                  end
                end
              end
          valMatrix
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

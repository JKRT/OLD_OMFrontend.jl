  module CevalFunction 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl LoopControl 

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
         #=  Jump table for CevalFunction:
         =#
         #=  [TYPE]  Types.
         =#
         #=  [EVAL]  Constant evaluation functions.
         =#
         #=  [EENV]  Environment extension functions (add variables).
         =#
         #=  [MENV]  Environment manipulation functions (set and get variables).
         =#
         #=  [DEPS]  Function variable dependency handling.
         =#
         #=  [EOPT]  Expression optimization functions.
         =#
         #=  public imports
         =#

        import Absyn

        import AbsynUtil

        import DAE

        import FCore

        import SCode

        import Values
         #=  protected imports
         =#

        import Ceval

        import ClassInf

        import ComponentReference

        import DAEDump

        import DAEUtil

        import Debug

        import ElementSource

        import Error

        import Expression

        import ExpressionDump

        import Flags

        import Graph

        import Lapack

        import ListUtil

        import Lookup

        import Types

        import Util

        import ValuesUtil

        import FGraph

        import FNode
         #=  [TYPE]  Types
         =#

        FunctionVar = Tuple 
         #=  LoopControl is used to control the functions behaviour in different
         =#
         #=  situations. All evaluation functions returns a LoopControl variable that
         =#
         #=  tells the caller whether it should continue evaluating or not.
         =#

         @Uniontype LoopControl begin
              @Record NEXT begin

              end

              @Record BREAK begin

              end

              @Record RETURN begin

              end
         end

         #=  [EVAL]  Constant evaluation functions.
         =#

         #= This is the entry point of CevalFunction. This function constant evaluates a
          function given an instantiated function and a list of function arguments. =#
        function evaluate(inCache::FCore.Cache, inEnv::FCore.Graph, inFunction::DAE.Function, inFunctionArguments::List{<:Values.Value}) ::Tuple{FCore.Cache, Values.Value} 
              local outResult::Values.Value
              local outCache::FCore.Cache

              (outCache, outResult) = begin
                  local p::Absyn.Path
                  local func::DAE.FunctionDefinition
                  local ty::DAE.Type
                  local result::Values.Value
                  local func_name::String
                  local cache::FCore.Cache
                  local partialPrefix::Bool
                  local src::DAE.ElementSource
                   #=  The DAE.FUNCTION structure might contain an optional function derivative
                   =#
                   #=  mapping which is why functions below is a list. We only evaluate the
                   =#
                   #=  first function, which is hopefully the one we want.
                   =#
                @matchcontinue (inCache, inEnv, inFunction, inFunctionArguments) begin
                  (_, _, DAE.FUNCTION(path = p, functions = func <| _, type_ = ty, partialPrefix = false, source = src), _)  => begin
                      func_name = AbsynUtil.pathString(p)
                      (cache, result) = evaluateFunctionDefinition(inCache, inEnv, func_name, func, ty, inFunctionArguments, src)
                    (cache, result)
                  end
                  
                  (_, _, DAE.FUNCTION(path = p, functions = _ <| _, partialPrefix = partialPrefix), _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- CevalFunction.evaluate failed for function: " + (if partialPrefix
                            "partial "
                          else
                            ""
                          end) + AbsynUtil.pathString(p))
                    fail()
                  end
                end
              end
          (outCache, outResult)
        end

         #= This function constant evaluates a function definition. =#
        function evaluateFunctionDefinition(inCache::FCore.Cache, inEnv::FCore.Graph, inFuncName::String, inFunc::DAE.FunctionDefinition, inFuncType::DAE.Type, inFuncArgs::List{<:Values.Value}, inSource::DAE.ElementSource) ::Tuple{FCore.Cache, Values.Value} 
              local outResult::Values.Value
              local outCache::FCore.Cache

              (outCache, outResult) = begin
                  local body::List{DAE.Element}
                  local vars::List{DAE.Element}
                  local output_vars::List{DAE.Element}
                  local func_params::List{FunctionVar}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local return_values::List{Values.Value}
                  local return_value::Values.Value
                  local ext_fun_name::String
                  local ext_fun_args::List{DAE.ExtArg}
                  local ext_fun_ret::DAE.ExtArg
                @matchcontinue (inCache, inEnv, inFuncName, inFunc, inFuncType, inFuncArgs, inSource) begin
                  (_, _, _, DAE.FUNCTION_DEF(body = body), _, _, _)  => begin
                      (vars, body) = ListUtil.splitOnFirstMatch(body, DAEUtil.isNotVar)
                      vars = ListUtil.map(vars, removeSelfReferentialDims)
                      output_vars = ListUtil.filterOnTrue(vars, DAEUtil.isOutputVar)
                      func_params = pairFuncParamsWithArgs(vars, inFuncArgs)
                      func_params = sortFunctionVarsByDependency(func_params, inSource)
                      (cache, env) = setupFunctionEnvironment(inCache, inEnv, inFuncName, func_params)
                      (cache, env, _) = evaluateElements(body, cache, env, NEXT())
                      return_values = ListUtil.map1(output_vars, getFunctionReturnValue, env)
                      return_value = boxReturnValue(return_values)
                    (cache, return_value)
                  end
                  
                  (_, _, _, DAE.FUNCTION_EXT(body = body, externalDecl = DAE.EXTERNALDECL(name = ext_fun_name, args = ext_fun_args)), _, _, _)  => begin
                      (vars, _) = ListUtil.splitOnFirstMatch(body, DAEUtil.isNotVar)
                      vars = ListUtil.map(vars, removeSelfReferentialDims)
                      output_vars = ListUtil.filterOnTrue(vars, DAEUtil.isOutputVar)
                      func_params = pairFuncParamsWithArgs(vars, inFuncArgs)
                      func_params = sortFunctionVarsByDependency(func_params, inSource)
                      (cache, env) = setupFunctionEnvironment(inCache, inEnv, inFuncName, func_params)
                      (cache, env) = evaluateExternalFunc(ext_fun_name, ext_fun_args, cache, env)
                      return_values = ListUtil.map1(output_vars, getFunctionReturnValue, env)
                      return_value = boxReturnValue(return_values)
                    (cache, return_value)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- CevalFunction.evaluateFunction failed.\\n")
                      fail()
                  end
                end
              end
               #=  Split the definition into function variables and statements.
               =#
               #=  Save the output variables, so that we can return their values when
               =#
               #=  we're done.
               =#
               #=  Pair the input arguments to input parameters and sort the function
               =#
               #=  variables by dependencies.
               =#
               #=  Create an environment for the function and add all function variables.
               =#
               #=  Evaluate the body of the function.
               =#
               #=  Fetch the values of the output variables.
               =#
               #=  If we have several output variables they should be boxed into a tuple.
               =#
               #=  Get all variables from the function. Ignore everything else, since
               =#
               #=  external functions shouldn't have statements.
               =#
               #=  Save the output variables, so that we can return their values when
               =#
               #=  we're done.
               =#
               #=  Pair the input arguments to input parameters and sort the function
               =#
               #=  variables by dependencies.
               =#
               #=  Create an environment for the function and add all function variables.
               =#
               #=  Call the function.
               =#
               #=  Fetch the values of the output variables.
               =#
               #=  If we have several output variables they should be boxed into a tuple.
               =#
          (outCache, outResult)
        end

         #= This function pairs up the input arguments to the input parameters, so that
          each input parameter get one input argument. This is done since we sort the
          function variables by dependencies, and need to keep track of which argument
          belongs to which parameter. =#
        function pairFuncParamsWithArgs(inElements::List{<:DAE.Element}, inValues::List{<:Values.Value}) ::List{FunctionVar} 
              local outFunctionVars::List{FunctionVar}

              outFunctionVars = begin
                  local var::DAE.Element
                  local rest_vars::List{DAE.Element}
                  local val::Values.Value
                  local rest_vals::List{Values.Value}
                  local params::List{FunctionVar}
                @match (inElements, inValues) begin
                  ( nil(),  nil())  => begin
                    nil
                  end
                  
                  (DAE.VAR(direction = DAE.INPUT(__)) <| _,  nil())  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- CevalFunction.pairFuncParamsWithArgs failed because of too few input arguments.\\n")
                    fail()
                  end
                  
                  (var && DAE.VAR(direction = DAE.INPUT(__)) <| rest_vars, val <| rest_vals)  => begin
                      params = pairFuncParamsWithArgs(rest_vars, rest_vals)
                    _cons((var, SOME(val)), params)
                  end
                  
                  (var <| rest_vars, _)  => begin
                      params = pairFuncParamsWithArgs(rest_vars, inValues)
                    _cons((var, NONE()), params)
                  end
                end
              end
          outFunctionVars
        end

         #= We can't handle self-referential dimensions in function parameters, i.e.
           x[:, size(x, 1)], so just replace them with : instead. =#
        function removeSelfReferentialDims(inElement::DAE.Element) ::DAE.Element 
              local outElement::DAE.Element

              outElement = begin
                  local cref::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local vd::DAE.VarDirection
                  local vp::DAE.VarParallelism
                  local vv::DAE.VarVisibility
                  local ty::DAE.Type
                  local bind::Option{DAE.Exp}
                  local dims::DAE.InstDims
                  local ct::DAE.ConnectorType
                  local es::DAE.ElementSource
                  local va::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local io::Absyn.InnerOuter
                  local name::String
                @match inElement begin
                  DAE.VAR(cref && DAE.CREF_IDENT(ident = name), vk, vd, vp, vv, ty, bind, dims, ct, es, va, cmt, io)  => begin
                      dims = ListUtil.map1(dims, removeSelfReferentialDim, name)
                    DAE.VAR(cref, vk, vd, vp, vv, ty, bind, dims, ct, es, va, cmt, io)
                  end
                end
              end
          outElement
        end

        function removeSelfReferentialDim(inDim::DAE.Dimension, inName::String) ::DAE.Dimension 
              local outDim::DAE.Dimension

              outDim = begin
                  local exp::DAE.Exp
                  local crefs::List{DAE.ComponentRef}
                @matchcontinue (inDim, inName) begin
                  (DAE.DIM_EXP(exp = exp), _)  => begin
                      crefs = Expression.extractCrefsFromExp(exp)
                      @match true = ListUtil.isMemberOnTrue(inName, crefs, isCrefNamed)
                    DAE.DIM_UNKNOWN()
                  end
                  
                  _  => begin
                      inDim
                  end
                end
              end
          outDim
        end

        function isCrefNamed(inName::String, inCref::DAE.ComponentRef) ::Bool 
              local outIsNamed::Bool

              outIsNamed = begin
                  local name::String
                @match (inName, inCref) begin
                  (_, DAE.CREF_IDENT(ident = name))  => begin
                    stringEq(inName, name)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsNamed
        end

         #= Evaluates an external function argument to a value. =#
        function evaluateExtInputArg(inArgument::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{Values.Value, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::Values.Value

              (outValue, outCache) = begin
                  local cref::DAE.ComponentRef
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local val::Values.Value
                  local cache::FCore.Cache
                  local err_str::String
                @matchcontinue (inArgument, inCache, inEnv) begin
                  (DAE.EXTARG(componentRef = cref, type_ = ty), _, _)  => begin
                      val = getVariableValue(cref, ty, inEnv)
                    (val, inCache)
                  end
                  
                  (DAE.EXTARGEXP(exp = exp), cache, _)  => begin
                      (cache, val) = cevalExp(exp, cache, inEnv)
                    (val, cache)
                  end
                  
                  (DAE.EXTARGSIZE(componentRef = cref, exp = exp), cache, _)  => begin
                      exp = DAE.SIZE(DAE.CREF(cref, DAE.T_UNKNOWN_DEFAULT), SOME(exp))
                      (cache, val) = cevalExp(exp, cache, inEnv)
                    (val, cache)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        err_str = DAEDump.dumpExtArgStr(inArgument)
                        Debug.traceln("- CevalFunction.evaluateExtInputArg failed on " + err_str)
                      fail()
                  end
                end
              end
          (outValue, outCache)
        end

         #= Evaluates an external function argument to an Integer. =#
        function evaluateExtIntArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{ModelicaInteger, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::ModelicaInteger

              @match (Values.INTEGER(outValue), outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
          (outValue, outCache)
        end

         #= Evaluates an external function argument to a Real. =#
        function evaluateExtRealArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{ModelicaReal, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::ModelicaReal

              @match (Values.REAL(outValue), outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
          (outValue, outCache)
        end

         #= Evaluates an external function argument to a String. =#
        function evaluateExtStringArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{String, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::String

              @match (Values.STRING(outValue), outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
          (outValue, outCache)
        end

         #= Evaluates an external function argument to an Integer array. =#
        function evaluateExtIntArrayArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{List{ModelicaInteger}, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::List{ModelicaInteger}

              local val::Values.Value

              (val, outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
              outValue = ValuesUtil.arrayValueInts(val)
          (outValue, outCache)
        end

         #= Evaluates an external function argument to a Real array. =#
        function evaluateExtRealArrayArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{List{ModelicaReal}, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::List{ModelicaReal}

              local val::Values.Value

              (val, outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
              outValue = ValuesUtil.arrayValueReals(val)
          (outValue, outCache)
        end

         #= Evaluates an external function argument to a Real matrix. =#
        function evaluateExtRealMatrixArg(inArg::DAE.ExtArg, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{List{List{ModelicaReal}}, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::List{List{ModelicaReal}}

              local val::Values.Value

              (val, outCache) = evaluateExtInputArg(inArg, inCache, inEnv)
              outValue = ValuesUtil.matrixValueReals(val)
          (outValue, outCache)
        end

         #= Returns the component reference to an external function output. =#
        function evaluateExtOutputArg(inArg::DAE.ExtArg) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              @match DAE.EXTARG(componentRef = outCref) = inArg
          outCref
        end

         #= Assigns the outputs from an external function to the correct variables in the
          environment. =#
        function assignExtOutputs(inArgs::List{<:DAE.ExtArg}, inValues::List{<:Values.Value}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local arg::DAE.ExtArg
                  local val::Values.Value
                  local rest_args::List{DAE.ExtArg}
                  local rest_vals::List{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local cr::DAE.ComponentRef
                @match (inArgs, inValues, inCache, inEnv) begin
                  ( nil(),  nil(), _, _)  => begin
                    (inCache, inEnv)
                  end
                  
                  (arg <| rest_args, val <| rest_vals, cache, env)  => begin
                      cr = evaluateExtOutputArg(arg)
                      val = unliftExtOutputValue(cr, val, env)
                      (cache, env) = assignVariable(cr, val, cache, env)
                      (cache, env) = assignExtOutputs(rest_args, rest_vals, cache, env)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= Some external functions don't make much difference between arrays and
          matrices, so this function converts a matrix value to an array value when
          needed. =#
        function unliftExtOutputValue(inCref::DAE.ComponentRef, inValue::Values.Value, inEnv::FCore.Graph) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local ty::DAE.Type
                  local vals::List{Values.Value}
                  local dim::ModelicaInteger
                  local dims::DAE.Dimensions
                   #=  Matrix value, array type => convert.
                   =#
                @matchcontinue (inCref, inValue, inEnv) begin
                  (_, Values.ARRAY(valueLst = vals && Values.ARRAY(__) <| _, dimLst = dim <| _), _)  => begin
                      @match (DAE.T_ARRAY(ty = ty, dims = dims), _) = getVariableTypeAndBinding(inCref, inEnv)
                      @match false = Types.isNonscalarArray(ty, dims)
                      vals = ListUtil.map(vals, ValuesUtil.arrayScalar)
                    Values.ARRAY(vals, list(dim))
                  end
                  
                  _  => begin
                      inValue
                  end
                end
              end
               #=  Otherwise, do nothing.
               =#
          outValue
        end

         #= This function evaluates an external function, at the moment this means a
          LAPACK function. This function was automatically generated. No programmers
          were hurt during the generation of this function. =#
        function evaluateExternalFunc(inFuncName::String, inFuncArgs::List{<:DAE.ExtArg}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local arg_JOBU::DAE.ExtArg
                  local arg_JOBVL::DAE.ExtArg
                  local arg_JOBVR::DAE.ExtArg
                  local arg_JOBVT::DAE.ExtArg
                  local arg_TRANS::DAE.ExtArg
                  local arg_INFO::DAE.ExtArg
                  local arg_K::DAE.ExtArg
                  local arg_KL::DAE.ExtArg
                  local arg_KU::DAE.ExtArg
                  local arg_LDA::DAE.ExtArg
                  local arg_LDAB::DAE.ExtArg
                  local arg_LDB::DAE.ExtArg
                  local arg_LDU::DAE.ExtArg
                  local arg_LDVL::DAE.ExtArg
                  local arg_LDVR::DAE.ExtArg
                  local arg_LDVT::DAE.ExtArg
                  local arg_LWORK::DAE.ExtArg
                  local arg_M::DAE.ExtArg
                  local arg_N::DAE.ExtArg
                  local arg_NRHS::DAE.ExtArg
                  local arg_P::DAE.ExtArg
                  local arg_RANK::DAE.ExtArg
                  local arg_RCOND::DAE.ExtArg
                  local arg_IPIV::DAE.ExtArg
                  local arg_JPVT::DAE.ExtArg
                  local arg_ALPHAI::DAE.ExtArg
                  local arg_ALPHAR::DAE.ExtArg
                  local arg_BETA::DAE.ExtArg
                  local arg_C::DAE.ExtArg
                  local arg_D::DAE.ExtArg
                  local arg_DL::DAE.ExtArg
                  local arg_DU::DAE.ExtArg
                  local arg_TAU::DAE.ExtArg
                  local arg_WI::DAE.ExtArg
                  local arg_WORK::DAE.ExtArg
                  local arg_WR::DAE.ExtArg
                  local arg_X::DAE.ExtArg
                  local arg_A::DAE.ExtArg
                  local arg_AB::DAE.ExtArg
                  local arg_B::DAE.ExtArg
                  local arg_S::DAE.ExtArg
                  local arg_U::DAE.ExtArg
                  local arg_VL::DAE.ExtArg
                  local arg_VR::DAE.ExtArg
                  local arg_VT::DAE.ExtArg
                  local val_INFO::Values.Value
                  local val_RANK::Values.Value
                  local val_IPIV::Values.Value
                  local val_JPVT::Values.Value
                  local val_ALPHAI::Values.Value
                  local val_ALPHAR::Values.Value
                  local val_BETA::Values.Value
                  local val_C::Values.Value
                  local val_D::Values.Value
                  local val_DL::Values.Value
                  local val_DU::Values.Value
                  local val_TAU::Values.Value
                  local val_WI::Values.Value
                  local val_WORK::Values.Value
                  local val_WR::Values.Value
                  local val_X::Values.Value
                  local val_A::Values.Value
                  local val_AB::Values.Value
                  local val_B::Values.Value
                  local val_S::Values.Value
                  local val_U::Values.Value
                  local val_VL::Values.Value
                  local val_VR::Values.Value
                  local val_VT::Values.Value
                  local INFO::ModelicaInteger
                  local K::ModelicaInteger
                  local KL::ModelicaInteger
                  local KU::ModelicaInteger
                  local LDA::ModelicaInteger
                  local LDAB::ModelicaInteger
                  local LDB::ModelicaInteger
                  local LDU::ModelicaInteger
                  local LDVL::ModelicaInteger
                  local LDVR::ModelicaInteger
                  local LDVT::ModelicaInteger
                  local LWORK::ModelicaInteger
                  local M::ModelicaInteger
                  local N::ModelicaInteger
                  local NRHS::ModelicaInteger
                  local P::ModelicaInteger
                  local RANK::ModelicaInteger
                  local RCOND::ModelicaReal
                  local JOBU::String
                  local JOBVL::String
                  local JOBVR::String
                  local JOBVT::String
                  local TRANS::String
                  local IPIV::List{ModelicaInteger}
                  local JPVT::List{ModelicaInteger}
                  local ALPHAI::List{ModelicaReal}
                  local ALPHAR::List{ModelicaReal}
                  local BETA::List{ModelicaReal}
                  local C::List{ModelicaReal}
                  local D::List{ModelicaReal}
                  local DL::List{ModelicaReal}
                  local DU::List{ModelicaReal}
                  local TAU::List{ModelicaReal}
                  local WI::List{ModelicaReal}
                  local WORK::List{ModelicaReal}
                  local WR::List{ModelicaReal}
                  local X::List{ModelicaReal}
                  local S::List{ModelicaReal}
                  local A::List{List{ModelicaReal}}
                  local AB::List{List{ModelicaReal}}
                  local B::List{List{ModelicaReal}}
                  local U::List{List{ModelicaReal}}
                  local VL::List{List{ModelicaReal}}
                  local VR::List{List{ModelicaReal}}
                  local VT::List{List{ModelicaReal}}
                  local arg_out::List{DAE.ExtArg}
                  local val_out::List{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inFuncName, inFuncArgs, inCache, inEnv) begin
                  ("dgeev", arg_JOBVL <| arg_JOBVR <| arg_N <| arg_A <| arg_LDA <| arg_WR <| arg_WI <| arg_VL <| arg_LDVL <| arg_VR <| arg_LDVR <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (JOBVL, cache) = evaluateExtStringArg(arg_JOBVL, cache, env)
                      (JOBVR, cache) = evaluateExtStringArg(arg_JOBVR, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (LDVL, cache) = evaluateExtIntArg(arg_LDVL, cache, env)
                      (LDVR, cache) = evaluateExtIntArg(arg_LDVR, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, WR, WI, VL, VR, WORK, INFO) = Lapack.dgeev(JOBVL, JOBVR, N, A, LDA, LDVL, LDVR, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_WR = ValuesUtil.makeRealArray(WR)
                      val_WI = ValuesUtil.makeRealArray(WI)
                      val_VL = ValuesUtil.makeRealMatrix(VL)
                      val_VR = ValuesUtil.makeRealMatrix(VR)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_WR, arg_WI, arg_VL, arg_VR, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_WR, val_WI, val_VL, val_VR, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgegv", arg_JOBVL <| arg_JOBVR <| arg_N <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_ALPHAR <| arg_ALPHAI <| arg_BETA <| arg_VL <| arg_LDVL <| arg_VR <| arg_LDVR <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (JOBVL, cache) = evaluateExtStringArg(arg_JOBVL, cache, env)
                      (JOBVR, cache) = evaluateExtStringArg(arg_JOBVR, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (LDVL, cache) = evaluateExtIntArg(arg_LDVL, cache, env)
                      (LDVR, cache) = evaluateExtIntArg(arg_LDVR, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (ALPHAR, ALPHAI, BETA, VL, VR, WORK, INFO) = Lapack.dgegv(JOBVL, JOBVR, N, A, LDA, B, LDB, LDVL, LDVR, WORK, LWORK)
                      val_ALPHAR = ValuesUtil.makeRealArray(ALPHAR)
                      val_ALPHAI = ValuesUtil.makeRealArray(ALPHAI)
                      val_BETA = ValuesUtil.makeRealArray(BETA)
                      val_VL = ValuesUtil.makeRealMatrix(VL)
                      val_VR = ValuesUtil.makeRealMatrix(VR)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_ALPHAR, arg_ALPHAI, arg_BETA, arg_VL, arg_VR, arg_WORK, arg_INFO)
                      val_out = list(val_ALPHAR, val_ALPHAI, val_BETA, val_VL, val_VR, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgels", arg_TRANS <| arg_M <| arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (TRANS, cache) = evaluateExtStringArg(arg_TRANS, cache, env)
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, B, WORK, INFO) = Lapack.dgels(TRANS, M, N, NRHS, A, LDA, B, LDB, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_B, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_B, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgelsx", arg_M <| arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_JPVT <| arg_RCOND <| arg_RANK <| arg_WORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (JPVT, cache) = evaluateExtIntArrayArg(arg_JPVT, cache, env)
                      (RCOND, cache) = evaluateExtRealArg(arg_RCOND, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (A, B, JPVT, RANK, INFO) = Lapack.dgelsx(M, N, NRHS, A, LDA, B, LDB, JPVT, RCOND, WORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_JPVT = ValuesUtil.makeIntArray(JPVT)
                      val_RANK = ValuesUtil.makeInteger(RANK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_B, arg_JPVT, arg_RANK, arg_INFO)
                      val_out = list(val_A, val_B, val_JPVT, val_RANK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgelsx", arg_M <| arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_JPVT <| arg_RCOND <| arg_RANK <| arg_WORK <| _ <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (JPVT, cache) = evaluateExtIntArrayArg(arg_JPVT, cache, env)
                      (RCOND, cache) = evaluateExtRealArg(arg_RCOND, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (A, B, JPVT, RANK, INFO) = Lapack.dgelsx(M, N, NRHS, A, LDA, B, LDB, JPVT, RCOND, WORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_JPVT = ValuesUtil.makeIntArray(JPVT)
                      val_RANK = ValuesUtil.makeInteger(RANK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_B, arg_JPVT, arg_RANK, arg_INFO)
                      val_out = list(val_A, val_B, val_JPVT, val_RANK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgelsy", arg_M <| arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_JPVT <| arg_RCOND <| arg_RANK <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (JPVT, cache) = evaluateExtIntArrayArg(arg_JPVT, cache, env)
                      (RCOND, cache) = evaluateExtRealArg(arg_RCOND, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, B, JPVT, RANK, WORK, INFO) = Lapack.dgelsy(M, N, NRHS, A, LDA, B, LDB, JPVT, RCOND, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_JPVT = ValuesUtil.makeIntArray(JPVT)
                      val_RANK = ValuesUtil.makeInteger(RANK)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_B, arg_JPVT, arg_RANK, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_B, val_JPVT, val_RANK, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgesv", arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_IPIV <| arg_B <| arg_LDB <| arg_INFO <|  nil(), cache, env)  => begin
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (A, IPIV, B, INFO) = Lapack.dgesv(N, NRHS, A, LDA, B, LDB)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_IPIV = ValuesUtil.makeIntArray(IPIV)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_IPIV, arg_B, arg_INFO)
                      val_out = list(val_A, val_IPIV, val_B, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgglse", arg_M <| arg_N <| arg_P <| arg_A <| arg_LDA <| arg_B <| arg_LDB <| arg_C <| arg_D <| arg_X <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (P, cache) = evaluateExtIntArg(arg_P, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (C, cache) = evaluateExtRealArrayArg(arg_C, cache, env)
                      (D, cache) = evaluateExtRealArrayArg(arg_D, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, B, C, D, X, WORK, INFO) = Lapack.dgglse(M, N, P, A, LDA, B, LDB, C, D, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_C = ValuesUtil.makeRealArray(C)
                      val_D = ValuesUtil.makeRealArray(D)
                      val_X = ValuesUtil.makeRealArray(X)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_B, arg_C, arg_D, arg_X, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_B, val_C, val_D, val_X, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgtsv", arg_N <| arg_NRHS <| arg_DL <| arg_D <| arg_DU <| arg_B <| arg_LDB <| arg_INFO <|  nil(), cache, env)  => begin
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (DL, cache) = evaluateExtRealArrayArg(arg_DL, cache, env)
                      (D, cache) = evaluateExtRealArrayArg(arg_D, cache, env)
                      (DU, cache) = evaluateExtRealArrayArg(arg_DU, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (DL, D, DU, B, INFO) = Lapack.dgtsv(N, NRHS, DL, D, DU, B, LDB)
                      val_DL = ValuesUtil.makeRealArray(DL)
                      val_D = ValuesUtil.makeRealArray(D)
                      val_DU = ValuesUtil.makeRealArray(DU)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_DL, arg_D, arg_DU, arg_B, arg_INFO)
                      val_out = list(val_DL, val_D, val_DU, val_B, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgbsv", arg_N <| arg_KL <| arg_KU <| arg_NRHS <| arg_AB <| arg_LDAB <| arg_IPIV <| arg_B <| arg_LDB <| arg_INFO <|  nil(), cache, env)  => begin
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (KL, cache) = evaluateExtIntArg(arg_KL, cache, env)
                      (KU, cache) = evaluateExtIntArg(arg_KU, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (AB, cache) = evaluateExtRealMatrixArg(arg_AB, cache, env)
                      (LDAB, cache) = evaluateExtIntArg(arg_LDAB, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (AB, IPIV, B, INFO) = Lapack.dgbsv(N, KL, KU, NRHS, AB, LDAB, B, LDB)
                      val_AB = ValuesUtil.makeRealMatrix(AB)
                      val_IPIV = ValuesUtil.makeIntArray(IPIV)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_AB, arg_IPIV, arg_B, arg_INFO)
                      val_out = list(val_AB, val_IPIV, val_B, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgesvd", arg_JOBU <| arg_JOBVT <| arg_M <| arg_N <| arg_A <| arg_LDA <| arg_S <| arg_U <| arg_LDU <| arg_VT <| arg_LDVT <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (JOBU, cache) = evaluateExtStringArg(arg_JOBU, cache, env)
                      (JOBVT, cache) = evaluateExtStringArg(arg_JOBVT, cache, env)
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (LDU, cache) = evaluateExtIntArg(arg_LDU, cache, env)
                      (LDVT, cache) = evaluateExtIntArg(arg_LDVT, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, S, U, VT, WORK, INFO) = Lapack.dgesvd(JOBU, JOBVT, M, N, A, LDA, LDU, LDVT, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_S = ValuesUtil.makeRealArray(S)
                      val_U = ValuesUtil.makeRealMatrix(U)
                      val_VT = ValuesUtil.makeRealMatrix(VT)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_S, arg_U, arg_VT, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_S, val_U, val_VT, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgetrf", arg_M <| arg_N <| arg_A <| arg_LDA <| arg_IPIV <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (A, IPIV, INFO) = Lapack.dgetrf(M, N, A, LDA)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_IPIV = ValuesUtil.makeIntArray(IPIV)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_IPIV, arg_INFO)
                      val_out = list(val_A, val_IPIV, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgetrs", arg_TRANS <| arg_N <| arg_NRHS <| arg_A <| arg_LDA <| arg_IPIV <| arg_B <| arg_LDB <| arg_INFO <|  nil(), cache, env)  => begin
                      (TRANS, cache) = evaluateExtStringArg(arg_TRANS, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (NRHS, cache) = evaluateExtIntArg(arg_NRHS, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (IPIV, cache) = evaluateExtIntArrayArg(arg_IPIV, cache, env)
                      (B, cache) = evaluateExtRealMatrixArg(arg_B, cache, env)
                      (LDB, cache) = evaluateExtIntArg(arg_LDB, cache, env)
                      (B, INFO) = Lapack.dgetrs(TRANS, N, NRHS, A, LDA, IPIV, B, LDB)
                      val_B = ValuesUtil.makeRealMatrix(B)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_B, arg_INFO)
                      val_out = list(val_B, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgetri", arg_N <| arg_A <| arg_LDA <| arg_IPIV <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (IPIV, cache) = evaluateExtIntArrayArg(arg_IPIV, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, WORK, INFO) = Lapack.dgetri(N, A, LDA, IPIV, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dgeqpf", arg_M <| arg_N <| arg_A <| arg_LDA <| arg_JPVT <| arg_TAU <| arg_WORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (JPVT, cache) = evaluateExtIntArrayArg(arg_JPVT, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (A, JPVT, TAU, INFO) = Lapack.dgeqpf(M, N, A, LDA, JPVT, WORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_JPVT = ValuesUtil.makeIntArray(JPVT)
                      val_TAU = ValuesUtil.makeRealArray(TAU)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_JPVT, arg_TAU, arg_INFO)
                      val_out = list(val_A, val_JPVT, val_TAU, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                  
                  ("dorgqr", arg_M <| arg_N <| arg_K <| arg_A <| arg_LDA <| arg_TAU <| arg_WORK <| arg_LWORK <| arg_INFO <|  nil(), cache, env)  => begin
                      (M, cache) = evaluateExtIntArg(arg_M, cache, env)
                      (N, cache) = evaluateExtIntArg(arg_N, cache, env)
                      (K, cache) = evaluateExtIntArg(arg_K, cache, env)
                      (A, cache) = evaluateExtRealMatrixArg(arg_A, cache, env)
                      (LDA, cache) = evaluateExtIntArg(arg_LDA, cache, env)
                      (TAU, cache) = evaluateExtRealArrayArg(arg_TAU, cache, env)
                      (WORK, cache) = evaluateExtRealArrayArg(arg_WORK, cache, env)
                      (LWORK, cache) = evaluateExtIntArg(arg_LWORK, cache, env)
                      (A, WORK, INFO) = Lapack.dorgqr(M, N, K, A, LDA, TAU, WORK, LWORK)
                      val_A = ValuesUtil.makeRealMatrix(A)
                      val_WORK = ValuesUtil.makeRealArray(WORK)
                      val_INFO = ValuesUtil.makeInteger(INFO)
                      arg_out = list(arg_A, arg_WORK, arg_INFO)
                      val_out = list(val_A, val_WORK, val_INFO)
                      (cache, env) = assignExtOutputs(arg_out, val_out, cache, env)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= This function evaluates a list of elements. =#
        function evaluateElements(inElements::List{<:DAE.Element}, inCache::FCore.Cache, inEnv::FCore.Graph, inLoopControl::LoopControl) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local elem::DAE.Element
                  local rest_elems::List{DAE.Element}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local loop_ctrl::LoopControl
                @match (inElements, inCache, inEnv, inLoopControl) begin
                  (_, _, _, RETURN(__))  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  ( nil(), _, _, _)  => begin
                    (inCache, inEnv, NEXT())
                  end
                  
                  (elem <| rest_elems, _, _, _)  => begin
                      (cache, env, loop_ctrl) = evaluateElement(elem, inCache, inEnv)
                      (cache, env, loop_ctrl) = evaluateElements(rest_elems, cache, env, loop_ctrl)
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates a single element, which should be an algorithm. =#
        function evaluateElement(inElement::DAE.Element, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local loop_ctrl::LoopControl
                  local sl::List{DAE.Statement}
                @match (inElement, inCache, inEnv) begin
                  (DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(statementLst = sl)), _, _)  => begin
                      (sl, (_, env)) = DAEUtil.traverseDAEEquationsStmts(sl, Expression.traverseSubexpressionsHelper, (optimizeExpTraverser, inEnv))
                      (cache, env, loop_ctrl) = evaluateStatements(sl, inCache, env)
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates a statement. =#
        function evaluateStatement(inStatement::DAE.Statement, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local condition::DAE.Exp
                  local lhs_cref::DAE.ComponentRef
                  local rhs_val::Values.Value
                  local v::Values.Value
                  local exps::List{DAE.Exp}
                  local vals::List{Values.Value}
                  local statements::List{DAE.Statement}
                  local path::Absyn.Path
                  local returnType::DAE.Type
                  local loop_ctrl::LoopControl
                  local tailCall::DAE.TailCall
                  local var::String
                  local vars::List{String}
                @match (inStatement, inCache, inEnv) begin
                  (DAE.STMT_ASSIGN(exp1 = lhs, exp = rhs), cache, env)  => begin
                      (cache, rhs_val) = cevalExp(rhs, cache, env)
                      lhs_cref = extractLhsComponentRef(lhs)
                      (cache, env) = assignVariable(lhs_cref, rhs_val, cache, env)
                    (cache, env, NEXT())
                  end
                  
                  (DAE.STMT_TUPLE_ASSIGN(__), _, _)  => begin
                      (cache, env) = evaluateTupleAssignStatement(inStatement, inCache, inEnv)
                    (cache, env, NEXT())
                  end
                  
                  (DAE.STMT_ASSIGN_ARR(lhs = lhs, exp = rhs), _, env)  => begin
                      (cache, rhs_val) = cevalExp(rhs, inCache, env)
                      lhs_cref = extractLhsComponentRef(lhs)
                      (cache, env) = assignVariable(lhs_cref, rhs_val, cache, env)
                    (cache, env, NEXT())
                  end
                  
                  (DAE.STMT_IF(__), _, _)  => begin
                      (cache, env, loop_ctrl) = evaluateIfStatement(inStatement, inCache, inEnv)
                    (cache, env, loop_ctrl)
                  end
                  
                  (DAE.STMT_FOR(__), _, _)  => begin
                      (cache, env, loop_ctrl) = evaluateForStatement(inStatement, inCache, inEnv)
                    (cache, env, loop_ctrl)
                  end
                  
                  (DAE.STMT_WHILE(exp = condition, statementLst = statements), _, _)  => begin
                      (cache, env, loop_ctrl) = evaluateWhileStatement(condition, statements, inCache, inEnv, NEXT())
                    (cache, env, loop_ctrl)
                  end
                  
                  (DAE.STMT_ASSERT(cond = condition), _, _)  => begin
                      @match (cache, Values.BOOL(boolean = true)) = cevalExp(condition, inCache, inEnv)
                    (cache, inEnv, NEXT())
                  end
                  
                  (DAE.STMT_ASSERT(cond = condition), _, _)  => begin
                      @match (cache, Values.BOOL(boolean = true)) = cevalExp(condition, inCache, inEnv)
                    (cache, inEnv, NEXT())
                  end
                  
                  (DAE.STMT_NORETCALL(exp = rhs && DAE.CALL(expLst = exps, attr = DAE.CALL_ATTR(ty = _, tailCall = tailCall))), _, _)  => begin
                       #=  If the condition is true in the assert, do nothing. If the condition
                       =#
                       #=  is false we should stop the instantiation (depending on the assertion
                       =#
                       #=  level), but we can't really do much about that here. So right now we just
                       =#
                       #=  fail.
                       =#
                       #=  Special case for print, and other known calls for now; evaluated even when there is no ST
                       =#
                      (cache, vals) = cevalExpList(exps, inCache, inEnv)
                      (cache, v) = cevalExp(rhs, cache, inEnv)
                      (cache, env, outLoopControl) = begin
                        @match tailCall begin
                          DAE.NO_TAIL(__)  => begin
                            (cache, inEnv, NEXT())
                          end
                          
                          DAE.TAIL(outVars =  nil())  => begin
                            (cache, inEnv, RETURN())
                          end
                          
                          DAE.TAIL(outVars = var <|  nil())  => begin
                               #=  Handle tail recursion; same as a assigning all outputs followed by a return
                               =#
                              (cache, env) = assignVariable(ComponentReference.makeUntypedCrefIdent(var), v, cache, inEnv)
                            (cache, env, RETURN())
                          end
                          
                          DAE.TAIL(outVars = vars)  => begin
                              @match Values.TUPLE(vals) = v
                              for val in vals
                                @match _cons(var, vars) = vars
                                (cache, env) = assignVariable(ComponentReference.makeUntypedCrefIdent(var), val, cache, inEnv)
                              end
                            (cache, env, RETURN())
                          end
                        end
                      end
                    (cache, env, NEXT())
                  end
                  
                  (DAE.STMT_RETURN(__), _, _)  => begin
                    (inCache, inEnv, RETURN())
                  end
                  
                  (DAE.STMT_BREAK(__), _, _)  => begin
                    (inCache, inEnv, BREAK())
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- CevalFunction.evaluateStatement failed for:")
                        Debug.traceln(DAEDump.ppStatementStr(inStatement))
                      fail()
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates a list of statements. This is just a wrapper for
          evaluateStatements2. =#
        function evaluateStatements(inStatement::List{<:DAE.Statement}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = evaluateStatements2(inStatement, inCache, inEnv, NEXT())
          (outCache, outEnv, outLoopControl)
        end

         #= This is a helper function to evaluateStatements that evaluates a list of
          statements. =#
        function evaluateStatements2(inStatement::List{<:DAE.Statement}, inCache::FCore.Cache, inEnv::FCore.Graph, inLoopControl::LoopControl) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local stmt::DAE.Statement
                  local rest_stmts::List{DAE.Statement}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local loop_ctrl::LoopControl
                @match (inStatement, inCache, inEnv, inLoopControl) begin
                  (_, _, _, BREAK(__))  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  (_, _, _, RETURN(__))  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  ( nil(), _, _, _)  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  (stmt <| rest_stmts, _, _, NEXT(__))  => begin
                      (cache, env, loop_ctrl) = evaluateStatement(stmt, inCache, inEnv)
                      (cache, env, loop_ctrl) = evaluateStatements2(rest_stmts, cache, env, loop_ctrl)
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates tuple assignment statements, i.e. assignment
          statements where the right hand side expression is a tuple. Ex:
            (x, y, z) := fun(...) =#
        function evaluateTupleAssignStatement(inStatement::DAE.Statement, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local lhs_expl::List{DAE.Exp}
                  local rhs::DAE.Exp
                  local rhs_vals::List{Values.Value}
                  local lhs_crefs::List{DAE.ComponentRef}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inStatement, inCache, inEnv) begin
                  (DAE.STMT_TUPLE_ASSIGN(expExpLst = lhs_expl, exp = rhs), _, env)  => begin
                      @match (cache, Values.TUPLE(valueLst = rhs_vals)) = cevalExp(rhs, inCache, env)
                      lhs_crefs = ListUtil.map(lhs_expl, extractLhsComponentRef)
                      (cache, env) = assignTuple(lhs_crefs, rhs_vals, cache, env)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= This function evaluates an if statement. =#
        function evaluateIfStatement(inStatement::DAE.Statement, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local cond::DAE.Exp
                  local stmts::List{DAE.Statement}
                  local else_branch::DAE.Else
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local bool_cond::Bool
                  local loop_ctrl::LoopControl
                @match (inStatement, inCache, inEnv) begin
                  (DAE.STMT_IF(exp = cond, statementLst = stmts, else_ = else_branch), _, _)  => begin
                      @match (cache, Values.BOOL(boolean = bool_cond)) = cevalExp(cond, inCache, inEnv)
                      (cache, env, loop_ctrl) = evaluateIfStatement2(bool_cond, stmts, else_branch, cache, inEnv)
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= Helper function to evaluateIfStatement. =#
        function evaluateIfStatement2(inCondition::Bool, inStatements::List{<:DAE.Statement}, inElse::DAE.Else, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local statements::List{DAE.Statement}
                  local condition::DAE.Exp
                  local bool_condition::Bool
                  local else_branch::DAE.Else
                  local loop_ctrl::LoopControl
                   #=  If the condition is true, evaluate the statements in the if branch.
                   =#
                @match (inCondition, inStatements, inElse, inCache, inEnv) begin
                  (true, statements, _, _, env)  => begin
                      (cache, env, loop_ctrl) = evaluateStatements(statements, inCache, env)
                    (cache, env, loop_ctrl)
                  end
                  
                  (false, _, DAE.ELSE(statementLst = statements), _, env)  => begin
                      (cache, env, loop_ctrl) = evaluateStatements(statements, inCache, env)
                    (cache, env, loop_ctrl)
                  end
                  
                  (false, _, DAE.ELSEIF(exp = condition, statementLst = statements, else_ = else_branch), _, env)  => begin
                      @match (cache, Values.BOOL(boolean = bool_condition)) = cevalExp(condition, inCache, env)
                      (cache, env, loop_ctrl) = evaluateIfStatement2(bool_condition, statements, else_branch, cache, env)
                    (cache, env, loop_ctrl)
                  end
                  
                  (false, _, DAE.NOELSE(__), _, _)  => begin
                    (inCache, inEnv, NEXT())
                  end
                end
              end
               #=  If the condition is false and we have an else, evaluate the statements in
               =#
               #=  the else branch.
               =#
               #=  If the condition is false and we have an else if, call this function
               =#
               #=  again recursively.
               =#
               #=  If the condition is false and we have no else branch, just continue.
               =#
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates for statements. =#
        function evaluateForStatement(inStatement::DAE.Statement, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local ety::DAE.Type
                  local ty::DAE.Type
                  local iter_name::String
                  local range::DAE.Exp
                  local statements::List{DAE.Statement}
                  local range_vals::List{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local iter_cr::DAE.ComponentRef
                  local loop_ctrl::LoopControl
                   #=  The case where the range is an array.
                   =#
                @matchcontinue (inStatement, inCache, inEnv) begin
                  (DAE.STMT_FOR(type_ = ety, iter = iter_name, range = range, statementLst = statements), _, env)  => begin
                      @match (cache, Values.ARRAY(valueLst = range_vals)) = cevalExp(range, inCache, env)
                      (env, ty, iter_cr) = extendEnvWithForScope(iter_name, ety, env)
                      (cache, env, loop_ctrl) = evaluateForLoopArray(cache, env, iter_cr, ty, range_vals, statements, NEXT())
                    (cache, env, loop_ctrl)
                  end
                  
                  (DAE.STMT_FOR(range = range), _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- evaluateForStatement not implemented for:")
                      Debug.traceln(ExpressionDump.printExpStr(range))
                    fail()
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates a for loop where the range is an array. =#
        function evaluateForLoopArray(inCache::FCore.Cache, inEnv::FCore.Graph, inIter::DAE.ComponentRef, inIterType::DAE.Type, inValues::List{<:Values.Value}, inStatements::List{<:DAE.Statement}, inLoopControl::LoopControl) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local value::Values.Value
                  local rest_vals::List{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local loop_ctrl::LoopControl
                @match (inCache, inEnv, inIter, inIterType, inValues, inStatements, inLoopControl) begin
                  (_, _, _, _, _, _, BREAK(__))  => begin
                    (inCache, inEnv, NEXT())
                  end
                  
                  (_, _, _, _, _, _, RETURN(__))  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  (_, _, _, _,  nil(), _, _)  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  (_, env, _, _, value <| rest_vals, _, NEXT(__))  => begin
                      env = updateVariableBinding(inIter, env, inIterType, value)
                      (cache, env, loop_ctrl) = evaluateStatements(inStatements, inCache, env)
                      (cache, env, loop_ctrl) = evaluateForLoopArray(cache, env, inIter, inIterType, rest_vals, inStatements, loop_ctrl)
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function evaluates a while statement. =#
        function evaluateWhileStatement(inCondition::DAE.Exp, inStatements::List{<:DAE.Statement}, inCache::FCore.Cache, inEnv::FCore.Graph, inLoopControl::LoopControl) ::Tuple{FCore.Cache, FCore.Graph, LoopControl} 
              local outLoopControl::LoopControl
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outLoopControl) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local loop_ctrl::LoopControl
                  local b::Bool
                @match (inCondition, inStatements, inCache, inEnv, inLoopControl) begin
                  (_, _, _, _, BREAK(__))  => begin
                    (inCache, inEnv, NEXT())
                  end
                  
                  (_, _, _, _, RETURN(__))  => begin
                    (inCache, inEnv, inLoopControl)
                  end
                  
                  (_, _, _, _, _)  => begin
                      @match (cache, Values.BOOL(boolean = b)) = cevalExp(inCondition, inCache, inEnv)
                      if b
                        (cache, env, loop_ctrl) = evaluateStatements(inStatements, cache, inEnv)
                        (cache, env, loop_ctrl) = evaluateWhileStatement(inCondition, inStatements, cache, env, loop_ctrl)
                      else
                        loop_ctrl = NEXT()
                        env = inEnv
                      end
                    (cache, env, loop_ctrl)
                  end
                end
              end
          (outCache, outEnv, outLoopControl)
        end

         #= This function extracts a component reference from an expression. It's used to
          get the left hand side component reference in simple assignments. =#
        function extractLhsComponentRef(inExp::DAE.Exp) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              outCref = begin
                  local cref::DAE.ComponentRef
                @match inExp begin
                  DAE.CREF(componentRef = cref)  => begin
                    cref
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- CevalFunction.extractLhsComponentRef failed on " + ExpressionDump.printExpStr(inExp))
                      fail()
                  end
                end
              end
          outCref
        end

         #= A wrapper for Ceval with most of the arguments filled in. =#
        function cevalExp(inExp::DAE.Exp, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = Ceval.ceval(inCache, inEnv, inExp, true, Absyn.NO_MSG(), 0)
              @match false = valueEq(Values.META_FAIL(), outValue)
          (outCache, outValue)
        end

         #= A wrapper for Ceval with most of the arguments filled in. =#
        function cevalExpList(inExpLst::List{<:DAE.Exp}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, List{Values.Value}} 
              local outValue::List{Values.Value}
              local outCache::FCore.Cache

              (outCache, outValue) = Ceval.cevalList(inCache, inEnv, inExpLst, true, Absyn.NO_MSG(), 0)
          (outCache, outValue)
        end

         #=  [EENV]  Environment extension functions (add variables).
         =#

         #= Opens up a new scope for the functions and adds all function variables to it. =#
        function setupFunctionEnvironment(inCache::FCore.Cache, inEnv::FCore.Graph, inFuncName::String, inFuncParams::List{<:FunctionVar}) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              outEnv = FGraph.openScope(inEnv, SCode.NOT_ENCAPSULATED(), inFuncName, SOME(FCore.FUNCTION_SCOPE()))
              (outCache, outEnv) = extendEnvWithFunctionVars(inCache, outEnv, inFuncParams)
          (outCache, outEnv)
        end

         #= Extends the environment with a list of variables. The list of values is the
          input arguments to the function. =#
        function extendEnvWithFunctionVars(inCache::FCore.Cache, inEnv::FCore.Graph, inFuncParams::List{<:FunctionVar}) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local param::FunctionVar
                  local rest_params::List{FunctionVar}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inCache, inEnv, inFuncParams) begin
                  (_, _,  nil())  => begin
                    (inCache, inEnv)
                  end
                  
                  (cache, env, param <| rest_params)  => begin
                      (cache, env) = extendEnvWithFunctionVar(cache, env, param)
                      (cache, env) = extendEnvWithFunctionVars(cache, env, rest_params)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

        function extendEnvWithFunctionVar(inCache::FCore.Cache, inEnv::FCore.Graph, inFuncParam::FunctionVar) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local e::DAE.Element
                  local val::Option{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local binding_exp::Option{DAE.Exp}
                   #=  Input parameters are assigned their corresponding input argument given to
                   =#
                   #=  the function.
                   =#
                @matchcontinue (inCache, inEnv, inFuncParam) begin
                  (_, env, (e, val && SOME(_)))  => begin
                      (cache, env) = extendEnvWithElement(e, val, inCache, env)
                    (cache, env)
                  end
                  
                  (_, env, (e && DAE.VAR(binding = binding_exp), NONE()))  => begin
                      (val, cache) = evaluateBinding(binding_exp, inCache, inEnv)
                      (cache, env) = extendEnvWithElement(e, val, cache, env)
                    (cache, env)
                  end
                  
                  (_, _, (e, _))  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- CevalFunction.extendEnvWithFunctionVars failed for:")
                      Debug.traceln(DAEDump.dumpElementsStr(list(e)))
                    fail()
                  end
                end
              end
               #=  Non-input parameters might have a default binding, so we use that if it's
               =#
               #=  available.
               =#
          (outCache, outEnv)
        end

         #= Evaluates an optional binding expression. If SOME expression is given,
          returns SOME value or fails. If NONE expression given, returns NONE value. =#
        function evaluateBinding(inBinding::Option{<:DAE.Exp}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{Option{Values.Value}, FCore.Cache} 
              local outCache::FCore.Cache
              local outValue::Option{Values.Value}

              (outValue, outCache) = begin
                  local binding_exp::DAE.Exp
                  local cache::FCore.Cache
                  local val::Values.Value
                @match (inBinding, inCache, inEnv) begin
                  (SOME(binding_exp), _, _)  => begin
                      (cache, val) = cevalExp(binding_exp, inCache, inEnv)
                    (SOME(val), cache)
                  end
                  
                  (NONE(), _, _)  => begin
                    (NONE(), inCache)
                  end
                end
              end
          (outValue, outCache)
        end

         #= This function extracts the necessary data from a variable element, and calls
          extendEnvWithVar to add a new variable to the environment. =#
        function extendEnvWithElement(inElement::DAE.Element, inBindingValue::Option{<:Values.Value}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local cr::DAE.ComponentRef
                  local name::String
                  local ty::DAE.Type
                  local dims::DAE.InstDims
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inElement, inBindingValue, inCache, inEnv) begin
                  (DAE.VAR(componentRef = cr, ty = ty, dims = dims), _, _, _)  => begin
                      name = ComponentReference.crefStr(cr)
                      (cache, env) = extendEnvWithVar(name, ty, inBindingValue, dims, inCache, inEnv)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= This function does the actual work of extending the environment with a
          variable. =#
        function extendEnvWithVar(inName::String, inType::DAE.Type, inOptValue::Option{<:Values.Value}, inDims::DAE.InstDims, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local ty::DAE.Type
                  local var::DAE.Var
                  local binding::DAE.Binding
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local record_env::FCore.Graph
                   #=  Records are special, since they have their own environment with their
                   =#
                   #=  components in them. A record variable is thus always unbound, and their
                   =#
                   #=  values are instead determined by their components values.
                   =#
                @matchcontinue (inName, inType, inOptValue, inDims, inCache, inEnv) begin
                  (_, _, _, _, _, _)  => begin
                      @match true = Types.isRecord(inType)
                      binding = getBinding(inOptValue)
                      (cache, ty) = appendDimensions(inType, inOptValue, inDims, inCache, inEnv)
                      var = makeFunctionVariable(inName, ty, binding)
                      (cache, record_env) = makeRecordEnvironment(inType, inOptValue, cache, inEnv)
                      env = FGraph.mkComponentNode(inEnv, var, SCode.COMPONENT(inName, SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), DAE.NOMOD(), FCore.VAR_TYPED(), record_env)
                    (cache, env)
                  end
                  
                  _  => begin
                        binding = getBinding(inOptValue)
                        (cache, ty) = appendDimensions(inType, inOptValue, inDims, inCache, inEnv)
                        var = makeFunctionVariable(inName, ty, binding)
                        env = FGraph.mkComponentNode(inEnv, var, SCode.COMPONENT(inName, SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), DAE.NOMOD(), FCore.VAR_TYPED(), FGraph.empty())
                      (cache, env)
                  end
                end
              end
               #=  Normal variables.
               =#
          (outCache, outEnv)
        end

         #= This function creates a new variable ready to be added to an environment
          given a name, type and binding. =#
        function makeFunctionVariable(inName::String, inType::DAE.Type, inBinding::DAE.Binding) ::DAE.Var 
              local outVar::DAE.Var

              outVar = DAE.TYPES_VAR(inName, DAE.dummyAttrVar, inType, inBinding, NONE())
          outVar
        end

         #= Creates a binding from an optional value. If some value is given we return a
          value bound binding, otherwise an unbound binding. =#
        function getBinding(inBindingValue::Option{<:Values.Value}) ::DAE.Binding 
              local outBinding::DAE.Binding

              outBinding = begin
                  local val::Values.Value
                @match inBindingValue begin
                  SOME(val)  => begin
                    DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE())
                  end
                  
                  NONE()  => begin
                    DAE.UNBOUND()
                  end
                end
              end
          outBinding
        end

         #= This function creates an environment for a record variable by creating a new
          environment and adding the records components to it. If an optional value is
          supplied it also gives the components a value binding. =#
        function makeRecordEnvironment(inRecordType::DAE.Type, inOptValue::Option{<:Values.Value}, inCache::FCore.Cache, inGraph::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outRecordEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outRecordEnv) = begin
                  local var_lst::List{DAE.Var}
                  local vals::List{Option{Values.Value}}
                  local cache::FCore.Cache
                  local graph::FCore.Graph
                  local parent::FCore.Ref
                  local child::FCore.Ref
                  local node::FCore.Node
                @match (inRecordType, inOptValue, inCache, inGraph) begin
                  (DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__), varLst = var_lst), _, _, _)  => begin
                      parent = FGraph.lastScopeRef(inGraph)
                      (graph, node) = FGraph.node(inGraph, FNode.feNodeName, list(parent), FCore.ND(NONE()))
                      child = FNode.toRef(node)
                      FNode.addChildRef(parent, FNode.feNodeName, child)
                      graph = FGraph.pushScopeRef(graph, child)
                      vals = getRecordValues(inOptValue, inRecordType)
                      (cache, graph) = ListUtil.threadFold(var_lst, vals, extendEnvWithRecordVar, (inCache, graph))
                    (cache, graph)
                  end
                end
              end
          (outCache, outRecordEnv)
        end

         #= This function returns a list of optional values that will be assigned to a
          records components. If some record value is given it returns the list of
          values inside it, made into options, otherwise it returns a list of as many
          NONE as there are components in the record. =#
        function getRecordValues(inOptValue::Option{<:Values.Value}, inRecordType::DAE.Type) ::List{Option{Values.Value}} 
              local outValues::List{Option{Values.Value}}

              outValues = begin
                  local vals::List{Values.Value}
                  local opt_vals::List{Option{Values.Value}}
                  local vars::List{DAE.Var}
                  local n::ModelicaInteger
                @match (inOptValue, inRecordType) begin
                  (SOME(Values.RECORD(orderd = vals)), _)  => begin
                      opt_vals = ListUtil.map(vals, Util.makeOption)
                    opt_vals
                  end
                  
                  (NONE(), DAE.T_COMPLEX(varLst = vars))  => begin
                      n = listLength(vars)
                      opt_vals = ListUtil.fill(NONE(), n)
                    opt_vals
                  end
                end
              end
          outValues
        end

         #= This function extends an environment with a record component. =#
        function extendEnvWithRecordVar(inVar::DAE.Var, inOptValue::Option{<:Values.Value}, inEnv::Tuple{<:FCore.Cache, FCore.Graph}) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::Tuple{FCore.Cache, FCore.Graph}

              outEnv = begin
                  local name::String
                  local ty::DAE.Type
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inVar, inOptValue, inEnv) begin
                  (DAE.TYPES_VAR(name = name, ty = ty), _, (cache, env))  => begin
                      (cache, env) = extendEnvWithVar(name, ty, inOptValue, nil, cache, env)
                      outEnv = (cache, env)
                    outEnv
                  end
                end
              end
          outEnv
        end

         #= This function opens a new for loop scope in the environment by opening a new
          scope and adding the given iterator to it. For convenience it also returns the
          type and component reference of the iterator. =#
        function extendEnvWithForScope(inIterName::String, inIterType::DAE.Type, inEnv::FCore.Graph) ::Tuple{FCore.Graph, DAE.Type, DAE.ComponentRef} 
              local outIterCref::DAE.ComponentRef
              local outIterType::DAE.Type
              local outEnv::FCore.Graph

              local iter_cr::DAE.ComponentRef

              outIterType = Types.expTypetoTypesType(inIterType)
              outEnv = FGraph.addForIterator(inEnv, inIterName, outIterType, DAE.UNBOUND(), SCode.CONST(), SOME(DAE.C_CONST()))
              outIterCref = ComponentReference.makeCrefIdent(inIterName, inIterType, nil)
          (outEnv, outIterType, outIterCref)
        end

         #= This function appends dimensions to a type. This is needed because DAE.VAR
          separates the type and dimensions, while DAE.TYPES_VAR keeps the dimension
          information in the type itself. The dimensions can come from two sources:
          either they are specified in the variable itself as DAE.InstDims, or if the
          variable is declared with unknown dimensions they can be determined from the
          variables binding (i.e. input argument to the function). =#
        function appendDimensions(inType::DAE.Type, inOptBinding::Option{<:Values.Value}, inDims::DAE.InstDims, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, DAE.Type} 
              local outType::DAE.Type
              local outCache::FCore.Cache

              local binding_dims::List{ModelicaInteger}

              binding_dims = ValuesUtil.valueDimensions(Util.getOptionOrDefault(inOptBinding, Values.INTEGER(0)))
              (outCache, outType) = appendDimensions2(inType, inDims, binding_dims, inCache, inEnv)
          (outCache, outType)
        end

         #= Helper function to appendDimensions. Appends dimensions to a type. inDims is
          the declared dimensions of the variable while inBindingDims is the dimensions
          of the variables binding (empty list if it doesn't have a binding). =#
        function appendDimensions2(inType::DAE.Type, inDims::DAE.InstDims, inBindingDims::List{<:ModelicaInteger}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, DAE.Type} 
              local outType::DAE.Type
              local outCache::FCore.Cache

              (outCache, outType) = begin
                  local rest_dims::DAE.InstDims
                  local dim_exp::DAE.Exp
                  local dim_val::Values.Value
                  local dim_int::ModelicaInteger
                  local dim::DAE.Dimension
                  local ty::DAE.Type
                  local bind_dims::List{ModelicaInteger}
                  local sub::DAE.Subscript
                  local cache::FCore.Cache
                @matchcontinue (inType, inDims, inBindingDims, inCache, inEnv) begin
                  (ty,  nil(), _, _, _)  => begin
                    (inCache, ty)
                  end
                  
                  (ty, DAE.DIM_UNKNOWN(__) <| rest_dims, dim_int <| bind_dims, _, _)  => begin
                      dim = Expression.intDimension(dim_int)
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(dim)))
                  end
                  
                  (ty, DAE.DIM_UNKNOWN(__) <| rest_dims, bind_dims, _, _)  => begin
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(0))))
                  end
                  
                  (ty, DAE.DIM_INTEGER(dim_int) <| rest_dims, bind_dims, _, _)  => begin
                      dim = DAE.DIM_INTEGER(dim_int)
                      bind_dims = ListUtil.stripFirst(bind_dims)
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(dim)))
                  end
                  
                  (ty, DAE.DIM_BOOLEAN(__) <| rest_dims, bind_dims, _, _)  => begin
                      dim = DAE.DIM_INTEGER(2)
                      bind_dims = ListUtil.stripFirst(bind_dims)
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(dim)))
                  end
                  
                  (ty, DAE.DIM_ENUM(size = dim_int) <| rest_dims, bind_dims, _, _)  => begin
                      dim = DAE.DIM_INTEGER(dim_int)
                      bind_dims = ListUtil.stripFirst(bind_dims)
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(dim)))
                  end
                  
                  (ty, DAE.DIM_EXP(exp = dim_exp) <| rest_dims, bind_dims, _, _)  => begin
                      (cache, dim_val) = cevalExp(dim_exp, inCache, inEnv)
                      dim_int = ValuesUtil.valueInteger(dim_val)
                      dim = DAE.DIM_INTEGER(dim_int)
                      bind_dims = ListUtil.stripFirst(bind_dims)
                      (cache, ty) = appendDimensions2(ty, rest_dims, bind_dims, inCache, inEnv)
                    (cache, DAE.T_ARRAY(ty, list(dim)))
                  end
                  
                  (_, _ <| _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- CevalFunction.appendDimensions2 failed\\n")
                    fail()
                  end
                end
              end
               #=  If the variable is not an input, set the dimension size to 0 (dynamic size).
               =#
          (outCache, outType)
        end

         #=  [MENV]  Environment manipulation functions (set and get variables).
         =#

         #= This function assigns a variable in the environment a new value. =#
        function assignVariable(inCref::DAE.ComponentRef, inNewValue::Values.Value, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local cr::DAE.ComponentRef
                  local cr_rest::DAE.ComponentRef
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local subs::List{DAE.Subscript}
                  local ty::DAE.Type
                  local ety::DAE.Type
                  local val::Values.Value
                  local var::DAE.Var
                  local inst_status::FCore.Status
                  local id::String
                  local comp_id::String
                   #=  Wildcard, no need to assign anything.
                   =#
                @matchcontinue (inCref, inNewValue, inCache, inEnv) begin
                  (DAE.WILD(__), _, _, _)  => begin
                    (inCache, inEnv)
                  end
                  
                  (DAE.CREF_IDENT(ident = id, subscriptLst =  nil(), identType = ety && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))), _, _, _)  => begin
                      (_, var, _, _, inst_status, env) = Lookup.lookupIdentLocal(inCache, inEnv, id)
                      (cache, env) = assignRecord(ety, inNewValue, inCache, env)
                      var = updateRecordBinding(var, inNewValue)
                      env = FGraph.updateComp(inEnv, var, inst_status, env)
                    (cache, env)
                  end
                  
                  (cr && DAE.CREF_IDENT(subscriptLst =  nil()), _, _, _)  => begin
                      ty = Types.unflattenArrayType(Expression.typeof(ValuesUtil.valueExp(inNewValue)))
                      env = updateVariableBinding(cr, inEnv, ty, inNewValue)
                    (inCache, env)
                  end
                  
                  (DAE.CREF_IDENT(subscriptLst = subs), _, _, _)  => begin
                      cr = ComponentReference.crefStripSubs(inCref)
                      (ty, val) = getVariableTypeAndValue(cr, inEnv)
                      (cache, val) = assignVector(inNewValue, val, subs, inCache, inEnv)
                      env = updateVariableBinding(cr, inEnv, ty, val)
                    (cache, env)
                  end
                  
                  (DAE.CREF_QUAL(ident = id, subscriptLst =  nil(), componentRef = cr_rest), _, _, _)  => begin
                      (_, var, _, _, inst_status, env) = Lookup.lookupIdentLocal(inCache, inEnv, id)
                      (cache, env) = assignVariable(cr_rest, inNewValue, inCache, env)
                      comp_id = ComponentReference.crefFirstIdent(cr_rest)
                      var = updateRecordComponentBinding(var, comp_id, inNewValue)
                      env = FGraph.updateComp(inEnv, var, inst_status, env)
                    (cache, env)
                  end
                end
              end
               #=  A record assignment.
               =#
               #=  If we get a scalar we just update the value.
               =#
               #=  In case of zero-dimensions, update the dimensions; they are all known now
               =#
               #=  If we get a vector we first get the old value and update the relevant
               =#
               #=  part of it, and then update the variables value.
               =#
               #=  A qualified component reference is a record component, so first lookup
               =#
               #=  the records environment, and then assign the variable in that environment.
               =#
          (outCache, outEnv)
        end

         #= This function assign a tuple by calling assignVariable for each tuple
          component. =#
        function assignTuple(inLhsCrefs::List{<:DAE.ComponentRef}, inRhsValues::List{<:Values.Value}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local cr::DAE.ComponentRef
                  local rest_crefs::List{DAE.ComponentRef}
                  local value::Values.Value
                  local rest_vals::List{Values.Value}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inLhsCrefs, inRhsValues, inCache, inEnv) begin
                  ( nil(), _, cache, env)  => begin
                    (cache, env)
                  end
                  
                  (cr <| rest_crefs, value <| rest_vals, cache, env)  => begin
                      (cache, env) = assignVariable(cr, value, cache, env)
                      (cache, env) = assignTuple(rest_crefs, rest_vals, cache, env)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

        function assignRecord(inType::DAE.Type, inValue::Values.Value, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local values::List{Values.Value}
                  local vars::List{DAE.Var}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inType, inValue, inCache, inEnv) begin
                  (DAE.T_COMPLEX(varLst = vars), Values.RECORD(orderd = values), _, _)  => begin
                      (cache, env) = assignRecordComponents(vars, values, inCache, inEnv)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

        function assignRecordComponents(inVars::List{<:DAE.Var}, inValues::List{<:Values.Value}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph} 
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv) = begin
                  local rest_vars::List{DAE.Var}
                  local val::Values.Value
                  local rest_vals::List{Values.Value}
                  local name::String
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inVars, inValues, inCache, inEnv) begin
                  ( nil(),  nil(), _, _)  => begin
                    (inCache, inEnv)
                  end
                  
                  (DAE.TYPES_VAR(name = name, ty = ty) <| rest_vars, val <| rest_vals, _, _)  => begin
                      cr = ComponentReference.makeCrefIdent(name, ty, nil)
                      (cache, env) = assignVariable(cr, val, inCache, inEnv)
                      (cache, env) = assignRecordComponents(rest_vars, rest_vals, cache, env)
                    (cache, env)
                  end
                end
              end
          (outCache, outEnv)
        end

         #= This function assigns a part of a vector by replacing the parts indicated by
          the subscripts in the old value with the new value. =#
        function assignVector(inNewValue::Values.Value, inOldValue::Values.Value, inSubscripts::List{<:DAE.Subscript}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, Values.Value} 
              local outResult::Values.Value
              local outCache::FCore.Cache

              (outCache, outResult) = begin
                  local e::DAE.Exp
                  local index::Values.Value
                  local val::Values.Value
                  local values::List{Values.Value}
                  local values2::List{Values.Value}
                  local old_values::List{Values.Value}
                  local old_values2::List{Values.Value}
                  local indices::List{Values.Value}
                  local dims::List{ModelicaInteger}
                  local i::ModelicaInteger
                  local sub::DAE.Subscript
                  local rest_subs::List{DAE.Subscript}
                  local cache::FCore.Cache
                   #=  No subscripts, we have either reached the end of the recursion or the
                   =#
                   #=  whole vector was assigned.
                   =#
                @matchcontinue (inNewValue, inOldValue, inSubscripts, inCache, inEnv) begin
                  (_, _,  nil(), _, _)  => begin
                    (inCache, inNewValue)
                  end
                  
                  (_, Values.ARRAY(valueLst = values, dimLst = dims), DAE.INDEX(exp = e) <| rest_subs, _, _)  => begin
                      (cache, index) = cevalExp(e, inCache, inEnv)
                      i = ValuesUtil.valueInteger(index)
                      val = listGet(values, i)
                      (cache, val) = assignVector(inNewValue, val, rest_subs, cache, inEnv)
                      values = ListUtil.replaceAt(val, i, values)
                    (cache, Values.ARRAY(values, dims))
                  end
                  
                  (Values.ARRAY(valueLst = values), Values.ARRAY(valueLst = old_values, dimLst = dims), DAE.SLICE(exp = e) <| rest_subs, _, _)  => begin
                      @match (cache, Values.ARRAY(valueLst = (@match _cons(Values.INTEGER(integer = i), _) = indices))) = cevalExp(e, inCache, inEnv)
                      (old_values, old_values2) = ListUtil.splitr(old_values, i - 1)
                      (cache, values2) = assignSlice(values, old_values2, indices, rest_subs, i, cache, inEnv)
                      values = ListUtil.append_reverse(old_values, values2)
                    (cache, Values.ARRAY(values, dims))
                  end
                  
                  (Values.ARRAY(valueLst = values), Values.ARRAY(valueLst = values2, dimLst = dims), DAE.WHOLEDIM(__) <| rest_subs, _, _)  => begin
                      (cache, values) = assignWholeDim(values, values2, rest_subs, inCache, inEnv)
                    (cache, Values.ARRAY(values, dims))
                  end
                  
                  (_, _, sub <| _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      print("- CevalFunction.assignVector failed on: ")
                      print(ExpressionDump.printSubscriptStr(sub) + "\\n")
                    fail()
                  end
                end
              end
               #=  An index subscript. Extract the indicated vector element and update it
               =#
               #=  with assignVector, and then put it back in the list of old values.
               =#
               #=  A slice.
               =#
               #=  Evaluate the slice range to a list of values.
               =#
               #=  Split the list of old values at the first slice index.
               =#
               #=  Update the rest of the old value with assignSlice.
               =#
               #=  Assemble the list of values again.
               =#
               #=  A : (whole dimension).
               =#
          (outCache, outResult)
        end

         #= This function assigns a slice of a vector given a list of new and old values
          and a list of indices. =#
        function assignSlice(inNewValues::List{<:Values.Value}, inOldValues::List{<:Values.Value}, inIndices::List{<:Values.Value}, inSubscripts::List{<:DAE.Subscript}, inIndex::ModelicaInteger, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, List{Values.Value}} 
              local outResult::List{Values.Value}
              local outCache::FCore.Cache

              (outCache, outResult) = begin
                  local v1::Values.Value
                  local v2::Values.Value
                  local index::Values.Value
                  local vl1::List{Values.Value}
                  local vl2::List{Values.Value}
                  local rest_indices::List{Values.Value}
                  local cache::FCore.Cache
                @matchcontinue (inNewValues, inOldValues, inIndices, inSubscripts, inIndex, inCache, inEnv) begin
                  (_, _,  nil(), _, _, _, _)  => begin
                    (inCache, inOldValues)
                  end
                  
                  (vl1, v2 <| vl2, index <| _, _, _, _, _)  => begin
                      @match true = inIndex < ValuesUtil.valueInteger(index)
                      (cache, vl1) = assignSlice(vl1, vl2, inIndices, inSubscripts, inIndex + 1, inCache, inEnv)
                    (cache, _cons(v2, vl1))
                  end
                  
                  (v1 <| vl1, v2 <| vl2, _ <| rest_indices, _, _, _, _)  => begin
                      (cache, v1) = assignVector(v1, v2, inSubscripts, inCache, inEnv)
                      (cache, vl1) = assignSlice(vl1, vl2, rest_indices, inSubscripts, inIndex + 1, inCache, inEnv)
                    (cache, _cons(v1, vl1))
                  end
                end
              end
               #=  Skip indices that are smaller than the next index in the slice.
               =#
          (outCache, outResult)
        end

         #= This function assigns a whole dimension of a vector. =#
        function assignWholeDim(inNewValues::List{<:Values.Value}, inOldValues::List{<:Values.Value}, inSubscripts::List{<:DAE.Subscript}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{FCore.Cache, List{Values.Value}} 
              local outResult::List{Values.Value}
              local outCache::FCore.Cache

              (outCache, outResult) = begin
                  local v1::Values.Value
                  local v2::Values.Value
                  local vl1::List{Values.Value}
                  local vl2::List{Values.Value}
                  local cache::FCore.Cache
                @match (inNewValues, inOldValues, inSubscripts, inCache, inEnv) begin
                  ( nil(), _, _, _, _)  => begin
                    (inCache, nil)
                  end
                  
                  (v1 <| vl1, v2 <| vl2, _, _, _)  => begin
                      (cache, v1) = assignVector(v1, v2, inSubscripts, inCache, inEnv)
                      (cache, vl1) = assignWholeDim(vl1, vl2, inSubscripts, inCache, inEnv)
                    (cache, _cons(v1, vl1))
                  end
                end
              end
          (outCache, outResult)
        end

         #= This function updates a variables binding in the environment. =#
        function updateVariableBinding(inVariableCref::DAE.ComponentRef, inEnv::FCore.Graph, inType::DAE.Type, inNewValue::Values.Value) ::FCore.Graph 
              local outEnv::FCore.Graph

              local var_name::String
              local var::DAE.Var

              var_name = ComponentReference.crefStr(inVariableCref)
              var = makeFunctionVariable(var_name, inType, DAE.VALBOUND(inNewValue, DAE.BINDING_FROM_DEFAULT_VALUE()))
              outEnv = FGraph.updateComp(inEnv, var, FCore.VAR_TYPED(), FGraph.empty())
          outEnv
        end

         #= Updates the binding of a record variable. =#
        function updateRecordBinding(inVar::DAE.Var, inValue::Values.Value) ::DAE.Var 
              local outVar::DAE.Var

              local name::DAE.Ident
              local attr::DAE.Attributes
              local ty::DAE.Type
              local c::Option{DAE.Const}

              @match DAE.TYPES_VAR(name, attr, ty, _, c) = inVar
              outVar = DAE.TYPES_VAR(name, attr, ty, DAE.VALBOUND(inValue, DAE.BINDING_FROM_DEFAULT_VALUE()), c)
          outVar
        end

         #= Updates the binding of a record component. =#
        function updateRecordComponentBinding(inVar::DAE.Var, inComponentId::String, inValue::Values.Value) ::DAE.Var 
              local outVar::DAE.Var

              local name::DAE.Ident
              local attr::DAE.Attributes
              local ty::DAE.Type
              local binding::DAE.Binding
              local c::Option{DAE.Const}
              local val::Values.Value

              @match DAE.TYPES_VAR(name, attr, ty, binding, c) = inVar
              val = getBindingOrDefault(binding, ty)
              val = updateRecordComponentValue(inComponentId, inValue, val)
              binding = DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE())
              outVar = DAE.TYPES_VAR(name, attr, ty, binding, c)
          outVar
        end

        function updateRecordComponentValue(inComponentId::String, inComponentValue::Values.Value, inRecordValue::Values.Value) ::Values.Value 
              local outRecordValue::Values.Value

              local name::Absyn.Path
              local vals::List{Values.Value}
              local comps::List{String}
              local pos::ModelicaInteger

              @match Values.RECORD(name, vals, comps, -1) = inRecordValue
              pos = ListUtil.position(inComponentId, comps)
              vals = ListUtil.replaceAt(inComponentValue, pos, vals)
              outRecordValue = Values.RECORD(name, vals, comps, -1)
          outRecordValue
        end

         #= This function looks a variable up in the environment, and returns it's type
          and binding. =#
        function getVariableTypeAndBinding(inCref::DAE.ComponentRef, inEnv::FCore.Graph) ::Tuple{DAE.Type, DAE.Binding} 
              local outBinding::DAE.Binding
              local outType::DAE.Type

              (_, _, outType, outBinding, _, _, _, _, _) = Lookup.lookupVar(FCoreUtil.emptyCache(), inEnv, inCref)
          (outType, outBinding)
        end

         #= This function looks a variable up in the environment, and returns it's type
          and value. If it doesn't have a value, then a default value will be returned. =#
        function getVariableTypeAndValue(inCref::DAE.ComponentRef, inEnv::FCore.Graph) ::Tuple{DAE.Type, Values.Value} 
              local outValue::Values.Value
              local outType::DAE.Type

              local binding::DAE.Binding

              (outType, binding) = getVariableTypeAndBinding(inCref, inEnv)
              outValue = getBindingOrDefault(binding, outType)
          (outType, outValue)
        end

         #= Returns the value in a binding, or a default value if binding isn't a value
          binding. =#
        function getBindingOrDefault(inBinding::DAE.Binding, inType::DAE.Type) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local val::Values.Value
                @match (inBinding, inType) begin
                  (DAE.VALBOUND(valBound = val), _)  => begin
                    val
                  end
                  
                  _  => begin
                      generateDefaultBinding(inType)
                  end
                end
              end
          outValue
        end

         #= This function generates a default value for a type. This is needed when
          assigning parts of an array, since we can only assign parts of an already
          existing array. The value will be the types equivalence to zero. =#
        function generateDefaultBinding(inType::DAE.Type) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local dim::DAE.Dimension
                  local int_dim::ModelicaInteger
                  local dims::List{ModelicaInteger}
                  local ty::DAE.Type
                  local values::List{Values.Value}
                  local value::Values.Value
                  local path::Absyn.Path
                  local vars::List{DAE.Var}
                  local var_names::List{String}
                @matchcontinue inType begin
                  DAE.T_INTEGER(__)  => begin
                    Values.INTEGER(0)
                  end
                  
                  DAE.T_REAL(__)  => begin
                    Values.REAL(0.0)
                  end
                  
                  DAE.T_STRING(__)  => begin
                    Values.STRING("")
                  end
                  
                  DAE.T_BOOL(__)  => begin
                    Values.BOOL(false)
                  end
                  
                  DAE.T_ENUMERATION(__)  => begin
                    Values.ENUM_LITERAL(Absyn.IDENT(""), 0)
                  end
                  
                  DAE.T_ARRAY(dims = dim <|  nil(), ty = ty)  => begin
                      int_dim = Expression.dimensionSize(dim)
                      value = generateDefaultBinding(ty)
                      values = ListUtil.fill(value, int_dim)
                      dims = ValuesUtil.valueDimensions(value)
                    Values.ARRAY(values, _cons(int_dim, dims))
                  end
                  
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = path), varLst = vars)  => begin
                      (values, var_names) = ListUtil.map_2(vars, getRecordVarBindingAndName)
                    Values.RECORD(path, values, var_names, -1)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- CevalFunction.generateDefaultBinding failed\\n")
                      fail()
                  end
                end
              end
          outValue
        end

        function getRecordVarBindingAndName(inVar::DAE.Var) ::Tuple{Values.Value, String} 
              local outName::String
              local outBinding::Values.Value

              (outBinding, outName) = begin
                  local name::String
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local val::Values.Value
                @matchcontinue inVar begin
                  DAE.TYPES_VAR(name = name, ty = ty, binding = binding)  => begin
                      val = getBindingOrDefault(binding, ty)
                    (val, name)
                  end
                  
                  DAE.TYPES_VAR(name = name)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- CevalFunction.getRecordVarBindingAndName failed on variable " + name + "\\n")
                    fail()
                  end
                end
              end
          (outBinding, outName)
        end

         #= This function fetches one return value for the function, given an output
          variable and an environment. =#
        function getFunctionReturnValue(inOutputVar::DAE.Element, inEnv::FCore.Graph) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local val::Values.Value
                @match (inOutputVar, inEnv) begin
                  (DAE.VAR(componentRef = cr, ty = ty), _)  => begin
                      val = getVariableValue(cr, ty, inEnv)
                    val
                  end
                end
              end
          outValue
        end

         #= Helper function to getFunctionReturnValue. Fetches a variables value from the
          environment. =#
        function getVariableValue(inCref::DAE.ComponentRef, inType::DAE.Type, inEnv::FCore.Graph) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local val::Values.Value
                  local p::Absyn.Path
                   #=  A record doesn't have a value, but an environment with it's components.
                   =#
                   #=  So we need to assemble the records value.
                   =#
                @matchcontinue (inCref, inType, inEnv) begin
                  (_, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__)), _)  => begin
                      p = ComponentReference.crefToPath(inCref)
                      val = getRecordValue(p, inType, inEnv)
                    val
                  end
                  
                  _  => begin
                        (_, val) = getVariableTypeAndValue(inCref, inEnv)
                      val
                  end
                end
              end
               #=  All other variables we can just look up in the environment.
               =#
          outValue
        end

         #= Looks up the value of a record by looking up the record components in the
          records environment and assembling a record value. =#
        function getRecordValue(inRecordName::Absyn.Path, inType::DAE.Type, inEnv::FCore.Graph) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local vars::List{DAE.Var}
                  local vals::List{Values.Value}
                  local var_names::List{String}
                  local id::String
                  local p::Absyn.Path
                  local env::FCore.Graph
                @match (inRecordName, inType, inEnv) begin
                  (Absyn.IDENT(name = id), DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = p), varLst = vars), _)  => begin
                      (_, _, _, _, _, env) = Lookup.lookupIdentLocal(FCoreUtil.emptyCache(), inEnv, id)
                      vals = ListUtil.map1(vars, getRecordComponentValue, env)
                      var_names = ListUtil.map(vars, Types.getVarName)
                    Values.RECORD(p, vals, var_names, -1)
                  end
                end
              end
          outValue
        end

         #= Looks up the value for a record component. =#
        function getRecordComponentValue(inVars::DAE.Var, inEnv::FCore.Graph) ::Values.Value 
              local outValues::Values.Value

              outValues = begin
                  local val::Values.Value
                  local id::String
                  local ty::DAE.Type
                  local binding::DAE.Binding
                   #=  The component is a record itself.
                   =#
                @match (inVars, inEnv) begin
                  (DAE.TYPES_VAR(name = id, ty = ty && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))), _)  => begin
                      val = getRecordValue(Absyn.IDENT(id), ty, inEnv)
                    val
                  end
                  
                  (DAE.TYPES_VAR(name = id, ty = ty), _)  => begin
                      @match (_, DAE.TYPES_VAR(binding = binding), _, _, _, _) = Lookup.lookupIdentLocal(FCoreUtil.emptyCache(), inEnv, id)
                      val = getBindingOrDefault(binding, ty)
                    val
                  end
                end
              end
               #=  A non-record variable.
               =#
          outValues
        end

         #= This function takes a list of return values, and return either a NORETCALL, a
          single value or a tuple with the values depending on how many return variables
          there are. =#
        function boxReturnValue(inReturnValues::List{<:Values.Value}) ::Values.Value 
              local outValue::Values.Value

              outValue = begin
                  local val::Values.Value
                @match inReturnValues begin
                   nil()  => begin
                    Values.NORETCALL()
                  end
                  
                  val <|  nil()  => begin
                    val
                  end
                  
                  _ <| _  => begin
                    Values.TUPLE(inReturnValues)
                  end
                end
              end
          outValue
        end

         #=  [DEPS]  Function variable dependency handling.
         =#

         #= A functions variables might depend on each other, for example by defining
          dimensions that depend on the size of another variable. This function sorts
          the list of variables so that any dependencies to a variable will be before
          the variable in resulting list. =#
        function sortFunctionVarsByDependency(inFuncVars::List{<:FunctionVar}, inSource::DAE.ElementSource) ::List{FunctionVar} 
              local outFuncVars::List{FunctionVar}

              local cycles::List{Tuple{FunctionVar, List{FunctionVar}}}

              (outFuncVars, cycles) = Graph.topologicalSort(Graph.buildGraph(inFuncVars, getElementDependencies, inFuncVars), isElementEqual)
              checkCyclicalComponents(cycles, inSource)
          outFuncVars
        end

         #= Returns the dependencies given an element. =#
        function getElementDependencies(inElement::FunctionVar, inAllElements::List{<:FunctionVar}) ::List{FunctionVar} 
              local outDependencies::List{FunctionVar}

              outDependencies = begin
                  local bind_exp::DAE.Exp
                  local deps::List{FunctionVar}
                  local dims::List{DAE.Dimension}
                  local arg::Arg
                @matchcontinue (inElement, inAllElements) begin
                  ((DAE.VAR(binding = SOME(bind_exp), dims = dims), _), _)  => begin
                      @match (_, (@match (_, deps, _) = arg)) = Expression.traverseExpBidir(bind_exp, getElementDependenciesTraverserEnter, getElementDependenciesTraverserExit, (inAllElements, nil, nil))
                      (_, (_, deps, _)) = ListUtil.mapFold(dims, getElementDependenciesFromDims, arg)
                    deps
                  end
                  
                  ((DAE.VAR(dims = dims), _), _)  => begin
                      (_, (_, deps, _)) = ListUtil.mapFold(dims, getElementDependenciesFromDims, (inAllElements, nil, nil))
                    deps
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outDependencies
        end

         #= Helper function to getElementDependencies that gets the dependencies from the
          dimensions of a variable. =#
        function getElementDependenciesFromDims(inDimension::DAE.Dimension, inArg::Arg) ::Tuple{DAE.Dimension, Arg} 
              local outArg::Arg
              local outDimension::DAE.Dimension

              (outDimension, outArg) = begin
                  local arg::Arg
                  local dim_exp::DAE.Exp
                @matchcontinue (inDimension, inArg) begin
                  (_, _)  => begin
                      dim_exp = Expression.dimensionSizeExp(inDimension)
                      (_, arg) = Expression.traverseExpBidir(dim_exp, getElementDependenciesTraverserEnter, getElementDependenciesTraverserExit, inArg)
                    (inDimension, arg)
                  end
                  
                  _  => begin
                      (inDimension, inArg)
                  end
                end
              end
          (outDimension, outArg)
        end

         #= Traverse function used by getElementDependencies to collect all dependencies
          for an element. The extra arguments are a list of all elements, a list of
          accumulated depencies and a list of iterators from enclosing for-loops. =#
        function getElementDependenciesTraverserEnter(inExp::DAE.Exp, inArg::Arg) ::Tuple{DAE.Exp, Arg} 
              local outArg::Arg
              local outExp::DAE.Exp

              (outExp, outArg) = begin
                  local exp::DAE.Exp
                  local cref::DAE.ComponentRef
                  local all_el::List{FunctionVar}
                  local accum_el::List{FunctionVar}
                  local e::FunctionVar
                  local iter::DAE.Ident
                  local iters::List{DAE.Ident}
                  local riters::DAE.ReductionIterators
                   #=  Check if the crefs matches any of the iterators that might shadow a
                   =#
                   #=  function variable, and don't add it as a dependency if that's the case.
                   =#
                @matchcontinue (inExp, inArg) begin
                  (exp && DAE.CREF(componentRef = DAE.CREF_IDENT(ident = iter)), (all_el, accum_el, iters && _ <| _))  => begin
                      @match true = ListUtil.isMemberOnTrue(iter, iters, stringEqual)
                    (exp, (all_el, accum_el, iters))
                  end
                  
                  (exp && DAE.CREF(componentRef = cref), (all_el, accum_el, iters))  => begin
                      @match (all_el, SOME(e)) = ListUtil.deleteMemberOnTrue(cref, all_el, isElementNamed)
                    (exp, (all_el, _cons(e, accum_el), iters))
                  end
                  
                  (exp && DAE.REDUCTION(iterators = riters), (all_el, accum_el, iters))  => begin
                      iters = listAppend(ListUtil.map(riters, Expression.reductionIterName), iters)
                    (exp, (all_el, accum_el, iters))
                  end
                  
                  _  => begin
                      (inExp, inArg)
                  end
                end
              end
               #=  Otherwise, try to delete the cref from the list of all elements. If that
               =#
               #=  succeeds, add it to the list of dependencies. Since we have deleted the
               =#
               #=  element from the list of all variables this ensures that the dependency
               =#
               #=  list only contains unique elements.
               =#
               #=  If we encounter a reduction, add the iterator to the iterator list so
               =#
               #=  that we know which iterators shadow function variables.
               =#
          (outExp, outArg)
        end

         #= Exit traversal function used by getElementDependencies. =#
        function getElementDependenciesTraverserExit(inExp::DAE.Exp, inArg::Arg) ::Tuple{DAE.Exp, Arg} 
              local outArg::Arg
              local outExp::DAE.Exp

              (outExp, outArg) = begin
                  local exp::DAE.Exp
                  local all_el::List{FunctionVar}
                  local accum_el::List{FunctionVar}
                  local iters::List{DAE.Ident}
                  local riters::DAE.ReductionIterators
                   #=  If we encounter a reduction, make sure that its iterator matches the
                   =#
                   #=  first iterator in the iterator list, and if so remove it from the list.
                   =#
                @match (inExp, inArg) begin
                  (exp && DAE.REDUCTION(iterators = riters), (all_el, accum_el, iters))  => begin
                      iters = compareIterators(listReverse(riters), iters)
                    (exp, (all_el, accum_el, iters))
                  end
                  
                  _  => begin
                      (inExp, inArg)
                  end
                end
              end
          (outExp, outArg)
        end

        function compareIterators(inRiters::DAE.ReductionIterators, inIters::List{<:String}) ::List{String} 
              local outIters::List{String}

              outIters = begin
                  local id1::String
                  local id2::String
                  local riters::DAE.ReductionIterators
                  local iters::List{String}
                @matchcontinue (inRiters, inIters) begin
                  (DAE.REDUCTIONITER(id = id1) <| riters, id2 <| iters)  => begin
                      @match true = stringEqual(id1, id2)
                    compareIterators(riters, iters)
                  end
                  
                  ( nil(), _)  => begin
                    inIters
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Different iterators in CevalFunction.compareIterators."))
                      fail()
                  end
                end
              end
               #=  This should never happen, print an error if it does.
               =#
          outIters
        end

         #= Checks if a function parameter has the given name. =#
        function isElementNamed(inName::DAE.ComponentRef, inElement::FunctionVar) ::Bool 
              local isNamed::Bool

              local name::DAE.ComponentRef

              @match (DAE.VAR(componentRef = name), _) = inElement
              isNamed = ComponentReference.crefEqualWithoutSubs(name, inName)
          isNamed
        end

         #= Checks if two function parameters are equal, i.e. have the same name. =#
        function isElementEqual(inElement1::FunctionVar, inElement2::FunctionVar) ::Bool 
              local isEqual::Bool

              local cr1::DAE.ComponentRef
              local cr2::DAE.ComponentRef

              @match (DAE.VAR(componentRef = cr1), _) = inElement1
              @match (DAE.VAR(componentRef = cr2), _) = inElement2
              isEqual = ComponentReference.crefEqualWithoutSubs(cr1, cr2)
          isEqual
        end

         #= Checks the return value from Graph.topologicalSort. If the list of cycles is
          not empty, print an error message and fail, since it's not allowed for
          constants or parameters to have cyclic dependencies. =#
        function checkCyclicalComponents(inCycles::List{<:Tuple{<:FunctionVar, List{<:FunctionVar}}}, inSource::DAE.ElementSource)  
              _ = begin
                  local cycles::List{List{FunctionVar}}
                  local elements::List{List{DAE.Element}}
                  local crefs::List{List{DAE.ComponentRef}}
                  local names::List{List{String}}
                  local cycles_strs::List{String}
                  local cycles_str::String
                  local scope_str::String
                  local info::SourceInfo
                @match (inCycles, inSource) begin
                  ( nil(), _)  => begin
                    ()
                  end
                  
                  _  => begin
                        cycles = Graph.findCycles(inCycles, isElementEqual)
                        elements = ListUtil.mapList(cycles, Util.tuple21)
                        crefs = ListUtil.mapList(elements, DAEUtil.varCref)
                        names = ListUtil.mapList(crefs, ComponentReference.printComponentRefStr)
                        cycles_strs = ListUtil.map1(names, stringDelimitList, ",")
                        cycles_str = stringDelimitList(cycles_strs, "}, {")
                        cycles_str = "{" + cycles_str + "}"
                        scope_str = ""
                        info = ElementSource.getElementSourceFileInfo(inSource)
                        Error.addSourceMessage(Error.CIRCULAR_COMPONENTS, list(scope_str, cycles_str), info)
                      fail()
                  end
                end
              end
        end

         #=  [EOPT]  Expression optimization functions.
         =#

         #= This function optimizes expressions in a function. So far this is only used
          to transform ASUB expressions to CREFs so that this doesn't need to be done
          while evaluating the function. But it's possible that more forms of
          optimization can be done too. =#
        function optimizeExpTraverser(inExp::DAE.Exp, inEnv::FCore.Graph) ::Tuple{DAE.Exp, FCore.Graph} 
              local outEnv::FCore.Graph
              local outExp::DAE.Exp

              (outExp, outEnv) = begin
                  local cref::DAE.ComponentRef
                  local ety::DAE.Type
                  local sub_exps::List{DAE.Exp}
                  local subs::List{DAE.Subscript}
                  local env::FCore.Graph
                  local exp::DAE.Exp
                @match (inExp, inEnv) begin
                  (DAE.ASUB(exp = DAE.CREF(componentRef = cref, ty = ety), sub = sub_exps), env)  => begin
                      subs = ListUtil.map(sub_exps, Expression.makeIndexSubscript)
                      cref = ComponentReference.subscriptCref(cref, subs)
                      exp = Expression.makeCrefExp(cref, ety)
                    (exp, env)
                  end
                  
                  (DAE.TSUB(exp = DAE.TUPLE(exp <| _), ix = 1), env)  => begin
                    (exp, env)
                  end
                  
                  _  => begin
                      (inExp, inEnv)
                  end
                end
              end
          (outExp, outEnv)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
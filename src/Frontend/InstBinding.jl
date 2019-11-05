  module InstBinding


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

        import ClassInf

        import DAE

        import FCore

        import FGraph

        import InnerOuter

        import Mod

        import Prefix

        import SCode

        import Values

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

        InstDims = List

        import Ceval

        import ComponentReference

        import ElementSource

        import Error

        import Expression

        import ExpressionDump

        import ExpressionSimplify

        import InstUtil

        import ListUtil

        import Flags

        import Debug

        import DAEUtil

        import PrefixUtil
        import SCodeUtil

        import Types

        import InstSection

        import ValuesUtil

         const stateSelectType = DAE.T_ENUMERATION(NONE(), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), list(DAE.TYPES_VAR("never", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(1), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("avoid", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(2), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("default", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(3), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("prefer", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(4), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("always", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(5), Absyn.IDENT(""), list("never", "avoid", "default", "prefer", "always"), nil, nil), DAE.UNBOUND(), NONE())), nil)::DAE.Type

         const uncertaintyType = DAE.T_ENUMERATION(NONE(), Absyn.IDENT(""), list("given", "sought", "refine"), list(DAE.TYPES_VAR("given", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(1), Absyn.IDENT(""), list("given", "sought", "refine"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("sought", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(2), Absyn.IDENT(""), list("given", "sought", "refine"), nil, nil), DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("refine", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(3), Absyn.IDENT(""), list("given", "sought", "refine"), nil, nil), DAE.UNBOUND(), NONE())), nil)::DAE.Type

         const distributionType = DAE.T_COMPLEX(ClassInf.RECORD(Absyn.IDENT("Distribution")), list(DAE.TYPES_VAR("name", DAE.ATTR(DAE.NON_CONNECTOR(), SCode.NON_PARALLEL(), SCode.PARAM(), Absyn.BIDIR(), Absyn.NOT_INNER_OUTER(), SCode.PUBLIC()), DAE.T_STRING_DEFAULT, DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("params", DAE.ATTR(DAE.NON_CONNECTOR(), SCode.NON_PARALLEL(), SCode.PARAM(), Absyn.BIDIR(), Absyn.NOT_INNER_OUTER(), SCode.PUBLIC()), DAE.T_ARRAY_REAL_NODIM, DAE.UNBOUND(), NONE()), DAE.TYPES_VAR("paramNames", DAE.ATTR(DAE.NON_CONNECTOR(), SCode.NON_PARALLEL(), SCode.PARAM(), Absyn.BIDIR(), Absyn.NOT_INNER_OUTER(), SCode.PUBLIC()), DAE.T_ARRAY_STRING_NODIM, DAE.UNBOUND(), NONE())), NONE())::DAE.Type
         #=  binding
         =#
         #=  binding
         =#
         #=  binding
         =#

         #= This function investigates a modification and extracts the
          <...> modification. E.g. Real x(<...>=1+3) => 1+3
          It also handles the case Integer T0[2](final <...>={5,6})={9,10} becomes
          Integer T0[1](<...>=5); Integer T0[2](<...>=6);

           If no modifier is given it also investigates the type to check for binding there.
           I.e. type A = Real(start=1); A a; will set the start attribute since it's found in the type.

          Arg 1 is the modification
          Arg 2 are the type variables.
          Arg 3 is the expected type that the modification should have
          Arg 4 is the index list for the element: for T0{1,2} is {1,2} =#
        function instBinding(inMod::DAE.Mod, inVarLst::List{<:DAE.Var}, inType::DAE.Type, inIntegerLst::List{<:ModelicaInteger}, inString::String, useConstValue::Bool #= if true use constant value present in TYPED (if present) =#) ::Option{DAE.Exp}
              local outExpExpOption::Option{DAE.Exp}

              outExpExpOption = begin
                  local mod2::DAE.Mod
                  local mod::DAE.Mod
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local ty2::DAE.Type
                  local ty_1::DAE.Type
                  local expected_type::DAE.Type
                  local etype::DAE.Type
                  local bind_name::String
                  local result::Option{DAE.Exp}
                  local index_list::List{ModelicaInteger}
                  local binding::DAE.Binding
                  local name::Ident
                  local optVal::Option{Values.Value}
                  local varLst::List{DAE.Var}
                @matchcontinue (inMod, inVarLst, inType, inIntegerLst, inString) begin
                  (mod, _, expected_type,  nil(), bind_name)  => begin
                      mod2 = Mod.lookupCompModification(mod, bind_name)
                      @match SOME(DAE.TYPED(e, optVal, DAE.PROP(ty2, _), _)) = Mod.modEquation(mod2)
                      (e_1, _) = Types.matchType(e, ty2, expected_type, true)
                      e_1 = InstUtil.checkUseConstValue(useConstValue, e_1, optVal)
                    SOME(e_1)
                  end

                  (mod, _, etype, index_list, bind_name)  => begin
                      mod2 = Mod.lookupCompModification(mod, bind_name)
                      result = instBinding2(mod2, etype, index_list, bind_name, useConstValue)
                    result
                  end

                  (mod, _, _,  nil(), bind_name)  => begin
                      @shouldFail _ = Mod.lookupCompModification(mod, bind_name)
                    NONE()
                  end

                  (_, DAE.TYPES_VAR(name = name, binding = binding) <| _, _, _, bind_name)  => begin
                      @match true = stringEq(name, bind_name)
                    DAEUtil.bindingExp(binding)
                  end

                  (mod, _ <| varLst, etype, index_list, bind_name)  => begin
                    instBinding(mod, varLst, etype, index_list, bind_name, useConstValue)
                  end

                  (_,  nil(), _, _, _)  => begin
                    NONE()
                  end
                end
              end
               #= /* No subscript/index */ =#
               #= /* Have subscript/index */ =#
               #= /* No modifier for this name. */ =#
          outExpExpOption
        end

         #= This function investigates a modification and extracts the <...>
          modification if the modification is in array of components.
          Help-function to instBinding =#
        function instBinding2(inMod::DAE.Mod, inType::DAE.Type, inIntegerLst::List{<:ModelicaInteger}, inString::String, useConstValue::Bool #= if true, use constant value in TYPED (if present) =#) ::Option{DAE.Exp}
              local outExpExpOption::Option{DAE.Exp}

              outExpExpOption = begin
                  local mod2::DAE.Mod
                  local mod::DAE.Mod
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local ty2::DAE.Type
                  local ty_1::DAE.Type
                  local etype::DAE.Type
                  local index::ModelicaInteger
                  local bind_name::String
                  local result::Option{DAE.Exp}
                  local res::List{ModelicaInteger}
                  local optVal::Option{Values.Value}
                @match (inMod, inType, inIntegerLst, inString) begin
                  (mod, etype, index <|  nil(), _)  => begin
                      mod2 = Mod.lookupIdxModification(mod, DAE.ICONST(index))
                      @match SOME(DAE.TYPED(e, optVal, DAE.PROP(ty2, _), _)) = Mod.modEquation(mod2)
                      (e_1, _) = Types.matchType(e, ty2, etype, true)
                      e_1 = InstUtil.checkUseConstValue(useConstValue, e_1, optVal)
                    SOME(e_1)
                  end

                  (mod, etype, index <| res, bind_name)  => begin
                      result = begin
                        @matchcontinue () begin
                          ()  => begin
                              mod2 = Mod.lookupIdxModification(mod, DAE.ICONST(index))
                              result = instBinding2(mod2, etype, res, bind_name, useConstValue)
                            result
                          end

                          _  => begin
                              NONE()
                          end
                        end
                      end
                    result
                  end
                end
              end
               #= /* Only one element in the index-list */ =#
               #= /* Several elements in the index-list */ =#
          outExpExpOption
        end

         #= This function investigates a modification and extracts the
          start modification. E.g. Real x(start=1+3) => 1+3
          It also handles the case Integer T0{2}(final start={5,6})={9,10} becomes
          Integer T0{1}(start=5); Integer T0{2}(start=6);

          Arg 1 is the start modification
          Arg 2 is the expected type that the modification should have
          Arg 3 is variability of the element =#
        function instStartBindingExp(inMod::DAE.Mod, inExpectedType::DAE.Type, inVariability::SCode.Variability) ::DAE.StartValue
              local outStartValue::DAE.StartValue

              if SCodeUtil.isConstant(inVariability)
                outStartValue = NONE()
              else
                outStartValue = instBinding(inMod, nil, Types.arrayElementType(inExpectedType), nil, "start", false)
              end
               #=  When instantiating arrays, the array type is passed.
               =#
               #=  But binding is performed on the element type.
               =#
          outStartValue
        end

         #= This function investigates if the start value comes from the modification or the type =#
        function instStartOrigin(inMod::DAE.Mod, inVarLst::List{<:DAE.Var}, inString::String) ::Option{DAE.Exp}
              local outExpExpOption::Option{DAE.Exp}

              outExpExpOption = begin
                  local mod2::DAE.Mod
                  local mod::DAE.Mod
                  local bind_name::String
                  local binding::DAE.Binding
                  local name::Ident
                  local varLst::List{DAE.Var}
                @matchcontinue (inMod, inVarLst, inString) begin
                  (mod, _, bind_name)  => begin
                      mod2 = Mod.lookupCompModification(mod, bind_name)
                      @match SOME(_) = Mod.modEquation(mod2)
                    SOME(DAE.SCONST("binding"))
                  end

                  (_, DAE.TYPES_VAR(name = name) <| _, bind_name)  => begin
                      @match true = stringEq(name, bind_name)
                    SOME(DAE.SCONST("type"))
                  end

                  (mod, _ <| varLst, bind_name)  => begin
                    instStartOrigin(mod, varLst, bind_name)
                  end

                  (_,  nil(), _)  => begin
                    NONE()
                  end
                end
              end
          outExpExpOption
        end

         #= this function extracts the attributes from the modification
          It returns a DAE.VariableAttributes option because
          somtimes a varible does not contain the variable-attr. =#
        function instDaeVariableAttributes(inCache::FCore.Cache, inEnv::FCore.Graph, inMod::DAE.Mod, inType::DAE.Type, inIntegerLst::List{<:ModelicaInteger}) ::Tuple{FCore.Cache, Option{DAE.VariableAttributes}}
              local outDAEVariableAttributesOption::Option{DAE.VariableAttributes}
              local outCache::FCore.Cache

              (outCache, outDAEVariableAttributesOption) = begin
                  local quantity_str::Option{DAE.Exp}
                  local unit_str::Option{DAE.Exp}
                  local displayunit_str::Option{DAE.Exp}
                  local nominal_val::Option{DAE.Exp}
                  local fixed_val::Option{DAE.Exp}
                  local exp_bind_select::Option{DAE.Exp}
                  local exp_bind_uncertainty::Option{DAE.Exp}
                  local exp_bind_min::Option{DAE.Exp}
                  local exp_bind_max::Option{DAE.Exp}
                  local exp_bind_start::Option{DAE.Exp}
                  local min_val::Option{DAE.Exp}
                  local max_val::Option{DAE.Exp}
                  local start_val::Option{DAE.Exp}
                  local startOrigin::Option{DAE.Exp}
                  local stateSelect_value::Option{DAE.StateSelect}
                  local uncertainty_value::Option{DAE.Uncertainty}
                  local distribution_value::Option{DAE.Distribution}
                  local env::FCore.Graph
                  local mod::DAE.Mod
                  local index_list::List{ModelicaInteger}
                  local enumtype::DAE.Type
                  local cache::FCore.Cache
                  local tp::DAE.Type
                  local varLst::List{DAE.Var}
                   #=  Real
                   =#
                @matchcontinue (inCache, inEnv, inMod, inType, inIntegerLst) begin
                  (cache, _, mod, DAE.T_REAL(varLst = varLst), index_list)  => begin
                      quantity_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "quantity", false)
                      unit_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "unit", false)
                      displayunit_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "displayUnit", false)
                      min_val = instBinding(mod, varLst, DAE.T_REAL_DEFAULT, index_list, "min", false)
                      max_val = instBinding(mod, varLst, DAE.T_REAL_DEFAULT, index_list, "max", false)
                      start_val = instBinding(mod, varLst, DAE.T_REAL_DEFAULT, index_list, "start", false)
                      fixed_val = instBinding(mod, varLst, DAE.T_BOOL_DEFAULT, index_list, "fixed", true)
                      nominal_val = instBinding(mod, varLst, DAE.T_REAL_DEFAULT, index_list, "nominal", false)
                      exp_bind_select = instEnumerationBinding(mod, varLst, index_list, "stateSelect", stateSelectType, true)
                      stateSelect_value = InstUtil.getStateSelectFromExpOption(exp_bind_select)
                      exp_bind_uncertainty = instEnumerationBinding(mod, varLst, index_list, "uncertain", uncertaintyType, true)
                      uncertainty_value = getUncertainFromExpOption(exp_bind_uncertainty)
                      distribution_value = instDistributionBinding(mod, varLst, index_list, "distribution", false)
                      startOrigin = instStartOrigin(mod, varLst, "start")
                    (cache, SOME(DAE.VAR_ATTR_REAL(quantity_str, unit_str, displayunit_str, min_val, max_val, start_val, fixed_val, nominal_val, stateSelect_value, uncertainty_value, distribution_value, NONE(), NONE(), NONE(), startOrigin)))
                  end

                  (cache, _, mod, DAE.T_INTEGER(varLst = varLst), index_list)  => begin
                      quantity_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "quantity", false)
                      min_val = instBinding(mod, varLst, DAE.T_INTEGER_DEFAULT, index_list, "min", false)
                      max_val = instBinding(mod, varLst, DAE.T_INTEGER_DEFAULT, index_list, "max", false)
                      start_val = instBinding(mod, varLst, DAE.T_INTEGER_DEFAULT, index_list, "start", false)
                      fixed_val = instBinding(mod, varLst, DAE.T_BOOL_DEFAULT, index_list, "fixed", true)
                      exp_bind_uncertainty = instEnumerationBinding(mod, varLst, index_list, "uncertain", uncertaintyType, true)
                      uncertainty_value = getUncertainFromExpOption(exp_bind_uncertainty)
                      distribution_value = instDistributionBinding(mod, varLst, index_list, "distribution", false)
                      startOrigin = instStartOrigin(mod, varLst, "start")
                    (cache, SOME(DAE.VAR_ATTR_INT(quantity_str, min_val, max_val, start_val, fixed_val, uncertainty_value, distribution_value, NONE(), NONE(), NONE(), startOrigin)))
                  end

                  (cache, _, mod, tp && DAE.T_BOOL(varLst = varLst), index_list)  => begin
                      quantity_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "quantity", false)
                      start_val = instBinding(mod, varLst, tp, index_list, "start", false)
                      fixed_val = instBinding(mod, varLst, tp, index_list, "fixed", true)
                      startOrigin = instStartOrigin(mod, varLst, "start")
                    (cache, SOME(DAE.VAR_ATTR_BOOL(quantity_str, start_val, fixed_val, NONE(), NONE(), NONE(), startOrigin)))
                  end

                  (cache, _, _, DAE.T_CLOCK(__), _)  => begin
                    (cache, SOME(DAE.VAR_ATTR_CLOCK(NONE(), NONE())))
                  end

                  (cache, _, mod, tp && DAE.T_STRING(varLst = varLst), index_list)  => begin
                      quantity_str = instBinding(mod, varLst, tp, index_list, "quantity", false)
                      start_val = instBinding(mod, varLst, tp, index_list, "start", false)
                      fixed_val = instBinding(mod, varLst, DAE.T_BOOL_DEFAULT, index_list, "fixed", true)
                      startOrigin = instStartOrigin(mod, varLst, "start")
                    (cache, SOME(DAE.VAR_ATTR_STRING(quantity_str, start_val, fixed_val, NONE(), NONE(), NONE(), startOrigin)))
                  end

                  (cache, _, mod, enumtype && DAE.T_ENUMERATION(attributeLst = varLst), index_list)  => begin
                      quantity_str = instBinding(mod, varLst, DAE.T_STRING_DEFAULT, index_list, "quantity", false)
                      exp_bind_min = instBinding(mod, varLst, enumtype, index_list, "min", false)
                      exp_bind_max = instBinding(mod, varLst, enumtype, index_list, "max", false)
                      exp_bind_start = instBinding(mod, varLst, enumtype, index_list, "start", false)
                      fixed_val = instBinding(mod, varLst, DAE.T_BOOL_DEFAULT, index_list, "fixed", true)
                      startOrigin = instStartOrigin(mod, varLst, "start")
                    (cache, SOME(DAE.VAR_ATTR_ENUMERATION(quantity_str, exp_bind_min, exp_bind_max, exp_bind_start, fixed_val, NONE(), NONE(), NONE(), startOrigin)))
                  end

                  (cache, _, _, _, _)  => begin
                    (cache, NONE())
                  end
                end
              end
               #= TODO: check for protected attribute (here and below matches)
               =#
               #=  Integer
               =#
               #=  Boolean
               =#
               #=  BTH Clock
               =#
               #=  String
               =#
               #=  Enumeration
               =#
               #=  not a basic type?
               =#
          (outCache, outDAEVariableAttributesOption)
        end

         #= author: LP
          instantiates a enumeration binding and retrieves the value. =#
        function instEnumerationBinding(inMod::DAE.Mod, varLst::List{<:DAE.Var}, inIndices::List{<:ModelicaInteger}, inName::String, expected_type::DAE.Type, useConstValue::Bool #= if true, use constant value in TYPED (if present) =#) ::Option{DAE.Exp}
              local outBinding::Option{DAE.Exp}

              try
                outBinding = instBinding(inMod, varLst, expected_type, inIndices, inName, useConstValue)
              catch
                Error.addMessage(Error.TYPE_ERROR, list(inName, "enumeration type"))
              end
          outBinding
        end

         #=
          Author:Peter Aronsson, 2012

          Instantiates a distribution binding and retrieves the value.
         =#
        function instDistributionBinding(inMod::DAE.Mod, varLst::List{<:DAE.Var}, inIntegerLst::List{<:ModelicaInteger}, inString::String, useConstValue::Bool #= if true, use constant value in TYPED (if present) =#) ::Option{DAE.Distribution}
              local out::Option{DAE.Distribution}

              out = begin
                  local mod::DAE.Mod
                  local name::DAE.Exp
                  local params::DAE.Exp
                  local paramNames::DAE.Exp
                  local index_list::List{ModelicaInteger}
                  local bind_name::String
                  local ty::DAE.Type
                  local paramDim::ModelicaInteger
                  local cr::DAE.ComponentRef
                  local crName::DAE.ComponentRef
                  local crParams::DAE.ComponentRef
                  local crParamNames::DAE.ComponentRef
                  local path::Absyn.Path
                   #= Record constructor
                   =#
                @matchcontinue (inMod, inIntegerLst, inString) begin
                  (mod, index_list, bind_name)  => begin
                      @match SOME(DAE.CALL(path = path, expLst = name <| params <| paramNames <| nil)) = instBinding(mod, varLst, distributionType, index_list, bind_name, useConstValue)
                      @match true = AbsynUtil.pathEqual(path, Absyn.IDENT("Distribution"))
                    SOME(DAE.DISTRIBUTION(name, params, paramNames))
                  end

                  (mod, index_list, bind_name)  => begin
                      @match SOME(DAE.RECORD(path = path, exps = name <| params <| paramNames <| nil)) = instBinding(mod, varLst, distributionType, index_list, bind_name, useConstValue)
                      @match true = AbsynUtil.pathEqual(path, Absyn.IDENT("Distribution"))
                    SOME(DAE.DISTRIBUTION(name, params, paramNames))
                  end

                  (mod, index_list, bind_name)  => begin
                      @match SOME(DAE.CREF(cr, ty)) = instBinding(mod, varLst, distributionType, index_list, bind_name, useConstValue)
                      @match true = Types.isRecord(ty)
                      @match DAE.T_COMPLEX(varLst = _ <| DAE.TYPES_VAR(ty = DAE.T_ARRAY(dims = DAE.DIM_INTEGER(paramDim) <| nil)) <| _) = ty
                      crName = ComponentReference.crefPrependIdent(cr, "name", nil, DAE.T_STRING_DEFAULT)
                      crParams = ComponentReference.crefPrependIdent(cr, "params", nil, DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_INTEGER(paramDim))))
                      name = Expression.makeCrefExp(crName, DAE.T_STRING_DEFAULT)
                      params = Expression.makeCrefExp(crParams, DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_INTEGER(paramDim))))
                      paramNames = Expression.makeCrefExp(crParams, DAE.T_ARRAY(DAE.T_STRING_DEFAULT, list(DAE.DIM_INTEGER(paramDim))))
                    SOME(DAE.DISTRIBUTION(name, params, paramNames))
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
               #=  Cref
               =#
          out
        end

         #=
          Author: Daniel Hedberg 2011-01

          Extracts the uncertainty value, as defined in DAE, from a DAE.Exp.
         =#
        function getUncertainFromExpOption(expOption::Option{<:DAE.Exp}) ::Option{DAE.Uncertainty}
              local out::Option{DAE.Uncertainty}

              out = begin
                @match expOption begin
                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "Uncertainty", path = Absyn.IDENT("given"))))  => begin
                    SOME(DAE.GIVEN())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "Uncertainty", path = Absyn.IDENT("sought"))))  => begin
                    SOME(DAE.SOUGHT())
                  end

                  SOME(DAE.ENUM_LITERAL(name = Absyn.QUALIFIED(name = "Uncertainty", path = Absyn.IDENT("refine"))))  => begin
                    SOME(DAE.REFINE())
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          out
        end

         #= This function adds the equation in the declaration
          of a variable, if such an equation exists. =#
        function instModEquation(inComponentRef::DAE.ComponentRef, inType::DAE.Type, inMod::DAE.Mod, inSource::DAE.ElementSource #= the origin of the element =#, inImpl::Bool) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local t::DAE.Type
                  local dae::DAE.DAElist
                  local mod::DAE.Mod
                  local m::DAE.Mod
                  local e::DAE.Exp
                  local lhs::DAE.Exp
                  local prop2::DAE.Properties
                  local impl::Bool
                  local aexp1::Absyn.Exp
                  local aexp2::Absyn.Exp
                  local scode::SCode.EEquation
                  local acr::Absyn.ComponentRef
                  local info::SourceInfo
                  local source::DAE.ElementSource
                   #=  Record constructors are different
                   =#
                   #=  If it's a constant binding, all fields will already be bound correctly. Don't return a DAE.
                   =#
                @matchcontinue (inType, inMod) begin
                  (DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)), DAE.MOD(binding = SOME(DAE.TYPED(_, SOME(_), DAE.PROP(_, DAE.C_CONST(__)), _))))  => begin
                    DAE.emptyDae
                  end

                  (_, DAE.MOD(binding = SOME(DAE.TYPED(properties = prop2))))  => begin
                       #=  Special case if the dimensions of the expression is 0.
                       =#
                       #=  If this is true, and it is instantiated normally, matching properties
                       =#
                       #=  will result in error messages (Real[0] is not Real), so we handle it here.
                       =#
                      @match DAE.T_ARRAY(dims = DAE.DIM_INTEGER(0) <| nil) = Types.getPropType(prop2)
                    DAE.emptyDae
                  end

                  (_, DAE.MOD(binding = SOME(DAE.TYPED(e, _, prop2, aexp2)), info = info))  => begin
                       #=  Regular cases
                       =#
                      t = Types.simplifyType(inType)
                      lhs = Expression.makeCrefExp(inComponentRef, t)
                      acr = ComponentReference.unelabCref(inComponentRef)
                      aexp1 = Absyn.CREF(acr)
                      scode = SCode.EQ_EQUALS(aexp1, aexp2, SCode.noComment, info)
                      source = ElementSource.addSymbolicTransformation(inSource, DAE.FLATTEN(scode, NONE()))
                      dae = InstSection.instEqEquation(lhs, DAE.PROP(inType, DAE.C_VAR()), e, prop2, source, SCode.NON_INITIAL(), inImpl, info)
                    dae
                  end

                  (_, DAE.MOD(binding = NONE()))  => begin
                    DAE.emptyDae
                  end

                  (_, DAE.NOMOD(__))  => begin
                    DAE.emptyDae
                  end

                  (_, DAE.REDECL(__))  => begin
                    DAE.emptyDae
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstBinding.instModEquation failed\\n type: ")
                        Debug.trace(Types.printTypeStr(inType))
                        Debug.trace("\\n  cref: ")
                        Debug.trace(ComponentReference.printComponentRefStr(inComponentRef))
                        Debug.trace("\\n mod:")
                        Debug.traceln(Mod.printModStr(inMod))
                      fail()
                  end
                end
              end
          outDae
        end

         #= This function looks at the equation part of a modification, and
          if there is a declaration equation builds a DAE.Binding for it. =#
        function makeBinding(inCache::FCore.Cache, inEnv::FCore.Graph, inAttributes::SCode.Attributes, inMod::DAE.Mod, inType::DAE.Type, inPrefix::Prefix.PrefixType, componentName::String, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Binding}
              local outBinding::DAE.Binding
              local outCache::FCore.Cache

              (outCache, outBinding) = begin
                  local tp::DAE.Type
                  local e_tp::DAE.Type
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local e_val_exp::DAE.Exp
                  local e_val::Option{Values.Value}
                  local c::DAE.Const
                  local e_tp_str::String
                  local tp_str::String
                  local e_str::String
                  local e_str_1::String
                  local str::String
                  local s::String
                  local pre_str::String
                  local cache::FCore.Cache
                  local prop::DAE.Properties
                  local binding::DAE.Binding
                  local startValueModification::DAE.Mod
                  local complex_vars::List{DAE.Var}
                  local tpath::Absyn.Path
                  local sub_mods::List{DAE.SubMod}
                  local info::SourceInfo
                  local v::Values.Value
                   #=  A record might have bindings from the class, use those if there is no modifier!
                   =#
                @matchcontinue (inCache, inAttributes, inMod, inType) begin
                  (cache, _, DAE.NOMOD(__), _)  => begin
                      @match DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = tpath), varLst = complex_vars) = Types.arrayElementType(inType)
                      @match true = Types.allHaveBindings(complex_vars)
                      binding = makeRecordBinding(cache, inEnv, tpath, inType, complex_vars, nil, inInfo)
                    (cache, binding)
                  end

                  (cache, _, DAE.NOMOD(__), _)  => begin
                    (cache, DAE.UNBOUND())
                  end

                  (_, _, DAE.REDECL(__), _)  => begin
                    makeBinding(inCache, inEnv, inAttributes, inMod.mod, inType, inPrefix, componentName, inInfo)
                  end

                  (cache, SCode.ATTR(variability = SCode.PARAM(__)), DAE.MOD(binding = NONE()), tp)  => begin
                      @match true = Types.getFixedVarAttributeParameterOrConstant(tp)
                      startValueModification = Mod.lookupCompModification(inMod, "start")
                      @match false = Mod.isEmptyMod(startValueModification)
                      (cache, binding) = makeBinding(cache, inEnv, inAttributes, startValueModification, inType, inPrefix, componentName, inInfo)
                      binding = DAEUtil.setBindingSource(binding, DAE.BINDING_FROM_START_VALUE())
                    (cache, binding)
                  end

                  (cache, _, DAE.MOD(subModLst = sub_mods && _ <| _), _)  => begin
                      @match DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path = tpath), varLst = complex_vars) = Types.arrayElementType(inType)
                      binding = makeRecordBinding(cache, inEnv, tpath, inType, complex_vars, sub_mods, inInfo)
                    (cache, binding)
                  end

                  (cache, _, DAE.MOD(binding = NONE()), _)  => begin
                    (cache, DAE.UNBOUND())
                  end

                  (cache, _, DAE.MOD(binding = SOME(DAE.TYPED(e, SOME(v), prop, _))), e_tp)  => begin
                      c = Types.propAllConst(prop)
                      tp = Types.getPropType(prop)
                      @match false = Types.equivtypes(tp, e_tp)
                      e_val_exp = ValuesUtil.valueExp(v)
                      (e_1, _) = Types.matchType(e, tp, e_tp, false)
                      (e_1, _) = ExpressionSimplify.simplify(e_1)
                      (e_val_exp, _) = Types.matchType(e_val_exp, tp, e_tp, false)
                      (e_val_exp, _) = ExpressionSimplify.simplify(e_val_exp)
                      v = Ceval.cevalSimple(e_val_exp)
                      e_val = SOME(v)
                    (cache, DAE.EQBOUND(e_1, e_val, c, DAE.BINDING_FROM_DEFAULT_VALUE()))
                  end

                  (cache, _, DAE.MOD(binding = SOME(DAE.TYPED(e, e_val, prop, _))), e_tp)  => begin
                      c = Types.propAllConst(prop)
                      tp = Types.getPropType(prop)
                      (e_1, _) = Types.matchType(e, tp, e_tp, false)
                      (e_1, _) = ExpressionSimplify.simplify(e_1)
                    (cache, DAE.EQBOUND(e_1, e_val, c, DAE.BINDING_FROM_DEFAULT_VALUE()))
                  end

                  (_, _, DAE.MOD(binding = SOME(DAE.TYPED(e, _, prop, _)), info = info), tp)  => begin
                      e_tp = Types.getPropType(prop)
                      _ = Types.propAllConst(prop)
                      @shouldFail (_, _) = Types.matchType(e, e_tp, tp, false)
                      e_tp_str = Types.unparseTypeNoAttr(e_tp)
                      tp_str = Types.unparseTypeNoAttr(tp)
                      e_str = ExpressionDump.printExpStr(e)
                      e_str_1 = stringAppend("=", e_str)
                      str = PrefixUtil.printPrefixStrIgnoreNoPre(inPrefix) + "." + componentName
                      Types.typeErrorSanityCheck(e_tp_str, tp_str, info)
                      Error.addSourceMessage(Error.MODIFIER_TYPE_MISMATCH_ERROR, list(str, tp_str, e_str_1, e_tp_str), info)
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Inst.makeBinding failed on component:" + PrefixUtil.printPrefixStr(inPrefix) + "." + componentName)
                      fail()
                  end
                end
              end
               #=  adrpo: if the binding is missing for a parameter and
               =#
               #=         the parameter has a start value modification,
               =#
               #=         use that to create the binding as if we have
               =#
               #=         a modification from outside it will be re-written.
               =#
               #=         this fixes:
               =#
               #=              Modelica.Electrical.Machines.Examples.SMEE_Generator
               =#
               #=              (BUG: #1156 at https:openmodelica.org:8443/cb/issue/1156)
               =#
               #=              and maybe a lot others.
               =#
               #=  this always succeeds but return NOMOD if there is no (start = x)
               =#
               #=  make sure is NOT a DAE.NOMOD!
               =#
               #=  lochel: I moved the warning to the back end for now
               =#
               #=  s = componentName;
               =#
               #=  pre_str = PrefixUtil.printPrefixStr2(inPrefix);
               =#
               #=  s = pre_str + s;
               =#
               #=  str = DAEUtil.printBindingExpStr(binding);
               =#
               #=  Error.addSourceMessage(Error.UNBOUND_PARAMETER_WITH_START_VALUE_WARNING, {s,str}, inInfo);
               =#
               #=  A record might have bindings for each component instead of a single
               =#
               #=  binding for the whole record, in which case we need to assemble them into
               =#
               #=  a binding.
               =#
               #= /* adrpo: CHECK! do we need this here? numerical values
                  case (cache,env,_,DAE.MOD(binding = SOME(DAE.TYPED(e,_,DAE.PROP(e_tp,_)))),tp,_,_)
                    equation
                      (e_1,_) = Types.matchType(e, e_tp, tp);
                      (cache,v,_) = Ceval.ceval(cache,env, e_1, false,NONE(), NONE(), Absyn.NO_MSG(),0);
                    then
                      (cache,DAE.VALBOUND(v, DAE.BINDING_FROM_DEFAULT_VALUE()));
                  */ =#
               #= /* default */ =#
               #=  Handle bindings of the type Boolean b[Boolean]={true,false}, enumerations, and similar
               =#
               #=  tp = Types.traverseType(tp, 1, Types.makeKnownDimensionsInteger);
               =#
               #=  e_tp = Types.traverseType(e_tp, 1, Types.makeKnownDimensionsInteger);
               =#
               #= /* default */ =#
               #=  Handle bindings of the type Boolean b[Boolean]={true,false}, enumerations, and similar
               =#
               #=  tp = Types.traverseType(tp, 1, Types.makeKnownDimensionsInteger);
               =#
               #=  e_tp = Types.traverseType(e_tp, 1, Types.makeKnownDimensionsInteger);
               =#
          (outCache, outBinding)
        end

         #= Creates a binding for a record given a list of submodifiers. This is the case
           when a record is given a binding by modifiers, ex:

             record R
               Real x; Real y;
             end R;

             constant R r(x = 2.0, y = 3.0);

          This is translated to:
             constant R r = R(2.0, 3.0);

          This is needed when we assign a record to another record.
           =#
        function makeRecordBinding(inCache::FCore.Cache, inEnv::FCore.Graph, inRecordName::Absyn.Path, inRecordType::DAE.Type, inRecordVars::List{<:DAE.Var}, inMods::List{<:DAE.SubMod}, inInfo::SourceInfo) ::DAE.Binding
              local outBinding::DAE.Binding

              local accum_exps::List{DAE.Exp} = nil
              local accum_vals::List{Values.Value} = nil
              local accum_names::List{String} = nil
              local mods::List{DAE.SubMod} = inMods
              local opt_mod::Option{DAE.SubMod}
              local name::String = ""
              local scope::String
              local ty_str::String
              local ty::DAE.Type
              local ety::DAE.Type
              local binding::DAE.Binding
              local dims::List{DAE.Dimension}
              local exp::DAE.Exp
              local val::Values.Value

              dims = Types.getDimensions(inRecordType)
              try
                for var in inRecordVars
                  @match DAE.TYPES_VAR(name = name, ty = ty, binding = binding) = var
                  (mods, opt_mod) = ListUtil.deleteMemberOnTrue(name, mods, InstUtil.isSubModNamed)
                  if isSome(opt_mod)
                    ty = Types.liftArrayListDims(ty, dims)
                    (exp, val) = makeRecordBinding3(opt_mod, ty, inInfo)
                  elseif DAEUtil.isBound(binding)
                    @match DAE.EQBOUND(exp = exp, evaluatedExp = SOME(val)) = binding
                  else
                    ety = Types.simplifyType(ty)
                    ty = Types.liftArrayListDims(ty, dims)
                    scope = FGraph.printGraphPathStr(inEnv)
                    ty_str = Types.printTypeStr(ty)
                    exp = DAE.EMPTY(scope, DAE.CREF_IDENT(name, ety, nil), ety, ty_str)
                    val = Values.EMPTY(scope, name, Types.typeToValue(ty), ty_str)
                  end
                  accum_exps = _cons(exp, accum_exps)
                  accum_vals = _cons(val, accum_vals)
                  accum_names = _cons(name, accum_names)
                end
                ety = Types.simplifyType(Types.arrayElementType(inRecordType))
                exp = DAE.CALL(inRecordName, listReverse(accum_exps), DAE.CALL_ATTR(ety, false, false, false, false, DAE.NORM_INLINE(), DAE.NO_TAIL()))
                val = Values.RECORD(inRecordName, listReverse(accum_vals), listReverse(accum_names), -1)
                (exp, val) = InstUtil.liftRecordBinding(inRecordType, exp, val)
                outBinding = DAE.EQBOUND(exp, SOME(val), DAE.C_CONST(), DAE.BINDING_FROM_DEFAULT_VALUE())
              catch
                if Flags.isSet(Flags.FAILTRACE)
                  Debug.traceln("- Inst.makeRecordBinding2 failed for " + AbsynUtil.pathString(inRecordName) + "." + name + "\\n")
                end
                fail()
              end
               #=  Try to find a submod with the same name as the variable.
               =#
               #=  Found a submod, use its binding.
               =#
               #=  Couldn't find a submod, but variable has a binding already.
               =#
               #=  Couldn't find a submod, and the variable doesn't have a binding.
               =#
               #=  Assemble the binding for the record.
               =#
          outBinding
        end

         #= Helper function to makeRecordBinding2. Fetches the binding expression and
           value from an optional submod. =#
        function makeRecordBinding3(inSubMod::Option{<:DAE.SubMod}, inType::DAE.Type, inInfo::SourceInfo) ::Tuple{DAE.Exp, Values.Value}
              local outValue::Values.Value
              local outExp::DAE.Exp

              (outExp, outValue) = begin
                  local exp::DAE.Exp
                  local val::Values.Value
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local ident::DAE.Ident
                  local binding_str::String
                  local expected_type_str::String
                  local given_type_str::String
                   #=  Array type and each prefix => return the expression and value.
                   =#
                @matchcontinue inSubMod begin
                  SOME(DAE.NAMEMOD(mod = DAE.MOD(eachPrefix = SCode.EACH(__), binding = SOME(DAE.TYPED(modifierAsExp = exp, modifierAsValue = SOME(val))))))  => begin
                    (exp, val)
                  end

                  SOME(DAE.NAMEMOD(mod = DAE.MOD(eachPrefix = SCode.NOT_EACH(__), binding = SOME(DAE.TYPED(modifierAsExp = exp, modifierAsValue = SOME(val), properties = DAE.PROP(type_ = ty))))))  => begin
                       #=  Scalar type and no each prefix => return the expression and value.
                       =#
                      (exp, ty) = Types.matchType(exp, ty, inType, true)
                    (exp, val)
                  end

                  SOME(DAE.NAMEMOD(mod = DAE.MOD(eachPrefix = SCode.NOT_EACH(__), binding = SOME(DAE.TYPED(modifierAsExp = exp, modifierAsValue = NONE(), properties = DAE.PROP(type_ = ty))))))  => begin
                       #=  Scalar type and no each prefix => bindings given by expressions myRecord(v1 = inV1, v2 = inV2)
                       =#
                      (exp, ty) = Types.matchType(exp, ty, inType, true)
                    (exp, Values.OPTION(NONE()))
                  end

                  SOME(DAE.NAMEMOD(ident = ident, mod = DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = exp, properties = DAE.PROP(type_ = ty))))))  => begin
                      binding_str = ExpressionDump.printExpStr(exp)
                      expected_type_str = Types.unparseTypeNoAttr(inType)
                      given_type_str = Types.unparseTypeNoAttr(ty)
                      Types.typeErrorSanityCheck(given_type_str, expected_type_str, inInfo)
                      Error.addSourceMessage(Error.VARIABLE_BINDING_TYPE_MISMATCH, list(ident, binding_str, expected_type_str, given_type_str), inInfo)
                    fail()
                  end
                end
              end
          (outExp, outValue)
        end

         #= Returns a variable's bound expression. =#
        function makeVariableBinding(inType::DAE.Type, inMod::DAE.Mod, inConst::DAE.Const, inPrefix::Prefix.PrefixType, inName::String) ::Option{DAE.Exp}
              local outBinding::Option{DAE.Exp}

              local oeq_mod::Option{DAE.EqMod} = Mod.modEquation(inMod)
              local e::DAE.Exp
              local e2::DAE.Exp
              local p::DAE.Properties
              local info::SourceInfo
              local c::DAE.Const
              local e_str::String
              local et_str::String
              local bt_str::String

               #=  No modifier => no binding.
               =#
              if isNone(oeq_mod)
                outBinding = NONE()
                return outBinding
              end
              @match SOME(DAE.TYPED(modifierAsExp = e, properties = p)) = oeq_mod
              if Types.isExternalObject(inType)
                outBinding = SOME(e)
              elseif Types.isEmptyArray(Types.getPropType(p))
                outBinding = NONE()
              else
                info = Mod.getModInfo(inMod)
                try
                  @match (e2, DAE.PROP(constFlag = c)) = Types.matchProp(e, p, DAE.PROP(inType, inConst), true)
                catch
                  e_str = ExpressionDump.printExpStr(e)
                  et_str = Types.unparseTypeNoAttr(inType)
                  bt_str = Types.unparseTypeNoAttr(Types.getPropType(p))
                  Types.typeErrorSanityCheck(et_str, bt_str, info)
                  Error.addSourceMessageAndFail(Error.VARIABLE_BINDING_TYPE_MISMATCH, list(inName, e_str, et_str, bt_str), info)
                end
                InstUtil.checkHigherVariability(inConst, c, inPrefix, inName, e, info)
                outBinding = SOME(e2)
              end
               #=  For external objects the binding contains the constructor call. Return it as it is.
               =#
               #=  An empty array has unknown type, skip type matching.
               =#
               #=  For normal variables, make sure the types match.
               =#
               #=  The types of the variable and binding are incompatible, print an error.
               =#
               #=  Check that the variability is compatible too.
               =#
          outBinding
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

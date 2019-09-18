  module Types


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    TypeFn = Function

    MatchFunc = Function

    Func = Function

    Func = Function

    Func = Function

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

        import ClassInf

        import Absyn

        import AbsynUtil

        import DAE

        import InstTypes

        import Values

        import SCode

        Binding = DAE.Binding

        Const = DAE.Const

        EqualityConstraint = DAE.EqualityConstraint

        FuncArg = DAE.FuncArg

        Properties = DAE.Properties

        TupleConst = DAE.TupleConst

        Type = DAE.Type

        Var = DAE.Var

        EqMod = DAE.EqMod

        import ComponentReference

        import Config

        import Dump

        import Debug

        import Error

        import Expression

        import ExpressionDump

        import ExpressionSimplify

        import Flags

        import ListUtil

        import Patternm

        import Print

        import Util

        import System

        import ValuesUtil

        import DAEUtil

        import SCodeDump

        import MetaModelica.Dangerous.listReverseInPlace

         #= Succeeds for all the discrete types, Integer, String, Boolean and enumeration. =#
        function discreteType(inType::DAE.Type)
              @match true = isDiscreteType(inType)
        end

        function isDiscreteType(inType::DAE.Type) ::Bool
              local outIsDiscrete::Bool

              outIsDiscrete = begin
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
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

                  DAE.T_ENUMERATION(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    isDiscreteType(inType.complexType)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsDiscrete
        end

         #= Function for merging a list of properties, currently only working on DAE.PROP() and not TUPLE_DAE.PROP(). =#
        function propsAnd(inProps::List{<:DAE.Properties}) ::DAE.Properties
              local outProp::DAE.Properties

              outProp = begin
                  local prop::Properties
                  local prop2::Properties
                  local c::Const
                  local c2::Const
                  local ty::Type
                  local ty2::Type
                  local props::List{DAE.Properties}
                @matchcontinue inProps begin
                  prop <|  nil()  => begin
                    prop
                  end

                  DAE.PROP(ty, c) <| props  => begin
                      @match DAE.PROP(ty2, c2) = propsAnd(props)
                      c = constAnd(c, c2)
                      @match true = equivtypes(ty, ty2)
                    DAE.PROP(ty, c)
                  end
                end
              end
          outProp
        end

         #= returns the same Properties but with the const flag set to Var =#
        function makePropsNotConst(inProperties::DAE.Properties) ::DAE.Properties
              local outProperties::DAE.Properties

              outProperties = begin
                  local t::Type
                @match inProperties begin
                  DAE.PROP(type_ = t)  => begin
                    DAE.PROP(t, DAE.C_VAR())
                  end
                end
              end
          outProperties
        end

         #=  stefan
         =#

         #= retrieves a list of Consts from a list of Properties =#
        function getConstList(inPropertiesList::List{<:DAE.Properties}) ::List{DAE.Const}
              local outConstList::List{DAE.Const}

              outConstList = begin
                  local c::Const
                  local ccdr::List{DAE.Const}
                  local pcdr::List{DAE.Properties}
                  local tc::TupleConst
                @match inPropertiesList begin
                   nil()  => begin
                    nil
                  end

                  DAE.PROP(constFlag = c) <| pcdr  => begin
                      ccdr = getConstList(pcdr)
                    _cons(c, ccdr)
                  end

                  DAE.PROP_TUPLE(tupleConst = tc) <| pcdr  => begin
                      c = propertiesListToConst2(tc)
                      ccdr = getConstList(pcdr)
                    _cons(c, ccdr)
                  end
                end
              end
          outConstList
        end

         #= this function elaborates on a DAE.Properties and return the DAE.Const value. =#
        function propertiesListToConst(p::List{<:DAE.Properties}) ::DAE.Const
              local c::DAE.Const

              c = begin
                  local p1::Properties
                  local pps::List{DAE.Properties}
                  local c1::Const
                  local c2::Const
                  local tc1::TupleConst
                @match p begin
                   nil()  => begin
                    DAE.C_CONST()
                  end

                  DAE.PROP(_, c1) <| pps  => begin
                      c2 = propertiesListToConst(pps)
                      c1 = constAnd(c1, c2)
                    c1
                  end

                  DAE.PROP_TUPLE(_, tc1) <| pps  => begin
                      c1 = propertiesListToConst2(tc1)
                      c2 = propertiesListToConst(pps)
                      c1 = constAnd(c1, c2)
                    c1
                  end
                end
              end
          c
        end

         #=  =#
        function propertiesListToConst2(t::DAE.TupleConst) ::DAE.Const
              local c::DAE.Const

              c = begin
                  local p1::TupleConst
                  local c1::Const
                  local c2::Const
                  local tcxl::List{TupleConst}
                  local tc1::TupleConst
                @match t begin
                  DAE.SINGLE_CONST(c1)  => begin
                    c1
                  end

                  DAE.TUPLE_CONST(tc1 <| tcxl)  => begin
                      c1 = propertiesListToConst2(tc1)
                      c2 = tupleConstListToConst(tcxl)
                      c1 = constAnd(c1, c2)
                    c1
                  end
                end
              end
          c
        end

         #=  =#
        function tupleConstListToConst(t::List{<:DAE.TupleConst}) ::DAE.Const
              local c::DAE.Const

              c = begin
                  local p1::TupleConst
                  local c1::Const
                  local c2::Const
                  local tcxl::List{TupleConst}
                @match t begin
                   nil()  => begin
                    DAE.C_CONST()
                  end

                  DAE.SINGLE_CONST(c1) <| tcxl  => begin
                      c2 = tupleConstListToConst(tcxl)
                      c1 = constAnd(c1, c2)
                    c1
                  end

                  p1 && DAE.TUPLE_CONST(_) <| tcxl  => begin
                      c1 = propertiesListToConst2(p1)
                      c2 = tupleConstListToConst(tcxl)
                      c1 = constAnd(c1, c2)
                    c1
                  end
                end
              end
          c
        end

         #= author: PA
         Succeeds if type is ExternalObject =#
        function externalObjectType(inType::DAE.Type)
              _ = begin
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(_))  => begin
                    ()
                  end
                end
              end
        end

         #=
        Author BZ, 2009-09
        Function for getting the name of a DAE.Var =#
        function varName(v::DAE.Var) ::String
              local s::String

              @match DAE.TYPES_VAR(name = s) = v
          s
        end

        function varBinding(inVar::DAE.Var) ::DAE.Binding
              local outBinding::DAE.Binding

              @match DAE.TYPES_VAR(binding = outBinding) = inVar
          outBinding
        end

        function varEqualName(inVar1::DAE.Var, inVar2::DAE.Var) ::Bool
              local outEqual::Bool

              local name1::String
              local name2::String

              @match DAE.TYPES_VAR(name = name1) = inVar1
              @match DAE.TYPES_VAR(name = name2) = inVar2
              outEqual = name1 == name2
          outEqual
        end

         #= author: PA
          Succeeds if type is ExternalObject constructor function =#
        function externalObjectConstructorType(inType::DAE.Type)
              _ = begin
                  local tp::Type
                @match inType begin
                  DAE.T_FUNCTION(funcResultType = tp)  => begin
                      externalObjectType(tp)
                    ()
                  end
                end
              end
        end

         #= author: PA
          Succeeds for all the builtin types, Integer, String, Real, Boolean =#
        function simpleType(inType::DAE.Type)
              @match true = isSimpleType(inType)
        end

         #= Returns true for all the builtin types, Integer, String, Real, Boolean =#
        function isSimpleType(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local t::DAE.Type
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    true
                  end

                  DAE.T_INTEGER(__)  => begin
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

                  DAE.T_ENUMERATION(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                    isSimpleType(t)
                  end

                  DAE.T_FUNCTION(funcResultType = t)  => begin
                    isSimpleType(t)
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

         #= Returns true for simple numeric builtin types, Integer and Real =#
        function isSimpleNumericType(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local t::DAE.Type
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    true
                  end

                  DAE.T_INTEGER(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                    isSimpleNumericType(t)
                  end

                  DAE.T_FUNCTION(funcResultType = t)  => begin
                    isSimpleNumericType(t)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= This function checks if the element type is Numeric type or array of Numeric type. =#
        function isNumericType(inType::DAE.Type) ::Bool
              local outBool::Bool

              outBool = begin
                  local ty::Type
                @match inType begin
                  DAE.T_ARRAY(ty = ty)  => begin
                    isNumericType(ty)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isNumericType(ty)
                  end

                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    isNumericType(ty)
                  end

                  _  => begin
                      isSimpleNumericType(inType)
                  end
                end
              end
          outBool
        end

         #= Returns true if the given type is a connector type, otherwise false. =#
        function isConnector(inType::DAE.Type) ::Bool
              local outIsConnector::Bool

              outIsConnector = begin
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(__))  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsConnector
        end

         #= Returns true if the given type is a complex connector type, i.e. a connector
           with components, otherwise false. =#
        function isComplexConnector(inType::DAE.Type) ::Bool
              local outIsComplexConnector::Bool

              outIsComplexConnector = begin
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsComplexConnector
        end

         #= Returns true if the given type is an expandable connector, otherwise false. =#
        function isComplexExpandableConnector(inType::DAE.Type) ::Bool
              local outResult::Bool

              outResult = begin
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(isExpandable = true))  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(isExpandable = true))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outResult
        end

         #=
        Author: BZ, 2008-11
        This function checks wheter a type is complex AND not extending a base type. =#
        function isComplexType(ity::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local ty::Type
                @match ity begin
                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isComplexType(ty)
                  end

                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    isComplexType(ty)
                  end

                  DAE.T_COMPLEX(varLst = _ <| _)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  not derived from baseclass
               =#
          b
        end

         #= Returns true if type is COMPLEX and external object (ClassInf) =#
        function isExternalObject(tp::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match tp begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(_))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=  Converts a DAE.Type to a DAE.Type
         NOTE: This function should not be used in general, since it is not recommended to translate DAE.Type into DAE.Type. =#
        function expTypetoTypesType(inType::DAE.Type) ::DAE.Type
              local oType::DAE.Type

              oType = begin
                  local ty::Type
                  local tty::Type
                  local at::Type
                  local ad::DAE.Dimensions
                  local dim::DAE.Dimension
                  local vars::List{DAE.Var}
                  local CIS::ClassInf.SMNode
                  local ec::DAE.EqualityConstraint
                   #=  convert just the array!
                   =#
                @matchcontinue inType begin
                  DAE.T_ARRAY(at, dim <|  nil())  => begin
                      ty = expTypetoTypesType(at)
                      tty = DAE.T_ARRAY(ty, list(dim))
                    tty
                  end

                  DAE.T_ARRAY(at, dim <| ad)  => begin
                      ty = expTypetoTypesType(DAE.T_ARRAY(at, ad))
                      tty = DAE.T_ARRAY(ty, list(dim))
                    tty
                  end

                  DAE.T_COMPLEX(CIS, vars, ec)  => begin
                      vars = ListUtil.map(vars, convertFromExpToTypesVar)
                    DAE.T_COMPLEX(CIS, vars, ec)
                  end

                  DAE.T_SUBTYPE_BASIC(CIS, vars, ty, ec)  => begin
                      vars = ListUtil.map(vars, convertFromExpToTypesVar)
                      ty = expTypetoTypesType(ty)
                    DAE.T_SUBTYPE_BASIC(CIS, vars, ty, ec)
                  end

                  DAE.T_METABOXED(ty)  => begin
                      ty = expTypetoTypesType(ty)
                    DAE.T_METABOXED(ty)
                  end

                  _  => begin
                      inType
                  end
                end
              end
               #=  the rest fall in line!
               =#
          oType
        end

         #=  =#
        function convertFromExpToTypesVar(inVar::DAE.Var) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local name::String
                  local ty::Type
                  local attributes::DAE.Attributes
                  local binding::Binding
                  local constOfForIteratorRange::Option{DAE.Const}
                @matchcontinue inVar begin
                  DAE.TYPES_VAR(name, attributes, ty, binding, constOfForIteratorRange)  => begin
                      ty = expTypetoTypesType(ty)
                    DAE.TYPES_VAR(name, attributes, ty, binding, constOfForIteratorRange)
                  end

                  _  => begin
                        print("error in Types.convertFromExpToTypesVar\\n")
                      fail()
                  end
                end
              end
          outVar
        end

         #= Returns true if type is TUPLE =#
        function isTuple(tp::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match tp begin
                  DAE.T_TUPLE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if type is TUPLE =#
        function isMetaTuple(tp::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match tp begin
                  DAE.T_METATUPLE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if type is COMPLEX and a record (ClassInf) =#
        function isRecord(tp::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match tp begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= gets the record path =#
        function getRecordPath(tp::DAE.Type) ::Absyn.Path
              local p::Absyn.Path

              p = begin
                @match tp begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p))  => begin
                    p
                  end
                end
              end
          p
        end

         #= Returns true if type is a record only containing Reals =#
        function isRecordWithOnlyReals(tp::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local varLst::List{DAE.Var}
                @match tp begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_), varLst = varLst)  => begin
                    ListUtil.mapAllValueBool(ListUtil.map(varLst, getVarType), isReal, true)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  otherwise false
               =#
          b
        end

         #= Return the Type of a Var =#
        function getVarType(v::DAE.Var) ::DAE.Type
              local tp::DAE.Type

              tp = begin
                @match v begin
                  DAE.TYPES_VAR(ty = tp)  => begin
                    tp
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Types.getVarType failed"))
                      fail()
                  end
                end
              end
          tp
        end

        function varIsVariable(v::DAE.Var) ::Bool
              local b::Bool

              b = begin
                @match v begin
                  DAE.TYPES_VAR(attributes = DAE.ATTR(variability = SCode.VAR(__)))  => begin
                    true
                  end

                  DAE.TYPES_VAR(attributes = DAE.ATTR(variability = SCode.DISCRETE(__)))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Return the name of a Var =#
        function getVarName(v::DAE.Var) ::String
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

         #= Returns true if type is Real =#
        function isReal(tp::DAE.Type) ::Bool
              local res::Bool

              res = isScalarReal(arrayElementType(tp))
          res
        end

        function isScalarReal(inType::DAE.Type) ::Bool
              local outIsScalarReal::Bool

              outIsScalarReal = begin
                  local ty::Type
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isScalarReal(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsScalarReal
        end

         #=
        Author BZ 2008-05
        This function verifies if it is some kind of a Real type we are working with. =#
        function isRealOrSubTypeReal(inType::DAE.Type) ::Bool
              local b::Bool

              local lb1::Bool
              local lb2::Bool

              lb1 = isReal(inType)
              lb2 = equivtypes(inType, DAE.T_REAL_DEFAULT)
              b = lb1 || lb2
          b
        end

         #=
        Author BZ 2009-02
        This function verifies if it is some kind of a Integer type we are working with. =#
        function isIntegerOrSubTypeInteger(inType::DAE.Type) ::Bool
              local b::Bool

              local lb1::Bool
              local lb2::Bool

              lb1 = isInteger(inType)
              lb2 = equivtypes(inType, DAE.T_INTEGER_DEFAULT)
              b = lb1 || lb2
          b
        end

        function isClockOrSubTypeClock1(inType::DAE.Type) ::Bool
              local b::Bool

              local lb1::Bool
              local lb2::Bool
              local lb3::Bool

              lb1 = isClock(inType)
              lb2 = equivtypes(inType, DAE.T_CLOCK_DEFAULT)
              lb3 = ! equivtypes(inType, DAE.T_UNKNOWN_DEFAULT)
              b = lb1 || lb2 && lb3
          b
        end

        function isClockOrSubTypeClock(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local ty::DAE.Type
                @match inType begin
                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    isClockOrSubTypeClock1(ty)
                  end

                  _  => begin
                      isClockOrSubTypeClock1(inType)
                  end
                end
              end
          b
        end

         #= @author: adrpo
         This function verifies if it is some kind of a Boolean type we are working with. =#
        function isBooleanOrSubTypeBoolean(inType::DAE.Type) ::Bool
              local b::Bool

              local lb1::Bool
              local lb2::Bool

              lb1 = isBoolean(inType)
              lb2 = equivtypes(inType, DAE.T_BOOL_DEFAULT)
              b = lb1 || lb2
          b
        end

         #= @author: adrpo
         This function verifies if it is some kind of a String type we are working with. =#
        function isStringOrSubTypeString(inType::DAE.Type) ::Bool
              local b::Bool

              local lb1::Bool
              local lb2::Bool

              lb1 = isString(inType)
              lb2 = equivtypes(inType, DAE.T_STRING_DEFAULT)
              b = lb1 || lb2
          b
        end

         #= Checks if a type is either some Integer or Real type. =#
        function isIntegerOrRealOrSubTypeOfEither(t::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match t begin
                  _ where (isRealOrSubTypeReal(t))  => begin
                    true
                  end

                  _ where (isIntegerOrSubTypeInteger(t))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Checks if a type is either some Integer or Real type. =#
        function isIntegerOrRealOrBooleanOrSubTypeOfEither(t::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match t begin
                  _ where (isRealOrSubTypeReal(t))  => begin
                    true
                  end

                  _ where (isIntegerOrSubTypeInteger(t))  => begin
                    true
                  end

                  _ where (isBooleanOrSubTypeBoolean(t))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isClock(tp::DAE.Type) ::Bool
              local res::Bool

              res = isScalarClock(arrayElementType(tp))
          res
        end

        function isScalarClock(inType::DAE.Type) ::Bool
              local res::Bool

              res = begin
                  local ty::Type
                @match inType begin
                  DAE.T_CLOCK(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isScalarClock(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Returns true if type is Integer =#
        function isInteger(tp::DAE.Type) ::Bool
              local res::Bool

              res = isScalarInteger(arrayElementType(tp))
          res
        end

        function isScalarInteger(inType::DAE.Type) ::Bool
              local outIsScalarInteger::Bool

              outIsScalarInteger = begin
                  local ty::Type
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isScalarInteger(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsScalarInteger
        end

         #= Returns true if type is Boolean =#
        function isBoolean(tp::DAE.Type) ::Bool
              local res::Bool

              res = isScalarBoolean(arrayElementType(tp))
          res
        end

        function isScalarBoolean(inType::DAE.Type) ::Bool
              local outIsScalarBoolean::Bool

              outIsScalarBoolean = begin
                  local ty::Type
                @match inType begin
                  DAE.T_BOOL(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isScalarBoolean(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsScalarBoolean
        end

         #= author: PA
          Succeeds for the builtin types Integer and Real
          (including classes extending the basetype Integer or Real). =#
        function integerOrReal(inType::DAE.Type)
              _ = begin
                  local tp::Type
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    ()
                  end

                  DAE.T_INTEGER(__)  => begin
                    ()
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = tp)  => begin
                      integerOrReal(tp)
                    ()
                  end
                end
              end
        end

         #= Returns true if Type is an nonscalar array (array of arrays). =#
        function isNonscalarArray(inType::DAE.Type, inDims::DAE.Dimensions) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local t::Type
                  local tys::List{Type}
                  local b::Bool
                   #=  several (at least 2) dimensions means array!
                   =#
                @matchcontinue (inType, inDims) begin
                  (_, _ <| _ <| _)  => begin
                    true
                  end

                  (DAE.T_ARRAY(__), _)  => begin
                    true
                  end

                  (DAE.T_SUBTYPE_BASIC(complexType = t), _)  => begin
                    isNonscalarArray(t, nil)
                  end

                  (DAE.T_TUPLE(types = tys), _)  => begin
                      b = ListUtil.applyAndFold1(tys, boolOr, isNonscalarArray, nil, false)
                    b
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  if the type is an array, then is an array
               =#
               #=  if is a type extending basic type
               =#
          outBoolean
        end

         #= Returns true if the given type is an array type. =#
        function isArray(inType::DAE.Type) ::Bool
              local outIsArray::Bool

              outIsArray = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    isArray(inType.complexType)
                  end

                  DAE.T_FUNCTION(__)  => begin
                    isArray(inType.funcResultType)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsArray
        end

        function isEmptyArray(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inType begin
                  DAE.T_ARRAY(dims = DAE.DIM_INTEGER(0) <|  nil())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if Type is the builtin String type. =#
        function isString(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inType begin
                  DAE.T_STRING(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if Type is the builtin String type. =#
        function isEnumeration(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match arrayElementType(inType) begin
                  DAE.T_ENUMERATION(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return true if Type is array or the builtin String type. =#
        function isArrayOrString(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local ty::Type
                @match inType begin
                  ty where (isArray(ty))  => begin
                    true
                  end

                  ty where (isString(ty))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Return the number of dimensions of a Type. =#
        function numberOfDimensions(inType::DAE.Type) ::ModelicaInteger
              local outInteger::ModelicaInteger

              outInteger = begin
                  local n::ModelicaInteger
                  local t::Type
                  local dims::DAE.Dimensions
                @matchcontinue inType begin
                  DAE.T_ARRAY(ty = t, dims = dims)  => begin
                      n = numberOfDimensions(t)
                      n = n + listLength(dims)
                    n
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                      n = numberOfDimensions(t)
                    n
                  end

                  _  => begin
                      0
                  end
                end
              end
          outInteger
        end

         #= Returns true if the dimensions of the type is known. =#
        function dimensionsKnown(inType::DAE.Type) ::Bool
              local outRes::Bool

              outRes = begin
                  local d::DAE.Dimension
                  local dims::DAE.Dimensions
                  local tp::Type
                @matchcontinue inType begin
                  DAE.T_ARRAY(dims = d <| dims, ty = tp)  => begin
                      @match true = Expression.dimensionKnown(d)
                      @match true = dimensionsKnown(DAE.T_ARRAY(tp, dims))
                    true
                  end

                  DAE.T_ARRAY(dims =  nil(), ty = tp)  => begin
                      @match true = dimensionsKnown(tp)
                    true
                  end

                  DAE.T_ARRAY(__)  => begin
                    false
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = tp)  => begin
                    dimensionsKnown(tp)
                  end

                  _  => begin
                      true
                  end
                end
              end
          outRes
        end

         #= Return the dimension sizes of a Type. =#
        function getDimensionSizes(inType::DAE.Type) ::List{ModelicaInteger}
              local outIntegerLst::List{ModelicaInteger}

              outIntegerLst = begin
                  local res::List{ModelicaInteger}
                  local d::DAE.Dimension
                  local dims::DAE.Dimensions
                  local i::ModelicaInteger
                  local tp::Type
                @matchcontinue inType begin
                  DAE.T_ARRAY(dims = d <| dims, ty = tp)  => begin
                      i = Expression.dimensionSize(d)
                      res = getDimensionSizes(DAE.T_ARRAY(tp, dims))
                    _cons(i, res)
                  end

                  DAE.T_ARRAY(dims = _ <| dims, ty = tp)  => begin
                      res = getDimensionSizes(DAE.T_ARRAY(tp, dims))
                    _cons(0, res)
                  end

                  DAE.T_ARRAY(dims =  nil(), ty = tp)  => begin
                      res = getDimensionSizes(tp)
                    res
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = tp)  => begin
                    getDimensionSizes(tp)
                  end

                  _  => begin
                        @match false = arrayType(inType)
                      nil
                  end
                end
              end
          outIntegerLst
        end

         #= Return the dimension sizes of a Type. =#
        function getDimensionProduct(inType::DAE.Type) ::ModelicaInteger
              local sz::ModelicaInteger

              sz = begin
                  local res::List{ModelicaInteger}
                  local dims::DAE.Dimensions
                  local i::ModelicaInteger
                  local tp::Type
                @match inType begin
                  DAE.T_ARRAY(dims = dims, ty = tp)  => begin
                    product(Expression.dimensionSize(d) for d in dims) * getDimensionProduct(tp)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = tp)  => begin
                    getDimensionProduct(tp)
                  end

                  _  => begin
                        @match false = arrayType(inType)
                      1
                  end
                end
              end
          sz
        end

         #= Returns the dimensions of a Type. =#
        function getDimensions(inType::DAE.Type) ::DAE.Dimensions
              local outDimensions::DAE.Dimensions

              outDimensions = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    listAppend(inType.dims, getDimensions(inType.ty))
                  end

                  DAE.T_METAARRAY(__)  => begin
                    _cons(DAE.DIM_UNKNOWN(), getDimensions(inType.ty))
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    getDimensions(inType.complexType)
                  end

                  DAE.T_METATYPE(__)  => begin
                    getDimensions(inType.ty)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outDimensions
        end

        function getDimensionNth(inType::DAE.Type, inDim::ModelicaInteger) ::DAE.Dimension
              local outDimension::DAE.Dimension

              outDimension = begin
                  local dim::DAE.Dimension
                  local t::DAE.Type
                  local d::ModelicaInteger
                  local dc::ModelicaInteger
                  local dims::DAE.Dimensions
                @matchcontinue (inType, inDim) begin
                  (DAE.T_ARRAY(dims = dims), d)  => begin
                      dim = listGet(dims, d)
                    dim
                  end

                  (DAE.T_ARRAY(ty = t, dims = dims), d)  => begin
                      dc = listLength(dims)
                      @match true = d > dc
                    getDimensionNth(t, d - dc)
                  end

                  (DAE.T_SUBTYPE_BASIC(complexType = t), d)  => begin
                    getDimensionNth(t, d)
                  end
                end
              end
          outDimension
        end

         #= Sets the nth dimension of an array type to the given dimension. =#
        function setDimensionNth(inType::DAE.Type, inDim::DAE.Dimension, inDimNth::ModelicaInteger) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local dim::DAE.Dimension
                  local ty::DAE.Type
                @match (inType, inDim, inDimNth) begin
                  (DAE.T_ARRAY(dims = _ <|  nil(), ty = ty), _, 1)  => begin
                    DAE.T_ARRAY(ty, list(inDim))
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = ty), _, _)  => begin
                      @match true = inDimNth > 1
                      ty = setDimensionNth(ty, inDim, inDimNth - 1)
                    DAE.T_ARRAY(ty, list(dim))
                  end
                end
              end
          outType
        end

         #= Prints dimensions to a string =#
        function printDimensionsStr(dims::DAE.Dimensions) ::String
              local res::String

              res = stringDelimitList(ListUtil.map(dims, ExpressionDump.dimensionString), ", ")
          res
        end

         #= Translates a list of Values.Value to a Var list, using a list
          of identifiers as component names.
          Used e.g. when retrieving the type of a record value. =#
        function valuesToVars(inValuesValueLst::List{<:Values.Value}, inExpIdentLst::List{<:DAE.Ident}) ::List{DAE.Var}
              local outVarLst::List{DAE.Var}

              outVarLst = begin
                  local tp::Type
                  local rest::List{DAE.Var}
                  local v::Values.Value
                  local vs::List{Values.Value}
                  local id::String
                  local ids::List{String}
                @matchcontinue (inValuesValueLst, inExpIdentLst) begin
                  ( nil(),  nil())  => begin
                    nil
                  end

                  (v <| vs, id <| ids)  => begin
                      tp = typeOfValue(v)
                      rest = valuesToVars(vs, ids)
                    _cons(DAE.TYPES_VAR(id, DAE.dummyAttrVar, tp, DAE.UNBOUND(), NONE()), rest)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("-values_to_vars failed\\n")
                      fail()
                  end
                end
              end
          outVarLst
        end

         #= author: PA
          Returns the type of a Values.Value.
          Some information is lost in the translation, like attributes
          of the builtin type. =#
        function typeOfValue(inValue::Values.Value) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local tp::Type
                  local dim1::ModelicaInteger
                  local index::ModelicaInteger
                  local w::Values.Value
                  local v::Values.Value
                  local vs::List{Values.Value}
                  local vl::List{Values.Value}
                  local ts::List{DAE.Type}
                  local vars::List{DAE.Var}
                  local str::String
                  local cname::Absyn.Path
                  local path::Absyn.Path
                  local utPath::Absyn.Path
                  local ids::List{String}
                  local explist::List{DAE.Exp}
                  local valType::Values.Value
                @matchcontinue inValue begin
                  Values.EMPTY(ty = valType)  => begin
                    typeOfValue(valType)
                  end

                  Values.INTEGER(__)  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  Values.REAL(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  Values.STRING(__)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  Values.BOOL(__)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  Values.ENUM_LITERAL(name = path, index = index)  => begin
                      path = AbsynUtil.pathPrefix(path)
                    DAE.T_ENUMERATION(SOME(index), path, nil, nil, nil)
                  end

                  Values.ARRAY(valueLst = v <| vs)  => begin
                      tp = typeOfValue(v)
                      dim1 = listLength(_cons(v, vs))
                    DAE.T_ARRAY(tp, list(DAE.DIM_INTEGER(dim1)))
                  end

                  Values.ARRAY(valueLst =  nil())  => begin
                    DAE.T_ARRAY(DAE.T_UNKNOWN_DEFAULT, list(DAE.DIM_INTEGER(0)))
                  end

                  Values.TUPLE(valueLst = vs)  => begin
                      ts = ListUtil.map(vs, typeOfValue)
                    DAE.T_TUPLE(ts, NONE())
                  end

                  Values.RECORD(record_ = cname, orderd = vl, comp = ids, index = -1)  => begin
                      vars = valuesToVars(vl, ids)
                    DAE.T_COMPLEX(ClassInf.RECORD(cname), vars, NONE())
                  end

                  Values.RECORD(record_ = cname, orderd = vl, comp = ids, index = index)  => begin
                      @match true = index >= 0
                      vars = valuesToVars(vl, ids)
                      utPath = AbsynUtil.stripLast(cname)
                    DAE.T_METARECORD(cname, utPath, nil, index, vars, false)
                  end

                  Values.LIST(vl)  => begin
                      explist = ListUtil.map(vl, ValuesUtil.valueExp)
                      ts = ListUtil.map(vl, typeOfValue)
                      (_, tp) = listMatchSuperType(explist, ts, true)
                      tp = boxIfUnboxedType(tp)
                    DAE.T_METALIST(tp)
                  end

                  Values.OPTION(NONE())  => begin
                      tp = DAE.T_METAOPTION(DAE.T_UNKNOWN_DEFAULT)
                    tp
                  end

                  Values.OPTION(SOME(v))  => begin
                      tp = boxIfUnboxedType(typeOfValue(v))
                      tp = DAE.T_METAOPTION(tp)
                    tp
                  end

                  Values.META_TUPLE(valueLst = vs)  => begin
                      ts = ListUtil.mapMap(vs, typeOfValue, boxIfUnboxedType)
                    DAE.T_METATUPLE(ts)
                  end

                  Values.META_ARRAY(valueLst = v <| vs)  => begin
                      tp = boxIfUnboxedType(typeOfValue(v))
                      tp = DAE.T_METAARRAY(tp)
                    tp
                  end

                  Values.META_ARRAY(valueLst =  nil())  => begin
                      tp = DAE.T_METAARRAY(DAE.T_UNKNOWN_DEFAULT)
                    tp
                  end

                  Values.META_BOX(v)  => begin
                      tp = typeOfValue(v)
                    boxIfUnboxedType(tp)
                  end

                  Values.NORETCALL(__)  => begin
                    DAE.T_NORETCALL_DEFAULT
                  end

                  Values.CODE(A = Absyn.C_TYPENAME(__))  => begin
                    DAE.T_CODE(DAE.C_TYPENAME())
                  end

                  Values.CODE(A = Absyn.C_VARIABLENAME(__))  => begin
                    DAE.T_CODE(DAE.C_VARIABLENAME())
                  end

                  Values.CODE(A = Absyn.C_EXPRESSION(__))  => begin
                    DAE.T_CODE(DAE.C_EXPRESSION())
                  end

                  Values.CODE(A = Absyn.C_MODIFICATION(__))  => begin
                    DAE.T_CODE(DAE.C_MODIFICATION())
                  end

                  v  => begin
                      str = "- Types.typeOfValue failed: " + ValuesUtil.valString(v)
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #=  MetaModelica Uniontype
               =#
               #= /* typeVar? */ =#
               #= /*We simply do not know...*/ =#
               #=  MetaModelica list type
               =#
          outType
        end

         #= Test whether a type is one of the builtin types. =#
        function basicType(inType::DAE.Type) ::Bool
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

                  DAE.T_ENUMERATION(__)  => begin
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

         #= Test whether a type extends one of the builtin types. =#
        function extendsBasicType(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inType begin
                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns the actual type of a type extending one of the builtin types. =#
        function derivedBasicType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inType begin
                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    derivedBasicType(inType.complexType)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

         #= Test whether a type is an array type. =#
        function arrayType(inType::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Sets a DAE.Var to input =#
        function setVarInput(var::DAE.Var) ::DAE.Var
              local outV::DAE.Var

              outV = begin
                  local name::String
                  local ct::DAE.ConnectorType
                  local vis::SCode.Visibility
                  local tp::DAE.Type
                  local bind::DAE.Binding
                  local prl::SCode.Parallelism
                  local v::SCode.Variability
                  local io::Absyn.InnerOuter
                  local cnstForRange::Option{DAE.Const}
                @match var begin
                  DAE.TYPES_VAR(name, DAE.ATTR(ct, prl, v, _, io, vis), tp, bind, cnstForRange)  => begin
                    DAE.TYPES_VAR(name, DAE.ATTR(ct, prl, v, Absyn.INPUT(), io, vis), tp, bind, cnstForRange)
                  end
                end
              end
          outV
        end

         #= Sets a DAE.Var to input =#
        function setVarDefaultInput(var::DAE.Var) ::DAE.Var
              local outV::DAE.Var

              outV = begin
                  local name::String
                  local ct::SCode.ConnectorType
                  local vis::SCode.Visibility
                  local tp::DAE.Type
                  local bind::DAE.Binding
                  local prl::SCode.Parallelism
                  local v::SCode.Variability
                  local io::Absyn.InnerOuter
                  local cnstForRange::Option{DAE.Const}
                @match var begin
                  DAE.TYPES_VAR(name, DAE.ATTR(_, prl, _, _, _, _), tp, bind, cnstForRange)  => begin
                    DAE.TYPES_VAR(name, DAE.ATTR(DAE.NON_CONNECTOR(), prl, SCode.VAR(), Absyn.INPUT(), Absyn.NOT_INNER_OUTER(), SCode.PUBLIC()), tp, bind, cnstForRange)
                  end
                end
              end
          outV
        end

         #= Sets a DAE.Var to input =#
        function setVarProtected(var::DAE.Var) ::DAE.Var
              local outV::DAE.Var

              outV = begin
                  local name::String
                  local ct::DAE.ConnectorType
                  local dir::Absyn.Direction
                  local tp::DAE.Type
                  local bind::DAE.Binding
                  local prl::SCode.Parallelism
                  local v::SCode.Variability
                  local io::Absyn.InnerOuter
                  local cnstForRange::Option{DAE.Const}
                @match var begin
                  DAE.TYPES_VAR(name, DAE.ATTR(ct, prl, v, dir, io, _), tp, bind, cnstForRange)  => begin
                    DAE.TYPES_VAR(name, DAE.ATTR(ct, prl, v, dir, io, SCode.PROTECTED()), tp, bind, cnstForRange)
                  end
                end
              end
          outV
        end

         #= Sets a DAE.Var's type =#
        function setVarType(var::DAE.Var, ty::DAE.Type) ::DAE.Var
              local outV::DAE.Var = var

              outV = begin
                @match outV begin
                  DAE.TYPES_VAR(__)  => begin
                      outV.ty = ty
                    outV
                  end
                end
              end
          outV
        end

         #= This function checks whether two types are semi-equal...
           With 'semi' we mean that they have the same base type, and if both are arrays
           the numbers of dimensions are equal, not necessarily equal dimension-sizes. =#
        function semiEquivTypes(inType1::DAE.Type, inType2::DAE.Type) ::Bool
              local outEquiv::Bool

              local ty1::DAE.Type
              local ty2::DAE.Type
              local dims1::List{DAE.Dimension}
              local dims2::List{DAE.Dimension}

              if arrayType(inType1) && arrayType(inType2)
                (ty1, dims1) = flattenArrayType(inType1)
                (ty2, dims2) = flattenArrayType(inType2)
                outEquiv = equivtypes(inType1, inType2) && listLength(dims1) == listLength(dims2)
              elseif ! arrayType(inType1) && ! arrayType(inType2)
                outEquiv = equivtypes(inType1, inType2)
              else
                outEquiv = false
              end
          outEquiv
        end

         #= This is the type equivalence function.  It is defined in terms of
          the subtype function.  Two types are considered equivalent if they
          are subtypes of each other. =#
        function equivtypes(t1::DAE.Type, t2::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = subtype(t1, t2) && subtype(t2, t1)
          outBoolean
        end

         #= Like equivtypes but accepts non-typeconverted records as well (for connections). =#
        function equivtypesOrRecordSubtypeOf(t1::DAE.Type, t2::DAE.Type) ::Bool
              local outBoolean::Bool

              outBoolean = subtype(t1, t2, false) && subtype(t2, t1, false)
               #= /* Allow record names to differ */ =#
          outBoolean
        end

         #= Is the first type a subtype of the second type?
          This function specifies the rules for subtyping in Modelica. =#
        function subtype(inType1::DAE.Type, inType2::DAE.Type, requireRecordNamesEqual::Bool = true) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local res::Bool
                  local b1::Bool
                  local b2::Bool
                  local l1::String
                  local l2::String
                  local els1::List{DAE.Var}
                  local els2::List{DAE.Var}
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local tp2::DAE.Type
                  local tp1::DAE.Type
                  local st1::ClassInf.SMNode
                  local st2::ClassInf.SMNode
                  local type_list1::List{DAE.Type}
                  local type_list2::List{DAE.Type}
                  local tList1::List{DAE.Type}
                  local tList2::List{DAE.Type}
                  local names1::List{String}
                  local names2::List{String}
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local dlst1::DAE.Dimensions
                  local dlst2::DAE.Dimensions
                  local farg1::List{DAE.FuncArg}
                  local farg2::List{DAE.FuncArg}
                  local c1::DAE.CodeType
                  local c2::DAE.CodeType
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                @matchcontinue (inType1, inType2) begin
                  (DAE.T_ANYTYPE(__), _)  => begin
                    true
                  end

                  (_, DAE.T_ANYTYPE(__))  => begin
                    true
                  end

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

                  (DAE.T_ENUMERATION(names =  nil()), DAE.T_ENUMERATION(__))  => begin
                    true
                  end

                  (DAE.T_ENUMERATION(__), DAE.T_ENUMERATION(names =  nil()))  => begin
                    true
                  end

                  (DAE.T_ENUMERATION(names = names1), DAE.T_ENUMERATION(names = names2))  => begin
                      res = ListUtil.isEqualOnTrue(names1, names2, stringEq)
                    res
                  end

                  (DAE.T_ARRAY(dims = dlst1 && _ <| _ <| _, ty = t1), DAE.T_ARRAY(dims = dlst2 && _ <| _ <| _, ty = t2))  => begin
                      @match true = Expression.dimsEqual(dlst1, dlst2)
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = dim1 <|  nil(), ty = t1), DAE.T_ARRAY(dims = dim2 <| dlst2 && _ <| _, ty = t2))  => begin
                      @match true = Expression.dimensionsEqual(dim1, dim2)
                      @match true = subtype(t1, DAE.T_ARRAY(t2, dlst2), requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = dim1 <| dlst1 && _ <| _, ty = t1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = t2))  => begin
                      @match true = Expression.dimensionsEqual(dim1, dim2)
                      @match true = subtype(DAE.T_ARRAY(t1, dlst1), t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(ty = t1), DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = t2))  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = t1), DAE.T_ARRAY(ty = t2))  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil(), ty = t1), DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil(), ty = t2))  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(ty = t1), DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil(), ty = t2))  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil(), ty = t1), DAE.T_ARRAY(ty = t2))  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_ARRAY(dims = dim1 <|  nil(), ty = t1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = t2))  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(p1)), DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(p2)))  => begin
                    AbsynUtil.pathEqual(p1, p2)
                  end

                  (DAE.T_COMPLEX(complexClassType = st1, varLst = els1), DAE.T_COMPLEX(complexClassType = st2, varLst = els2))  => begin
                      @match true = classTypeEqualIfRecord(st1, st2) || ! requireRecordNamesEqual #= We need to add a cast from one record to another =#
                      @match true = listLength(els1) == listLength(els2)
                      @match true = subtypeVarlist(els1, els2)
                    true
                  end

                  (DAE.T_SUBTYPE_BASIC(complexType = tp1), tp2)  => begin
                      res = subtype(tp1, tp2, requireRecordNamesEqual)
                    res
                  end

                  (tp1, DAE.T_SUBTYPE_BASIC(complexType = tp2))  => begin
                      res = subtype(tp1, tp2, requireRecordNamesEqual)
                    res
                  end

                  (DAE.T_TUPLE(types = type_list1), DAE.T_TUPLE(types = type_list2))  => begin
                      @match true = subtypeTypelist(type_list1, type_list2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_METALIST(ty = t1), DAE.T_METALIST(ty = t2))  => begin
                    subtype(t1, t2)
                  end

                  (DAE.T_METAARRAY(ty = t1), DAE.T_METAARRAY(ty = t2))  => begin
                    subtype(t1, t2)
                  end

                  (DAE.T_METATUPLE(types = tList1), DAE.T_METATUPLE(types = tList2))  => begin
                      res = subtypeTypelist(tList1, tList2, requireRecordNamesEqual)
                    res
                  end

                  (DAE.T_METAOPTION(ty = t1), DAE.T_METAOPTION(ty = t2))  => begin
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (DAE.T_METABOXED(ty = t1), DAE.T_METABOXED(ty = t2))  => begin
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (DAE.T_METABOXED(ty = t1), t2)  => begin
                      @match true = isBoxedType(t2)
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (t1, DAE.T_METABOXED(ty = t2))  => begin
                      @match true = isBoxedType(t1)
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (DAE.T_METAPOLYMORPHIC(name = l1), DAE.T_METAPOLYMORPHIC(name = l2))  => begin
                    l1 == l2
                  end

                  (DAE.T_UNKNOWN(__), _)  => begin
                    true
                  end

                  (_, DAE.T_UNKNOWN(__))  => begin
                    true
                  end

                  (DAE.T_NORETCALL(__), DAE.T_NORETCALL(__))  => begin
                    true
                  end

                  (DAE.T_FUNCTION(funcArg = farg1, funcResultType = t1), DAE.T_FUNCTION(funcArg = farg2, funcResultType = t2))  => begin
                      tList1 = list(traverseType(funcArgType(t), 1, unboxedTypeTraverseHelper) for t in farg1)
                      tList2 = list(traverseType(funcArgType(t), 1, unboxedTypeTraverseHelper) for t in farg2)
                      t1 = traverseType(t1, 1, unboxedTypeTraverseHelper)
                      t2 = traverseType(t2, 1, unboxedTypeTraverseHelper)
                      @match true = subtypeTypelist(tList1, tList2, requireRecordNamesEqual)
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    true
                  end

                  (DAE.T_FUNCTION_REFERENCE_VAR(functionType = t1), DAE.T_FUNCTION_REFERENCE_VAR(functionType = t2))  => begin
                    subtype(t1, t2)
                  end

                  (DAE.T_METARECORD(path = p1), DAE.T_METARECORD(path = p2))  => begin
                    AbsynUtil.pathEqual(p1, p2)
                  end

                  (DAE.T_METAUNIONTYPE(path = p1), DAE.T_METARECORD(utPath = p2))  => begin
                    if AbsynUtil.pathEqual(p1, p2)
                          subtypeTypelist(inType1.typeVars, inType2.typeVars, requireRecordNamesEqual)
                        else
                          false
                        end
                  end

                  (DAE.T_METARECORD(knownSingleton = b1, utPath = p1), DAE.T_METAUNIONTYPE(knownSingleton = b2, path = p2))  => begin
                    if AbsynUtil.pathEqual(p1, p2) && (b1 || b2)
                          subtypeTypelist(inType1.typeVars, inType2.typeVars, requireRecordNamesEqual)
                        else
                          false
                        end
                  end

                  (DAE.T_METAUNIONTYPE(path = p1), DAE.T_METAUNIONTYPE(path = p2))  => begin
                    if AbsynUtil.pathEqual(p1, p2)
                          subtypeTypelist(inType1.typeVars, inType2.typeVars, requireRecordNamesEqual)
                        else
                          false
                        end
                  end

                  (DAE.T_CODE(ty = c1), DAE.T_CODE(ty = c2))  => begin
                    valueEq(c1, c2)
                  end

                  (DAE.T_METATYPE(ty = t1), DAE.T_METATYPE(ty = t2))  => begin
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (t1, DAE.T_METATYPE(ty = t2))  => begin
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  (DAE.T_METATYPE(ty = t1), t2)  => begin
                    subtype(t1, t2, requireRecordNamesEqual)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
               #=  try dims as list vs. dims as tree
               =#
               #=  T_ARRAY(a::b::c) vs. T_ARRAY(a, T_ARRAY(b, T_ARRAY(c)))
               =#
               #=  try subtype of dimension list vs. dimension tree
               =#
               #= /* HUGE TODO: FIXME: After MSL is updated? */ =#
               #=  true = Expression.expEqual(e1,e2);
               =#
               #=  Array
               =#
               #= /*
                      true = boolOr(Expression.dimensionsKnownAndEqual(dim1, dim2),
                                    Expression.dimensionsEqualAllowZero(dim1, dim2));
                      */ =#
               #=  External objects use a nominal type system
               =#
               #=  Complex type
               =#
               #=  A complex type that extends a basic type is checked against the baseclass basic type
               =#
               #=  A complex type that extends a basic type is checked against the baseclass basic type
               =#
               #=  Check of tuples, similar to complex. Just that identifier name do not have to be checked. Only types are checked.
               =#
               #=  Part of MetaModelica extension. KS
               =#
               #=  MM Function Reference
               =#
               #=  If the record is the only one in the uniontype, of course their types match
               =#
               #= /*Values.mo loses knownSingleton information */ =#
               #=  <uniontype> = <uniontype>
               =#
               #= /*case (DAE.T_METAUNIONTYPE(path = p1), DAE.T_COMPLEX(complexClassType=ClassInf.META_UNIONTYPE(_), source = {p2}))
                    then AbsynUtil.pathEqual(p1,p2);  TODO: Remove?
                  case(DAE.T_COMPLEX(complexClassType=ClassInf.META_UNIONTYPE(_), source = {p2}), DAE.T_METAUNIONTYPE(path = p1))
                    then AbsynUtil.pathEqual(p1,p2);  TODO: Remove?*/ =#
               #= /* Uncomment for debugging
                      l1 = unparseType(t1);
                      l2 = unparseType(t2);
                      l1 = stringAppendList({\"- Types.subtype failed:\\n  t1=\",l1,\"\\n  t2=\",l2});
                      print(l1);
                      */ =#
          outBoolean
        end

         #= PR. function: subtypeTypelist
          This function checks if the both Type lists matches types, element by element. =#
        function subtypeTypelist(inTypeLst1::List{<:DAE.Type}, inTypeLst2::List{<:DAE.Type}, requireRecordNamesEqual::Bool) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local t1::Type
                  local t2::Type
                  local rest1::List{DAE.Type}
                  local rest2::List{DAE.Type}
                @matchcontinue (inTypeLst1, inTypeLst2, requireRecordNamesEqual) begin
                  ( nil(),  nil(), _)  => begin
                    true
                  end

                  (t1 <| rest1, t2 <| rest2, _)  => begin
                      @match true = subtype(t1, t2, requireRecordNamesEqual)
                    subtypeTypelist(rest1, rest2, requireRecordNamesEqual)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #= /* default */ =#
          outBoolean
        end

         #= This function checks if the Var list in the first list is a
          subset of the list in the second argument.  More precisely, it
          checks if, for each Var in the second list there is a Var in
          the first list with a type that is a subtype of the Var in the
          second list. =#
        function subtypeVarlist(inVarLst1::List{<:DAE.Var}, inVarLst2::List{<:DAE.Var}) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local l::List{DAE.Var}
                  local vs::List{DAE.Var}
                  local n::String
                @matchcontinue (inVarLst1, inVarLst2) begin
                  (_,  nil())  => begin
                    true
                  end

                  (l, DAE.TYPES_VAR(name = n, ty = t2) <| vs)  => begin
                      @match DAE.TYPES_VAR(ty = t1) = varlistLookup(l, n)
                      @match true = subtype(t1, t2, false)
                    subtypeVarlist(l, vs)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #= /* default */ =#
          outBoolean
        end

         #= Given a list of Var and a name, this function finds any Var with the given name. =#
        function varlistLookup(inVarLst::List{<:DAE.Var}, inIdent::String) ::DAE.Var
              local outVar::DAE.Var

              local name::String

              for var in inVarLst
                @match DAE.TYPES_VAR(name = name) = var
                if name == inIdent
                  outVar = var
                  return outVar
                end
              end
              fail()
          outVar
        end

         #= This function finds a subcomponent by name. =#
        function lookupComponent(inType::DAE.Type, inIdent::String) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local v::DAE.Var
                  local t::DAE.Type
                  local ty::DAE.Type
                  local ty_1::DAE.Type
                  local n::String
                  local id::String
                  local st::ClassInf.SMNode
                  local cs::List{DAE.Var}
                  local bc::Option{DAE.Type}
                  local attr::DAE.Attributes
                  local bnd::DAE.Binding
                  local dim::DAE.Dimension
                  local cnstForRange::Option{DAE.Const}
                @matchcontinue (inType, inIdent) begin
                  (t, n)  => begin
                      @match true = basicType(t)
                      v = lookupInBuiltin(t, n)
                    v
                  end

                  (DAE.T_COMPLEX(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_SUBTYPE_BASIC(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = DAE.T_COMPLEX(varLst = cs)), id)  => begin
                      @match DAE.TYPES_VAR(n, attr, ty, bnd, cnstForRange) = lookupComponent2(cs, id)
                      ty_1 = DAE.T_ARRAY(ty, list(dim))
                    DAE.TYPES_VAR(n, attr, ty_1, bnd, cnstForRange)
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = DAE.T_SUBTYPE_BASIC(varLst = cs)), id)  => begin
                      @match DAE.TYPES_VAR(n, attr, ty, bnd, cnstForRange) = lookupComponent2(cs, id)
                      ty_1 = DAE.T_ARRAY(ty, list(dim))
                    DAE.TYPES_VAR(n, attr, ty_1, bnd, cnstForRange)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  Print.printBuf(\"- Looking up \" + id + \" in noncomplex type\\n\");
               =#
          outVar
        end

         #= Since builtin types are not represented as DAE.T_COMPLEX, special care
          is needed to be able to lookup the attributes (*start* etc) in
          them.

          This is not a complete solution.  The current way of mapping the
          both the Modelica type Real and the simple type RealType to
          DAE.T_REAL is a bit problematic, since it does not make a
          difference between Real and RealType, which makes the
          translator accept things like x.start.start.start. =#
        function lookupInBuiltin(inType::DAE.Type, inIdent::String) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local v::DAE.Var
                  local cs::List{DAE.Var}
                  local id::String
                @match (inType, inIdent) begin
                  (DAE.T_REAL(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_INTEGER(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_STRING(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_BOOL(varLst = cs), id)  => begin
                      v = lookupComponent2(cs, id)
                    v
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "quantity")  => begin
                    DAE.TYPES_VAR("quantity", DAE.dummyAttrParam, DAE.T_STRING_DEFAULT, DAE.VALBOUND(Values.STRING(""), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "min")  => begin
                    DAE.TYPES_VAR("min", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(1), Absyn.IDENT(""), list("min,max"), nil, nil), DAE.UNBOUND(), NONE())
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "max")  => begin
                    DAE.TYPES_VAR("max", DAE.dummyAttrParam, DAE.T_ENUMERATION(SOME(2), Absyn.IDENT(""), list("min,max"), nil, nil), DAE.UNBOUND(), NONE())
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "start")  => begin
                    DAE.TYPES_VAR("start", DAE.dummyAttrParam, DAE.T_BOOL_DEFAULT, DAE.UNBOUND(), NONE())
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "fixed")  => begin
                    DAE.TYPES_VAR("fixed", DAE.dummyAttrParam, DAE.T_BOOL_DEFAULT, DAE.UNBOUND(), NONE())
                  end

                  (DAE.T_ENUMERATION(index = SOME(_)), "enable")  => begin
                    DAE.TYPES_VAR("enable", DAE.dummyAttrParam, DAE.T_BOOL_DEFAULT, DAE.VALBOUND(Values.BOOL(true), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end
                end
              end
               #= /* Real */ =#
               #=  Should be bound to the first element of DAE.T_ENUMERATION list higher up in the call chain
               =#
               #=  Should be bound to the last element of DAE.T_ENUMERATION list higher up in the call chain
               =#
               #=  Should be bound to the last element of DAE.T_ENUMERATION list higher up in the call chain
               =#
               #=  Needs to be set to true/false higher up the call chain depending on variability of instance
               =#
          outVar
        end

         #= This function finds a named Var in a list of Vars, comparing
          the name against the second argument to this function. =#
        function lookupComponent2(inVarLst::List{<:DAE.Var}, inIdent::String) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local v::DAE.Var
                  local n::String
                  local m::String
                  local vs::List{DAE.Var}
                @matchcontinue (inVarLst, inIdent) begin
                  (v && DAE.TYPES_VAR(name = n) <| _, m)  => begin
                      @match true = stringEq(n, m)
                    v
                  end

                  (_ <| vs, n)  => begin
                      v = lookupComponent2(vs, n)
                    v
                  end
                end
              end
          outVar
        end

         #= This function makes an array type given a Type and an Absyn.ArrayDim =#
        function makeArray(inType::DAE.Type, inArrayDim::Absyn.ArrayDim) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::Type
                  local len::ModelicaInteger
                  local l::List{Absyn.Subscript}
                @matchcontinue (inType, inArrayDim) begin
                  (t,  nil())  => begin
                    t
                  end

                  (t, l)  => begin
                      len = listLength(l)
                    DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(len)))
                  end
                end
              end
          outType
        end

         #=  This function makes an array type given a Type and a list of DAE.Subscript =#
        function makeArraySubscripts(inType::DAE.Type, lst::List{<:DAE.Subscript}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::Type
                  local i::ModelicaInteger
                  local e::DAE.Exp
                  local rest::List{DAE.Subscript}
                @matchcontinue (inType, lst) begin
                  (t,  nil())  => begin
                    t
                  end

                  (t, DAE.WHOLEDIM(__) <| rest)  => begin
                      t = makeArraySubscripts(DAE.T_ARRAY(t, list(DAE.DIM_UNKNOWN())), rest)
                    t
                  end

                  (t, DAE.SLICE(_) <| rest)  => begin
                      t = makeArraySubscripts(DAE.T_ARRAY(t, list(DAE.DIM_UNKNOWN())), rest)
                    t
                  end

                  (t, DAE.WHOLE_NONEXP(_) <| rest)  => begin
                      t = makeArraySubscripts(DAE.T_ARRAY(t, list(DAE.DIM_UNKNOWN())), rest)
                    t
                  end

                  (t, DAE.INDEX(DAE.ICONST(i)) <| rest)  => begin
                      t = makeArraySubscripts(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(i))), rest)
                    t
                  end

                  (t, DAE.INDEX(_) <| rest)  => begin
                      t = makeArraySubscripts(DAE.T_ARRAY(t, list(DAE.DIM_UNKNOWN())), rest)
                    t
                  end
                end
              end
          outType
        end

         #= This function turns a type into an array of that type.
          If the type already is an array, another dimension is simply added. =#
        function liftArray(inType::DAE.Type, inDimension::DAE.Dimension) ::DAE.Type
              local outType::DAE.Type

              outType = DAE.T_ARRAY(inType, list(inDimension))
          outType
        end

         #= This function turns a type into a list of that type.
          If the type already is a list, another dimension is simply added. =#
        function liftList(inType::DAE.Type, inDimension::DAE.Dimension) ::DAE.Type
              local outType::DAE.Type

              outType = DAE.T_METALIST(inType)
          outType
        end

         #=
          This function turns a type into an array of that type. =#
        function liftArrayListDims(inType::DAE.Type, inDimensions::DAE.Dimensions) ::DAE.Type
              local outType::DAE.Type = inType

              for dim in listReverse(inDimensions)
                outType = DAE.T_ARRAY(outType, list(dim))
              end
          outType
        end

         #= Turns a type into an array of that type, with the dimensions in the reverse order. =#
        function liftArrayListDimsReverse(inType::DAE.Type, dims::DAE.Dimensions) ::DAE.Type
              local ty::DAE.Type = inType

              for dim in dims
                ty = DAE.T_ARRAY(ty, list(dim))
              end
          ty
        end

         #=
          mahge: This function turns a type into an array of that type
          by appening the new dimension at the end.  =#
        function liftTypeWithDims(inType::DAE.Type, inDims::DAE.Dimensions) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local dims::List{DAE.Dimension}
                  local dims_::List{DAE.Dimension}
                  local ty::DAE.Type
                @match inType begin
                  DAE.T_ARRAY(ty = DAE.T_ARRAY(__))  => begin
                      print("Can not handle this yet!!")
                    fail()
                  end

                  DAE.T_ARRAY(ty, dims)  => begin
                      dims_ = listAppend(dims, inDims)
                    if referenceEq(dims, dims_)
                          inType
                        else
                          DAE.T_ARRAY(ty, dims_)
                        end
                  end

                  _  => begin
                      DAE.T_ARRAY(inType, inDims)
                  end
                end
              end
          outType
        end

         #=
          This function turns a type into an array of that type. =#
        function liftArrayListExp(inType::DAE.Type, inDimensionLst::List{<:DAE.Exp}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local d::DAE.Exp
                  local rest::List{DAE.Exp}
                @match (inType, inDimensionLst) begin
                  (ty,  nil())  => begin
                    ty
                  end

                  (ty, d <| rest)  => begin
                    liftArray(liftArrayListExp(ty, rest), DAE.DIM_EXP(d))
                  end
                end
              end
          outType
        end

         #= This function adds an array dimension to *the right* of the passed type. =#
        function liftArrayRight(inType::DAE.Type, inIntegerOption::DAE.Dimension) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty_1::Type
                  local ty::Type
                  local dim::DAE.Dimension
                  local d::DAE.Dimension
                  local ci::ClassInf.SMNode
                  local varlst::List{DAE.Var}
                  local ec::EqualityConstraint
                  local tty::Type
                @matchcontinue (inType, inIntegerOption) begin
                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = ty), d)  => begin
                      ty_1 = liftArrayRight(ty, d)
                    DAE.T_ARRAY(ty_1, list(dim))
                  end

                  (DAE.T_SUBTYPE_BASIC(ci, varlst, ty, ec), d)  => begin
                      @match false = listEmpty(getDimensions(ty))
                      ty_1 = liftArrayRight(ty, d)
                    DAE.T_SUBTYPE_BASIC(ci, varlst, ty_1, ec)
                  end

                  (tty, d)  => begin
                    DAE.T_ARRAY(tty, list(d))
                  end
                end
              end
          outType
        end

         #= This function turns an array of a type into that type. =#
        function unliftArray(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                @match inType begin
                  DAE.T_ARRAY(ty = ty)  => begin
                    ty
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    unliftArray(ty)
                  end

                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    unliftArray(ty)
                  end
                end
              end
               #=  adrpo: handle also functions returning arrays!
               =#
          outType
        end

        function unliftArrayOrList(inType::DAE.Type) ::Tuple{DAE.Type, DAE.Dimension}
              local dim::DAE.Dimension
              local outType::DAE.Type

              (outType, dim) = begin
                  local ty::Type
                @match inType begin
                  DAE.T_METALIST(ty = ty)  => begin
                    (boxIfUnboxedType(ty), DAE.DIM_UNKNOWN())
                  end

                  DAE.T_METAARRAY(ty = ty)  => begin
                    (boxIfUnboxedType(ty), DAE.DIM_UNKNOWN())
                  end

                  DAE.T_ARRAY(dims = dim <|  nil(), ty = ty)  => begin
                    (ty, dim)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                      (ty, dim) = unliftArrayOrList(ty)
                    (ty, dim)
                  end

                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    unliftArrayOrList(ty)
                  end
                end
              end
          (outType, dim)
        end

         #= This function turns an array into the element type of the array. =#
        function arrayElementType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    arrayElementType(inType.ty)
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    if listEmpty(getDimensions(inType.complexType))
                          inType
                        else
                          arrayElementType(inType.complexType)
                        end
                  end

                  DAE.T_FUNCTION(__)  => begin
                    arrayElementType(inType.funcResultType)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

        function setArrayElementType(inType::DAE.Type, inBaseType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                @match (inType, inBaseType) begin
                  (DAE.T_ARRAY(ty, dims), _)  => begin
                      ty = setArrayElementType(ty, inBaseType)
                    DAE.T_ARRAY(ty, dims)
                  end

                  _  => begin
                      inBaseType
                  end
                end
              end
          outType
        end

         #= prints eqmod to a string =#
        function unparseEqMod(eq::DAE.EqMod) ::String
              local str::String

              str = begin
                  local e::DAE.Exp
                  local e2::Absyn.Exp
                @match eq begin
                  DAE.TYPED(modifierAsExp = e)  => begin
                      str = ExpressionDump.printExpStr(e)
                    str
                  end

                  DAE.UNTYPED(exp = e2)  => begin
                      str = Dump.printExpStr(e2)
                    str
                  end
                end
              end
          str
        end

         #= prints eqmod to a string =#
        function unparseOptionEqMod(eq::Option{<:DAE.EqMod}) ::String
              local str::String

              str = begin
                  local e::DAE.EqMod
                @match eq begin
                  NONE()  => begin
                    "NONE()"
                  end

                  SOME(e)  => begin
                    unparseEqMod(e)
                  end
                end
              end
          str
        end

         #= This function prints a Modelica type as a piece of Modelica code. =#
        function unparseType(inType::DAE.Type) ::String
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
                      tystr = unparseType(ty)
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
                      bc_tp_str = unparseType(bc_tp)
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
                      restypestr = unparseType(restype)
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
                            list(@do_threaded_for unparseType(t) + " " + n (t, n) (tys, names))
                          end

                          _  => begin
                              list(unparseType(t) for t in tys)
                          end
                        end
                      end
                      tystr = stringDelimitList(tystrs, ", ")
                      res = stringAppendList(list("(", tystr, ")"))
                    res
                  end

                  DAE.T_METATUPLE(types = tys)  => begin
                      tystrs = ListUtil.map(tys, unparseType)
                      tystr = stringDelimitList(tystrs, ", ")
                      res = stringAppendList(list("tuple<", tystr, ">"))
                    res
                  end

                  DAE.T_METALIST(ty = ty)  => begin
                      tystr = unparseType(ty)
                      res = stringAppendList(list("list<", tystr, ">"))
                    res
                  end

                  DAE.T_METAARRAY(ty = ty)  => begin
                      tystr = unparseType(ty)
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
                          res + "<" + stringDelimitList(list(unparseType(tv) for tv in inType.typeVars), ",") + ">"
                        end
                  end

                  DAE.T_METARECORD(__)  => begin
                      res = AbsynUtil.pathStringNoQual(inType.path)
                    if listEmpty(inType.typeVars)
                          res
                        else
                          res + "<" + stringDelimitList(list(unparseType(tv) for tv in inType.typeVars), ",") + ">"
                        end
                  end

                  DAE.T_METABOXED(ty = ty)  => begin
                      res = unparseType(ty)
                      res = "#" + res
                    res
                  end

                  DAE.T_METAOPTION(ty = DAE.T_UNKNOWN(__))  => begin
                    "Option<Any>"
                  end

                  DAE.T_METAOPTION(ty = ty)  => begin
                      tystr = unparseType(ty)
                      res = stringAppendList(list("Option<", tystr, ">"))
                    res
                  end

                  DAE.T_METATYPE(ty = ty)  => begin
                    unparseType(ty)
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
                    "#FUNCTION_REFERENCE_VAR#" + unparseType(ty)
                  end

                  DAE.T_FUNCTION_REFERENCE_FUNC(functionType = ty)  => begin
                    "#FUNCTION_REFERENCE_FUNC#" + unparseType(ty)
                  end

                  _  => begin
                      "Internal error Types.unparseType: not implemented yet\\n"
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

         #= Like unparseType, but doesn't print out builtin attributes. =#
        function unparseTypeNoAttr(inType::DAE.Type) ::String
              local outString::String

              local ty::DAE.Type

              (ty, _) = stripTypeVars(inType)
              outString = unparseType(ty)
          outString
        end

        function unparsePropTypeNoAttr(inProps::DAE.Properties) ::String
              local outString::String

              outString = begin
                  local ty::DAE.Type
                @match inProps begin
                  DAE.PROP(type_ = ty)  => begin
                    unparseTypeNoAttr(ty)
                  end

                  DAE.PROP_TUPLE(type_ = ty)  => begin
                    unparseTypeNoAttr(ty)
                  end
                end
              end
          outString
        end

        function unparseConst(inConst::DAE.Const) ::String
              local outString::String

              outString = begin
                @match inConst begin
                  DAE.C_CONST(__)  => begin
                    "constant"
                  end

                  DAE.C_PARAM(__)  => begin
                    "parameter"
                  end

                  DAE.C_VAR(__)  => begin
                    "continuous"
                  end

                  DAE.C_UNKNOWN(__)  => begin
                    "unknown"
                  end
                end
              end
          outString
        end

         #= This function prints a Const as a string. =#
        function printConstStr(inConst::DAE.Const) ::String
              local outString::String

              outString = begin
                @match inConst begin
                  DAE.C_CONST(__)  => begin
                    "C_CONST"
                  end

                  DAE.C_PARAM(__)  => begin
                    "C_PARAM"
                  end

                  DAE.C_VAR(__)  => begin
                    "C_VAR"
                  end
                end
              end
          outString
        end

         #= This function prints a Modelica TupleConst as a string. =#
        function printTupleConstStr(inTupleConst::DAE.TupleConst) ::String
              local outString::String

              outString = begin
                  local cstr::String
                  local res::String
                  local res_1::String
                  local c::DAE.Const
                  local strlist::List{String}
                  local constlist::List{DAE.TupleConst}
                @match inTupleConst begin
                  DAE.SINGLE_CONST(constType = c)  => begin
                      cstr = printConstStr(c)
                    cstr
                  end

                  DAE.TUPLE_CONST(tupleConstLst = constlist)  => begin
                      strlist = ListUtil.map(constlist, printTupleConstStr)
                      res = stringDelimitList(strlist, ", ")
                      res_1 = stringAppendList(list("(", res, ")"))
                    res_1
                  end
                end
              end
          outString
        end

         #= This function prints a textual description of a Modelica type to a string.
          If the type is not one of the primitive types, it simply prints composite. =#
        function printTypeStr(inType::DAE.Type) ::String
              local str::String

              str = begin
                  local vars::List{DAE.Var}
                  local l::List{String}
                  local st::ClassInf.SMNode
                  local dims::List{DAE.Dimension}
                  local t::Type
                  local ty::Type
                  local restype::Type
                  local params::List{DAE.FuncArg}
                  local tys::List{DAE.Type}
                  local s1::String
                  local s2::String
                  local compType::String
                  local path::Absyn.Path
                @matchcontinue inType begin
                  DAE.T_INTEGER(varLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "Integer", "(", ", ", ")", false)
                  end

                  DAE.T_REAL(varLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "Real", "(", ", ", ")", false)
                  end

                  DAE.T_STRING(varLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "String", "(", ", ", ")", false)
                  end

                  DAE.T_BOOL(varLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "Boolean", "(", ", ", ")", false)
                  end

                  DAE.T_CLOCK(varLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "Clock", "(", ", ", ")", false)
                  end

                  DAE.T_ENUMERATION(literalVarLst = vars)  => begin
                    ListUtil.toString(vars, printVarStr, "Enumeration", "(", ", ", ")", false)
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = st, complexType = t, varLst = vars)  => begin
                      compType = printTypeStr(t)
                      s1 = ClassInf.printStateStr(st)
                      s2 = stringDelimitList(ListUtil.map(vars, printVarStr), ", ")
                      str = stringAppendList(list("composite(", s1, "{", s2, "}, derived from ", compType, ")"))
                    str
                  end

                  DAE.T_COMPLEX(complexClassType = st, varLst = vars)  => begin
                      s1 = ClassInf.printStateStr(st)
                      s2 = stringDelimitList(ListUtil.map(vars, printVarStr), ", ")
                      str = stringAppendList(list("composite(", s1, "{", s2, "})"))
                    str
                  end

                  DAE.T_ARRAY(dims = dims, ty = t)  => begin
                      s1 = stringDelimitList(ListUtil.map(dims, ExpressionDump.dimensionString), ", ")
                      s2 = printTypeStr(t)
                      str = stringAppendList(list("array(", s2, ")[", s1, "]"))
                    str
                  end

                  DAE.T_FUNCTION(funcArg = params, funcResultType = restype)  => begin
                      s1 = printParamsStr(params)
                      s2 = printTypeStr(restype)
                      str = stringAppendList(list("function(", s1, ") => ", s2))
                      str = str + AbsynUtil.pathString(inType.path)
                    str
                  end

                  DAE.T_TUPLE(types = tys)  => begin
                      s1 = stringDelimitList(ListUtil.map(tys, printTypeStr), ", ")
                      str = stringAppendList(list("(", s1, ")"))
                    str
                  end

                  DAE.T_METATUPLE(types = tys)  => begin
                      str = printTypeStr(DAE.T_TUPLE(tys, NONE()))
                    str
                  end

                  DAE.T_METALIST(ty = ty)  => begin
                      s1 = printTypeStr(ty)
                      str = stringAppendList(list("list<", s1, ">"))
                    str
                  end

                  DAE.T_METAOPTION(ty = ty)  => begin
                      s1 = printTypeStr(ty)
                      str = stringAppendList(list("Option<", s1, ">"))
                    str
                  end

                  DAE.T_METAARRAY(ty = ty)  => begin
                      s1 = printTypeStr(ty)
                      str = stringAppendList(list("array<", s1, ">"))
                    str
                  end

                  DAE.T_METABOXED(ty = ty)  => begin
                      s1 = printTypeStr(ty)
                      str = stringAppendList(list("boxed<", s1, ">"))
                    str
                  end

                  DAE.T_METAPOLYMORPHIC(name = s1)  => begin
                      str = stringAppendList(list("polymorphic<", s1, ">"))
                    str
                  end

                  DAE.T_UNKNOWN(__)  => begin
                      str = "T_UNKNOWN"
                    str
                  end

                  DAE.T_ANYTYPE(anyClassType = NONE())  => begin
                      str = "ANYTYPE()"
                    str
                  end

                  DAE.T_ANYTYPE(anyClassType = SOME(st))  => begin
                      s1 = ClassInf.printStateStr(st)
                      str = "ANYTYPE(" + s1 + ")"
                    str
                  end

                  DAE.T_NORETCALL(__)  => begin
                    "()"
                  end

                  DAE.T_METATYPE(ty = t)  => begin
                      s1 = printTypeStr(t)
                      str = stringAppendList(list("METATYPE(", s1, ")"))
                    str
                  end

                  t && DAE.T_METARECORD(__)  => begin
                      s1 = AbsynUtil.pathStringNoQual(t.path)
                      str = "#" + s1 + "#"
                    str
                  end

                  t && DAE.T_METAUNIONTYPE(__)  => begin
                      s1 = AbsynUtil.pathStringNoQual(t.path)
                      str = "#" + s1 + "#"
                    str
                  end

                  DAE.T_CODE(DAE.C_EXPRESSION(__))  => begin
                    "Code(Expression)"
                  end

                  DAE.T_CODE(DAE.C_EXPRESSION_OR_MODIFICATION(__))  => begin
                    "Code(ExpressionOrModification)"
                  end

                  DAE.T_CODE(DAE.C_TYPENAME(__))  => begin
                    "Code(TypeName)"
                  end

                  DAE.T_CODE(DAE.C_VARIABLENAME(__))  => begin
                    "Code(VariableName)"
                  end

                  DAE.T_CODE(DAE.C_VARIABLENAMES(__))  => begin
                    "Code(VariableName[:])"
                  end

                  _  => begin
                        str = "Types.printTypeStr failed"
                      str
                  end
                end
              end
               #=  MetaModelica tuple
               =#
               #=  MetaModelica list
               =#
               #=  MetaModelica Option
               =#
               #=  MetaModelica Array
               =#
               #=  MetaModelica Boxed
               =#
               #=  MetaModelica polymorphic
               =#
               #=  NoType
               =#
               #=  AnyType of none
               =#
               #=  AnyType of some
               =#
               #=  MetaType
               =#
               #=  Uniontype, Metarecord
               =#
               #=  Code
               =#
               #=  All the other ones we don't handle
               =#
          str
        end

         #= Author BZ, 2009-09
         Print the connector-type-name =#
        function printConnectorTypeStr(it::DAE.Type) ::Tuple{String, String}
              local s2::String #= Components of connector =#
              local s::String #= Connector type =#

              (s, s2) = begin
                  local st::ClassInf.SMNode
                  local connectorName::Absyn.Path
                  local vars::List{DAE.Var}
                  local varNames::List{String}
                  local isExpandable::Bool
                  local isExpandableStr::String
                  local t::Type
                @matchcontinue it begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(connectorName, isExpandable), varLst = vars)  => begin
                      varNames = ListUtil.map(vars, varName)
                      isExpandableStr = if isExpandable
                            "/* expandable */ "
                          else
                            ""
                          end
                      s = isExpandableStr + AbsynUtil.pathString(connectorName)
                      s2 = "{" + stringDelimitList(varNames, ", ") + "}"
                    (s, s2)
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(connectorName, isExpandable), varLst = vars, complexType = t)  => begin
                      varNames = ListUtil.map(vars, varName)
                      isExpandableStr = if isExpandable
                            "/* expandable */ "
                          else
                            ""
                          end
                      s = isExpandableStr + AbsynUtil.pathString(connectorName)
                      s2 = "{" + stringDelimitList(varNames, ", ") + "}" + " subtype of: " + printTypeStr(t)
                    (s, s2)
                  end

                  _  => begin
                      ("", unparseType(it))
                  end
                end
              end
               #=  TODO! check if we can get T_SUBTYPE_BASIC here??!!
               =#
          (s #= Connector type =#, s2 #= Components of connector =#)
        end

         #= Prints function arguments to a string. =#
        function printParamsStr(inFuncArgLst::List{<:DAE.FuncArg}) ::String
              local str::String

              str = begin
                  local n::String
                  local t::DAE.Type
                  local params::List{DAE.FuncArg}
                  local s1::String
                  local s2::String
                @matchcontinue inFuncArgLst begin
                   nil()  => begin
                    ""
                  end

                  DAE.FUNCARG(name = n, ty = t) <|  nil()  => begin
                      s1 = printTypeStr(t)
                      str = stringAppendList(list(n, " :: ", s1))
                    str
                  end

                  DAE.FUNCARG(name = n, ty = t) <| params  => begin
                      s1 = printTypeStr(t)
                      s2 = printParamsStr(params)
                      str = stringAppendList(list(n, " :: ", s1, " * ", s2))
                    str
                  end
                end
              end
          str
        end

         #=
          Prints a variable which is attribute of builtin type to a string, e.g. on the form 'max = 10.0' =#
        function unparseVarAttr(inVar::DAE.Var) ::String
              local outString::String

              outString = begin
                  local res::String
                  local n::String
                  local bindStr::String
                  local valStr::String
                  local value::Values.Value
                  local e::DAE.Exp
                @matchcontinue inVar begin
                  DAE.TYPES_VAR(name = n, binding = DAE.EQBOUND(exp = e))  => begin
                      bindStr = ExpressionDump.printExpStr(e)
                      res = stringAppendList(list(n, " = ", bindStr))
                    res
                  end

                  DAE.TYPES_VAR(name = n, binding = DAE.VALBOUND(valBound = value))  => begin
                      valStr = ValuesUtil.valString(value)
                      res = stringAppendList(list(n, " = ", valStr))
                    res
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= Prints a variable to a string. =#
        function unparseVar(inVar::DAE.Var) ::String
              local outString::String

              outString = begin
                  local t::String
                  local res::String
                  local n::String
                  local s::String
                  local typ::DAE.Type
                  local ct::DAE.ConnectorType
                @match inVar begin
                  DAE.TYPES_VAR(name = n, ty = typ, attributes = DAE.ATTR(connectorType = ct))  => begin
                      s = connectorTypeStr(ct)
                      t = unparseType(typ)
                      res = stringAppendList(list("  ", s, t, " ", n, ";\\n"))
                    res
                  end
                end
              end
          outString
        end

        function connectorTypeStr(ct::DAE.ConnectorType) ::String
              local str::String

              str = begin
                  local s::String
                @matchcontinue ct begin
                  DAE.POTENTIAL(__)  => begin
                    ""
                  end

                  DAE.FLOW(__)  => begin
                    "flow "
                  end

                  DAE.STREAM(_)  => begin
                    "stream "
                  end

                  _  => begin
                      ""
                  end
                end
              end
          str
        end

         #= Prints a function argument to a string. =#
        function unparseParam(inFuncArg::DAE.FuncArg) ::String
              local outString::String

              outString = begin
                  local tstr::String
                  local res::String
                  local id::String
                  local cstr::String
                  local estr::String
                  local pstr::String
                  local ty::DAE.Type
                  local c::DAE.Const
                  local p::DAE.VarParallelism
                  local exp::DAE.Exp
                @match inFuncArg begin
                  DAE.FUNCARG(id, ty, c, p, NONE())  => begin
                      tstr = unparseType(ty)
                      cstr = DAEUtil.constStrFriendly(c)
                      pstr = DAEUtil.dumpVarParallelismStr(p)
                      res = stringAppendList(list(tstr, " ", cstr, pstr, id))
                    res
                  end

                  DAE.FUNCARG(id, ty, c, p, SOME(exp))  => begin
                      tstr = unparseType(ty)
                      cstr = DAEUtil.constStrFriendly(c)
                      estr = ExpressionDump.printExpStr(exp)
                      pstr = DAEUtil.dumpVarParallelismStr(p)
                      res = stringAppendList(list(tstr, " ", cstr, pstr, id, " := ", estr))
                    res
                  end
                end
              end
          outString
        end

         #= author: LS
          Prints a Var to the a string. =#
        function printVarStr(inVar::DAE.Var) ::String
              local str::String

              str = begin
                  local vs::String
                  local n::String
                  local var::SCode.Variability
                  local typ::DAE.Type
                  local bind::DAE.Binding
                  local s1::String
                  local s2::String
                @matchcontinue inVar begin
                  DAE.TYPES_VAR(name = n, attributes = DAE.ATTR(variability = var), ty = typ, binding = bind)  => begin
                      s1 = printTypeStr(typ)
                      vs = SCodeDump.variabilityString(var)
                      s2 = printBindingStr(bind)
                      str = stringAppendList(list(s1, " ", n, " ", vs, " ", s2))
                    str
                  end

                  DAE.TYPES_VAR(name = n)  => begin
                      str = stringAppendList(list(n))
                    str
                  end
                end
              end
          str
        end

         #= Print a variable binding to a string. =#
        function printBindingStr(inBinding::DAE.Binding) ::String
              local outString::String

              outString = begin
                  local str::String
                  local str2::String
                  local res::String
                  local v_str::String
                  local s::String
                  local str3::String
                  local exp::DAE.Exp
                  local f::Const
                  local v::Values.Value
                  local source::DAE.BindingSource
                @matchcontinue inBinding begin
                  DAE.UNBOUND(__)  => begin
                    "UNBOUND"
                  end

                  DAE.EQBOUND(exp = exp, evaluatedExp = NONE(), constant_ = f, source = source)  => begin
                      str = ExpressionDump.printExpStr(exp)
                      str2 = printConstStr(f)
                      str3 = DAEUtil.printBindingSourceStr(source)
                      res = stringAppendList(list("DAE.EQBOUND(", str, ", NONE(), ", str2, ", ", str3, ")"))
                    res
                  end

                  DAE.EQBOUND(exp = exp, evaluatedExp = SOME(v), constant_ = f, source = source)  => begin
                      str = ExpressionDump.printExpStr(exp)
                      str2 = printConstStr(f)
                      v_str = ValuesUtil.valString(v)
                      str3 = DAEUtil.printBindingSourceStr(source)
                      res = stringAppendList(list("DAE.EQBOUND(", str, ", SOME(", v_str, "), ", str2, ", ", str3, ")"))
                    res
                  end

                  DAE.VALBOUND(valBound = v, source = source)  => begin
                      s = ValuesUtil.unparseValues(list(v))
                      str3 = DAEUtil.printBindingSourceStr(source)
                      res = stringAppendList(list("DAE.VALBOUND(", s, ", ", str3, ")"))
                    res
                  end

                  _  => begin
                      ""
                  end
                end
              end
          outString
        end

         #= author: LS
          Creates a function type from a function name an a list of input and
          output variables. =#
        function makeFunctionType(p::Absyn.Path, vl::List{<:DAE.Var}, functionAttributes::DAE.FunctionAttributes) ::DAE.Type
              local outType::DAE.Type

              local invl::List{DAE.Var}
              local outvl::List{DAE.Var}
              local fargs::List{DAE.FuncArg}
              local rettype::Type

              invl = getInputVars(vl)
              outvl = getOutputVars(vl)
              fargs = makeFargsList(invl)
              rettype = makeReturnType(outvl)
              outType = DAE.T_FUNCTION(fargs, rettype, functionAttributes, p)
          outType
        end

         #= function: extandFunctionType
          Extends function argument list adding var for element list. =#
        function extendsFunctionTypeArgs(inType::DAE.Type, inElementLst::List{<:DAE.Element}, inOutputElementLst::List{<:DAE.Element}, inBooltLst::List{<:Bool}) ::DAE.Type
              local outType::DAE.Type

              local tysrc::Absyn.Path
              local fargs::List{DAE.FuncArg}
              local fargs1::List{DAE.FuncArg}
              local newfargs::List{DAE.FuncArg}
              local rettype::DAE.Type
              local functionAttributes::DAE.FunctionAttributes

              @match DAE.T_FUNCTION(fargs, rettype, functionAttributes, tysrc) = inType
              (fargs1, _) = ListUtil.splitOnBoolList(fargs, inBooltLst)
              newfargs = ListUtil.threadMap(inElementLst, fargs1, makeElementFarg)
              newfargs = listAppend(fargs, newfargs)
               #=  The type of DAE.Element.VAR seems to be wrong,
               =#
               #=  but the original type should be also correct
               =#
               #= rettype := makeElementReturnType(inOutputElementLst);
               =#
              outType = DAE.T_FUNCTION(newfargs, rettype, functionAttributes, tysrc)
          outType
        end

         #=
          Create a return type from a list of Element output variables.
          Depending on the length of the output variable list, different
          kinds of return types are created. =#
        function makeElementReturnType(inElementLst::List{<:DAE.Element}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local element::DAE.Element
                  local elements::List{DAE.Element}
                  local types::List{Type}
                  local names::List{String}
                  local namesOpt::Option{List{String}}
                @match inElementLst begin
                   nil()  => begin
                    DAE.T_NORETCALL()
                  end

                  element <|  nil()  => begin
                      ty = makeElementReturnTypeSingle(element)
                    ty
                  end

                  elements  => begin
                      types = nil
                      names = nil
                      for element in elements
                        types = _cons(makeElementReturnTypeSingle(element), types)
                        names = _cons(DAEUtil.varName(element), names)
                      end
                      if listEmpty(names)
                        namesOpt = NONE()
                      else
                        namesOpt = SOME(listReverse(names))
                      end
                    DAE.T_TUPLE(listReverse(types), namesOpt)
                  end
                end
              end
          outType
        end

         #= Create the return type from an Element for a single return value. =#
        function makeElementReturnTypeSingle(inElement::DAE.Element) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                @match inElement begin
                  DAE.VAR(ty = ty)  => begin
                    ty
                  end
                end
              end
          outType
        end

         #= Creates an enumeration type from a name and an enumeration type containing
          the literal variables. =#
        function makeEnumerationType(inPath::Absyn.Path, inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local p::Absyn.Path
                  local names::List{String}
                  local attr_names::List{String}
                  local vars::List{DAE.Var}
                  local attrs::List{DAE.Var}
                  local ty::Type
                @matchcontinue (inPath, inType) begin
                  (_, DAE.T_ENUMERATION(index = NONE(), path = p, names = names, literalVarLst = vars, attributeLst = attrs))  => begin
                      vars = makeEnumerationType1(p, vars, names, 1)
                      attr_names = ListUtil.map(vars, getVarName)
                      attrs = makeEnumerationType1(p, attrs, attr_names, 1)
                    DAE.T_ENUMERATION(NONE(), p, names, vars, attrs)
                  end

                  (_, DAE.T_ARRAY(ty = ty))  => begin
                    makeEnumerationType(inPath, ty)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Types.makeEnumerationType failed on " + printTypeStr(inType))
                      fail()
                  end
                end
              end
          outType
        end

         #= Helper function to makeEnumerationType. Updates a list of enumeration
          literals with the correct index and type. =#
        function makeEnumerationType1(inPath::Absyn.Path, inVarLst::List{<:DAE.Var}, inNames::List{<:String}, inIdx::ModelicaInteger) ::List{DAE.Var}
              local outVarLst::List{DAE.Var}

              outVarLst = begin
                  local names::List{String}
                  local p::Absyn.Path
                  local name::String
                  local xs::List{DAE.Var}
                  local vars::List{DAE.Var}
                  local t::DAE.Type
                  local idx::ModelicaInteger
                  local attributes::DAE.Attributes
                  local binding::DAE.Binding
                  local var::DAE.Var
                  local cnstForRange::Option{DAE.Const}
                @match (inPath, inVarLst, inNames, inIdx) begin
                  (p, DAE.TYPES_VAR(name, attributes, _, binding, cnstForRange) <| xs, names, idx)  => begin
                      vars = makeEnumerationType1(p, xs, names, idx + 1)
                      t = DAE.T_ENUMERATION(SOME(idx), p, names, nil, nil)
                      var = DAE.TYPES_VAR(name, attributes, t, binding, cnstForRange)
                    _cons(var, vars)
                  end

                  (_,  nil(), _, _)  => begin
                    nil
                  end
                end
              end
          outVarLst
        end

         #= Prints a function argument to the Print buffer. =#
        function printFarg(inFuncArg::DAE.FuncArg)
              _ = begin
                  local n::String
                  local ty::DAE.Type
                @match inFuncArg begin
                  DAE.FUNCARG(name = n, ty = ty)  => begin
                      Print.printErrorBuf(printTypeStr(ty))
                      Print.printErrorBuf(" ")
                      Print.printErrorBuf(n)
                    ()
                  end
                end
              end
        end

         #= Prints a function argument to a string =#
        function printFargStr(inFuncArg::DAE.FuncArg) ::String
              local outString::String

              outString = begin
                  local s::String
                  local res::String
                  local n::String
                  local cs::String
                  local ps::String
                  local ty::DAE.Type
                  local c::DAE.Const
                  local p::DAE.VarParallelism
                @match inFuncArg begin
                  DAE.FUNCARG(n, ty, c, _, _)  => begin
                      s = unparseType(ty)
                      cs = DAEUtil.constStrFriendly(c)
                      res = stringAppendList(list(cs, s, " ", n))
                    res
                  end
                end
              end
               #=  res = stringAppendList({ps,cs,s,\" \",n});
               =#
          outString
        end

         #= author: LS
          Retrieve all the input variables from a list of variables. =#
        function getInputVars(vl::List{<:DAE.Var}) ::List{DAE.Var}
              local vl_1::List{DAE.Var}

              vl_1 = ListUtil.select(vl, isInputVar)
          vl_1
        end

         #= Retrieve all output variables from a list of variables. =#
        function getOutputVars(vl::List{<:DAE.Var}) ::List{DAE.Var}
              local vl_1::List{DAE.Var}

              vl_1 = ListUtil.select(vl, isOutputVar)
          vl_1
        end

         #= Returns the value of the fixed attribute of a builtin type.
         If there is no fixed in the tyep it returns true =#
        function getFixedVarAttributeParameterOrConstant(tp::DAE.Type) ::Bool
              local fix::Bool

              try
                fix = getFixedVarAttribute(tp)
              catch
                fix = true
              end
               #=  there is a fixed!
               =#
               #=  there is no fixed!
               =#
          fix
        end

         #= Returns the value of the fixed attribute of a builtin type =#
        function getFixedVarAttribute(tp::DAE.Type) ::Bool
              local fixed::Bool

              fixed = begin
                  local ty::Type
                  local result::Bool
                  local vars::List{DAE.Var}
                @matchcontinue tp begin
                  DAE.T_REAL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.VALBOUND(valBound = Values.BOOL(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_REAL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(evaluatedExp = SOME(Values.BOOL(fixed)))) <| _)  => begin
                    fixed
                  end

                  DAE.T_REAL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(exp = DAE.BCONST(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_REAL(varLst = _ <| vars)  => begin
                      fixed = getFixedVarAttribute(DAE.T_REAL(vars))
                    fixed
                  end

                  DAE.T_INTEGER(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.VALBOUND(valBound = Values.BOOL(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_INTEGER(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(evaluatedExp = SOME(Values.BOOL(fixed)))) <| _)  => begin
                    fixed
                  end

                  DAE.T_INTEGER(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(exp = DAE.BCONST(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_INTEGER(varLst = _ <| vars)  => begin
                      fixed = getFixedVarAttribute(DAE.T_INTEGER(vars))
                    fixed
                  end

                  DAE.T_BOOL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.VALBOUND(valBound = Values.BOOL(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_BOOL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(evaluatedExp = SOME(Values.BOOL(fixed)))) <| _)  => begin
                    fixed
                  end

                  DAE.T_BOOL(varLst = DAE.TYPES_VAR(name = "fixed", binding = DAE.EQBOUND(exp = DAE.BCONST(fixed))) <| _)  => begin
                    fixed
                  end

                  DAE.T_BOOL(varLst = _ <| vars)  => begin
                      fixed = getFixedVarAttribute(DAE.T_BOOL(vars))
                    fixed
                  end

                  DAE.T_ARRAY(ty = ty)  => begin
                      result = getFixedVarAttribute(ty)
                    result
                  end
                end
              end
          fixed
        end

         #= Returns the list of variables in a connector, or fails if the type is not a
          connector. =#
        function getConnectorVars(inType::DAE.Type) ::List{DAE.Var}
              local outVars::List{DAE.Var}

              outVars = begin
                  local vars::List{DAE.Var}
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(__), varLst = vars)  => begin
                    vars
                  end
                end
              end
          outVars
        end

         #= Succeds if variable is an input variable. =#
        function isInputVar(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                  local attr::DAE.Attributes
                @match inVar begin
                  DAE.TYPES_VAR(attributes = attr)  => begin
                    isInputAttr(attr) && isPublicAttr(attr)
                  end
                end
              end
          b
        end

         #= Succeds if variable is an output variable. =#
        function isOutputVar(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                  local attr::DAE.Attributes
                @match inVar begin
                  DAE.TYPES_VAR(attributes = attr)  => begin
                    isOutputAttr(attr) && isPublicAttr(attr)
                  end
                end
              end
          b
        end

         #= Returns true if the Attributes of a variable indicates
          that the variable is input. =#
        function isInputAttr(inAttributes::DAE.Attributes) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inAttributes begin
                  DAE.ATTR(direction = Absyn.INPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if the Attributes of a variable indicates
          that the variable is output. =#
        function isOutputAttr(inAttributes::DAE.Attributes) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inAttributes begin
                  DAE.ATTR(direction = Absyn.OUTPUT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

         #= Returns true if the Attributes of a variable indicates that the variable
          is bidirectional, i.e. neither input nor output. =#
        function isBidirAttr(inAttributes::DAE.Attributes) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match inAttributes begin
                  DAE.ATTR(direction = Absyn.BIDIR(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outBoolean
        end

        function isPublicAttr(inAttributes::DAE.Attributes) ::Bool
              local outIsPublic::Bool

              outIsPublic = begin
                @match inAttributes begin
                  DAE.ATTR(visibility = SCode.PUBLIC(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsPublic
        end

         #= true if variable is a public variable. =#
        function isPublicVar(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                  local attr::DAE.Attributes
                @match inVar begin
                  DAE.TYPES_VAR(attributes = attr)  => begin
                    isPublicAttr(attr)
                  end
                end
              end
          b
        end

         #= true if variable is a protected variable. =#
        function isProtectedVar(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                  local attr::DAE.Attributes
                @match inVar begin
                  DAE.TYPES_VAR(attributes = attr)  => begin
                    ! isPublicAttr(attr)
                  end
                end
              end
          b
        end

        function isModifiableTypesVar(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                  local attrs::DAE.Attributes
                @matchcontinue inVar begin
                  DAE.TYPES_VAR(attributes = attrs)  => begin
                      @match false = isPublicAttr(attrs)
                    false
                  end

                  DAE.TYPES_VAR(attributes = attrs, binding = DAE.UNBOUND(__))  => begin
                      @match true = isConstAttr(attrs)
                    true
                  end

                  DAE.TYPES_VAR(attributes = attrs)  => begin
                      @match true = isConstAttr(attrs)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

        function getBindingExp(inVar::DAE.Var, inPath::Absyn.Path) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local exp::DAE.Exp
                  local str::String
                  local name::String
                @match (inVar, inPath) begin
                  (DAE.TYPES_VAR(binding = DAE.EQBOUND(exp = exp)), _)  => begin
                    exp
                  end

                  (DAE.TYPES_VAR(name = name, binding = DAE.UNBOUND(__)), _)  => begin
                      str = "Record '" + AbsynUtil.pathString(inPath) + "' member '" + name + "' has no default value and is not modifiable by a constructor function.\\n"
                      Error.addCompilerWarning(str)
                    DAE.ICONST(0)
                  end
                end
              end
          outExp
        end

        function isConstAttr(inAttributes::DAE.Attributes) ::Bool
              local outIsPublic::Bool

              outIsPublic = begin
                @match inAttributes begin
                  DAE.ATTR(variability = SCode.CONST(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsPublic
        end

         #= Makes a function argument list from a list of variables. =#
        function makeFargsList(vars::List{<:DAE.Var}) ::List{DAE.FuncArg}
              local fargs::List{DAE.FuncArg}

              fargs = ListUtil.map(vars, makeFarg)
          fargs
        end

         #= Makes a function argument list from a variable. =#
        function makeFarg(variable::DAE.Var) ::DAE.FuncArg
              local farg::DAE.FuncArg

              farg = begin
                  local n::String
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local bnd::DAE.Binding
                  local c::DAE.Const
                  local p::DAE.VarParallelism
                  local var::SCode.Variability
                  local par::SCode.Parallelism
                  local oexp::Option{DAE.Exp}
                  local comment::Option{SCode.Comment}
                @match variable begin
                  DAE.TYPES_VAR(name = n, attributes = DAE.ATTR(variability = var, parallelism = par), ty = ty, binding = bnd)  => begin
                      c = variabilityToConst(var)
                      p = DAEUtil.scodePrlToDaePrl(par)
                      oexp = DAEUtil.bindingExp(bnd)
                    DAE.FUNCARG(n, ty, c, p, oexp)
                  end
                end
              end
          farg
        end

         #= Makes a function argument list from a variable. =#
        function makeElementFarg(inElement::DAE.Element, inFarg::DAE.FuncArg) ::DAE.FuncArg
              local farg::DAE.FuncArg

              farg = begin
                  local name::String
                  local varKind::DAE.VarKind
                  local ty::Type
                  local c::DAE.Const
                  local binding::Option{DAE.Exp}
                  local cref::DAE.ComponentRef
                  local parallelism::DAE.VarParallelism
                @match (inElement, inFarg) begin
                  (DAE.VAR(componentRef = cref), _)  => begin
                      name = ComponentReference.crefLastIdent(cref)
                    setFuncArgName(inFarg, name)
                  end
                end
              end
          farg
        end

         #= author: LS
          Create a return type from a list of output variables.
          Depending on the length of the output variable list, different
          kinds of return types are created. =#
        function makeReturnType(inVarLst::List{<:DAE.Var}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local var::Var
                  local tys::List{DAE.Type}
                  local vl::List{DAE.Var}
                @matchcontinue inVarLst begin
                   nil()  => begin
                    DAE.T_NORETCALL()
                  end

                  var <|  nil()  => begin
                      ty = makeReturnTypeSingle(var)
                    ty
                  end

                  vl  => begin
                    DAE.T_TUPLE(list(makeReturnTypeSingle(v) for v in vl), SOME(list(varName(v) for v in vl)))
                  end
                end
              end
          outType
        end

         #= author: LS
          Create the return type for a single return value. =#
        function makeReturnTypeSingle(inVar::DAE.Var) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                @match inVar begin
                  DAE.TYPES_VAR(ty = ty)  => begin
                    ty
                  end
                end
              end
          outType
        end

         #= author: LS
          Succeds if a variable is a parameter. =#
        function isParameterVar(inVar::DAE.Var)
              @match DAE.TYPES_VAR(attributes = DAE.ATTR(variability = SCode.PARAM(), visibility = SCode.PUBLIC())) = inVar
        end

         #= Returns true of c is C_CONST. =#
        function isConstant(c::DAE.Const) ::Bool
              local b::Bool

              b = begin
                @match c begin
                  DAE.C_CONST(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if c is C_PARAM. =#
        function isParameter(c::DAE.Const) ::Bool
              local b::Bool

              b = begin
                @match c begin
                  DAE.C_PARAM(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= returns true if Const is PARAM or CONST =#
        function isParameterOrConstant(c::DAE.Const) ::Bool
              local b::Bool

              b = begin
                @match c begin
                  DAE.C_CONST(__)  => begin
                    true
                  end

                  DAE.C_PARAM(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isVar(inConst::DAE.Const) ::Bool
              local outIsVar::Bool

              outIsVar = begin
                @match inConst begin
                  DAE.C_VAR(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsVar
        end

         #= Returns true if any of the given properties contains a Real type. =#
        function propsContainReal(inProperties::List{<:DAE.Properties}) ::Bool
              local outHasReal::Bool = false

              for prop in inProperties
                if isReal(getPropType(prop))
                  outHasReal = true
                  break
                end
              end
          outHasReal
        end

         #= Returns true if a builtin type, or array-type is Real. =#
        function containReal(inTypes::List{<:DAE.Type}) ::Bool
              local outHasReal::Bool

              for ty in inTypes
                if isReal(ty)
                  outHasReal = true
                  return outHasReal
                end
              end
              outHasReal = false
          outHasReal
        end

         #= Returns the element type of a Type and the dimensions of the type. =#
        function flattenArrayType(inType::DAE.Type) ::Tuple{DAE.Type, DAE.Dimensions}
              local outDimensions::DAE.Dimensions
              local outType::DAE.Type

              (outType, outDimensions) = begin
                  local ty::Type
                  local dims::DAE.Dimensions
                  local dim::DAE.Dimension
                   #=  Array type
                   =#
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                      (ty, dims) = flattenArrayType(inType.ty)
                      dims = listAppend(inType.dims, dims)
                    (ty, dims)
                  end

                  DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
                    (inType, nil)
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    flattenArrayType(inType.complexType)
                  end

                  _  => begin
                      (inType, nil)
                  end
                end
              end
               #=  Complex type extending basetype with equality constraint
               =#
               #=  Complex type extending basetype.
               =#
               #=  Element type
               =#
          (outType, outDimensions)
        end

         #= Return the type name of a Type. =#
        function getTypeName(inType::DAE.Type) ::String
              local outString::String

              outString = begin
                  local n::String
                  local dimstr::String
                  local tystr::String
                  local str::String
                  local st::ClassInf.SMNode
                  local ty::DAE.Type
                  local arrayty::DAE.Type
                  local dims::List{DAE.Dimension}
                @matchcontinue inType begin
                  DAE.T_INTEGER(__)  => begin
                    "Integer"
                  end

                  DAE.T_REAL(__)  => begin
                    "Real"
                  end

                  DAE.T_STRING(__)  => begin
                    "String"
                  end

                  DAE.T_BOOL(__)  => begin
                    "Boolean"
                  end

                  DAE.T_CLOCK(__)  => begin
                    "Clock"
                  end

                  DAE.T_COMPLEX(complexClassType = st)  => begin
                      n = AbsynUtil.pathString(ClassInf.getStateName(st))
                    n
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = st)  => begin
                      n = AbsynUtil.pathString(ClassInf.getStateName(st))
                    n
                  end

                  arrayty && DAE.T_ARRAY(__)  => begin
                      (ty, dims) = flattenArrayType(arrayty)
                      dimstr = ExpressionDump.dimensionsString(dims)
                      tystr = getTypeName(ty)
                      str = stringAppendList(list(tystr, "[", dimstr, "]"))
                    str
                  end

                  DAE.T_METALIST(ty = ty)  => begin
                      n = getTypeName(ty)
                    n
                  end

                  _  => begin
                      "Not nameable type or no type"
                  end
                end
              end
               #=  BTH
               =#
               #=  MetaModelica type
               =#
          outString
        end

         #= author: LS
          If PROP_TUPLE, returns true if all of the flags are constant. =#
        function propAllConst(inProperties::DAE.Properties) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                  local c::DAE.Const
                  local res::DAE.Const
                  local constant_::DAE.TupleConst
                  local str::String
                  local prop::DAE.Properties
                @matchcontinue inProperties begin
                  DAE.PROP(constFlag = c)  => begin
                    c
                  end

                  DAE.PROP_TUPLE(tupleConst = constant_)  => begin
                      res = propTupleAllConst(constant_)
                    res
                  end

                  prop  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- prop_all_const failed: ")
                      str = printPropStr(prop)
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
          outConst
        end

         #= author: LS
          If PROP_TUPLE, returns true if any of the flags are true =#
        function propAnyConst(inProperties::DAE.Properties) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                  local constant_::DAE.Const
                  local res::DAE.Const
                  local str::String
                  local prop::DAE.Properties
                  local tconstant_::DAE.TupleConst
                @matchcontinue inProperties begin
                  DAE.PROP(constFlag = constant_)  => begin
                    constant_
                  end

                  DAE.PROP_TUPLE(tupleConst = tconstant_)  => begin
                      res = propTupleAnyConst(tconstant_)
                    res
                  end

                  prop  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- prop_any_const failed: ")
                      str = printPropStr(prop)
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
          outConst
        end

         #= author: LS
          Helper function to prop_any_const. =#
        function propTupleAnyConst(inTupleConst::DAE.TupleConst) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                  local c::DAE.Const
                  local res::DAE.Const
                  local first::DAE.TupleConst
                  local constType::DAE.TupleConst
                  local rest::List{DAE.TupleConst}
                  local str::String
                @matchcontinue inTupleConst begin
                  DAE.SINGLE_CONST(constType = c)  => begin
                    c
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| _)  => begin
                      @match DAE.C_CONST() = propTupleAnyConst(first)
                    DAE.C_CONST()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <|  nil())  => begin
                      @match DAE.C_PARAM() = propTupleAnyConst(first)
                    DAE.C_PARAM()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <|  nil())  => begin
                      @match DAE.C_VAR() = propTupleAnyConst(first)
                    DAE.C_VAR()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| rest)  => begin
                      @match DAE.C_PARAM() = propTupleAnyConst(first)
                      res = propTupleAnyConst(DAE.TUPLE_CONST(rest))
                    res
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| rest)  => begin
                      @match DAE.C_VAR() = propTupleAnyConst(first)
                      res = propTupleAnyConst(DAE.TUPLE_CONST(rest))
                    res
                  end

                  constType  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- prop_tuple_any_const failed: ")
                      str = printTupleConstStr(constType)
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
          outConst
        end

         #= author: LS
          Helper function to propAllConst. =#
        function propTupleAllConst(inTupleConst::DAE.TupleConst) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                  local c::DAE.Const
                  local res::DAE.Const
                  local first::DAE.TupleConst
                  local constType::DAE.TupleConst
                  local rest::List{DAE.TupleConst}
                  local str::String
                @matchcontinue inTupleConst begin
                  DAE.SINGLE_CONST(constType = c)  => begin
                    c
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| _)  => begin
                      @match DAE.C_PARAM() = propTupleAllConst(first)
                    DAE.C_PARAM()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| _)  => begin
                      @match DAE.C_VAR() = propTupleAllConst(first)
                    DAE.C_VAR()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <|  nil())  => begin
                      @match DAE.C_CONST() = propTupleAllConst(first)
                    DAE.C_CONST()
                  end

                  DAE.TUPLE_CONST(tupleConstLst = first <| rest)  => begin
                      @match DAE.C_CONST() = propTupleAllConst(first)
                      res = propTupleAllConst(DAE.TUPLE_CONST(rest))
                    res
                  end

                  constType  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- prop_tuple_all_const failed: ")
                      str = printTupleConstStr(constType)
                      Debug.traceln(str)
                    fail()
                  end
                end
              end
          outConst
        end

         #= This function will check all elements in the tuple if anyone is an array, return true.
        As for now it will not check tuple of tuples ie. no recursion. =#
        function isPropTupleArray(p::DAE.Properties) ::Bool
              local ob::Bool

              local b1::Bool
              local b2::Bool

              b1 = isPropTuple(p)
              b2 = isPropArray(p)
              ob = boolOr(b1, b2)
          ob
        end

         #= Checks if Properties is a tuple or not. =#
        function isPropTuple(p::DAE.Properties) ::Bool
              local b::Bool

              b = begin
                @matchcontinue p begin
                  _  => begin
                      @match DAE.T_TUPLE() = getPropType(p)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Return true if properties contain an array type. =#
        function isPropArray(p::DAE.Properties) ::Bool
              local b::Bool

              local t::Type

              t = getPropType(p)
              b = isArray(t)
          b
        end

         #= Returns the first property from a tuple's properties or fails. =#
        function propTupleFirstProp(inTupleProp::DAE.Properties) ::DAE.Properties
              local outFirstProp::DAE.Properties

              local ty::Type
              local c::DAE.Const

              @match DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types = _cons(ty, _)), tupleConst = DAE.TUPLE_CONST(tupleConstLst = _cons(DAE.SINGLE_CONST(constType = c), _))) = inTupleProp
              outFirstProp = DAE.PROP(ty, c)
          outFirstProp
        end

         #= Splits a PROP_TUPLE into a list of PROPs. =#
        function propTuplePropList(prop_tuple::DAE.Properties) ::List{DAE.Properties}
              local prop_list::List{DAE.Properties}

              prop_list = begin
                  local pl::List{DAE.Properties}
                  local tl::List{DAE.Type}
                  local cl::List{TupleConst}
                @match prop_tuple begin
                  DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types = tl), tupleConst = DAE.TUPLE_CONST(tupleConstLst = cl))  => begin
                      pl = propTuplePropList2(tl, cl)
                    pl
                  end
                end
              end
          prop_list
        end

         #= Helper function to propTuplePropList =#
        function propTuplePropList2(tl::List{<:DAE.Type}, cl::List{<:TupleConst}) ::List{DAE.Properties}
              local pl::List{DAE.Properties}

              pl = begin
                  local t::Type
                  local t_rest::List{DAE.Type}
                  local c::Const
                  local c_rest::List{TupleConst}
                  local p_rest::List{DAE.Properties}
                @match (tl, cl) begin
                  ( nil(),  nil())  => begin
                    nil
                  end

                  (t <| t_rest, DAE.SINGLE_CONST(c) <| c_rest)  => begin
                      p_rest = propTuplePropList2(t_rest, c_rest)
                    _cons(DAE.PROP(t, c), p_rest)
                  end
                end
              end
          pl
        end

         #= author: adrpo
          Return the const from Properties (no tuples!). =#
        function getPropConst(inProperties::DAE.Properties) ::DAE.Const
              local outConst::DAE.Const

              @match DAE.PROP(constFlag = outConst) = inProperties
          outConst
        end

         #= author: LS
          Return the Type from Properties. =#
        function getPropType(inProperties::DAE.Properties) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inProperties begin
                  DAE.PROP(__)  => begin
                    inProperties.type_
                  end

                  DAE.PROP_TUPLE(__)  => begin
                    inProperties.type_
                  end
                end
              end
          outType
        end

         #= Set the Type from Properties. =#
        function setPropType(inProperties::DAE.Properties, ty::DAE.Type) ::DAE.Properties
              local outProperties::DAE.Properties

              outProperties = begin
                @match inProperties begin
                  DAE.PROP(__)  => begin
                    DAE.PROP(ty, inProperties.constFlag)
                  end

                  DAE.PROP_TUPLE(__)  => begin
                    DAE.PROP_TUPLE(ty, inProperties.tupleConst)
                  end
                end
              end
          outProperties
        end

         #= @author: adrpo
          creates an array, with one element for each record in TType!
          Note: This has to be at least 4 larger than the number of records in DAE.Type,
          due to the way bootstrapping indexes records. =#
        function createEmptyTypeMemory() ::InstTypes.TypeMemoryEntryListArray
              local tyMemory::InstTypes.TypeMemoryEntryListArray

              tyMemory = arrayCreate(30, nil)
          tyMemory
        end

         #= @author: adrpo
          simplifies the given type, to be used in an expression or component reference =#
        function simplifyType(inType::DAE.Type) ::DAE.Type
              local outExpType::DAE.Type

              outExpType = begin
                  local str::String
                  local t::Type
                  local t_1::DAE.Type
                  local dims::DAE.Dimensions
                  local tys::List{DAE.Type}
                  local varLst::List{DAE.Var}
                  local CIS::ClassInf.SMNode
                  local ec::DAE.EqualityConstraint
                @matchcontinue inType begin
                  DAE.T_FUNCTION(__)  => begin
                    DAE.T_FUNCTION_REFERENCE_VAR(inType)
                  end

                  DAE.T_METAUNIONTYPE(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METARECORD(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METAPOLYMORPHIC(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METALIST(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METAARRAY(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METAOPTION(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_METATUPLE(__)  => begin
                    DAE.T_METATYPE(inType)
                  end

                  DAE.T_UNKNOWN(__)  => begin
                    DAE.T_UNKNOWN_DEFAULT
                  end

                  DAE.T_ANYTYPE(__)  => begin
                    DAE.T_UNKNOWN_DEFAULT
                  end

                  t && DAE.T_ARRAY(__)  => begin
                      (t, dims) = flattenArrayType(t)
                      t_1 = simplifyType(t)
                    DAE.T_ARRAY(t_1, dims)
                  end

                  DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
                    inType
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                    simplifyType(t)
                  end

                  DAE.T_INTEGER(__)  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  DAE.T_REAL(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  DAE.T_BOOL(__)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  DAE.T_CLOCK(__)  => begin
                    DAE.T_CLOCK_DEFAULT
                  end

                  DAE.T_STRING(__)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  DAE.T_NORETCALL(__)  => begin
                    DAE.T_NORETCALL_DEFAULT
                  end

                  DAE.T_TUPLE(types = tys)  => begin
                      tys = ListUtil.map(tys, simplifyType)
                    DAE.T_TUPLE(tys, inType.names)
                  end

                  DAE.T_ENUMERATION(__)  => begin
                    inType
                  end

                  DAE.T_COMPLEX(CIS, varLst, ec)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      varLst = list(simplifyVar(v) for v in varLst)
                    DAE.T_COMPLEX(CIS, varLst, ec)
                  end

                  DAE.T_COMPLEX(CIS && ClassInf.RECORD(__), varLst, ec)  => begin
                      varLst = list(simplifyVar(v) for v in varLst)
                    DAE.T_COMPLEX(CIS, varLst, ec)
                  end

                  DAE.T_COMPLEX(__)  => begin
                    inType
                  end

                  DAE.T_METABOXED(ty = t)  => begin
                      t_1 = simplifyType(t)
                    DAE.T_METABOXED(t_1)
                  end

                  _  => begin
                    DAE.T_UNKNOWN_DEFAULT
                  end

                  _  => begin
                        str = "Types.simplifyType failed for: " + unparseType(inType)
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
               #=  do NOT simplify out equality constraint
               =#
               #=  BTH watch out: Due to simplification some type info is lost here
               =#
               #=  for metamodelica we need this for some reson!
               =#
               #=  do this for records too, otherwise:
               =#
               #=  frame.R = Modelica.Mechanics.MultiBody.Frames.Orientation({const_matrix);
               =#
               #=  does not get expanded into the component equations.
               =#
               #=  otherwise just return the same!
               =#
               #=  This is the case when the type is currently UNTYPED
               =#
               #= /*
                      print(\" untyped \");
                      print(unparseType(inType));
                      print(\"\\n\");
                      */ =#
          outExpType
        end

        function simplifyVar(inVar::DAE.Var) ::DAE.Var
              local outVar::DAE.Var = inVar

              outVar = begin
                @match outVar begin
                  DAE.TYPES_VAR(__)  => begin
                      outVar.ty = simplifyType(outVar.ty)
                    outVar
                  end
                end
              end
          outVar
        end

         #= Does the opposite of simplifyType, as far as it's possible. =#
        function complicateType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type = inType

              outType = begin
                  local ty::DAE.Type
                  local dims::List{DAE.Dimension}
                @match outType begin
                  DAE.T_ARRAY(dims = _ <| _)  => begin
                      (ty, dims) = flattenArrayType(outType)
                    liftArrayListDims(ty, dims)
                  end

                  DAE.T_FUNCTION_REFERENCE_VAR(__)  => begin
                    outType.functionType
                  end

                  DAE.T_METATYPE(__)  => begin
                    outType.ty
                  end

                  DAE.T_TUPLE(__)  => begin
                      outType.types = list(complicateType(t) for t in outType.types)
                    outType
                  end

                  DAE.T_COMPLEX(__)  => begin
                      if isRecord(inType) || Config.acceptMetaModelicaGrammar()
                        outType.varLst = list(complicateVar(v) for v in outType.varLst)
                      end
                    outType
                  end

                  DAE.T_METABOXED(__)  => begin
                      outType.ty = complicateType(outType.ty)
                    outType
                  end

                  _  => begin
                      outType
                  end
                end
              end
          outType
        end

        function complicateVar(inVar::DAE.Var) ::DAE.Var
              local outVar::DAE.Var = inVar

              outVar = begin
                @match outVar begin
                  DAE.TYPES_VAR(__)  => begin
                      outVar.ty = complicateType(outVar.ty)
                    outVar
                  end
                end
              end
          outVar
        end

        function typeMemoryEntryEq(inType1::DAE.Type, inType2::Tuple{<:DAE.Type, DAE.Type}) ::Bool
              local outEq::Bool

              local ty2::DAE.Type

              (ty2, _) = inType2
              outEq = typesElabEquivalent(inType1, ty2)
          outEq
        end

         #= This function checks if two types will result in the same elaborated type.
          Used by simplifyType to check if a matching elaborated type already exists. =#
        function typesElabEquivalent(inType1::DAE.Type, inType2::DAE.Type) ::Bool
              local isEqual::Bool

              try
                isEqual = ttypesElabEquivalent(inType1, inType2)
              catch
                isEqual = false
              end
          isEqual
        end

         #= Helper function to typesElabEquivalent. Checks if two TType will result in
          the same elaborated type. =#
        function ttypesElabEquivalent(inType1::DAE.Type, inType2::DAE.Type) ::Bool
              local isEqual::Bool

              isEqual = begin
                  local cty1::ClassInf.SMNode
                  local cty2::ClassInf.SMNode
                  local vars1::List{DAE.Var}
                  local vars2::List{DAE.Var}
                  local ad1::DAE.Dimension
                  local ad2::DAE.Dimension
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local names1::List{String}
                  local names2::List{String}
                  local types1::List{DAE.Type}
                  local types2::List{DAE.Type}
                @match (inType1, inType2) begin
                  (DAE.T_COMPLEX(complexClassType = cty1, varLst = vars1), DAE.T_COMPLEX(complexClassType = cty2, varLst = vars2))  => begin
                      @match true = AbsynUtil.pathEqual(ClassInf.getStateName(cty1), ClassInf.getStateName(cty2))
                      @match true = ListUtil.isEqualOnTrue(vars1, vars2, varsElabEquivalent)
                    true
                  end

                  (DAE.T_ARRAY(dims = ad1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = ad2 <|  nil(), ty = ty2))  => begin
                      @match true = valueEq(ad1, ad2)
                      @match true = typesElabEquivalent(ty1, ty2)
                    true
                  end

                  (DAE.T_ENUMERATION(path = p1, names = names1), DAE.T_ENUMERATION(path = p2, names = names2))  => begin
                      @match true = AbsynUtil.pathEqual(p1, p2)
                      @match true = ListUtil.isEqualOnTrue(names1, names2, stringEqual)
                    true
                  end

                  (DAE.T_TUPLE(types = types1), DAE.T_TUPLE(types = types2))  => begin
                    ListUtil.isEqualOnTrue(types1, types2, typesElabEquivalent)
                  end

                  (DAE.T_METABOXED(ty = ty1), DAE.T_METABOXED(ty = ty2))  => begin
                    typesElabEquivalent(ty1, ty2)
                  end

                  _  => begin
                      valueEq(inType1, inType2)
                  end
                end
              end
          isEqual
        end

         #= Helper function to ttypesElabEquivalent. Check if two DAE.Var will result in
          the same DAE.Var after elaboration. =#
        function varsElabEquivalent(inVar1::DAE.Var, inVar2::DAE.Var) ::Bool
              local isEqual::Bool

              isEqual = begin
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                @matchcontinue (inVar1, inVar2) begin
                  (DAE.TYPES_VAR(name = id1, ty = ty1), DAE.TYPES_VAR(name = id2, ty = ty2))  => begin
                      @match true = stringEqual(id1, id2)
                      @match true = typesElabEquivalent(ty1, ty2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isEqual
        end

         #= This is basically a wrapper aroune matchType.
          It matches an expression with properties with another set of properties.
          If necessary, the expression is modified to match.
          The only relevant property is the type. =#
        function matchProp(inExp::DAE.Exp, inActualType::DAE.Properties, inExpectedType::DAE.Properties, printFailtrace::Bool) ::Tuple{DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp

              (outExp, outProperties) = begin
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local t_1::Type
                  local gt::Type
                  local et::Type
                  local c::Const
                  local c1::Const
                  local c2::Const
                  local c_1::Const
                  local tc::TupleConst
                  local tc1::TupleConst
                  local tc2::TupleConst
                  local prop::Properties
                @matchcontinue (inExp, inActualType, inExpectedType, printFailtrace) begin
                  (e, DAE.PROP(type_ = gt, constFlag = c1), DAE.PROP(type_ = et, constFlag = c2), _)  => begin
                      (e_1, t_1) = matchType(e, gt, et, printFailtrace)
                      c = constAnd(c1, c2)
                    (e_1, DAE.PROP(t_1, c))
                  end

                  (e, DAE.PROP_TUPLE(type_ = gt, tupleConst = tc1), DAE.PROP_TUPLE(type_ = et, tupleConst = tc2), _)  => begin
                      (e_1, t_1) = matchType(e, gt, et, printFailtrace)
                      tc = constTupleAnd(tc1, tc2)
                    (e_1, DAE.PROP_TUPLE(t_1, tc))
                  end

                  (e, DAE.PROP_TUPLE(type_ = gt && DAE.T_TUPLE(__), tupleConst = tc1), DAE.PROP(type_ = et && DAE.T_METATUPLE(__), constFlag = c2), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (e_1, t_1) = matchType(e, gt, et, printFailtrace)
                      c_1 = propTupleAllConst(tc1)
                      c = constAnd(c_1, c2)
                    (e_1, DAE.PROP(t_1, c))
                  end

                  (e, DAE.PROP_TUPLE(type_ = gt && DAE.T_TUPLE(__), tupleConst = tc1), DAE.PROP(type_ = et && DAE.T_METABOXED(__), constFlag = c2), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (e_1, t_1) = matchType(e, gt, et, printFailtrace)
                      c_1 = propTupleAllConst(tc1)
                      c = constAnd(c_1, c2)
                    (e_1, DAE.PROP(t_1, c))
                  end

                  (e, DAE.PROP(type_ = gt), DAE.PROP_TUPLE(__), _)  => begin
                      prop = propTupleFirstProp(inExpectedType)
                      (e_1, prop) = matchProp(e, inActualType, prop, printFailtrace)
                      gt = simplifyType(gt)
                      e_1 = DAE.TSUB(e_1, 1, gt)
                    (e_1, prop)
                  end

                  (e, DAE.PROP_TUPLE(__), DAE.PROP(__), _)  => begin
                      @match (@match DAE.PROP(type_ = gt) = prop) = propTupleFirstProp(inActualType)
                      (e_1, prop) = matchProp(e, prop, inExpectedType, printFailtrace)
                      gt = simplifyType(gt)
                      e_1 = DAE.TSUB(e_1, 1, gt)
                    (e_1, prop)
                  end

                  (e, _, _, true)  => begin
                      @match true = Flags.isSet(Flags.TYPES)
                      Debug.traceln("- Types.matchProp failed on exp: " + ExpressionDump.printExpStr(e))
                      Debug.traceln(printPropStr(inActualType) + " != ")
                      Debug.traceln(printPropStr(inExpectedType))
                    fail()
                  end
                end
              end
               #=  The problem with MetaModelica tuple is that it is a datatype (should use PROP instead of PROP_TUPLE)
               =#
               #=  this case converts a TUPLE to META_TUPLE
               =#
               #=  activate on -d=types flag
               =#
          (outExp, outProperties)
        end

        function matchTypeList(exps::List{<:DAE.Exp}, expType::DAE.Type, expectedType::DAE.Type, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTypeLst::List{DAE.Type} = nil
              local outExp::List{DAE.Exp} = nil

              local expLstNew::List{DAE.Exp} = exps
              local exp::DAE.Exp
              local e_1::DAE.Exp
              local tp::Type

              while ! listEmpty(expLstNew)
                @match _cons(exp, expLstNew) = expLstNew
                (e_1, tp) = matchType(exp, expType, expectedType, printFailtrace)
                outExp = _cons(e_1, outExp)
                outTypeLst = _cons(tp, outTypeLst)
              end
              outExp = listReverseInPlace(outExp)
              outTypeLst = listReverseInPlace(outTypeLst)
          (outExp, outTypeLst)
        end

         #= Transforms a list of expressions and types into a list of expressions
        of the expected types. =#
        function matchTypeTuple(inExp1::List{<:DAE.Exp}, inTypeLst2::List{<:DAE.Type}, inTypeLst3::List{<:DAE.Type}, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTypeLst::List{DAE.Type}
              local outExp::List{DAE.Exp}

              (outExp, outTypeLst) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local rest::List{DAE.Exp}
                  local e_2::List{DAE.Exp}
                  local tp::Type
                  local t1::Type
                  local t2::Type
                  local res::List{DAE.Type}
                  local ts1::List{DAE.Type}
                  local ts2::List{DAE.Type}
                @matchcontinue (inExp1, inTypeLst2, inTypeLst3, printFailtrace) begin
                  ( nil(),  nil(),  nil(), _)  => begin
                    (nil, nil)
                  end

                  (e <| rest, t1 <| ts1, t2 <| ts2, _)  => begin
                      (e_1, tp) = matchType(e, t1, t2, printFailtrace)
                      (e_2, res) = matchTypeTuple(rest, ts1, ts2, printFailtrace)
                    (_cons(e_1, e_2), _cons(tp, res))
                  end

                  (_, t1 <| _, t2 <| _, true)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Types.matchTypeTuple failed:" + Types.unparseType(t1) + " " + Types.unparseType(t2) + "\\n")
                    fail()
                  end
                end
              end
          (outExp, outTypeLst)
        end

        function matchTypeTupleCall(inExp1::DAE.Exp, inTypeLst2::List{<:DAE.Type}, inTypeLst3::List{<:DAE.Type})
              _ = begin
                  local e::DAE.Exp
                  local t1::Type
                  local t2::Type
                  local ts1::List{DAE.Type}
                  local ts2::List{DAE.Type}
                @matchcontinue (inExp1, inTypeLst2, inTypeLst3) begin
                  (_, _,  nil())  => begin
                    ()
                  end

                  (e, t1 <| ts1, t2 <| ts2)  => begin
                      @match true = subtype(t1, t2)
                      matchTypeTupleCall(e, ts1, ts2)
                    ()
                  end

                  (_, _ <| _, _ <| _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- matchTypeTupleCall failed\\n")
                    fail()
                  end
                end
              end
               #=  We cannot use matchType here because it does not cast tuple calls properly
               =#
               #= /* (oe,_) = matchType(e, t1, t2, true);
                      true = Expression.expEqual(e,oe); */ =#
        end

         #= author: PA
          This function checks if a given type can be (converted and) vectorized to
          a expected type.
          For instance and argument of type Integer{:} can be vectorized to an
          argument type Real, using type coersion and vectorization of one dimension. =#
        function vectorizableType(inExp::DAE.Exp, inExpType::DAE.Type, inExpectedType::DAE.Type, fnPath::Option{<:Absyn.Path}) ::Tuple{DAE.Exp, DAE.Type, DAE.Dimensions, InstTypes.PolymorphicBindings}
              local outBindings::InstTypes.PolymorphicBindings
              local outArrayDimLst::DAE.Dimensions
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType, outArrayDimLst, outBindings) = vectorizableType2(inExp, inExpType, inExpType, nil, inExpectedType, fnPath)
          (outExp, outType, outArrayDimLst, outBindings)
        end

        function vectorizableType2(inExp::DAE.Exp, inExpType::DAE.Type, inCurrentType::DAE.Type, inDims::DAE.Dimensions, inExpectedType::DAE.Type, fnPath::Option{<:Absyn.Path}) ::Tuple{DAE.Exp, DAE.Type, DAE.Dimensions, InstTypes.PolymorphicBindings}
              local outBindings::InstTypes.PolymorphicBindings
              local outDims::DAE.Dimensions
              local outType::DAE.Type
              local outExp::DAE.Exp

              local vec_type::Type
              local cur_type::Type
              local dim::DAE.Dimension

              try
                vec_type = liftArrayListDimsReverse(inExpectedType, inDims)
                (outExp, outType, outBindings) = matchTypePolymorphic(inExp, inExpType, vec_type, fnPath, nil, true)
                outDims = listReverse(inDims)
              catch
                @match DAE.T_ARRAY(ty = cur_type, dims = list(dim)) = inCurrentType
                (outExp, outType, outDims, outBindings) = vectorizableType2(inExp, inExpType, cur_type, _cons(dim, inDims), inExpectedType, fnPath)
              end
          (outExp, outType, outDims, outBindings)
        end

         #= transforms T_ARRAY(a::b::c) to T_ARRAY(a, T_ARRAY(b, T_ARRAY(c)))
         Always call it with  =#
        function unflattenArrayType(inTy::DAE.Type) ::DAE.Type
              local outTy::DAE.Type

              outTy = unflattenArrayType2(inTy, false)
          outTy
        end

         #= transforms T_ARRAY(a::b::c) to T_ARRAY(a, T_ARRAY(b, T_ARRAY(c)))
         Always call it with  =#
        function unflattenArrayType2(inTy::DAE.Type, last::Bool) ::DAE.Type
              local outTy::DAE.Type

              outTy = begin
                  local ty::DAE.Type
                  local t::DAE.Type
                  local dims::DAE.Dimensions
                  local dim::DAE.Dimension
                  local ci::ClassInf.SMNode
                  local vl::List{DAE.Var}
                  local eqc::EqualityConstraint
                   #=  subtype basic crap
                   =#
                @matchcontinue (inTy, last) begin
                  (DAE.T_SUBTYPE_BASIC(ci, vl, ty, eqc), _)  => begin
                      ty = unflattenArrayType(ty)
                    DAE.T_SUBTYPE_BASIC(ci, vl, ty, eqc)
                  end

                  (DAE.T_ARRAY(t, dim <|  nil()), _)  => begin
                      t = unflattenArrayType(t)
                    DAE.T_ARRAY(t, list(dim))
                  end

                  (DAE.T_ARRAY(t,  nil()), true)  => begin
                    unflattenArrayType(t)
                  end

                  (DAE.T_ARRAY(t, dim <| dims), _)  => begin
                      ty = unflattenArrayType2(DAE.T_ARRAY(t, dims), true)
                      ty = DAE.T_ARRAY(ty, list(dim))
                    ty
                  end

                  (ty, false)  => begin
                    ty
                  end
                end
              end
               #=  already in the way we want it
               =#
               #=  we might get here via true!
               =#
               #=  the usual case
               =#
          outTy
        end

         #= This functions converts the expression in the first argument to
          the type specified in the third argument.  The current type of the
          expression is given in the second argument.
          If no type conversion is possible, this function fails. =#
        function typeConvert(inExp1::DAE.Exp, actual::DAE.Type, expected::DAE.Type, printFailtrace::Bool) ::Tuple{DAE.Exp, DAE.Type}
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType) = begin
                  local elist_1::List{DAE.Exp}
                  local elist::List{DAE.Exp}
                  local inputs::List{DAE.Exp}
                  local at::DAE.Type
                  local t::DAE.Type
                  local sc::Bool
                  local a::Bool
                  local nmax::ModelicaInteger
                  local oi::ModelicaInteger
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local dim11::DAE.Dimension
                  local dim22::DAE.Dimension
                  local dims::DAE.Dimensions
                  local ty1::Type
                  local ty2::Type
                  local t1::Type
                  local t2::Type
                  local t_1::Type
                  local t_2::Type
                  local ty0::Type
                  local ty::Type
                  local begin_1::DAE.Exp
                  local step_1::DAE.Exp
                  local stop_1::DAE.Exp
                  local begin_0::DAE.Exp
                  local step::DAE.Exp
                  local stop::DAE.Exp
                  local e_1::DAE.Exp
                  local e::DAE.Exp
                  local exp::DAE.Exp
                  local ell_1::List{List{DAE.Exp}}
                  local ell::List{List{DAE.Exp}}
                  local elist_big::List{List{DAE.Exp}}
                  local tys_1::List{DAE.Type}
                  local tys1::List{DAE.Type}
                  local tys2::List{DAE.Type}
                  local name::String
                  local l::List{String}
                  local v::List{DAE.Var}
                  local path::Absyn.Path
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local pathList::List{Absyn.Path}
                  local cref::DAE.ComponentRef
                  local crefList::List{DAE.ComponentRef}
                  local expTypes::List{DAE.Type}
                  local et::DAE.Type
                  local ety1::DAE.Type
                  local cases::List{DAE.MatchCase}
                  local matchTy::DAE.MatchType
                  local localDecls::List{DAE.Element}
                  local els1::List{DAE.Var}
                  local els2::List{DAE.Var}
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                  local tp::Absyn.Path
                  local aliases::List{List{String}}
                   #=  For the types that cannot be type-converted, but may be subtypes of another type
                   =#
                @matchcontinue (inExp1, actual, expected, printFailtrace) begin
                  (e, ty1, ty2, _)  => begin
                      @match true = subtype(ty1, ty2)
                    (e, ty2)
                  end

                  (e, DAE.T_TUPLE(types = ty1 <| _), ty2, _)  => begin
                      @match false = Config.acceptMetaModelicaGrammar()
                      @match false = isTuple(ty2)
                      @match true = subtype(ty1, ty2)
                      e = DAE.TSUB(e, 1, ty2)
                      ty = ty2
                    (e, ty)
                  end

                  (e, DAE.T_ARRAY(dims = _ <| _ <| _), ty2, _)  => begin
                      ty1 = unflattenArrayType(actual)
                      ty2 = unflattenArrayType(ty2)
                      (e, ty) = typeConvert(e, ty1, ty2, printFailtrace)
                    (e, ty)
                  end

                  (e, ty1, DAE.T_ARRAY(dims = _ <| _ <| _), _)  => begin
                      ty1 = unflattenArrayType(ty1)
                      ty2 = unflattenArrayType(expected)
                      (e, ty) = typeConvert(e, ty1, ty2, printFailtrace)
                    (e, ty)
                  end

                  (DAE.ARRAY(array = elist), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), ty0 && DAE.T_ARRAY(dims = dim2 <|  nil(), ty = ty2), _)  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      elist_1 = typeConvertArray(elist, ty1, ty2, printFailtrace)
                      at = simplifyType(ty0)
                      a = isArray(ty2)
                      sc = boolNot(a)
                    (DAE.ARRAY(at, sc, elist_1), DAE.T_ARRAY(ty2, list(dim1)))
                  end

                  (DAE.ARRAY(array = elist), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = ty2), _)  => begin
                      @match true = Expression.dimensionKnown(dim1)
                      elist_1 = typeConvertArray(elist, ty1, ty2, printFailtrace)
                      dims = Expression.arrayDimension(simplifyType(ty1))
                      a = isArray(ty2)
                      sc = boolNot(a)
                      dims = _cons(dim1, dims)
                      ty2 = arrayElementType(ty2)
                      ety1 = simplifyType(ty2)
                      ty2 = liftArrayListDims(ty2, dims)
                    (DAE.ARRAY(DAE.T_ARRAY(ety1, dims), sc, elist_1), ty2)
                  end

                  (DAE.RANGE(start = begin_0, step = SOME(step), stop = stop), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = ty2), _)  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      (begin_1, _) = typeConvert(begin_0, ty1, ty2, printFailtrace)
                      (step_1, _) = typeConvert(step, ty1, ty2, printFailtrace)
                      (stop_1, _) = typeConvert(stop, ty1, ty2, printFailtrace)
                      at = simplifyType(ty2)
                    (DAE.RANGE(at, begin_1, SOME(step_1), stop_1), DAE.T_ARRAY(ty2, list(dim1)))
                  end

                  (DAE.RANGE(start = begin_0, step = NONE(), stop = stop), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = ty2), _)  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      (begin_1, _) = typeConvert(begin_0, ty1, ty2, printFailtrace)
                      (stop_1, _) = typeConvert(stop, ty1, ty2, printFailtrace)
                      at = simplifyType(ty2)
                    (DAE.RANGE(at, begin_1, NONE(), stop_1), DAE.T_ARRAY(ty2, list(dim1)))
                  end

                  (DAE.MATRIX(integer = nmax, matrix = ell), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = DAE.T_ARRAY(dims = dim11 <|  nil(), ty = t1)), ty0 && DAE.T_ARRAY(dims = dim2 <|  nil(), ty = DAE.T_ARRAY(dims = dim22 <|  nil(), ty = t2)), _)  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      @match true = Expression.dimensionsKnownAndEqual(dim11, dim22)
                      ell_1 = typeConvertMatrix(ell, t1, t2, printFailtrace)
                      at = simplifyType(ty0)
                    (DAE.MATRIX(at, nmax, ell_1), DAE.T_ARRAY(DAE.T_ARRAY(t2, list(dim11)), list(dim1)))
                  end

                  (DAE.MATRIX(integer = nmax, matrix = ell), DAE.T_ARRAY(dims = dim1 <|  nil(), ty = DAE.T_ARRAY(dims = dim11 <|  nil(), ty = t1)), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = DAE.T_ARRAY(dims = dim22 <|  nil(), ty = t2)), _) where (! Expression.dimensionKnown(dim2))  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim11, dim22)
                      ell_1 = typeConvertMatrix(ell, t1, t2, printFailtrace)
                      ty = DAE.T_ARRAY(DAE.T_ARRAY(t2, list(dim11)), list(dim1))
                      at = simplifyType(ty)
                    (DAE.MATRIX(at, nmax, ell_1), ty)
                  end

                  (e, DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = ty2), _)  => begin
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      (e_1, t_1) = typeConvert(e, ty1, ty2, printFailtrace)
                      e_1 = liftExpType(e_1, dim1)
                      t_2 = DAE.T_ARRAY(t_1, list(dim2))
                    (e_1, t_2)
                  end

                  (e, DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = ty1), DAE.T_ARRAY(dims = _ <|  nil(), ty = ty2), _)  => begin
                      (e_1, t_1) = typeConvert(e, ty1, ty2, printFailtrace)
                      e_1 = liftExpType(e_1, DAE.DIM_UNKNOWN())
                    (e_1, DAE.T_ARRAY(t_1, list(DAE.DIM_UNKNOWN())))
                  end

                  (e, DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = ty2), _)  => begin
                      (e_1, t_1) = typeConvert(e, ty1, ty2, printFailtrace)
                      e_1 = liftExpType(e_1, dim1)
                    (e_1, DAE.T_ARRAY(t_1, list(dim1)))
                  end

                  (e, DAE.T_ARRAY(dims = dim1 <|  nil(), ty = ty1), DAE.T_ARRAY(dims = dim2 <|  nil(), ty = ty2), _)  => begin
                      @match false = Expression.dimensionKnown(dim1)
                      @match false = Expression.dimensionKnown(dim2)
                      (e_1, t_1) = typeConvert(e, ty1, ty2, printFailtrace)
                      e_1 = liftExpType(e_1, DAE.DIM_UNKNOWN())
                    (e_1, DAE.T_ARRAY(t_1, list(DAE.DIM_UNKNOWN())))
                  end

                  (DAE.TUPLE(PR = elist), DAE.T_TUPLE(types = tys1), DAE.T_TUPLE(types = tys2), _)  => begin
                      (elist_1, tys_1) = typeConvertList(elist, tys1, tys2, printFailtrace)
                    (DAE.TUPLE(elist_1), DAE.T_TUPLE(tys_1, expected.names))
                  end

                  (exp && DAE.ICONST(oi), DAE.T_INTEGER(__), t2 && DAE.T_ENUMERATION(path = tp, names = l), _)  => begin
                      @match true = Config.intEnumConversion()
                      @match true = typeConvertIntToEnumCheck(exp, t2)
                      name = listGet(l, oi)
                      tp = AbsynUtil.joinPaths(tp, Absyn.IDENT(name))
                    (DAE.ENUM_LITERAL(tp, oi), expected)
                  end

                  (e, DAE.T_INTEGER(__), DAE.T_REAL(__), _)  => begin
                    (DAE.CAST(DAE.T_REAL_DEFAULT, e), expected)
                  end

                  (e, DAE.T_SUBTYPE_BASIC(complexType = t1), t2, _)  => begin
                      (e_1, t_1) = typeConvert(e, t1, t2, printFailtrace)
                    (e_1, t_1)
                  end

                  (e, t1, DAE.T_SUBTYPE_BASIC(complexType = t2), _)  => begin
                      (e_1, t_1) = typeConvert(e, t1, t2, printFailtrace)
                    (e_1, t_1)
                  end

                  (e, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p1), varLst = els1), t2 && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(p2), varLst = els2), _)  => begin
                      @match false = AbsynUtil.pathEqual(p1, p2) #= We need to add a cast from one record to another =#
                      @match true = Flags.isSet(Flags.ALLOW_RECORD_TOO_MANY_FIELDS) || listLength(els1) == listLength(els2)
                      @match true = subtypeVarlist(els1, els2)
                      e = DAE.CAST(t2, e)
                    (e, t2)
                  end

                  (DAE.META_OPTION(SOME(e)), DAE.T_METAOPTION(ty = t1), DAE.T_METAOPTION(t2), _) where (Config.acceptMetaModelicaGrammar())  => begin
                      (e_1, t_1) = matchType(e, t1, t2, printFailtrace)
                    (DAE.META_OPTION(SOME(e_1)), DAE.T_METAOPTION(t_1))
                  end

                  (DAE.META_OPTION(NONE()), _, DAE.T_METAOPTION(t2), _) where (Config.acceptMetaModelicaGrammar())  => begin
                    (DAE.META_OPTION(NONE()), DAE.T_METAOPTION(t2))
                  end

                  (DAE.TUPLE(elist), DAE.T_TUPLE(types = tys1), DAE.T_METATUPLE(tys2), _) where (Config.acceptMetaModelicaGrammar())  => begin
                      tys2 = ListUtil.map(tys2, boxIfUnboxedType)
                      (elist_1, tys_1) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                    (DAE.META_TUPLE(elist_1), DAE.T_METATUPLE(tys_1))
                  end

                  (DAE.MATCHEXPRESSION(matchTy, inputs, aliases, localDecls, cases, et), _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      elist = Patternm.resultExps(cases)
                      (elist_1, _) = matchTypeList(elist, actual, expected, printFailtrace)
                      cases = Patternm.fixCaseReturnTypes2(cases, elist_1, AbsynUtil.dummyInfo)
                      et = simplifyType(expected)
                    (DAE.MATCHEXPRESSION(matchTy, inputs, aliases, localDecls, cases, et), expected)
                  end

                  (DAE.META_TUPLE(elist), DAE.T_METATUPLE(types = tys1), DAE.T_METATUPLE(tys2), _)  => begin
                      tys2 = ListUtil.map(tys2, boxIfUnboxedType)
                      (elist_1, tys_1) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                    (DAE.META_TUPLE(elist_1), DAE.T_METATUPLE(tys_1))
                  end

                  (DAE.TUPLE(elist), DAE.T_TUPLE(types = tys1), ty2 && DAE.T_METABOXED(ty = DAE.T_UNKNOWN(__)), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      tys2 = ListUtil.fill(ty2, listLength(tys1))
                      (elist_1, tys_1) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                    (DAE.META_TUPLE(elist_1), DAE.T_METATUPLE(tys_1))
                  end

                  (DAE.ARRAY(DAE.T_ARRAY(__), _, elist), DAE.T_ARRAY(ty = t1), DAE.T_METALIST(t2), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      t2 = boxIfUnboxedType(t2)
                      (elist_1, _) = matchTypeList(elist, t1, t2, printFailtrace)
                      e_1 = DAE.LIST(elist_1)
                      t2 = DAE.T_METALIST(t2)
                    (e_1, t2)
                  end

                  (DAE.ARRAY(DAE.T_ARRAY(__), _, elist), DAE.T_ARRAY(ty = t1), DAE.T_METABOXED(t2), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (elist_1, tys1) = matchTypeList(elist, t1, t2, printFailtrace)
                      (elist_1, t2) = listMatchSuperType(elist_1, tys1, printFailtrace)
                      t2 = boxIfUnboxedType(t2)
                      (elist_1, _) = matchTypeList(elist_1, t1, t2, printFailtrace)
                      e_1 = DAE.LIST(elist_1)
                      t2 = DAE.T_METALIST(t2)
                    (e_1, t2)
                  end

                  (DAE.MATRIX(DAE.T_ARRAY(__), _, elist_big), t1, t2, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (elist, ty2) = typeConvertMatrixToList(elist_big, t1, t2, printFailtrace)
                      e_1 = DAE.LIST(elist)
                    (e_1, ty2)
                  end

                  (DAE.LIST(elist), DAE.T_METALIST(ty = t1), DAE.T_METALIST(t2), _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      (elist_1, tys1) = matchTypeList(elist, t1, t2, printFailtrace)
                      (elist_1, t2) = listMatchSuperType(elist_1, tys1, printFailtrace)
                      e_1 = DAE.LIST(elist_1)
                      t2 = DAE.T_METALIST(t2)
                    (e_1, t2)
                  end

                  (e, t1 && DAE.T_INTEGER(__), DAE.T_METABOXED(ty = t2), _)  => begin
                      (e, t1) = matchType(e, t1, unboxedType(t2), printFailtrace)
                      t2 = DAE.T_METABOXED(t1)
                      e = Expression.boxExp(e)
                    (e, t2)
                  end

                  (e, t1 && DAE.T_BOOL(__), DAE.T_METABOXED(ty = t2), _)  => begin
                      (e, t1) = matchType(e, t1, unboxedType(t2), printFailtrace)
                      t2 = DAE.T_METABOXED(t1)
                      e = Expression.boxExp(e)
                    (e, t2)
                  end

                  (e, t1 && DAE.T_REAL(__), DAE.T_METABOXED(ty = t2), _)  => begin
                      (e, t1) = matchType(e, t1, unboxedType(t2), printFailtrace)
                      t2 = DAE.T_METABOXED(t1)
                      e = Expression.boxExp(e)
                    (e, t2)
                  end

                  (e, t1 && DAE.T_ENUMERATION(__), DAE.T_METABOXED(ty = t2), _)  => begin
                      (e, t1) = matchType(e, t1, unboxedType(t2), printFailtrace)
                      t2 = DAE.T_METABOXED(t1)
                      e = Expression.boxExp(e)
                    (e, t2)
                  end

                  (e, t1 && DAE.T_ARRAY(__), DAE.T_METABOXED(ty = t2), _)  => begin
                      (e, t1) = matchType(e, t1, unboxedType(t2), printFailtrace)
                      t2 = DAE.T_METABOXED(t1)
                      e = Expression.boxExp(e)
                    (e, t2)
                  end

                  (DAE.CALL(path = path1, expLst = elist), t1 && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path2), varLst = v), DAE.T_METABOXED(ty = t2), _)  => begin
                      @match true = subtype(t1, t2)
                      @match true = AbsynUtil.pathEqual(path1, path2)
                      t2 = DAE.T_METABOXED(t1)
                      l = ListUtil.map(v, getVarName)
                      tys1 = ListUtil.map(v, getVarType)
                      tys2 = ListUtil.map(tys1, boxIfUnboxedType)
                      (elist, _) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                      e_1 = DAE.METARECORDCALL(path1, elist, l, -1, nil)
                    (e_1, t2)
                  end

                  (DAE.RECORD(path = path1, exps = elist), t1 && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path2), varLst = v), DAE.T_METABOXED(ty = t2), _)  => begin
                      @match true = subtype(t1, t2)
                      @match true = AbsynUtil.pathEqual(path1, path2)
                      t2 = DAE.T_METABOXED(t1)
                      l = ListUtil.map(v, getVarName)
                      tys1 = ListUtil.map(v, getVarType)
                      tys2 = ListUtil.map(tys1, boxIfUnboxedType)
                      (elist, _) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                      e_1 = DAE.METARECORDCALL(path1, elist, l, -1, nil)
                    (e_1, t2)
                  end

                  (DAE.CREF(cref, _), t1 && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path), varLst = v), DAE.T_METABOXED(ty = t2), _)  => begin
                      @match true = subtype(t1, t2)
                      t2 = DAE.T_METABOXED(t1)
                      l = ListUtil.map(v, getVarName)
                      tys1 = ListUtil.map(v, getVarType)
                      tys2 = ListUtil.map(tys1, boxIfUnboxedType)
                      expTypes = ListUtil.map(tys1, simplifyType)
                      pathList = ListUtil.map(l, AbsynUtil.makeIdentPathFromString)
                      crefList = ListUtil.map(pathList, ComponentReference.pathToCref)
                      crefList = ListUtil.map1r(crefList, ComponentReference.joinCrefs, cref)
                      elist = ListUtil.threadMap(crefList, expTypes, Expression.makeCrefExp)
                      (elist, _) = matchTypeTuple(elist, tys1, tys2, printFailtrace)
                      e_1 = DAE.METARECORDCALL(path, elist, l, -1, nil)
                    (e_1, t2)
                  end

                  (e, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__)), DAE.T_METABOXED(__), _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Not yet implemented: Converting record into boxed records: " + ExpressionDump.printExpStr(e) + "\\n")
                    fail()
                  end

                  (DAE.BOX(e), DAE.T_METABOXED(ty = t1), t2, _)  => begin
                      @match true = subtype(t1, t2)
                      (e_1, t2) = matchType(e, t1, t2, printFailtrace)
                    (e_1, t2)
                  end

                  (e, DAE.T_METABOXED(ty = t1), t2 && DAE.T_INTEGER(__), _)  => begin
                      @match true = subtype(t1, t2)
                      (_, _) = matchType(e, t1, t2, printFailtrace)
                      t = simplifyType(t2)
                    (DAE.UNBOX(e, t), t2)
                  end

                  (e, DAE.T_METABOXED(ty = t1), t2 && DAE.T_REAL(__), _)  => begin
                      @match true = subtype(t1, t2)
                      (_, _) = matchType(e, t1, t2, printFailtrace)
                      t = simplifyType(t2)
                    (DAE.UNBOX(e, t), t2)
                  end

                  (e, DAE.T_METABOXED(ty = t1), t2 && DAE.T_BOOL(__), _)  => begin
                      @match true = subtype(t1, t2)
                      (_, _) = matchType(e, t1, t2, printFailtrace)
                      t = simplifyType(t2)
                    (DAE.UNBOX(e, t), t2)
                  end

                  (e, DAE.T_METABOXED(ty = t1), t2 && DAE.T_ENUMERATION(__), _)  => begin
                      @match true = subtype(t1, t2)
                      matchType(e, t1, t2, printFailtrace)
                      t = simplifyType(t2)
                    (DAE.UNBOX(e, t), t2)
                  end

                  (e, DAE.T_METABOXED(ty = t1), t2 && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)), _)  => begin
                      @match true = subtype(t1, t2)
                      (e_1, _) = matchType(e, t1, t2, printFailtrace)
                      t = simplifyType(t2)
                    (DAE.CALL(Absyn.IDENT("mmc_unbox_record"), list(e_1), DAE.CALL_ATTR(t, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())), t2)
                  end
                end
              end
          (outExp, outType)
        end

         #= help function to typeConvert. Changes the DAE.Type stored
        in expression (which is typically a CAST) by adding a dimension to it, making it into an array
        type. =#
        function liftExpType(ie::DAE.Exp, dim::DAE.Dimension) ::DAE.Exp
              local res::DAE.Exp

              res = begin
                  local ty::DAE.Type
                  local ty1::DAE.Type
                  local e::DAE.Exp
                @matchcontinue (ie, dim) begin
                  (DAE.CAST(ty, e), _)  => begin
                      ty1 = Expression.liftArrayR(ty, dim)
                    DAE.CAST(ty1, e)
                  end

                  (e, _)  => begin
                    e
                  end
                end
              end
          res
        end

         #= Calls typeConvert on a list of expressions. =#
        function typeConvertArray(inArray::List{<:DAE.Exp}, inActualType::DAE.Type, inExpectedType::DAE.Type, inPrintFailtrace::Bool) ::List{DAE.Exp}
              local outArray::List{DAE.Exp}

              outArray = begin
                  local e::DAE.Exp
                  local expl::List{DAE.Exp}
                   #=  Empty array. Create a dummy expression and try to type convert that, to
                   =#
                   #=  make sure that empty arrays are type checked.
                   =#
                @match (inArray, inActualType, inExpectedType, inPrintFailtrace) begin
                  ( nil(), _, _, _)  => begin
                      e = makeDummyExpFromType(inActualType)
                      (_, _) = typeConvert(e, inActualType, inExpectedType, inPrintFailtrace)
                    nil
                  end

                  _  => begin
                        (expl, _) = ListUtil.map3_2(inArray, typeConvert, inActualType, inExpectedType, inPrintFailtrace)
                      expl
                  end
                end
              end
          outArray
        end

         #=
          Helper function to type_convert. Handles matrix expressions.
         =#
        function typeConvertMatrix(inMatrix::List{<:List{<:DAE.Exp}}, inActualType::DAE.Type, inExpectedType::DAE.Type, printFailtrace::Bool) ::List{List{DAE.Exp}}
              local outMatrix::List{List{DAE.Exp}}

              outMatrix = ListUtil.map3(inMatrix, typeConvertArray, inActualType, inExpectedType, printFailtrace)
          outMatrix
        end

         #=
          Helper function to type_convert.
         =#
        function typeConvertList(inExpExpLst1::List{<:DAE.Exp}, inTypeLst2::List{<:DAE.Type}, inTypeLst3::List{<:DAE.Type}, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTypeLst::List{DAE.Type}
              local outExpExpLst::List{DAE.Exp}

              (outExpExpLst, outTypeLst) = begin
                  local rest_1::List{DAE.Exp}
                  local rest::List{DAE.Exp}
                  local tyrest_1::List{DAE.Type}
                  local ty1rest::List{DAE.Type}
                  local ty2rest::List{DAE.Type}
                  local first_1::DAE.Exp
                  local first::DAE.Exp
                  local ty_1::Type
                  local ty1::Type
                  local ty2::Type
                @match (inExpExpLst1, inTypeLst2, inTypeLst3, printFailtrace) begin
                  ( nil(), _, _, _)  => begin
                    (nil, nil)
                  end

                  (first <| rest, ty1 <| ty1rest, ty2 <| ty2rest, _)  => begin
                      (rest_1, tyrest_1) = typeConvertList(rest, ty1rest, ty2rest, printFailtrace)
                      (first_1, ty_1) = typeConvert(first, ty1, ty2, printFailtrace)
                    (_cons(first_1, rest_1), _cons(ty_1, tyrest_1))
                  end
                end
              end
          (outExpExpLst, outTypeLst)
        end

        function typeConvertMatrixToList(melist::List{<:List{<:DAE.Exp}}, inType::DAE.Type, outType::DAE.Type, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, DAE.Type}
              local actualOutType::DAE.Type
              local outExp::List{DAE.Exp}

              (outExp, actualOutType) = begin
                  local expl::List{DAE.Exp}
                  local rest::List{List{DAE.Exp}}
                  local t::DAE.Type
                  local t1::Type
                  local t2::Type
                  local e::DAE.Exp
                @matchcontinue (melist, inType, outType, printFailtrace) begin
                  ( nil(), _, _, _)  => begin
                    (nil, DAE.T_UNKNOWN_DEFAULT)
                  end

                  (expl <| rest, DAE.T_ARRAY(ty = DAE.T_ARRAY(ty = t1)), DAE.T_METALIST(ty = DAE.T_METALIST(ty = t2)), _)  => begin
                      (e, t1) = typeConvertMatrixRowToList(expl, t1, t2, printFailtrace)
                      (expl, _) = typeConvertMatrixToList(rest, inType, outType, printFailtrace)
                    (_cons(e, expl), DAE.T_METALIST(t1))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.TYPES)
                        Debug.trace("- typeConvertMatrixToList failed\\n")
                      fail()
                  end
                end
              end
          (outExp, actualOutType)
        end

        function typeConvertMatrixRowToList(elist::List{<:DAE.Exp}, inType::DAE.Type, outType::DAE.Type, printFailtrace::Bool) ::Tuple{DAE.Exp, DAE.Type}
              local t1::DAE.Type
              local out::DAE.Exp

              local exp::DAE.Exp
              local elist_1::List{DAE.Exp}
              local t::DAE.Type

              (elist_1, _cons(t1, _)) = matchTypeList(elist, inType, outType, printFailtrace)
              out = DAE.LIST(elist_1)
              t1 = DAE.T_METALIST(t1)
          (out, t1)
        end

         #= This function is used for matching expressions in matrix construction,
          where automatic promotion is allowed. This means that array dimensions of
          size one (1) is added from the right to arrays of matrix construction until
          all elements have the same dimension size (with a maximum of 2).
          For instance, {1,{2}} becomes {1,2}.
          The function also has a flag indicating that Integer to Real
          conversion can be used. =#
        function matchWithPromote(inProperties1::DAE.Properties, inProperties2::DAE.Properties, inBoolean3::Bool) ::DAE.Properties
              local outProperties::DAE.Properties

              outProperties = begin
                  local t::Type
                  local t1::Type
                  local t2::Type
                  local c::Const
                  local c1::Const
                  local c2::Const
                  local dim::DAE.Dimension
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local havereal::Bool
                  local v::List{DAE.Var}
                  local tt::Type
                @matchcontinue (inProperties1, inProperties2, inBoolean3) begin
                  (DAE.PROP(DAE.T_SUBTYPE_BASIC(complexType = t1), c1), DAE.PROP(t2, c2), havereal)  => begin
                    matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                  end

                  (DAE.PROP(t1, c1), DAE.PROP(DAE.T_SUBTYPE_BASIC(complexType = t2), c2), havereal)  => begin
                    matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                  end

                  (DAE.PROP(type_ = DAE.T_ARRAY(dims = dim1 <|  nil(), ty = t1), constFlag = c1), DAE.PROP(type_ = DAE.T_ARRAY(dims = _ <|  nil(), ty = t2), constFlag = c2), havereal)  => begin
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                      dim = dim1
                    DAE.PROP(DAE.T_ARRAY(t, list(dim)), c)
                  end

                  (DAE.PROP(type_ = t1, constFlag = c1), DAE.PROP(type_ = DAE.T_ARRAY(dims = DAE.DIM_INTEGER(1) <|  nil(), ty = t2), constFlag = c2), havereal)  => begin
                      @match false = isArray(t1)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(1))), c)
                  end

                  (DAE.PROP(type_ = t1, constFlag = c1), DAE.PROP(type_ = DAE.T_ARRAY(dims = dim && DAE.DIM_ENUM(size = 1) <|  nil(), ty = t2), constFlag = c2), havereal)  => begin
                      @match false = isArray(t1)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(dim)), c)
                  end

                  (DAE.PROP(type_ = t1, constFlag = c1), DAE.PROP(type_ = DAE.T_ARRAY(dims = dim && DAE.DIM_BOOLEAN(__) <|  nil(), ty = t2), constFlag = c2), havereal)  => begin
                      @match false = isArray(t1)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(dim)), c)
                  end

                  (DAE.PROP(type_ = DAE.T_ARRAY(dims = DAE.DIM_INTEGER(1) <|  nil(), ty = t1), constFlag = c1), DAE.PROP(type_ = t2, constFlag = c2), havereal)  => begin
                      @match false = isArray(t2)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(DAE.DIM_INTEGER(1))), c)
                  end

                  (DAE.PROP(type_ = DAE.T_ARRAY(dims = dim && DAE.DIM_ENUM(size = 1) <|  nil(), ty = t1), constFlag = c1), DAE.PROP(type_ = t2, constFlag = c2), havereal)  => begin
                      @match false = isArray(t2)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(dim)), c)
                  end

                  (DAE.PROP(type_ = DAE.T_ARRAY(dims = dim && DAE.DIM_BOOLEAN(__) <|  nil(), ty = t1), constFlag = c1), DAE.PROP(type_ = t2, constFlag = c2), havereal)  => begin
                      @match false = isArray(t2)
                      @match DAE.PROP(t, c) = matchWithPromote(DAE.PROP(t1, c1), DAE.PROP(t2, c2), havereal)
                    DAE.PROP(DAE.T_ARRAY(t, list(dim)), c)
                  end

                  (DAE.PROP(type_ = t1, constFlag = c1), DAE.PROP(type_ = t2, constFlag = c2), false)  => begin
                      @match false = isArray(t1)
                      @match false = isArray(t2)
                      @match true = equivtypes(t1, t2)
                      c = constAnd(c1, c2)
                    DAE.PROP(t1, c)
                  end

                  (DAE.PROP(type_ = t && DAE.T_ENUMERATION(__), constFlag = c1), DAE.PROP(type_ = DAE.T_ENUMERATION(__), constFlag = c2), false)  => begin
                      c = constAnd(c1, c2) #= Have enum and both Enum =#
                    DAE.PROP(t, c)
                  end

                  (DAE.PROP(type_ = DAE.T_REAL(varLst = v), constFlag = c1), DAE.PROP(type_ = DAE.T_REAL(__), constFlag = c2), true)  => begin
                      c = constAnd(c1, c2) #= Have real and both Real =#
                    DAE.PROP(DAE.T_REAL(v), c)
                  end

                  (DAE.PROP(type_ = DAE.T_INTEGER(__), constFlag = c1), DAE.PROP(type_ = DAE.T_REAL(varLst = v), constFlag = c2), true)  => begin
                      c = constAnd(c1, c2) #= Have real and first Integer =#
                    DAE.PROP(DAE.T_REAL(v), c)
                  end

                  (DAE.PROP(type_ = DAE.T_REAL(varLst = v), constFlag = c1), DAE.PROP(type_ = DAE.T_INTEGER(__), constFlag = c2), true)  => begin
                      c = constAnd(c1, c2) #= Have real and second Integer =#
                    DAE.PROP(DAE.T_REAL(v), c)
                  end

                  (DAE.PROP(type_ = DAE.T_INTEGER(__), constFlag = c1), DAE.PROP(type_ = DAE.T_INTEGER(__), constFlag = c2), true)  => begin
                      c = constAnd(c1, c2) #= Have real and both Integer =#
                    DAE.PROP(DAE.T_REAL_DEFAULT, c)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Types.matchWithPromote failed on: " + "\\nprop1: " + printPropStr(inProperties1) + "\\nprop2: " + printPropStr(inProperties2) + "\\nhaveReal: " + boolString(inBoolean3))
                      fail()
                  end
                end
              end
               #=  Allow Integer => Real
               =#
               #=  match integer, second
               =#
               #=  match enum, second
               =#
               #=  match boolean, second
               =#
               #=  match integer, first
               =#
               #=  match enum, first
               =#
               #=  match boolean, first
               =#
               #=  equal types
               =#
               #=  enums
               =#
               #=  reals
               =#
               #=  integer vs. real
               =#
               #=  real vs. integer
               =#
               #=  both integers
               =#
          outProperties
        end

         #= Returns the *and* operator of two Consts.
          I.e. C_CONST iff. both are C_CONST,
               C_PARAM iff both are C_PARAM (or one of them C_CONST),
               V_VAR otherwise. =#
        function constAnd(inConst1::DAE.Const, inConst2::DAE.Const) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                @match (inConst1, inConst2) begin
                  (DAE.C_CONST(__), DAE.C_CONST(__))  => begin
                    DAE.C_CONST()
                  end

                  (DAE.C_CONST(__), DAE.C_PARAM(__))  => begin
                    DAE.C_PARAM()
                  end

                  (DAE.C_PARAM(__), DAE.C_CONST(__))  => begin
                    DAE.C_PARAM()
                  end

                  (DAE.C_PARAM(__), DAE.C_PARAM(__))  => begin
                    DAE.C_PARAM()
                  end

                  (DAE.C_UNKNOWN(__), _)  => begin
                    DAE.C_UNKNOWN()
                  end

                  (_, DAE.C_UNKNOWN(__))  => begin
                    DAE.C_UNKNOWN()
                  end

                  _  => begin
                      DAE.C_VAR()
                  end
                end
              end
          outConst
        end

         #= Returns the *and* operator of two TupleConsts
          For now, returns first tuple. =#
        function constTupleAnd(inTupleConst1::DAE.TupleConst, inTupleConst2::DAE.TupleConst) ::DAE.TupleConst
              local outTupleConst::DAE.TupleConst

              outTupleConst = begin
                  local c1::TupleConst
                  local c2::TupleConst
                @match (inTupleConst1, inTupleConst2) begin
                  (c1, _)  => begin
                    c1
                  end
                end
              end
          outTupleConst
        end

         #= Returns the *or* operator of two Const's.
          I.e. C_CONST if some is C_CONST,
               C_PARAM if none is C_CONST but some is C_PARAM and
               V_VAR otherwise. =#
        function constOr(inConst1::DAE.Const, inConst2::DAE.Const) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                @match (inConst1, inConst2) begin
                  (DAE.C_CONST(__), _)  => begin
                    DAE.C_CONST()
                  end

                  (_, DAE.C_CONST(__))  => begin
                    DAE.C_CONST()
                  end

                  (DAE.C_PARAM(__), _)  => begin
                    DAE.C_PARAM()
                  end

                  (_, DAE.C_PARAM(__))  => begin
                    DAE.C_PARAM()
                  end

                  (DAE.C_UNKNOWN(__), _)  => begin
                    DAE.C_UNKNOWN()
                  end

                  (_, DAE.C_UNKNOWN(__))  => begin
                    DAE.C_UNKNOWN()
                  end

                  _  => begin
                      DAE.C_VAR()
                  end
                end
              end
          outConst
        end

         #= author: PA
          Creates a Const value from a bool.
          if true, C_CONST,
          if false C_VAR
          There is no way to create a C_PARAM using this function. =#
        function boolConst(inBoolean::Bool) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                @match inBoolean begin
                  false  => begin
                    DAE.C_VAR()
                  end

                  true  => begin
                    DAE.C_CONST()
                  end
                end
              end
          outConst
        end

         #= author: alleb
          A version of boolConst supposed to be used by Static.elabBuiltinSize.
          Creates a Const value from a bool. If true, C_CONST, if false C_PARAM. =#
        function boolConstSize(inBoolean::Bool) ::DAE.Const
              local outConst::DAE.Const

              outConst = begin
                @match inBoolean begin
                  false  => begin
                    DAE.C_PARAM()
                  end

                  true  => begin
                    DAE.C_CONST()
                  end
                end
              end
          outConst
        end

        function constEqualOrHigher(c1::DAE.Const, c2::DAE.Const) ::Bool
              local b::Bool

              b = begin
                @match (c1, c2) begin
                  (DAE.C_CONST(__), _)  => begin
                    true
                  end

                  (_, DAE.C_CONST(__))  => begin
                    false
                  end

                  (DAE.C_PARAM(__), _)  => begin
                    true
                  end

                  (_, DAE.C_PARAM(__))  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

        function constEqual(c1::DAE.Const, c2::DAE.Const) ::Bool
              local b::Bool

              b = begin
                @matchcontinue (c1, c2) begin
                  (_, _)  => begin
                      equality(c1, c2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if Const is C_VAR. =#
        function constIsVariable(c::DAE.Const) ::Bool
              local b::Bool

              b = constEqual(c, DAE.C_VAR())
          b
        end

         #= Returns true if Const is C_PARAM. =#
        function constIsParameter(c::DAE.Const) ::Bool
              local b::Bool

              b = constEqual(c, DAE.C_PARAM())
          b
        end

         #= Returns true if Const is C_CONST. =#
        function constIsConst(c::DAE.Const) ::Bool
              local b::Bool

              b = constEqual(c, DAE.C_CONST())
          b
        end

         #= Print the properties to a string. =#
        function printPropStr(inProperties::DAE.Properties) ::String
              local outString::String

              outString = begin
                  local ty_str::String
                  local const_str::String
                  local res::String
                  local ty::DAE.Type
                  local constType::DAE.Const
                  local tconst::DAE.TupleConst
                @match inProperties begin
                  DAE.PROP(type_ = ty, constFlag = constType)  => begin
                      ty_str = unparseType(ty)
                      const_str = printConstStr(constType)
                      res = stringAppendList(list("DAE.PROP(", ty_str, ", ", const_str, ")"))
                    res
                  end

                  DAE.PROP_TUPLE(type_ = ty, tupleConst = tconst)  => begin
                      ty_str = unparseType(ty)
                      const_str = printTupleConstStr(tconst)
                      res = stringAppendList(list("DAE.PROP_TUPLE(", ty_str, ", ", const_str, ")"))
                    res
                  end
                end
              end
          outString
        end

         #= Print the Properties to the Print buffer. =#
        function printProp(p::DAE.Properties)
              local str::String

              str = printPropStr(p)
              Print.printErrorBuf(str)
        end

         #= This function retrieves all variables names that are flow variables, and
          prepends the prefix given as an DAE.ComponentRef =#
        function flowVariables(inVarLst::List{<:DAE.Var}, inComponentRef::DAE.ComponentRef) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local res::List{DAE.ComponentRef}
                  local id::String
                  local vs::List{DAE.Var}
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local cref_::DAE.ComponentRef
                   #=  handle empty case
                   =#
                @matchcontinue (inVarLst, inComponentRef) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.TYPES_VAR(name = id, attributes = DAE.ATTR(connectorType = DAE.FLOW(__)), ty = ty) <| vs, cr)  => begin
                      ty2 = simplifyType(ty)
                      cr_1 = ComponentReference.crefPrependIdent(cr, id, nil, ty2)
                      res = flowVariables(vs, cr)
                    _cons(cr_1, res)
                  end

                  (_ <| vs, cr)  => begin
                      res = flowVariables(vs, cr)
                    res
                  end
                end
              end
               #=  we have a flow prefix
               =#
               #=  print(\"\\n created: \" + ComponentReference.debugPrintComponentRefTypeStr(cr_1) + \"\\n\");
               =#
               #=  handle the rest
               =#
          outExpComponentRefLst
        end

         #= This function retrieves all variables names that are stream variables,
          and prepends the prefix given as an DAE.ComponentRef =#
        function streamVariables(inVarLst::List{<:DAE.Var}, inComponentRef::DAE.ComponentRef) ::List{DAE.ComponentRef}
              local outExpComponentRefLst::List{DAE.ComponentRef}

              outExpComponentRefLst = begin
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local res::List{DAE.ComponentRef}
                  local id::String
                  local vs::List{DAE.Var}
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local cref_::DAE.ComponentRef
                @matchcontinue (inVarLst, inComponentRef) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.TYPES_VAR(name = id, attributes = DAE.ATTR(connectorType = DAE.STREAM(__)), ty = ty) <| vs, cr)  => begin
                      ty2 = simplifyType(ty)
                      cr_1 = ComponentReference.crefPrependIdent(cr, id, nil, ty2)
                      res = streamVariables(vs, cr)
                    _cons(cr_1, res)
                  end

                  (_ <| vs, cr)  => begin
                      res = streamVariables(vs, cr)
                    res
                  end
                end
              end
          outExpComponentRefLst
        end

         #= This function goes through the Type structure and finds all the
          expressions and returns them in a list =#
        function getAllExps(inType::DAE.Type) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = getAllExpsTt(inType)
          outExpExpLst
        end

         #= This function goes through the TType structure and finds all the
          expressions and returns them in a list =#
        function getAllExpsTt(inType::DAE.Type) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = begin
                  local exps::List{DAE.Exp}
                  local tyexps::List{DAE.Exp}
                  local vars::List{DAE.Var}
                  local attrs::List{DAE.Var}
                  local strs::List{String}
                  local dim::DAE.Dimension
                  local ty::Type
                  local cinf::ClassInf.SMNode
                  local bc::Option{DAE.Type}
                  local tys::List{DAE.Type}
                  local explists::List{List{DAE.Exp}}
                  local explist::List{List{DAE.Exp}}
                  local fargs::List{DAE.FuncArg}
                  local tty::Type
                  local str::String
                @matchcontinue inType begin
                  DAE.T_INTEGER(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_REAL(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_STRING(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_BOOL(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_CLOCK(__)  => begin
                    nil
                  end

                  DAE.T_ENUMERATION(literalVarLst = vars, attributeLst = attrs)  => begin
                      exps = getAllExpsVars(vars)
                      tyexps = getAllExpsVars(attrs)
                      exps = listAppend(tyexps, exps)
                    exps
                  end

                  DAE.T_ARRAY(ty = ty)  => begin
                    getAllExps(ty)
                  end

                  DAE.T_COMPLEX(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_SUBTYPE_BASIC(varLst = vars)  => begin
                    getAllExpsVars(vars)
                  end

                  DAE.T_FUNCTION(funcArg = fargs, funcResultType = ty)  => begin
                      explists = ListUtil.mapMap(fargs, funcArgType, getAllExps)
                      tyexps = getAllExps(ty)
                      exps = ListUtil.flatten(_cons(tyexps, explists))
                    exps
                  end

                  DAE.T_TUPLE(types = tys)  => begin
                      explist = ListUtil.map(tys, getAllExps)
                      exps = ListUtil.flatten(explist)
                    exps
                  end

                  DAE.T_METATUPLE(types = tys)  => begin
                      exps = getAllExpsTt(DAE.T_TUPLE(tys, NONE()))
                    exps
                  end

                  DAE.T_METAUNIONTYPE(__)  => begin
                    nil
                  end

                  DAE.T_METAOPTION(ty = ty)  => begin
                    getAllExps(ty)
                  end

                  DAE.T_METALIST(ty = ty)  => begin
                    getAllExps(ty)
                  end

                  DAE.T_METAARRAY(ty = ty)  => begin
                    getAllExps(ty)
                  end

                  DAE.T_METABOXED(ty = ty)  => begin
                    getAllExps(ty)
                  end

                  DAE.T_METAPOLYMORPHIC(__)  => begin
                    nil
                  end

                  DAE.T_UNKNOWN(__)  => begin
                    nil
                  end

                  DAE.T_NORETCALL(__)  => begin
                    nil
                  end

                  tty  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      str = unparseType(tty)
                      Debug.traceln("-- Types.getAllExpsTt failed " + str)
                    fail()
                  end
                end
              end
               #=  BTH return empty list for clock since it doesn't have attributes
               =#
          outExpExpLst
        end

         #= Helper function to getAllExpsTt. =#
        function getAllExpsVars(vars::List{<:DAE.Var}) ::List{DAE.Exp}
              local exps::List{DAE.Exp}

              local explist::List{List{DAE.Exp}}

              explist = ListUtil.map(vars, getAllExpsVar)
              exps = ListUtil.flatten(explist)
          exps
        end

         #= Helper function to getAllExpsVars. =#
        function getAllExpsVar(inVar::DAE.Var) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = begin
                  local tyexps::List{DAE.Exp}
                  local bndexp::List{DAE.Exp}
                  local exps::List{DAE.Exp}
                  local id::String
                  local ty::DAE.Type
                  local bnd::DAE.Binding
                @match inVar begin
                  DAE.TYPES_VAR(ty = ty, binding = bnd)  => begin
                      tyexps = getAllExps(ty)
                      bndexp = getAllExpsBinding(bnd)
                      exps = listAppend(tyexps, bndexp)
                    exps
                  end
                end
              end
          outExpExpLst
        end

         #= Helper function to get_all_exps_var. =#
        function getAllExpsBinding(inBinding::DAE.Binding) ::List{DAE.Exp}
              local outExpExpLst::List{DAE.Exp}

              outExpExpLst = begin
                  local exp::DAE.Exp
                  local cnst::Const
                  local v::Values.Value
                @match inBinding begin
                  DAE.EQBOUND(exp = exp)  => begin
                    list(exp)
                  end

                  DAE.UNBOUND(__)  => begin
                    nil
                  end

                  DAE.VALBOUND(__)  => begin
                    nil
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("-- Types.getAllExpsBinding failed\\n")
                      fail()
                  end
                end
              end
          outExpExpLst
        end

        function isBoxedType(ty::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_STRING(__)  => begin
                    true
                  end

                  DAE.T_METAOPTION(__)  => begin
                    true
                  end

                  DAE.T_METALIST(__)  => begin
                    true
                  end

                  DAE.T_METATUPLE(__)  => begin
                    true
                  end

                  DAE.T_METAUNIONTYPE(__)  => begin
                    true
                  end

                  DAE.T_METARECORD(__)  => begin
                    true
                  end

                  DAE.T_METAPOLYMORPHIC(__)  => begin
                    true
                  end

                  DAE.T_METAARRAY(__)  => begin
                    true
                  end

                  DAE.T_FUNCTION(__)  => begin
                    true
                  end

                  DAE.T_METABOXED(__)  => begin
                    true
                  end

                  DAE.T_ANYTYPE(__)  => begin
                    true
                  end

                  DAE.T_UNKNOWN(__)  => begin
                    true
                  end

                  DAE.T_METATYPE(__)  => begin
                    true
                  end

                  DAE.T_NORETCALL(__)  => begin
                    true
                  end

                  DAE.T_CODE(__)  => begin
                    true
                  end

                  DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isMetaBoxedType(inType::DAE.Type) ::Bool
              local outIsMetaBoxed::Bool

              outIsMetaBoxed = begin
                @match inType begin
                  DAE.T_METABOXED(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsMetaBoxed
        end

        function boxIfUnboxedType(ty::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local tys::List{DAE.Type}
                @matchcontinue ty begin
                  DAE.T_TUPLE(__)  => begin
                      tys = ListUtil.map(ty.types, boxIfUnboxedType)
                    DAE.T_METATUPLE(tys)
                  end

                  _  => begin
                      if isBoxedType(ty)
                            ty
                          else
                            DAE.T_METABOXED(ty)
                          end
                  end
                end
              end
               #=  TODO?! should now propagate the type source?
               =#
          outType
        end

        function unboxedType(ity::DAE.Type) ::DAE.Type
              local out::DAE.Type

              out = begin
                  local tys::List{DAE.Type}
                  local t::Type
                  local ty::Type
                @match ity begin
                  DAE.T_METABOXED(__)  => begin
                    unboxedType(ity.ty)
                  end

                  DAE.T_METAOPTION(__)  => begin
                      ty = unboxedType(ity.ty)
                      ty = boxIfUnboxedType(ty)
                    DAE.T_METAOPTION(ty)
                  end

                  DAE.T_METALIST(__)  => begin
                      ty = unboxedType(ity.ty)
                      ty = boxIfUnboxedType(ty)
                    DAE.T_METALIST(ty)
                  end

                  DAE.T_METATUPLE(__)  => begin
                      tys = ListUtil.mapMap(ity.types, unboxedType, boxIfUnboxedType)
                    DAE.T_METATUPLE(tys)
                  end

                  DAE.T_METAARRAY(__)  => begin
                      ty = unboxedType(ity.ty)
                      ty = boxIfUnboxedType(ty)
                    DAE.T_METAARRAY(ty)
                  end

                  t && DAE.T_ARRAY(__)  => begin
                      t.ty = unboxedType(t.ty)
                    t
                  end

                  _  => begin
                      ity
                  end
                end
              end
          out
        end

         #= Takes lists of Exp,Type and calculates the
        supertype of the list, then converts the expressions to this type.
         =#
        function listMatchSuperType(ielist::List{<:DAE.Exp}, typeList::List{<:DAE.Type}, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, DAE.Type}
              local t::DAE.Type
              local out::List{DAE.Exp}

              (out, t) = begin
                  local e::DAE.Exp
                  local ty::Type
                  local st::Type
                  local elist::List{DAE.Exp}
                @matchcontinue (ielist, typeList, printFailtrace) begin
                  ( nil(),  nil(), _)  => begin
                    (nil, DAE.T_UNKNOWN_DEFAULT)
                  end

                  (_ <| _, _ <| _, _)  => begin
                      st = ListUtil.reduce(typeList, superType)
                      st = superType(st, st)
                      st = unboxedType(st)
                      elist = listMatchSuperType2(ielist, typeList, st, printFailtrace)
                    (elist, st)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Types.listMatchSuperType failed\\n")
                      fail()
                  end
                end
              end
          (out, t)
        end

        function listMatchSuperType2(elist::List{<:DAE.Exp}, typeList::List{<:DAE.Type}, st::DAE.Type, printFailtrace::Bool) ::List{DAE.Exp}
              local out::List{DAE.Exp}

              out = begin
                  local e::DAE.Exp
                  local erest::List{DAE.Exp}
                  local t::Type
                  local trest::List{DAE.Type}
                  local str::String
                @matchcontinue (elist, typeList, st, printFailtrace) begin
                  ( nil(),  nil(), _, _)  => begin
                    nil
                  end

                  (e <| erest, t <| trest, _, _)  => begin
                      (e, t) = matchType(e, t, st, printFailtrace)
                      erest = listMatchSuperType2(erest, trest, st, printFailtrace)
                    _cons(e, erest)
                  end

                  (e <| _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      str = ExpressionDump.printExpStr(e)
                      Debug.traceln("- Types.listMatchSuperType2 failed: " + str)
                    fail()
                  end
                end
              end
          out
        end

         #= find the supertype of the two types =#
        function superType(inType1::DAE.Type, inType2::DAE.Type) ::DAE.Type
              local out::DAE.Type

              out = begin
                  local t1::Type
                  local t2::Type
                  local tp::Type
                  local type_list1::List{DAE.Type}
                  local type_list2::List{DAE.Type}
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                @matchcontinue (inType1, inType2) begin
                  (DAE.T_ANYTYPE(__), t2)  => begin
                    t2
                  end

                  (t1, DAE.T_ANYTYPE(__))  => begin
                    t1
                  end

                  (DAE.T_UNKNOWN(__), t2)  => begin
                    t2
                  end

                  (t1, DAE.T_UNKNOWN(__))  => begin
                    t1
                  end

                  (_, t2 && DAE.T_METAPOLYMORPHIC(__))  => begin
                    t2
                  end

                  (DAE.T_TUPLE(types = type_list1), DAE.T_TUPLE(types = type_list2))  => begin
                      type_list1 = ListUtil.map(type_list1, boxIfUnboxedType)
                      type_list2 = ListUtil.map(type_list2, boxIfUnboxedType)
                      type_list1 = ListUtil.threadMap(type_list1, type_list2, superType)
                    DAE.T_METATUPLE(type_list1)
                  end

                  (DAE.T_TUPLE(types = type_list1), DAE.T_METATUPLE(types = type_list2))  => begin
                      type_list1 = ListUtil.map(type_list1, boxIfUnboxedType)
                      type_list2 = ListUtil.map(type_list2, boxIfUnboxedType)
                      type_list1 = ListUtil.threadMap(type_list1, type_list2, superType)
                    DAE.T_METATUPLE(type_list1)
                  end

                  (DAE.T_METATUPLE(types = type_list1), DAE.T_TUPLE(types = type_list2))  => begin
                      type_list1 = ListUtil.map(type_list1, boxIfUnboxedType)
                      type_list2 = ListUtil.map(type_list2, boxIfUnboxedType)
                      type_list1 = ListUtil.threadMap(type_list1, type_list2, superType)
                    DAE.T_METATUPLE(type_list1)
                  end

                  (DAE.T_METATUPLE(types = type_list1), DAE.T_METATUPLE(types = type_list2))  => begin
                      type_list1 = ListUtil.map(type_list1, boxIfUnboxedType)
                      type_list2 = ListUtil.map(type_list2, boxIfUnboxedType)
                      type_list1 = ListUtil.threadMap(type_list1, type_list2, superType)
                    DAE.T_METATUPLE(type_list1)
                  end

                  (DAE.T_METALIST(ty = t1), DAE.T_METALIST(ty = t2))  => begin
                      t1 = boxIfUnboxedType(t1)
                      t2 = boxIfUnboxedType(t2)
                      tp = superType(t1, t2)
                    DAE.T_METALIST(tp)
                  end

                  (DAE.T_METAOPTION(ty = t1), DAE.T_METAOPTION(ty = t2))  => begin
                      t1 = boxIfUnboxedType(t1)
                      t2 = boxIfUnboxedType(t2)
                      tp = superType(t1, t2)
                    DAE.T_METAOPTION(tp)
                  end

                  (DAE.T_METAARRAY(ty = t1), DAE.T_METAARRAY(ty = t2))  => begin
                      t1 = boxIfUnboxedType(t1)
                      t2 = boxIfUnboxedType(t2)
                      tp = superType(t1, t2)
                    DAE.T_METAARRAY(tp)
                  end

                  (t1 && DAE.T_METAUNIONTYPE(path = path1), DAE.T_METARECORD(utPath = path2))  => begin
                      @match true = AbsynUtil.pathEqual(path1, path2)
                    t1
                  end

                  (DAE.T_METARECORD(knownSingleton = false, utPath = path1), DAE.T_METARECORD(knownSingleton = false, utPath = path2))  => begin
                      @match true = AbsynUtil.pathEqual(path1, path2)
                    DAE.T_METAUNIONTYPE(nil, inType1.typeVars, false, DAE.NOT_SINGLETON(), path1)
                  end

                  (DAE.T_INTEGER(__), DAE.T_REAL(__))  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  (DAE.T_REAL(__), DAE.T_INTEGER(__))  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  (t1, t2)  => begin
                      @match true = subtype(t1, t2)
                    t2
                  end

                  (t1, t2)  => begin
                      @match true = subtype(t2, t1)
                    t1
                  end
                end
              end
          out
        end

         #= Like matchType, except we also
        bind polymorphic variabled. Used when elaborating calls. =#
        function matchTypePolymorphic(iexp::DAE.Exp, iactual::DAE.Type, expected::DAE.Type, envPath::Option{<:Absyn.Path} #= to detect which polymorphic types are recursive =#, ipolymorphicBindings::InstTypes.PolymorphicBindings, printFailtrace::Bool) ::Tuple{DAE.Exp, DAE.Type, InstTypes.PolymorphicBindings}
              local polymorphicBindings::InstTypes.PolymorphicBindings = ipolymorphicBindings
              local actual::DAE.Type = iactual
              local exp::DAE.Exp = iexp

              local debug::Bool = false

              if listEmpty(getAllInnerTypesOfType(expected, isPolymorphic))
                (exp, actual) = matchType(exp, actual, expected, printFailtrace)
              else
                if debug
                  print("match type: " + ExpressionDump.printExpStr(exp) + " of " + unparseType(actual) + " with " + unparseType(expected) + "\\n")
                end
                (exp, actual) = matchType(exp, actual, DAE.T_METABOXED(DAE.T_UNKNOWN_DEFAULT), printFailtrace)
                if debug
                  print("matched type: " + ExpressionDump.printExpStr(exp) + " of " + unparseType(actual) + " with " + unparseType(expected) + " (boxed)\\n")
                end
                polymorphicBindings = subtypePolymorphic(getUniontypeIfMetarecordReplaceAllSubtypes(actual), getUniontypeIfMetarecordReplaceAllSubtypes(expected), envPath, polymorphicBindings)
                if debug
                  print("match type: " + ExpressionDump.printExpStr(exp) + " of " + unparseType(actual) + " with " + unparseType(expected) + " and bindings " + polymorphicBindingsStr(polymorphicBindings) + " (OK)\\n")
                end
              end
               #= /*(if not Config.acceptMetaModelicaGrammar() then true else*/ =#
          (exp, actual, polymorphicBindings)
        end

         #= Like matchType, except we also
        bind polymorphic variabled. Used when elaborating calls. =#
        function matchTypePolymorphicWithError(iexp::DAE.Exp, iactual::DAE.Type, iexpected::DAE.Type, envPath::Option{<:Absyn.Path} #= to detect which polymorphic types are recursive =#, ipolymorphicBindings::InstTypes.PolymorphicBindings, info::SourceInfo) ::Tuple{DAE.Exp, DAE.Type, InstTypes.PolymorphicBindings}
              local outBindings::InstTypes.PolymorphicBindings
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType, outBindings) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local exp::DAE.Exp
                  local e_type::Type
                  local expected_type::Type
                  local e_type_1::Type
                  local actual::Type
                  local expected::Type
                  local polymorphicBindings::InstTypes.PolymorphicBindings
                  local str1::String
                  local str2::String
                  local str3::String
                @matchcontinue (iexp, iactual, iexpected, envPath, ipolymorphicBindings, info) begin
                  (exp, actual, expected, _, polymorphicBindings, _)  => begin
                      (exp, actual, polymorphicBindings) = matchTypePolymorphic(exp, actual, expected, envPath, polymorphicBindings, false)
                    (exp, actual, polymorphicBindings)
                  end

                  _  => begin
                        str1 = ExpressionDump.printExpStr(iexp)
                        str2 = unparseType(iactual)
                        str3 = unparseType(iexpected)
                        Error.addSourceMessage(Error.EXP_TYPE_MISMATCH, list(str1, str3, str2), info)
                      fail()
                  end
                end
              end
          (outExp, outType, outBindings)
        end

         #= This function matches an expression with an expected type, and converts the
            expression to the expected type if necessary. =#
        function matchType(inExp::DAE.Exp, inActualType::DAE.Type, inExpectedType::DAE.Type, inPrintFailtrace::Bool = false) ::Tuple{DAE.Exp, DAE.Type}
              local outType::DAE.Type
              local outExp::DAE.Exp

              if subtype(inExpectedType, inActualType)
                outExp = inExp
                outType = inActualType
              else
                try
                  @match false = subtype(inActualType, inExpectedType)
                  (outExp, outType) = typeConvert(inExp, inActualType, inExpectedType, inPrintFailtrace)
                  outExp = ExpressionSimplify.simplify1(outExp)
                catch
                  printFailure(Flags.TYPES, "matchType", inExp, inActualType, inExpectedType)
                  fail()
                end
              end
               #= /* TODO: Don't return ANY as type here; use the most restrictive... Else we get issues... */ =#
          (outExp, outType)
        end

        function matchTypeNoFail(inExp::DAE.Exp, inActualType::DAE.Type, inExpectedType::DAE.Type) ::Tuple{DAE.Exp, DAE.Type, Bool}
              local outMatch::Bool
              local outType::DAE.Type
              local outExp::DAE.Exp

              if subtype(inExpectedType, inActualType)
                outExp = inExp
                outType = inActualType
                outMatch = true
              else
                try
                  (outExp, outType) = typeConvert(inExp, inActualType, inExpectedType, false)
                  outExp = ExpressionSimplify.simplify1(outExp)
                  outMatch = true
                catch
                  outExp = inExp
                  outType = inActualType
                  outMatch = true
                end
              end
          (outExp, outType, outMatch)
        end

         #= matchType, list of actual types, one expected type. =#
        function matchTypes(iexps::List{<:DAE.Exp}, itys::List{<:DAE.Type}, expected::DAE.Type, printFailtrace::Bool) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTys::List{DAE.Type}
              local outExps::List{DAE.Exp}

              (outExps, outTys) = matchTypes_tail(iexps, itys, expected, printFailtrace, nil, nil)
          (outExps, outTys)
        end

        function matchTypes_tail(iexps::List{<:DAE.Exp}, itys::List{<:DAE.Type}, expected::DAE.Type, printFailtrace::Bool, inAccumExps::List{<:DAE.Exp}, inAccumTypes::List{<:DAE.Type}) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTys::List{DAE.Type}
              local outExps::List{DAE.Exp}

              (outExps, outTys) = begin
                  local e::DAE.Exp
                  local exps::List{DAE.Exp}
                  local ty::DAE.Type
                  local tys::List{DAE.Type}
                @match (iexps, itys, expected, printFailtrace, inAccumExps, inAccumTypes) begin
                  (e <| exps, ty <| tys, _, _, _, _)  => begin
                      (e, ty) = matchTypes2(e, ty, expected, printFailtrace)
                      (exps, tys) = matchTypes_tail(exps, tys, expected, printFailtrace, _cons(e, inAccumExps), _cons(ty, inAccumTypes))
                    (exps, tys)
                  end

                  ( nil(),  nil(), _, _, _, _)  => begin
                    (listReverse(inAccumExps), listReverse(inAccumTypes))
                  end
                end
              end
          (outExps, outTys)
        end

        function matchTypes2(inExp::DAE.Exp, inType::DAE.Type, inExpected::DAE.Type, inPrintFailtrace::Bool) ::Tuple{DAE.Exp, DAE.Type}
              local outType::DAE.Type
              local outExp::DAE.Exp

              (outExp, outType) = begin
                  local e::DAE.Exp
                  local ty::DAE.Type
                  local expected_ty::DAE.Type
                  local str::String
                @matchcontinue (inExp, inType, inExpected, inPrintFailtrace) begin
                  (_, _, _, _)  => begin
                      ty = getUniontypeIfMetarecordReplaceAllSubtypes(inType)
                      expected_ty = getUniontypeIfMetarecordReplaceAllSubtypes(inExpected)
                      (e, ty) = matchType(inExp, ty, expected_ty, inPrintFailtrace)
                    (e, ty)
                  end

                  _  => begin
                        str = "- Types.matchTypes failed for " + ExpressionDump.printExpStr(inExp) + " from " + unparseType(inType) + " to " + unparseType(inExpected) + "\\n"
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
          (outExp, outType)
        end

         #= @author adrpo
         print the message only when flag is on.
         this is to speed up the flattening as we don't
         generate the strings at all. =#
        function printFailure(flag::Flags.DebugFlag, source::String, e::DAE.Exp, e_type::DAE.Type, expected_type::DAE.Type)
              if Flags.isSet(flag)
                Debug.traceln("- Types." + source + " failed on:" + ExpressionDump.printExpStr(e))
                Debug.traceln("  type:" + unparseType(e_type) + " differs from expected\\n  type:" + unparseType(expected_type))
              end
        end

        function polymorphicBindingStr(binding::Tuple{<:String, List{<:DAE.Type}}) ::String
              local str::String

              local tys::List{DAE.Type}

              (str, tys) = binding
               #=  Don't bother doing this fast; it's just for error messages
               =#
              str = "    " + str + ":\\n" + stringDelimitList(ListUtil.map1r(ListUtil.map(tys, unparseType), stringAppend, "      "), "\\n")
          str
        end

        function polymorphicBindingsStr(bindings::InstTypes.PolymorphicBindings) ::String
              local str::String

              str = stringDelimitList(ListUtil.map(bindings, polymorphicBindingStr), "\\n")
          str
        end

         #= Uses the polymorphic bindings to determine the result type of the function. =#
        function fixPolymorphicRestype(ty::DAE.Type, bindings::InstTypes.PolymorphicBindings, info::SourceInfo) ::DAE.Type
              local resType::DAE.Type

               #= print(\"Trying to fix restype: \" + unparseType(ty) + \"\\n\");
               =#
              resType = fixPolymorphicRestype2(ty, "", bindings, info)
               #= print(\"OK: \" + unparseType(resType) + \"\\n\");
               =#
          resType
        end

        function fixPolymorphicRestype2(ty::DAE.Type, prefix::String, bindings::InstTypes.PolymorphicBindings, info::SourceInfo) ::DAE.Type
              local resType::DAE.Type

              resType = begin
                  local id::String
                  local bstr::String
                  local tstr::String
                  local t1::Type
                  local t2::Type
                  local ty1::Type
                  local tys::List{DAE.Type}
                  local tys1::List{DAE.Type}
                  local names1::List{String}
                  local args1::List{DAE.FuncArg}
                  local functionAttributes::DAE.FunctionAttributes
                  local cs::List{DAE.Const}
                  local ps::List{DAE.VarParallelism}
                  local oe::List{Option{DAE.Exp}}
                  local paths::List{Absyn.Path}
                  local path::Absyn.Path
                  local knownSingleton::Bool
                  local singletonType::DAE.EvaluateSingletonType
                @matchcontinue (ty, prefix, bindings, info) begin
                  (DAE.T_METAPOLYMORPHIC(name = id), _, _, _)  => begin
                      @match list(t1) = polymorphicBindingsLookup(prefix + id, bindings)
                      t1 = fixPolymorphicRestype2(t1, "", bindings, info)
                    t1
                  end

                  (DAE.T_METALIST(ty = t1), _, _, _)  => begin
                      t2 = fixPolymorphicRestype2(t1, prefix, bindings, info)
                      t2 = boxIfUnboxedType(t2)
                    DAE.T_METALIST(t2)
                  end

                  (DAE.T_METAARRAY(ty = t1), _, _, _)  => begin
                      t2 = fixPolymorphicRestype2(t1, prefix, bindings, info)
                      t2 = boxIfUnboxedType(t2)
                    DAE.T_METAARRAY(t2)
                  end

                  (DAE.T_METAOPTION(ty = t1), _, _, _)  => begin
                      t2 = fixPolymorphicRestype2(t1, prefix, bindings, info)
                      t2 = boxIfUnboxedType(t2)
                    DAE.T_METAOPTION(t2)
                  end

                  (DAE.T_METAUNIONTYPE(typeVars =  nil()), _, _, _)  => begin
                    ty
                  end

                  (DAE.T_METAUNIONTYPE(typeVars = tys), _, _, _)  => begin
                      tys = ListUtil.map3(tys, fixPolymorphicRestype2, prefix, bindings, info)
                      tys = ListUtil.map(tys, boxIfUnboxedType)
                    DAE.T_METAUNIONTYPE(ty.paths, tys, ty.knownSingleton, ty.singletonType, ty.path)
                  end

                  (DAE.T_METATUPLE(types = tys), _, _, _)  => begin
                      tys = ListUtil.map3(tys, fixPolymorphicRestype2, prefix, bindings, info)
                      tys = ListUtil.map(tys, boxIfUnboxedType)
                    DAE.T_METATUPLE(tys)
                  end

                  (t1 && DAE.T_ARRAY(__), _, _, _)  => begin
                      t1.ty = fixPolymorphicRestype2(t1.ty, prefix, bindings, info)
                    t1
                  end

                  (t1 && DAE.T_TUPLE(__), _, _, _)  => begin
                      t1.types = ListUtil.map3(t1.types, fixPolymorphicRestype2, prefix, bindings, info)
                    t1
                  end

                  (DAE.T_FUNCTION(args1, ty1, functionAttributes, path), _, _, _)  => begin
                      tys1 = ListUtil.map(args1, funcArgType)
                      tys1 = ListUtil.map3(tys1, fixPolymorphicRestype2, prefix, bindings, info)
                      ty1 = fixPolymorphicRestype2(ty1, prefix, bindings, info)
                      args1 = ListUtil.threadMap(args1, tys1, setFuncArgType)
                      ty1 = DAE.T_FUNCTION(args1, ty1, functionAttributes, path)
                    ty1
                  end

                  (_, _, _, _)  => begin
                    ty
                  end

                  _  => begin
                        tstr = unparseType(ty)
                        bstr = polymorphicBindingsStr(bindings)
                        id = "Types.fixPolymorphicRestype failed for type: " + tstr + " using bindings: " + bstr
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list(id), info)
                      fail()
                  end
                end
              end
               #=  Add Uniontype, Function reference(?)
               =#
               #=  failure(isPolymorphic(ty)); Recursive functions like to return polymorphic crap we don't know of
               =#
          resType
        end

        function polymorphicBindingsLookup(id::String, bindings::InstTypes.PolymorphicBindings) ::List{DAE.Type}
              local resType::List{DAE.Type}

              resType = begin
                  local id2::String
                  local tys::List{DAE.Type}
                  local rest::InstTypes.PolymorphicBindings
                @matchcontinue (id, bindings) begin
                  (_, (id2, tys) <| _)  => begin
                      @match true = id == id2
                    ListUtil.map(tys, boxIfUnboxedType)
                  end

                  (_, _ <| rest)  => begin
                      tys = polymorphicBindingsLookup(id, rest)
                    tys
                  end
                end
              end
          resType
        end

         #= Traverses all the types the input DAE.Type contains, checks if
        they are of the type the given function specifies, then returns
        a list of all those types. =#
        function getAllInnerTypesOfType(inType::DAE.Type, inFn::TypeFn) ::List{DAE.Type}
              local outTypes::List{DAE.Type}

              outTypes = getAllInnerTypes(list(inType), nil, inFn)
          outTypes
        end

         #= Traverses all the types that the input DAE.Type contains, and returns all
           types for which the given function returns true. =#
        function getAllInnerTypes(inTypes::List{<:DAE.Type}, inAccum::List{<:DAE.Type} = nil, inFunc::MatchFunc = nothing)::List{DAE.Type}
              local outTypes::List{DAE.Type} = inAccum

              local ty::DAE.Type
              local tys::List{DAE.Type}

              for t in inTypes
                if inFunc(t)
                  outTypes = _cons(t, outTypes)
                end
                tys = begin
                     #=  Add the type to the result list if the match function return true.
                     =#
                     #=  Get the inner types of the type.
                     =#
                    local fields::List{DAE.Var}
                    local funcArgs::List{DAE.FuncArg}
                  @match t begin
                    DAE.T_ARRAY(ty = ty)  => begin
                      list(ty)
                    end

                    DAE.T_METALIST(ty = ty)  => begin
                      list(ty)
                    end

                    DAE.T_METAARRAY(ty = ty)  => begin
                      list(ty)
                    end

                    DAE.T_METABOXED(ty = ty)  => begin
                      list(ty)
                    end

                    DAE.T_METAOPTION(ty = ty)  => begin
                      list(ty)
                    end

                    DAE.T_TUPLE(types = tys)  => begin
                      tys
                    end

                    DAE.T_METATUPLE(types = tys)  => begin
                      tys
                    end

                    DAE.T_METAUNIONTYPE(typeVars = tys)  => begin
                      tys
                    end

                    DAE.T_METARECORD(typeVars = tys, fields = fields)  => begin
                      listAppend(tys, ListUtil.map(fields, getVarType))
                    end

                    DAE.T_COMPLEX(varLst = fields)  => begin
                      ListUtil.map(fields, getVarType)
                    end

                    DAE.T_SUBTYPE_BASIC(varLst = fields)  => begin
                      ListUtil.map(fields, getVarType)
                    end

                    DAE.T_FUNCTION(funcArg = funcArgs, funcResultType = ty)  => begin
                      _cons(ty, ListUtil.map(funcArgs, funcArgType))
                    end

                    _  => begin
                        nil
                    end
                  end
                end
                outTypes = getAllInnerTypes(tys, outTypes, inFunc)
              end
               #=  Call this function recursively to filter out the matching inner types and
               =#
               #=  add them to the result.
               =#
          outTypes
        end

        function uniontypeFilter(ty::DAE.Type) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match ty begin
                  DAE.T_METAUNIONTYPE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

        function metarecordFilter(ty::DAE.Type) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match ty begin
                  DAE.T_METARECORD(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

        function getUniontypePaths(ty::DAE.Type) ::List{Absyn.Path}
              local outPaths::List{Absyn.Path}

              outPaths = begin
                  local paths::List{Absyn.Path}
                @match ty begin
                  DAE.T_METAUNIONTYPE(paths = paths)  => begin
                    paths
                  end
                end
              end
          outPaths
        end

         #= Takes a function reference. If it contains any types that are not boxed, we
        return a reference to the function that does take boxed types. Else, we
        return a reference to the regular function. =#
        function makeFunctionPolymorphicReference(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local funcArgs1::List{DAE.FuncArg}
                  local funcArgs2::List{DAE.FuncArg}
                  local funcArgNames::List{String}
                  local funcArgTypes1::List{DAE.Type}
                  local funcArgTypes2::List{DAE.Type}
                  local dummyBoxedTypeList::List{DAE.Type}
                  local dummyExpList::List{DAE.Exp}
                  local cs::List{DAE.Const}
                  local ps::List{DAE.VarParallelism}
                  local oe::List{Option{DAE.Exp}}
                  local ty2::Type
                  local resType1::Type
                  local resType2::Type
                  local tty1::Type
                  local path::Absyn.Path
                  local functionAttributes::DAE.FunctionAttributes
                @match inType begin
                  DAE.T_FUNCTION(funcArgs1, resType1, functionAttributes, path)  => begin
                      funcArgTypes1 = ListUtil.map(funcArgs1, funcArgType)
                      (dummyExpList, dummyBoxedTypeList) = makeDummyExpAndTypeLists(funcArgTypes1)
                      (_, funcArgTypes2) = matchTypeTuple(dummyExpList, funcArgTypes1, dummyBoxedTypeList, false)
                      funcArgs2 = ListUtil.threadMap(funcArgs1, funcArgTypes2, setFuncArgType)
                      resType2 = makeFunctionPolymorphicReferenceResType(resType1)
                      ty2 = DAE.T_FUNCTION(funcArgs2, resType2, functionAttributes, path)
                    ty2
                  end

                  _  => begin
                    fail()
                  end
                end
              end
               #= /* Maybe add this case when standard Modelica gets function references?
                  case (ty1 as (tty1 as DAE.T_FUNCTION(funcArgs1,resType),SOME(path)))
                    local
                      list<Boolean> boolList;
                    equation
                      funcArgTypes1 = List.map(funcArgs1, Util.tuple22);
                      boolList = List.map(funcArgTypes1, isBoxedType);
                      true = List.reduce(boolList, boolAnd);
                    then ty1; */ =#
               #=  fprintln(Flags.FAILTRACE, \"- Types.makeFunctionPolymorphicReference failed\");
               =#
          outType
        end

        function makeFunctionPolymorphicReferenceResType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local e::DAE.Exp
                  local ty::Type
                  local ty1::Type
                  local ty2::Type
                  local tys::List{DAE.Type}
                  local dummyBoxedTypeList::List{DAE.Type}
                  local dummyExpList::List{DAE.Exp}
                @matchcontinue inType begin
                  ty && DAE.T_TUPLE(tys)  => begin
                      (dummyExpList, dummyBoxedTypeList) = makeDummyExpAndTypeLists(tys)
                      (_, tys) = matchTypeTuple(dummyExpList, tys, dummyBoxedTypeList, false)
                      ty.types = tys
                    ty
                  end

                  ty && DAE.T_NORETCALL(__)  => begin
                    ty
                  end

                  ty1  => begin
                      @match (list(e), list(ty2)) = makeDummyExpAndTypeLists(list(ty1))
                      (_, ty) = matchType(e, ty1, ty2, false)
                    ty
                  end
                end
              end
          outType
        end

        function makeDummyExpAndTypeLists(lst::List{<:DAE.Type}) ::Tuple{List{DAE.Exp}, List{DAE.Type}}
              local outTypes::List{DAE.Type}
              local outExps::List{DAE.Exp}

              (outExps, outTypes) = begin
                  local restExp::List{DAE.Exp}
                  local restType::List{DAE.Type}
                  local rest::List{DAE.Type}
                  local cref_::DAE.ComponentRef
                  local crefExp::DAE.Exp
                @match lst begin
                   nil()  => begin
                    (nil, nil)
                  end

                  _ <| rest  => begin
                      (restExp, restType) = makeDummyExpAndTypeLists(rest)
                      cref_ = ComponentReference.makeCrefIdent("#DummyExp#", DAE.T_UNKNOWN_DEFAULT, nil)
                      crefExp = Expression.crefExp(cref_)
                    (_cons(crefExp, restExp), _cons(DAE.T_METABOXED(DAE.T_UNKNOWN_DEFAULT), restType))
                  end
                end
              end
          (outExps, outTypes)
        end

         #= Transforms a DAE.T_TUPLE to a list of types. Other types return the same type (as a list) =#
        function resTypeToListTypes(inType::DAE.Type) ::List{DAE.Type}
              local outType::List{DAE.Type}

              outType = begin
                  local tys::List{DAE.Type}
                  local ty::Type
                @match inType begin
                  DAE.T_TUPLE(types = tys)  => begin
                    tys
                  end

                  DAE.T_NORETCALL(__)  => begin
                    nil
                  end

                  ty  => begin
                    list(ty)
                  end
                end
              end
          outType
        end

         #= If the type is a Real, Integer or an array of Real or Integer, the function returns
        list of dimensions; otherwise, it fails. =#
        function getRealOrIntegerDimensions(inType::DAE.Type) ::DAE.Dimensions
              local outDims::DAE.Dimensions

              outDims = begin
                  local ty::Type
                  local d::DAE.Dimension
                  local dims::DAE.Dimensions
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    nil
                  end

                  DAE.T_INTEGER(__)  => begin
                    nil
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    getRealOrIntegerDimensions(ty)
                  end

                  DAE.T_ARRAY(dims = d && DAE.DIM_INTEGER(_) <|  nil(), ty = ty)  => begin
                      dims = getRealOrIntegerDimensions(ty)
                    _cons(d, dims)
                  end
                end
              end
          outDims
        end

        function isPolymorphic(ty::DAE.Type) ::Bool
              local outMatch::Bool

              outMatch = begin
                @match ty begin
                  DAE.T_METAPOLYMORPHIC(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMatch
        end

        function polymorphicTypeName(ty::DAE.Type) ::String
              local name::String

              @match DAE.T_METAPOLYMORPHIC(name = name) = ty
          name
        end

        function addPolymorphicBinding(id::String, ity::DAE.Type, bindings::InstTypes.PolymorphicBindings) ::InstTypes.PolymorphicBindings
              local outBindings::InstTypes.PolymorphicBindings

              outBindings = begin
                  local id1::String
                  local id2::String
                  local tys::List{DAE.Type}
                  local rest::InstTypes.PolymorphicBindings
                  local first::Tuple{String, List{DAE.Type}}
                  local ty::Type
                @matchcontinue (id, ity, bindings) begin
                  (_, ty,  nil())  => begin
                      ty = unboxedType(ty)
                      ty = boxIfUnboxedType(ty)
                    list((id, list(ty)))
                  end

                  (id1, ty, (id2, tys) <| rest)  => begin
                      @match true = id1 == id2
                      ty = unboxedType(ty)
                      ty = boxIfUnboxedType(ty)
                    _cons((id2, _cons(ty, tys)), rest)
                  end

                  (_, ty, first <| rest)  => begin
                      rest = addPolymorphicBinding(id, ty, rest)
                    _cons(first, rest)
                  end
                end
              end
          outBindings
        end

         #= Takes a set of polymorphic bindings and tries to solve the constraints
        such that each name is bound to a non-polymorphic type.
        Solves by doing iterations until a valid state is found (or no change is
        possible). =#
        function solvePolymorphicBindings(bindings::InstTypes.PolymorphicBindings, info::SourceInfo, path::Absyn.Path) ::InstTypes.PolymorphicBindings
              local solvedBindings::InstTypes.PolymorphicBindings

              local unsolvedBindings::InstTypes.PolymorphicBindings

               #=  print(\"solvePoly \" + polymorphicBindingsStr(bindings) + \"\\n\");
               =#
              (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(bindings, nil, nil)
              checkValidBindings(bindings, solvedBindings, unsolvedBindings, info, path)
               #=  print(\"solved poly \" + polymorphicBindingsStr(solvedBindings) + \"\\n\");
               =#
          solvedBindings
        end

         #= Emits an error message if we could not solve the polymorphic types to actual types. =#
        function checkValidBindings(bindings::InstTypes.PolymorphicBindings, solvedBindings::InstTypes.PolymorphicBindings, unsolvedBindings::InstTypes.PolymorphicBindings, info::SourceInfo, path::Absyn.Path)
              local bindingsStr::String
              local solvedBindingsStr::String
              local unsolvedBindingsStr::String
              local pathStr::String
              local tys::List{DAE.Type}

              if ! listEmpty(unsolvedBindings)
                pathStr = AbsynUtil.pathString(path)
                bindingsStr = polymorphicBindingsStr(bindings)
                solvedBindingsStr = polymorphicBindingsStr(solvedBindings)
                unsolvedBindingsStr = polymorphicBindingsStr(unsolvedBindings)
                Error.addSourceMessage(Error.META_UNSOLVED_POLYMORPHIC_BINDINGS, list(pathStr, bindingsStr, solvedBindingsStr, unsolvedBindingsStr), info)
                fail()
              end
        end

        function solvePolymorphicBindingsLoop(ibindings::InstTypes.PolymorphicBindings, isolvedBindings::InstTypes.PolymorphicBindings, iunsolvedBindings::InstTypes.PolymorphicBindings) ::Tuple{InstTypes.PolymorphicBindings, InstTypes.PolymorphicBindings}
              local outUnsolvedBindings::InstTypes.PolymorphicBindings
              local outSolvedBindings::InstTypes.PolymorphicBindings

              (outSolvedBindings, outUnsolvedBindings) = begin
                   #= /* Fail by returning crap :) */ =#
                  local first::Tuple{String, List{DAE.Type}}
                  local ty::Type
                  local tys::List{DAE.Type}
                  local id::String
                  local len1::ModelicaInteger
                  local len2::ModelicaInteger
                  local rest::InstTypes.PolymorphicBindings
                  local solvedBindings::InstTypes.PolymorphicBindings
                  local unsolvedBindings::InstTypes.PolymorphicBindings
                @matchcontinue (ibindings, isolvedBindings, iunsolvedBindings) begin
                  ( nil(), solvedBindings, unsolvedBindings)  => begin
                    (solvedBindings, unsolvedBindings)
                  end

                  ((id, ty <|  nil()) <| rest, solvedBindings, unsolvedBindings)  => begin
                      ty = Types.boxIfUnboxedType(ty)
                      (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(listAppend(unsolvedBindings, rest), _cons((id, list(ty)), solvedBindings), nil)
                    (solvedBindings, unsolvedBindings)
                  end

                  ((id, tys) <| rest, solvedBindings, unsolvedBindings)  => begin
                       #=  Replace solved bindings
                       =#
                      tys = replaceSolvedBindings(tys, solvedBindings, false)
                      tys = ListUtil.unionOnTrue(tys, nil, equivtypes)
                      (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(listAppend(_cons((id, tys), unsolvedBindings), rest), solvedBindings, nil)
                    (solvedBindings, unsolvedBindings)
                  end

                  ((id, tys) <| rest, solvedBindings, unsolvedBindings)  => begin
                      (tys, solvedBindings) = solveBindings(tys, tys, solvedBindings)
                      tys = ListUtil.unionOnTrue(tys, nil, equivtypes)
                      (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(listAppend(_cons((id, tys), unsolvedBindings), rest), solvedBindings, nil)
                    (solvedBindings, unsolvedBindings)
                  end

                  ((id, tys) <| rest, solvedBindings, unsolvedBindings)  => begin
                       #=  Duplicate types need to be removed
                       =#
                      len1 = listLength(tys)
                      @match true = len1 > 1
                      tys = ListUtil.unionOnTrue(tys, nil, equivtypes)
                       #=  Remove duplicates
                       =#
                      len2 = listLength(tys)
                      @match false = len1 == len2
                      (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(listAppend(_cons((id, tys), unsolvedBindings), rest), solvedBindings, nil)
                    (solvedBindings, unsolvedBindings)
                  end

                  (first <| rest, solvedBindings, unsolvedBindings)  => begin
                      (solvedBindings, unsolvedBindings) = solvePolymorphicBindingsLoop(rest, solvedBindings, _cons(first, unsolvedBindings))
                    (solvedBindings, unsolvedBindings)
                  end
                end
              end
          (outSolvedBindings, outUnsolvedBindings)
        end

         #= Checks all types against each other to find an unbound polymorphic variable, which will then become bound.
        Uses unification to solve the system, but the algorithm is slow (possibly quadratic).
        The good news is we don't have functions with many unknown types in the compiler.
        Horribly complicated function to keep track of what happens... =#
        function solveBindings(itys1::List{<:DAE.Type}, itys2::List{<:DAE.Type}, isolvedBindings::InstTypes.PolymorphicBindings) ::Tuple{List{DAE.Type}, InstTypes.PolymorphicBindings}
              local outSolvedBindings::InstTypes.PolymorphicBindings
              local outTys::List{DAE.Type}

              (outTys, outSolvedBindings) = begin
                  local ty::Type
                  local ty1::Type
                  local ty2::Type
                  local tys::List{DAE.Type}
                  local rest::List{DAE.Type}
                  local tys1::List{DAE.Type}
                  local tys2::List{DAE.Type}
                  local id::String
                  local id1::String
                  local id2::String
                  local names1::List{String}
                  local args1::List{DAE.FuncArg}
                  local args2::List{DAE.FuncArg}
                  local functionAttributes1::DAE.FunctionAttributes
                  local functionAttributes2::DAE.FunctionAttributes
                  local path::Absyn.Path
                  local fromOtherFunction::Bool
                  local cs1::List{DAE.Const}
                  local ps1::List{DAE.VarParallelism}
                  local solvedBindings::InstTypes.PolymorphicBindings
                @matchcontinue (itys1, itys2, isolvedBindings) begin
                  (ty1 && DAE.T_METAPOLYMORPHIC(name = id1) <| _, ty2 && DAE.T_METAPOLYMORPHIC(name = id2) <| tys2, solvedBindings)  => begin
                      @match false = id1 == id2
                      fromOtherFunction = System.stringFind(id1, "") != (-1)
                      id = if fromOtherFunction
                            id1
                          else
                            id2
                          end
                      ty = if fromOtherFunction
                            ty2
                          else
                            ty1
                          end
                      @shouldFail _ = polymorphicBindingsLookup(id, solvedBindings)
                      solvedBindings = addPolymorphicBinding(id, ty, solvedBindings)
                    (_cons(ty, tys2), solvedBindings)
                  end

                  (DAE.T_METAPOLYMORPHIC(name = id) <| _, ty2 <| tys2, solvedBindings)  => begin
                      @match false = isPolymorphic(ty2)
                      @shouldFail _ = polymorphicBindingsLookup(id, solvedBindings)
                      solvedBindings = addPolymorphicBinding(id, ty2, solvedBindings)
                    (_cons(ty2, tys2), solvedBindings)
                  end

                  (ty1 <| _, DAE.T_METAPOLYMORPHIC(name = id) <| tys2, solvedBindings)  => begin
                      @match false = isPolymorphic(ty1)
                      @shouldFail _ = polymorphicBindingsLookup(id, solvedBindings)
                      solvedBindings = addPolymorphicBinding(id, ty1, solvedBindings)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  (DAE.T_METAOPTION(ty = ty1) <| _, DAE.T_METAOPTION(ty = ty2) <| tys2, solvedBindings)  => begin
                      @match (list(ty1), solvedBindings) = solveBindings(list(ty1), list(ty2), solvedBindings)
                      ty1 = DAE.T_METAOPTION(ty1)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  (DAE.T_METALIST(ty = ty1) <| _, DAE.T_METALIST(ty = ty2) <| tys2, solvedBindings)  => begin
                      @match (list(ty1), solvedBindings) = solveBindings(list(ty1), list(ty2), solvedBindings)
                      ty1 = DAE.T_METALIST(ty1)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  (DAE.T_METAARRAY(ty = ty1) <| _, DAE.T_METAARRAY(ty = ty2) <| tys2, solvedBindings)  => begin
                      @match (list(ty1), solvedBindings) = solveBindings(list(ty1), list(ty2), solvedBindings)
                      ty1 = DAE.T_METAARRAY(ty1)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  (DAE.T_METATUPLE(types = tys1) <| _, DAE.T_METATUPLE(types = tys2) <| rest, solvedBindings)  => begin
                      (tys1, solvedBindings) = solveBindingsThread(tys1, tys2, false, solvedBindings)
                      ty1 = DAE.T_METATUPLE(tys1)
                    (_cons(ty1, rest), solvedBindings)
                  end

                  (DAE.T_FUNCTION(args1, ty1, functionAttributes1, path) <| _, DAE.T_FUNCTION(args2, ty2, _, _) <| rest, solvedBindings)  => begin
                      tys1 = ListUtil.map(args1, funcArgType)
                      tys2 = ListUtil.map(args2, funcArgType)
                      (_cons(ty1, tys1), solvedBindings) = solveBindingsThread(_cons(ty1, tys1), _cons(ty2, tys2), false, solvedBindings)
                      tys1 = ListUtil.map(tys1, boxIfUnboxedType)
                      args1 = ListUtil.threadMap(args1, tys1, setFuncArgType)
                      args1 = ListUtil.map(args1, clearDefaultBinding)
                      ty1 = DAE.T_FUNCTION(args1, ty1, functionAttributes1, path)
                    (_cons(ty1, rest), solvedBindings)
                  end

                  (tys1, ty <| tys2, solvedBindings)  => begin
                      (tys, solvedBindings) = solveBindings(tys1, tys2, solvedBindings)
                    (_cons(ty, tys), solvedBindings)
                  end
                end
              end
               #=  If we have $X,Y,..., bind $X = Y instead of Y = $X
               =#
               #=  Lookup from one id to the other type
               =#
          (outTys, outSolvedBindings)
        end

         #= Checks all types against each other to find an unbound polymorphic variable, which will then become bound.
        Uses unification to solve the system, but the algorithm is slow (possibly quadratic).
        The good news is we don't have functions with many unknown types in the compiler.

        Horribly complicated function to keep track of what happens... =#
        function solveBindingsThread(itys1::List{<:DAE.Type}, itys2::List{<:DAE.Type}, changed::Bool #= if true, something changed and the function will succeed =#, isolvedBindings::InstTypes.PolymorphicBindings) ::Tuple{List{DAE.Type}, InstTypes.PolymorphicBindings}
              local outSolvedBindings::InstTypes.PolymorphicBindings
              local outTys::List{DAE.Type}

              (outTys, outSolvedBindings) = begin
                  local ty1::Type
                  local ty2::Type
                  local solvedBindings::InstTypes.PolymorphicBindings
                  local tys1::List{DAE.Type}
                  local tys2::List{DAE.Type}
                @matchcontinue (itys1, itys2, changed, isolvedBindings) begin
                  (ty1 <| tys1, ty2 <| tys2, _, solvedBindings)  => begin
                      @match (list(ty1), solvedBindings) = solveBindings(list(ty1), list(ty2), solvedBindings)
                      (tys2, solvedBindings) = solveBindingsThread(tys1, tys2, true, solvedBindings)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  (ty1 <| tys1, _ <| tys2, _, solvedBindings)  => begin
                      (tys2, solvedBindings) = solveBindingsThread(tys1, tys2, changed, solvedBindings)
                    (_cons(ty1, tys2), solvedBindings)
                  end

                  ( nil(),  nil(), true, solvedBindings)  => begin
                    (nil, solvedBindings)
                  end
                end
              end
          (outTys, outSolvedBindings)
        end

        function replaceSolvedBindings(itys::List{<:DAE.Type}, isolvedBindings::InstTypes.PolymorphicBindings, changed::Bool #= if true, something changed and the function will succeed =#) ::List{DAE.Type}
              local outTys::List{DAE.Type}

              outTys = begin
                  local ty::Type
                  local tys::List{DAE.Type}
                  local solvedBindings::InstTypes.PolymorphicBindings
                @matchcontinue (itys, isolvedBindings, changed) begin
                  ( nil(), _, true)  => begin
                    nil
                  end

                  (ty <| tys, solvedBindings, _)  => begin
                      ty = replaceSolvedBinding(ty, solvedBindings)
                      tys = replaceSolvedBindings(tys, solvedBindings, true)
                    _cons(ty, tys)
                  end

                  (ty <| tys, solvedBindings, _)  => begin
                      tys = replaceSolvedBindings(tys, solvedBindings, changed)
                    _cons(ty, tys)
                  end
                end
              end
          outTys
        end

        function replaceSolvedBinding(ity::DAE.Type, isolvedBindings::InstTypes.PolymorphicBindings) ::DAE.Type
              local outTy::DAE.Type

              outTy = begin
                  local args::List{DAE.FuncArg}
                  local tys::List{DAE.Type}
                  local id::String
                  local names::List{String}
                  local cs::List{DAE.Const}
                  local ps::List{DAE.VarParallelism}
                  local path::Absyn.Path
                  local oe::List{Option{DAE.Exp}}
                  local functionAttributes::DAE.FunctionAttributes
                  local ty::DAE.Type
                  local resType::DAE.Type
                  local solvedBindings::InstTypes.PolymorphicBindings
                @match (ity, isolvedBindings) begin
                  (DAE.T_METALIST(ty = ty), solvedBindings)  => begin
                      ty = replaceSolvedBinding(ty, solvedBindings)
                      ty = DAE.T_METALIST(ty)
                    ty
                  end

                  (DAE.T_METAARRAY(ty = ty), solvedBindings)  => begin
                      ty = replaceSolvedBinding(ty, solvedBindings)
                      ty = DAE.T_METAARRAY(ty)
                    ty
                  end

                  (DAE.T_METAOPTION(ty = ty), solvedBindings)  => begin
                      ty = replaceSolvedBinding(ty, solvedBindings)
                      ty = DAE.T_METAOPTION(ty)
                    ty
                  end

                  (DAE.T_METATUPLE(types = tys), solvedBindings)  => begin
                      tys = replaceSolvedBindings(tys, solvedBindings, false)
                      ty = DAE.T_METATUPLE(tys)
                    ty
                  end

                  (DAE.T_TUPLE(types = tys), solvedBindings)  => begin
                      tys = replaceSolvedBindings(tys, solvedBindings, false)
                      ty = DAE.T_TUPLE(tys, ity.names)
                    ty
                  end

                  (DAE.T_FUNCTION(args, resType, functionAttributes, path), solvedBindings)  => begin
                      tys = ListUtil.map(args, funcArgType)
                      tys = replaceSolvedBindings(_cons(resType, tys), solvedBindings, false)
                      tys = ListUtil.map(tys, unboxedType)
                      @match _cons(ty, tys) = ListUtil.map(tys, boxIfUnboxedType)
                      args = ListUtil.threadMap(args, tys, setFuncArgType)
                      ty = makeRegularTupleFromMetaTupleOnTrue(isTuple(resType), ty)
                      ty = DAE.T_FUNCTION(args, ty, functionAttributes, path)
                    ty
                  end

                  (DAE.T_METAPOLYMORPHIC(name = id), solvedBindings)  => begin
                      @match list(ty) = polymorphicBindingsLookup(id, solvedBindings)
                    ty
                  end
                end
              end
          outTy
        end

         #= A simple subtype() that also binds polymorphic variables.
        Only works on the MetaModelica datatypes; the input is assumed to be boxed.
         =#
        function subtypePolymorphic(actual::DAE.Type, expected::DAE.Type, envPath::Option{<:Absyn.Path}, inBindings::InstTypes.PolymorphicBindings) ::InstTypes.PolymorphicBindings
              local bindings::InstTypes.PolymorphicBindings

              bindings = begin
                  local id::String
                  local prefix::String
                  local ty::Type
                  local ty1::Type
                  local ty2::Type
                  local farg1::List{DAE.FuncArg}
                  local farg2::List{DAE.FuncArg}
                  local tList1::List{DAE.Type}
                  local tList2::List{DAE.Type}
                  local tys::List{DAE.Type}
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local ids::List{String}
                  local names1::List{String}
                  local names2::List{String}
                @matchcontinue (actual, expected) begin
                  (_, DAE.T_METAPOLYMORPHIC(name = id))  => begin
                    addPolymorphicBinding("" + id, actual, inBindings)
                  end

                  (DAE.T_METAPOLYMORPHIC(name = id), _)  => begin
                      if stringGet(id, 1) != stringCharInt("")
                        fail()
                      end
                       #=  We allow things like inner type variables of function pointers,
                       =#
                       #=  but not things like accepting T1 can be tuple<T2,T3>.
                       =#
                       #=  print(\"Not adding METAPOLYMORPHIC $$\"+id+\"=\"+unparseType(expected)+\"\\n\");
                       =#
                    addPolymorphicBinding("" + id, expected, inBindings)
                  end

                  (DAE.T_METABOXED(ty = ty1), ty2)  => begin
                      ty1 = unboxedType(ty1)
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (ty1, DAE.T_METABOXED(ty = ty2))  => begin
                      ty2 = unboxedType(ty2)
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (DAE.T_NORETCALL(__), DAE.T_NORETCALL(__))  => begin
                    inBindings
                  end

                  (DAE.T_INTEGER(__), DAE.T_INTEGER(__))  => begin
                    inBindings
                  end

                  (DAE.T_REAL(__), DAE.T_INTEGER(__))  => begin
                    inBindings
                  end

                  (DAE.T_STRING(__), DAE.T_STRING(__))  => begin
                    inBindings
                  end

                  (DAE.T_BOOL(__), DAE.T_BOOL(__))  => begin
                    inBindings
                  end

                  (DAE.T_ENUMERATION(names = names1), DAE.T_ENUMERATION(names = names2))  => begin
                      @match true = ListUtil.isEqualOnTrue(names1, names2, stringEq)
                    inBindings
                  end

                  (DAE.T_ARRAY(ty = ty1), DAE.T_ARRAY(ty = ty2))  => begin
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (DAE.T_METAARRAY(ty = ty1), DAE.T_METAARRAY(ty = ty2))  => begin
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (DAE.T_METALIST(ty = ty1), DAE.T_METALIST(ty = ty2))  => begin
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (DAE.T_METAOPTION(ty = ty1), DAE.T_METAOPTION(ty = ty2))  => begin
                    subtypePolymorphic(ty1, ty2, envPath, inBindings)
                  end

                  (DAE.T_METATUPLE(types = tList1), DAE.T_METATUPLE(types = tList2))  => begin
                    subtypePolymorphicList(tList1, tList2, envPath, inBindings)
                  end

                  (DAE.T_TUPLE(types = tList1), DAE.T_TUPLE(types = tList2))  => begin
                    subtypePolymorphicList(tList1, tList2, envPath, inBindings)
                  end

                  (DAE.T_METAUNIONTYPE(__), DAE.T_METAUNIONTYPE(__))  => begin
                      @match true = AbsynUtil.pathEqual(actual.path, expected.path)
                    subtypePolymorphicList(actual.typeVars, expected.typeVars, envPath, inBindings)
                  end

                  (DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(path1)), DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(path2)))  => begin
                      @match true = AbsynUtil.pathEqual(path1, path2)
                    inBindings
                  end

                  (DAE.T_FUNCTION(farg1, ty1, _, path1), DAE.T_FUNCTION(farg2, ty2, _, _))  => begin
                       #=  MM Function Reference. sjoelund
                       =#
                      if AbsynUtil.pathPrefixOf(Util.getOptionOrDefault(envPath, Absyn.IDENT("TOP")), path1)
                        tList1 = ListUtil.map(farg1, funcArgType)
                        tList2 = ListUtil.map(farg2, funcArgType)
                        bindings = subtypePolymorphicList(tList1, tList2, envPath, inBindings)
                        bindings = subtypePolymorphic(ty1, ty2, envPath, bindings)
                      else
                        prefix = "" + AbsynUtil.pathString(path1) + "."
                        @match (DAE.T_FUNCTION(farg1, ty1, _, _), _) = traverseType(actual, prefix, prefixTraversedPolymorphicType)
                        tList1 = ListUtil.map(farg1, funcArgType)
                        tList2 = ListUtil.map(farg2, funcArgType)
                        bindings = subtypePolymorphicList(tList1, tList2, envPath, inBindings)
                        bindings = subtypePolymorphic(ty1, ty2, envPath, bindings)
                      end
                       #=  Don't rename the result type for recursive calls...
                       =#
                    bindings
                  end

                  (DAE.T_UNKNOWN(__), ty2)  => begin
                      tys = getAllInnerTypesOfType(ty2, isPolymorphic)
                      ids = ListUtil.map(tys, polymorphicTypeName)
                      bindings = ListUtil.fold1(ids, addPolymorphicBinding, actual, inBindings)
                    bindings
                  end

                  (DAE.T_ANYTYPE(__), ty2)  => begin
                      tys = getAllInnerTypesOfType(ty2, isPolymorphic)
                      ids = ListUtil.map(tys, polymorphicTypeName)
                      bindings = ListUtil.fold1(ids, addPolymorphicBinding, actual, inBindings)
                    bindings
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  print(\"subtypePolymorphic failed: \" + unparseType(actual) + \" and \" + unparseType(expected) + \"\\n\");
               =#
          bindings
        end

         #= A simple subtype() that also binds polymorphic variables.
         Only works on the MetaModelica datatypes; the input is assumed to be boxed. =#
        function subtypePolymorphicList(actual::List{<:DAE.Type}, expected::List{<:DAE.Type}, envPath::Option{<:Absyn.Path}, ibindings::InstTypes.PolymorphicBindings) ::InstTypes.PolymorphicBindings
              local outBindings::InstTypes.PolymorphicBindings

              outBindings = begin
                  local ty1::Type
                  local ty2::Type
                  local tList1::List{DAE.Type}
                  local tList2::List{DAE.Type}
                  local bindings::InstTypes.PolymorphicBindings
                @match (actual, expected, envPath, ibindings) begin
                  ( nil(),  nil(), _, bindings)  => begin
                    bindings
                  end

                  (ty1 <| tList1, ty2 <| tList2, _, bindings)  => begin
                      bindings = subtypePolymorphic(ty1, ty2, envPath, bindings)
                      bindings = subtypePolymorphicList(tList1, tList2, envPath, bindings)
                    bindings
                  end
                end
              end
          outBindings
        end

        function boxVarLst(vars::List{<:DAE.Var}) ::List{DAE.Var}
              local ovars::List{DAE.Var}

              ovars = begin
                  local name::String
                  local attributes::DAE.Attributes
                  local type_::DAE.Type
                  local binding::DAE.Binding
                  local constOfForIteratorRange::Option{DAE.Const}
                  local rest::List{DAE.Var}
                @match vars begin
                   nil()  => begin
                    nil
                  end

                  DAE.TYPES_VAR(name, attributes, type_, binding, constOfForIteratorRange) <| rest  => begin
                      type_ = boxIfUnboxedType(type_)
                      rest = boxVarLst(rest)
                    _cons(DAE.TYPES_VAR(name, attributes, type_, binding, constOfForIteratorRange), rest)
                  end
                end
              end
          ovars
        end

         #= Lifts a type to an array using DAE.Subscript for dimension in the case of non-expanded arrays =#
        function liftArraySubscript(inType::DAE.Type, inSubscript::DAE.Subscript) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local i::ModelicaInteger
                  local e::DAE.Exp
                   #=  An array with an explicit dimension
                   =#
                @match (inType, inSubscript) begin
                  (ty, DAE.WHOLE_NONEXP(exp = DAE.ICONST(i)))  => begin
                    DAE.T_ARRAY(ty, list(DAE.DIM_INTEGER(i)))
                  end

                  (ty, DAE.WHOLE_NONEXP(exp = e))  => begin
                    DAE.T_ARRAY(ty, list(DAE.DIM_EXP(e)))
                  end

                  (ty, _)  => begin
                    ty
                  end
                end
              end
               #=  An array with parametric dimension
               =#
               #=  All other kinds of subscripts denote an index, so the type stays the same
               =#
          outType
        end

         #=
          Lifts a type using list<DAE.Subscript> to determine dimensions in the case of non-expanded arrays =#
        function liftArraySubscriptList(inType::DAE.Type, inSubscriptLst::List{<:DAE.Subscript}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::Type
                  local sub::DAE.Subscript
                  local rest::List{DAE.Subscript}
                @match (inType, inSubscriptLst) begin
                  (ty,  nil())  => begin
                    ty
                  end

                  (ty, sub <| rest)  => begin
                    liftArraySubscript(liftArraySubscriptList(ty, rest), sub)
                  end
                end
              end
          outType
        end

         #= Needed when pattern-matching =#
        function convertTupleToMetaTuple(exp::DAE.Exp, ty::DAE.Type) ::Tuple{DAE.Exp, DAE.Type}
              local oty::DAE.Type
              local oexp::DAE.Exp

              (oexp, oty) = begin
                @match (exp, ty) begin
                  (DAE.TUPLE(_), _)  => begin
                      (oexp, oty) = matchType(exp, ty, DAE.T_METABOXED_DEFAULT, false)
                    (oexp, oty)
                  end

                  _  => begin
                      (exp, ty)
                  end
                end
              end
               #= /* So we can verify that the contents of the tuple is boxed */ =#
          (oexp, oty)
        end

        function isFunctionType(ty::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_FUNCTION(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function prefixTraversedPolymorphicType(ty::Type, prefix::String) ::Tuple{Type, String}
              local str::String
              local oty::Type = ty

              (oty, str) = begin
                @match oty begin
                  DAE.T_METAPOLYMORPHIC(__)  => begin
                      oty.name = prefix + oty.name
                    (oty, prefix)
                  end

                  _  => begin
                      (ty, prefix)
                  end
                end
              end
          (oty, str)
        end

        function makeExpDimensionsUnknown(ty::DAE.Type, dummy::ModelicaInteger) ::Tuple{DAE.Type, ModelicaInteger}
              local odummy::ModelicaInteger = dummy
              local oty::DAE.Type = ty

              oty = begin
                @match oty begin
                  DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil())  => begin
                      oty.dims = list(DAE.DIM_UNKNOWN())
                    oty
                  end

                  _  => begin
                      oty
                  end
                end
              end
          (oty, odummy)
        end

         #= In binding equations, [Boolean] and [2] match, so we need to convert them =#
        function makeKnownDimensionsInteger(ty::DAE.Type, dummy::ModelicaInteger) ::Tuple{DAE.Type, ModelicaInteger}
              local odummy::ModelicaInteger = dummy
              local oty::DAE.Type = ty

              oty = begin
                  local size::ModelicaInteger
                @match oty begin
                  DAE.T_ARRAY(dims = DAE.DIM_BOOLEAN(__) <|  nil())  => begin
                      oty.dims = list(DAE.DIM_INTEGER(2))
                    oty
                  end

                  DAE.T_ARRAY(dims = DAE.DIM_ENUM(size = size) <|  nil())  => begin
                      oty.dims = list(DAE.DIM_INTEGER(size))
                    oty
                  end

                  DAE.T_ARRAY(dims = DAE.DIM_EXP(exp = DAE.ICONST(size)) <|  nil())  => begin
                      oty.dims = list(DAE.DIM_INTEGER(size))
                    oty
                  end

                  _  => begin
                      oty
                  end
                end
              end
          (oty, odummy)
        end
        A = Any
        function traverseType(ty::DAE.Type, arg::A, fn::Func) ::Tuple{DAE.Type, A}
              local a::A = arg
              local oty::DAE.Type

              (oty, a) = begin
                  local tys::List{DAE.Type}
                  local tyInner::Type
                  local ad::DAE.Dimensions
                  local str::String
                  local index::ModelicaInteger
                  local vars::List{DAE.Var}
                  local path::Absyn.Path
                  local eq::EqualityConstraint
                  local state::ClassInf.SMNode
                  local farg::List{DAE.FuncArg}
                  local functionAttributes::DAE.FunctionAttributes
                  local singleton::Bool
                  local b::Bool
                @match ty begin
                  DAE.T_INTEGER(__)  => begin
                    (ty, a)
                  end

                  DAE.T_REAL(__)  => begin
                    (ty, a)
                  end

                  DAE.T_STRING(__)  => begin
                    (ty, a)
                  end

                  DAE.T_BOOL(__)  => begin
                    (ty, a)
                  end

                  DAE.T_CLOCK(__)  => begin
                    (ty, a)
                  end

                  DAE.T_ENUMERATION(__)  => begin
                    (ty, a)
                  end

                  DAE.T_NORETCALL(__)  => begin
                    (ty, a)
                  end

                  DAE.T_UNKNOWN(__)  => begin
                    (ty, a)
                  end

                  DAE.T_METAUNIONTYPE(__)  => begin
                    (ty, a)
                  end

                  DAE.T_METAPOLYMORPHIC(__)  => begin
                    (ty, a)
                  end

                  DAE.T_CODE(__)  => begin
                    (ty, a)
                  end

                  oty && DAE.T_METABOXED(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_ARRAY(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_METATYPE(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_METALIST(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_METAOPTION(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_METAARRAY(__)  => begin
                      (tyInner, a) = traverseType(oty.ty, a, fn)
                      oty.ty = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_FUNCTION_REFERENCE_VAR(__)  => begin
                      (tyInner, a) = traverseType(oty.functionType, a, fn)
                      oty.functionType = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_FUNCTION_REFERENCE_FUNC(__)  => begin
                      (tyInner, a) = traverseType(oty.functionType, a, fn)
                      oty.functionType = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_METATUPLE(__)  => begin
                      (tys, a) = traverseTupleType(oty.types, a, fn)
                      oty.types = tys
                    (oty, a)
                  end

                  oty && DAE.T_TUPLE(__)  => begin
                      (tys, a) = traverseTupleType(oty.types, a, fn)
                      oty.types = tys
                    (oty, a)
                  end

                  oty && DAE.T_METARECORD(__)  => begin
                      (vars, a) = traverseVarTypes(oty.fields, a, fn)
                      oty.fields = vars
                    (oty, a)
                  end

                  oty && DAE.T_COMPLEX(__)  => begin
                      (vars, a) = traverseVarTypes(oty.varLst, a, fn)
                      oty.varLst = vars
                    (oty, a)
                  end

                  oty && DAE.T_SUBTYPE_BASIC(__)  => begin
                      (vars, a) = traverseVarTypes(oty.varLst, a, fn)
                      (tyInner, a) = traverseType(oty.complexType, a, fn)
                      oty.varLst = vars
                      oty.complexType = tyInner
                    (oty, a)
                  end

                  oty && DAE.T_FUNCTION(__)  => begin
                      (farg, a) = traverseFuncArg(oty.funcArg, a, fn)
                      (tyInner, a) = traverseType(oty.funcResultType, a, fn)
                      oty.funcArg = farg
                      oty.funcResultType = tyInner
                    (oty, a)
                  end

                  _  => begin
                        str = "Types.traverseType not implemented correctly: " + unparseType(ty)
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
              (oty, a) = fn(oty, a)
          (oty, a)
        end

        function traverseTupleType(itys::List{<:DAE.Type}, ia::A, fn::Func) ::Tuple{List{DAE.Type}, A}
              local oa::A
              local otys::List{DAE.Type}

              (otys, oa) = begin
                  local ty::Type
                  local tys::List{DAE.Type}
                  local a::A
                @match (itys, ia, fn) begin
                  ( nil(), a, _)  => begin
                    (nil, a)
                  end

                  (ty <| tys, a, _)  => begin
                      (ty, a) = traverseType(ty, a, fn)
                      (tys, a) = traverseTupleType(tys, a, fn)
                    (_cons(ty, tys), a)
                  end
                end
              end
          (otys, oa)
        end

        function traverseVarTypes(ivars::List{<:DAE.Var}, ia::A, fn::Func) ::Tuple{List{DAE.Var}, A}
              local oa::A
              local ovars::List{DAE.Var}

              (ovars, oa) = begin
                  local var::DAE.Var
                  local ty::DAE.Type
                  local vars::List{DAE.Var}
                  local a::A
                @match (ivars, ia, fn) begin
                  ( nil(), a, _)  => begin
                    (nil, a)
                  end

                  (var <| vars, a, _)  => begin
                      ty = getVarType(var)
                      (ty, a) = traverseType(ty, a, fn)
                      var = setVarType(var, ty)
                      (vars, a) = traverseVarTypes(vars, a, fn)
                    (_cons(var, vars), a)
                  end
                end
              end
          (ovars, oa)
        end

        function traverseFuncArg(iargs::List{<:DAE.FuncArg}, ia::A, fn::Func) ::Tuple{List{DAE.FuncArg}, A}
              local oa::A
              local oargs::List{DAE.FuncArg}

              (oargs, oa) = begin
                  local b::String
                  local c::DAE.Const
                  local p::DAE.VarParallelism
                  local d::Option{DAE.Exp}
                  local args::List{DAE.FuncArg}
                  local a::A
                  local arg::DAE.FuncArg
                  local ty::DAE.Type
                @match (iargs, ia) begin
                  ( nil(), a)  => begin
                    (nil, a)
                  end

                  (arg && DAE.FUNCARG(__) <| args, a)  => begin
                      (ty, a) = traverseType(arg.ty, a, fn)
                      arg.ty = ty
                      (args, a) = traverseFuncArg(args, a, fn)
                    (_cons(arg, args), a)
                  end
                end
              end
          (oargs, oa)
        end

        function makeRegularTupleFromMetaTupleOnTrue(b::Bool, ty::DAE.Type) ::DAE.Type
              local out::DAE.Type

              out = begin
                  local tys::List{DAE.Type}
                @match (b, ty) begin
                  (true, DAE.T_METATUPLE(tys))  => begin
                      tys = ListUtil.mapMap(tys, unboxedType, boxIfUnboxedType)
                      tys = ListUtil.map(tys, unboxedType)
                    DAE.T_TUPLE(tys, NONE())
                  end

                  (false, _)  => begin
                    ty
                  end
                end
              end
               #=  Yes. Crazy
               =#
          out
        end

        function allTuple(itys::List{<:DAE.Type}) ::Bool
              local b::Bool

              b = begin
                  local tys::List{DAE.Type}
                @match itys begin
                   nil()  => begin
                    true
                  end

                  DAE.T_TUPLE(__) <| tys  => begin
                    allTuple(tys)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= For DAE.PARTEVALFUNC =#
        function unboxedFunctionType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local args1::List{DAE.FuncArg}
                  local tys1::List{DAE.Type}
                  local names1::List{String}
                  local cs1::List{DAE.Const}
                  local ps1::List{DAE.VarParallelism}
                  local oe1::List{Option{DAE.Exp}}
                  local ty1::Type
                  local functionAttributes::DAE.FunctionAttributes
                  local path::Absyn.Path
                @match inType begin
                  DAE.T_FUNCTION(args1, ty1, functionAttributes, path)  => begin
                      tys1 = ListUtil.mapMap(args1, funcArgType, unboxedType)
                      ty1 = unboxedType(ty1)
                      args1 = ListUtil.threadMap(args1, tys1, setFuncArgType)
                    DAE.T_FUNCTION(args1, ty1, functionAttributes, path)
                  end
                end
              end
          outType
        end

        function printCodeTypeStr(ct::DAE.CodeType) ::String
              local str::String

              str = begin
                @match ct begin
                  DAE.C_EXPRESSION(__)  => begin
                    "OpenModelica.Code.Expression"
                  end

                  DAE.C_EXPRESSION_OR_MODIFICATION(__)  => begin
                    "OpenModelica.Code.ExpressionOrModification"
                  end

                  DAE.C_MODIFICATION(__)  => begin
                    "OpenModelica.Code.Modification"
                  end

                  DAE.C_TYPENAME(__)  => begin
                    "OpenModelica.Code.TypeName"
                  end

                  DAE.C_VARIABLENAME(__)  => begin
                    "OpenModelica.Code.VariableName"
                  end

                  DAE.C_VARIABLENAMES(__)  => begin
                    "OpenModelica.Code.VariableNames"
                  end

                  _  => begin
                      "Types.printCodeTypeStr failed"
                  end
                end
              end
          str
        end

        function varHasMetaRecordType(var::DAE.Var) ::Bool
              local b::Bool

              b = begin
                @match var begin
                  DAE.TYPES_VAR(ty = DAE.T_METABOXED(ty = DAE.T_METARECORD(__)))  => begin
                    true
                  end

                  DAE.TYPES_VAR(ty = DAE.T_METARECORD(__))  => begin
                    true
                  end

                  DAE.TYPES_VAR(ty = DAE.T_METABOXED(ty = DAE.T_COMPLEX(complexClassType = ClassInf.META_RECORD(_))))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function optInteger(inInt::Option{<:ModelicaInteger}) ::ModelicaInteger
              local outInt::ModelicaInteger

              outInt = begin
                  local i::ModelicaInteger
                @match inInt begin
                  SOME(i)  => begin
                    i
                  end

                  _  => begin
                      -1
                  end
                end
              end
          outInt
        end

         #= This function builds Values.Value out of a type using generated bindings. =#
        function typeToValue(inType::DAE.Type) ::Values.Value
              local defaultValue::Values.Value

              defaultValue = begin
                  local vars::List{DAE.Var}
                  local comp::List{String}
                  local st::ClassInf.SMNode
                  local t::Type
                  local tys::List{DAE.Type}
                  local s1::String
                  local path::Absyn.Path
                  local i::ModelicaInteger
                  local iOpt::Option{ModelicaInteger}
                  local v::Values.Value
                  local valueLst::List{Values.Value}
                  local ordered::List{Values.Value}
                @matchcontinue inType begin
                  DAE.T_INTEGER(__)  => begin
                    Values.INTEGER(0)
                  end

                  DAE.T_REAL(__)  => begin
                    Values.REAL(0.0)
                  end

                  DAE.T_STRING(__)  => begin
                    Values.STRING("<EMPTY>")
                  end

                  DAE.T_BOOL(__)  => begin
                    Values.BOOL(false)
                  end

                  DAE.T_ENUMERATION(index = iOpt, path = path)  => begin
                      i = optInteger(iOpt)
                    Values.ENUM_LITERAL(path, i)
                  end

                  DAE.T_COMPLEX(complexClassType = st, varLst = vars)  => begin
                      (ordered, comp) = varsToValues(vars)
                      path = ClassInf.getStateName(st)
                    Values.RECORD(path, ordered, comp, -1)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                      v = typeToValue(t)
                    v
                  end

                  DAE.T_ARRAY(dims = DAE.DIM_INTEGER(i) <|  nil(), ty = t)  => begin
                      v = typeToValue(t)
                      valueLst = ListUtil.fill(v, i)
                    Values.ARRAY(valueLst, list(i))
                  end

                  DAE.T_TUPLE(types = tys)  => begin
                      valueLst = ListUtil.map(tys, typeToValue)
                      v = Values.TUPLE(valueLst)
                    v
                  end

                  DAE.T_UNKNOWN(__)  => begin
                    Values.META_FAIL()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Types.typeToValue failed on unhandled Type ")
                        s1 = printTypeStr(inType)
                        Debug.traceln(s1)
                      fail()
                  end
                end
              end
               #=  All the other ones we don't handle
               =#
          defaultValue
        end

         #= Translates a list of Var list to Values.Value, the
          names of the variables as component names.
          Used e.g. when retrieving the type of a record value. =#
        function varsToValues(inVarLst::List{<:DAE.Var}) ::Tuple{List{Values.Value}, List{String}}
              local outExpIdentLst::List{String}
              local outValuesValueLst::List{Values.Value}

              (outValuesValueLst, outExpIdentLst) = begin
                  local tp::DAE.Type
                  local rest::List{DAE.Var}
                  local v::Values.Value
                  local restVals::List{Values.Value}
                  local id::String
                  local restIds::List{String}
                @matchcontinue inVarLst begin
                   nil()  => begin
                    (nil, nil)
                  end

                  DAE.TYPES_VAR(name = id, ty = tp) <| rest  => begin
                      v = typeToValue(tp)
                      (restVals, restIds) = varsToValues(rest)
                    (_cons(v, restVals), _cons(id, restIds))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Types.varsToValues failed\\n")
                      fail()
                  end
                end
              end
          (outValuesValueLst, outExpIdentLst)
        end

         #= Real [3,2,1],3 => Real [3,2,:] =#
        function makeNthDimUnknown(ty::DAE.Type, dim::ModelicaInteger) ::DAE.Type
              local oty::DAE.Type

              oty = begin
                  local ad::DAE.Dimension
                  local ty1::Type
                @match (ty, dim) begin
                  (DAE.T_ARRAY(ty1, _ <|  nil()), 1)  => begin
                    DAE.T_ARRAY(ty1, list(DAE.DIM_UNKNOWN()))
                  end

                  (DAE.T_ARRAY(ty1, ad <|  nil()), _)  => begin
                      ty1 = makeNthDimUnknown(ty1, dim - 1)
                    DAE.T_ARRAY(ty1, list(ad))
                  end
                end
              end
          oty
        end

         #= Selects the supertype out of two array-types. Integer may be promoted to Real. =#
        function arraySuperType(ity1::DAE.Type, info::SourceInfo, ity2::DAE.Type) ::DAE.Type
              local ty::DAE.Type

              ty = begin
                  local str1::String
                  local str2::String
                  local ty1::Type
                  local ty2::Type
                @matchcontinue (ity1, info, ity2) begin
                  (ty1, _, ty2)  => begin
                      @match true = isInteger(arrayElementType(ty1))
                      @match true = isReal(arrayElementType(ty2))
                      ty1 = traverseType(ty1, -1, replaceIntegerTypeWithReal)
                      @match true = subtype(ty1, ty2)
                    ty1
                  end

                  (ty1, _, ty2)  => begin
                      @match true = isInteger(arrayElementType(ty2))
                      @match true = isReal(arrayElementType(ty1))
                      ty2 = traverseType(ty2, -1, replaceIntegerTypeWithReal)
                      @match true = subtype(ty1, ty2)
                    ty1
                  end

                  (ty1, _, ty2)  => begin
                      @match true = subtype(ty1, ty2)
                    ty1
                  end

                  (ty1, _, ty2)  => begin
                      str1 = unparseType(ty1)
                      str2 = unparseType(ty2)
                      typeErrorSanityCheck(str1, str2, info)
                      Error.addSourceMessage(Error.ARRAY_TYPE_MISMATCH, list(str1, str2), info)
                    fail()
                  end
                end
              end
          ty
        end

        function replaceIntegerTypeWithReal(ty::Type, dummy::ModelicaInteger) ::Tuple{Type, ModelicaInteger}
              local odummy::ModelicaInteger = dummy
              local oty::Type

              oty = begin
                @match ty begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  _  => begin
                      ty
                  end
                end
              end
          (oty, odummy)
        end

        function isZeroLengthArray(ty::DAE.Type) ::Bool
              local res::Bool

              res = begin
                  local dims::List{DAE.Dimension}
                @match ty begin
                  DAE.T_ARRAY(dims = dims)  => begin
                      res = ListUtil.fold(dims, isZeroDim, false)
                    res
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= Check dimensions by folding and checking for zeroes =#
        function isZeroDim(dim::DAE.Dimension, acc::Bool) ::Bool
              local res::Bool

              res = begin
                @match (dim, acc) begin
                  (DAE.DIM_INTEGER(integer = 0), _)  => begin
                    true
                  end

                  (DAE.DIM_ENUM(size = 0), _)  => begin
                    true
                  end

                  _  => begin
                      acc
                  end
                end
              end
          res
        end

         #= translates an SCode.Variability to a DAE.Const =#
        function variabilityToConst(variability::SCode.Variability) ::DAE.Const
              local constType::DAE.Const

              constType = begin
                @match variability begin
                  SCode.VAR(__)  => begin
                    DAE.C_VAR()
                  end

                  SCode.DISCRETE(__)  => begin
                    DAE.C_VAR()
                  end

                  SCode.PARAM(__)  => begin
                    DAE.C_PARAM()
                  end

                  SCode.CONST(__)  => begin
                    DAE.C_CONST()
                  end
                end
              end
          constType
        end

         #= translates an DAE.varKind to a DAE.Const =#
        function varKindToConst(varKind::DAE.VarKind) ::DAE.Const
              local constType::DAE.Const

              constType = begin
                @match varKind begin
                  DAE.VARIABLE(__)  => begin
                    DAE.C_VAR()
                  end

                  DAE.DISCRETE(__)  => begin
                    DAE.C_VAR()
                  end

                  DAE.PARAM(__)  => begin
                    DAE.C_PARAM()
                  end

                  DAE.CONST(__)  => begin
                    DAE.C_CONST()
                  end
                end
              end
          constType
        end

        function isValidFunctionVarType(inType::DAE.Type) ::Bool
              local outIsValid::Bool

              outIsValid = begin
                  local ty::Type
                  local state::ClassInf.SMNode
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = state)  => begin
                    isValidFunctionVarState(state)
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = ty)  => begin
                    isValidFunctionVarType(ty)
                  end

                  _  => begin
                      true
                  end
                end
              end
          outIsValid
        end

        function isValidFunctionVarState(inState::ClassInf.SMNode) ::Bool
              local outIsValid::Bool

              outIsValid = begin
                @match inState begin
                  ClassInf.MODEL(__)  => begin
                    false
                  end

                  ClassInf.BLOCK(__)  => begin
                    false
                  end

                  ClassInf.CONNECTOR(__)  => begin
                    false
                  end

                  ClassInf.OPTIMIZATION(__)  => begin
                    false
                  end

                  ClassInf.PACKAGE(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outIsValid
        end

         #= Creates a dummy expression from a type. Used by typeConvertArray to handle
          empty arrays. =#
        function makeDummyExpFromType(inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local p::Absyn.Path
                  local ty::Type
                  local dim::DAE.Dimension
                  local idim::ModelicaInteger
                  local exp::DAE.Exp
                  local expl::List{DAE.Exp}
                  local ety::DAE.Type
                @match inType begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.ICONST(0)
                  end

                  DAE.T_REAL(__)  => begin
                    DAE.RCONST(0.0)
                  end

                  DAE.T_STRING(__)  => begin
                    DAE.SCONST("")
                  end

                  DAE.T_BOOL(__)  => begin
                    DAE.BCONST(false)
                  end

                  DAE.T_ENUMERATION(path = p)  => begin
                    DAE.ENUM_LITERAL(p, 1)
                  end

                  DAE.T_ARRAY(ty = ty, dims = dim <|  nil())  => begin
                      idim = Expression.dimensionSize(dim)
                      exp = makeDummyExpFromType(ty)
                      ety = Expression.typeof(exp)
                      ety = Expression.liftArrayLeft(ety, dim)
                      expl = ListUtil.fill(exp, idim)
                    DAE.ARRAY(ety, true, expl)
                  end
                end
              end
          outExp
        end

        function printExpTypeStr(iet::DAE.Type) ::String
              local str::String

              str = printTypeStr(expTypetoTypesType(iet))
          str
        end

         #= Return true if the type is DAE.T_UNKNOWN or DAE.T_ANYTYPE =#
        function isUnknownType(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match inType begin
                  DAE.T_UNKNOWN(__)  => begin
                    true
                  end

                  DAE.T_ANYTYPE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if the given type is overdetermined, i.e. a type or record with
           an equalityConstraint function, otherwise false. =#
        function isOverdeterminedType(inType::DAE.Type) ::Bool
              local outIsOverdetermined::Bool

              outIsOverdetermined = begin
                  local cct::ClassInf.SMNode
                @match inType begin
                  DAE.T_COMPLEX(complexClassType = cct, equalityConstraint = SOME(_))  => begin
                    ClassInf.isTypeOrRecord(cct)
                  end

                  DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
                    true
                  end
                end
              end
          outIsOverdetermined
        end

        function hasMetaArray(ty::DAE.Type) ::Bool
              local b::Bool

              (_, b) = traverseType(ty, false, hasMetaArrayWork)
          b
        end

        function hasMetaArrayWork(ty::Type, b::Bool) ::Tuple{Type, Bool}
              local ob::Bool = b
              local oty::Type = ty

              if ! b
                ob = begin
                  @match ty begin
                    DAE.T_METAARRAY(__)  => begin
                      true
                    end

                    _  => begin
                        false
                    end
                  end
                end
              end
          (oty, ob)
        end

        function classTypeEqualIfRecord(st1::ClassInf.SMNode, st2::ClassInf.SMNode) ::Bool
              local b::Bool

              b = begin
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                @match (st1, st2) begin
                  (ClassInf.RECORD(p1), ClassInf.RECORD(p2))  => begin
                    AbsynUtil.pathEqual(p1, p2)
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

         #= If one branch of an if-expression has truly unknown dimensions they both will need to return unknown dimensions for type-checking to work =#
        function ifExpMakeDimsUnknown(ty1::DAE.Type, ty2::DAE.Type) ::Tuple{DAE.Type, DAE.Type}
              local oty2::DAE.Type
              local oty1::DAE.Type

              (oty1, oty2) = begin
                  local inner1::DAE.Type
                  local inner2::DAE.Type
                  local d1::DAE.Dimension
                  local d2::DAE.Dimension
                @match (ty1, ty2) begin
                  (DAE.T_ARRAY(ty = inner1, dims = DAE.DIM_UNKNOWN(__) <|  nil()), DAE.T_ARRAY(ty = inner2, dims = _ <|  nil()))  => begin
                      (oty1, oty2) = ifExpMakeDimsUnknown(inner1, inner2)
                    (DAE.T_ARRAY(inner1, _cons(DAE.DIM_UNKNOWN(), nil)), DAE.T_ARRAY(inner2, _cons(DAE.DIM_UNKNOWN(), nil)))
                  end

                  (DAE.T_ARRAY(ty = inner1, dims = _ <|  nil()), DAE.T_ARRAY(ty = inner2, dims = DAE.DIM_UNKNOWN(__) <|  nil()))  => begin
                      (oty1, oty2) = ifExpMakeDimsUnknown(inner1, inner2)
                    (DAE.T_ARRAY(inner1, _cons(DAE.DIM_UNKNOWN(), nil)), DAE.T_ARRAY(inner2, _cons(DAE.DIM_UNKNOWN(), nil)))
                  end

                  (DAE.T_ARRAY(ty = inner1, dims = d1 <|  nil()), DAE.T_ARRAY(ty = inner2, dims = d2 <|  nil()))  => begin
                      (oty1, oty2) = ifExpMakeDimsUnknown(inner1, inner2)
                    (DAE.T_ARRAY(inner1, list(d1)), DAE.T_ARRAY(inner2, list(d2)))
                  end

                  _  => begin
                      (ty1, ty2)
                  end
                end
              end
          (oty1, oty2)
        end

         #= check if the type has bindings for everything
         if is parameter or constant without fixed = false
         specified otherwise =#
        function isFixedWithNoBinding(inTy::DAE.Type, inVariability::SCode.Variability) ::Bool
              local outFixed::Bool

              outFixed = begin
                  local b::Bool
                  local vl::List{DAE.Var}
                @matchcontinue (inTy, inVariability) begin
                  (_, _)  => begin
                      b = getFixedVarAttribute(inTy)
                    b
                  end

                  (DAE.T_COMPLEX(varLst = vl), _)  => begin
                      @match true = allHaveBindings(vl)
                    false
                  end

                  _  => begin
                        b = listMember(inVariability, list(SCode.PARAM(), SCode.CONST()))
                      b
                  end
                end
              end
               #=  if this function doesn't fail return its value
               =#
               #=  we couldn't get the fixed attribute
               =#
               #=  assume true for constants and parameters
               =#
               #=  false otherwise
               =#
          outFixed
        end

        function allHaveBindings(inVars::List{<:DAE.Var}) ::Bool
              local b::Bool

              b = begin
                  local v::DAE.Var
                  local rest::List{DAE.Var}
                @matchcontinue inVars begin
                   nil()  => begin
                    true
                  end

                  v <| _  => begin
                      @match false = hasBinding(v)
                    false
                  end

                  v <| rest  => begin
                      @match true = hasBinding(v)
                      @match true = allHaveBindings(rest)
                    true
                  end
                end
              end
          b
        end

        function hasBinding(inVar::DAE.Var) ::Bool
              local b::Bool

              b = begin
                @match inVar begin
                  DAE.TYPES_VAR(binding = DAE.UNBOUND(__))  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

        function typeErrorSanityCheck(inType1::String, inType2::String, inInfo::SourceInfo)
              _ = begin
                @matchcontinue (inType1, inType2, inInfo) begin
                  (_, _, _)  => begin
                      @match false = stringEq(inType1, inType2)
                    ()
                  end

                  _  => begin
                        Error.addSourceMessage(Error.ERRONEOUS_TYPE_ERROR, list(inType1), inInfo)
                      fail()
                  end
                end
              end
        end

        function dimNotFixed(dim::DAE.Dimension) ::Bool
              local b::Bool

              b = begin
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
          b
        end

        function isArrayWithUnknownDimension(ty::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_ARRAY(__)  => begin
                    max(begin
                      @match d begin
                        DAE.DIM_UNKNOWN(__)  => begin
                          true
                        end

                        _  => begin
                            false
                        end
                      end
                    end for d in getDimensions(ty))
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Strips the attribute variables from a type, and returns both the stripped
           type and the attribute variables. =#
        function stripTypeVars(inType::DAE.Type) ::Tuple{DAE.Type, List{DAE.Var}}
              local outVars::List{DAE.Var}
              local outType::DAE.Type

              (outType, outVars) = begin
                  local vars::List{DAE.Var}
                  local sub_vars::List{DAE.Var}
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                  local state::ClassInf.SMNode
                  local ec::EqualityConstraint
                  local tys::List{DAE.Type}
                @match inType begin
                  DAE.T_INTEGER(varLst = vars)  => begin
                    (DAE.T_INTEGER_DEFAULT, vars)
                  end

                  DAE.T_REAL(varLst = vars)  => begin
                    (DAE.T_REAL_DEFAULT, vars)
                  end

                  DAE.T_STRING(varLst = vars)  => begin
                    (DAE.T_STRING_DEFAULT, vars)
                  end

                  DAE.T_BOOL(varLst = vars)  => begin
                    (DAE.T_BOOL_DEFAULT, vars)
                  end

                  DAE.T_TUPLE(tys, _)  => begin
                    (DAE.T_TUPLE(tys, NONE()), nil)
                  end

                  DAE.T_ARRAY(ty, dims)  => begin
                      (ty, vars) = stripTypeVars(ty)
                    (DAE.T_ARRAY(ty, dims), vars)
                  end

                  DAE.T_SUBTYPE_BASIC(state, sub_vars, ty, ec)  => begin
                      (ty, vars) = stripTypeVars(ty)
                    (DAE.T_SUBTYPE_BASIC(state, sub_vars, ty, ec), vars)
                  end

                  _  => begin
                      (inType, nil)
                  end
                end
              end
          (outType, outVars)
        end

        function setTypeVars(ty::DAE.Type, inVars::List{<:DAE.Var}) ::DAE.Type


              ty = begin
                @match ty begin
                  DAE.T_REAL(__)  => begin
                      ty.varLst = inVars
                    ty
                  end

                  DAE.T_INTEGER(__)  => begin
                      ty.varLst = inVars
                    ty
                  end

                  DAE.T_STRING(__)  => begin
                      ty.varLst = inVars
                    ty
                  end

                  DAE.T_BOOL(__)  => begin
                      ty.varLst = inVars
                    ty
                  end

                  DAE.T_CLOCK(__)  => begin
                      ty.varLst = inVars
                    ty
                  end

                  DAE.T_ENUMERATION(__)  => begin
                      ty.attributeLst = inVars
                    ty
                  end

                  DAE.T_ARRAY(__)  => begin
                      ty.ty = setTypeVars(ty.ty, inVars)
                    ty
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                      ty.complexType = setTypeVars(ty.complexType, inVars)
                    ty
                  end
                end
              end
          ty
        end

        function isEmptyOrNoRetcall(ty::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_TUPLE(types =  nil())  => begin
                    true
                  end

                  DAE.T_METATUPLE(types =  nil())  => begin
                    true
                  end

                  DAE.T_NORETCALL(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #=
          Deal with the invalid conversions from Integer to enumeration.
          If the Integer corresponds to the Integer(ENUM) value of some enumeration constant ENUM,
          just give a warning, otherwise report an error.
          Returns false if an error was reported, otherwise true.
         =#
        function typeConvertIntToEnumCheck(exp::DAE.Exp, expected::DAE.Type) ::Bool
              local conversionOK::Bool

              conversionOK = begin
                  local oi::ModelicaInteger
                  local tp::Absyn.Path
                  local l::List{String}
                  local pathStr::String
                  local intStr::String
                  local enumConst::String
                  local lengthStr::String
                @matchcontinue (exp, expected) begin
                  (DAE.ICONST(oi), DAE.T_ENUMERATION(path = tp, names = l))  => begin
                      @match true = 1 <= oi && oi <= listLength(l)
                      pathStr = AbsynUtil.pathString(tp)
                      intStr = intString(oi)
                      enumConst = listGet(l, oi)
                      Error.addMessage(Error.INTEGER_ENUMERATION_CONVERSION_WARNING, list(intStr, pathStr, enumConst))
                    true
                  end

                  (DAE.ICONST(oi), DAE.T_ENUMERATION(path = tp, names = l))  => begin
                      pathStr = AbsynUtil.pathString(tp)
                      @match false = stringEq(pathStr, "")
                      intStr = intString(oi)
                      lengthStr = intString(listLength(l))
                      Error.addMessage(Error.INTEGER_ENUMERATION_OUT_OF_RANGE, list(pathStr, intStr, lengthStr))
                    false
                  end

                  (DAE.ICONST(oi), DAE.T_ENUMERATION(path = tp))  => begin
                      pathStr = AbsynUtil.pathString(tp)
                      @match true = stringEq(pathStr, "")
                      intStr = intString(oi)
                      Error.addMessage(Error.INTEGER_TO_UNKNOWN_ENUMERATION, list(intStr))
                    false
                  end
                end
              end
          conversionOK
        end

        function findVarIndex(id::String, vars::List{<:DAE.Var}) ::ModelicaInteger
              local index::ModelicaInteger

              index = ListUtil.position1OnTrue(vars, selectVar, id) - 1 #= shift to zero-based index =#
          index
        end

        function selectVar(var::DAE.Var, id::String) ::Bool
              local b::Bool

              b = begin
                  local id1::String
                @match var begin
                  DAE.TYPES_VAR(name = id1)  => begin
                    stringEq(id, id1)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function getUniontypeIfMetarecord(inTy::DAE.Type) ::DAE.Type
              local ty::DAE.Type

              ty = begin
                  local b::Bool
                  local p::Absyn.Path
                @match inTy begin
                  DAE.T_METARECORD(utPath = p, knownSingleton = b)  => begin
                    DAE.T_METAUNIONTYPE(nil, inTy.typeVars, b, if b
                          DAE.EVAL_SINGLETON_KNOWN_TYPE(inTy)
                        else
                          DAE.NOT_SINGLETON()
                        end, p)
                  end

                  _  => begin
                      inTy
                  end
                end
              end
          ty
        end

        function getUniontypeIfMetarecordReplaceAllSubtypes(inTy::DAE.Type) ::DAE.Type
              local ty::DAE.Type

              (ty, _) = traverseType(inTy, 1, getUniontypeIfMetarecordTraverse)
          ty
        end

        function getUniontypeIfMetarecordTraverse(ty::DAE.Type, dummy::ModelicaInteger) ::Tuple{DAE.Type, ModelicaInteger}
              local odummy::ModelicaInteger = dummy
              local oty::DAE.Type

              oty = begin
                @match ty begin
                  DAE.T_METARECORD(__)  => begin
                    DAE.T_METAUNIONTYPE(nil, ty.typeVars, ty.knownSingleton, if ty.knownSingleton
                          DAE.EVAL_SINGLETON_KNOWN_TYPE(ty)
                        else
                          DAE.NOT_SINGLETON()
                        end, ty.utPath)
                  end

                  _  => begin
                      ty
                  end
                end
              end
          (oty, odummy)
        end

        function isBuiltin(a::DAE.FunctionBuiltin) ::Bool
              local b::Bool

              b = begin
                @match a begin
                  DAE.FUNCTION_NOT_BUILTIN(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

        function makeCallAttr(ty::DAE.Type, attr::DAE.FunctionAttributes) ::DAE.CallAttributes
              local callAttr::DAE.CallAttributes

              local isImpure::Bool
              local isT::Bool
              local isB::Bool
              local isbuiltin::DAE.FunctionBuiltin
              local isinline::DAE.InlineType
              local name::Option{String}

              @match DAE.FUNCTION_ATTRIBUTES(isBuiltin = isbuiltin, isImpure = isImpure, inline = isinline) = attr
              isT = isTuple(ty)
              isB = isBuiltin(isbuiltin)
              callAttr = DAE.CALL_ATTR(ty, isT, isB, isImpure, false, isinline, DAE.NO_TAIL())
          callAttr
        end

        function builtinName(isbuiltin::DAE.FunctionBuiltin) ::Option{String}
              local name::Option{String}

              name = begin
                @match isbuiltin begin
                  DAE.FUNCTION_BUILTIN(__)  => begin
                    isbuiltin.name
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          name
        end

        function getFuncArg(ty::DAE.Type) ::List{DAE.FuncArg}
              local args::List{DAE.FuncArg}

              @match DAE.T_FUNCTION(funcArg = args) = ty
          args
        end

        function isArray1D(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local ty::DAE.Type
                @match inType begin
                  DAE.T_ARRAY(ty = ty)  => begin
                    ! arrayType(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isArray2D(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                  local ty::DAE.Type
                @match inType begin
                  DAE.T_ARRAY(ty = DAE.T_ARRAY(ty = ty))  => begin
                    ! arrayType(ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function funcArgName(arg::DAE.FuncArg) ::String
              local name::String

              @match DAE.FUNCARG(name = name) = arg
          name
        end

        function funcArgType(arg::DAE.FuncArg) ::DAE.Type
              local ty::DAE.Type

              @match DAE.FUNCARG(ty = ty) = arg
          ty
        end

        function funcArgDefaultBinding(arg::DAE.FuncArg) ::Option{DAE.Exp}
              local defaultBinding::Option{DAE.Exp}

              @match DAE.FUNCARG(defaultBinding = defaultBinding) = arg
          defaultBinding
        end

        function setFuncArgType(arg::DAE.FuncArg, ty::DAE.Type) ::DAE.FuncArg
              local outArg::DAE.FuncArg

              local name::String
              local constType::DAE.Const
              local par::DAE.VarParallelism
              local defaultBinding::Option{DAE.Exp}

              @match DAE.FUNCARG(name, _, constType, par, defaultBinding) = arg
              outArg = DAE.FUNCARG(name, ty, constType, par, defaultBinding)
          outArg
        end

        function setFuncArgName(arg::DAE.FuncArg, name::String) ::DAE.FuncArg
              local outArg::DAE.FuncArg

              local ty::DAE.Type
              local constType::DAE.Const
              local par::DAE.VarParallelism
              local defaultBinding::Option{DAE.Exp}

              @match DAE.FUNCARG(_, ty, constType, par, defaultBinding) = arg
              outArg = DAE.FUNCARG(name, ty, constType, par, defaultBinding)
          outArg
        end

        function clearDefaultBinding(arg::DAE.FuncArg) ::DAE.FuncArg
              local outArg::DAE.FuncArg

              local name::String
              local ty::DAE.Type
              local constType::DAE.Const
              local par::DAE.VarParallelism

              @match DAE.FUNCARG(name, ty, constType, par, _) = arg
              outArg = DAE.FUNCARG(name, ty, constType, par, NONE())
          outArg
        end

        function makeDefaultFuncArg(name::String, ty::DAE.Type) ::DAE.FuncArg
              local arg::DAE.FuncArg

              arg = DAE.FUNCARG(name, ty, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())
          arg
        end

        function setIsFunctionPointer(ty::DAE.Type, dummy::ModelicaInteger) ::Tuple{DAE.Type, ModelicaInteger}
              local odummy::ModelicaInteger = dummy
              local oty::DAE.Type = ty

              oty = begin
                  local attr::DAE.FunctionAttributes
                @match oty begin
                  DAE.T_FUNCTION(functionAttributes = attr && DAE.FUNCTION_ATTRIBUTES(isFunctionPointer = false))  => begin
                      attr.isFunctionPointer = true
                      oty.functionAttributes = attr
                    oty
                  end

                  _  => begin
                      oty
                  end
                end
              end
          (oty, odummy)
        end

        function isFunctionReferenceVar(ty::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_FUNCTION_REFERENCE_VAR(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isFunctionPointer(inType::DAE.Type) ::Bool
              local outIsFunPtr::Bool

              outIsFunPtr = begin
                @match inType begin
                  DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isFunctionPointer = true))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsFunPtr
        end

        function filterRecordComponents(inRecordVars::List{<:DAE.Var}, inInfo::SourceInfo) ::List{DAE.Var}
              local outRecordVars::List{DAE.Var}

              outRecordVars = list(begin
                @match v begin
                  DAE.TYPES_VAR(__)  => begin
                      if ! allowedInRecord(v.ty)
                        Error.addSourceMessage(Error.ILLEGAL_RECORD_COMPONENT, list(unparseVar(v)), inInfo)
                        fail()
                      end
                    v
                  end
                end
              end for v in inRecordVars)
          outRecordVars
        end

        function allowedInRecord(ty::DAE.Type) ::Bool
              local yes::Bool

              yes = begin
                  local t::DAE.Type
                   #=  basic types, records or arrays of the same
                   =#
                @matchcontinue ty begin
                  _  => begin
                      t = arrayElementType(ty)
                      @match true = basicType(t) || isRecord(t) || extendsBasicType(t)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  nothing else please!
               =#
          yes
        end

        function lookupIndexInMetaRecord(vars::List{<:DAE.Var}, name::String) ::ModelicaInteger
              local index::ModelicaInteger

              index = ListUtil.position1OnTrue(vars, DAEUtil.typeVarIdentEqual, name)
          index
        end

        function checkEnumDuplicateLiterals(names::List{<:String}, info::Absyn.Info)
              local sortedNames::List{String}

               #=  Sort+uniq = O(n*log(n)); naive way to check duplicates is O(n*n) but might be faster...
               =#
              sortedNames = ListUtil.sort(names, Util.strcmpBool)
              if ! ListUtil.sortedListAllUnique(sortedNames, stringEq)
                Error.addSourceMessage(Error.ENUM_DUPLICATES, list(stringDelimitList(ListUtil.sortedUniqueOnlyDuplicates(sortedNames, stringEq), ","), stringDelimitList(names, ",")), info)
                fail()
              end
        end

         #= This function checks that two types are compatible, as per the definition of
           type compatible expressions in the specification. If needed it also does type
           casting to make the expressions compatible. If the types are compatible it
           returns the compatible type, otherwise the type returned is undefined. =#
        function checkTypeCompat(inExp1::DAE.Exp, inType1::DAE.Type, inExp2::DAE.Exp, inType2::DAE.Type, inAllowUnknown::Bool = false) ::Tuple{DAE.Exp, DAE.Exp, DAE.Type, Bool}
              local outCompatible::Bool = true
              local outCompatType::DAE.Type
              local outExp2::DAE.Exp = inExp2
              local outExp1::DAE.Exp = inExp1

              local ty1::DAE.Type
              local ty2::DAE.Type

               #=  Return true if the references are the same.
               =#
              if referenceEq(inType1, inType2)
                outCompatType = inType1
                return (outExp1, outExp2, outCompatType, outCompatible)
              end
               #=  Check if the types are different kinds of types.
               =#
              if valueConstructor(inType1) != valueConstructor(inType2)
                if extendsBasicType(inType1) || extendsBasicType(inType2)
                  ty1 = derivedBasicType(inType1)
                  ty2 = derivedBasicType(inType2)
                  (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, ty1, inExp2, ty2)
                else
                  (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat_cast(inExp1, inType1, inExp2, inType2, inAllowUnknown)
                end
                return (outExp1, outExp2, outCompatType, outCompatible)
              end
               #=  If either type extends a basic type, check the basic type instead.
               =#
               #=  If the types are not of the same kind they might need to be type cast
               =#
               #=  to become compatible.
               =#
               #=  Regardless of the chosen branch above, we are done here.
               =#
               #=  The types are of the same kind, so we only need to match on one of them
               =#
               #=  (which is a lot more efficient than matching both).
               =#
              outCompatType = begin
                  local dims1::List{DAE.Dimension}
                  local dims2::List{DAE.Dimension}
                  local ety1::DAE.Type
                  local ety2::DAE.Type
                  local ty::DAE.Type
                  local names::List{String}
                  local vars::List{DAE.Var}
                  local args::List{FuncArg}
                  local tys::List{DAE.Type}
                  local tys2::List{DAE.Type}
                  local name::String
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                   #=  Basic types, must be the same.
                   =#
                @match inType1 begin
                  DAE.T_INTEGER(__)  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  DAE.T_REAL(__)  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  DAE.T_STRING(__)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  DAE.T_BOOL(__)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  DAE.T_CLOCK(__)  => begin
                    DAE.T_CLOCK_DEFAULT
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                      @match DAE.T_SUBTYPE_BASIC(complexType = ty) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.complexType, inExp2, ty)
                    outCompatType
                  end

                  DAE.T_ENUMERATION(__)  => begin
                       #=  Enumerations, check that they have same literals.
                       =#
                      @match DAE.T_ENUMERATION(names = names) = inType2
                      outCompatible = ListUtil.isEqualOnTrue(inType1.names, names, stringEq)
                    inType1
                  end

                  DAE.T_ARRAY(__)  => begin
                       #=  Arrays, must have compatible element types and dimensions.
                       =#
                       #=  Check that the element types are compatible.
                       =#
                      ety1 = arrayElementType(inType1)
                      ety2 = arrayElementType(inType2)
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, ety1, inExp2, ety2)
                       #=  If the element types are compatible, check the dimensions too.
                       =#
                      if outCompatible
                        dims1 = getDimensions(inType1)
                        dims2 = getDimensions(inType2)
                        if listLength(dims1) == listLength(dims2)
                          dims1 = list(@do_threaded_for if Expression.dimensionsKnownAndEqual(dim1, dim2)
                                dim1
                              else
                                DAE.DIM_UNKNOWN()
                              end (dim1, dim2) (dims1, dims2))
                          outCompatType = liftArrayListDims(outCompatType, dims1)
                        else
                          outCompatible = false
                        end
                      end
                       #=  The arrays must have the same number of dimensions.
                       =#
                    outCompatType
                  end

                  DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))  => begin
                       #=  Records, must have the same components.
                       =#
                      @match DAE.T_COMPLEX(varLst = vars) = inType2
                       #=  TODO: Implement type casting for records with the same components but
                       =#
                       #=  in different order.
                       =#
                      outCompatible = ListUtil.isEqualOnTrue(inType1.varLst, vars, varEqualName)
                    inType1
                  end

                  DAE.T_FUNCTION(__)  => begin
                      @match DAE.T_FUNCTION(funcResultType = ty, funcArg = args) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.funcResultType, inExp2, ty)
                      if outCompatible
                        tys = list(funcArgType(arg) for arg in inType1.funcArg)
                        tys2 = list(funcArgType(arg) for arg in args)
                        (_, outCompatible) = checkTypeCompatList(inExp1, tys, inExp2, tys2)
                      end
                    inType1
                  end

                  DAE.T_TUPLE(__)  => begin
                      @match DAE.T_TUPLE(types = tys) = inType2
                      (tys, outCompatible) = checkTypeCompatList(inExp1, inType1.types, inExp2, tys)
                    DAE.T_TUPLE(tys, inType1.names)
                  end

                  DAE.T_METALIST(__)  => begin
                       #=  MetaModelica types.
                       =#
                      @match DAE.T_METALIST(ty = ty) = inType2
                       #= print(\"List(\" + anyString(inType1.ty) + \"), List(\" + anyString(ty) + \")\\n\");
                       =#
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.ty, inExp2, ty, true)
                    DAE.T_METALIST(outCompatType)
                  end

                  DAE.T_METAARRAY(__)  => begin
                      @match DAE.T_METAARRAY(ty = ty) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.ty, inExp2, ty, true)
                    DAE.T_METAARRAY(outCompatType)
                  end

                  DAE.T_METAOPTION(__)  => begin
                      @match DAE.T_METAOPTION(ty = ty) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.ty, inExp2, ty, true)
                    DAE.T_METAOPTION(outCompatType)
                  end

                  DAE.T_METATUPLE(__)  => begin
                      @match DAE.T_METATUPLE(types = tys) = inType2
                      (tys, outCompatible) = checkTypeCompatList(inExp1, inType1.types, inExp2, tys)
                    DAE.T_METATUPLE(tys)
                  end

                  DAE.T_METABOXED(__)  => begin
                      @match DAE.T_METABOXED(ty = ty) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.ty, inExp2, ty)
                    DAE.T_METABOXED(outCompatType)
                  end

                  DAE.T_METAPOLYMORPHIC(__)  => begin
                      @match DAE.T_METAPOLYMORPHIC(name = name) = inType2
                      outCompatible = inType1.name == name
                    inType1
                  end

                  DAE.T_METAUNIONTYPE(path = p1)  => begin
                      @match DAE.T_METAUNIONTYPE(path = p2) = inType2
                      outCompatible = AbsynUtil.pathEqual(p1, p2)
                    inType1
                  end

                  DAE.T_METARECORD(utPath = p1)  => begin
                      @match DAE.T_METARECORD(utPath = p2) = inType2
                      outCompatible = AbsynUtil.pathEqual(p1, p2)
                    inType1
                  end

                  DAE.T_FUNCTION_REFERENCE_VAR(__)  => begin
                      @match DAE.T_FUNCTION_REFERENCE_VAR(functionType = ty) = inType2
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, inType1.functionType, inExp2, ty)
                    DAE.T_FUNCTION_REFERENCE_VAR(outCompatType)
                  end

                  _  => begin
                        outCompatible = false
                      DAE.T_UNKNOWN_DEFAULT
                  end
                end
              end
          (outExp1, outExp2, outCompatType, outCompatible)
        end

         #= Checks that two lists of types are compatible using checkTypeCompat. =#
        function checkTypeCompatList(inExp1::DAE.Exp, inTypes1::List{<:DAE.Type}, inExp2::DAE.Exp, inTypes2::List{<:DAE.Type}) ::Tuple{List{DAE.Type}, Bool}
              local outCompatible::Bool = true
              local outCompatibleTypes::List{DAE.Type} = nil

              local ty2::DAE.Type
              local rest_ty2::List{DAE.Type} = inTypes2
              local compat::Bool

              if listLength(inTypes1) != listLength(inTypes2)
                outCompatible = false
                return (outCompatibleTypes, outCompatible)
              end
              for ty1 in inTypes1
                @match _cons(ty2, rest_ty2) = rest_ty2
                (_, _, ty2, compat) = checkTypeCompat(inExp1, ty1, inExp2, ty2)
                if ! compat
                  outCompatible = false
                  return (outCompatibleTypes, outCompatible)
                end
                outCompatibleTypes = _cons(ty2, outCompatibleTypes)
              end
               #=  Ignore the returned expressions. This function is used for tuples, and
               =#
               #=  it's not clear how tuples should be type converted. So we only check that
               =#
               #=  the types are compatible and hope for the best.
               =#
              outCompatibleTypes = listReverse(outCompatibleTypes)
          (outCompatibleTypes, outCompatible)
        end

         #= Helper function to checkTypeCompat. Tries to type cast one of the given
           expressions so that they become type compatible. =#
        function checkTypeCompat_cast(inExp1::DAE.Exp, inType1::DAE.Type, inExp2::DAE.Exp, inType2::DAE.Type, inAllowUnknown::Bool) ::Tuple{DAE.Exp, DAE.Exp, DAE.Type, Bool}
              local outCompatible::Bool = true
              local outCompatType::DAE.Type
              local outExp2::DAE.Exp = inExp2
              local outExp1::DAE.Exp = inExp1

              local ty1::DAE.Type
              local ty2::DAE.Type
              local path::Absyn.Path

              ty1 = derivedBasicType(inType1)
              ty2 = derivedBasicType(inType2)
              outCompatType = begin
                @match (ty1, ty2) begin
                  (DAE.T_REAL(__), DAE.T_INTEGER(__))  => begin
                       #=  Real <-> Integer
                       =#
                      outExp2 = Expression.typeCastElements(inExp2, DAE.T_REAL_DEFAULT)
                    DAE.T_REAL_DEFAULT
                  end

                  (DAE.T_INTEGER(__), DAE.T_REAL(__))  => begin
                      outExp1 = Expression.typeCastElements(inExp1, DAE.T_REAL_DEFAULT)
                    DAE.T_REAL_DEFAULT
                  end

                  (DAE.T_METABOXED(__), _)  => begin
                       #=  If one of the expressions is boxed, unbox it.
                       =#
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, ty1.ty, inExp2, ty2, inAllowUnknown)
                      outExp1 = if isBoxedType(ty2)
                            outExp1
                          else
                            DAE.UNBOX(outExp1, outCompatType)
                          end
                    ty2
                  end

                  (_, DAE.T_METABOXED(__))  => begin
                      (outExp1, outExp2, outCompatType, outCompatible) = checkTypeCompat(inExp1, ty1, inExp2, ty2.ty, inAllowUnknown)
                      outExp2 = if isBoxedType(ty1)
                            outExp2
                          else
                            DAE.UNBOX(outExp2, outCompatType)
                          end
                    ty1
                  end

                  (DAE.T_METARECORD(__), DAE.T_METAUNIONTYPE(__))  => begin
                       #=  Expressions such as Absyn.IDENT gets the type T_METARECORD(Absyn.Path.IDENT)
                       =#
                       #=  instead of UNIONTYPE(Absyn.Path), but e.g. a function returning an
                       =#
                       #=  Absyn.PATH has the type UNIONTYPE(Absyn.PATH). So we'll just pretend that
                       =#
                       #=  metarecords actually have uniontype type.
                       =#
                      outCompatible = AbsynUtil.pathEqual(ty1.utPath, ty2.path)
                    ty2
                  end

                  (DAE.T_METAUNIONTYPE(__), DAE.T_METARECORD(__))  => begin
                      outCompatible = AbsynUtil.pathEqual(ty1.path, ty2.utPath)
                    ty1
                  end

                  (DAE.T_UNKNOWN(__), _)  => begin
                       #=  Allow unknown types in some cases, e.g. () has type T_METALIST(T_UNKNOWN)
                       =#
                      outCompatible = inAllowUnknown
                    ty2
                  end

                  (_, DAE.T_UNKNOWN(__))  => begin
                       #= print(\"Unknown(\" + boolString(inAllowUnknown) + \")\\n\");
                       =#
                      outCompatible = inAllowUnknown
                    ty1
                  end

                  _  => begin
                         #=  Anything else is not compatible.
                         =#
                        outCompatible = false
                      DAE.T_UNKNOWN_DEFAULT
                  end
                end
              end
          (outExp1, outExp2, outCompatType, outCompatible)
        end

         #= Checks if an array type has dimensions which are unknown. =#
        function arrayHasUnknownDims(inType::DAE.Type) ::Bool
              local outUnknownDims::Bool

              outUnknownDims = begin
                @match inType begin
                  DAE.T_ARRAY(__)  => begin
                    ListUtil.exist(inType.dims, Expression.dimensionUnknown) || arrayHasUnknownDims(inType.ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outUnknownDims
        end

        function metaArrayElementType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inType begin
                  DAE.T_METAARRAY(__)  => begin
                    inType.ty
                  end

                  DAE.T_METATYPE(__)  => begin
                    metaArrayElementType(inType.ty)
                  end
                end
              end
          outType
        end

        function isMetaArray(inType::DAE.Type) ::Bool
              local b::Bool

              b = begin
                @match inType begin
                  DAE.T_METAARRAY(__)  => begin
                    true
                  end

                  DAE.T_METATYPE(__)  => begin
                    isMetaArray(inType.ty)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function getAttributes(inType::DAE.Type) ::List{DAE.Var}
              local outAttributes::List{DAE.Var}

              outAttributes = begin
                @match inType begin
                  DAE.T_REAL(__)  => begin
                    inType.varLst
                  end

                  DAE.T_INTEGER(__)  => begin
                    inType.varLst
                  end

                  DAE.T_STRING(__)  => begin
                    inType.varLst
                  end

                  DAE.T_BOOL(__)  => begin
                    inType.varLst
                  end

                  DAE.T_ENUMERATION(__)  => begin
                    inType.attributeLst
                  end

                  DAE.T_SUBTYPE_BASIC(__)  => begin
                    getAttributes(inType.complexType)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outAttributes
        end

        function lookupAttributeValue(inAttributes::List{<:DAE.Var}, inName::String) ::Option{Values.Value}
              local outValue::Option{Values.Value} = NONE()

              for attr in inAttributes
                if inName == varName(attr)
                  outValue = DAEUtil.bindingValue(varBinding(attr))
                  break
                end
              end
          outValue
        end

        function lookupAttributeExp(inAttributes::List{<:DAE.Var}, inName::String) ::Option{DAE.Exp}
              local outExp::Option{DAE.Exp} = NONE()

              for attr in inAttributes
                if inName == varName(attr)
                  outExp = DAEUtil.bindingExp(varBinding(attr))
                  break
                end
              end
          outExp
        end

        function unboxedTypeTraverseHelper(ty::DAE.Type, dummy::T)  where {T}
              local odummy::T = dummy
              local oty::DAE.Type = unboxedType(ty)
          (oty, odummy)
        end

        function getMetaRecordFields(ty::DAE.Type) ::List{DAE.Var}
              local fields::List{DAE.Var}

              fields = begin
                  local fun::DAE.EvaluateSingletonTypeFunction
                @match ty begin
                  DAE.T_METARECORD(fields = fields)  => begin
                    fields
                  end

                  DAE.T_METAUNIONTYPE(knownSingleton = false)  => begin
                      Error.addInternalError(getInstanceName() + " called on a non-singleton uniontype: " + unparseType(ty), sourceInfo())
                    fail()
                  end

                  DAE.T_METAUNIONTYPE(singletonType = DAE.EVAL_SINGLETON_KNOWN_TYPE(ty = DAE.T_METARECORD(fields = fields)))  => begin
                    fields
                  end

                  DAE.T_METAUNIONTYPE(singletonType = DAE.EVAL_SINGLETON_TYPE_FUNCTION(fun = fun))  => begin
                      @match DAE.T_METARECORD(fields = fields) = fun()
                    fields
                  end

                  _  => begin
                        Error.addInternalError(getInstanceName() + " called on a non-singleton uniontype: " + unparseType(ty), sourceInfo())
                      fail()
                  end
                end
              end
          fields
        end

        function getMetaRecordIfSingleton(ty::DAE.Type) ::DAE.Type
              local oty::DAE.Type

              oty = begin
                  local fun::DAE.EvaluateSingletonTypeFunction
                @match ty begin
                  DAE.T_METAUNIONTYPE(knownSingleton = false)  => begin
                    ty
                  end

                  DAE.T_METAUNIONTYPE(singletonType = DAE.EVAL_SINGLETON_KNOWN_TYPE(ty = oty))  => begin
                    setTypeVariables(oty, ty.typeVars)
                  end

                  DAE.T_METAUNIONTYPE(singletonType = DAE.EVAL_SINGLETON_TYPE_FUNCTION(fun = fun))  => begin
                      oty = fun()
                    setTypeVariables(oty, ty.typeVars)
                  end

                  _  => begin
                      ty
                  end
                end
              end
          oty
        end

        function setTypeVariables(ty::DAE.Type, typeVars::List{<:DAE.Type}) ::DAE.Type
              local oty::DAE.Type

              oty = begin
                @match ty begin
                  oty && DAE.T_METAUNIONTYPE(__)  => begin
                      oty.typeVars = typeVars
                    oty
                  end

                  oty && DAE.T_METARECORD(__)  => begin
                      oty.typeVars = typeVars
                    oty
                  end

                  _  => begin
                      ty
                  end
                end
              end
          oty
        end

         #= @author: adrpo
          this function checks if the given type is an expandable connector =#
        function isExpandableConnector(ty::DAE.Type) ::Bool
              local isExpandable::Bool

              isExpandable = begin
                @match ty begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, true))  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(_, true))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  TODO! check if subtype is needed here
               =#
          isExpandable
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

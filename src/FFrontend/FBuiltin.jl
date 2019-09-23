
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

module FBuiltin


using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
  #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

  MakeTypeNode = Function
MakeCompNode = Function

import Absyn

import AbsynUtil

import DAE

import Error

import SCode

import FCore
println(FCore.Seq)
import FGraph
println(FGraph.Graph)
import ClassInf

import Config

import Flags

import FGraphBuild

import Global

import ListUtil

import MetaUtil

import Parser

import AbsynToSCode
import SCodeUtil

import Settings

import System

import Util
#= /* These imports were used in e.g. MSL 1.6. They should not be here anymore...
If you need them, add them to the initial environment and recompile; they are not standard Modelica.
import arcsin = asin;
import arccos = acos;
import arctan = atan;
import ln = log;
*/ =#
#=  Predefined DAE.Types
=#
#=  Real arrays
=#

const T_REAL_ARRAY_DEFAULT = DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_UNKNOWN()))::DAE.Type

const T_REAL_ARRAY_1_DEFAULT = DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_INTEGER(1)))::DAE.Type
#=  Integer arrays
=#

const T_INT_ARRAY_1_DEFAULT = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(1)))::DAE.Type

const commonPrefixes = SCode.PREFIXES(SCode.PUBLIC(), SCode.NOT_REDECLARE(), SCode.FINAL(), Absyn.NOT_INNER_OUTER(), SCode.NOT_REPLACEABLE())::SCode.Prefixes
#=  make everything here final!
=#

const commonPrefixesNotFinal = SCode.PREFIXES(SCode.PUBLIC(), SCode.NOT_REDECLARE(), SCode.NOT_FINAL(), Absyn.NOT_INNER_OUTER(), SCode.NOT_REPLACEABLE())::SCode.Prefixes
#=  make everything here final!
=#

const attrConst = SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.CONST(), Absyn.BIDIR(), Absyn.NONFIELD())::SCode.Attributes
const attrParam = SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.PARAM(), Absyn.BIDIR(), Absyn.NONFIELD())::SCode.Attributes
const attrParamVectorNoDim = SCode.ATTR(list(Absyn.NOSUB()), SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.PARAM(), Absyn.BIDIR(), Absyn.NONFIELD())::SCode.Attributes
#=
=#
#=  The primitive types
=#
#=  These are the primitive types that are used to build the types
=#
#=  Real, Integer etc.
=#

const rlType = SCode.CLASS("RealType", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_REAL(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #=  real type  =#::SCode.Element

const intType = SCode.CLASS("IntegerType", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_INTEGER(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

const strType = SCode.CLASS("StringType", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_STRING(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

const boolType = SCode.CLASS("BooleanType", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_BOOLEAN(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

const enumType = SCode.CLASS("EnumType", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_ENUMERATION(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

const unit = SCode.COMPONENT("unit", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StringType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.STRING("")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo) #= This `unit\\' component is used in several places below, and it is
declared once here to make the definitions below easier to read. =#::SCode.Element

const quantity = SCode.COMPONENT("quantity", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StringType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.STRING("")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const displayUnit = SCode.COMPONENT("displayUnit", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StringType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.STRING("")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const min = SCode.COMPONENT("min", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("RealType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.REAL("-1e+099")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const max = SCode.COMPONENT("max", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("RealType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.REAL("1e+099")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const startOrigin = SCode.COMPONENT("startOrigin", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StringType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.STRING("undefined")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const realStart = SCode.COMPONENT("start", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("RealType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.REAL("0.0")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const integerStart = SCode.COMPONENT("start", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("IntegerType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.INTEGER(0)), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const stringStart = SCode.COMPONENT("start", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StringType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.STRING("")), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const booleanStart = SCode.COMPONENT("start", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("BooleanType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.BOOL(false)), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const fixed = SCode.COMPONENT("fixed", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("BooleanType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.BOOL(false)), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo) #= Should be true for variables =#::SCode.Element

const nominal = SCode.COMPONENT("nominal", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("RealType"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, NONE(), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const stateSelect = SCode.COMPONENT("stateSelect", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("StateSelect"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.CREF(Absyn.CREF_QUAL("StateSelect", nil, Absyn.CREF_IDENT("default", nil)))), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
#=  Extensions for uncertainties
=#

const uncertainty = SCode.COMPONENT("uncertain", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("Uncertainty"), NONE()), SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), nil, SOME(Absyn.CREF(Absyn.CREF_QUAL("Uncertainty", nil, Absyn.CREF_IDENT("given", nil)))), AbsynUtil.dummyInfo), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const distribution = SCode.COMPONENT("distribution", commonPrefixes, attrParam, Absyn.TPATH(Absyn.IDENT("Distribution"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
#=  Distribution is declared in ModelicaBuiltin.mo
=#
#=  END Extensions for uncertainties
=#

const stateSelectComps = list(SCode.COMPONENT("never", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("avoid", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("default", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("prefer", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("always", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)) #= The StateSelect enumeration =#::List

const uncertaintyComps = list(SCode.COMPONENT("given", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("sought", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), SCode.COMPONENT("refine", commonPrefixes, attrConst, Absyn.TPATH(Absyn.IDENT("EnumType"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)) #= The Uncertainty enumeration =#::List

const stateSelectType = SCode.CLASS("StateSelect", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_ENUMERATION(), SCode.PARTS(stateSelectComps, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= The SMNode Select Type =#::SCode.Element

const uncertaintyType = SCode.CLASS("Uncertainty", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_ENUMERATION(), SCode.PARTS(uncertaintyComps, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= The Uncertainty Type =#::SCode.Element

const ExternalObjectType = SCode.CLASS("ExternalObject", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_CLASS(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= ExternalObject type =#::SCode.Element
#=  The Real type
=#

const realType = SCode.CLASS("Real", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_REAL(), SCode.PARTS(list(unit, quantity, displayUnit, min, max, realStart, fixed, nominal, stateSelect, uncertainty, distribution, startOrigin), nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= - The `Real\\' type =#::SCode.Element
#=  The Integer type
=#

const integerType = SCode.CLASS("Integer", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_INTEGER(), SCode.PARTS(list(quantity, min, max, integerStart, fixed, uncertainty, distribution, startOrigin), nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= - The `Integer\\' type =#::SCode.Element
#=  The String type
=#

const stringType = SCode.CLASS("String", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_STRING(), SCode.PARTS(list(quantity, stringStart, startOrigin), nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= - The `String\\' type =#::SCode.Element
#=  The Boolean type
=#

const booleanType = SCode.CLASS("Boolean", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_BOOLEAN(), SCode.PARTS(list(quantity, booleanStart, fixed, startOrigin), nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= - The `Boolean\\' type =#::SCode.Element
#=  BTH The Clock type
=#

const clockType = SCode.CLASS("Clock", commonPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_CLOCK(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo) #= - The `Clock\\' type =#::SCode.Element
#=  The builtin variable time. See also variableIsBuiltin
=#

const timeVar = DAE.TYPES_VAR("time", DAE.dummyAttrInput, DAE.T_REAL_DEFAULT, DAE.UNBOUND(), NONE())::DAE.Var
#= /* Optimica Extensions. Theses variables are considered builtin for Optimica: startTime, finalTime, objectiveIntegrand and objective */ =#
#= /* Optimica Extensions. The builtin variable startTime. */ =#

const startTimeVar = DAE.TYPES_VAR("startTime", DAE.dummyAttrInput, DAE.T_REAL_DEFAULT, DAE.UNBOUND(), NONE()) #= - The `startTime\\' variable =#::DAE.Var
#= /* Optimica Extensions. The builtin variable finalTime. */ =#

const finalTimeVar = DAE.TYPES_VAR("finalTime", DAE.dummyAttrInput, DAE.T_REAL_DEFAULT, DAE.UNBOUND(), NONE()) #= - The `finalTime\\' variable =#::DAE.Var
#= /* Optimica Extensions. The builtin variable objectiveIntegrand. */ =#

const objectiveIntegrandVar = DAE.TYPES_VAR("objectiveIntegrand", DAE.dummyAttrInput, DAE.T_REAL_DEFAULT, DAE.UNBOUND(), NONE()) #= - The `objectiveIntegrand\\' variable =#::DAE.Var
#= /* Optimica Extensions. The builtin variable objective. */ =#

const objectiveVar = DAE.TYPES_VAR("objective", DAE.dummyAttrInput, DAE.T_REAL_DEFAULT, DAE.UNBOUND(), NONE()) #= - The `objective\\' variable =#::DAE.Var

const argRealX = DAE.FUNCARG("x", DAE.T_REAL_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())::DAE.FuncArg

const argRealY = DAE.FUNCARG("y", DAE.T_REAL_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())::DAE.FuncArg

const argRealZ = DAE.FUNCARG("z", DAE.T_REAL_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())::DAE.FuncArg

const argsRealX = list(argRealX)::List

const argsRealXY = list(argRealX, argRealY)::List

const argsRealXYZ = list(argRealX, argRealY, argRealZ)::List

const timeComp = SCode.COMPONENT("time", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.INPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT("Real"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const startTimeComp = SCode.COMPONENT("startTime", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.INPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT("Real"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const finalTimeComp = SCode.COMPONENT("finalTime", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.INPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT("Real"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const objectiveIntegrandComp = SCode.COMPONENT("objectiveIntegrand", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.INPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT("Real"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const objectiveVarComp = SCode.COMPONENT("objectiveVar", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.INPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT("Real"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

const basicTypes = list(clockType, rlType, intType, strType, boolType, enumType, ExternalObjectType, realType, integerType, stringType, booleanType, uncertaintyType)::List

const basicTypesNF = list(clockType, rlType, intType, strType, boolType, enumType, realType, integerType, stringType, booleanType, uncertaintyType)::List

function getBasicTypes() ::List{SCode.Element}
  local tys::List{SCode.Element}

  tys = if Flags.isSet(Flags.SCODE_INST)
    basicTypesNF
  else
    basicTypes
  end
  tys
end

#= Returns true if cref is a builtin variable.
Currently only 'time' is a builtin variable. =#
function variableIsBuiltin(cref::DAE.ComponentRef, useOptimica::Bool) ::Bool
  local b::Bool

  b = begin
    @match (cref, useOptimica) begin
      (DAE.CREF_IDENT(ident = "time"), _)  => begin
        true
      end

      (_, false)  => begin
        false
      end

      (DAE.CREF_IDENT(ident = "startTime"), true)  => begin
        true
      end

      (DAE.CREF_IDENT(ident = "finalTime"), true)  => begin
        true
      end

      (DAE.CREF_IDENT(ident = "objective"), true)  => begin
        true
      end

      (DAE.CREF_IDENT(ident = "objectiveIntegrand"), true)  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  #= If accepting Optimica then these variabels are also builtin
  =#
  b
end

function isDer(inPath::Absyn.Path)
  _ = begin
    local path::Absyn.Path
    @match inPath begin
      Absyn.IDENT(name = "der")  => begin
        ()
      end

      Absyn.FULLYQUALIFIED(path)  => begin
        isDer(path)
        ()
      end
    end
  end
end

#= Fetches the Absyn.Program representation of the functions (and other classes) in the initial environment =#
function getInitialFunctions() ::Tuple{Absyn.Program, SCode.Program}
  local initialSCodeProgram::SCode.Program
  local initialProgram::Absyn.Program

  #=  legend: NF = new frontend; CF = current frontend
  =#
  local fileModelicaNF::String
  local fileModelicaCF::String
  local fileMetaModelica::String
  local fileParModelica::String
  local filePDEModelica::String
  local assocLst::List{Tuple{Tuple{ModelicaInteger, Bool}, Tuple{Absyn.Program, SCode.Program}}}
  local classesNF::List{Absyn.Class}
  local classesCF::List{Absyn.Class}
  local classes1NF::List{Absyn.Class}
  local classes1CF::List{Absyn.Class}
  local classes2::List{Absyn.Class}
  local p::Absyn.Program
  local pNF::Absyn.Program
  local pCF::Absyn.Program
  local sp::SCode.Program
  local spNF::SCode.Program
  local spCF::SCode.Program

  fileModelicaNF = Settings.getInstallationDirectoryPath() + "/lib/omc/NFModelicaBuiltin.mo"
  fileModelicaCF = Settings.getInstallationDirectoryPath() + "/lib/omc/ModelicaBuiltin.mo"
  fileMetaModelica = Settings.getInstallationDirectoryPath() + "/lib/omc/MetaModelicaBuiltin.mo"
  fileParModelica = Settings.getInstallationDirectoryPath() + "/lib/omc/ParModelicaBuiltin.mo"
  filePDEModelica = Settings.getInstallationDirectoryPath() + "/lib/omc/PDEModelicaBuiltin.mo"
  (initialProgram, initialSCodeProgram) = begin
    @matchcontinue () begin
      ()  => begin
        @shouldFail _ = getGlobalRoot(Global.builtinIndex)
        setGlobalRoot(Global.builtinIndex, nil)
        fail()
      end

      ()  => begin
        assocLst = getGlobalRoot(Global.builtinIndex)
        (p, sp) = Util.assoc(Util.makeTuple(Flags.getConfigEnum(Flags.GRAMMAR), Flags.isSet(Flags.SCODE_INST)), assocLst)
        (p, sp)
      end

      ()  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.METAMODELICA)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaNF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaNF), AbsynUtil.dummyInfo)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaCF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaCF), AbsynUtil.dummyInfo)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileMetaModelica), Error.FILE_NOT_FOUND_ERROR, list(fileMetaModelica), AbsynUtil.dummyInfo)
        @match Absyn.PROGRAM(classes = classes1NF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaNF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        @match Absyn.PROGRAM(classes = classes1CF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaCF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        @match Absyn.PROGRAM(classes = classes2, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileMetaModelica, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        classesNF = listAppend(classes1NF, classes2)
        classesCF = listAppend(classes1CF, classes2)
        pNF = Absyn.PROGRAM(classesNF, Absyn.TOP())
        pCF = Absyn.PROGRAM(classesCF, Absyn.TOP())
        @match (@match Absyn.PROGRAM(classes = classesNF) = pNF) = MetaUtil.createMetaClassesInProgram(pNF)
        @match (@match Absyn.PROGRAM(classes = classesCF) = pCF) = MetaUtil.createMetaClassesInProgram(pCF)
        spNF = ListUtil.map(classesNF, AbsynToSCode.translateClass)
        spCF = ListUtil.map(classesCF, AbsynToSCode.translateClass)
        assocLst = getGlobalRoot(Global.builtinIndex)
        setGlobalRoot(Global.builtinIndex, _cons(((Flags.METAMODELICA, true), (pNF, spNF)), _cons(((Flags.METAMODELICA, false), (pCF, spCF)), assocLst)))
        (p, sp) = if Flags.isSet(Flags.SCODE_INST)
          (pNF, spNF)
        else
          (pCF, spCF)
        end
        (p, sp)
      end

      ()  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PARMODELICA)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaNF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaNF), AbsynUtil.dummyInfo)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaCF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaCF), AbsynUtil.dummyInfo)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileMetaModelica), Error.FILE_NOT_FOUND_ERROR, list(fileMetaModelica), AbsynUtil.dummyInfo)
        @match Absyn.PROGRAM(classes = classes1NF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaNF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        @match Absyn.PROGRAM(classes = classes1CF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaCF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        @match Absyn.PROGRAM(classes = classes2, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileParModelica, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        classesNF = listAppend(classes1NF, classes2)
        classesCF = listAppend(classes1CF, classes2)
        pNF = Absyn.PROGRAM(classesNF, Absyn.TOP())
        pCF = Absyn.PROGRAM(classesCF, Absyn.TOP())
        spNF = ListUtil.map(classesNF, AbsynToSCode.translateClass)
        spCF = ListUtil.map(classesCF, AbsynToSCode.translateClass)
        assocLst = getGlobalRoot(Global.builtinIndex)
        setGlobalRoot(Global.builtinIndex, _cons(((Flags.PARMODELICA, true), (pNF, spNF)), _cons(((Flags.PARMODELICA, false), (pCF, spCF)), assocLst)))
        (p, sp) = if Flags.isSet(Flags.SCODE_INST)
          (pNF, spNF)
        else
          (pCF, spCF)
        end
        (p, sp)
      end

      ()  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.MODELICA) || intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.OPTIMICA)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaNF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaNF), AbsynUtil.dummyInfo)
        Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaCF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaCF), AbsynUtil.dummyInfo)
        @match (@match Absyn.PROGRAM(classes = classes1NF, within_ = Absyn.TOP()) = pNF) = Parser.parsebuiltin(fileModelicaNF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        @match (@match Absyn.PROGRAM(classes = classes1CF, within_ = Absyn.TOP()) = pCF) = Parser.parsebuiltin(fileModelicaCF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
        spNF = ListUtil.map(classes1NF, AbsynToSCode.translateClass)
        spCF = ListUtil.map(classes1CF, AbsynToSCode.translateClass)
        assocLst = getGlobalRoot(Global.builtinIndex)
        setGlobalRoot(Global.builtinIndex, _cons(((Flags.MODELICA, true), (pNF, spNF)), _cons(((Flags.MODELICA, false), (pCF, spCF)), assocLst)))
        (p, sp) = if Flags.isSet(Flags.SCODE_INST)
          (pNF, spNF)
        else
          (pCF, spCF)
        end
        (p, sp)
      end

()  => begin
  @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
  Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaNF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaNF), AbsynUtil.dummyInfo)
  Error.assertionOrAddSourceMessage(System.regularFileExists(fileModelicaCF), Error.FILE_NOT_FOUND_ERROR, list(fileModelicaCF), AbsynUtil.dummyInfo)
  Error.assertionOrAddSourceMessage(System.regularFileExists(filePDEModelica), Error.FILE_NOT_FOUND_ERROR, list(filePDEModelica), AbsynUtil.dummyInfo)
  @match Absyn.PROGRAM(classes = classes1NF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaNF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
  @match Absyn.PROGRAM(classes = classes1CF, within_ = Absyn.TOP()) = Parser.parsebuiltin(fileModelicaCF, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
  @match Absyn.PROGRAM(classes = classes2, within_ = Absyn.TOP()) = Parser.parsebuiltin(filePDEModelica, "UTF-8", "", NONE(), acceptedGram = Flags.METAMODELICA)
  classesNF = listAppend(classes1NF, classes2)
  classesCF = listAppend(classes1CF, classes2)
  pNF = Absyn.PROGRAM(classesNF, Absyn.TOP())
  pCF = Absyn.PROGRAM(classesCF, Absyn.TOP())
  spNF = ListUtil.map(classesNF, AbsynToSCode.translateClass)
  spCF = ListUtil.map(classesCF, AbsynToSCode.translateClass)
  assocLst = getGlobalRoot(Global.builtinIndex)
  setGlobalRoot(Global.builtinIndex, _cons(((Flags.PDEMODELICA, true), (pNF, spNF)), _cons(((Flags.PDEMODELICA, false), (pCF, spCF)), assocLst)))
  (p, sp) = if Flags.isSet(Flags.SCODE_INST)
    (pNF, spNF)
  else
    (pCF, spCF)
  end
  (p, sp)
end

_  => begin
  Error.addInternalError("FBuiltin.getInitialFunctions failed.", sourceInfo())
  fail()
end
end
end
(initialProgram, initialSCodeProgram)
end

#= The initial environment where instantiation takes place is built
up using this function.  It creates an empty environment and adds
all the built-in definitions to it.
NOTE:
The following built in operators can not be described in
the type system, since they e.g. have arbitrary arguments, etc.
- fill
- cat
These operators are catched in the elabBuiltinHandler, along with all
others. =#
function initialGraph(inCache::FCore.Cache) ::Tuple{FCore.Cache, FGraph.Graph}
  local graph::FGraph.Graph
  local outCache::FCore.Cache

  local cache::FCore.Cache

  (outCache, graph) = begin
    local initialClasses::List{Absyn.Class}
    local initialProgram::SCode.Program
    local types::List{SCode.Element}
    #=  First look for cached version
    =#
    @matchcontinue inCache begin
      cache  => begin
        graph = FCoreUtil.getCachedInitialGraph(cache)
        (cache, graph)
      end

      cache  => begin
        graph = getSetInitialGraph(NONE())
        (cache, graph)
      end

      cache  => begin
        graph = FGraph.new("graph", FCore.dummyTopModel)
        graph = FGraphBuild.mkProgramGraph(basicTypes, FCore.BASIC_TYPE(), graph)
        graph = initialGraphOptimica(graph, FGraphBuild.mkCompNode)
        graph = initialGraphMetaModelica(graph, FGraphBuild.mkTypeNode)
        graph = initialGraphModelica(graph, FGraphBuild.mkTypeNode, FGraphBuild.mkCompNode)
        (_, initialProgram) = getInitialFunctions()
        graph = FGraphBuild.mkProgramGraph(initialProgram, FCore.BUILTIN(), graph)
        cache = FCore.setCachedInitialGraph(cache, graph)
        _ = getSetInitialGraph(SOME(graph))
        (cache, graph)
      end
    end
  end
  #=  then look in the global roots[builtinEnvIndex]
  =#
  #=  if no cached version found create initial graph.
  =#
  #=  add the ModelicaBuiltin/MetaModelicaBuiltin classes in the initial graph
  =#
  (outCache, graph)
end

#= gets/sets the initial environment depending on grammar flags =#
function getSetInitialGraph(inEnvOpt::Option{<:FGraph.Graph})::FGraph.Graph
  local initialEnv::FGraph.Graph

  initialEnv = begin
    local assocLst::List{Tuple{ModelicaInteger, FGraph.Graph}}
    local graph::FGraph.Graph

    @matchcontinue inEnvOpt begin
      _  => begin
        @shouldFail _ = getGlobalRoot(Global.builtinGraphIndex)
        setGlobalRoot(Global.builtinGraphIndex, nil)
        fail()
      end

      NONE()  => begin
        assocLst = getGlobalRoot(Global.builtinGraphIndex)
        Util.assoc(Flags.getConfigEnum(Flags.GRAMMAR), assocLst)
      end

      SOME(graph)  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.METAMODELICA)
        assocLst = getGlobalRoot(Global.builtinGraphIndex)
        setGlobalRoot(Global.builtinGraphIndex, _cons((Flags.METAMODELICA, graph), assocLst))
        graph
      end

      SOME(graph)  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PARMODELICA)
        assocLst = getGlobalRoot(Global.builtinGraphIndex)
        setGlobalRoot(Global.builtinGraphIndex, _cons((Flags.PARMODELICA, graph), assocLst))
        graph
      end

      SOME(graph)  => begin
        @match true = intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.MODELICA) || intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.OPTIMICA)
        assocLst = getGlobalRoot(Global.builtinGraphIndex)
        setGlobalRoot(Global.builtinGraphIndex, _cons((Flags.MODELICA, graph), assocLst))
        graph
      end
    end
  end
  #=  return the correct graph depending on flags
  =#
  initialEnv
end





function initialGraphModelica(graph::FGraph.Graph, mkTypeNode::MakeTypeNode, mkCompNode::MakeCompNode) ::FGraph.Graph


  local enumeration2int::DAE.Type = DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ENUMERATION(NONE(), Absyn.IDENT(""), nil, nil, nil), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("Integer"))

  graph = mkCompNode(timeComp, FGraph.top(graph), FCore.BUILTIN(), graph)
  graph = FGraph.updateComp(graph, timeVar, FCore.VAR_UNTYPED(), FGraph.empty())
  graph = mkTypeNode(list(DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE(SOME(ClassInf.CONNECTOR(Absyn.IDENT("dummy"), false))), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("cardinality")), DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE(SOME(ClassInf.CONNECTOR(Absyn.IDENT("dummy"), true))), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("cardinality"))), FGraph.top(graph), "cardinality", graph)
  graph = mkTypeNode(list(enumeration2int), FGraph.top(graph), "Integer", graph)
  graph = mkTypeNode(list(enumeration2int), FGraph.top(graph), "EnumToInteger", graph)
  graph = mkTypeNode(list(DAE.T_FUNCTION(argsRealX, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("noEvent"))), FGraph.top(graph), "noEvent", graph)
  graph = mkTypeNode(list(DAE.T_FUNCTION(argsRealX, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("actualStream"))), FGraph.top(graph), "actualStream", graph)
  graph = mkTypeNode(list(DAE.T_FUNCTION(argsRealX, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("inStream"))), FGraph.top(graph), "inStream", graph)
  graph = mkTypeNode(list(DAE.T_FUNCTION(argsRealXYZ, DAE.T_REAL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("constrain")), DAE.T_FUNCTION(list(DAE.FUNCARG("x", T_REAL_ARRAY_1_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("y", T_REAL_ARRAY_1_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("z", T_REAL_ARRAY_1_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), T_REAL_ARRAY_1_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("constrain"))), FGraph.top(graph), "constrain", graph)
  graph
end

function initialGraphMetaModelica(graph::FGraph.Graph, mkTypeNode::MakeTypeNode) ::FGraph.Graph


  if ! Config.acceptMetaModelicaGrammar()
    return graph
  end
  #=  getGlobalRoot can not be represented by a regular function...
  =#
  graph = mkTypeNode(list(DAE.T_FUNCTION(list(DAE.FUNCARG("index", DAE.T_INTEGER_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_METABOXED_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("getGlobalRoot"))), FGraph.top(graph), "getGlobalRoot", graph)
  graph
end

function initialGraphOptimica(graph::FGraph.Graph, mkCompNode::MakeCompNode) ::FGraph.Graph


  if ! Config.acceptOptimicaGrammar()
    return graph
  end
  #= If Optimica add the startTime,finalTime,objectiveIntegrand and objective \"builtin\" variables.
  =#
  graph = mkCompNode(objectiveVarComp, FGraph.top(graph), FCore.BUILTIN(), graph)
  graph = FGraph.updateComp(graph, objectiveVar, FCore.VAR_UNTYPED(), FGraph.empty())
  graph = mkCompNode(objectiveIntegrandComp, FGraph.top(graph), FCore.BUILTIN(), graph)
  graph = FGraph.updateComp(graph, objectiveIntegrandVar, FCore.VAR_UNTYPED(), FGraph.empty())
  graph = mkCompNode(startTimeComp, FGraph.top(graph), FCore.BUILTIN(), graph)
  graph = FGraph.updateComp(graph, startTimeVar, FCore.VAR_UNTYPED(), FGraph.empty())
  graph = mkCompNode(finalTimeComp, FGraph.top(graph), FCore.BUILTIN(), graph)
  graph = FGraph.updateComp(graph, finalTimeVar, FCore.VAR_UNTYPED(), FGraph.empty())
  graph
end

#= returns the element from the program having the name as the id.
if the element does not exist it fails =#
function getElementWithPathCheckBuiltin(inProgram::SCode.Program, inPath::Absyn.Path) ::SCode.Element
  local outElement::SCode.Element

  outElement = begin
    local sp::SCode.Program
    local rest::SCode.Program
    local c::SCode.Element
    local e::SCode.Element
    local p::Absyn.Path
    local i::Absyn.Ident
    local n::Absyn.Ident
    @matchcontinue (inProgram, inPath) begin
      (_, _)  => begin
        SCodeUtil.getElementWithPath(inProgram, inPath)
      end

      _  => begin
        (_, sp) = FBuiltin.getInitialFunctions()
        SCodeUtil.getElementWithPath(sp, inPath)
      end
    end
  end
  outElement
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

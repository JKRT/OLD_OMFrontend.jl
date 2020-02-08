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

module NFSCodeEnv

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
  #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

@UniontypeDecl ImportTable
@UniontypeDecl Redeclaration
@UniontypeDecl Extends
@UniontypeDecl ExtendsTable
@UniontypeDecl FrameType
@UniontypeDecl Frame
@UniontypeDecl ClassType
@UniontypeDecl Item


import Absyn
import AbsynUtil
import Mutable
import SCode
import Util

import Error
import FBuiltin
import ListUtil
import SCodeDump
import NFEnvExtends
import NFSCodeFlattenRedeclare
import NFSCodeLookup
import NFSCodeCheck
import AbsynToSCode
import SCodeUtil
import System

MutableType = Mutable.MutableType

Import = Absyn.Import
  const tmpTickIndex = 2::ModelicaInteger
const extendsTickIndex = 3::ModelicaInteger

@Uniontype ImportTable begin
  @Record IMPORT_TABLE begin

    #=  Imports should not be inherited, but removing them from the environment
    =#
    #=  when doing lookup through extends causes problems for the lookup later
    =#
    #=  on, because for example components may have types that depends on
    =#
    #=  imports.  The hidden flag allows the lookup to 'hide' the imports
    =#
    #=  temporarily, without actually removing them.
    =#
    hidden #= If true means that the imports are hidden. =#::Bool
    qualifiedImports::List{Import}
    unqualifiedImports::List{Import}
  end
end

#= This uniontype stores a redeclare modifier (which might be derived from an
element redeclare). The RAW_MODIFIER stores a 'raw' modifier, i.e. the raw
element stored in the SCode representation. These are processed when they are
used, i.e. when replacements are done, and converted into PROCESSED_MODIFIERs
which are environment items ready to be replaced in the environment. =#
@Uniontype Redeclaration begin
  @Record RAW_MODIFIER begin

    modifier::SCode.Element
  end

  @Record PROCESSED_MODIFIER begin

    modifier::Item
  end
end

@Uniontype Extends begin
  @Record EXTENDS begin

    baseClass::Absyn.Path
    redeclareModifiers::List{Redeclaration}
    index::ModelicaInteger
    info::SourceInfo
  end
end

@Uniontype ExtendsTable begin
  @Record EXTENDS_TABLE begin

    baseClasses::List{Extends}
    redeclaredElements::List{SCode.Element}
    classExtendsInfo::Option{SCode.Element}
  end
end

@Uniontype FrameType begin
  @Record NORMAL_SCOPE begin

  end

  @Record ENCAPSULATED_SCOPE begin

  end

  @Record IMPLICIT_SCOPE begin

    iterIndex::ModelicaInteger
  end
end

@Uniontype Frame begin
  @Record FRAME begin

    name::Option{String}
    frameType::FrameType
    clsAndVars::EnvTree.Tree
    extendsTable::ExtendsTable
    importTable::ImportTable
  isUsed #= Used by SCodeDependency. =#::Option{MutableType #= {Bool} =#}
  end
end

@Uniontype ClassType begin
  @Record USERDEFINED begin

  end

  @Record BUILTIN begin

  end

  @Record CLASS_EXTENDS begin

  end

  @Record BASIC_TYPE begin

  end
end

@Uniontype Item begin
  @Record VAR begin

    var::SCode.Element
    isUsed #= Used by SCodeDependency. =#::Option{MutableType #= {Bool} =#}
  end

  @Record CLASS begin

    cls::SCode.Element
    env::Env
    classType::ClassType
  end

  @Record ALIAS begin

    name::String
    path::Option{Absyn.Path}
    info::SourceInfo
  end

  @Record REDECLARED_ITEM begin

    item::Item
    declaredEnv::Env
  end
end

module EnvTree


using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

  import BaseAvlTree
import NFSCodeEnv.Item
using BaseAvlTree
Key = String
Value = Item
addConflictDefault = addConflictReplace
@exportAll()
end

const Env = List

const emptyEnv = nil::Env

const BASE_CLASS_SUFFIX = "base"::String

#= Returns a new environment with only one frame. =#
function newEnvironment(inName::Option{<:SCode.Ident}) ::Env
  local outEnv::Env

  local new_frame::Frame

  new_frame = newFrame(inName, NORMAL_SCOPE())
  outEnv = list(new_frame)
  outEnv
end

#= Open a new class scope in the environment by adding a new frame for the given
class. =#
function openScope(inEnv::Env, inClass::SCode.Element) ::Env
  local outEnv::Env

  local name::String
  local encapsulatedPrefix::SCode.Encapsulated
  local new_frame::Frame

  @match SCode.CLASS(name = name, encapsulatedPrefix = encapsulatedPrefix) = inClass
  new_frame = newFrame(SOME(name), getFrameType(encapsulatedPrefix))
  outEnv = _cons(new_frame, inEnv)
  outEnv
end

#= Enters a new scope in the environment by looking up an item in the
environment and appending it's frame to the environment. =#
function enterScope(inEnv::Env, inName::SCode.Ident) ::Env
  local outEnv::Env

  outEnv = begin
    local cls_env::Frame
    local item::Item
    @matchcontinue (inEnv, inName) begin
      (_, _)  => begin
        (item, _) = NFSCodeLookup.lookupInClass(inName, inEnv)
        @match cls_env <| nil = getItemEnv(item)
        outEnv = enterFrame(cls_env, inEnv)
        outEnv
      end

      (_, _)  => begin
        print("Failed to enterScope: " + inName + " in env: " + printEnvStr(inEnv) + "\\n")
        fail()
      end
    end
  end
  #= /*********************************************************************/ =#
  #=  TODO: Should we use the environment returned by lookupInClass?
  =#
  #= /*********************************************************************/ =#
  outEnv
end

function enterScopePath(inEnv::Env, inPath::Absyn.Path) ::Env
  local outEnv::Env

  outEnv = begin
    local name::Absyn.Ident
    local path::Absyn.Path
    local env::Env
    @match (inEnv, inPath) begin
      (_, Absyn.QUALIFIED(name = name, path = path))  => begin
        env = enterScope(inEnv, name)
        enterScopePath(env, path)
      end

      (_, Absyn.IDENT(name = name))  => begin
        enterScope(inEnv, name)
      end

      (_, Absyn.FULLYQUALIFIED(path = path))  => begin
        env = getEnvTopScope(inEnv)
        enterScopePath(env, path)
      end
    end
  end
  outEnv
end

function enterFrame(inFrame::Frame, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = _cons(inFrame, inEnv)
  outEnv
end

#= Returns the top scope, i.e. last frame in the environment. =#
function getEnvTopScope(inEnv::Env) ::Env
  local outEnv::Env

  local top_scope::Frame
  local env::Env

  env = listReverse(inEnv)
  @match _cons(top_scope, _) = env
  outEnv = list(top_scope)
  outEnv
end

#= Returns a new FrameType given if the frame should be encapsulated or not. =#
function getFrameType(encapsulatedPrefix::SCode.Encapsulated) ::FrameType
  local outType::FrameType

  outType = begin
    @match encapsulatedPrefix begin
      SCode.ENCAPSULATED(__)  => begin
        ENCAPSULATED_SCOPE()
      end

      _  => begin
        NORMAL_SCOPE()
      end
    end
  end
  outType
end

#= Creates a new frame with an optional name and a frame type. =#
function newFrame(inName::Option{<:String}, inType::FrameType) ::Frame
  local outFrame::Frame

  local tree::EnvTree.Tree
  local exts::ExtendsTable
  local imps::ImportTable
  local is_used::MutableType #= {Bool} =#

  tree = EnvTree.new()
  exts = newExtendsTable()
  imps = newImportTable()
  is_used = Mutable.create(false)
  outFrame = FRAME(inName, inType, tree, exts, imps, SOME(is_used))
  outFrame
end

#= Creates a new import table. =#
function newImportTable() ::ImportTable
  local outImports::ImportTable

  outImports = IMPORT_TABLE(false, nil, nil)
  outImports
end

#= Creates a new extends table. =#
function newExtendsTable() ::ExtendsTable
  local outExtends::ExtendsTable

  outExtends = EXTENDS_TABLE(nil, nil, NONE())
  outExtends
end

function newItem(inElement::SCode.Element) ::Item
  local outItem::Item

  outItem = begin
    local class_env::Env
    local item::Item
    @match inElement begin
      SCode.CLASS(__)  => begin
        class_env = makeClassEnvironment(inElement, true)
        item = newClassItem(inElement, class_env, USERDEFINED())
        item
      end

      SCode.COMPONENT(__)  => begin
        newVarItem(inElement, false)
      end
    end
  end
  outItem
end

#= Creates a new class environment item. =#
function newClassItem(inClass::SCode.Element, inEnv::Env, inClassType::ClassType) ::Item
  local outClassItem::Item

  outClassItem = CLASS(inClass, inEnv, inClassType)
  outClassItem
end

#= Creates a new variable environment item. =#
function newVarItem(inVar::SCode.Element, inIsUsed::Bool) ::Item
  local outVarItem::Item

  local is_used::MutableType #= {Bool} =#

  is_used = Mutable.create(inIsUsed)
  outVarItem = VAR(inVar, SOME(is_used))
  outVarItem
end

#= Extends the environment with a list of classes. =#
function extendEnvWithClasses(inClasses::List{<:SCode.Element}, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = ListUtil.fold(inClasses, extendEnvWithClass, inEnv)
  outEnv
end

#= Extends the environment with a class. =#
function extendEnvWithClass(inClass::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = extendEnvWithClassDef(inClass, inEnv)
  outEnv
end

#= Returns a class's type. =#
function getClassType(inClassDef::SCode.ClassDef) ::ClassType
  local outType::ClassType

  outType = begin
    @match inClassDef begin
      SCode.PARTS(externalDecl = SOME(SCode.EXTERNALDECL(lang = SOME("builtin"))))  => begin
        BUILTIN()
      end

      _  => begin
        USERDEFINED()
      end
    end
  end
  #=  A builtin class.
  =#
  #=  A user-defined class (i.e. not builtin).
  =#
  outType
end

function printClassType(inClassType::ClassType) ::String
  local outString::String

  outString = begin
    @match inClassType begin
      BUILTIN(__)  => begin
        "BUILTIN"
      end

      CLASS_EXTENDS(__)  => begin
        "CLASS_EXTENDS"
      end

      USERDEFINED(__)  => begin
        "USERDEFINED"
      end

      BASIC_TYPE(__)  => begin
        "BASIC_TYPE"
      end
    end
  end
  outString
end

#= Removes all extends from the local scope, i.e. inserts a new empty
extends-table into the first frame. =#
function removeExtendsFromLocalScope(inEnv::Env) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local exts::ExtendsTable
  local rest::Env
  local is_used::Option{MutableType #= {Bool} =#}

  @match _cons(FRAME(name = name, frameType = ty, clsAndVars = tree, importTable = imps, isUsed = is_used), rest) = inEnv
  exts = newExtendsTable()
  outEnv = _cons(FRAME(name, ty, tree, exts, imps, is_used), rest)
  outEnv
end

#= Removes a given extends clause from the local scope. =#
function removeExtendFromLocalScope(inExtend::Absyn.Path, inEnv::Env) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local rest::Env
  local iu::Option{MutableType #= {Bool} =#}
  local bcl::List{Extends}
  local re::List{SCode.Element}
  local cei::Option{SCode.Element}

  @match _cons(FRAME(name = name, frameType = ty, clsAndVars = tree, extendsTable = EXTENDS_TABLE(baseClasses = bcl, redeclaredElements = re, classExtendsInfo = cei), importTable = imps, isUsed = iu), rest) = inEnv
  (bcl, _) = ListUtil.deleteMemberOnTrue(inExtend, bcl, isExtendNamed)
  outEnv = _cons(FRAME(name, ty, tree, EXTENDS_TABLE(bcl, re, cei), imps, iu), rest)
  outEnv
end

function isExtendNamed(inName::Absyn.Path, inExtends::Extends) ::Bool
  local outIsNamed::Bool

  local bc::Absyn.Path

  @match EXTENDS(baseClass = bc) = inExtends
  outIsNamed = AbsynUtil.pathEqual(inName, bc)
  outIsNamed
end

function removeRedeclaresFromLocalScope(inEnv::Env) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local exts::ExtendsTable
  local rest::Env
  local is_used::Option{MutableType #= {Bool} =#}
  local bc::List{Extends}
  local cei::Option{SCode.Element}

  @match _cons(FRAME(name = name, frameType = ty, clsAndVars = tree, extendsTable = EXTENDS_TABLE(baseClasses = bc, classExtendsInfo = cei), importTable = imps, isUsed = is_used), rest) = inEnv
  bc = ListUtil.map(bc, removeRedeclaresFromExtend)
  exts = EXTENDS_TABLE(bc, nil, cei)
  outEnv = _cons(FRAME(name, ty, tree, exts, imps, is_used), rest)
  outEnv
end

function removeRedeclaresFromExtend(inExtend::Extends) ::Extends
  local outExtend::Extends

  local bc::Absyn.Path
  local index::ModelicaInteger
  local info::SourceInfo

  @match EXTENDS(bc, _, index, info) = inExtend
  outExtend = EXTENDS(bc, nil, index, info)
  outExtend
end

#= Removes the classes variables from a frame. =#
function removeClsAndVarsFromFrame(inFrame::Frame) ::Tuple{Frame, EnvTree.Tree}
  local outClsAndVars::EnvTree.Tree
  local outFrame::Frame

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local exts::ExtendsTable
  local is_used::Option{MutableType #= {Bool} =#}

  @match FRAME(name = name, frameType = ty, clsAndVars = outClsAndVars, extendsTable = exts, importTable = imps, isUsed = is_used) = inFrame
  tree = EnvTree.new()
  outFrame = FRAME(name, ty, tree, exts, imps, is_used)
  (outFrame, outClsAndVars)
end

#= Sets the 'hidden' flag in the import table in the local scope of the given
environment. =#
function setImportTableHidden(inEnv::Env, inHidden::Bool) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local exts::ExtendsTable
  local rest::Env
  local qi::List{Import}
  local uqi::List{Import}
  local is_used::Option{MutableType #= {Bool} =#}

  @match _cons(FRAME(name = name, frameType = ty, clsAndVars = tree, extendsTable = exts, importTable = IMPORT_TABLE(qualifiedImports = qi, unqualifiedImports = uqi), isUsed = is_used), rest) = inEnv
  outEnv = _cons(FRAME(name, ty, tree, exts, IMPORT_TABLE(inHidden, qi, uqi), is_used), rest)
  outEnv
end

#= Sets the 'hidden' flag in the import table for the given items environment if
the item is a class. Otherwise does nothing. =#
function setImportsInItemHidden(inItem::Item, inHidden::Bool) ::Item
  local outItem::Item

  outItem = begin
    local cls::SCode.Element
    local env::Env
    local cls_ty::ClassType
    @match (inItem, inHidden) begin
      (CLASS(cls = cls, env = env, classType = cls_ty), _)  => begin
        env = setImportTableHidden(env, inHidden)
        CLASS(cls, env, cls_ty)
      end

      _  => begin
        inItem
      end
    end
  end
  outItem
end

#= Checks if an item is used or not. =#
function isItemUsed(inItem::Item) ::Bool
  local isUsed::Bool

  isUsed = begin
    local is_used::MutableType #= {Bool} =#
    local item::Item
    @match inItem begin
      CLASS(env = FRAME(isUsed = SOME(is_used)) <|  nil())  => begin
        Mutable.access(is_used)
      end

      VAR(isUsed = SOME(is_used))  => begin
        Mutable.access(is_used)
      end

      ALIAS(__)  => begin
        true
      end

      REDECLARED_ITEM(item = item)  => begin
        isItemUsed(item)
      end

      _  => begin
        false
      end
    end
  end
  isUsed
end

#= 'Links' two items to each other, by making them share the same isUsed
variable. =#
function linkItemUsage(inSrcItem::Item, inDestItem::Item) ::Item
  local outDestItem::Item

  outDestItem = begin
    local is_used::Option{MutableType #= {Bool} =#}
    local elem::SCode.Element
    local cls_ty::ClassType
    local name::Option{String}
    local ft::FrameType
    local cv::EnvTree.Tree
    local exts::ExtendsTable
    local imps::ImportTable
  local item::Item
    local env::Env
    @match (inSrcItem, inDestItem) begin
      (VAR(isUsed = is_used), VAR(var = elem))  => begin
        VAR(elem, is_used)
      end

      (CLASS(env = FRAME(isUsed = is_used) <|  nil()), CLASS(cls = elem, classType = cls_ty, env = FRAME(name, ft, cv, exts, imps, _) <|  nil()))  => begin
        CLASS(elem, list(FRAME(name, ft, cv, exts, imps, is_used)), cls_ty)
      end

      (_, REDECLARED_ITEM(item, env))  => begin
        item = linkItemUsage(inSrcItem, item)
        REDECLARED_ITEM(item, env)
      end

      _  => begin
        inDestItem
      end
    end
  end
  outDestItem
end

function isClassItem(inItem::Item) ::Bool
  local outIsClass::Bool

  outIsClass = begin
    local item::Item
    @match inItem begin
      CLASS(__)  => begin
        true
      end

      REDECLARED_ITEM(item = item)  => begin
        isClassItem(item)
      end

      _  => begin
        false
      end
    end
  end
  outIsClass
end

function isVarItem(inItem::Item) ::Bool
  local outIsVar::Bool

  outIsVar = begin
    local item::Item
    @match inItem begin
      VAR(__)  => begin
        true
      end

      REDECLARED_ITEM(item = item)  => begin
        isVarItem(item)
      end

      _  => begin
        false
      end
    end
  end
  outIsVar
end

function isClassExtendsItem(inItem::Item) ::Bool
  local outIsClassExtends::Bool

  outIsClassExtends = begin
    local item::Item
    @match inItem begin
      CLASS(classType = CLASS_EXTENDS(__))  => begin
        true
      end

      REDECLARED_ITEM(item = item)  => begin
        isClassExtendsItem(item)
      end

      _  => begin
        false
      end
    end
  end
  outIsClassExtends
end

#= Extends the environment with a class definition. =#
function extendEnvWithClassDef(inClassDefElement::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local cls_name::String
    local alias_name::String
    local class_env::Env
    local env::Env
    local cdef::SCode.ClassDef
    local cls_type::ClassType
    local info::SourceInfo
    #=  A class extends.
    =#
    @match (inClassDefElement, inEnv) begin
      (SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)), _)  => begin
        NFEnvExtends.extendEnvWithClassExtends(inClassDefElement, inEnv)
      end

      (SCode.CLASS(name = cls_name, classDef = cdef, prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_)), info = info), _)  => begin
        class_env = makeClassEnvironment(inClassDefElement, false)
        cls_type = getClassType(cdef)
        alias_name = cls_name + BASE_CLASS_SUFFIX
        env = extendEnvWithItem(newClassItem(inClassDefElement, class_env, cls_type), inEnv, alias_name)
        env = extendEnvWithItem(ALIAS(alias_name, NONE(), info), env, cls_name)
        env
      end

      (SCode.CLASS(name = cls_name, classDef = cdef), _)  => begin
        class_env = makeClassEnvironment(inClassDefElement, false)
        cls_type = getClassType(cdef)
        env = extendEnvWithItem(newClassItem(inClassDefElement, class_env, cls_type), inEnv, cls_name)
        env
      end
    end
  end
  #=  A normal class.
  =#
  #=  Create a new environment and add the class's components to it.
  =#
  #=  Add the class with it's environment to the environment.
  =#
  outEnv
end

function makeClassEnvironment(inClassDefElement::SCode.Element, inInModifierScope::Bool) ::Env
  local outClassEnv::Env

  local cdef::SCode.ClassDef
  local cls::SCode.Element
  local cls_name::String
  local env::Env
  local enclosing_env::Env
  local info::SourceInfo

  @match SCode.CLASS(name = cls_name, classDef = cdef, info = info) = inClassDefElement
  env = openScope(emptyEnv, inClassDefElement)
  enclosing_env = if inInModifierScope
    emptyEnv
  else
    env
  end
  outClassEnv = extendEnvWithClassComponents(cls_name, cdef, env, enclosing_env, info)
  outClassEnv
end

#= Extends the environment with a variable. =#
function extendEnvWithVar(inVar::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  local var_name::String
  local is_used::MutableType #= {Bool} =#
  local ty::Absyn.TypeSpec
  local info::SourceInfo

  @match SCode.COMPONENT(name = var_name, typeSpec = ty, info = info) = inVar
  is_used = Mutable.create(false)
  outEnv = extendEnvWithItem(VAR(inVar, SOME(is_used)), inEnv, var_name)
  outEnv
end

#= Extends the environment with an environment item. =#
function extendEnvWithItem(inItem::Item, inEnv::Env, inItemName::String) ::Env
  local outEnv::Env

  local name::Option{String}
  local tree::EnvTree.Tree
  local exts::ExtendsTable
  local imps::ImportTable
  local ty::FrameType
  local rest::Env
  local is_used::Option{MutableType #= {Bool} =#}

  @match _cons(FRAME(name, ty, tree, exts, imps, is_used), rest) = inEnv
  tree = EnvTree.add(tree, inItemName, inItem, extendEnvWithItemConflict)
  outEnv = _cons(FRAME(name, ty, tree, exts, imps, is_used), rest)
  outEnv
end

function extendEnvWithItemConflict(newItem::Item, oldItem::Item, name::String) ::Item
  local item::Item

  item = linkItemUsage(oldItem, newItem)
  item
end

#= Updates an item in the environment by replacing an existing item. =#
function updateItemInEnv(inItem::Item, inEnv::Env, inItemName::String) ::Env
  local outEnv::Env

  local name::Option{String}
  local tree::EnvTree.Tree
  local exts::ExtendsTable
  local imps::ImportTable
  local ty::FrameType
  local rest::Env
  local is_used::Option{MutableType #= {Bool} =#}

  @match _cons(FRAME(name, ty, tree, exts, imps, is_used), rest) = inEnv
  tree = EnvTree.add(tree, inItemName, inItem)
  outEnv = _cons(FRAME(name, ty, tree, exts, imps, is_used), rest)
  outEnv
end

#= Extends the environment with an import element. =#
function extendEnvWithImport(inImport::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local imp::Import
  local name::Option{String}
    local tree::EnvTree.Tree
    local exts::ExtendsTable
    local qual_imps::List{Import}
    local unqual_imps::List{Import}
    local ty::FrameType
    local rest::Env
    local info::SourceInfo
    local hidden::Bool
    local is_used::Option{MutableType #= {Bool} =#}
    #=  Unqualified imports
    =#
    @match (inImport, inEnv) begin
      (SCode.IMPORT(imp = imp && Absyn.UNQUAL_IMPORT(__)), FRAME(name, ty, tree, exts, IMPORT_TABLE(hidden, qual_imps, unqual_imps), is_used) <| rest)  => begin
        unqual_imps = _cons(imp, unqual_imps)
        _cons(FRAME(name, ty, tree, exts, IMPORT_TABLE(hidden, qual_imps, unqual_imps), is_used), rest)
      end

      (SCode.IMPORT(imp = imp), FRAME(name, ty, tree, exts, IMPORT_TABLE(hidden, qual_imps, unqual_imps), is_used) <| rest)  => begin
        imp = translateQualifiedImportToNamed(imp)
        qual_imps = _cons(imp, qual_imps)
        _cons(FRAME(name, ty, tree, exts, IMPORT_TABLE(hidden, qual_imps, unqual_imps), is_used), rest)
      end
    end
  end
  #=  Qualified imports
  =#
  outEnv
end

#= Translates a qualified import to a named import. =#
function translateQualifiedImportToNamed(inImport::Import) ::Import
  local outImport::Import

  outImport = begin
    local name::Absyn.Ident
    local path::Absyn.Path
    #=  Already named.
    =#
    @match inImport begin
      Absyn.NAMED_IMPORT(__)  => begin
        inImport
      end

      Absyn.QUAL_IMPORT(path = path)  => begin
        name = AbsynUtil.pathLastIdent(path)
        Absyn.NAMED_IMPORT(name, path)
      end
    end
  end
  #=  Get the last identifier from the import and use that as the name.
  =#
  outImport
end

#= Extends the environment with an extends-clause. =#
function extendEnvWithExtends(inExtends::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  local bc::Absyn.Path
  local mods::SCode.Mod
  local redecls::List{Redeclaration}
  local info::SourceInfo
  local env::Env
  local index::ModelicaInteger

  @match SCode.EXTENDS(baseClassPath = bc, modifications = mods, info = info) = inExtends
  redecls = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
  index = System.tmpTickIndex(extendsTickIndex)
  outEnv = addExtendsToEnvExtendsTable(EXTENDS(bc, redecls, index, info), inEnv)
  outEnv
end

#= Adds an Extents to the environment. =#
function addExtendsToEnvExtendsTable(inExtends::Extends, inEnv::Env) ::Env
  local outEnv::Env

  local exts::List{Extends}
  local re::List{SCode.Element}
  local cei::Option{SCode.Element}

  @match EXTENDS_TABLE(exts, re, cei) = getEnvExtendsTable(inEnv)
  exts = _cons(inExtends, exts)
  outEnv = setEnvExtendsTable(EXTENDS_TABLE(exts, re, cei), inEnv)
  outEnv
end

function addElementRedeclarationToEnvExtendsTable(inRedeclare::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  local exts::List{Extends}
  local re::List{SCode.Element}
  local cei::Option{SCode.Element}

  @match EXTENDS_TABLE(exts, re, cei) = getEnvExtendsTable(inEnv)
  re = _cons(inRedeclare, re)
  outEnv = setEnvExtendsTable(EXTENDS_TABLE(exts, re, cei), inEnv)
  outEnv
end

#= Extends the environment with a class's components. =#
function extendEnvWithClassComponents(inClassName::String, inClassDef::SCode.ClassDef, inEnv::Env, inEnclosingScope::Env, inInfo::SourceInfo) ::Env
  local outEnv::Env

  outEnv = begin
    local el::List{SCode.Element}
    local enums::List{SCode.Enum}
    local ty::Absyn.TypeSpec
    local env::Env
    local mods::SCode.Mod
    local path::Absyn.Path
    @match (inClassName, inClassDef, inEnv, inEnclosingScope, inInfo) begin
      (_, SCode.PARTS(elementLst = el), _, _, _)  => begin
        env = ListUtil.fold(el, extendEnvWithElement, inEnv)
        env
      end

      (_, SCode.DERIVED(typeSpec = ty && Absyn.TPATH(path = path), modifications = mods), _, _, _)  => begin
        NFSCodeCheck.checkRecursiveShortDefinition(ty, inClassName, inEnclosingScope, inInfo)
        env = extendEnvWithExtends(SCode.EXTENDS(path, SCode.PUBLIC(), mods, NONE(), inInfo), inEnv)
        env
      end

      (_, SCode.ENUMERATION(enumLst = enums), _, _, _)  => begin
        path = Absyn.IDENT(inClassName)
        env = extendEnvWithEnumLiterals(enums, path, 1, inEnv, inInfo)
        env
      end

      _  => begin
        inEnv
      end
    end
  end
  outEnv
end

#= Extends the environment with a class element. =#
function extendEnvWithElement(inElement::SCode.Element, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local env::Env
    local name::SCode.Ident
    #=  redeclare-as-element component
    =#
    @matchcontinue (inElement, inEnv) begin
      (SCode.COMPONENT(prefixes = SCode.PREFIXES(redeclarePrefix = SCode.REDECLARE(__))), _)  => begin
        env = addElementRedeclarationToEnvExtendsTable(inElement, inEnv)
        env = extendEnvWithVar(inElement, env)
        env
      end

      (SCode.COMPONENT(__), _)  => begin
        env = extendEnvWithVar(inElement, inEnv)
        env
      end

      (SCode.CLASS(prefixes = SCode.PREFIXES(redeclarePrefix = SCode.REDECLARE(__))), _)  => begin
        env = addElementRedeclarationToEnvExtendsTable(inElement, inEnv)
        env = extendEnvWithClassDef(inElement, env)
        env
      end

      (SCode.CLASS(__), _)  => begin
        env = extendEnvWithClassDef(inElement, inEnv)
        env
      end

      (SCode.EXTENDS(__), _)  => begin
        env = extendEnvWithExtends(inElement, inEnv)
        env
      end

      (SCode.IMPORT(__), _)  => begin
        env = extendEnvWithImport(inElement, inEnv)
        env
      end

      (SCode.DEFINEUNIT(__), _)  => begin
        inEnv
      end
    end
  end
  #=  normal component
  =#
  #=  redeclare-as-element class
  =#
  #=  normal class
  =#
  outEnv
end

#= Checks that a qualified import is unique, because it's not allowed to have
qualified imports with the same name. =#
function checkUniqueQualifiedImport(inImport::Import, inImports::List{<:Import}, inInfo::SourceInfo)
  _ = begin
    local name::Absyn.Ident
    @matchcontinue (inImport, inImports, inInfo) begin
      (_, _, _)  => begin
        @match false = ListUtil.isMemberOnTrue(inImport, inImports, compareQualifiedImportNames)
        ()
      end

      (Absyn.NAMED_IMPORT(name = name), _, _)  => begin
        Error.addSourceMessage(Error.MULTIPLE_QUALIFIED_IMPORTS_WITH_SAME_NAME, list(name), inInfo)
        fail()
      end
    end
  end
end

#= Compares two qualified imports, returning true if they have the same import
name, otherwise false. =#
function compareQualifiedImportNames(inImport1::Import, inImport2::Import) ::Bool
  local outEqual::Bool

  outEqual = begin
    local name1::Absyn.Ident
    local name2::Absyn.Ident
    @match (inImport1, inImport2) begin
      (Absyn.NAMED_IMPORT(name = name1), Absyn.NAMED_IMPORT(name = name2)) where (stringEqual(name1, name2))  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  outEqual
end

function extendEnvWithEnumLiterals(inEnum::List{<:SCode.Enum}, inEnumPath::Absyn.Path, inNextValue::ModelicaInteger, inEnv::Env, inInfo::SourceInfo) ::Env
  local outEnv::Env

  outEnv = begin
    local lit::SCode.Enum
    local rest_lits::List{SCode.Enum}
    local env::Env
    @match (inEnum, inEnumPath, inNextValue, inEnv, inInfo) begin
      (lit <| rest_lits, _, _, _, _)  => begin
        env = extendEnvWithEnum(lit, inEnumPath, inNextValue, inEnv, inInfo)
        extendEnvWithEnumLiterals(rest_lits, inEnumPath, inNextValue + 1, env, inInfo)
      end

      ( nil(), _, _, _, _)  => begin
        inEnv
      end
    end
  end
  outEnv
end

#= Extends the environment with an enumeration. =#
function extendEnvWithEnum(inEnum::SCode.Enum, inEnumPath::Absyn.Path, inValue::ModelicaInteger, inEnv::Env, inInfo::SourceInfo) ::Env
  local outEnv::Env

  local enum_lit::SCode.Element
  local lit_name::SCode.Ident
  local ty::Absyn.TypeSpec
  local index::String

  @match SCode.ENUM(literal = lit_name) = inEnum
  index = intString(inValue)
  ty = Absyn.TPATH(Absyn.QUALIFIED("EnumType", Absyn.QUALIFIED(index, inEnumPath)), NONE())
  enum_lit = SCode.COMPONENT(lit_name, SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.CONST(), Absyn.BIDIR(), Absyn.NONFIELD()), ty, SCode.NOMOD(), SCode.noComment, NONE(), inInfo)
  outEnv = extendEnvWithElement(enum_lit, inEnv)
  outEnv
end

#= Extends the environment with a new scope and adds a list of iterators to it. =#
function extendEnvWithIterators(inIterators::Absyn.ForIterators, iterIndex::ModelicaInteger, inEnv::Env) ::Env
  local outEnv::Env

  local frame::Frame

  frame = newFrame(SOME("for"), IMPLICIT_SCOPE(iterIndex))
  outEnv = ListUtil.fold(inIterators, extendEnvWithIterator, _cons(frame, inEnv))
  outEnv
end

#= Extends the environment with an iterator. =#
function extendEnvWithIterator(inIterator::Absyn.ForIterator, inEnv::Env) ::Env
  local outEnv::Env

  local iter_name::Absyn.Ident
  local iter::SCode.Element

  @match Absyn.ITERATOR(name = iter_name) = inIterator
  iter = SCode.COMPONENT(iter_name, SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.CONST(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)
  outEnv = extendEnvWithElement(iter, inEnv)
  outEnv
end

#= Extends the environment with a match-expression, i.e. opens a new scope and
adds the local declarations in the match to it. =#
function extendEnvWithMatch(inMatchExp::Absyn.Exp, iterIndex::ModelicaInteger, inEnv::Env) ::Env
  local outEnv::Env

  local frame::Frame
  local local_decls::List{Absyn.ElementItem}

  frame = newFrame(SOME("match"), IMPLICIT_SCOPE(iterIndex))
  @match Absyn.MATCHEXP(localDecls = local_decls) = inMatchExp
  outEnv = ListUtil.fold(local_decls, extendEnvWithElementItem, _cons(frame, inEnv))
  outEnv
end

#= Extends the environment with an Absyn.ElementItem. =#
function extendEnvWithElementItem(inElementItem::Absyn.ElementItem, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local element::Absyn.Element
    local el::List{SCode.Element}
    local env::Env
    @match (inElementItem, inEnv) begin
      (Absyn.ELEMENTITEM(element = element), _)  => begin
        el = AbsynToSCode.translateElement(element, SCode.PROTECTED())
        env = ListUtil.fold(el, extendEnvWithElement, inEnv)
        env
      end

      _  => begin
        inEnv
      end
    end
  end
  #=  Translate the element item to a SCode element.
  =#
  outEnv
end

#= Returns the environment path as a string. =#
function getEnvName(inEnv::Env) ::String
  local outString::String

  outString = begin
    local str::String
    @matchcontinue inEnv begin
      _  => begin
        str = AbsynUtil.pathString(getEnvPath(inEnv))
        str
      end

      _  => begin
        ""
      end
    end
  end
  outString
end

#= Returns the environment path. Fails for an empty environment or the top
scope, which can't be represented as an Absyn.Path. =#
function getEnvPath(inEnv::Env) ::Absyn.Path
  local outPath::Absyn.Path

  outPath = begin
    local name::String
    local path::Absyn.Path
    local rest::Env
    @match inEnv begin
      FRAME(frameType = IMPLICIT_SCOPE(__)) <| rest  => begin
        getEnvPath(rest)
      end

      FRAME(name = SOME(name)) <|  nil()  => begin
        Absyn.IDENT(name)
      end

      FRAME(name = SOME(name)) <| FRAME(name = NONE()) <|  nil()  => begin
        Absyn.IDENT(name)
      end

      FRAME(name = SOME(name)) <| rest  => begin
        path = getEnvPath(rest)
        path = AbsynUtil.joinPaths(path, Absyn.IDENT(name))
        path
      end
    end
  end
  outPath
end

#= Returns the name of the innermost that has a name. =#
function getScopeName(inEnv::Env) ::String
  local outString::String

  outString = begin
    local name::String
    local rest::Env
    @match inEnv begin
      FRAME(name = SOME(name)) <| _  => begin
        name
      end

      _ <| rest  => begin
        getScopeName(rest)
      end
    end
  end
  outString
end

function envPrefixOf(inPrefixEnv::Env, inEnv::Env) ::Bool
  local outIsPrefix::Bool

  outIsPrefix = envPrefixOf2(listReverse(inPrefixEnv), listReverse(inEnv))
  outIsPrefix
end

#= Checks if one environment is a prefix of another. =#
function envPrefixOf2(inPrefixEnv::Env, inEnv::Env) ::Bool
  local outIsPrefix::Bool

  outIsPrefix = begin
    local n1::String
    local n2::String
    local rest1::Env
    local rest2::Env
    @matchcontinue (inPrefixEnv, inEnv) begin
      ( nil(), _)  => begin
        true
      end

      (FRAME(name = NONE()) <| rest1, FRAME(name = NONE()) <| rest2)  => begin
        envPrefixOf2(rest1, rest2)
      end

      (FRAME(name = SOME(n1)) <| rest1, FRAME(name = SOME(n2)) <| rest2)  => begin
        @match true = stringEqual(n1, n2)
        envPrefixOf2(rest1, rest2)
      end

      _  => begin
        false
      end
    end
  end
  outIsPrefix
end

function envScopeNames(inEnv::Env) ::List{String}
  local outNames::List{String}

  outNames = envScopeNames2(inEnv, nil)
  outNames
end

function envScopeNames2(inEnv::Env, inAccumNames::List{<:String}) ::List{String}
  local outNames::List{String}

  outNames = begin
    local name::String
    local rest_env::Env
    local names::List{String}
    @match (inEnv, inAccumNames) begin
      (FRAME(name = SOME(name)) <| rest_env, _)  => begin
        names = envScopeNames2(rest_env, _cons(name, inAccumNames))
        names
      end

      (FRAME(name = NONE()) <| rest_env, _)  => begin
        envScopeNames2(rest_env, inAccumNames)
      end

      ( nil(), _)  => begin
        inAccumNames
      end
    end
  end
  outNames
end

function envEqualPrefix(inEnv1::Env, inEnv2::Env) ::Env
  local outPrefix::Env

  outPrefix = envEqualPrefix2(listReverse(inEnv1), listReverse(inEnv2), nil)
  outPrefix
end

function envEqualPrefix2(inEnv1::Env, inEnv2::Env, inAccumEnv::Env) ::Env
  local outPrefix::Env

  outPrefix = begin
    local name1::String
    local name2::String
    local env::Env
    local rest_env1::Env
    local rest_env2::Env
    local frame::Frame
    @matchcontinue (inEnv1, inEnv2, inAccumEnv) begin
      (frame && FRAME(name = SOME(name1)) <| rest_env1, FRAME(name = SOME(name2)) <| rest_env2, _)  => begin
        @match true = stringEq(name1, name2)
        env = envEqualPrefix2(rest_env1, rest_env2, _cons(frame, inAccumEnv))
        env
      end

      (FRAME(name = NONE()) <| rest_env1, FRAME(name = NONE()) <| rest_env2, _)  => begin
        envEqualPrefix2(rest_env1, rest_env2, inAccumEnv)
      end

      _  => begin
        inAccumEnv
      end
    end
  end
  outPrefix
end

#= Returns the SourceInfo of an environment item. =#
function getItemInfo(inItem::Item) ::SourceInfo
  local outInfo::SourceInfo

  outInfo = begin
    local info::SourceInfo
    local item::Item
    @match inItem begin
      VAR(var = SCode.COMPONENT(info = info))  => begin
        info
      end

      CLASS(cls = SCode.CLASS(info = info))  => begin
        info
      end

      ALIAS(info = info)  => begin
        info
      end

      REDECLARED_ITEM(item = item)  => begin
        getItemInfo(item)
      end
    end
  end
  outInfo
end

#= Returns more info on an environment item. =#
function itemStr(inItem::Item) ::String
  local outName::String

  outName = begin
    local name::String
    local alias_str::String
    local el::SCode.Element
    local path::Absyn.Path
    local item::Item
    @matchcontinue inItem begin
      VAR(var = el)  => begin
        SCodeDump.unparseElementStr(el, SCodeDump.defaultOptions)
      end

      CLASS(cls = el)  => begin
        SCodeDump.unparseElementStr(el, SCodeDump.defaultOptions)
      end

      ALIAS(name = name, path = SOME(path))  => begin
        alias_str = AbsynUtil.pathString(path)
        "alias " + name + " -> (" + alias_str + "." + name + ")"
      end

      ALIAS(name = name, path = NONE())  => begin
        "alias " + name + " -> ()"
      end

      REDECLARED_ITEM(item = item)  => begin
        name = itemStr(item)
        "redeclared " + name
      end

      _  => begin
        "UNHANDLED ITEM"
      end
    end
  end
  outName
end

#= Returns the name of an environment item. =#
function getItemName(inItem::Item) ::String
  local outName::String

  outName = begin
    local name::String
    local item::Item
    @match inItem begin
      VAR(var = SCode.COMPONENT(name = name))  => begin
        name
      end

      CLASS(cls = SCode.CLASS(name = name))  => begin
        name
      end

      ALIAS(name = name)  => begin
        name
      end

      REDECLARED_ITEM(item = item)  => begin
        getItemName(item)
      end
    end
  end
  outName
end

#= Returns the environment in an environment item. =#
function getItemEnv(inItem::Item) ::Env
  local outEnv::Env

  outEnv = begin
    local env::Env
    local item::Item
    @match inItem begin
      CLASS(env = env)  => begin
        env
      end

      REDECLARED_ITEM(item = item)  => begin
        getItemEnv(item)
      end
    end
  end
  outEnv
end

#= Returns the environment in an environment item. =#
function getItemEnvNoFail(inItem::Item) ::Env
  local outEnv::Env

  outEnv = begin
    local env::Env
    local item::Item
    local str::String
    local f::Frame
    @matchcontinue inItem begin
      CLASS(env = env)  => begin
        env
      end

      REDECLARED_ITEM(item = item)  => begin
        getItemEnvNoFail(item)
      end

      _  => begin
        str = "NO ENV FOR ITEM: " + getItemName(inItem)
        f = newFrame(SOME(str), ENCAPSULATED_SCOPE())
        env = list(f)
        env
      end
    end
  end
  outEnv
end

#= Sets the environment in an environment item. =#
function setItemEnv(inItem::Item, inNewEnv::Env) ::Item
  local outItem::Item

  outItem = begin
    local env::Env
    local item::Item
    local cls::SCode.Element
    local ct::ClassType
    @match (inItem, inNewEnv) begin
      (CLASS(cls, _, ct), _)  => begin
        CLASS(cls, inNewEnv, ct)
      end

      (REDECLARED_ITEM(item = item), _)  => begin
        setItemEnv(item, inNewEnv)
      end
    end
  end
  outItem
end

#= myMerges an environment item's environment with the given environment. =#
function myMergeItemEnv(inItem::Item, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local cls_env::Frame
    local item::Item
    @match (inItem, inEnv) begin
      (CLASS(env = cls_env <|  nil()), _)  => begin
        enterFrame(cls_env, inEnv)
      end

      (REDECLARED_ITEM(item = item), _)  => begin
        myMergeItemEnv(item, inEnv)
      end

      _  => begin
        inEnv
      end
    end
  end
  outEnv
end

#= myMerges an environment item's environment with the given environment. =#
function unmyMergeItemEnv(inItem::Item, inEnv::Env) ::Env
  local outEnv::Env

  outEnv = begin
    local item::Item
    local env::Env
    @match (inItem, inEnv) begin
      (_, _ <| env)  => begin
        env
      end

      _  => begin
        inEnv
      end
    end
  end
  outEnv
end

function getItemPrefixes(inItem::Item) ::SCode.Prefixes
  local outPrefixes::SCode.Prefixes

  outPrefixes = begin
    local pf::SCode.Prefixes
    local item::Item
    @match inItem begin
      CLASS(cls = SCode.CLASS(prefixes = pf))  => begin
        pf
      end

      VAR(var = SCode.COMPONENT(prefixes = pf))  => begin
        pf
      end

      REDECLARED_ITEM(item = item)  => begin
        getItemPrefixes(item)
      end
    end
  end
  outPrefixes
end

function resolveRedeclaredItem(inItem::Item, inEnv::Env) ::Tuple{Item, Env, List{Tuple{Item, Env}}}
  local outPreviousItem::List{Tuple{Item, Env}}
  local outEnv::Env
  local outItem::Item

  (outItem, outEnv, outPreviousItem) = begin
    local item::Item
    local env::Env
    @match (inItem, inEnv) begin
      (REDECLARED_ITEM(item = item, declaredEnv = env), _)  => begin
        (item, env, list((inItem, inEnv)))
      end

      _  => begin
        (inItem, inEnv, nil)
      end
    end
  end
  (outItem, outEnv, outPreviousItem)
end

function getEnvExtendsTable(inEnv::Env) ::ExtendsTable
  local outExtendsTable::ExtendsTable

  @match _cons(FRAME(extendsTable = outExtendsTable), _) = inEnv
  outExtendsTable
end

function getEnvExtendsFromTable(inEnv::Env) ::List{Extends}
  local outExtends::List{Extends}

  @match EXTENDS_TABLE(baseClasses = outExtends) = getEnvExtendsTable(inEnv)
  outExtends
end

#= @author: adrpo
returns the redeclares inside the extends table for the given class.
The derived class should have only 1 extends =#
function getDerivedClassRedeclares(inDerivedName::SCode.Ident, inTypeSpec::Absyn.TypeSpec, inEnv::Env) ::List{Redeclaration}
  local outRedeclarations::List{Redeclaration}

  outRedeclarations = begin
    local bc::Absyn.Path
    local path::Absyn.Path
    local rm::List{Redeclaration}
    #=  only one extends!
    =#
    @matchcontinue (inDerivedName, inTypeSpec, inEnv) begin
      (_, Absyn.TPATH(path, _), _)  => begin
        @match EXTENDS(baseClass = bc, redeclareModifiers = rm) <| nil = getEnvExtendsFromTable(inEnv)
        @match true = AbsynUtil.pathSuffixOf(path, bc)
        rm
      end

      (_, Absyn.TPATH(path, _), _)  => begin
        @match EXTENDS(baseClass = bc, redeclareModifiers = rm) <| nil = getEnvExtendsFromTable(inEnv)
        @match false = AbsynUtil.pathSuffixOf(path, bc)
        print("Derived paths are not the same: " + AbsynUtil.pathString(path) + " != " + AbsynUtil.pathString(bc) + "\\n")
        rm
      end

      _  => begin
        nil
      end
    end
  end
  #=  else nothing
  =#
  outRedeclarations
end

function setEnvExtendsTable(inExtendsTable::ExtendsTable, inEnv::Env) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local tree::EnvTree.Tree
  local imps::ImportTable
  local is_used::Option{MutableType #= {Bool} =#}
  local rest_env::Env

  @match _cons(FRAME(name, ty, tree, _, imps, is_used), rest_env) = inEnv
  outEnv = _cons(FRAME(name, ty, tree, inExtendsTable, imps, is_used), rest_env)
  outEnv
end

function setEnvClsAndVars(inTree::EnvTree.Tree, inEnv::Env) ::Env
  local outEnv::Env

  local name::Option{String}
  local ty::FrameType
  local ext::ExtendsTable
  local imps::ImportTable
  local is_used::Option{MutableType #= {Bool} =#}
  local rest_env::Env

  @match _cons(FRAME(name, ty, _, ext, imps, is_used), rest_env) = inEnv
  outEnv = _cons(FRAME(name, ty, inTree, ext, imps, is_used), rest_env)
  outEnv
end

#= myMerges a path with the environment path. =#
function myMergePathWithEnvPath(inPath::Absyn.Path, inEnv::Env) ::Absyn.Path
  local outPath::Absyn.Path

  outPath = begin
    local env_path::Absyn.Path
    local id::Absyn.Ident
    #=  Try to myMerge the last identifier in the path with the environment path.
    =#
    @matchcontinue (inPath, inEnv) begin
      (_, _)  => begin
        env_path = getEnvPath(inEnv)
        id = AbsynUtil.pathLastIdent(inPath)
        AbsynUtil.joinPaths(env_path, Absyn.IDENT(id))
      end

      _  => begin
        inPath
      end
    end
  end
  #=  If the previous case failed (which will happen at the top-scope when
  =#
  #=  getEnvPath fails), just return the path as it is.
  =#
  outPath
end

#= myMerges a path with the environment path. =#
function myMergeTypeSpecWithEnvPath(inTS::Absyn.TypeSpec, inEnv::Env) ::Absyn.TypeSpec
  local outTS::Absyn.TypeSpec

  outTS = begin
    local path::Absyn.Path
    local id::Absyn.Ident
    local ad::Option{Absyn.ArrayDim}
    #=  Try to myMerge the last identifier in the path with the environment path.
    =#
    @matchcontinue (inTS, inEnv) begin
      (Absyn.TPATH(path, ad), _)  => begin
        id = AbsynUtil.pathLastIdent(path)
        path = AbsynUtil.joinPaths(getEnvPath(inEnv), Absyn.IDENT(id))
        Absyn.TPATH(path, ad)
      end

      _  => begin
        inTS
      end
    end
  end
  #=  If the previous case failed (which will happen at the top-scope when
  =#
  #=  getEnvPath fails), just return the path as it is.
  =#
  outTS
end

function prefixIdentWithEnv(inIdent::String, inEnv::Env) ::Absyn.Path
  local outPath::Absyn.Path

  outPath = begin
    local path::Absyn.Path
    @match (inIdent, inEnv) begin
      (_, FRAME(name = NONE()) <|  nil())  => begin
        Absyn.IDENT(inIdent)
      end

      _  => begin
        path = getEnvPath(inEnv)
        path = AbsynUtil.suffixPath(path, inIdent)
        path
      end
    end
  end
  outPath
end

function getRedeclarationElement(inRedeclare::Redeclaration) ::SCode.Element
  local outElement::SCode.Element

  outElement = begin
    local e::SCode.Element
    local item::Item
    @match inRedeclare begin
      RAW_MODIFIER(modifier = e)  => begin
        e
      end

      PROCESSED_MODIFIER(modifier = CLASS(cls = e))  => begin
        e
      end

      PROCESSED_MODIFIER(modifier = VAR(var = e))  => begin
        e
      end

      PROCESSED_MODIFIER(modifier = REDECLARED_ITEM(item = item))  => begin
        getRedeclarationElement(PROCESSED_MODIFIER(item))
      end
    end
  end
  outElement
end

function getRedeclarationNameInfo(inRedeclare::Redeclaration) ::Tuple{String, SourceInfo}
  local outInfo::SourceInfo
  local outName::String

  (outName, outInfo) = begin
    local el::SCode.Element
    local name::String
    local info::SourceInfo
    @match inRedeclare begin
      PROCESSED_MODIFIER(modifier = ALIAS(name = name, info = info))  => begin
        (name, info)
      end

      _  => begin
        el = getRedeclarationElement(inRedeclare)
        (name, info) = SCodeUtil.elementNameInfo(el)
        (name, info)
      end
    end
  end
  (outName, outInfo)
end

#= Build a new environment that contains some things that can't be represented
in ModelicaBuiltin or MetaModelicaBuiltin. =#
function buildInitialEnv() ::Env
  local outInitialEnv::Env

  local tree::EnvTree.Tree
  local exts::ExtendsTable
  local imps::ImportTable
  local is_used::MutableType #= {Bool} =#
  local p::SCode.Program
  local initialClasses::List{Absyn.Class}

  tree = EnvTree.new()
  exts = newExtendsTable()
  imps = newImportTable()
  is_used = Mutable.create(false)
  tree = addDummyClassToTree("String", tree)
  tree = addDummyClassToTree("Integer", tree)
  tree = addDummyClassToTree("spliceFunction", tree)
  outInitialEnv = list(FRAME(NONE(), NORMAL_SCOPE(), tree, exts, imps, SOME(is_used)))
  #=  add the builtin classes from ModelicaBuiltin.mo and MetaModelicaBuiltin.mo
  =#
  (_, p) = FBuiltin.getInitialFunctions()
  outInitialEnv = extendEnvWithClasses(p, outInitialEnv)
  outInitialEnv
end

#= Insert a dummy class into the EnvTree. =#
function addDummyClassToTree(inName::String, inTree::EnvTree.Tree) ::EnvTree.Tree
  local outTree::EnvTree.Tree

  local cls::SCode.Element

  cls = SCode.CLASS(inName, SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_CLASS(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)
  outTree = EnvTree.add(inTree, inName, CLASS(cls, emptyEnv, BUILTIN()))
  outTree
end

function printEnvStr(inEnv::Env) ::String
  local outString::String

  local env::Env

  env = listReverse(inEnv)
  outString = stringDelimitList(ListUtil.map(env, printFrameStr), "\\n")
  outString
end

function printFrameStr(inFrame::Frame) ::String
  local outString::String

  outString = begin
    local name::Option{String}
    local ty::FrameType
    local tree::EnvTree.Tree
    local exts::ExtendsTable
    local imps::ImportTable
  local name_str::String
    local ty_str::String
    local tree_str::String
    local ext_str::String
    local imp_str::String
    local out::String
    @match inFrame begin
      FRAME(name, ty, tree, exts, imps, _)  => begin
        name_str = printFrameNameStr(name)
        ty_str = printFrameTypeStr(ty)
        tree_str = EnvTree.printTreeStr(tree)
        ext_str = printExtendsTableStr(exts)
        imp_str = printImportTableStr(imps)
        name_str = "<<<" + ty_str + " frame " + name_str + ">>>\\n"
        out = name_str + "\\tImports:\\n" + imp_str + "\\n\\tExtends:\\n" + ext_str + "\\n\\tComponents:\\n" + tree_str + "\\n"
        out
      end
    end
  end
  outString
end

function printFrameNameStr(inFrame::Option{<:String}) ::String
  local outString::String

  outString = begin
    local name::String
    @match inFrame begin
      NONE()  => begin
        "global"
      end

      SOME(name)  => begin
        name
      end
    end
  end
  outString
end

function printFrameTypeStr(inFrame::FrameType) ::String
  local outString::String

  outString = begin
    @match inFrame begin
      NORMAL_SCOPE(__)  => begin
        "Normal"
      end

      ENCAPSULATED_SCOPE(__)  => begin
        "Encapsulated"
      end

      IMPLICIT_SCOPE(__)  => begin
        "Implicit"
      end
    end
  end
  outString
end

function printExtendsTableStr(inExtendsTable::ExtendsTable) ::String
  local outString::String

  local bcl::List{Extends}
  local re::List{SCode.Element}
  local cei::Option{SCode.Element}

  @match EXTENDS_TABLE(baseClasses = bcl, redeclaredElements = re, classExtendsInfo = cei) = inExtendsTable
  outString = stringDelimitList(ListUtil.map(bcl, printExtendsStr), "\\n") + "\\n\\t\\tRedeclare elements:\\n\\t\\t\\t" + stringDelimitList(ListUtil.map1(re, SCodeDump.unparseElementStr, SCodeDump.defaultOptions), "\\n\\t\\t\\t") + "\\n\\t\\tClass extends:\\n\\t\\t\\t" + Util.stringOption(Util.applyOption1(cei, SCodeDump.unparseElementStr, SCodeDump.defaultOptions))
  outString
end

function printExtendsStr(inExtends::Extends) ::String
  local outString::String

  local bc::Absyn.Path
  local mods::List{Redeclaration}
  local mods_str::String

  @match EXTENDS(baseClass = bc, redeclareModifiers = mods) = inExtends
  mods_str = stringDelimitList(ListUtil.map(mods, printRedeclarationStr), "\\n")
  outString = "\\t\\t" + AbsynUtil.pathString(bc) + "(" + mods_str + ")"
  outString
end

function printRedeclarationStr(inRedeclare::Redeclaration) ::String
  local outString::String

  outString = begin
    local name::String
    local p::Absyn.Path
    @matchcontinue inRedeclare begin
      PROCESSED_MODIFIER(modifier = ALIAS(name = name, path = SOME(p)))  => begin
        "ALIAS(" + AbsynUtil.pathString(p) + "." + name + ")"
      end

      PROCESSED_MODIFIER(modifier = ALIAS(name = name))  => begin
        "ALIAS(" + name + ")"
      end

      _  => begin
        SCodeDump.unparseElementStr(getRedeclarationElement(inRedeclare), SCodeDump.defaultOptions)
      end
    end
  end
  outString
end

function printImportTableStr(inImports::ImportTable) ::String
  local outString::String

  local qual_imps::List{Import}
  local unqual_imps::List{Import}
  local qual_str::String
  local unqual_str::String

  @match IMPORT_TABLE(qualifiedImports = qual_imps, unqualifiedImports = unqual_imps) = inImports
  qual_str = stringDelimitList(ListUtil.map(qual_imps, AbsynUtil.printImportString), "\\n\\t\\t")
  unqual_str = stringDelimitList(ListUtil.map(unqual_imps, AbsynUtil.printImportString), "\\n\\t\\t")
  outString = "\\t\\t" + qual_str + unqual_str
  outString
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

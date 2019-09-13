
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

module FCore

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
  #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

@UniontypeDecl ImportTable
@UniontypeDecl Node
@UniontypeDecl ModScope
@UniontypeDecl Data
@UniontypeDecl Kind
@UniontypeDecl Status
@UniontypeDecl Visit
@UniontypeDecl Visited
@UniontypeDecl VAvlTree
@UniontypeDecl VAvlTreeValue
@UniontypeDecl Extra
@UniontypeDecl Graph
@UniontypeDecl Top
@UniontypeDecl Cache
@UniontypeDecl ScopeType


module RefTree
using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

import BaseAvlTree
import FCore.Name
import FCore.Ref
import FCore.Node
using BaseAvlTree
Key = String
Value = Ref
#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

import Absyn
const Import = Absyn.Import
const Name = String  #= an identifier is just a string =#
const Names = List  #= list of names =#
const Id = ModelicaInteger
const Seq = ModelicaInteger
const Next = Seq
const Refs = List
const Parents = Refs
const Scope = Refs
const Children = RefTree.Tree
import AbsynUtil
import AvlSetCR
import DAE
import Mutable
using Mutable: MutableType
import SCode
import Prefix
import DAEUtil
import Config

@Uniontype ImportTable begin
  @Record IMPORT_TABLE begin

    #=  Imports should not be inherited, but removing them from the node
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

const emptyScope = nil #= empty scope =#::Scope
const emptyImportTable = IMPORT_TABLE(false, nil, nil)::ImportTable

  #The question is can we just use Ref? I think so. Add Compatabilty for MetaModelica.jl for now...
  #Ref = Array  #= array of 1 =#

  @Uniontype Node begin
    @Record N begin

      name #= node name, class/component/extends name, etc. see also *NodeName in above =#::Name
      id #= Unique node id =#::Id
      parents #= A node can have several parents depending on the context =#::Parents
      children #= List of uniquely named classes and variables =#::Children
      data #= More data for this node, Class, Var, etc =#::Data
    end
  end

#= Used to know where a modifier came from, for error reporting. =#
@Uniontype ModScope begin
  @Record MS_COMPONENT begin

    name::String
  end

  @Record MS_EXTENDS begin

    path::Absyn.Path
  end

  @Record MS_DERIVED begin

    path::Absyn.Path
  end

  @Record MS_CLASS_EXTENDS begin

    name::String
  end

  @Record MS_CONSTRAINEDBY begin

    path::Absyn.Path
  end
end

@Uniontype Data begin
  @Record TOP begin

  end

  @Record IT begin

    i #= instantiated component =#::DAE.Var
  end

  @Record IM begin

    i #= imports =#::ImportTable
  end

  @Record CL begin
    e::SCode.Element
    pre::Prefix.PrefixType
    mod #= modification =#::DAE.Mod
    kind #= usedefined, builtin, basic type =#::Kind
    status #= if it is untyped, typed or fully instantiated (dae) =#::Status
  end

  @Record CO begin

    e::SCode.Element
    mod #= modification =#::DAE.Mod
    kind #= usedefined, builtin, basic type =#::Kind
    status #= if it is untyped, typed or fully instantiated (dae) =#::Status
  end

  @Record EX begin

    e::SCode.Element
    mod #= modification =#::DAE.Mod
  end

  @Record DU begin

    els::List{SCode.Element}
  end

  @Record FT begin

    tys #= list since several types with the same name can exist in the same scope (overloading) =#::List{DAE.Type}
  end

  @Record AL begin

    name #= al or ial (initial) =#::Name
    a::List{SCode.AlgorithmSection}
  end

  @Record EQ begin

    name #= eq or ieq (initial) =#::Name
    e::List{SCode.Equation}
  end

  @Record OT begin

    constrainLst::List{SCode.ConstraintSection}
    clsAttrs::List{Absyn.NamedArg}
  end

  @Record ED begin

    ed::SCode.ExternalDecl
  end

  @Record FS begin

    fis::Absyn.ForIterators
  end

  @Record FI begin

    fi::Absyn.ForIterator
  end

  @Record MS begin

    e::Absyn.Exp
  end

  @Record MO begin

    m::SCode.Mod
  end

  @Record EXP begin

    name #= what is the expression for =#::String
    e::Absyn.Exp
  end

  @Record CR begin

    r::Absyn.ComponentRef
  end

  @Record DIMS begin

    name #= what are the dimensions for, type or component =#::String
    dims::Absyn.ArrayDim
  end

  @Record CC begin

    cc::SCode.ConstrainClass
  end

  @Record REF begin

    target::Scope
  end

  @Record ND begin

    scopeType::Option{ScopeType}
  end

  @Record VR begin

    source::Scope
    p::Prefix.PrefixType
    m::DAE.Mod
    scopeType::Option{ScopeType}
  end

  @Record ASSERT begin

    message::String
  end

  @Record STATUS begin

    isInstantiating::Bool
  end
end


@Uniontype Kind begin
  @Record USERDEFINED begin

  end

  @Record BUILTIN begin

  end

  @Record BASIC_TYPE begin

  end
end

#= Used to distinguish between different phases of the instantiation of a component
A component is first added to environment untyped. It can thereafter be instantiated to get its type
and finally instantiated to produce the DAE. These three states are indicated by this datatype. =#
@Uniontype Status begin
  @Record VAR_UNTYPED begin

  end

  @Record VAR_TYPED begin

  end

  @Record VAR_DAE begin

  end

  @Record VAR_DELETED begin

  end

  @Record CLS_UNTYPED begin

  end

  @Record CLS_PARTIAL begin

  end

  @Record CLS_FULL begin

  end

  @Record CLS_INSTANCE begin

    instanceOf::String
  end
end

#=  ************************ FVisit structures ***************************
=#
#=  ************************ FVisit structures ***************************
=#
#=  ************************ FVisit structures ***************************
=#
#=  ************************ FVisit structures ***************************
=#

#= Visit Node Info =#
@Uniontype Visit begin
  @Record VN begin

    ref #= which node it is =#::Ref
    seq #= order in which was visited =#::Seq
  end
end

#= Visited structure is an AvlTree Id <-> Visit =#
@Uniontype Visited begin
  @Record V begin

    tree::VAvlTree
    next #= the next visit node id =#::Next
  end
end

VAvlKey = Id

VAvlValue = Visit

#= The binary tree data structure for visited =#
@Uniontype VAvlTree begin
  @Record VAVLTREENODE begin

    value #= Value =#::Option{VAvlTreeValue}
    height #= heigth of tree, used for balancing =#::ModelicaInteger
    left #= left subtree =#::Option{VAvlTree}
    right #= right subtree =#::Option{VAvlTree}
  end
end

#= Each node in the binary tree can have a value associated with it. =#
@Uniontype VAvlTreeValue begin
  @Record VAVLTREEVALUE begin

    key #= Key =#::VAvlKey
    value #= Value =#::VAvlValue
  end
end

const emptyVAvlTree = VAVLTREENODE(NONE(), 0, NONE(), NONE())::VAvlTree
#=  ************************ FGraph structures ***************************
=#
#=  ************************ FGraph structures ***************************
=#
#=  ************************ FGraph structures ***************************
=#
#=  ************************ FGraph structures ***************************
=#

#= propagate more info into env if needed =#
@Uniontype Extra begin
  @Record EXTRA begin

    topModel::Absyn.Path
  end
end

#= graph =#
@Uniontype Graph begin
  @Record G begin

    top #= the top node =#::Top
    scope #= current scope =#::Scope
  end

  @Record EG begin

    name::Name
  end
end

@Uniontype Top begin
  @Record GTOP begin

    graph::Array{Graph}
    name #= name of the graph =#::Name
    node #= the top node =#::Ref
    extra #= extra information =#::Extra
  end
end

const dummyTopModel = Absyn.IDENT("EMPTY")::Absyn.Path
const dummyExtra = EXTRA(dummyTopModel)::Extra
const recordConstructorSuffix = "recordconstructor"::String
const forScopeName = "for loop scope" #= a unique scope used in for equations =#::String
const forIterScopeName = "foriter loop scope" #= a unique scope used in for iterators =#::String
const parForScopeName = "pafor loop scope" #= a unique scope used in parfor loops =#::String
const parForIterScopeName = "parforiter loop scope" #= a unique scope used in parfor iterators =#::String
const matchScopeName = "match scope" #= a unique scope used by match expressions =#::String
const caseScopeName = "case scope" #= a unique scope used by match expressions; to be removed when local decls are deprecated =#::String
const patternTypeScope = "pattern type scope" #= a scope for specializing pattern types =#::String
const implicitScopeNames = list(forScopeName, forIterScopeName, parForScopeName, parForIterScopeName, matchScopeName, caseScopeName, patternTypeScope)::List
const firstId = 0::Id
#=  ************************ Cache structures ***************************
=#
#=  ************************ Cache structures ***************************
=#
#=  ************************ Cache structures ***************************
=#
#=  ************************ Cache structures ***************************
=#

StructuralParameters = Tuple
test = DAE.FunctionTree
@Uniontype Cache begin
  @Record CACHE begin

    initialGraph #= and the initial environment =#::Option{Graph}
    functions #= set of Option<DAE.Function>; NONE() means instantiation started; SOME() means it's finished =#::MutableType{DAE.FunctionTree}
    evaluatedParams #= ht of prefixed crefs and a stack of evaluated but not yet prefix crefs =#::StructuralParameters
    modelName #= name of the model being instantiated =#::Absyn.Path
  end

  @Record NO_CACHE begin

  end
end

@Uniontype ScopeType begin
  @Record FUNCTION_SCOPE begin

  end

  @Record CLASS_SCOPE begin

  end

  @Record PARALLEL_SCOPE begin

  end
end

#=  ************************ functions ***************************
=#

function next(inext::Next) ::Next
  local onext::Next

  onext = inext + 1
  onext
end

#= returns an empty cache =#
function emptyCache() ::Cache
  local cache::Cache

  local instFuncs::MutableType{DAE.FunctionTree}
  local ht::StructuralParameters

  instFuncs = Mutable.create(DAE.AvlTreePathFunction.Tree.EMPTY())
  ht = (AvlSetCR.EMPTY(), nil)
  cache = CACHE(NONE(), instFuncs, ht, Absyn.IDENT("##UNDEFINED##"))
  cache
end

#= returns an empty cache =#
function noCache() ::Cache
  local cache::Cache

  cache = NO_CACHE()
  cache
end

function addEvaluatedCref(cache::Cache, var::SCode.Variability, cr::DAE.ComponentRef) ::Cache
  local ocache::Cache

  ocache = begin
    local initialGraph::Option{Graph}
    local functions::MutableType{DAE.FunctionTree}
    local ht::AvlSetCR.Tree
    local st::List{List{DAE.ComponentRef}}
    local crs::List{DAE.ComponentRef}
    local p::Absyn.Path
    @match (cache, var, cr) begin
      (CACHE(initialGraph, functions, (ht, crs <| st), p), SCode.PARAM(__), _)  => begin
        CACHE(initialGraph, functions, (ht, _cons(_cons(cr, crs), st)), p)
      end

      (CACHE(initialGraph, functions, (ht,  nil()), p), SCode.PARAM(__), _)  => begin
        CACHE(initialGraph, functions, (ht, _cons(list(cr), nil)), p)
      end

      _  => begin
        cache
      end
    end
  end
  ocache
end

function getEvaluatedParams(cache::Cache) ::AvlSetCR.Tree
  local ht::AvlSetCR.Tree

  @match CACHE(evaluatedParams = (ht, _)) = cache
  ht
end

function printNumStructuralParameters(cache::Cache)
  local crs::List{DAE.ComponentRef}

  @match CACHE(evaluatedParams = (_, _cons(crs, _))) = cache
  print("printNumStructuralParameters: " + intString(listLength(crs)) + "\\n")
end

function setCacheClassName(inCache::Cache, p::Absyn.Path) ::Cache
  local outCache::Cache

  outCache = begin
    local ef::MutableType{DAE.FunctionTree}
    local ht::StructuralParameters
    local igraph::Option{Graph}
    @match (inCache, p) begin
      (CACHE(igraph, ef, ht, _), _)  => begin
        CACHE(igraph, ef, ht, p)
      end

      _  => begin
        inCache
      end
    end
  end
  outCache
end

function isImplicitScope(inName::Name) ::Bool
  local isImplicit::Bool

  isImplicit = begin
    local id::Name
    @matchcontinue inName begin
      id  => begin
        stringGet(id, 1) == 36
      end

      _  => begin
        false
      end
    end
  end
  #=  \"$\"
  =#
  isImplicit
end

#= returns the function in the set =#
function getCachedInstFunc(inCache::Cache, path::Absyn.Path) ::DAE.Function
  local func::DAE.Function

  func = begin
    local ef::MutableType{DAE.FunctionTree}
    @match (inCache, path) begin
      (CACHE(functions = ef), _)  => begin
        @match SOME(func) = DAE.AvlTreePathFunction.get(Mutable.access(ef), path)
        func
      end
    end
  end
  func
end

#= succeeds if the FQ function is in the set of functions =#
function checkCachedInstFuncGuard(inCache::Cache, path::Absyn.Path)
  _ = begin
    local ef::MutableType{DAE.FunctionTree}
    @match (inCache, path) begin
      (CACHE(functions = ef), _)  => begin
        DAE.AvlTreePathFunction.get(Mutable.access(ef), path)
        ()
      end
    end
  end
end

#= Selector function =#
function getFunctionTree(cache::Cache) ::DAE.FunctionTree
  local ft::DAE.FunctionTree

  ft = begin
    local ef::MutableType{DAE.FunctionTree}
    @match cache begin
      CACHE(functions = ef)  => begin
        Mutable.access(ef)
      end

      _  => begin
        DAE.AvlTreePathFunction.Tree.EMPTY()
      end
    end
  end
  ft
end

#= adds the FQ path to the set of instantiated functions as NONE().
This guards against recursive functions. =#
function addCachedInstFuncGuard(cache::Cache, func::Absyn.Path #= fully qualified function name =#) ::Cache
  local outCache::Cache

  outCache = begin
    local ef::MutableType{DAE.FunctionTree}
    local igraph::Option{Graph}
    local ht::StructuralParameters
    local p::Absyn.Path
    #=  Don't overwrite SOME() with NONE()
    =#
    @matchcontinue (cache, func) begin
      (_, _)  => begin
        checkCachedInstFuncGuard(cache, func)
        cache
      end

      (CACHE(functions = ef), Absyn.FULLYQUALIFIED(_))  => begin
        Mutable.update(ef, DAE.AvlTreePathFunction.add(Mutable.access(ef), func, NONE()))
        cache
      end

      (_, _)  => begin
        cache
      end
    end
  end
  #=  print(\"Func quard [there]: \" + AbsynUtil.pathString(func) + \"\\n\");
  =#
  #=  print(\"Func quard [new]: \" + AbsynUtil.pathString(func) + \"\\n\");
  =#
  #=  Non-FQ paths mean aliased functions; do not add these to the cache
  =#
  #=  print(\"Func quard [unqual]: \" + AbsynUtil.pathString(func) + \"\\n\");
  =#
  outCache
end

#= adds the list<DAE.Function> to the set of instantiated functions =#
function addDaeFunction(inCache::Cache, funcs::List{<:DAE.Function} #= fully qualified function name =#) ::Cache
  local outCache::Cache

  outCache = begin
    local ef::MutableType{DAE.FunctionTree}
    local igraph::Option{Graph}
    local ht::StructuralParameters
    local p::Absyn.Path
    @match (inCache, funcs) begin
      (CACHE(_, ef, _, _), _)  => begin
        Mutable.update(ef, DAEUtil.addDaeFunction(funcs, Mutable.access(ef)))
        inCache
      end

      _  => begin
        inCache
      end
    end
  end
  outCache
end

#= adds the external functions in list<DAE.Function> to the set of instantiated functions =#
function addDaeExtFunction(inCache::Cache, funcs::List{<:DAE.Function} #= fully qualified function name =#) ::Cache
  local outCache::Cache

  outCache = begin
    local ef::MutableType{DAE.FunctionTree}
    local igraph::Option{Graph}
    local ht::StructuralParameters
    local p::Absyn.Path
    @match (inCache, funcs) begin
      (CACHE(_, ef, _, _), _)  => begin
        Mutable.update(ef, DAEUtil.addDaeExtFunction(funcs, Mutable.access(ef)))
        inCache
      end

      _  => begin
        inCache
      end
    end
  end
  outCache
end

function setCachedFunctionTree(inCache::Cache, inFunctions::DAE.FunctionTree)
  _ = begin
    @match inCache begin
      CACHE(__)  => begin
        Mutable.update(inCache.functions, inFunctions)
        ()
      end

      _  => begin
        ()
      end
    end
  end
end

#= author BZ 2008-06
This function checks wheter an InstStatus is typed or not.
Currently used by Inst.updateComponentsInEnv. =#
function isTyped(is::Status) ::Bool
  local b::Bool

  b = begin
    @match is begin
      VAR_UNTYPED(__)  => begin
        false
      end

      _  => begin
        true
      end
    end
  end
  b
end

#= Returns true if the status indicates a deleted conditional component,
otherwise false. =#
function isDeletedComp(status::Status) ::Bool
  local isDeleted::Bool

  isDeleted = begin
    @match status begin
      VAR_DELETED(__)  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  isDeleted
end

#= get the initial environment from the cache =#
function getCachedInitialGraph(cache::Cache) ::Graph
  local g::Graph

  g = begin
    @match cache begin
      CACHE(initialGraph = SOME(g))  => begin
        g
      end
    end
  end
  g
end

#= set the initial environment in the cache =#
function setCachedInitialGraph(cache::Cache, g::Graph) ::Cache


  cache = begin
    @match cache begin
      CACHE(__)  => begin
        cache.initialGraph = SOME(g)
        cache
      end

      _  => begin
        cache
      end
    end
  end
  cache
end

#= @author: adrpo
adds suffix FCore.recordConstructorSuffix ($recordconstructor)
to the given name. does not do it for MetaModelica =#
function getRecordConstructorName(inName::Name) ::Name
  local outName::Name

  outName = if Config.acceptMetaModelicaGrammar()
    inName
  else
    inName + recordConstructorSuffix
  end
  outName
end

function getRecordConstructorPath(inPath::Absyn.Path) ::Absyn.Path
  local outPath::Absyn.Path

  local lastId::Name

  if Config.acceptMetaModelicaGrammar()
    outPath = inPath
  else
    lastId = AbsynUtil.pathLastIdent(inPath)
    lastId = getRecordConstructorName(lastId)
    outPath = AbsynUtil.pathSetLastIdent(inPath, AbsynUtil.makeIdentPathFromString(lastId))
  end
  outPath
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

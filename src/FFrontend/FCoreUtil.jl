module FCoreUtil

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
#= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


using FCore
import Absyn
import SCode
import DAE
import DAEUtil
import Mutable
import AvlSetCR
using Mutable: MutableType


function next(inext::Next) ::Next
  local onext::Next

  onext = inext + 1
  onext
end

#= returns an empty cache =#
function emptyCache() ::Cache
  local cache::Cache

  local instFuncs::MutableType #= {DAE.FunctionTree} =#
  local ht::StructuralParameters

  instFuncs = Mutable.create(DAE.AvlTreePathFunction.EMPTY())
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
    local functions::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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
    local ef::MutableType #= {DAE.FunctionTree} =#
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

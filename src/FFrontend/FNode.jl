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

module FNode

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

FunctionRefIs = Function

Filter = Function

FunctionRefIs = Function

Apply = Function

@importDBG Absyn
@importDBG AbsynUtil
@importDBG DAE
@importDBG SCode
@importDBG FCore
@importDBG Error
@importDBG ListUtil
@importDBG Config
@importDBG Flags
@importDBG SCodeUtil
print("After imports in FNode")
Name = FCore.Name
Names = FCore.Names
Id = FCore.Id
Seq = FCore.Seq
Next = FCore.Next
Node = FCore.Node
Data = FCore.Data
Kind = FCore.Kind
MMRef = FCore.MMRef
Refs = FCore.Refs
import FCore.RefTree
@importDBG FCoreUtil
Children = FCore.Children
Parents = FCore.Parents
Scope = FCore.Scope
ImportTable = FCore.ImportTable
Graph = FCore.Graph
Extra = FCore.Extra
Visited = FCore.Visited
Import = FCore.Import
  const extendsPrefix = "ext_" #= prefix of the extends node =#::Name
const topNodeName = "top"::Name
#=  these names are used mostly for edges in the graph
=#
#=  the edges are saved inside the AvlTree (\"name\", MMRef)
=#
const tyNodeName = "ty" #= type node =#::Name
const ftNodeName = "ft" #= function types node =#::Name
const refNodeName = "ref" #= reference node =#::Name
const modNodeName = "mod" #= modifier node =#::Name
const bndNodeName = "bnd" #= binding node =#::Name
const cndNodeName = "cnd" #= conditional component condition =#::Name
const dimsNodeName = "dims" #= dimensions node =#::Name
const tydimsNodeName = "tydims" #= type dimensions node =#::Name
const subsNodeName = "subs" #= cref subscripts =#::Name
const ccNodeName = "cc" #= constrain class node =#::Name
const eqNodeName = "eq" #= equation =#::Name
const ieqNodeName = "ieq" #= initial equation =#::Name
const alNodeName = "al" #= algorithm =#::Name
const ialNodeName = "ial" #= initial algorithm =#::Name
const optNodeName = "opt" #= optimization node =#::Name
const edNodeName = "ed" #= external declaration node =#::Name
const forNodeName = "for" #= scope for for-iterators =#::Name
const matchNodeName = "match" #= scope for match exps =#::Name
const cloneNodeName = "clone" #= clone of the reference node =#::Name
const origNodeName = "original" #= the original of the clone =#::Name
const feNodeName = "functionEvaluation" #= a node for function evaluation =#::Name
const duNodeName = "definedUnits" #= a node for storing defined units =#::Name
const veNodeName = "ve" #= a node for storing references to instance component =#::Name
const imNodeName = "imp" #= an node holding the import table =#::Name
const itNodeName = "it" #= an node holding the instance information DAE.Var =#::Name
const assertNodeName = "assert" #= an assersion node =#::Name
const statusNodeName = "status" #= an status node =#::Name

#= @author: adrpo
turns a node into a ref =#
function toRef(inNode::Node) ::MMRef
  local outRef::MMRef

  outRef = arrayCreate(1, inNode)
  outRef
end

#= @author: adrpo
turns a ref into a node =#
function fromRef(inRef::MMRef) ::Node
  local outNode::Node

  outNode = arrayGet(inRef, 1)
  outNode
end

#= @author: adrpo
sets a node into a ref =#
function updateRef(inRef::MMRef, inNode::Node) ::MMRef
  local outRef::MMRef

  outRef = arrayUpdate(inRef, 1, inNode)
  outRef
end

function id(inNode::Node) ::Id
  local id::Id

  @match FCore.N(id = id) = inNode
  id
end

function parents(inNode::Node) ::Parents
  local p::Parents

  @match FCore.N(parents = p) = inNode
  p
end

function hasParents(inNode::Node) ::Bool
  local b::Bool

  b = ! listEmpty(parents(inNode))
  b
end

function refParents(inRef::MMRef) ::Parents
  local p::Parents

  @match FCore.N(parents = p) = fromRef(inRef)
  p
end

function refPushParents(inRef::MMRef, inParents::Parents) ::MMRef
  local outRef::MMRef

  local n::Name
  local i::Id
  local p::Parents
  local c::Children
  local d::Data

  @match FCore.N(n, i, p, c, d) = fromRef(inRef)
  p = listAppend(inParents, p)
  outRef = updateRef(inRef, FCore.N(n, i, p, c, d))
  outRef
end

function setParents(inNode::Node, inParents::Parents) ::Node
  local outNode::Node

  local n::Name
  local i::Id
  local p::Parents
  local c::Children
  local d::Data

  @match FCore.N(n, i, p, c, d) = inNode
  outNode = FCore.N(n, i, inParents, c, d)
  outNode
end

#= returns a target from a REF node =#
function target(inNode::Node) ::MMRef
  local outRef::MMRef

  @match _cons(outRef, _) = targetScope(inNode)
  outRef
end

#= returns the target scope from a REF node =#
function targetScope(inNode::Node) ::Scope
  local outScope::Scope

  outScope = begin
    @match inNode begin
      FCore.N(data = FCore.REF(target = outScope))  => begin
        outScope
      end
    end
  end
  outScope
end

function new(inName::Name, inId::Id, inParents::Parents, inData::Data) ::Node
  local node::Node

  node = FCore.N(inName, inId, inParents, RefTree.EMPTY(), inData)
  node
end

#= add import to the import table =#
function addImport(inImport::SCode.Element, inImportTable::ImportTable) ::ImportTable
  local outImportTable::ImportTable

  outImportTable = begin
    local imp::Import
  local qual_imps::List{Import}
    local unqual_imps::List{Import}
    local info::SourceInfo
    local hidden::Bool
    #=  Unqualified imports
    =#
    @match (inImport, inImportTable) begin
      (SCode.IMPORT(imp = imp && Absyn.UNQUAL_IMPORT(__)), FCore.IMPORT_TABLE(hidden, qual_imps, unqual_imps))  => begin
        unqual_imps = ListUtil.unionElt(imp, unqual_imps)
        FCore.IMPORT_TABLE(hidden, qual_imps, unqual_imps)
      end

      (SCode.IMPORT(imp = imp, info = info), FCore.IMPORT_TABLE(hidden, qual_imps, unqual_imps))  => begin
        imp = translateQualifiedImportToNamed(imp)
        checkUniqueQualifiedImport(imp, qual_imps, info)
        qual_imps = ListUtil.unionElt(imp, qual_imps)
        FCore.IMPORT_TABLE(hidden, qual_imps, unqual_imps)
      end
    end
  end
  #=  Qualified imports
  =#
  outImportTable
end

function toConnectorTypeNoState(scodeConnectorType::SCode.ConnectorType, flowName::Option{<:DAE.ComponentRef} = NONE()) ::DAE.ConnectorType
  local daeConnectorType::DAE.ConnectorType

  daeConnectorType = begin
    @match scodeConnectorType begin
      SCode.FLOW(__)  => begin
        DAE.FLOW()
      end

      SCode.STREAM(__)  => begin
        DAE.STREAM(flowName)
      end

      _  => begin
        DAE.POTENTIAL()
      end
    end
  end
  daeConnectorType
end

#= Translates a qualified import to a named import. =#
function translateQualifiedImportToNamed(inImport::Import) ::Import
  local outImport::Import

  outImport = begin
    local name::Name
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

#= Checks that a qualified import is unique, because it's not allowed to have
qualified imports with the same name. =#
function checkUniqueQualifiedImport(inImport::Import, inImports::List{<:Import}, inInfo::SourceInfo)
  _ = begin
    local name::Name
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
    local name1::Name
    local name2::Name
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

function printElementConflictError(newRef::MMRef, oldRef::MMRef, name::RefTree.Key) ::MMRef
  local dummy::MMRef

  local info1::SourceInfo
  local info2::SourceInfo

  if Config.acceptMetaModelicaGrammar()
    dummy = newRef
  else
    info1 = SCodeUtil.elementInfo(FNode.getElementFromRef(newRef))
    info2 = SCodeUtil.elementInfo(FNode.getElementFromRef(oldRef))
    Error.addMultiSourceMessage(Error.DOUBLE_DECLARATION_OF_ELEMENTS, list(name), list(info2, info1))
    fail()
  end
  dummy
end

function addChildRef(inParentRef::MMRef, inName::Name, inChildRef::MMRef, checkDuplicate::Bool = false)
  local n::Name
  local i::ModelicaInteger
  local p::Parents
  local c::Children
  local d::Data
  local parent::MMRef

  @match FCore.N(n, i, p, c, d) = fromRef(inParentRef)
  #@show RefTree.keyCompare
  #@show methods(RefTree.keyCompare)
  c = RefTree.add(c, inName, inChildRef,
        if checkDuplicate
          printElementConflictError
        else
         RefTree.addConflictReplace
       end)
  parent = updateRef(inParentRef, FCore.N(n, i, p, c, d))
end

function addImportToRef(ref::MMRef, imp::SCode.Element)
  local n::Name
  local id::ModelicaInteger
  local p::Parents
  local c::Children
  local d::Data
  local e::SCode.Element
  local t::Kind
  local it::ImportTable
  local r::MMRef

  @match FCore.N(n, id, p, c, FCore.IM(it)) = fromRef(ref)
  it = addImport(imp, it)
  r = updateRef(ref, FCore.N(n, id, p, c, FCore.IM(it)))
end

function addTypesToRef(ref::MMRef, inTys::List{<:DAE.Type})
  local n::Name
  local id::ModelicaInteger
  local p::Parents
  local c::Children
  local d::Data
  local e::SCode.Element
  local t::Kind
  local it::ImportTable
  local tys::List{DAE.Type}
  local r::MMRef

  @match FCore.N(n, id, p, c, FCore.FT(tys)) = fromRef(ref)
  tys = ListUtil.unique(listAppend(inTys, tys))
  #=  update the child
  =#
  r = updateRef(ref, FCore.N(n, id, p, c, FCore.FT(tys)))
end

function addIteratorsToRef(ref::MMRef, inIterators::Absyn.ForIterators)
  local n::Name
  local id::ModelicaInteger
  local p::Parents
  local c::Children
  local d::Data
  local e::SCode.Element
  local t::Kind
  local it::Absyn.ForIterators
  local r::MMRef

  @match FCore.N(n, id, p, c, FCore.FS(it)) = fromRef(ref)
  it = listAppend(it, inIterators)
  #=  update the child
  =#
  r = updateRef(ref, FCore.N(n, id, p, c, FCore.FS(it)))
end

function addDefinedUnitToRef(ref::MMRef, du::SCode.Element)
  local n::Name
  local id::ModelicaInteger
  local p::Parents
  local c::Children
  local d::Data
  local e::SCode.Element
  local t::Kind
  local it::ImportTable
  local r::MMRef
  local dus::List{SCode.Element}

  @match FCore.N(n, id, p, c, FCore.DU(dus)) = fromRef(ref)
  r = updateRef(ref, FCore.N(n, id, p, c, FCore.DU(_cons(du, dus))))
end

function name(n::Node) ::String
  local name::String

  name = begin
    local s::String
    @match n begin
      FCore.N(name = s)  => begin
        s
      end
    end
  end
  name
end

function refName(r::MMRef) ::String
  local n::String

  n = name(fromRef(r))
  n
end

function data(n::Node) ::Data
  local d::Data

  d = begin
    @match n begin
      FCore.N(data = d)  => begin
        d
      end
    end
  end
  d
end

function refData(r::MMRef) ::Data
  local outData::Data

  outData = data(fromRef(r))
  outData
end

#= @author: adrpo
return the top node ref =#
function top(inRef::MMRef) ::MMRef
  local outTop::MMRef

  outTop = inRef
  while hasParents(fromRef(outTop))
    outTop = original(parents(fromRef(outTop)))
  end
  outTop
end

function children(inNode::Node) ::Children
  local outChildren::Children

  @match FCore.N(children = outChildren) = inNode
  outChildren
end

function hasChild(inNode::Node, inName::Name) ::Bool
  local b::Bool

  b = begin
    @matchcontinue (inNode, inName) begin
      (_, _)  => begin
        _ = childFromNode(inNode, inName)
        true
      end

      _  => begin
        false
      end
    end
  end
  b
end

function refHasChild(inRef::MMRef, inName::Name) ::Bool
  local b::Bool

  b = hasChild(fromRef(inRef), inName)
  b
end

function setChildren(inNode::Node, inChildren::Children) ::Node
  local outNode::Node

  local n::Name
  local i::Id
  local p::Parents
  local c::Children
  local d::Data

  @match FCore.N(n, i, p, c, d) = inNode
  outNode = FCore.N(n, i, p, inChildren, d)
  outNode
end

function setData(inNode::Node, inData::Data) ::Node
  local outNode::Node

  local n::Name
  local i::Id
  local p::Parents
  local c::Children
  local d::Data

  @match FCore.N(n, i, p, c, _) = inNode
  outNode = FCore.N(n, i, p, c, inData)
  outNode
end

function child(inParentRef::MMRef, inName::Name)::MMRef
  childFromNode(fromRef(inParentRef), inName)
end

function childFromNode(inNode::Node, inName::Name)::MMRef
  RefTree.get(children(inNode), inName)
end

function element2Data(inElement::SCode.Element, inKind::Kind)::Tuple{Data, DAE.Var}
  local outVar::DAE.Var
  local outData::Data

  (outData, outVar) = begin
    local n::String
    local finalPrefix::SCode.Final
    local repl::SCode.Replaceable
    local vis::SCode.Visibility
    local ct::SCode.ConnectorType
    local redecl::SCode.Redeclare
    local io::Absyn.InnerOuter
    local attr::SCode.Attributes
    local ad::List{Absyn.Subscript}
    local prl::SCode.Parallelism
    local var::SCode.Variability
    local dir::Absyn.Direction
    local t::Absyn.TypeSpec
    local m::SCode.Mod
    local comment::SCode.Comment
    local info::SourceInfo
    local condition::Option{Absyn.Exp}
    local nd::Data
    local i::DAE.Var
    #=  a component
    =#
    @match (inElement, inKind) begin
      (SCode.COMPONENT(n, SCode.PREFIXES(vis, _, _, io, _), SCode.ATTR(_, ct, prl, var, dir), _, _, _, _, _), _)  => begin
        nd = FCore.CO(inElement, DAE.NOMOD(), inKind, FCore.VAR_UNTYPED())
        i = DAE.TYPES_VAR(n, DAE.ATTR(toConnectorTypeNoState(ct), prl, var, dir, io, vis), DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE())
        (nd, i)
      end
    end
  end
  (outData, outVar)
end

function dataStr(inData::Data) ::String
  local outStr::String

  outStr = begin
    local n::Name
    local c::Absyn.ComponentRef
    local m::String
    @match inData begin
      FCore.TOP(__)  => begin
        "TOP"
      end

      FCore.IT(_)  => begin
        "I"
      end

      FCore.CL(e = SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)))  => begin
        "CE"
      end

      FCore.CL(__)  => begin
        "C"
      end

      FCore.CO(__)  => begin
        "c"
      end

      FCore.EX(__)  => begin
        "E"
      end

      FCore.DU(_)  => begin
        "U"
      end

      FCore.FT(_)  => begin
        "FT"
      end

      FCore.AL(_, _)  => begin
        "ALG"
      end

      FCore.EQ(_, _)  => begin
        "EQ"
      end

      FCore.OT(_, _)  => begin
        "OPT"
      end

      FCore.ED(_)  => begin
        "ED"
      end

      FCore.FS(_)  => begin
        "FS"
      end

      FCore.FI(_)  => begin
        "FI"
      end

      FCore.MS(_)  => begin
        "MS"
      end

      FCore.MO(_)  => begin
        "M"
      end

      FCore.EXP(name = n)  => begin
        n
      end

      FCore.DIMS(name = n)  => begin
        n
      end

      FCore.CR(_)  => begin
        "r"
      end

      FCore.CC(_)  => begin
        "CC"
      end

      FCore.ND(_)  => begin
        "ND"
      end

      FCore.REF(_)  => begin
        "REF"
      end

      FCore.VR(__)  => begin
        "VR"
      end

      FCore.IM(_)  => begin
        "IM"
      end

      FCore.ASSERT(m)  => begin
        "assert(" + m + ")"
      end

      _  => begin
        "UKNOWN NODE DATA"
      end
    end
  end
  outStr
end

function toStr(inNode::Node) ::String
  local outStr::String

  outStr = begin
    local n::Name
    local i::Id
    local p::Parents
    local c::Children
    local d::Data
    @matchcontinue inNode begin
      FCore.N(_, i, p, _, d)  => begin
        outStr = "[i:" + intString(i) + "] " + "[p:" + stringDelimitList(ListUtil.mymap(ListUtil.mymap(ListUtil.mymap(p, fromRef), id), intString), ", ") + "] " + "[n:" + name(inNode) + "] " + "[d:" + dataStr(d) + "]"
        outStr
      end

      _  => begin
        "Unhandled node!"
      end
    end
  end
  outStr
end

#= returns the path from top to this node =#
function toPathStr(inNode::Node) ::String
  local outStr::String

  outStr = begin
    local n::Name
    local id::Id
    local p::Parents
    local c::Children
    local d::Data
    local nr::MMRef
    local s::String
    #=  top node
    =#
    @matchcontinue inNode begin
      FCore.N(_, _,  nil(), _, _)  => begin
        outStr = name(inNode)
        outStr
      end

      FCore.N(_, _, p, _, _)  => begin
        nr = contextual(p)
        @match true = hasParents(fromRef(nr))
        s = toPathStr(fromRef(nr))
        outStr = s + "." + name(inNode)
        outStr
      end

      FCore.N(_, _, p, _, _)  => begin
        nr = contextual(p)
        @match false = hasParents(fromRef(nr))
        outStr = "." + name(inNode)
        outStr
      end
    end
  end
  outStr
end

#= note that this function returns the scopes in reverse =#
function scopeStr(sc::Scope) ::String
  local s::String
  s = stringDelimitList(ListUtil.mymap(listReverse(sc), refName), "/")
  s
end


#= @author: adrpo
returns the first NON implicit
reference from the given scope! =#
function nonImplicitRefFromScope(inScope::Scope) ::MMRef
  local outRef::MMRef

  outRef = begin
    local r::MMRef
    local rest::Scope
    @match inScope begin
      nil()  => begin
        fail()
      end

      r <| _ where (! isRefImplicitScope(r))  => begin
        r
      end

      _ <| rest  => begin
        nonImplicitRefFromScope(rest)
      end
    end
  end
  outRef
end

#= @author: adrpo
returns the names of parents up
to the given name. if the name
is not found up to the top the
empty list is returned.
note that for A.B.C.D.E.F searching for B from F will give you
{C, D, E, F} =#
function namesUpToParentName(inRef::MMRef, inName::Name) ::Names
  local outNames::Names

  outNames = namesUpToParentName_dispatch(inRef, inName, nil)
  outNames
end

#= @author: adrpo
returns the names of parents up
to the given name. if the name
is not found up to the top the
empty list is returned.
note that for A.B.C.D.E.F searching for B from F will give you
{C, D, E, F} =#
function namesUpToParentName_dispatch(inRef::MMRef, inName::Name, acc::Names) ::Names
  local outNames::Names

  outNames = begin
    local r::MMRef
    local names::Names
    local name::Name
    #=  bah, error!
    =#
    @match (inRef, inName, acc) begin
      (r, _, _) where (isRefTop(r))  => begin
        nil
      end

      (r, _, _) where (stringEq(inName, refName(r)))  => begin
        acc
      end

      (r, name, _)  => begin
        namesUpToParentName_dispatch(original(refParents(r)), name, _cons(refName(r), acc))
      end
    end
  end
  #=  we're done, return
  =#
  #=  up the parent
  =#
  outNames
end

#= @author: adrpo
returns the target of the modifer =#
function getModifierTarget(inRef::MMRef) ::MMRef
  local outRef::MMRef

  outRef = begin
    local r::MMRef
    #=  bah, error!
    =#
    @matchcontinue inRef begin
      r where (isRefTop(r))  => begin
        fail()
      end

      r where (isRefModHolder(r))  => begin
        r = original(refParents(r))
        @match _cons(r, _) = refRefTargetScope(r)
        r
      end

      _  => begin
        getModifierTarget(original(refParents(inRef)))
      end
    end
  end
  #=  we're done, return
  =#
  #=  get his parent
  =#
  #=  up the parent
  =#
  outRef
end

#= @author:
return the scope from this ref to the top as a list of references.
NOTE:
the starting point reference is included and
the scope is returned reversed, from leafs
to top =#
function originalScope(inRef::MMRef) ::Scope
  local outScope::Scope

  outScope = originalScope_dispatch(inRef, nil)
  outScope
end

#= @author:
return the scope from this ref to the top as a list of references.
NOTE:
the starting point reference is included and
the scope is returned reversed, from leafs
to top =#
function originalScope_dispatch(inRef::MMRef, inAcc::Scope) ::Scope
  local outScope::Scope

  outScope = begin
    local acc::Scope
    local r::MMRef
    #=  top
    =#
    @match (inRef, inAcc) begin
      (_, acc) where (isTop(fromRef(inRef)))  => begin
        listReverse(_cons(inRef, acc))
      end

      (_, acc)  => begin
        r = original(parents(fromRef(inRef)))
        originalScope_dispatch(r, _cons(inRef, acc))
      end
    end
  end
  #=  not top
  =#
  outScope
end

#= @author:
return the original parent from the parents (the last one) =#
function original(inParents::Parents) ::MMRef
  local outOriginal::MMRef

  outOriginal = ListUtil.last(inParents)
  outOriginal
end

#= @author:
return the scope from this ref to the top as a list of references.
NOTE:
the starting point reference is included and
the scope is returned reversed, from leafs
to top =#
function contextualScope(inRef::MMRef) ::Scope
  local outScope::Scope

  outScope = contextualScope_dispatch(inRef, nil)
  outScope
end

#= @author:
return the scope from this ref to the top as a list of references.
NOTE:
the starting point reference is included and
the scope is returned reversed, from leafs
to top =#
function contextualScope_dispatch(inRef::MMRef, inAcc::Scope) ::Scope
  local outScope::Scope

  outScope = begin
    local acc::Scope
    local r::MMRef
    #=  top
    =#
    @match (inRef, inAcc) begin
      (_, acc) where (isTop(fromRef(inRef)))  => begin
        listReverse(_cons(inRef, acc))
      end

      (_, acc)  => begin
        r = contextual(parents(fromRef(inRef)))
        contextualScope_dispatch(r, _cons(inRef, acc))
      end
    end
  end
  #=  not top
  =#
  outScope
end

#= @author:
return the contextual parent from the parents (the first one) =#
function contextual(inParents::Parents) ::MMRef
  local outContextual::MMRef

  outContextual = listHead(inParents)
  outContextual
end

#= @author: adrpo
lookup a reference based on given scope names
NOTE:
inRef/outRef could be in a totally different graph =#
function lookupRef(inRef::MMRef, inScope::Scope) ::MMRef
  local outRef::MMRef

  outRef = begin
    local s::Scope
    local r::MMRef
    #=  for the top, return itself
    =#
    @matchcontinue (inRef, inScope) begin
      (_, _ <|  nil())  => begin
        inRef
      end

      (_, s)  => begin
        @match _cons(_, s) = listReverse(s)
        r = lookupRef_dispatch(inRef, s)
        r
      end
    end
  end
  #=  print(\"Searching for scope: \" + toPathStr(fromRef(listHead(s))) + \" in \" + toPathStr(fromRef(inRef)) + \"\\n\");
  =#
  #=  reverse and remove top
  =#
  outRef
end

#= @author: adrpo
lookup a reference based on given scope names
NOTE:
inRef/outRef could be in a totally different graph =#
function lookupRef_dispatch(inRef::MMRef, inScope::Scope) ::MMRef
  local outRef::MMRef

  outRef = begin
    local r::MMRef
    local rest::Scope
    local n::Name
    @match (inRef, inScope) begin
      (_,  nil())  => begin
        inRef
      end

      (_, r <| rest)  => begin
        n = name(fromRef(r))
        r = child(inRef, n)
        r = lookupRef_dispatch(r, rest)
        r
      end
    end
  end
  #=  print(\"Lookup child: \" + n + \" in \" + toPathStr(fromRef(inRef)) + \"\\n\");
  =#
  outRef
end

#= @author: adrpo
filter the children of the given
reference by the given filter =#
function filter(inRef::MMRef, inFilter::Filter) ::Refs
  local filtered::Refs

  local c::Children

  c = children(fromRef(inRef))
  filtered = RefTree.fold(c, (inFilter) -> filter_work(filter = inFilter), nil)
  filtered = listReverse(filtered)
  filtered
end

function filter_work(name::Name, ref::MMRef, filter::Filter, accum::Refs) ::Refs
  local refs::Refs = accum

  if filter(ref)
    refs = _cons(ref, refs)
  end
  refs
end

function isRefExtends(inRef::MMRef) ::Bool
  local b::Bool

  b = isExtends(fromRef(inRef))
  b
end

function isRefDerived(inRef::MMRef) ::Bool
  local b::Bool

  b = isDerived(fromRef(inRef))
  b
end

function isRefComponent(inRef::MMRef) ::Bool
  local b::Bool

  b = isComponent(fromRef(inRef))
  b
end

function isRefConstrainClass(inRef::MMRef) ::Bool
  local b::Bool

  b = isConstrainClass(fromRef(inRef))
  b
end

function isRefClass(inRef::MMRef) ::Bool
  local b::Bool

  b = isClass(fromRef(inRef))
  b
end

function isRefInstance(inRef::MMRef) ::Bool
  local b::Bool

  b = isInstance(fromRef(inRef))
  b
end

function isRefRedeclare(inRef::MMRef) ::Bool
  local b::Bool

  b = isRedeclare(fromRef(inRef))
  b
end

function isRefClassExtends(inRef::MMRef) ::Bool
  local b::Bool

  b = isClassExtends(fromRef(inRef))
  b
end

function isRefCref(inRef::MMRef) ::Bool
  local b::Bool

  b = isCref(fromRef(inRef))
  b
end

function isRefReference(inRef::MMRef) ::Bool
  local b::Bool

  b = isReference(fromRef(inRef))
  b
end

function isRefUserDefined(inRef::MMRef) ::Bool
  local b::Bool

  b = isUserDefined(fromRef(inRef))
  b
end

function isRefTop(inRef::MMRef) ::Bool
  local b::Bool

  b = isTop(fromRef(inRef))
  b
end

function isRefBasicType(inRef::MMRef) ::Bool
  local b::Bool

  b = isBasicType(fromRef(inRef))
  b
end

function isRefBuiltin(inRef::MMRef) ::Bool
  local b::Bool

  b = isBuiltin(fromRef(inRef))
  b
end

function isRefFunction(inRef::MMRef) ::Bool
  local b::Bool

  b = isFunction(fromRef(inRef))
  b
end

function isRefRecord(inRef::MMRef) ::Bool
  local b::Bool

  b = isRecord(fromRef(inRef))
  b
end

function isRefSection(inRef::MMRef) ::Bool
  local b::Bool

  b = isSection(fromRef(inRef))
  b
end

function isRefMod(inRef::MMRef) ::Bool
  local b::Bool

  b = isMod(fromRef(inRef))
  b
end

function isRefModHolder(inRef::MMRef) ::Bool
  local b::Bool

  b = isModHolder(fromRef(inRef))
  b
end

function isRefClone(inRef::MMRef) ::Bool
  local b::Bool

  b = isClone(fromRef(inRef))
  b
end

function isRefVersion(inRef::MMRef) ::Bool
  local b::Bool

  b = isVersion(fromRef(inRef))
  b
end

function isRefDims(inRef::MMRef) ::Bool
  local b::Bool

  b = isDims(fromRef(inRef))
  b
end

function isRefIn(inRef::MMRef, inFunctionRefIs::FunctionRefIs) ::Bool
  local b::Bool

  b = isIn(fromRef(inRef), inFunctionRefIs)
  b
end

#= @author: adrpo
return all refs as given by
depth first search =#
function dfs(inRef::MMRef) ::Refs
  local outRefs::Refs

  outRefs = begin
    local refs::Refs
    local c::Children
    @match inRef begin
      _  => begin
        c = children(fromRef(inRef))
        refs = RefTree.listValues(c)
        refs = ListUtil.flatten(ListUtil.mymap(refs, dfs))
        refs = _cons(inRef, refs)
        refs
      end
    end
  end
  outRefs
end

#= @author: adrpo
apply a function on all the subtree pointed by given ref.
the order of application is dfs. =#
function apply1(inRef, inApply, inExtraArg)
  local outExtraArg
  outExtraArg = RefTree.fold(children(fromRef(inRef)), inApply, inExtraArg)
  outExtraArg = inApply(refName(inRef), inRef, outExtraArg)
  outExtraArg
end

function hasImports(inNode::Node) ::Bool
  local b::Bool

  b = begin
    local qi::List{Import}
    local uqi::List{Import}
    @match inNode begin
      _  => begin
        @match FCore.IMPORT_TABLE(_, qi, uqi) = importTable(fromRef(refImport(toRef(inNode))))
        b = boolOr(! listEmpty(qi), ! listEmpty(uqi))
        b
      end

      _  => begin
        false
      end
    end
  end
  b
end

function imports(inNode::Node) ::Tuple{List{Import}, List{Import}}
  local outUnQualifiedImports::List{Import}
  local outQualifiedImports::List{Import}

  (outQualifiedImports, outUnQualifiedImports) = begin
    local qi::List{Import}
    local uqi::List{Import}
    @match inNode begin
      _  => begin
        @match FCore.IMPORT_TABLE(_, qi, uqi) = importTable(fromRef(refImport(toRef(inNode))))
        (qi, uqi)
      end

      _  => begin
        (nil, nil)
      end
    end
  end
  (outQualifiedImports, outUnQualifiedImports)
end

function derivedRef(inRef::MMRef) ::Refs
  local outRefs::Refs

  outRefs = begin
    local r::MMRef
    @match inRef begin
      _ where (isRefDerived(inRef))  => begin
        list(child(inRef, refNodeName))
      end

      _  => begin
        nil
      end
    end
  end
  outRefs
end

function extendsRefs(inRef::MMRef) ::Refs
  local outRefs::Refs

  outRefs = begin
    local refs::Refs
    local rd::Refs
    @match inRef begin
      _ where (isRefClass(inRef))  => begin
        rd = derivedRef(inRef)
        refs = filter(inRef, isRefExtends)
        refs = ListUtil.flatten(ListUtil.map1(refs, filter, isRefReference))
        refs = listAppend(rd, refs)
        refs
      end

      _  => begin
        nil
      end
    end
  end
  #=  we have a class
  =#
  #=  get the derived ref
  =#
  #=  get the extends
  =#
  outRefs
end

#= @author: adrpo
clone a node ref entire subtree
the clone will have 2 parents
{inParentRef, originalParentRef} =#
function cloneRef(inName::Name, inRef::MMRef, inParentRef::MMRef, inGraph::Graph) ::Tuple{Graph, MMRef}
  local outRef::MMRef
  local outGraph::Graph

  (outGraph, outRef) = begin
    local n::Node
    local g::Graph
    local r::MMRef
    @match (inName, inRef, inParentRef, inGraph) begin
      (_, _, _, g)  => begin
        (g, r) = clone(fromRef(inRef), inParentRef, g)
        addChildRef(inParentRef, inName, r)
        (g, r)
      end
    end
  end
  (outGraph, outRef)
end

#= @author: adrpo
clone a node entire subtree
the clone will have 2 parents
{inParentRef, originalParentRef} =#
function clone(inNode::Node, inParentRef::MMRef, inGraph::Graph) ::Tuple{Graph, MMRef}
  local outRef::MMRef
  local outGraph::Graph

  (outGraph, outRef) = begin
    local n::Node
    local g::Graph
    local r::MMRef
    local name::Name
    local id::Id
    local parents::Parents
    local children::Children
    local data::Data
    @match (inNode, inParentRef, inGraph) begin
      (FCore.N(name, id, parents, children, data), _, g)  => begin
        parents = _cons(inParentRef, parents)
        @match (g, (@match FCore.N(name, id, parents, _, data) = n)) = node(g, name, parents, data)
        r = toRef(n)
        (g, children) = cloneTree(children, r, g)
        r = updateRef(r, FCore.N(name, id, parents, children, data))
        (g, r)
      end
    end
  end
  #=  add parent
  =#
  #=  create node clone
  =#
  #=  make the reference to the new node
  =#
  #=  clone children
  =#
  #=  set the children in the new node
  =#
  (outGraph, outRef)
end

#= @author: adrpo
clone a node entire subtree
the clone will have 2 parents
{inParentRef, originalParentRef} =#
function cloneTree(inChildren::Children, inParentRef::MMRef, inGraph::Graph) ::Tuple{Graph, Children}
  local outChildren::Children
  local outGraph::Graph

  (outChildren, outGraph) = RefTree.mapFold(inChildren, (inParentRef) -> cloneChild(parentRef = inParentRef), inGraph)
  (outGraph, outChildren)
end

function cloneChild(name::Name, parentRef::MMRef, inRef::MMRef, inGraph::Graph) ::Tuple{MMRef, Graph}
  local graph::Graph
  local ref::MMRef

  (graph, ref) = cloneRef(name, inRef, parentRef, inGraph)
  (ref, graph)
end

#= @author: adrpo
copy a node ref entire subtree
this is like clone but the parents are kept as they are =#
function copyRef(inRef::MMRef, inGraph::Graph) ::Tuple{Graph, MMRef}
  local outRef::MMRef
  local outGraph::Graph

  (outGraph, outRef) = begin
    local n::Node
    local g::Graph
    local r::MMRef
    @match (inRef, inGraph) begin
      (_, g)  => begin
        r = copyRefNoUpdate(inRef)
        (g, r) = updateRefs(r, g)
        (g, r)
      end
    end
  end
  #=  first copy the entire tree as it is
  =#
  #=  generating new array references
  =#
  #=  then update all array references
  =#
  #=  in the tree to their new places
  =#
  (outGraph, outRef)
end

#= @author: adrpo
update all parent and node data references in the graph =#
function updateRefs(inRef::MMRef, inGraph::Graph) ::Tuple{Graph, MMRef}
  local outRef::MMRef
  local outGraph::Graph

  (outGraph, outRef) = begin
    local n::Node
    local g::Graph
    local r::MMRef
    @match (inRef, inGraph) begin
      (_, g)  => begin
        (r, g) = apply1(inRef, updateRefInGraph, (inRef, g))
        (g, r)
      end
    end
  end
  #=  for each node in the tree
  =#
  #=  update all refs from the node parents or node data
  =#
  (outGraph, outRef)
end

function updateRefInGraph(name::Name, inRef::MMRef, inTopRefAndGraph::Tuple{<:MMRef, Graph}) ::Tuple{MMRef, Graph}
  local outTopRefAndGraph::Tuple{MMRef, Graph}

  outTopRefAndGraph = begin
    local r::MMRef
    local t::MMRef
    local g::Graph
    local n::Name
    local i::Id
    local p::Parents
    local c::Children
    local d::Data
    @match (inRef, inTopRefAndGraph) begin
      (_, (t, g))  => begin
        @match FCore.N(n, i, p, c, d) = fromRef(inRef)
        p = ListUtil.map1r(p, lookupRefFromRef, t)
        d = updateRefInData(d, t)
        _ = updateRef(inRef, FCore.N(n, i, p, c, d))
        (t, g)
      end
    end
  end
  #=  print(\"Updating references in node: \" + toStr(fromRef(inRef)) + \" / [\" + toPathStr(fromRef(inRef)) + \"]\\n\");
  =#
  outTopRefAndGraph
end

#= @author: adrpo
lookup a reference based on old reference in a different graph =#
function lookupRefFromRef(inRef::MMRef, inOldRef::MMRef) ::MMRef
  local outRef::MMRef

  outRef = begin
    local r::MMRef
    local s::Scope
    @match (inRef, inOldRef) begin
      (_, _)  => begin
        s = originalScope(inOldRef)
        r = lookupRef(inRef, s)
        r
      end
    end
  end
  #=  get the original scope from the old ref
  =#
  outRef
end

#= @author: adrpo
update references in the node data currently just REF and CLONE hold other references.
if you add more nodes in FCore that have references in them you need to update this function too! =#
function updateRefInData(inData::Data, inRef::MMRef) ::Data
  local outData::Data

  outData = begin
    local oldRef::MMRef
    local r::MMRef
    local e::SCode.Element
    local i::DAE.Var
    local m::DAE.Mod
    local s::FCore.Status
    local k::Kind
    local sc::Scope
    @match (inData, inRef) begin
      (FCore.REF(sc), _)  => begin
        sc = ListUtil.map1r(sc, lookupRefFromRef, inRef)
        FCore.REF(sc)
      end

      _  => begin
        inData
      end
    end
  end
  outData
end

#= @author: adrpo
copy a node ref entire subtree =#
function copyRefNoUpdate(inRef::MMRef) ::MMRef
  local outRef::MMRef = copy(fromRef(inRef))
  outRef
end

#= @author: adrpo
copy a node entire subtree.
this is like clone but the parents are kept as they are =#
function copy(inNode::Node) ::MMRef
  local outRef::MMRef

  local node::Node = inNode

  outRef = begin
    @match node begin
      FCore.N(n, i, p, c, d)  => begin
        #=  copy children
        =#
        k = RefTree.mymap(c, copyChild)
        node = FCore.N(n, i, p, k, d)
        toRef(node)
      end
    end
  end
  outRef
end

function copyChild(name::Name, inRef::MMRef) ::MMRef
  local ref::MMRef = copyRefNoUpdate(inRef)
  ref
end

#= @author: adrpo
get element from the node data =#
function getElement(inNode::Node) ::SCode.Element
  local outElement::SCode.Element

  outElement = begin
    local e::SCode.Element
    @match inNode begin
      FCore.N(data = FCore.CL(e = e))  => begin
        e
      end

      FCore.N(data = FCore.CO(e = e))  => begin
        e
      end
    end
  end
  outElement
end

#= @author: adrpo
get element from the ref =#
function getElementFromRef(inRef::MMRef) ::SCode.Element
  local outElement::SCode.Element

  outElement = getElement(fromRef(inRef))
  outElement
end

#= returns true if the node ref is a for-loop scope or a valueblock scope.
This is indicated by the name of the frame. =#
function isImplicitRefName(r::MMRef) ::Bool
  local b::Bool

  b = begin
    @match r begin
      _ where (! isRefTop(r))  => begin
        FCore.isImplicitScope(refName(r))
      end

      _  => begin
        false
      end
    end
  end
  b
end

#= @author: adrpo
get the DAE.Var from the child node named itNodeName of this reference =#
function refInstVar(inRef::MMRef) ::DAE.Var
  local v::DAE.Var

  local r::MMRef

  r = refInstance(inRef)
  @match FCore.IT(i = v) = refData(r)
  v
end

function refInstance(inRef::MMRef) ::MMRef
  local r::MMRef

  r = child(inRef, itNodeName)
  r
end

function isRefRefUnresolved(inRef::MMRef) ::Bool
  local b::Bool

  b = begin
    @matchcontinue inRef begin
      _  => begin
        _ = refRef(inRef)
        b = listEmpty(refRefTargetScope(inRef))
        b
      end

      _  => begin
        true
      end
    end
  end
  #=  node exists
  =#
  #=  with non empty scope
  =#
  b
end

function isRefRefResolved(inRef::MMRef) ::Bool
  local b::Bool

  b = ! isRefRefUnresolved(inRef)
  b
end

function refRef(inRef::MMRef) ::MMRef
  local r::MMRef

  r = child(inRef, refNodeName)
  r
end

function refRefTargetScope(inRef::MMRef) ::Scope
  local sc::Scope

  local r::MMRef

  r = refRef(inRef)
  sc = targetScope(fromRef(r))
  sc
end

function refImport(inRef::MMRef) ::MMRef
  local r::MMRef

  r = child(inRef, imNodeName)
  r
end

#= returns the import table from a IM node =#
function importTable(inNode::Node) ::ImportTable
  local it::ImportTable

  it = begin
    @match inNode begin
      FCore.N(data = FCore.IM(i = it))  => begin
        it
      end
    end
  end
  it
end

function mkExtendsName(inPath::Absyn.Path) ::Name
  local outName::Name

  outName = extendsPrefix + AbsynUtil.pathString(inPath)
  outName
end

function scopeHashWork(scope::Scope, hash::ModelicaInteger) ::ModelicaInteger


  for r in scope
    hash = 31 * hash + stringHashDjb2(FNode.refName(r))
  end
  hash
end

function scopePathEq(scope1::Scope, scope2::Scope) ::Bool
  local eq::Bool

  eq = min(@do_threaded_for FNode.refName(r1) == FNode.refName(r2) (r1, r2) (scope1, scope2))
  eq
end


#= make a new node in the graph =#
function node(inGraph::Graph, inName::Name, inParents::Parents, inData::Data) ::Tuple{Graph, Node}
  local outNode::Node
  local outGraph::Graph
  (outGraph, outNode) = begin
    local i::ModelicaInteger
    local b::Bool
    local id::Id
    local g::Graph
    local n::Node
    @match (inGraph, inName, inParents, inData) begin
      (g, _, _, _)  => begin
        i = System.tmpTickIndex(Global.fgraph_nextId)
                      n = FNode.new(inName, i, inParents, inData)
        (g, n)
      end
    end
  end
  (outGraph, outNode)
end


#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

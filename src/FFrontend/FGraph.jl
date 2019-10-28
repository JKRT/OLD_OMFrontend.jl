
#= /*
* This file is part of OpenModelica.
*
* Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
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

module FGraph


using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll

import Absyn
import AbsynUtil
import SCode
import DAE
import Prefix
import ClassInf
import FCore

const Name = FCore.Name
const Id = FCore.Id
const Seq = FCore.Seq
const Next = FCore.Next
const Node = FCore.Node
const Data = FCore.Data
const Kind = FCore.Kind
const MMRef = FCore.MMRef
const Refs = FCore.Refs
const RefTree = FCore.RefTree
const Children = FCore.Children
const Parents = FCore.Parents
const Scope = FCore.Scope
const Top = FCore.Top
const Graph = FCore.Graph
println("Graph = FCore.Graph")
const Extra = FCore.Extra
const Visited = FCore.Visited
const Status = FCore.Status
const emptyGraph = FCore.EG("empty")

import FNode
import InnerOuter

import ListUtil
import Util
import System
import Debug
import FGraphStream
import FGraphBuildEnv
import Global
import Config
import PrefixUtil
import Flags
import SCodeDump
import MetaModelica.Dangerous
import Mod
import Error
import ComponentReference
import Types
import SCodeUtil

         #= get the top node ref from the graph =#
        function top(inGraph::Graph) ::MMRef
              local outRef::MMRef

              outRef = begin
                @match inGraph begin
                  FCore.G(__)  => begin
                    inGraph.top.node
                  end
                end
              end
          outRef
        end

         #= get the extra from the graph =#
        function extra(inGraph::Graph) ::Extra
              local outExtra::Extra

              outExtra = begin
                @match inGraph begin
                  FCore.G(__)  => begin
                    inGraph.top.extra
                  end
                end
              end
          outExtra
        end

         #= get the top current scope from the graph =#
        function currentScope(inGraph::Graph) ::Scope
              local outScope::Scope

              outScope = begin
                @match inGraph begin
                  FCore.G(scope = outScope)  => begin
                    outScope
                  end

                  FCore.EG(_)  => begin
                    nil
                  end
                end
              end
          outScope
        end

         #= get the last ref from the current scope the graph =#
        function lastScopeRef(inGraph::Graph) ::MMRef
              local outRef::MMRef

              outRef = listHead(currentScope(inGraph))
          outRef
        end

        function setLastScopeRef(inRef::MMRef, inGraph::Graph) ::Graph
              local outGraph::Graph = inGraph

              outGraph = begin
                @match outGraph begin
                  FCore.G(__)  => begin
                      outGraph.scope = _cons(inRef, listRest(outGraph.scope))
                    outGraph
                  end

                  _  => begin
                      outGraph
                  end
                end
              end
          outGraph
        end

         #= remove the last ref from the current scope the graph =#
        function stripLastScopeRef(inGraph::Graph) ::Tuple{Graph, MMRef}
              local outRef::MMRef
              local outGraph::Graph

              local t::Top
              local s::Scope

              @match FCore.G(t, _cons(outRef, s)) = inGraph
               #=  strip the last scope ref
               =#
              outGraph = FCore.G(t, s)
          (outGraph, outRef)
        end

         #= remove all the scopes, leave just the top one from the graph scopes =#
        function topScope(inGraph::Graph) ::Graph
              local outGraph::Graph

              local t::MMRef
              local r::MMRef
              local s::Scope
              local gn::Name
              local v::Visited
              local e::Extra
              local next::Next

               #=  leave only the top scope
               =#
              outGraph = begin
                @match inGraph begin
                  FCore.G(__)  => begin
                    arrayGet(inGraph.top.graph, 1)
                  end
                end
              end
          outGraph
        end

         #= make an empty graph =#
        function empty() ::Graph
              local outGraph::Graph

              outGraph = emptyGraph
          outGraph
        end

         #= make a new graph =#
        function new(inGraphName::Name, inPath)::Graph
              local outGraph::Graph

              local n::Node
              local s::Scope
              local v::Visited
              local nr::MMRef
              local next::Next
              local id::Id
              local ag::Array{Graph}
              local top::Top

              id = System.tmpTickIndex(Global.fgraph_nextId)
              n = FNode.new(FNode.topNodeName, id, nil, FCore.TOP())
              nr = FNode.toRef(n)
              s = list(nr)
              ag = Dangerous.arrayCreateNoInit(1, emptyGraph)
              top = FCore.GTOP(ag, inGraphName, nr, FCore.EXTRA(inPath))
              outGraph = FCore.G(top, s)
               #=  Creates a cycle, but faster to get the initial environment
               =#
              arrayUpdate(ag, 1, FCore.G(top, list(nr)))
              FGraphStream.node(n)
          outGraph
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
                      FGraphStream.node(n)
                    (g, n)
                  end
                end
              end
               #=  uncomment this if unique node id's are not unique!
               =#
               #= /*
                      b = (id == i);
                      Debug.bcall1(true, print, \"Next: \" + intString(id) + \" <-> \" + intString(i) + \" node: \" + FNode.toStr(n) + \"\\n\");
                       true = b;
                      */ =#
          (outGraph, outNode)
        end

         #= @author: adrpo
         clone a graph. everything is copied except visited information and refs (which will be new) =#
        function clone(inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local t::Top
                  local nt::MMRef
                  local gn::Name
                  local s::Scope
                  local v::Visited
                  local e::Extra
                  local n::Next #= next node id for this graph =#
                  local ag::Array{Graph}
                @match inGraph begin
                  FCore.G(t, s)  => begin
                      nt = FNode.toRef(FNode.fromRef(t.node))
                      (g, nt) = FNode.copyRef(nt, inGraph)
                      s = ListUtil.map1r(s, FNode.lookupRefFromRef, nt)
                      ag = arrayCreate(1, emptyGraph)
                      t = FCore.GTOP(ag, t.name, nt, t.extra)
                      g = FCore.G(t, s)
                      arrayUpdate(ag, 1, g)
                    g
                  end
                end
              end
               #=  make a new top
               =#
               #=  make new graph
               =#
               #=  g = FCore.G(t, s);
               =#
               #=  deep copy the top, clone the entire subtree, update references
               =#
               #=  update scope references
               =#
          outGraph
        end

         #= This function updates a component already added to the graph, but
         that prior to the update did not have any binding. I.e this function is
         called in the second stage of instantiation with declare before use. =#
        function updateComp(inGraph::Graph, inVar::DAE.Var, instStatus::FCore.Status, inTargetGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local pr::MMRef
                  local r::MMRef
                  local n::Name
                  local id::Id
                  local p::Parents
                  local c::Children
                  local e::SCode.Element
                  local i::DAE.Var
                  local v::DAE.Var
                  local m::DAE.Mod
                  local s::Status
                  local k::Kind
                  local sc::Scope
                  local g::Graph
                   #=  update in the current frame
                   =#
                @matchcontinue (inGraph, inVar, instStatus, inTargetGraph) begin
                  (g, v && DAE.TYPES_VAR(name = n), _, _)  => begin
                      pr = lastScopeRef(g)
                      r = FNode.child(pr, n)
                      @match FCore.N(n, id, p, c, FCore.CO(e, m, k, _)) = FNode.fromRef(r)
                      r = FNode.updateRef(r, FCore.N(n, id, p, c, FCore.CO(e, m, k, instStatus)))
                      r = updateSourceTargetScope(r, currentScope(inTargetGraph))
                      r = updateInstance(r, v)
                    g
                  end

                  (g, v, _, _)  => begin
                      pr = lastScopeRef(g)
                      @match true = FNode.isImplicitRefName(pr)
                      (g, _) = stripLastScopeRef(g)
                      g = updateComp(g, v, instStatus, inTargetGraph)
                    g
                  end

                  _  => begin
                      inGraph
                  end
                end
              end
               #=  update the target scope
               =#
               #=  if not found update in the parent frame
               =#
               #=  do NOT fail!
               =#
          outGraph
        end

         #= update the class scope in the source =#
        function updateSourceTargetScope(inRef::MMRef, inTargetScope::Scope) ::MMRef
              local outRef::MMRef

              outRef = begin
                  local pr::MMRef
                  local r::MMRef
                  local g::Graph
                  local sc::Scope
                   #=  update the target scope of the node, hopefully existing
                   =#
                @matchcontinue (inRef, inTargetScope) begin
                  (r, _)  => begin
                      r = FNode.refRef(r)
                      r = FNode.updateRef(r, FNode.setData(FNode.fromRef(r), FCore.REF(inTargetScope)))
                    inRef
                  end

                  (r, _)  => begin
                      Error.addCompilerWarning("FNode.updateSourceTargetScope: node does not yet have a reference child: " + FNode.toPathStr(FNode.fromRef(r)) + " target scope: " + FNode.scopeStr(inTargetScope) + "\\n")
                    inRef
                  end
                end
              end
               #=  create one and update it
               =#
          outRef
        end

         #= update the class scope in the source =#
        function updateInstance(inRef::MMRef, inVar::DAE.Var) ::MMRef
              local outRef::MMRef

              outRef = begin
                  local pr::MMRef
                  local r::MMRef
                  local g::Graph
                  local sc::Scope
                   #=  update the instance node
                   =#
                @matchcontinue (inRef, inVar) begin
                  (r, _)  => begin
                      r = FNode.refInstance(r)
                      r = FNode.updateRef(r, FNode.setData(FNode.fromRef(r), FCore.IT(inVar)))
                    inRef
                  end

                  _  => begin
                        Error.addCompilerError("FGraph.updateInstance failed for node: " + FNode.toPathStr(FNode.fromRef(inRef)) + " variable:" + Types.printVarStr(inVar))
                      fail()
                  end
                end
              end
          outRef
        end

         #= update the component data =#
        function updateVarAndMod(inGraph::Graph, inVar::DAE.Var, inMod::DAE.Mod, instStatus::FCore.Status, inTargetGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local pr::MMRef
                  local r::MMRef
                  local n::Name
                  local id::Id
                  local p::Parents
                  local c::Children
                  local e::SCode.Element
                  local i::DAE.Var
                  local v::DAE.Var
                  local m::DAE.Mod
                  local s::Status
                  local k::Kind
                  local sc::Scope
                  local g::Graph
                   #=  update in the current frame
                   =#
                @matchcontinue (inGraph, inVar, inMod, instStatus, inTargetGraph) begin
                  (g, v && DAE.TYPES_VAR(name = n), _, _, _)  => begin
                      pr = lastScopeRef(g)
                      r = FNode.child(pr, n)
                      @match FCore.N(n, id, p, c, FCore.CO(e, _, k, _)) = FNode.fromRef(r)
                      r = FNode.updateRef(r, FCore.N(n, id, p, c, FCore.CO(e, inMod, k, instStatus)))
                      r = updateSourceTargetScope(r, currentScope(inTargetGraph))
                      r = updateInstance(r, v)
                    g
                  end

                  (g, v, _, _, _)  => begin
                      pr = lastScopeRef(g)
                      @match true = FNode.isImplicitRefName(pr)
                      (g, _) = stripLastScopeRef(g)
                      g = updateVarAndMod(g, v, inMod, instStatus, inTargetGraph)
                    g
                  end

                  _  => begin
                      inGraph
                  end
                end
              end
               #=  if not found update in the parent frame
               =#
               #=  do NOT fail!
               =#
          outGraph
        end

         #= This function updates a class element in the graph =#
        function updateClass(inGraph::Graph, inElement::SCode.Element, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, instStatus::FCore.Status, inTargetGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local pr::MMRef
                  local r::MMRef
                  local n::Name
                  local id::Id
                  local p::Parents
                  local c::Children
                  local e::SCode.Element
                  local k::Kind
                  local sc::Scope
                  local g::Graph
                  local s::Status
                  local m::DAE.Mod
                  local pre::Prefix.PrefixType
                   #=  update in the current frame
                   =#
                @matchcontinue (inGraph, inElement, inPrefix, inMod, instStatus, inTargetGraph) begin
                  (g, e && SCode.CLASS(name = n), _, _, _, _)  => begin
                      pr = lastScopeRef(g)
                      r = FNode.child(pr, n)
                      @match FCore.N(n, id, p, c, FCore.CL(_, _, _, k, _)) = FNode.fromRef(r)
                      r = FNode.updateRef(r, FCore.N(n, id, p, c, FCore.CL(e, inPrefix, inMod, k, instStatus)))
                    g
                  end

                  (g, e, _, _, _, _)  => begin
                      pr = lastScopeRef(g)
                      @match true = FNode.isImplicitRefName(pr)
                      (g, _) = stripLastScopeRef(g)
                      g = updateClass(g, e, inPrefix, inMod, instStatus, inTargetGraph)
                    g
                  end
                end
              end
               #=  r = updateSourceTargetScope(r, currentScope(inTargetGraph));
               =#
               #=  if not found update in the parent frame
               =#
          outGraph
        end

         #= This function updates a class element in the given parent ref =#
        function updateClassElement(inRef::MMRef, inElement::SCode.Element, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, instStatus::FCore.Status, inTargetGraph::Graph) ::MMRef
              local outRef::MMRef

              outRef = begin
                  local pr::MMRef
                  local r::MMRef
                  local n::Name
                  local id::Id
                  local p::Parents
                  local c::Children
                  local e::SCode.Element
                  local k::Kind
                  local sc::Scope
                  local g::Graph
                  local s::Status
                  local m::DAE.Mod
                  local pre::Prefix.PrefixType
                @match (inRef, inElement, inPrefix, inMod, instStatus, inTargetGraph) begin
                  (r, e && SCode.CLASS(name = n), _, _, _, _)  => begin
                      @match FCore.N(_, id, p, c, FCore.CL(_, _, _, k, _)) = FNode.fromRef(r)
                      r = FNode.updateRef(r, FCore.N(n, id, p, c, FCore.CL(e, inPrefix, inMod, k, instStatus)))
                    r
                  end
                end
              end
          outRef
        end

         #= Adds a for loop iterator to the graph. =#
        function addForIterator(inGraph::Graph, name::String, ty::DAE.Type, binding::DAE.Binding, variability::SCode.Variability, constOfForIteratorRange::Option{<:DAE.Const}) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local r::MMRef
                  local c::SCode.Element
                  local v::DAE.Var
                @match (inGraph, name, ty, binding, variability, constOfForIteratorRange) begin
                  (g, _, _, _, _, _)  => begin
                      c = SCode.COMPONENT(name, SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.CONST(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)
                      v = DAE.TYPES_VAR(name, DAE.ATTR(DAE.NON_CONNECTOR(), SCode.NON_PARALLEL(), variability, Absyn.BIDIR(), Absyn.NOT_INNER_OUTER(), SCode.PUBLIC()), ty, binding, constOfForIteratorRange)
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkCompNode(c, r, FCore.BUILTIN(), g)
                      g = updateVarAndMod(g, v, DAE.NOMOD(), FCore.VAR_UNTYPED(), empty())
                    g
                  end
                end
              end
               #=  update the var too!
               =#
          outGraph
        end

         #= Retrive the graph current scope path as a string =#
        function printGraphPathStr(inGraph::Graph) ::String
              local outString::String

              outString = begin
                  local str::String
                  local s::Scope
                @matchcontinue inGraph begin
                  FCore.G(scope = s && _ <| _ <| _)  => begin
                      @match _cons(_, s) = listReverse(s)
                      str = stringDelimitList(ListUtil.map(s, FNode.refName), ".")
                    str
                  end

                  _  => begin
                      "<global scope>"
                  end
                end
              end
               #=  remove top
               =#
          outString
        end

         #= Opening a new scope in the graph means adding a new node in the current scope. =#
        function openNewScope(inGraph::Graph, encapsulatedPrefix::SCode.Encapsulated, inName::Option{<:Name}, inScopeType::Option{<:FCore.ScopeType}) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Name
                  local no::Node
                  local r::MMRef
                  local p::MMRef
                   #=  else open a new scope!
                   =#
                @matchcontinue (inGraph, encapsulatedPrefix, inName, inScopeType) begin
                  (g, _, SOME(n), _)  => begin
                      p = lastScopeRef(g)
                      (g, no) = node(g, n, list(p), FCore.ND(inScopeType))
                      r = FNode.toRef(no)
                      g = pushScopeRef(g, r)
                    g
                  end

                  _  => begin
                        Error.addCompilerError("FGraph.openNewScope: failed to open new scope in scope: " + getGraphNameStr(inGraph) + " name: " + Util.stringOption(inName) + "\\n")
                      fail()
                  end
                end
              end
               #=  FNode.addChildRef(p, n, r);
               =#
          outGraph
        end

         #= Opening a new scope in the graph means adding a new node in the current scope. =#
        function openScope(inGraph::Graph, encapsulatedPrefix::SCode.Encapsulated, inName::Name, inScopeType::Option{<:FCore.ScopeType}) ::Graph
              local outGraph::Graph

              local p::MMRef

              p = lastScopeRef(inGraph)
              outGraph = begin
                  local g::Graph
                  local gComp::Graph
                  local n::Name
                  local no::Node
                  local r::MMRef
                  local sc::Scope
                   #=  see if we have it as a class instance
                   =#
                @matchcontinue (inGraph, encapsulatedPrefix, inName, inScopeType) begin
                  (g, _, n, _)  => begin
                      r = FNode.child(p, n)
                      @match FCore.CL(status = FCore.CLS_INSTANCE(_)) = FNode.refData(r)
                      FNode.addChildRef(p, n, r)
                      g = pushScopeRef(g, r)
                    g
                  end

                  (g, _, n, _)  => begin
                      r = FNode.child(p, n)
                      r = FNode.copyRefNoUpdate(r)
                      g = pushScopeRef(g, r)
                    g
                  end

                  (g, _, n, _)  => begin
                      (g, no) = node(g, n, list(p), FCore.ND(inScopeType))
                      r = FNode.toRef(no)
                      g = pushScopeRef(g, r)
                    g
                  end

                  _  => begin
                        Error.addCompilerError("FGraph.openScope: failed to open new scope in scope: " + getGraphNameStr(inGraph) + " name: " + inName + "\\n")
                      fail()
                  end
                end
              end
               #=  see if we have a child with the same name!
               =#
               #=  FNode.addChildRef(p, n, r);
               =#
               #=  else open a new scope!
               =#
               #=  FNode.addChildRef(p, n, r);
               =#
          outGraph
        end

         #= returns true if environment has a frame that is a for loop =#
        function inForLoopScope(inGraph::Graph) ::Bool
              local res::Bool

              res = begin
                  local name::String
                @matchcontinue inGraph begin
                  _  => begin
                      name = FNode.refName(listHead(currentScope(inGraph)))
                      @match true = stringEq(name, FCore.forScopeName)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if environment has a frame that is a for iterator 'loop' =#
        function inForOrParforIterLoopScope(inGraph::Graph) ::Bool
              local res::Bool

              res = begin
                  local name::String
                @matchcontinue inGraph begin
                  _  => begin
                      name = FNode.refName(listHead(currentScope(inGraph)))
                      @match true = stringEq(name, FCore.forIterScopeName) || stringEq(name, FCore.parForIterScopeName)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= get the current scope as a path from the graph =#
        function getScopePath(inGraph::Graph) ::Option{Absyn.Path}
              local outPath::Option{Absyn.Path}

              outPath = begin
                  local p::Absyn.Path
                  local r::MMRef
                @matchcontinue inGraph begin
                  _  => begin
                      @match r <| nil = currentScope(inGraph)
                      @match true = FNode.isRefTop(r)
                    NONE()
                  end

                  _  => begin
                      p = getGraphName(inGraph)
                    SOME(p)
                  end
                end
              end
          outPath
        end

         #= Returns the FQ name of the environment. =#
        function getGraphNameStr(inGraph::Graph) ::String
              local outString::String

              outString = begin
                @matchcontinue inGraph begin
                  _  => begin
                    AbsynUtil.pathString(getGraphName(inGraph))
                  end

                  _  => begin
                      "."
                  end
                end
              end
          outString
        end

         #= Returns the FQ name of the environment. =#
        function getGraphName(inGraph::Graph) ::Absyn.Path
              local outPath::Absyn.Path

              local p::Absyn.Path
              local s::Scope
              local r::MMRef

              @match _cons(r, s) = currentScope(inGraph)
              p = AbsynUtil.makeIdentPathFromString(FNode.refName(r))
              for r in s
                p = Absyn.QUALIFIED(FNode.refName(r), p)
              end
              @match Absyn.QUALIFIED(_, outPath) = p
          outPath
        end

         #= Returns the FQ name of the environment. =#
        function getGraphNameNoImplicitScopes(inGraph::Graph) ::Absyn.Path
              local outPath::Absyn.Path

              local p::Absyn.Path
              local s::Scope

              @match _cons(_, s) = listReverse(currentScope(inGraph))
              outPath = AbsynUtil.stringListPath(list(str for str in list(FNode.refName(n) for n in s) if stringGet(str, 1) != 36))
               #= /* \"$\" */ =#
          outPath
        end

         #= @author:adrpo
         push the given ref as first element in the graph scope list =#
        function pushScopeRef(graph::Graph, inRef::MMRef) ::Graph


              _ = begin
                @match graph begin
                  FCore.G(t, s)  => begin
                      graph = FCore.G(t, _cons(inRef, graph.scope))
                    ()
                  end
                end
              end
          graph
        end

         #= @author:adrpo
         put the given scope in the graph scope at the begining (listAppend(inScope, currentScope(graph))) =#
        function pushScope(graph::Graph, inScope::Scope) ::Graph


              _ = begin
                @match graph begin
                  FCore.G(t, s)  => begin
                      graph = FCore.G(t, listAppend(inScope, graph.scope))
                    ()
                  end
                end
              end
          graph
        end

         #= @author:adrpo
         replaces the graph scope with the given scope =#
        function setScope(graph::Graph, inScope::Scope) ::Graph


              _ = begin
                @match graph begin
                  FCore.G(t, s)  => begin
                      graph.scope = FCore.G(t, inScope)
                    ()
                  end
                end
              end
          graph
        end

        function restrictionToScopeType(inRestriction::SCode.Restriction) ::Option{FCore.ScopeType}
              local outType::Option{FCore.ScopeType}

              outType = begin
                @match inRestriction begin
                  SCode.R_FUNCTION(SCode.FR_PARALLEL_FUNCTION(__))  => begin
                    SOME(FCore.PARALLEL_SCOPE())
                  end

                  SCode.R_FUNCTION(SCode.FR_KERNEL_FUNCTION(__))  => begin
                    SOME(FCore.PARALLEL_SCOPE())
                  end

                  SCode.R_FUNCTION(_)  => begin
                    SOME(FCore.FUNCTION_SCOPE())
                  end

                  _  => begin
                      SOME(FCore.CLASS_SCOPE())
                  end
                end
              end
          outType
        end

         #= Converts a ScopeType to a Restriction. Restriction is much more expressive
           than ScopeType, so the returned Restriction is more of a rough indication of
           what the original Restriction was. =#
        function scopeTypeToRestriction(inScopeType::FCore.ScopeType) ::SCode.Restriction
              local outRestriction::SCode.Restriction

              outRestriction = begin
                @match inScopeType begin
                  FCore.PARALLEL_SCOPE(__)  => begin
                    SCode.R_FUNCTION(SCode.FR_PARALLEL_FUNCTION())
                  end

                  FCore.FUNCTION_SCOPE(__)  => begin
                    SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(false))
                  end

                  _  => begin
                      SCode.R_CLASS()
                  end
                end
              end
          outRestriction
        end

         #= Returns true if we are in the top-most scope =#
        function isTopScope(graph::Graph) ::Bool
              local isTop::Bool

              isTop = begin
                @matchcontinue graph begin
                  _  => begin
                      @match true = FNode.isRefTop(lastScopeRef(graph))
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isTop
        end

         #= Removes the entire environment prefix from the given component reference, or
          returns the unchanged reference. This is done because models might import
          local packages, for example:

            package P
              import myP = InsideP;

              package InsideP
                function f end f;
              end InsideP;

              constant c = InsideP.f();
            end P;

            package P2
              extends P;
            end P2;

          When P2 is instantiated all elements from P will be brought into P2's scope
          due to the extends. The binding of c will still point to P.InsideP.f though, so
          the lookup will try to instantiate P which might fail if P is a partial
          package or for other reasons. This is really a bug in Lookup (it shouldn't
          need to instantiate the whole package just to find a function), but to work
          around this problem for now this function will remove the environment prefix
          when InsideP.f is looked up in P, so that it resolves to InsideP.f and not
          P.InsideP.f. This allows P2 to find it in the local scope instead, since the
          InsideP package has been inherited from P. =#
        function crefStripGraphScopePrefix(inCref::Absyn.ComponentRef, inEnv::Graph, stripPartial::Bool) ::Absyn.ComponentRef
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local env_path::Absyn.Path
                  local cref1::Absyn.ComponentRef
                  local cref2::Absyn.ComponentRef
                @matchcontinue (inCref, inEnv, stripPartial) begin
                  (_, _, _)  => begin
                      @match false = Flags.isSet(Flags.STRIP_PREFIX)
                    inCref
                  end

                  (_, _, _)  => begin
                      @match SOME(env_path) = getScopePath(inEnv)
                      cref1 = AbsynUtil.unqualifyCref(inCref)
                      env_path = AbsynUtil.makeNotFullyQualified(env_path)
                      cref2 = crefStripGraphScopePrefix2(cref1, env_path, stripPartial)
                      @match false = AbsynUtil.crefEqual(cref1, cref2)
                    cref2
                  end

                  _  => begin
                      inCref
                  end
                end
              end
               #=  try to strip as much as possible
               =#
               #=  check if we really did anything, fail if we did nothing!
               =#
          outCref
        end

        function crefStripGraphScopePrefix2(inCref::Absyn.ComponentRef, inEnvPath::Absyn.Path, stripPartial::Bool) ::Absyn.ComponentRef
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local id1::Absyn.Ident
                  local id2::Absyn.Ident
                  local cref::Absyn.ComponentRef
                  local env_path::Absyn.Path
                @matchcontinue (inCref, inEnvPath, stripPartial) begin
                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil(), componentRef = cref), Absyn.QUALIFIED(name = id2, path = env_path), _)  => begin
                      @match true = stringEqual(id1, id2)
                    crefStripGraphScopePrefix2(cref, env_path, stripPartial)
                  end

                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil(), componentRef = cref), Absyn.IDENT(name = id2), _)  => begin
                      @match true = stringEqual(id1, id2)
                    cref
                  end

                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil()), env_path, true)  => begin
                      @match false = stringEqual(id1, AbsynUtil.pathFirstIdent(env_path))
                    inCref
                  end
                end
              end
               #=  adrpo: leave it as stripped as you can if you can't match it above and we have true for stripPartial
               =#
          outCref
        end

         #= same as pathStripGraphScopePrefix =#
        function pathStripGraphScopePrefix(inPath::Absyn.Path, inEnv::Graph, stripPartial::Bool) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local env_path::Absyn.Path
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                @matchcontinue (inPath, inEnv, stripPartial) begin
                  (_, _, _)  => begin
                      @match false = Flags.isSet(Flags.STRIP_PREFIX)
                    inPath
                  end

                  (_, _, _)  => begin
                      @match SOME(env_path) = getScopePath(inEnv)
                      path1 = AbsynUtil.makeNotFullyQualified(inPath)
                      env_path = AbsynUtil.makeNotFullyQualified(env_path)
                      path2 = pathStripGraphScopePrefix2(path1, env_path, stripPartial)
                      @match false = AbsynUtil.pathEqual(path1, path2)
                    path2
                  end

                  _  => begin
                      inPath
                  end
                end
              end
               #=  try to strip as much as possible
               =#
               #=  check if we really did anything, fail if we did nothing!
               =#
          outPath
        end

        function pathStripGraphScopePrefix2(inPath::Absyn.Path, inEnvPath::Absyn.Path, stripPartial::Bool) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local id1::Absyn.Ident
                  local id2::Absyn.Ident
                  local path::Absyn.Path
                  local env_path::Absyn.Path
                @match (inPath, inEnvPath, stripPartial) begin
                  (Absyn.QUALIFIED(name = id1, path = path), Absyn.QUALIFIED(name = id2, path = env_path), _) where (stringEqual(id1, id2))  => begin
                    pathStripGraphScopePrefix2(path, env_path, stripPartial)
                  end

                  (Absyn.QUALIFIED(name = id1, path = path), Absyn.IDENT(name = id2), _) where (stringEqual(id1, id2))  => begin
                    path
                  end

                  (Absyn.QUALIFIED(name = id1), env_path, true) where (! stringEqual(id1, AbsynUtil.pathFirstIdent(env_path)))  => begin
                    inPath
                  end
                end
              end
               #=  adrpo: leave it as stripped as you can if you can't match it above and stripPartial is true
               =#
          outPath
        end

         #= This function adds a component to the graph. =#
        function mkComponentNode(inGraph::Graph, inVar::DAE.Var, inVarEl::SCode.Element, inMod::DAE.Mod, instStatus::Status, inCompGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local id::Option{Name}
                  local st::Option{FCore.ScopeType}
                  local du::List{SCode.Element}
                  local v::DAE.Var
                  local n::Name
                  local c::SCode.Element
                  local g::Graph
                  local cg::Graph
                  local m::DAE.Mod
                  local r::MMRef
                  local i::FCore.Status
                   #=  Graph of component
                   =#
                @matchcontinue (inGraph, inVar, inVarEl, inMod, instStatus, inCompGraph) begin
                  (_, DAE.TYPES_VAR(name = n), c, _, _, _)  => begin
                      @match false = stringEq(n, SCodeUtil.elementName(c))
                      Error.addCompilerError("FGraph.mkComponentNode: The component name: " + SCodeUtil.elementName(c) + " is not the same as its DAE.TYPES_VAR: " + n + "\\n")
                    fail()
                  end

                  (g, v && DAE.TYPES_VAR(name = n), c, m, i, cg)  => begin
                      @match true = stringEq(n, SCodeUtil.elementName(c))
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkCompNode(c, r, FCore.USERDEFINED(), g)
                      g = updateVarAndMod(g, v, m, i, cg)
                    g
                  end
                end
              end
               #=  maks sure the element name and the DAE.TYPES_VAR name is the same!
               =#
               #=  Graph of component
               =#
               #=  make sure the element name and the DAE.TYPES_VAR name is the same!
               =#
               #=  update the var too!
               =#
          outGraph
        end

         #= This function adds a class definition to the environment.
         Enumeration are expanded from a list into a class with components =#
        function mkClassNode(inGraph::Graph, inClass::SCode.Element, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, checkDuplicate::Bool = false) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Name
                  local g::Graph
                  local r::MMRef
                   #=  already there as class instance, do nothing!
                   =#
                @matchcontinue (inGraph, inClass, inPrefix, inMod) begin
                  (g, SCode.CLASS(name = n), _, _)  => begin
                      r = lastScopeRef(g)
                      r = FNode.child(r, n)
                      @match FCore.CL(status = FCore.CLS_INSTANCE(_)) = FNode.refData(r)
                    g
                  end

                  (g, SCode.CLASS(__), _, _)  => begin
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkClassNode(inClass, inPrefix, inMod, r, FCore.USERDEFINED(), g, checkDuplicate)
                    g
                  end
                end
              end
          outGraph
        end

         #= This function adds a class definition to the environment.
         Enumeration are expanded from a list into a class with components =#
        function mkTypeNode(inGraph::Graph, inName::Name, inType::DAE.Type) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Name
                  local g::Graph
                  local r::MMRef
                @match (inGraph, inName, inType) begin
                  (g, _, _)  => begin
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkTypeNode(list(inType), r, inName, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= This function adds a class definition to the environment.
         Enumeration are expanded from a list into a class with components =#
        function mkImportNode(inGraph::Graph, inImport::SCode.Element) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Name
                  local g::Graph
                  local r::MMRef
                @match (inGraph, inImport) begin
                  (g, _)  => begin
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkElementNode(inImport, r, FCore.USERDEFINED(), g)
                    g
                  end
                end
              end
          outGraph
        end

         #= This function adds a class definition to the environment.
         Enumeration are expanded from a list into a class with components =#
        function mkDefunitNode(inGraph::Graph, inDu::SCode.Element) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Name
                  local g::Graph
                  local r::MMRef
                @match (inGraph, inDu) begin
                  (g, _)  => begin
                      r = lastScopeRef(g)
                      g = FGraphBuildEnv.mkElementNode(inDu, r, FCore.USERDEFINED(), g)
                    g
                  end
                end
              end
          outGraph
        end

        function classInfToScopeType(inState::ClassInf.SMNode) ::Option{FCore.ScopeType}
              local outType::Option{FCore.ScopeType}

              outType = begin
                @match inState begin
                  ClassInf.FUNCTION(__)  => begin
                    SOME(FCore.FUNCTION_SCOPE())
                  end

                  _  => begin
                      SOME(FCore.CLASS_SCOPE())
                  end
                end
              end
          outType
        end

         #= returns true if empty graph =#
        function isEmpty(inGraph::Graph) ::Bool
              local b::Bool

              b = begin
                @match inGraph begin
                  FCore.EG(_)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= returns true if not empty graph =#
        function isNotEmpty(inGraph::Graph) ::Bool
              local b::Bool

              b = ! isEmpty(inGraph)
          b
        end

        function isEmptyScope(graph::Graph) ::Bool
              local isEmpty::Bool

              try
                isEmpty = RefTree.isEmpty(FNode.children(FNode.fromRef(lastScopeRef(graph))))
              catch
                isEmpty = true
              end
          isEmpty
        end

         #= prints the graph =#
        function printGraphStr(inGraph::Graph) ::String
              local s::String

              s = "NOT IMPLEMENTED YET"
          s
        end

        function inFunctionScope(inGraph::Graph) ::Bool
              local inFunction::Bool

              inFunction = begin
                  local s::Scope
                  local r::MMRef
                @match inGraph begin
                  FCore.G(scope = s) where (checkScopeType(s, SOME(FCore.FUNCTION_SCOPE())) || checkScopeType(s, SOME(FCore.PARALLEL_SCOPE())))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          inFunction
        end

         #=  Returns the name of a scope, if no name exist, the function fails. =#
        function getScopeName(inGraph::Graph) ::Name
              local name::Name

              name = begin
                  local r::MMRef
                @match inGraph begin
                  _  => begin
                      r = lastScopeRef(inGraph)
                      @match false = FNode.isRefTop(r)
                      name = FNode.refName(r)
                    name
                  end
                end
              end
               #=  not top
               =#
          name
        end

        function checkScopeType(inScope::Scope, inScopeType::Option{<:FCore.ScopeType}) ::Bool
              local yes::Bool

              yes = begin
                  local r::MMRef
                  local rest::Scope
                  local restr::SCode.Restriction
                  local st::Option{FCore.ScopeType}
                @matchcontinue (inScope, inScopeType) begin
                  ( nil(), _)  => begin
                    false
                  end

                  (r <| _, _)  => begin
                      @match true = FNode.isRefClass(r)
                      restr = SCodeUtil.getClassRestriction(FNode.getElement(FNode.fromRef(r)))
                      @match true = valueEq(restrictionToScopeType(restr), inScopeType)
                    true
                  end

                  (r <| _, _)  => begin
                      @match FCore.N(data = FCore.ND(st)) = FNode.fromRef(r)
                      @match true = valueEq(st, inScopeType)
                    true
                  end

                  (_ <| rest, _)  => begin
                    checkScopeType(rest, inScopeType)
                  end
                end
              end
               #=  classes
               =#
               #=  FCore.ND(scopeType)
               =#
          yes
        end

        function lastScopeRestriction(inGraph::Graph) ::SCode.Restriction
              local outRestriction::SCode.Restriction

              local s::Scope

              @match FCore.G(scope = s) = inGraph
              outRestriction = getScopeRestriction(s)
          outRestriction
        end

        function getScopeRestriction(inScope::Scope) ::SCode.Restriction
              local outRestriction::SCode.Restriction

              outRestriction = begin
                  local r::MMRef
                  local st::FCore.ScopeType
                @matchcontinue inScope begin
                  r <| _ where (FNode.isRefClass(r))  => begin
                    SCodeUtil.getClassRestriction(FNode.getElement(FNode.fromRef(r)))
                  end

                  r <| _  => begin
                      @match FCore.N(data = FCore.ND(SOME(st))) = FNode.fromRef(r)
                    scopeTypeToRestriction(st)
                  end

                  _  => begin
                      getScopeRestriction(listRest(inScope))
                  end
                end
              end
          outRestriction
        end

         #= This function returns all partially instantiated parents as an Absyn.Path
         option I.e. it collects all identifiers of each frame until it reaches
         the topmost unnamed frame. If the environment is only the topmost frame,
         NONE() is returned. =#
        function getGraphPathNoImplicitScope(inGraph::Graph) ::Option{Absyn.Path}
              local outAbsynPathOption::Option{Absyn.Path}

              outAbsynPathOption = getGraphPathNoImplicitScope_dispatch(currentScope(inGraph))
          outAbsynPathOption
        end

         #= This function returns all partially instantiated parents as an Absyn.Path
         option I.e. it collects all identifiers of each frame until it reaches
         the topmost unnamed frame. If the environment is only the topmost frame,
         NONE() is returned. =#
        function getGraphPathNoImplicitScope_dispatch(inScope::Scope) ::Option{Absyn.Path}
              local outAbsynPathOption::Option{Absyn.Path}

              local opath::Option{Absyn.Path}

              outAbsynPathOption = begin
                  local id::Name
                  local path::Absyn.Path
                  local path_1::Absyn.Path
                  local rest::Scope
                  local ref::MMRef
                @matchcontinue inScope begin
                  ref <| rest where (! FNode.isRefTop(ref))  => begin
                      id = FNode.refName(ref)
                      if isImplicitScope(id)
                        opath = getGraphPathNoImplicitScope_dispatch(rest)
                      else
                        opath = getGraphPathNoImplicitScope_dispatch(rest)
                        if isSome(opath)
                          @match SOME(path) = opath
                          path_1 = AbsynUtil.joinPaths(path, Absyn.IDENT(id))
                          opath = SOME(path_1)
                        else
                          opath = SOME(Absyn.IDENT(id))
                        end
                      end
                    opath
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          outAbsynPathOption
        end

        function isImplicitScope(inName::Name) ::Bool
              local isImplicit::Bool

              isImplicit = FCore.isImplicitScope(inName)
          isImplicit
        end

         #= Used to join an Graph scope with an Absyn.Path (probably an IDENT) =#
        function joinScopePath(inGraph::Graph, inPath::Absyn.Path) ::Absyn.Path
              local outPath::Absyn.Path

              local opath::Option{Absyn.Path}
              local envPath::Absyn.Path

              opath = getScopePath(inGraph)
              if isSome(opath)
                @match SOME(envPath) = opath
                outPath = AbsynUtil.joinPaths(envPath, inPath)
              else
                outPath = inPath
              end
          outPath
        end

         #= splits out the for loop scope from the graph scope =#
        function splitGraphScope(inGraph::Graph) ::Tuple{Graph, Scope}
              local outForScope::Scope
              local outRealGraph::Graph

              (outRealGraph, outForScope) = splitGraphScope_dispatch(inGraph, nil)
          (outRealGraph, outForScope)
        end

         #= splits out the for loop scope from the graph scope =#
        function splitGraphScope_dispatch(inGraph::Graph, inAcc::Scope) ::Tuple{Graph, Scope}
              local outForScope::Scope
              local outRealGraph::Graph

              (outRealGraph, outForScope) = begin
                  local g::Graph
                  local r::MMRef
                  local s::Scope
                @match (inGraph, inAcc) begin
                  (FCore.EG(_), _)  => begin
                    (inGraph, listReverse(inAcc))
                  end

                  (FCore.G(scope = r <| _), _)  => begin
                      if FNode.isImplicitRefName(r)
                        (g, _) = stripLastScopeRef(inGraph)
                        (g, s) = splitGraphScope_dispatch(g, _cons(r, inAcc))
                      else
                        g = inGraph
                        s = listReverse(inAcc)
                      end
                    (g, s)
                  end
                end
              end
          (outRealGraph, outForScope)
        end

         #= @author: adrpo
          returns the a list with all the variables names in the given graph from the last graph scope =#
        function getVariablesFromGraphScope(inGraph::Graph) ::List{Name}
              local variables::List{Name}

              variables = begin
                  local lst::List{Name}
                  local r::MMRef
                   #=  empty case
                   =#
                @match inGraph begin
                  FCore.EG(_)  => begin
                    nil
                  end

                  FCore.G(scope =  nil())  => begin
                    nil
                  end

                  FCore.G(scope = r <| _)  => begin
                      lst = ListUtil.map(FNode.filter(r, FNode.isRefComponent), FNode.refName)
                    lst
                  end
                end
              end
               #=  some graph, no scope
               =#
               #=  some graph
               =#
          variables
        end

         #= @author:adrpo
         remove the children of the last ref =#
        function removeComponentsFromScope(inGraph::Graph) ::Graph
              local outGraph::Graph

              local r::MMRef
              local n::Node

              r = lastScopeRef(inGraph)
              r = FNode.copyRefNoUpdate(r)
              n = FNode.fromRef(r)
              n = FNode.setChildren(n, RefTree.new())
              r = FNode.updateRef(r, n)
              (outGraph, _) = stripLastScopeRef(inGraph)
              outGraph = pushScopeRef(outGraph, r)
          outGraph
        end

        function cloneLastScopeRef(inGraph::Graph) ::Graph
              local outGraph::Graph

              local r::MMRef

              (outGraph, r) = stripLastScopeRef(inGraph)
              r = FNode.copyRefNoUpdate(r)
              outGraph = pushScopeRef(outGraph, r)
          outGraph
        end

        function updateScope(inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                @match inGraph begin
                  _  => begin
                    inGraph
                  end
                end
              end
          outGraph
        end

         #= @author: adrpo
         THE MOST IMPORTANT FUNCTION IN THE COMPILER :)
         This function works like this:
         From source scope:
           A.B.C.D
         we lookup a target scope
           X.Y.Z.W
         to be used for a component, derived class, or extends
         We get back X.Y.Z + CLASS(W) via lookup.
         We build X.Y.Z.W_newVersion and return it.
         The newVersion name is generated by mkVersionName based on
         the source scope, the element name, prefix and modifiers.
         The newVersion scope is only created if there are non emtpy
         modifiers given to this functions =#
        function mkVersionNode(inSourceEnv::Graph, inSourceName::Name, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, inTargetClassEnv::Graph, inTargetClass::SCode.Element, inIH::InnerOuter.InstHierarchy) ::Tuple{Graph, SCode.Element, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outVersionedTargetClass::SCode.Element
              local outVersionedTargetClassEnv::Graph

              (outVersionedTargetClassEnv, outVersionedTargetClass, outIH) = begin
                  local gclass::Graph
                  local classRef::MMRef
                  local sourceRef::MMRef
                  local targetClassParentRef::MMRef
                  local versionRef::MMRef
                  local n::Node
                  local r::MMRef
                  local crefPrefix::Prefix.PrefixType
                  local sourceScope::Scope
                  local c::SCode.Element
                  local targetClassName::Name
                  local newTargetClassName::Name
                  local ih::InnerOuter.InstHierarchy
                   #= /*
                      case (_, _, _, _, _, _, _)
                        equation
                          c = inTargetClass;
                          gclass = inTargetClassEnv;
                          targetClassName = SCodeUtil.elementName(c);

                          (newTargetClassName, crefPrefix) = mkVersionName(inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, targetClassName);

                           get the last scope from target
                          targetClassParentRef = lastScopeRef(inTargetClassEnv);
                          classRef = FNode.child(targetClassParentRef, newTargetClassName);
                          c = FNode.getElementFromRef(classRef);
                        then
                          (inTargetClassEnv, c, inIH);*/ =#
                @matchcontinue (inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, inTargetClass, inIH) begin
                  (_, _, _, _, _, _, _)  => begin
                      c = inTargetClass
                      gclass = inTargetClassEnv
                      targetClassName = SCodeUtil.elementName(c)
                      (newTargetClassName, crefPrefix) = mkVersionName(inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, targetClassName)
                      sourceRef = FNode.child(lastScopeRef(inSourceEnv), inSourceName)
                      _ = _cons(sourceRef, currentScope(inSourceEnv))
                      targetClassParentRef = lastScopeRef(inTargetClassEnv)
                      classRef = FNode.child(targetClassParentRef, targetClassName)
                      classRef = FNode.copyRefNoUpdate(classRef)
                      @match FCore.CL(e = c) = FNode.refData(classRef)
                      c = SCodeUtil.setClassName(newTargetClassName, c)
                      classRef = updateClassElement(classRef, c, crefPrefix, inMod, FCore.CLS_INSTANCE(targetClassName), empty())
                      FNode.addChildRef(targetClassParentRef, newTargetClassName, classRef)
                      sourceRef = updateSourceTargetScope(sourceRef, _cons(classRef, currentScope(gclass)))
                      ih = inIH
                    (gclass, c, ih)
                  end

                  _  => begin
                        c = inTargetClass
                        targetClassName = SCodeUtil.elementName(c)
                        (newTargetClassName, _) = mkVersionName(inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, targetClassName)
                        Error.addCompilerWarning("FGraph.mkVersionNode: failed to create version node:\\n" + "Instance: CL(" + getGraphNameStr(inSourceEnv) + ").CO(" + inSourceName + ").CL(" + getGraphNameStr(inTargetClassEnv) + "." + targetClassName + SCodeDump.printModStr(Mod.unelabMod(inMod), SCodeDump.defaultOptions) + ")\\n\\t" + newTargetClassName + "\\n")
                      (inTargetClassEnv, inTargetClass, inIH)
                  end
                end
              end
               #=  get the last item in the source env
               =#
               #=  get the last scope from target
               =#
               #=  get the class from class env
               =#
               #=  clone the class
               =#
               #=  check if the name of the class already exists!
               =#
               #=  failure(_ = FNode.child(targetClassParentRef, newTargetClassName));
               =#
               #=  change class name (so unqualified references to the same class reach the original element
               =#
               #= /* FCore.CLS_UNTYPED() */ =#
               #=  parent the classRef
               =#
               #=  update the source target scope
               =#
               #=  we never need to add the instance as inner!
               =#
               #=  ih = InnerOuter.addClassIfInner(c, crefPrefix, gclass, inIH);
               =#
               #= /*
                      print(\"Instance1: CL(\" + getGraphNameStr(inSourceEnv) + \").CO(\" +
                            inSourceName + \").CL(\" + getGraphNameStr(inTargetClassEnv) + \".\" +
                            targetClassName + SCodeDump.printModStr(Mod.unelabMod(inMod), SCodeDump.defaultOptions) + \")\\n\\t\" +
                            newTargetClassName + \"\\n\");*/ =#
          (outVersionedTargetClassEnv, outVersionedTargetClass, outIH)
        end

        function createVersionScope(inSourceEnv::Graph, inSourceName::Name, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, inTargetClassEnv::Graph, inTargetClass::SCode.Element, inIH::InnerOuter.InstHierarchy) ::Tuple{Graph, SCode.Element, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outVersionedTargetClass::SCode.Element
              local outVersionedTargetClassEnv::Graph

              (outVersionedTargetClassEnv, outVersionedTargetClass, outIH) = begin
                  local gclass::Graph
                  local c::SCode.Element
                   #= /*
                      case (_, _, _, _, _, _, _)
                        equation
                          print(AbsynUtil.pathString(PrefixUtil.prefixToPath(inPrefix)) + \" S:\" + getGraphNameStr(inSourceEnv) + \"/\" + inSourceName + \" ||| \" + \"T:\" + getGraphNameStr(inTargetClassEnv) + \"/\" + SCodeUtil.elementName(inTargetClass) + \"\\n\");
                        then
                          fail();*/ =#
                   #=  case (_, _, _, _, _, _, _) then (inTargetClassEnv, inTargetClass, inIH);
                   =#
                   #=  don't do this if there is no modifications on the class
                   =#
                   #=  TODO! FIXME! wonder if we can skip this if it has only a binding, not an actual type modifier
                   =#
                @matchcontinue (inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, inTargetClass, inIH) begin
                  (_, _, _, DAE.NOMOD(__), _, _, _)  => begin
                    (inTargetClassEnv, inTargetClass, inIH)
                  end

                  (_, _, _, DAE.MOD(subModLst =  nil()), _, _, _)  => begin
                    (inTargetClassEnv, inTargetClass, inIH)
                  end

                  (_, _, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar() || isTargetClassBuiltin(inTargetClassEnv, inTargetClass) || inFunctionScope(inSourceEnv) || SCodeUtil.isOperatorRecord(inTargetClass)
                    (inTargetClassEnv, inTargetClass, inIH)
                  end

                  (_, _, _, _, _, _, _)  => begin
                      @match true = stringEq(AbsynUtil.pathFirstIdent(getGraphName(inTargetClassEnv)), "OpenModelica")
                    (inTargetClassEnv, inTargetClass, inIH)
                  end

                  (_, _, _, _, _, _, _)  => begin
                      (gclass, c, outIH) = mkVersionNode(inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, inTargetClass, inIH)
                    (gclass, c, outIH)
                  end
                end
              end
               #=  don't do this for MetaModelica, target class is builtin or builtin type, functions
               =#
               #=  or OpenModelica scripting stuff
               =#
               #=  need to create a new version of the class
               =#
          (outVersionedTargetClassEnv, outVersionedTargetClass, outIH)
        end

        function isTargetClassBuiltin(inGraph::Graph, inClass::SCode.Element) ::Bool
              local yes::Bool

              yes = begin
                  local r::MMRef
                @matchcontinue (inGraph, inClass) begin
                  (_, _)  => begin
                      r = FNode.child(lastScopeRef(inGraph), SCodeUtil.elementName(inClass))
                      yes = FNode.isRefBasicType(r) || FNode.isRefBuiltin(r)
                    yes
                  end

                  _  => begin
                      false
                  end
                end
              end
          yes
        end

        function mkVersionName(inSourceEnv::Graph, inSourceName::Name, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, inTargetClassEnv::Graph, inTargetClassName::Name) ::Tuple{Name, Prefix.PrefixType}
              local outCrefPrefix::Prefix.PrefixType
              local outName::Name

              (outName, outCrefPrefix) = begin
                  local gcomp::Graph
                  local gclass::Graph
                  local classRef::MMRef
                  local compRef::MMRef
                  local n::Node
                  local r::MMRef
                  local crefPrefix::Prefix.PrefixType
                  local name::Name
                @match (inSourceEnv, inSourceName, inPrefix, inMod, inTargetClassEnv, inTargetClassName) begin
                  (_, _, _, _, _, _)  => begin
                      crefPrefix = PrefixUtil.prefixAdd(inSourceName, nil, nil, inPrefix, SCode.CONST(), ClassInf.UNKNOWN(Absyn.IDENT("")), AbsynUtil.dummyInfo)
                      name = inTargetClassName + "" + AbsynUtil.pathString(AbsynUtil.stringListPath(listReverse(AbsynUtil.pathToStringList(PrefixUtil.prefixToPath(crefPrefix)))), "", usefq = false)
                    (name, crefPrefix)
                  end
                end
              end
               #=  variability doesn't matter
               =#
               #=  name = inTargetClassName + \"$\" + ComponentReference.printComponentRefStr(PrefixUtil.prefixToCref(crefPrefix));
               =#
               #=  + \"$\" + AbsynUtil.pathString2NoLeadingDot(getGraphName(inSourceEnv), \"$\");
               =#
               #=  name = \"'$\" + inTargetClassName + \"@\" + AbsynUtil.pathString(AbsynUtil.stringListPath(listReverse(AbsynUtil.pathToStringList(PrefixUtil.prefixToPath(crefPrefix))))) + \"'\";
               =#
               #=  name = \"'$\" + getGraphNameStr(inSourceEnv) + \".\" + AbsynUtil.pathString(AbsynUtil.stringListPath(listReverse(AbsynUtil.pathToStringList(PrefixUtil.prefixToPath(crefPrefix))))) + \"'\";
               =#
               #=  name = \"$'\" + getGraphNameStr(inSourceEnv) + \".\" +
               =#
               #=         AbsynUtil.pathString(AbsynUtil.stringListPath(listReverse(AbsynUtil.pathToStringList(PrefixUtil.prefixToPath(crefPrefix))))) +
               =#
               #=         SCodeDump.printModStr(Mod.unelabMod(inMod), SCodeDump.defaultOptions);
               =#
          (outName, outCrefPrefix)
        end

        function getClassPrefix(inEnv::FCore.Graph, inClassName::Name) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              outPrefix = begin
                  local p::Prefix.PrefixType
                  local r::MMRef
                @matchcontinue (inEnv, inClassName) begin
                  (_, _)  => begin
                      r = FNode.child(lastScopeRef(inEnv), inClassName)
                      @match FCore.CL(pre = p) = FNode.refData(r)
                    p
                  end

                  _  => begin
                      Prefix.NOPRE()
                  end
                end
              end
          outPrefix
        end

        function isInstance(inEnv::FCore.Graph, inName::FCore.Name) ::Bool
              local yes::Bool

              yes = begin
                @matchcontinue (inEnv, inName) begin
                  (_, _)  => begin
                      @match FCore.CL(status = FCore.CLS_INSTANCE(_)) = FNode.refData(FNode.child(lastScopeRef(inEnv), inName))
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          yes
        end

        function getInstanceOriginalName(inEnv::FCore.Graph, inName::FCore.Name) ::FCore.Name
              local outName::FCore.Name

              outName = begin
                @matchcontinue (inEnv, inName) begin
                  (_, _)  => begin
                      @match FCore.CL(status = FCore.CLS_INSTANCE(outName)) = FNode.refData(FNode.child(lastScopeRef(inEnv), inName))
                    outName
                  end

                  _  => begin
                      inName
                  end
                end
              end
          outName
        end

         #= note that A.B.C is not prefix of A.B.C,
         only A.B is a prefix of A.B.C =#
        function graphPrefixOf(inPrefixEnv::Graph, inEnv::Graph) ::Bool
              local outIsPrefix::Bool

              outIsPrefix = graphPrefixOf2(listReverse(currentScope(inPrefixEnv)), listReverse(currentScope(inEnv)))
          outIsPrefix
        end

         #= Checks if one environment is a prefix of another.
         note that A.B.C is not prefix of A.B.C,
         only A.B is a prefix of A.B.C =#
        function graphPrefixOf2(inPrefixEnv::Scope, inEnv::Scope) ::Bool
              local outIsPrefix::Bool

              outIsPrefix = begin
                  local n1::String
                  local n2::String
                  local rest1::Scope
                  local rest2::Scope
                  local r1::MMRef
                  local r2::MMRef
                @match (inPrefixEnv, inEnv) begin
                  ( nil(), _ <| _)  => begin
                    true
                  end

                  (r1 <| rest1, r2 <| rest2) where (stringEq(FNode.refName(r1), FNode.refName(r2)))  => begin
                    graphPrefixOf2(rest1, rest2)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsPrefix
        end

        function setStatus(inEnv::Graph, inName::Name, inStatus::FCore.Data) ::Graph
              local outEnv::Graph

              outEnv = begin
                  local g::Graph
                  local n::Node
                  local ref::MMRef
                  local refParent::MMRef
                @matchcontinue (inEnv, inName, inStatus) begin
                  (g, _, _)  => begin
                      refParent = lastScopeRef(g)
                      if FNode.refHasChild(refParent, inName)
                        ref = FNode.child(refParent, inName)
                        if FNode.refHasChild(ref, FNode.statusNodeName)
                          ref = FNode.child(ref, FNode.statusNodeName)
                          n = FNode.setData(FNode.fromRef(ref), inStatus)
                          ref = FNode.updateRef(ref, n)
                        else
                          (g, n) = node(g, FNode.statusNodeName, list(ref), inStatus)
                          FNode.addChildRef(ref, FNode.statusNodeName, FNode.toRef(n))
                        end
                      end
                    g
                  end

                  (g, _, _)  => begin
                      print("FGraph.setStatus failed on: " + getGraphNameStr(g) + " element: " + inName + "\\n")
                    g
                  end
                end
              end
               #=  did we fail for some weird reson?
               =#
          outEnv
        end

        function getStatus(inEnv::Graph, inName::Name) ::FCore.Data
              local outStatus::FCore.Data

              outStatus = begin
                  local g::Graph
                  local n::Node
                  local ref::MMRef
                  local refParent::MMRef
                  local s::FCore.Data
                   #=  child exists and has a status node
                   =#
                @match (inEnv, inName) begin
                  (g, _)  => begin
                      refParent = lastScopeRef(g)
                      @match true = FNode.refHasChild(refParent, inName)
                      ref = FNode.child(refParent, inName)
                      @match true = FNode.refHasChild(ref, FNode.statusNodeName)
                      ref = FNode.child(ref, FNode.statusNodeName)
                      s = FNode.refData(ref)
                    s
                  end

                  (_, _)  => begin
                    fail()
                  end
                end
              end
               #=  we can fail here with no problem, there is no status node!
               =#
               #=  print(\"FGraph.getStatus failed on: \" + getGraphNameStr(g) + \" element: \" + inName + \"\\n\");
               =#
          outStatus
        end

         #= return the environment pointed by the path if it exists, else fails =#
        function selectScope(inEnv::Graph, inPath::Absyn.Path) ::Graph
              local outEnv::Graph

              outEnv = begin
                  local env::Graph
                  local pl::List{String}
                  local el::List{String}
                  local lp::ModelicaInteger
                  local le::ModelicaInteger
                  local diff::ModelicaInteger
                  local cs::Scope
                  local p::Absyn.Path
                @match (inEnv, inPath) begin
                  (_, _)  => begin
                      p = AbsynUtil.stripLast(inPath)
                      @match true = AbsynUtil.pathPrefixOf(p, getGraphName(inEnv))
                      pl = AbsynUtil.pathToStringList(p)
                      lp = listLength(pl)
                      cs = currentScope(inEnv)
                      le = listLength(cs) - 1
                      diff = le - lp
                      cs = ListUtil.stripN(cs, diff)
                      env = setScope(inEnv, cs)
                    env
                  end
                end
              end
               #=  print(\"F: \" + AbsynUtil.pathString(inPath) + \"\\n\"); print(\"E: \" + getGraphNameStr(inEnv) + \"\\n\"); print(\"R: \" + getGraphNameStr(env) + \"\\n\");
               =#
          outEnv
        end

        function makeScopePartial(inEnv::Graph) ::Graph
              local outEnv::Graph = inEnv

              local node::Node
              local data::Data
              local el::SCode.Element

              try
                node = FNode.fromRef(lastScopeRef(inEnv))
                node = begin
                  @match node begin
                    FCore.N(data = data && FCore.CL(e = el))  => begin
                        el = SCodeUtil.makeClassPartial(el)
                        data.e = el
                        node.data = data
                      node
                    end

                    _  => begin
                        node
                    end
                  end
                end
                outEnv = setLastScopeRef(FNode.toRef(node), outEnv)
              catch
              end
          outEnv
        end

        function isPartialScope(inEnv::Graph) ::Bool
              local outIsPartial::Bool

              local el::SCode.Element

              try
                @match FCore.N(data = FCore.CL(e = el)) = FNode.fromRef(lastScopeRef(inEnv))
                outIsPartial = SCodeUtil.isPartial(el)
              catch
                outIsPartial = false
              end
          outIsPartial
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

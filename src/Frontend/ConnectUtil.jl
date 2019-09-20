  module ConnectUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    FuncType = Function

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
         #=  public imports
         =#

        import Absyn
        import AbsynUtil
        import SCode
        import ClassInf
        import Config
        import Connect
        import DAE
        import FCore
        import InnerOuter
        import Prefix
        import ConnectionGraph
         #=  protected imports
         =#

        import ComponentReference
        import DAEUtil
        import Debug
        import ElementSource
        import Error
        import Expression
        import ExpressionDump
        import ExpressionSimplify
        import Flags
        import ListUtil
        import Lookup
        import PrefixUtil
        import SCodeUtil
        import System
        import Types
        import Util
        import Global
         #=  Import some types from Connect.
         =#
        import Connect.Face
        import Connect.ConnectorType
        import Connect.ConnectorElement
        import Connect.SetTrieNode
        import Connect.SetTrie
        import Connect.SetConnection
        import Connect.OuterConnect
        import Connect.Sets
        import Connect.Set
         #=  Set graph represented as an adjacency list.
         =#

        DaeEdges = List # ConnectionGraph.DaeEdges # this doesn't seem to work, it says DaeEdges is undefined!

        SetGraph = Array

         #= This function creates a 'new' set for the given prefix. This means that it
          makes a set with a new empty trie, but copies the set count and connection
          crefs from the old set. This is done because we don't need to propagate
          connections down in the instance hierarchy, but the list of connection crefs
          needs to be propagated to be able to evaluate the cardinality operator. See
          comments in addSet below for how the sets are merged later. =#
        function newSet(prefix::Prefix.PrefixType, sets::Sets) ::Sets


              local pstr::String
              local sc::ModelicaInteger
              local cr::DAE.ComponentRef

              @match Sets.SETS(setCount = sc) = sets
              try
                cr = PrefixUtil.prefixFirstCref(prefix)
                pstr = ComponentReference.printComponentRefStr(cr)
              catch
                cr = DAE.WILD()
                pstr = ""
              end
              sets = Sets.SETS(SetTrieNode.SET_TRIE_NODE(pstr, cr, nil, 0), sc, nil, nil)
          sets
        end

         #= This function adds a child set to a parent set. =#
        function addSet(parentSets::Sets, childSets::Sets) ::Sets
              local sets::Sets

              sets = begin
                  local c1::List{SetConnection}
                  local c2::List{SetConnection}
                  local o1::List{OuterConnect}
                  local o2::List{OuterConnect}
                  local sc::ModelicaInteger
                  local node::SetTrieNode
                   #=  If the child set is empty we don't need to add it.
                   =#
                @matchcontinue (parentSets, childSets) begin
                  (_, _) where (isEmptySet(childSets))  => begin
                    parentSets
                  end

                  (Sets.SETS(sets = SetTrieNode.SET_TRIE_NODE(cref = DAE.WILD(__))), Sets.SETS(sets = SetTrieNode.SET_TRIE_NODE(cref = DAE.WILD(__))))  => begin
                    childSets
                  end

                  (Sets.SETS(sets = node && SetTrieNode.SET_TRIE_NODE(__)), Sets.SETS(__))  => begin
                       #=  If both sets are nameless, i.e. a top scope set, just return the child
                       =#
                       #=  set as it is. This is to avoid getting nestled top scope sets in some
                       =#
                       #=  cases, and the child should be a superset of the parent.
                       =#
                       #=  Check if the node already exists. In that case it's probably due to
                       =#
                       #=  multiple inheritance and we should ignore it.
                       =#
                      _ = setTrieGetNode(setTrieNodeName(childSets.sets), node.nodes)
                    parentSets
                  end

                  (Sets.SETS(node && SetTrieNode.SET_TRIE_NODE(__), _, c1, o1), Sets.SETS(_, sc, c2, o2))  => begin
                       #=  In the normal case we add the trie on the child sets to the parent, and
                       =#
                       #=  also merge their lists of outer connects.
                       =#
                      c1 = listAppend(c2, c1)
                      o1 = listAppend(o2, o1)
                      node.nodes = _cons(childSets.sets, node.nodes)
                    Sets.SETS(node, sc, c1, o1)
                  end
                end
              end
          sets
        end

         #= Check if a given set is empty. =#
        function isEmptySet(sets::Sets) ::Bool
              local isEmpty::Bool

              isEmpty = begin
                @match sets begin
                  Sets.SETS(sets = SetTrieNode.SET_TRIE_NODE(nodes =  nil()), connections =  nil(), outerConnects =  nil())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isEmpty
        end

         #= Adds a new connection by looking up both the given connector elements in the
           set trie and merging the sets together. =#
        function addConnection(sets::Sets, cref1::DAE.ComponentRef, face1::Face, cref2::DAE.ComponentRef, face2::Face, connectorType::DAE.ConnectorType, source::DAE.ElementSource) ::Sets


              local e1::ConnectorElement
              local e2::ConnectorElement
              local ty::ConnectorType

              ty = makeConnectorType(connectorType)
              e1 = findElement(cref1, face1, ty, source, sets)
              e2 = findElement(cref2, face2, ty, source, sets)
              sets = mergeSets(e1, e2, sets)
          sets
        end

        function getConnectCount(cref::DAE.ComponentRef, trie::SetTrie) ::ModelicaInteger
              local count::ModelicaInteger

              local node::SetTrieNode

              try
                node = setTrieGet(cref, trie, false)
                count = begin
                  @match node begin
                    SetTrieNode.SET_TRIE_NODE(__)  => begin
                      node.connectCount
                    end

                    SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      node.connectCount
                    end
                  end
                end
              catch
                count = 0
              end
          count
        end

         #= Connects two arrays of connectors. =#
        function addArrayConnection(sets::Sets, cref1::DAE.ComponentRef, face1::Face, cref2::DAE.ComponentRef, face2::Face, source::DAE.ElementSource, connectorType::DAE.ConnectorType) ::Sets


              local crefs1::List{DAE.ComponentRef}
              local crefs2::List{DAE.ComponentRef}
              local cr2::DAE.ComponentRef

              crefs1 = ComponentReference.expandCref(cref1, false)
              crefs2 = ComponentReference.expandCref(cref2, false)
              for cr1 in crefs1
                @match _cons(cr2, crefs2) = crefs2
                sets = addConnection(sets, cr1, face1, cr2, face2, connectorType, source)
              end
          sets
        end

         #= Creates a connector type from the flow or stream prefix given. =#
        function makeConnectorType(connectorType::DAE.ConnectorType) ::ConnectorType
              local ty::ConnectorType

              local flowName::Option{DAE.ComponentRef}

              ty = begin
                @match connectorType begin
                  DAE.POTENTIAL(__)  => begin
                    ConnectorType.EQU()
                  end

                  DAE.FLOW(__)  => begin
                    ConnectorType.FLOW()
                  end

                  DAE.STREAM(flowName)  => begin
                    ConnectorType.STREAM(flowName)
                  end

                  DAE.NON_CONNECTOR(__)  => begin
                    ConnectorType.NO_TYPE()
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("ConnectUtil.makeConnectorType: invalid connector type."))
                      fail()
                  end
                end
              end
          ty
        end

         #= If the class state indicates a connector, this function adds all flow
          variables in the dae as inside connectors to the connection sets. =#
        function addConnectorVariablesFromDAE(ignore::Bool, classState::ClassInf.SMNode, prefix::Prefix.PrefixType, vars::List{<:DAE.Var}, info::SourceInfo, elementSource::DAE.ElementSource, sets::Sets) ::Sets


              sets = begin
                  local class_path::Absyn.Path
                  local streams::List{DAE.Var}
                  local flows::List{DAE.Var}
                @match classState begin
                  ClassInf.CONNECTOR(path = class_path, isExpandable = false) where (! ignore)  => begin
                       #=  Check balance of non expandable connectors.
                       =#
                      checkConnectorBalance(vars, class_path, info)
                       #=  Add flow variables as inside connectors, unless disabled by flag.
                       =#
                      if ! Flags.isSet(Flags.DISABLE_SINGLE_FLOW_EQ)
                        (flows, streams) = getStreamAndFlowVariables(vars)
                        sets = ListUtil.fold2(flows, addFlowVariableFromDAE, elementSource, prefix, sets)
                        sets = addStreamFlowAssociations(sets, prefix, streams, flows)
                      end
                    sets
                  end

                  _  => begin
                      sets
                  end
                end
              end
          sets
        end

         #= Adds a flow variable from the DAE to the sets as an inside flow variable. =#
        function addFlowVariableFromDAE(variable::DAE.Var, elementSource::DAE.ElementSource, prefix::Prefix.PrefixType, sets::Sets) ::Sets


              local crefs::List{DAE.ComponentRef}

              crefs = daeVarToCrefs(variable)
              for cr in crefs
                sets = addInsideFlowVariable(sets, cr, elementSource, prefix)
              end
          sets
        end

        function isExpandable(name::DAE.ComponentRef) ::Bool
              local expandableConnector::Bool

              expandableConnector = begin
                @match name begin
                  DAE.CREF_IDENT(__)  => begin
                    Types.isExpandableConnector(name.identType)
                  end

                  DAE.CREF_QUAL(__)  => begin
                    Types.isExpandableConnector(name.identType) || isExpandable(name.componentRef)
                  end

                  _  => begin
                      false
                  end
                end
              end
          expandableConnector
        end

         #= Checks if a DAE contains any expandable connectors. =#
        function daeHasExpandableConnectors(DAE::DAE.DAElist) ::Bool
              local hasExpandable::Bool

              local vars::List{DAE.Element}

              if System.getHasExpandableConnectors()
                @match DAE.DAE(vars) = DAE
                hasExpandable = ListUtil.exist(vars, isVarExpandable)
              else
                hasExpandable = false
              end
          hasExpandable
        end

        function isVarExpandable(var::DAE.Element) ::Bool
              local isExpandable::Bool

              isExpandable = begin
                @match var begin
                  DAE.VAR(__)  => begin
                    isExpandable(var.componentRef)
                  end

                  _  => begin
                      false
                  end
                end
              end
          isExpandable
        end

         #= @author: adrpo
           Goes through a list of expandable variables
           THAT HAVE NO BINDING and returns their crefs =#
        function getExpandableVariablesWithNoBinding(variables::List{<:DAE.Element}) ::List{DAE.ComponentRef}
              local potential::List{DAE.ComponentRef} = nil

              local name::DAE.ComponentRef

              for var in variables
                _ = begin
                  @match var begin
                    DAE.VAR(componentRef = name, binding = NONE())  => begin
                         #=  do not return the ones that have a binding as they are used
                         =#
                         #=  TODO: actually only if their binding is not another expandable??!!
                         =#
                        if isExpandable(name)
                          potential = _cons(name, potential)
                        end
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
          potential
        end

         #= Goes through a list of variables and filters out all flow and stream
           variables into separate lists. =#
        function getStreamAndFlowVariables(variables::List{<:DAE.Var}) ::Tuple{List{DAE.Var}, List{DAE.Var}}
              local streams::List{DAE.Var} = nil
              local flows::List{DAE.Var} = nil

              for var in variables
                _ = begin
                  @match var begin
                    DAE.TYPES_VAR(attributes = DAE.ATTR(connectorType = DAE.FLOW(__)))  => begin
                        flows = _cons(var, flows)
                      ()
                    end

                    DAE.TYPES_VAR(attributes = DAE.ATTR(connectorType = DAE.STREAM(__)))  => begin
                        streams = _cons(var, streams)
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
          (flows, streams)
        end

         #= Adds information to the connection sets about which flow variables each
          stream variable is associated to. =#
        function addStreamFlowAssociations(sets::Sets, prefix::Prefix.PrefixType, streamVars::List{<:DAE.Var}, flowVars::List{<:DAE.Var}) ::Sets


              local flow_var::DAE.Var
              local flow_cr::DAE.ComponentRef
              local stream_crs::List{DAE.ComponentRef}

               #=  No stream variables => not a stream connector.
               =#
              if listEmpty(streamVars)
                return sets
              end
               #=  Stream variables and exactly one flow => add associations.
               =#
              @match list(flow_var) = flowVars
              @match list(flow_cr) = daeVarToCrefs(flow_var)
              flow_cr = PrefixUtil.prefixCrefNoContext(prefix, flow_cr)
              for stream_var in streamVars
                stream_crs = daeVarToCrefs(stream_var)
                for stream_cr in stream_crs
                  sets = addStreamFlowAssociation(stream_cr, flow_cr, sets)
                end
              end
          sets
        end

         #= Converts a DAE.Var to a list of crefs. =#
        function daeVarToCrefs(var::DAE.Var) ::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef}

              local name::String
              local ty::DAE.Type
              local crs::List{DAE.ComponentRef}
              local dims::DAE.Dimensions
              local cr::DAE.ComponentRef

              @match DAE.TYPES_VAR(name = name, ty = ty) = var
              ty = Types.derivedBasicType(ty)
              crefs = begin
                @match ty begin
                  DAE.T_REAL(__)  => begin
                    list(DAE.CREF_IDENT(name, ty, nil))
                  end

                  DAE.T_COMPLEX(__)  => begin
                       #=  Scalar
                       =#
                       #=  Complex type
                       =#
                      crs = listAppend(daeVarToCrefs(v) for v in listReverse(ty.varLst))
                      cr = DAE.CREF_IDENT(name, DAE.T_REAL_DEFAULT, nil)
                    list(ComponentReference.joinCrefs(cr, c) for c in crs)
                  end

                  DAE.T_ARRAY(__)  => begin
                       #=  Array
                       =#
                      dims = Types.getDimensions(ty)
                      cr = DAE.CREF_IDENT(name, ty, nil)
                    expandArrayCref(cr, dims)
                  end

                  _  => begin
                        Error.addInternalError("Unknown var " + name + " in ConnectUtil.daeVarToCrefs", sourceInfo())
                      fail()
                  end
                end
              end
          crefs
        end

         #= This function takes an array cref and a list of dimensions, and generates all
          scalar crefs by expanding the dimensions into subscripts. =#
        function expandArrayCref(cref::DAE.ComponentRef, dims::DAE.Dimensions, accumCrefs::List{<:DAE.ComponentRef} = nil) ::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef}

              crefs = begin
                  local dim::DAE.Dimension
                  local rest_dims::DAE.Dimensions
                  local idx::DAE.Exp
                  local cr::DAE.ComponentRef
                  local crs::List{DAE.ComponentRef}
                @matchcontinue dims begin
                   nil()  => begin
                    _cons(cref, accumCrefs)
                  end

                  dim <| rest_dims  => begin
                      (idx, dim) = getNextIndex(dim)
                      cr = ComponentReference.subscriptCref(cref, list(DAE.INDEX(idx)))
                      crs = expandArrayCref(cr, rest_dims, accumCrefs)
                      crs = expandArrayCref(cref, _cons(dim, rest_dims), crs)
                    crs
                  end

                  _  => begin
                      accumCrefs
                  end
                end
              end
          crefs
        end

         #= Reverses the order of the literals in an enumeration dimension, or just
          returns the given dimension if it's not an enumeration. This is used by
          getNextIndex that starts from the end, so that it can take the first literal
          in the list instead of the last (more efficient). =#
        function reverseEnumType(dim::DAE.Dimension) ::DAE.Dimension


              _ = begin
                @match dim begin
                  DAE.DIM_ENUM(__)  => begin
                      dim.literals = listReverse(dim.literals)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
          dim
        end

         #= Returns the next index given a dimension, and updates the dimension. Fails
          when there are no indices left. =#
        function getNextIndex(dim::DAE.Dimension) ::Tuple{DAE.Exp, DAE.Dimension}
              local restDim::DAE.Dimension
              local nextIndex::DAE.Exp

              (nextIndex, restDim) = begin
                  local new_idx::ModelicaInteger
                  local dim_size::ModelicaInteger
                  local p::Absyn.Path
                  local ep::Absyn.Path
                  local l::String
                  local l_rest::List{String}
                @match dim begin
                  DAE.DIM_INTEGER(integer = 0)  => begin
                    fail()
                  end

                  DAE.DIM_ENUM(size = 0)  => begin
                    fail()
                  end

                  DAE.DIM_INTEGER(integer = new_idx)  => begin
                      dim_size = new_idx - 1
                    (DAE.ICONST(new_idx), DAE.DIM_INTEGER(dim_size))
                  end

                  DAE.DIM_ENUM(p, l <| l_rest, new_idx)  => begin
                       #=  Assumes that the enum has been reversed with reverseEnumType.
                       =#
                      ep = AbsynUtil.joinPaths(p, Absyn.IDENT(l))
                      dim_size = new_idx - 1
                    (DAE.ENUM_LITERAL(ep, new_idx), DAE.DIM_ENUM(p, l_rest, dim_size))
                  end
                end
              end
          (nextIndex, restDim)
        end

         #= Adds a single inside flow variable to the connection sets. =#
        function addInsideFlowVariable(sets::Sets, cref::DAE.ComponentRef, source::DAE.ElementSource, prefix::Prefix.PrefixType) ::Sets


              local e::ConnectorElement

              try
                setTrieGetElement(cref, Face.INSIDE(), sets.sets)
              catch
                sets.setCount = sets.setCount + 1
                e = newElement(cref, Face.INSIDE(), ConnectorType.FLOW(), source, sets.setCount)
                sets.sets = setTrieAdd(e, sets.sets)
              end
               #=  Check if it exists in the sets already.
               =#
               #=  Otherwise, add a new set for it.
               =#
          sets
        end

         #= Adds an association between a stream variable and a flow. =#
        function addStreamFlowAssociation(streamCref::DAE.ComponentRef, flowCref::DAE.ComponentRef, sets::Sets) ::Sets


              sets = updateSetLeaf(sets, streamCref, flowCref, addStreamFlowAssociation2)
          sets
        end

         #= Helper function to addSTreamFlowAssocication, sets the flow association in a
           leaf node. =#
        function addStreamFlowAssociation2(flowCref::DAE.ComponentRef, node::SetTrieNode) ::SetTrieNode


              _ = begin
                @match node begin
                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      node.flowAssociation = SOME(flowCref)
                    ()
                  end
                end
              end
          node
        end

         #= Returns the associated flow variable for a stream variable. =#
        function getStreamFlowAssociation(streamCref::DAE.ComponentRef, sets::Sets) ::DAE.ComponentRef
              local flowCref::DAE.ComponentRef

              @match SetTrieNode.SET_TRIE_LEAF(flowAssociation = SOME(flowCref)) = setTrieGet(streamCref, sets.sets, false)
          flowCref
        end

         #= Adds a connection with a reference to an outer connector These are added to a
           special list, such that they can be moved up in the instance hierarchy to a
           place where both instances are defined. =#
        function addOuterConnection(scope::Prefix.PrefixType, sets::Sets, cr1::DAE.ComponentRef, cr2::DAE.ComponentRef, io1::Absyn.InnerOuter, io2::Absyn.InnerOuter, f1::Face, f2::Face, source::DAE.ElementSource) ::Sets


              local new_oc::OuterConnect

               #=  Only add a new outer connection if it doesn't already exist in the list.
               =#
              if ! ListUtil.exist2(sets.outerConnects, outerConnectionMatches, cr1, cr2)
                new_oc = OuterConnect.OUTERCONNECT(scope, cr1, io1, f1, cr2, io2, f2, source)
                sets.outerConnects = _cons(new_oc, sets.outerConnects)
              end
          sets
        end

         #= Returns true if Connect.OuterConnect matches the two component references
          passed as argument. =#
        function outerConnectionMatches(oc::OuterConnect, cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local matches::Bool

              matches = begin
                @match oc begin
                  OuterConnect.OUTERCONNECT(__)  => begin
                    ComponentReference.crefEqual(oc.cr1, cr1) && ComponentReference.crefEqual(oc.cr2, cr2) || ComponentReference.crefEqual(oc.cr1, cr2) && ComponentReference.crefEqual(oc.cr2, cr1)
                  end
                end
              end
          matches
        end

         #= Adds an outer connection to all sets where a corresponding inner definition
          is present. For instance, if a connection set contains {world.v, topPin.v} and
          we have an outer connection connect(world, a2.aPin), the connection is added
          to the sets, resulting in {world.v, topPin.v, a2.aPin.v}. Returns the updated
          sets and a boolean that indicates if anything was added or not. =#
        function addOuterConnectToSets(cref1::DAE.ComponentRef, cref2::DAE.ComponentRef, io1::Absyn.InnerOuter, io2::Absyn.InnerOuter, face1::Face, face2::Face, sets::Sets, inInfo::SourceInfo) ::Tuple{Sets, Bool}
              local added::Bool


              local is_outer1::Bool
              local is_outer2::Bool

              is_outer1 = AbsynUtil.isOuter(io1)
              is_outer2 = AbsynUtil.isOuter(io2)
              added = begin
                @match (is_outer1, is_outer2) begin
                  (true, true)  => begin
                       #=  Both are outer => error.
                       =#
                      Error.addSourceMessage(Error.UNSUPPORTED_LANGUAGE_FEATURE, list("Connections where both connectors are outer references", "No suggestion"), inInfo)
                    false
                  end

                  (false, false)  => begin
                    false
                  end

                  (true, false)  => begin
                       #=  Both are inner => do nothing.
                       =#
                       #=  The first is outer and the second inner, call addOuterConnectToSets2.
                       =#
                      (sets, added) = addOuterConnectToSets2(cref1, cref2, face1, face2, sets)
                    added
                  end

                  (false, true)  => begin
                       #=  The first is inner and the second outer, call addOuterConnectToSets2 with
                       =#
                       #=  reversed order on the components compared to above.
                       =#
                      (sets, added) = addOuterConnectToSets2(cref2, cref1, face2, face1, sets)
                    added
                  end
                end
              end
          (sets, added)
        end

         #= Helper function to addOuterConnectToSets. Tries to add connections between
           the inner and outer components. =#
        function addOuterConnectToSets2(outerCref::DAE.ComponentRef, innerCref::DAE.ComponentRef, outerFace::Face, innerFace::Face, sets::Sets) ::Tuple{Sets, Bool}
              local added::Bool


              local node::SetTrieNode
              local outer_els::List{ConnectorElement}
              local inner_els::List{ConnectorElement}
              local sc::ModelicaInteger

              try
                node = setTrieGet(outerCref, sets.sets, true)
                outer_els = collectOuterElements(node, outerFace)
                inner_els = list(findInnerElement(oe, innerCref, innerFace, sets) for oe in outer_els)
                sc = sets.setCount
                sets = ListUtil.threadFold(outer_els, inner_els, mergeSets, sets)
                added = sc != sets.setCount
              catch
                added = false
              end
               #=  Find the trie node for the outer component.
               =#
               #=  Collect all connector elements in the node.
               =#
               #=  Find or create inner elements corresponding to the outer elements.
               =#
               #=  Merge the inner and outer sets pairwise from the two lists.
               =#
               #=  Check if the number of sets changed.
               =#
          (sets, added)
        end

         #= Collects all connector elements with a certain face from a trie node. =#
        function collectOuterElements(node::SetTrieNode, face::Face) ::List{ConnectorElement}
              local outerElements::List{ConnectorElement}

              outerElements = begin
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                    ListUtil.map2Flat(node.nodes, collectOuterElements2, face, NONE())
                  end

                  _  => begin
                      collectOuterElements2(node, face, NONE())
                  end
                end
              end
          outerElements
        end

         #= Helper function to collectOuterElements. =#
        function collectOuterElements2(node::SetTrieNode, face::Face, prefix::Option{<:DAE.ComponentRef}) ::List{ConnectorElement}
              local outerElements::List{ConnectorElement}

              outerElements = begin
                  local cr::DAE.ComponentRef
                  local nodes::List{SetTrieNode}
                  local e::ConnectorElement
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(cref = cr)  => begin
                      cr = optPrefixCref(prefix, cr)
                    ListUtil.map2Flat(node.nodes, collectOuterElements2, face, SOME(cr))
                  end

                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      e = setTrieGetLeafElement(node, face)
                      cr = getElementName(e)
                      e = setElementName(e, optPrefixCref(prefix, cr))
                    list(e)
                  end
                end
              end
          outerElements
        end

         #= Finds or creates an inner element based on a given outer element. =#
        function findInnerElement(outerElement::ConnectorElement, innerCref::DAE.ComponentRef, innerFace::Face, sets::Sets) ::ConnectorElement
              local innerElement::ConnectorElement

              local name::DAE.ComponentRef
              local ty::ConnectorType
              local src::DAE.ElementSource

              @match ConnectorElement.CONNECTOR_ELEMENT(name = name, ty = ty, source = src) = outerElement
              name = ComponentReference.joinCrefs(innerCref, name)
              innerElement = findElement(name, innerFace, ty, src, sets)
          innerElement
        end

         #= Appends an optional prefix to a cref. =#
        function optPrefixCref(prefix::Option{<:DAE.ComponentRef}, cref::DAE.ComponentRef) ::DAE.ComponentRef


              cref = begin
                  local cr::DAE.ComponentRef
                @match prefix begin
                  NONE()  => begin
                    cref
                  end

                  SOME(cr)  => begin
                    ComponentReference.joinCrefs(cr, cref)
                  end
                end
              end
          cref
        end

         #= Tries to find a connector element in the sets given a cref and a face. If no
           element can be found it creates a new one. =#
        function findElement(cref::DAE.ComponentRef, face::Face, ty::ConnectorType, source::DAE.ElementSource, sets::Sets) ::ConnectorElement
              local element::ConnectorElement

              try
                element = setTrieGetElement(cref, face, sets.sets)
              catch
                element = newElement(cref, face, ty, source, Connect.NEW_SET)
              end
          element
        end

         #= Creates a new connector element. =#
        function newElement(cref::DAE.ComponentRef, face::Face, ty::ConnectorType, source::DAE.ElementSource, set::ModelicaInteger) ::ConnectorElement
              local element::ConnectorElement

              element = ConnectorElement.CONNECTOR_ELEMENT(cref, face, ty, source, set)
          element
        end

         #= Checks if the element is new, i.e. hasn't been assigned to a set yet. =#
        function isNewElement(element::ConnectorElement) ::Bool
              local isNew::Bool

              local set::ModelicaInteger

              @match ConnectorElement.CONNECTOR_ELEMENT(set = set) = element
              isNew = set == Connect.NEW_SET
          isNew
        end

         #= Returns the set index of a connector element. =#
        function getElementSetIndex(inElement::ConnectorElement) ::ModelicaInteger
              local outIndex::ModelicaInteger

              @match ConnectorElement.CONNECTOR_ELEMENT(set = outIndex) = inElement
          outIndex
        end

         #= Sets the set index of a connector element. =#
        function setElementSetIndex(element::ConnectorElement, index::ModelicaInteger) ::ConnectorElement


              element.set = index
          element
        end

         #= Returns the name of a connector element. =#
        function getElementName(element::ConnectorElement) ::DAE.ComponentRef
              local name::DAE.ComponentRef

              @match ConnectorElement.CONNECTOR_ELEMENT(name = name) = element
          name
        end

         #= Sets the name of a connector element. =#
        function setElementName(element::ConnectorElement, name::DAE.ComponentRef) ::ConnectorElement


              element.name = name
          element
        end

         #= Returns the element source of a connector element. =#
        function getElementSource(element::ConnectorElement) ::DAE.ElementSource
              local source::DAE.ElementSource

              @match ConnectorElement.CONNECTOR_ELEMENT(source = source) = element
          source
        end

         #= Creates a new trie leaf. =#
        function setTrieNewLeaf(id::String, element::ConnectorElement) ::SetTrieNode
              local leaf::SetTrieNode

              leaf = begin
                @match element begin
                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__))  => begin
                    SetTrieNode.SET_TRIE_LEAF(id, SOME(element), NONE(), NONE(), 0)
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.OUTSIDE(__))  => begin
                    SetTrieNode.SET_TRIE_LEAF(id, NONE(), SOME(element), NONE(), 0)
                  end
                end
              end
          leaf
        end

         #= Creates a new trie node. =#
        function setTrieNewNode(cref::DAE.ComponentRef, element::ConnectorElement) ::SetTrieNode
              local node::SetTrieNode

              node = begin
                  local id::String
                  local cr::DAE.ComponentRef
                   #=  A simple identifier, just create a new leaf.
                   =#
                @match cref begin
                  DAE.CREF_IDENT(__)  => begin
                      id = ComponentReference.printComponentRefStr(cref)
                    setTrieNewLeaf(id, setElementName(element, cref))
                  end

                  DAE.CREF_QUAL(__)  => begin
                       #=  A qualified identifier, call this function recursively.
                       =#
                       #=  I.e. a.b.c becomes NODE(a, {NODE(b, {NODE(c)})});
                       =#
                      cr = ComponentReference.crefFirstCref(cref)
                      id = ComponentReference.printComponentRefStr(cr)
                      node = setTrieNewNode(cref.componentRef, element)
                    SetTrieNode.SET_TRIE_NODE(id, cr, list(node), 0)
                  end
                end
              end
          node
        end

        function setTrieNodeName(node::SetTrieNode) ::String
              local name::String

              name = begin
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                    node.name
                  end

                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                    node.name
                  end
                end
              end
          name
        end

         #= Merges two sets. =#
        function mergeSets(element1::ConnectorElement, element2::ConnectorElement, sets::Sets) ::Sets


              local new1::Bool
              local new2::Bool

              new1 = isNewElement(element1)
              new2 = isNewElement(element2)
              sets = mergeSets2(element1, element2, new1, new2, sets)
          sets
        end

         #= Helper function to mergeSets, dispatches to the correct function based on if
           the elements are new or not. =#
        function mergeSets2(element1::ConnectorElement, element2::ConnectorElement, isNew1::Bool, isNew2::Bool, sets::Sets) ::Sets


              sets = begin
                @match (isNew1, isNew2) begin
                  (true, true)  => begin
                    addNewSet(element1, element2, sets)
                  end

                  (true, false)  => begin
                    addToSet(element1, element2, sets)
                  end

                  (false, true)  => begin
                    addToSet(element2, element1, sets)
                  end

                  (false, false)  => begin
                    connectSets(element1, element2, sets)
                  end
                end
              end
               #=  Both elements are new, add them to a new set.
               =#
               #=  The first is new and the second old, add the first to the same set as the
               =#
               #=  second.
               =#
               #=  The second is new and the first old, add the second to the same set as
               =#
               #=  the first.
               =#
               #=  Both sets are old, add a connection between their sets.
               =#
          sets
        end

         #= Adds a new set containing the given two elements to the sets. =#
        function addNewSet(element1::ConnectorElement, element2::ConnectorElement, sets::Sets) ::Sets


              local node::SetTrie
              local sc::ModelicaInteger
              local e1::ConnectorElement
              local e2::ConnectorElement

              sc = sets.setCount + 1
              e1 = setElementSetIndex(element1, sc)
              e2 = setElementSetIndex(element2, sc)
              node = sets.sets
              node = setTrieAdd(e1, node)
              sets.sets = setTrieAdd(e2, node)
              sets.setCount = sc
          sets
        end

         #= Adds the first connector element to the same set as the second. =#
        function addToSet(element::ConnectorElement, set::ConnectorElement, sets::Sets) ::Sets


              local index::ModelicaInteger
              local e::ConnectorElement

              index = getElementSetIndex(set)
              e = setElementSetIndex(element, index)
              sets.sets = setTrieAdd(e, sets.sets)
          sets
        end

         #= Connects two sets. =#
        function connectSets(element1::ConnectorElement, element2::ConnectorElement, sets::Sets) ::Sets


              local set1::ModelicaInteger
              local set2::ModelicaInteger

              set1 = getElementSetIndex(element1)
              set2 = getElementSetIndex(element2)
               #=  Add a new connection if the elements don't belong to the same set already.
               =#
              if set1 != set2
                sets.connections = _cons((set1, set2), sets.connections)
              end
          sets
        end

         #= Fetches a connector element from the trie given a cref and a face. =#
        function setTrieGetElement(cref::DAE.ComponentRef, face::Face, trie::SetTrie) ::ConnectorElement
              local element::ConnectorElement

              local node::SetTrieNode

              node = setTrieGet(cref, trie, false)
              element = setTrieGetLeafElement(node, face)
          element
        end

         #= Adds a connector element to a trie leaf. =#
        function setTrieAddLeafElement(element::ConnectorElement, node::SetTrieNode) ::SetTrieNode


              _ = begin
                @match node begin
                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      _ = begin
                        @match element.face begin
                          Face.INSIDE(__)  => begin
                              node.insideElement = SOME(element)
                            ()
                          end

                          Face.OUTSIDE(__)  => begin
                              node.outsideElement = SOME(element)
                            ()
                          end
                        end
                      end
                    ()
                  end
                end
              end
          node
        end

         #= Returns the connector element of a trie leaf, given a face. =#
        function setTrieGetLeafElement(node::SetTrieNode, face::Face) ::ConnectorElement
              local element::ConnectorElement

              element = begin
                  local e::ConnectorElement
                @match (face, node) begin
                  (Face.INSIDE(__), SetTrieNode.SET_TRIE_LEAF(insideElement = SOME(e)))  => begin
                    e
                  end

                  (Face.OUTSIDE(__), SetTrieNode.SET_TRIE_LEAF(outsideElement = SOME(e)))  => begin
                    e
                  end
                end
              end
          element
        end

         #= Adds a connector element to the trie. =#
        function setTrieAdd(element::ConnectorElement, trie::SetTrie) ::SetTrie


              local cref::DAE.ComponentRef
              local el_cr::DAE.ComponentRef
              local el::ConnectorElement

              cref = getElementName(element)
              el_cr = ComponentReference.crefLastCref(cref)
              el = setElementName(element, el_cr)
              trie = setTrieUpdate(cref, el, trie, setTrieAddLeafElement)
          trie
        end

         #= Updates a trie leaf in the sets with the given update function. =#
        function updateSetLeaf(sets::Sets, cref::DAE.ComponentRef, arg::Arg, updateFunc::UpdateFunc)  where {Arg}


              sets.sets = setTrieUpdate(cref, arg, sets.sets, updateFunc)
          sets
        end

         #= Updates a trie leaf in the trie with the given update function. =#
        function setTrieUpdate(cref::DAE.ComponentRef, arg::Arg, trie::SetTrie, updateFunc::UpdateFunc)  where {Arg}


              _ = begin
                  local id::String
                @match (cref, trie) begin
                  (DAE.CREF_QUAL(__), SetTrieNode.SET_TRIE_NODE(__))  => begin
                      id = ComponentReference.printComponentRef2Str(cref.ident, cref.subscriptLst)
                      trie.nodes = setTrieUpdateNode(id, cref, cref.componentRef, arg, updateFunc, trie.nodes)
                    ()
                  end

                  (DAE.CREF_IDENT(__), SetTrieNode.SET_TRIE_NODE(__))  => begin
                      id = ComponentReference.printComponentRef2Str(cref.ident, cref.subscriptLst)
                      trie.nodes = setTrieUpdateLeaf(id, arg, trie.nodes, updateFunc)
                    ()
                  end
                end
              end
          trie
        end

         #= Helper function to setTrieUpdate, updates a node in the trie. =#
        function setTrieUpdateNode(id::String, wholeCref::DAE.ComponentRef, cref::DAE.ComponentRef, arg::Arg, updateFunc::UpdateFunc, nodes::List{SetTrieNode})  where {Arg}


              local node2::SetTrieNode
              local n::ModelicaInteger = 1

              for node in nodes
                if setTrieIsNode(node) && setTrieNodeName(node) == id
                  node2 = setTrieUpdate(cref, arg, node, updateFunc)
                  nodes = ListUtil.replaceAt(node2, n, nodes)
                  return nodes
                else
                  n = n + 1
                end
              end
               #=  Can be slow in memory and time
               =#
              nodes = setTrieUpdateNode2(wholeCref, arg, updateFunc, nodes)
          nodes
        end

         #= Helper function to setTrieUpdateNode. =#
        function setTrieUpdateNode2(cref::DAE.ComponentRef, arg::Arg, updateFunc::UpdateFunc, nodes::List{SetTrieNode})  where {Arg}


              nodes = begin
                  local id::String
                  local cr::DAE.ComponentRef
                  local rest_cr::DAE.ComponentRef
                  local node::SetTrieNode
                  local child_nodes::List{SetTrieNode}
                @match cref begin
                  DAE.CREF_IDENT(__)  => begin
                      id = ComponentReference.printComponentRefStr(cref)
                      node = SetTrieNode.SET_TRIE_LEAF(id, NONE(), NONE(), NONE(), 0)
                      node = updateFunc(arg, node)
                    _cons(node, nodes)
                  end

                  DAE.CREF_QUAL(__)  => begin
                      cr = ComponentReference.crefFirstCref(cref)
                      id = ComponentReference.printComponentRefStr(cr)
                      child_nodes = setTrieUpdateNode2(cref.componentRef, arg, updateFunc, nil)
                    _cons(SetTrieNode.SET_TRIE_NODE(id, cr, child_nodes, 0), nodes)
                  end
                end
              end
          nodes
        end

         #= Helper funtion to setTrieUpdate, updates a trie leaf. =#
        function setTrieUpdateLeaf(id::String, arg::Arg, nodes::List{SetTrieNode}, updateFunc::UpdateFunc)  where {Arg}


              local n::ModelicaInteger = 1

              for node in nodes
                if setTrieNodeName(node) == id
                  nodes = ListUtil.replaceAt(updateFunc(arg, node), n, nodes)
                  return nodes
                end
                n = n + 1
              end
               #=  Found matching leaf, update it.
               =#
               #=  Can be slow in time and memory...
               =#
               #=  Is slow in time; need to do a linear search. Cheap in memory (single cons)
               =#
              nodes = _cons(updateFunc(arg, Connect.SET_TRIE_LEAF(id, NONE(), NONE(), NONE(), 0)), nodes)
          nodes
        end

         #= Traverses the trie leaves in a sets. =#
        function traverseSets(sets::Sets, arg::Arg, updateFunc::UpdateFunc)  where {Arg}



              local node::SetTrieNode

              (node, arg) = setTrieTraverseLeaves(sets.sets, updateFunc, arg)
              sets.sets = node
          (sets, arg)
        end

         #= Traverses the leaves of a trie. =#
        function setTrieTraverseLeaves(node::SetTrieNode, updateFunc::UpdateFunc, arg::Arg)  where {Arg}



              _ = begin
                  local nodes::List{SetTrieNode}
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                      (nodes, arg) = ListUtil.map1Fold(node.nodes, setTrieTraverseLeaves, updateFunc, arg)
                      node.nodes = nodes
                    ()
                  end

                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      (node, arg) = updateFunc(node, arg)
                    ()
                  end
                end
              end
          (node, arg)
        end

         #= Fetches a node from the trie given a cref to search for. If inMatchPrefix is
          true it also matches a prefix of the cref if the full cref couldn't be found. =#
        function setTrieGet(cref::DAE.ComponentRef, trie::SetTrie, matchPrefix::Bool) ::SetTrieNode
              local leaf::SetTrieNode

              local nodes::List{SetTrieNode}
              local subs_str::String
              local id_subs::String
              local id_nosubs::String
              local node::SetTrieNode

              @match SetTrieNode.SET_TRIE_NODE(nodes = nodes) = trie
              id_nosubs = ComponentReference.crefFirstIdent(cref)
              subs_str = ListUtil.toString(ComponentReference.crefFirstSubs(cref), ExpressionDump.printSubscriptStr, "", "[", ",", "]", false)
              id_subs = id_nosubs + subs_str
              try
                leaf = setTrieGetNode(id_subs, nodes)
              catch
                leaf = setTrieGetNode(id_nosubs, nodes)
              end
               #=  Try to look up the identifier with subscripts, in case single array
               =#
               #=  elements have been added to the trie.
               =#
               #=  If the above fails, try again without the subscripts in case a whole
               =#
               #=  array has been added to the trie.
               =#
               #=  If the cref is qualified, continue to look up the rest of the cref in node
               =#
               #=  we just found.
               =#
              if ! ComponentReference.crefIsIdent(cref)
                try
                  leaf = setTrieGet(ComponentReference.crefRest(cref), leaf, matchPrefix)
                catch
                  @match true = matchPrefix && ! setTrieIsNode(leaf)
                end
              end
               #=  Look up failed, return the previously found node if prefix matching is
               =#
               #=  turned on and the node we found is a leaf.
               =#
          leaf
        end

         #= Returns a node with a given name from a list of nodes, or fails if no such
          node exists in the list. =#
        function setTrieGetNode(id::String, nodes::List{<:SetTrieNode}) ::SetTrieNode
              local node::SetTrieNode

              node = ListUtil.getMemberOnTrue(id, nodes, setTrieNodeNamed)
          node
        end

         #= Returns true if the given node has the same name as the given string,
          otherwise false. =#
        function setTrieNodeNamed(id::String, node::SetTrieNode) ::Bool
              local isNamed::Bool

              isNamed = begin
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                    id == node.name
                  end

                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                    id == node.name
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNamed
        end

         #= Returns a leaf node with a given name from a list of nodes, or fails if no
          such node exists in the list. =#
        function setTrieGetLeaf(id::String, nodes::List{<:SetTrieNode}) ::SetTrieNode
              local node::SetTrieNode

              node = ListUtil.getMemberOnTrue(id, nodes, setTrieLeafNamed)
          node
        end

         #= Returns true if the given leaf node has the same name as the given string,
          otherwise false. =#
        function setTrieLeafNamed(id::String, node::SetTrieNode) ::Bool
              local isNamed::Bool

              isNamed = begin
                @match node begin
                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                    id == node.name
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNamed
        end

        function setTrieIsNode(node::SetTrieNode) ::Bool
              local isNode::Bool

              isNode = begin
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isNode
        end

         #= Generates equations from a connection set and evaluates stream operators if
          called from the top scope, otherwise does nothing. =#
        function equations(topScope::Bool, sets::Sets, DAE::DAE.DAElist, connectionGraph::ConnectionGraph.ConnectionGraphType, modelNameQualified::String) ::DAE.DAElist


              local set_list::List{Set}
              local set_array::Array{Set}
              local dae::DAE.DAElist
              local dae2::DAE.DAElist
              local has_stream::Bool
              local has_expandable::Bool
              local has_cardinality::Bool
              local broken::DaeEdges
              local connected::DaeEdges

              setGlobalRoot(Global.isInStream, NONE())
              if ! topScope
                return DAE
              end
               #= print(printSetsStr(inSets) + \"\\n\");
               =#
              set_array = generateSetArray(sets)
              set_list = arrayList(set_array)
               #= print(\"Sets:\\n\");
               =#
               #= print(stringDelimitList(List.map(sets, printSetStr), \"\\n\") + \"\\n\");
               =#
              if daeHasExpandableConnectors(DAE)
                (set_list, dae) = removeUnusedExpandableVariablesAndConnections(set_list, DAE)
              else
                dae = DAE
              end
               #=  send in the connection graph and build the connected/broken connects
               =#
               #=  we do this here so we do it once and not for every EQU set.
               =#
              (dae, connected, broken) = ConnectionGraph.handleOverconstrainedConnections(connectionGraph, modelNameQualified, dae)
               #=  adrpo: FIXME: maybe we should just remove them from the sets then send the
               =#
               #=  updates sets further
               =#
              dae2 = equationsDispatch(listReverse(set_list), connected, broken)
              DAE = DAEUtil.joinDaes(dae, dae2)
              DAE = evaluateConnectionOperators(sets, set_array, DAE)
               #=  add the equality constraint equations to the dae.
               =#
              DAE = ConnectionGraph.addBrokenEqualityConstraintEquations(DAE, broken)
          DAE
        end

         #= @author: adrpo
         returns only the sets containing expandable connectors =#
        function getExpandableEquSetsAsCrefs(sets::List{<:Set}) ::List{List{DAE.ComponentRef}}
              local crefSets::List{List{DAE.ComponentRef}} = nil

              local cref_set::List{DAE.ComponentRef}

              for set in sets
                _ = begin
                  @match set begin
                    Set.SET(ty = ConnectorType.EQU(__))  => begin
                        cref_set = getAllEquCrefs(list(set))
                        if ListUtil.applyAndFold(cref_set, boolOr, isExpandable, false)
                          crefSets = _cons(cref_set, crefSets)
                        end
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
          crefSets
        end

        function removeCrefsFromSets(sets::List{<:Set}, nonUsefulExpandable::List{<:DAE.ComponentRef}) ::List{Set}


              sets = ListUtil.select1(sets, removeCrefsFromSets2, nonUsefulExpandable)
          sets
        end

        function removeCrefsFromSets2(set::Set, nonUsefulExpandable::List{<:DAE.ComponentRef}) ::Bool
              local isInSet::Bool

              local setCrefs::List{DAE.ComponentRef}
              local lst::List{DAE.ComponentRef}

              setCrefs = getAllEquCrefs(list(set))
              lst = ListUtil.intersectionOnTrue(setCrefs, nonUsefulExpandable, ComponentReference.crefEqualNoStringCompare)
              isInSet = listEmpty(lst)
          isInSet
        end

        function mergeEquSetsAsCrefs(setsAsCrefs::List{<:List{<:DAE.ComponentRef}}) ::List{List{DAE.ComponentRef}}


              setsAsCrefs = begin
                  local set::List{DAE.ComponentRef}
                  local rest::List{List{DAE.ComponentRef}}
                  local sets::List{List{DAE.ComponentRef}}
                @match setsAsCrefs begin
                   nil()  => begin
                    nil
                  end

                  set <|  nil()  => begin
                    list(set)
                  end

                  set <| rest  => begin
                      (set, rest) = mergeWithRest(set, rest)
                      sets = mergeEquSetsAsCrefs(rest)
                    _cons(set, sets)
                  end
                end
              end
          setsAsCrefs
        end

        function mergeWithRest(set::List{<:DAE.ComponentRef}, sets::List{<:List{<:DAE.ComponentRef}}, acc::List{<:List{<:DAE.ComponentRef}} = nil) ::Tuple{List{DAE.ComponentRef}, List{List{DAE.ComponentRef}}}



              (set, sets) = begin
                  local set1::List{DAE.ComponentRef}
                  local set2::List{DAE.ComponentRef}
                  local rest::List{List{DAE.ComponentRef}}
                  local b::Bool
                @match (set, sets) begin
                  (_,  nil())  => begin
                    (set, listReverse(acc))
                  end

                  (set1, set2 <| rest)  => begin
                       #=  Could be faster if we had a function for intersectionExist in a set
                       =#
                      b = listEmpty(ListUtil.intersectionOnTrue(set1, set2, ComponentReference.crefEqualNoStringCompare))
                      set = if ! b
                            ListUtil.unionOnTrue(set1, set2, ComponentReference.crefEqualNoStringCompare)
                          else
                            set1
                          end
                      (set, rest) = mergeWithRest(set, rest, ListUtil.consOnTrue(b, set2, acc))
                    (set, rest)
                  end
                end
              end
          (set, sets)
        end

        function getOnlyExpandableConnectedCrefs(sets::List{<:List{<:DAE.ComponentRef}}) ::List{DAE.ComponentRef}
              local usefulConnectedExpandable::List{DAE.ComponentRef} = nil

              for set in sets
                if allCrefsAreExpandable(set)
                  usefulConnectedExpandable = listAppend(set, usefulConnectedExpandable)
                end
              end
          usefulConnectedExpandable
        end

        function allCrefsAreExpandable(connects::List{<:DAE.ComponentRef}) ::Bool
              local allAreExpandable::Bool

              for cr in connects
                if ! isExpandable(cr)
                  allAreExpandable = false
                  return allAreExpandable
                end
              end
              allAreExpandable = true
          allAreExpandable
        end

         #= Generates an array of sets from a connection set. =#
        function generateSetArray(sets::Sets) ::Array{Set}
              local setArray::Array{Set}

               #=  Create a new array.
               =#
              setArray = arrayCreate(sets.setCount, Set.SET(ConnectorType.NO_TYPE(), nil))
               #=  Add connection pointers to the array.
               =#
              setArray = setArrayAddConnections(sets.connections, sets.setCount, setArray)
               #=  Fill the array with sets.
               =#
              setArray = generateSetArray2(sets.sets, nil, setArray)
          setArray
        end

         #= The connection set maintains a list of connections, but when we generate the
          set array which is used to generate the equations we want to merge these sets.
          This function adds pointers to the array, so that when we fill it with
          generateSetArray2 we can follow the pointers to the correct sets. I.e. if sets
          1 and 2 are connected we might add a pointer from 2 to 1, so that all elements
          that belongs to set 2 are instead added to set 1. To make sure that we get
          correct pointers we build a graph and use an algorithm to find the strongly
          connected components in it. =#
        function setArrayAddConnections(connections::List{<:SetConnection}, setCount::ModelicaInteger, sets::Array{<:Set}) ::Array{Set}


              local graph::SetGraph

               #=  Create a new graph, represented as an adjacency list.
               =#
              graph = arrayCreate(setCount, nil)
               #=  Add the connections to the graph.
               =#
              graph = ListUtil.fold(connections, addConnectionToGraph, graph)
               #=  Add the connections to the array with help from the graph.
               =#
              for i in 1:arrayLength(graph)
                (sets, graph) = setArrayAddConnection(i, graph[i], sets, graph)
              end
          sets
        end

         #= Adds a connection to the set graph. =#
        function addConnectionToGraph(connection::SetConnection, graph::SetGraph) ::SetGraph


              local set1::ModelicaInteger
              local set2::ModelicaInteger
              local node1::List{ModelicaInteger}
              local node2::List{ModelicaInteger}

              (set1, set2) = connection
              node1 = arrayGet(graph, set1)
              graph = arrayUpdate(graph, set1, _cons(set2, node1))
              node2 = arrayGet(graph, set2)
              graph = arrayUpdate(graph, set2, _cons(set1, node2))
          graph
        end

         #= Helper function to setArrayAddConnections, adds a connection pointer to the
           set array. =#
        function setArrayAddConnection(set::ModelicaInteger, edges::List{<:ModelicaInteger}, sets::Array{<:Set}, graph::SetGraph) ::Tuple{Array{Set}, SetGraph}



              local edge_lst::List{ModelicaInteger}

              for e in edges
                if e != set
                  sets = setArrayAddConnection2(e, set, sets)
                  edge_lst = graph[e]
                  graph[e] = nil
                  (sets, graph) = setArrayAddConnection(set, edge_lst, sets, graph)
                end
              end
               #=  Create a pointer to the given set.
               =#
          (sets, graph)
        end

         #= Helper function to setArrayAddConnection, adds a pointer from the given
           pointer to the pointee. =#
        function setArrayAddConnection2(setPointer::ModelicaInteger, setPointee::ModelicaInteger, sets::Array{<:Set}) ::Array{Set}


              local set::Set

              set = sets[setPointee]
              sets = begin
                @match set begin
                  Set.SET(__)  => begin
                    arrayUpdate(sets, setPointer, Set.SET_POINTER(setPointee))
                  end

                  Set.SET_POINTER(__)  => begin
                    setArrayAddConnection2(setPointer, set.index, sets)
                  end
                end
              end
               #=  If the set pointed at is a real set, add a pointer to it.
               =#
               #=  If the set pointed at is itself a pointer, follow the pointer until a
               =#
               #=  real set is found (path compression).
               =#
          sets
        end

         #= This function fills the set array with the sets from the set trie. =#
        function generateSetArray2(sets::SetTrie, prefix::List{<:DAE.ComponentRef}, setArray::Array{<:Set}) ::Array{Set}


              setArray = begin
                  local ie::Option{ConnectorElement}
                  local oe::Option{ConnectorElement}
                  local prefix_cr::Option{DAE.ComponentRef}
                  local flow_cr::Option{DAE.ComponentRef}
                @match sets begin
                  SetTrieNode.SET_TRIE_NODE(cref = DAE.WILD(__))  => begin
                    ListUtil.fold1(sets.nodes, generateSetArray2, prefix, setArray)
                  end

                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                    ListUtil.fold1(sets.nodes, generateSetArray2, _cons(sets.cref, prefix), setArray)
                  end

                  SetTrieNode.SET_TRIE_LEAF(insideElement = ie, outsideElement = oe, flowAssociation = flow_cr)  => begin
                      ie = insertFlowAssociationInStreamElement(ie, flow_cr)
                      oe = insertFlowAssociationInStreamElement(oe, flow_cr)
                      prefix_cr = buildElementPrefix(prefix)
                      setArray = setArrayAddElement(ie, prefix_cr, setArray)
                      setArray = setArrayAddElement(oe, prefix_cr, setArray)
                    setArray
                  end

                  _  => begin
                      setArray
                  end
                end
              end
          setArray
        end

         #= If the given element is a stream element, sets the associated flow. Otherwise
          does nothing. =#
        function insertFlowAssociationInStreamElement(element::Option{<:ConnectorElement}, flowCref::Option{<:DAE.ComponentRef}) ::Option{ConnectorElement}


              local el::ConnectorElement

              if isSome(element)
                @match SOME(el) = element
                element = begin
                  @match el begin
                    ConnectorElement.CONNECTOR_ELEMENT(ty = ConnectorType.STREAM(NONE()))  => begin
                        el.ty = ConnectorType.STREAM(flowCref)
                      SOME(el)
                    end

                    _  => begin
                        element
                    end
                  end
                end
              end
          element
        end

         #= Adds a connector element to the set array. =#
        function setArrayAddElement(element::Option{<:ConnectorElement}, prefix::Option{<:DAE.ComponentRef}, sets::Array{<:Set}) ::Array{Set}


              sets = begin
                  local el::ConnectorElement
                  local prefix_cr::DAE.ComponentRef
                   #=  No element, do nothing.
                   =#
                @match (element, prefix) begin
                  (NONE(), _)  => begin
                    sets
                  end

                  (SOME(el && ConnectorElement.CONNECTOR_ELEMENT(__)), NONE())  => begin
                    setArrayUpdate(sets, el.set, el)
                  end

                  (SOME(el && ConnectorElement.CONNECTOR_ELEMENT(__)), SOME(prefix_cr))  => begin
                       #=  An element but no prefix, add the element as it is.
                       =#
                       #=  Both an element and a prefix, add the prefix to the element before adding
                       =#
                       #=  it to the array.
                       =#
                      el.name = ComponentReference.joinCrefs(prefix_cr, el.name)
                    setArrayUpdate(sets, el.set, el)
                  end
                end
              end
          sets
        end

         #= Helper function to generateSetArray2, build a prefix from a list of crefs. =#
        function buildElementPrefix(prefix::List{<:DAE.ComponentRef}) ::Option{DAE.ComponentRef}
              local cref::Option{DAE.ComponentRef}

              local cr::DAE.ComponentRef
              local id::String
              local subs::List{DAE.Subscript}

               #=  If a connector that extends a basic type is used on the top level we
               =#
               #=  don't have a prefix.
               =#
              if listEmpty(prefix)
                cref = NONE()
              else
                cr = listHead(prefix)
                for c in listRest(prefix)
                  @match DAE.CREF_IDENT(ident = id, subscriptLst = subs) = c
                  cr = DAE.CREF_QUAL(id, DAE.T_UNKNOWN_DEFAULT, subs, cr)
                end
                cref = SOME(cr)
              end
          cref
        end

         #= Updates the element at a given index in the set array. =#
        function setArrayUpdate(sets::Array{<:Set}, index::ModelicaInteger, element::ConnectorElement) ::Array{Set}


              local set::Set
              local el::List{ConnectorElement}

              set = sets[index]
              sets = begin
                @match (set, element) begin
                  (Set.SET(__), ConnectorElement.CONNECTOR_ELEMENT(__))  => begin
                      if Config.orderConnections() && isEquType(element.ty)
                        el = ListUtil.mergeSorted(list(element), set.elements, equSetElementLess)
                      else
                        el = _cons(element, set.elements)
                      end
                       #=  Sort the elements if orderConnections is true and the set is an equality set.
                       =#
                       #=  Other sets, just add them.
                       =#
                    arrayUpdate(sets, index, Set.SET(element.ty, el))
                  end

                  (Set.SET_POINTER(__), _)  => begin
                    setArrayUpdate(sets, set.index, element)
                  end
                end
              end
               #=  A pointer, follow the pointer.
               =#
          sets
        end

         #= Comparison function used by setArrayUpdate2 to order equ sets. =#
        function equSetElementLess(element1::ConnectorElement, element2::ConnectorElement) ::Bool
              local isLess::Bool

              isLess = ComponentReference.crefSortFunc(element2.name, element1.name)
          isLess
        end

         #= Returns the set on a given index in the set array. =#
        function setArrayGet(setArray::Array{<:Set}, index::ModelicaInteger) ::Set
              local set::Set

              set = setArray[index]
              set = begin
                @match set begin
                  Set.SET(__)  => begin
                    set
                  end

                  Set.SET_POINTER(__)  => begin
                    setArrayGet(setArray, set.index)
                  end
                end
              end
          set
        end

         #= Dispatches to the correct equation generating function based on the type of
          the given set. =#
        function equationsDispatch(sets::List{<:Set}, connected::DaeEdges, broken::DaeEdges) ::DAE.DAElist
              local DAE::DAE.DAElist = DAE.emptyDae

              local eql::List{ConnectorElement}
              local eqll::List{List{ConnectorElement}}
              local flowThreshold::ModelicaReal = Flags.getConfigReal(Flags.FLOW_THRESHOLD)
              local dae::DAE.DAElist

              for set in sets
                DAE = begin
                  @match set begin
                    Set.SET_POINTER(__)  => begin
                      DAE
                    end

                    Set.SET(ty = ConnectorType.EQU(__))  => begin
                         #=  A set pointer left from generateSetList, ignore it.
                         =#
                         #=  Here we do some overconstrained connection breaking.
                         =#
                        eqll = ConnectionGraph.removeBrokenConnects(set.elements, connected, broken)
                        for eql in eqll
                          DAE = DAEUtil.joinDaes(generateEquEquations(eql), DAE)
                        end
                      DAE
                    end

                    Set.SET(ty = ConnectorType.FLOW(__), elements = eql)  => begin
                      DAEUtil.joinDaes(generateFlowEquations(eql), DAE)
                    end

                    Set.SET(ty = ConnectorType.STREAM(__), elements = eql)  => begin
                      DAEUtil.joinDaes(generateStreamEquations(eql, flowThreshold), DAE)
                    end

                    Set.SET(ty = ConnectorType.NO_TYPE(__))  => begin
                         #=  Should never happen.
                         =#
                        Error.addMessage(Error.INTERNAL_ERROR, list("ConnectUtil.equationsDispatch failed on connection set with no type."))
                      fail()
                    end

                    _  => begin
                          Error.addMessage(Error.INTERNAL_ERROR, list("ConnectUtil.equationsDispatch failed because of unknown reason."))
                        fail()
                    end
                  end
                end
              end
          DAE
        end

         #= A non-flow connection set contains a number of components. Generating the
           equations from this set means equating all the components. For n components,
           this will give n-1 equations. For example, if the set contains the components
           X, Y.A and Z.B, the equations generated will be X = Y.A and X = Z.B. The
           order of the equations depends on whether the compiler flag orderConnections
           is true or false. =#
        function generateEquEquations(elements::List{<:ConnectorElement}) ::DAE.DAElist
              local DAE::DAE.DAElist = DAE.emptyDae

              local eql::List{DAE.Element} = nil
              local e1::ConnectorElement
              local src::DAE.ElementSource
              local x_src::DAE.ElementSource
              local y_src::DAE.ElementSource
              local x::DAE.ComponentRef
              local y::DAE.ComponentRef

              if listEmpty(elements)
                return DAE
              end
              e1 = listHead(elements)
              if Config.orderConnections()
                for e2 in listRest(elements)
                  src = ElementSource.mergeSources(e1.source, e2.source)
                  src = ElementSource.addElementSourceConnect(src, (e1.name, e2.name))
                  eql = _cons(DAE.EQUEQUATION(e1.name, e2.name, src), eql)
                end
              else
                for e2 in listRest(elements)
                  (x, y) = Util.swap(shouldFlipEquEquation(e1.name, e1.source), e1.name, e2.name)
                  src = ElementSource.mergeSources(e1.source, e2.source)
                  src = ElementSource.addElementSourceConnect(src, (x, y))
                  eql = _cons(DAE.EQUEQUATION(x, y, src), eql)
                  e1 = e2
                end
              end
              DAE = DAE.DAE(listReverse(eql))
          DAE
        end

         #= If the flag +orderConnections=false is used, then we should keep the order of
           the connector elements as they occur in the connection (if possible). In that
           case we check if the cref of the first argument to the first connection
           stored in the element source is a prefix of the connector element cref. If
           it isn't, indicate that we should flip the generated equation. =#
        function shouldFlipEquEquation(lhsCref::DAE.ComponentRef, lhsSource::DAE.ElementSource) ::Bool
              local shouldFlip::Bool

              shouldFlip = begin
                  local lhs::DAE.ComponentRef
                @match lhsSource begin
                  DAE.SOURCE(connectEquationOptLst = (lhs, _) <| _)  => begin
                    ! ComponentReference.crefPrefixOf(lhs, lhsCref)
                  end

                  _  => begin
                      false
                  end
                end
              end
          shouldFlip
        end

         #= Generating equations from a flow connection set is a little trickier that
           from a non-flow set. Only one equation is generated, but it has to consider
           whether the components were inside or outside connectors. This function
           creates a sum expression of all components (some of which will be negated),
           and the returns the equation where this sum is equal to 0.0. =#
        function generateFlowEquations(elements::List{<:ConnectorElement}) ::DAE.DAElist
              local DAE::DAE.DAElist

              local sum::DAE.Exp
              local src::DAE.ElementSource

              sum = makeFlowExp(listHead(elements))
              src = getElementSource(listHead(elements))
              for e in listRest(elements)
                sum = Expression.makeRealAdd(sum, makeFlowExp(e))
                src = ElementSource.mergeSources(src, e.source)
              end
              DAE = DAE.DAE(list(DAE.EQUATION(sum, DAE.RCONST(0.0), src)))
          DAE
        end

         #= Creates an expression from a connector element, which is the element itself
           if it's an inside connector, or negated if it's outside. =#
        function makeFlowExp(element::ConnectorElement) ::DAE.Exp
              local exp::DAE.Exp

              exp = Expression.crefExp(element.name)
              if isOutsideElement(element)
                exp = Expression.negateReal(exp)
              end
          exp
        end

        function increaseConnectRefCount(lhsCref::DAE.ComponentRef, rhsCref::DAE.ComponentRef, sets::Sets) ::Sets


              local crefs::List{DAE.ComponentRef}

              if System.getUsesCardinality()
                crefs = ComponentReference.expandCref(lhsCref, false)
                sets.sets = increaseConnectRefCount2(crefs, sets.sets)
                crefs = ComponentReference.expandCref(rhsCref, false)
                sets.sets = increaseConnectRefCount2(crefs, sets.sets)
              end
          sets
        end

        function increaseConnectRefCount2(crefs::List{<:DAE.ComponentRef}, sets::SetTrie) ::SetTrie


              for cr in crefs
                sets = setTrieUpdate(cr, 1, sets, increaseRefCount)
              end
          sets
        end

        function increaseRefCount(amount::ModelicaInteger, node::SetTrieNode) ::SetTrieNode


              _ = begin
                @match node begin
                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                      node.connectCount = node.connectCount + amount
                    ()
                  end

                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      node.connectCount = node.connectCount + amount
                    ()
                  end
                end
              end
          node
        end

         #= Generates the equations for a stream connection set. =#
        function generateStreamEquations(elements::List{<:ConnectorElement}, flowThreshold::ModelicaReal) ::DAE.DAElist
              local DAE::DAE.DAElist

              DAE = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local src1::DAE.ElementSource
                  local src2::DAE.ElementSource
                  local src::DAE.ElementSource
                  local dae::DAE.DAElist
                  local cref1::DAE.Exp
                  local cref2::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local inside::List{ConnectorElement}
                  local outside::List{ConnectorElement}
                   #=  Unconnected stream connector, do nothing!
                   =#
                @match elements begin
                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__)) <|  nil()  => begin
                    DAE.emptyDae
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__)) <| ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__)) <|  nil()  => begin
                    DAE.emptyDae
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(name = cr1, face = Face.OUTSIDE(__), source = src1) <| ConnectorElement.CONNECTOR_ELEMENT(name = cr2, face = Face.OUTSIDE(__), source = src2) <|  nil()  => begin
                       #=  Both inside, do nothing!
                       =#
                       #=  Both outside:
                       =#
                       #=  cr1 = inStream(cr2);
                       =#
                       #=  cr2 = inStream(cr1);
                       =#
                      cref1 = Expression.crefExp(cr1)
                      cref2 = Expression.crefExp(cr2)
                      e1 = makeInStreamCall(cref2)
                      e2 = makeInStreamCall(cref1)
                      src = ElementSource.mergeSources(src1, src2)
                      dae = DAE.DAE(list(DAE.EQUATION(cref1, e1, src), DAE.EQUATION(cref2, e2, src)))
                    dae
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(name = cr1, source = src1) <| ConnectorElement.CONNECTOR_ELEMENT(name = cr2, source = src2) <|  nil()  => begin
                       #=  One inside, one outside:
                       =#
                       #=  cr1 = cr2;
                       =#
                      src = ElementSource.mergeSources(src1, src2)
                      e1 = Expression.crefExp(cr1)
                      e2 = Expression.crefExp(cr2)
                      dae = DAE.DAE(list(DAE.EQUATION(e1, e2, src)))
                    dae
                  end

                  _  => begin
                         #=  The general case with N inside connectors and M outside:
                         =#
                        (outside, inside) = ListUtil.splitOnTrue(elements, isOutsideElement)
                        dae = streamEquationGeneral(outside, inside, flowThreshold)
                      dae
                  end
                end
              end
          DAE
        end

         #= Returns true if the connector element belongs to an outside connector. =#
        function isOutsideElement(element::ConnectorElement) ::Bool
              local isOutside::Bool

              isOutside = begin
                @match element begin
                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.OUTSIDE(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isOutside
        end

         #= Returns true if the given flow attribute of a connector is zero. =#
        function isZeroFlowMinMax(streamCref::DAE.ComponentRef, element::ConnectorElement) ::Bool
              local isZero::Bool

              if compareCrefStreamSet(streamCref, element)
                isZero = false
              elseif isOutsideElement(element)
                isZero = isZeroFlow(element, "max")
              else
                isZero = isZeroFlow(element, "min")
              end
          isZero
        end

         #= Returns true if the given flow attribute of a connector is zero. =#
        function isZeroFlow(element::ConnectorElement, attr::String) ::Bool
              local isZero::Bool

              local ty::DAE.Type
              local attr_oexp::Option{DAE.Exp}
              local flow_exp::DAE.Exp
              local attr_exp::DAE.Exp

              flow_exp = flowExp(element)
              ty = Expression.typeof(flow_exp)
              attr_oexp = Types.lookupAttributeExp(Types.getAttributes(ty), attr)
              if isSome(attr_oexp)
                @match SOME(attr_exp) = attr_oexp
                isZero = Expression.isZero(attr_exp)
              else
                isZero = false
              end
          isZero
        end

         #= Generates an equation for an outside stream connector element. =#
        function streamEquationGeneral(outsideElements::List{<:ConnectorElement}, insideElements::List{<:ConnectorElement}, flowThreshold::ModelicaReal) ::DAE.DAElist
              local DAE::DAE.DAElist

              local outside::List{ConnectorElement}
              local cref_exp::DAE.Exp
              local res::DAE.Exp
              local src::DAE.ElementSource
              local dae::DAE.DAElist
              local name::DAE.ComponentRef
              local eql::List{DAE.Element} = nil

              for e in outsideElements
                cref_exp = Expression.crefExp(e.name)
                outside = removeStreamSetElement(e.name, outsideElements)
                res = streamSumEquationExp(outside, insideElements, flowThreshold)
                src = ElementSource.addAdditionalComment(e.source, " equation generated by stream handling")
                eql = _cons(DAE.EQUATION(cref_exp, res, src), eql)
              end
              DAE = DAE.DAE(eql)
          DAE
        end

         #= Generates the sum expression used by stream connector equations, given M
          outside connectors and N inside connectors:

            (sum(max(-flow_exp[i], eps) * stream_exp[i] for i in N) +
             sum(max( flow_exp[i], eps) * inStream(stream_exp[i]) for i in M)) /
            (sum(max(-flow_exp[i], eps) for i in N) +
             sum(max( flow_exp[i], eps) for i in M))

          where eps = inFlowThreshold.
           =#
        function streamSumEquationExp(outsideElements::List{<:ConnectorElement}, insideElements::List{<:ConnectorElement}, flowThreshold::ModelicaReal) ::DAE.Exp
              local sumExp::DAE.Exp

              local outside_sum1::DAE.Exp
              local outside_sum2::DAE.Exp
              local inside_sum1::DAE.Exp
              local inside_sum2::DAE.Exp
              local res::DAE.Exp

              if listEmpty(outsideElements)
                inside_sum1 = sumMap(insideElements, sumInside1, flowThreshold)
                inside_sum2 = sumMap(insideElements, sumInside2, flowThreshold)
                sumExp = Expression.expDiv(inside_sum1, inside_sum2)
              elseif listEmpty(insideElements)
                outside_sum1 = sumMap(outsideElements, sumOutside1, flowThreshold)
                outside_sum2 = sumMap(outsideElements, sumOutside2, flowThreshold)
                sumExp = Expression.expDiv(outside_sum1, outside_sum2)
              else
                outside_sum1 = sumMap(outsideElements, sumOutside1, flowThreshold)
                outside_sum2 = sumMap(outsideElements, sumOutside2, flowThreshold)
                inside_sum1 = sumMap(insideElements, sumInside1, flowThreshold)
                inside_sum2 = sumMap(insideElements, sumInside2, flowThreshold)
                sumExp = Expression.expDiv(Expression.expAdd(outside_sum1, inside_sum1), Expression.expAdd(outside_sum2, inside_sum2))
              end
               #=  No outside components.
               =#
               #=  No inside components.
               =#
               #=  Both outside and inside components.
               =#
          sumExp
        end

         #= Creates a sum expression by applying the given function on the list of
          elements and summing up the resulting expressions. =#
        function sumMap(elements::List{<:ConnectorElement}, func::FuncType, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              exp = Expression.expAdd(func(e, flowThreshold) for e in listReverse(elements))
          exp
        end

         #= Returns the stream and flow component in a stream set element as expressions. =#
        function streamFlowExp(element::ConnectorElement) ::Tuple{DAE.Exp, DAE.Exp}
              local flowExp::DAE.Exp
              local streamExp::DAE.Exp

              local flow_cr::DAE.ComponentRef

              @match ConnectorElement.CONNECTOR_ELEMENT(ty = ConnectorType.STREAM(SOME(flow_cr))) = element
              streamExp = Expression.crefExp(element.name)
              flowExp = Expression.crefExp(flow_cr)
          (streamExp, flowExp)
        end

         #= Returns the flow component in a stream set element as an expression. =#
        function flowExp(element::ConnectorElement) ::DAE.Exp
              local flowExp::DAE.Exp

              local flow_cr::DAE.ComponentRef

              @match ConnectorElement.CONNECTOR_ELEMENT(ty = ConnectorType.STREAM(SOME(flow_cr))) = element
              flowExp = Expression.crefExp(flow_cr)
          flowExp
        end

         #= Helper function to streamSumEquationExp. Returns the expression
            max(flow_exp, eps) * inStream(stream_exp)
          given a stream set element. =#
        function sumOutside1(element::ConnectorElement, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local stream_exp::DAE.Exp
              local flow_exp::DAE.Exp
              local flow_threshold::DAE.Exp

              (stream_exp, flow_exp) = streamFlowExp(element)
              flow_threshold = DAE.RCONST(flowThreshold)
              exp = Expression.expMul(makePositiveMaxCall(flow_exp, flow_threshold), makeInStreamCall(stream_exp))
          exp
        end

         #= Helper function to streamSumEquationExp. Returns the expression
            max(-flow_exp, eps) * stream_exp
          given a stream set element. =#
        function sumInside1(element::ConnectorElement, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local stream_exp::DAE.Exp
              local flow_exp::DAE.Exp
              local flow_threshold::DAE.Exp
              local flowTy::DAE.Type
              local streamTy::DAE.Type

              (stream_exp, flow_exp) = streamFlowExp(element)
              flowTy = Expression.typeof(flow_exp)
              flow_exp = DAE.UNARY(DAE.UMINUS(flowTy), flow_exp)
              flow_threshold = DAE.RCONST(flowThreshold)
              exp = Expression.expMul(makePositiveMaxCall(flow_exp, flow_threshold), stream_exp)
          exp
        end

         #= Helper function to streamSumEquationExp. Returns the expression
            max(flow_exp, eps)
          given a stream set element. =#
        function sumOutside2(element::ConnectorElement, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local flow_exp::DAE.Exp

              flow_exp = flowExp(element)
              exp = makePositiveMaxCall(flow_exp, DAE.RCONST(flowThreshold))
          exp
        end

         #= Helper function to streamSumEquationExp. Returns the expression
            max(-flow_exp, eps)
          given a stream set element. =#
        function sumInside2(element::ConnectorElement, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local flow_exp::DAE.Exp
              local flowTy::DAE.Type

              flow_exp = flowExp(element)
              flowTy = Expression.typeof(flow_exp)
              flow_exp = DAE.UNARY(DAE.UMINUS(flowTy), flow_exp)
              exp = makePositiveMaxCall(flow_exp, DAE.RCONST(flowThreshold))
          exp
        end

         #= Test for face equality. =#
        function faceEqual(face1::Face, face2::Face) ::Bool
              local sameFaces::Bool = valueConstructor(face1) == valueConstructor(face2)
          sameFaces
        end

         #= Creates an inStream call expression. =#
        function makeInStreamCall(streamExp::DAE.Exp) ::DAE.Exp
              local inStreamCall::DAE.Exp

              local ty::DAE.Type

              ty = Expression.typeof(streamExp)
              inStreamCall = Expression.makeBuiltinCall("inStream", list(streamExp), ty, false)
          inStreamCall
        end

         #= Generates a max(flow_exp, eps) call. =#
        function makePositiveMaxCall(flowExp::DAE.Exp, flowThreshold::DAE.Exp) ::DAE.Exp
              local positiveMaxCall::DAE.Exp

              local ty::DAE.Type
              local attr::List{DAE.Var}
              local nominal_oexp::Option{DAE.Exp}
              local nominal_exp::DAE.Exp
              local flow_threshold::DAE.Exp

              ty = Expression.typeof(flowExp)
              nominal_oexp = Types.lookupAttributeExp(Types.getAttributes(ty), "nominal")
              if isSome(nominal_oexp)
                @match SOME(nominal_exp) = nominal_oexp
                flow_threshold = Expression.expMul(flowThreshold, nominal_exp)
              else
                flow_threshold = flowThreshold
              end
              positiveMaxCall = DAE.CALL(Absyn.IDENT("OMCPositiveMax"), list(flowExp, flow_threshold), DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL()))
              setGlobalRoot(Global.isInStream, SOME(true))
          positiveMaxCall
        end

         #= Evaluates connection operators inStream, actualStream and cardinality in the
           given DAE. =#
        function evaluateConnectionOperators(sets::Sets, setArray::Array{<:Set}, DAE::DAE.DAElist) ::DAE.DAElist


              local flow_threshold::ModelicaReal
              local has_cardinality::Bool = System.getUsesCardinality()

               #=  Only do this phase if we have any connection operators.
               =#
              if System.getHasStreamConnectors() || has_cardinality
                flow_threshold = Flags.getConfigReal(Flags.FLOW_THRESHOLD)
                DAE = DAEUtil.traverseDAE(DAE, DAE.AvlTreePathFunction.Tree.EMPTY(), (has_cardinality, setArray, flow_threshold) -> evaluateConnectionOperators2(hasCardinality = has_cardinality, setArray = setArray, flowThreshold = flow_threshold), sets)
                DAE = simplifyDAEElements(has_cardinality, DAE)
              end
          DAE
        end

         #= Helper function to evaluateConnectionOperators. =#
        function evaluateConnectionOperators2(exp::DAE.Exp, sets::Sets, setArray::Array{<:Set}, hasCardinality::Bool, flowThreshold::ModelicaReal) ::Tuple{DAE.Exp, Sets}



              local changed::Bool

              (exp, changed) = Expression.traverseExpBottomUp(exp, (sets, setArray, flowThreshold) -> evaluateConnectionOperatorsExp(sets = sets, setArray = setArray, flowThreshold = flowThreshold), false)
               #=  Only apply simplify if the expression changed *AND* we have cardinality.
               =#
              if changed && hasCardinality
                exp = ExpressionSimplify.simplify(exp)
              end
          (exp, sets)
        end

         #= Helper function to evaluateConnectionOperators2. Checks if the given
           expression is a call to inStream or actualStream, and if so calls the
           appropriate function in ConnectUtil to evaluate the call. =#
        function evaluateConnectionOperatorsExp(exp::DAE.Exp, sets::Sets, setArray::Array{<:Set}, flowThreshold::ModelicaReal, changed::Bool) ::Tuple{DAE.Exp, Bool}



              (exp, changed) = begin
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                @match exp begin
                  DAE.CALL(path = Absyn.IDENT("inStream"), expLst = DAE.CREF(componentRef = cr) <|  nil())  => begin
                      e = evaluateInStream(cr, sets, setArray, flowThreshold)
                       #= print(\"Evaluated inStream(\" + ExpressionDump.dumpExpStr(DAE.CREF(cr, ty), 0) + \") ->\\n\" + ExpressionDump.dumpExpStr(e, 0) + \"\\n\");
                       =#
                    (e, true)
                  end

                  DAE.CALL(path = Absyn.IDENT("actualStream"), expLst = DAE.CREF(componentRef = cr) <|  nil())  => begin
                      e = evaluateActualStream(cr, sets, setArray, flowThreshold)
                       #= print(\"Evaluated actualStream(\" + ExpressionDump.dumpExpStr(DAE.CREF(cr, ty), 0) + \") ->\\n\" + ExpressionDump.dumpExpStr(e, 0) + \"\\n\");
                       =#
                    (e, true)
                  end

                  DAE.CALL(path = Absyn.IDENT("cardinality"), expLst = DAE.CREF(componentRef = cr) <|  nil())  => begin
                      e = evaluateCardinality(cr, sets)
                    (e, true)
                  end

                  _  => begin
                      (exp, changed)
                  end
                end
              end
          (exp, changed)
        end

         #= @author: adrpo
         does an array out of exp if needed =#
        function mkArrayIfNeeded(ty::DAE.Type, exp::DAE.Exp) ::DAE.Exp


              exp = Expression.arrayFill(Types.getDimensions(ty), exp)
          exp
        end

         #= This function evaluates the inStream operator for a component reference,
           given the connection sets. =#
        function evaluateInStream(streamCref::DAE.ComponentRef, sets::Sets, setArray::Array{<:Set}, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local e::ConnectorElement
              local sl::List{ConnectorElement}
              local set::ModelicaInteger

              try
                e = findElement(streamCref, Face.INSIDE(), ConnectorType.STREAM(NONE()), DAE.emptyElementSource, sets)
                if isNewElement(e)
                  sl = list(e)
                else
                  @match ConnectorElement.CONNECTOR_ELEMENT(set = set) = e
                  @match Set.SET(ty = ConnectorType.STREAM(), elements = sl) = setArrayGet(setArray, set)
                end
                exp = generateInStreamExp(streamCref, sl, sets, setArray, flowThreshold)
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- ConnectUtil.evaluateInStream failed for " + ComponentReference.crefStr(streamCref) + "\\n")
              end
               #=  A new element means that the stream element couldn't be found in the sets
               =#
               #=  => unconnected stream connector.
               =#
               #=  Otherwise, fetch the set that the element belongs to and evaluate the
               =#
               #=  inStream call.
               =#
          exp
        end

         #= Helper function to evaluateInStream. Generates an expression for inStream
          given a connection set. =#
        function generateInStreamExp(streamCref::DAE.ComponentRef, streams::List{<:ConnectorElement}, sets::Sets, setArray::Array{<:Set}, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local reducedStreams::List{ConnectorElement}

              reducedStreams = ListUtil.filterOnFalse(streams, (streamCref) -> isZeroFlowMinMax(streamCref = streamCref))
              exp = begin
                  local c::DAE.ComponentRef
                  local f1::Face
                  local f2::Face
                  local e::DAE.Exp
                  local expr::DAE.Exp
                  local inside::List{ConnectorElement}
                  local outside::List{ConnectorElement}
                   #=  Unconnected stream connector:
                   =#
                   #=  inStream(c) = c;
                   =#
                @match reducedStreams begin
                  ConnectorElement.CONNECTOR_ELEMENT(name = c, face = Face.INSIDE(__)) <|  nil()  => begin
                    Expression.crefExp(c)
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__)) <| ConnectorElement.CONNECTOR_ELEMENT(face = Face.INSIDE(__)) <|  nil()  => begin
                       #=  Two inside connected stream connectors:
                       =#
                       #=  inStream(c1) = c2;
                       =#
                       #=  inStream(c2) = c1;
                       =#
                      @match list(ConnectorElement.CONNECTOR_ELEMENT(name = c)) = removeStreamSetElement(streamCref, reducedStreams)
                      e = Expression.crefExp(c)
                    e
                  end

                  ConnectorElement.CONNECTOR_ELEMENT(face = f1) <| ConnectorElement.CONNECTOR_ELEMENT(face = f2) <|  nil() where (! faceEqual(f1, f2))  => begin
                       #=  One inside, one outside connected stream connector:
                       =#
                       #=  inStream(c1) = inStream(c2);
                       =#
                      @match list(ConnectorElement.CONNECTOR_ELEMENT(name = c)) = removeStreamSetElement(streamCref, reducedStreams)
                      e = evaluateInStream(c, sets, setArray, flowThreshold)
                    e
                  end

                  _  => begin
                         #=  The general case:
                         =#
                        (outside, inside) = ListUtil.splitOnTrue(reducedStreams, isOutsideElement)
                        inside = removeStreamSetElement(streamCref, inside)
                        e = streamSumEquationExp(outside, inside, flowThreshold)
                        if ! listEmpty(inside)
                          expr = streamFlowExp(ListUtil.first(inside))
                          e = Expression.makePureBuiltinCall("OMCinStreamDiv", list(e, expr), Expression.typeof(e))
                        end
                         #=  Evaluate any inStream calls that were generated.
                         =#
                        e = evaluateConnectionOperators2(e, sets, setArray, false, flowThreshold)
                      e
                  end
                end
              end
          exp
        end

         #= This function evaluates the actualStream operator for a component reference,
          given the connection sets. =#
        function evaluateActualStream(streamCref::DAE.ComponentRef, sets::Sets, setArray::Array{<:Set}, flowThreshold::ModelicaReal) ::DAE.Exp
              local exp::DAE.Exp

              local flow_cr::DAE.ComponentRef
              local e::DAE.Exp
              local flow_exp::DAE.Exp
              local stream_exp::DAE.Exp
              local instream_exp::DAE.Exp
              local rel_exp::DAE.Exp
              local ety::DAE.Type
              local flow_dir::ModelicaInteger

              flow_cr = getStreamFlowAssociation(streamCref, sets)
              ety = ComponentReference.crefLastType(flow_cr)
              flow_dir = evaluateFlowDirection(ety)
               #=  Select a branch if we know the flow direction, otherwise generate the whole
               =#
               #=  if-equation.
               =#
              if flow_dir == 1
                rel_exp = evaluateInStream(streamCref, sets, setArray, flowThreshold)
              elseif flow_dir == (-1)
                rel_exp = Expression.crefExp(streamCref)
              else
                flow_exp = Expression.crefExp(flow_cr)
                stream_exp = Expression.crefExp(streamCref)
                instream_exp = evaluateInStream(streamCref, sets, setArray, flowThreshold)
                rel_exp = DAE.IFEXP(DAE.RELATION(flow_exp, DAE.GREATER(ety), DAE.RCONST(0.0), -1, NONE()), instream_exp, stream_exp)
              end
               #=  actualStream(stream_var) = smooth(0, if flow_var > 0 then inStream(stream_var)
               =#
               #=                                                       else stream_var);
               =#
              exp = DAE.CALL(Absyn.IDENT("smooth"), list(DAE.ICONST(0), rel_exp), DAE.callAttrBuiltinReal)
          exp
        end

         #= Checks the min/max attributes of a flow variables type to try and determine
          the flow direction. If the flow is positive 1 is returned, if it is negative
          -1, otherwise 0 if the direction can't be decided. =#
        function evaluateFlowDirection(ty::DAE.Type) ::ModelicaInteger
              local direction::ModelicaInteger = 0

              local attr::List{DAE.Var}
              local min_oval::Option{Values.Value}
              local max_oval::Option{Values.Value}
              local min_val::ModelicaReal
              local max_val::ModelicaReal

              attr = Types.getAttributes(ty)
              if listEmpty(attr)
                return direction
              end
              min_oval = Types.lookupAttributeValue(attr, "min")
              max_oval = Types.lookupAttributeValue(attr, "max")
              direction = begin
                @match (min_oval, max_oval) begin
                  (NONE(), NONE())  => begin
                    0
                  end

                  (SOME(Values.REAL(min_val)), NONE())  => begin
                    if min_val >= 0
                          1
                        else
                          0
                        end
                  end

                  (NONE(), SOME(Values.REAL(max_val)))  => begin
                    if max_val <= 0
                          -1
                        else
                          0
                        end
                  end

                  (SOME(Values.REAL(min_val)), SOME(Values.REAL(max_val)))  => begin
                    if min_val >= 0 && max_val >= min_val
                          1
                        elseif (max_val <= 0 && min_val <= max_val)
                              -1
                        else
                          0
                        end
                  end

                  _  => begin
                      0
                  end
                end
              end
               #=  No attributes, flow direction can't be decided.
               =#
               #=  Flow is positive if min is positive.
               =#
               #=  Flow is negative if max is negative.
               =#
               #=  Flow is positive if both min and max are positive, negative if they are
               =#
               #=  both negative, otherwise undecideable.
               =#
          direction
        end

        function evaluateCardinality(cref::DAE.ComponentRef, sets::Sets) ::DAE.Exp
              local exp::DAE.Exp

              exp = DAE.ICONST(getConnectCount(cref, sets.sets))
          exp
        end

         #= run this only if we have cardinality =#
        function simplifyDAEElements(hasCardinality::Bool, DAE::DAE.DAElist) ::DAE.DAElist


              if hasCardinality
                DAE = DAE.DAE(ListUtil.mapFlat(DAE.elementLst, simplifyDAEElement))
              end
          DAE
        end

        function simplifyDAEElement(element::DAE.Element) ::List{DAE.Element}
              local elements::List{DAE.Element}

              elements = begin
                  local conds::List{DAE.Exp}
                  local branches::List{List{DAE.Element}}
                  local else_branch::List{DAE.Element}
                @matchcontinue element begin
                  DAE.IF_EQUATION(conds, branches, else_branch)  => begin
                    simplifyDAEIfEquation(conds, branches, else_branch)
                  end

                  DAE.INITIAL_IF_EQUATION(conds, branches, else_branch)  => begin
                    simplifyDAEIfEquation(conds, branches, else_branch)
                  end

                  DAE.ASSERT(condition = DAE.BCONST(true))  => begin
                    nil
                  end

                  _  => begin
                      list(element)
                  end
                end
              end
          elements
        end

        function simplifyDAEIfEquation(conditions::List{<:DAE.Exp}, branches::List{<:List{<:DAE.Element}}, elseBranch::List{<:DAE.Element}) ::List{DAE.Element}
              local elements::List{DAE.Element}

              local cond_value::Bool
              local rest_branches::List{List{DAE.Element}} = branches

              for cond in conditions
                @match DAE.BCONST(cond_value) = cond
                if cond_value == true
                  elements = listReverse(listHead(rest_branches))
                  return elements
                end
                rest_branches = listRest(rest_branches)
              end
               #=  Condition is true, substitute if-equation with the branch contents.
               =#
               #=  Condition is false, discard the branch and continue with the other branches.
               =#
               #=  All conditions were false, substitute if-equation with else-branch contents.
               =#
              elements = listReverse(elseBranch)
          elements
        end

         #= This function removes the given cref from a connection set. =#
        function removeStreamSetElement(cref::DAE.ComponentRef, elements::List{<:ConnectorElement}) ::List{ConnectorElement}


              elements = ListUtil.deleteMemberOnTrue(cref, elements, compareCrefStreamSet)
          elements
        end

         #= Helper function to removeStreamSetElement. Checks if the cref in a stream set
          element matches the given cref. =#
        function compareCrefStreamSet(cref::DAE.ComponentRef, element::ConnectorElement) ::Bool
              local matches::Bool

              matches = ComponentReference.crefEqualNoStringCompare(cref, element.name)
          matches
        end

         #= This function determines whether a component
          reference refers to an inner or outer connector:
          Rules:
            qualified cref and connector     => OUTSIDE
            non-qualifed cref                => OUTSIDE
            qualified cref and non-connector => INSIDE

          Modelica Specification 4.0
          Section: 9.1.2 Inside and Outside Connectors
          In an element instance M, each connector element of M is called an outside connector with respect to M.
          All other connector elements that are hierarchically inside M, but not in one of the outside connectors
          of M, is called an inside connector with respect to M. This is done **BEFORE** resolving outer elements
          to corresponding inner ones. =#
        function componentFace(env::FCore.Graph, componentRef::DAE.ComponentRef) ::Face
              local face::Face

              face = begin
                  local id::DAE.Ident
                   #=  is a non-qualified cref => OUTSIDE
                   =#
                @matchcontinue componentRef begin
                  DAE.CREF_IDENT(__)  => begin
                    Face.OUTSIDE()
                  end

                  DAE.CREF_QUAL(ident = id)  => begin
                       #=  is a qualified cref and is a connector => OUTSIDE
                       =#
                      @match (_, _, DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _)), _, _, _, _, _, _) = Lookup.lookupVar(FCoreUtil.emptyCache(), env, ComponentReference.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil))
                    Face.OUTSIDE()
                  end

                  DAE.CREF_QUAL(__)  => begin
                    Face.INSIDE()
                  end
                end
              end
               #=  is a qualified cref and is NOT a connector => INSIDE
               =#
          face
        end

         #= Author: BZ, 2008-12
          Same functionalty as componentFace, with the difference that
          this function checks ident-type rather then env->lookup ==> type.
          Rules:
            qualified cref and connector     => OUTSIDE
            non-qualifed cref                => OUTSIDE
            qualified cref and non-connector => INSIDE

          Modelica Specification 4.0
          Section: 9.1.2 Inside and Outside Connectors
          In an element instance M, each connector element of M is called an outside connector with respect to M.
          All other connector elements that are hierarchically inside M, but not in one of the outside connectors
          of M, is called an inside connector with respect to M. This is done **BEFORE** resolving outer elements
          to corresponding inner ones. =#
        function componentFaceType(inComponentRef::DAE.ComponentRef) ::Face
              local outFace::Face

              outFace = begin
                @match inComponentRef begin
                  DAE.CREF_IDENT(__)  => begin
                    Face.OUTSIDE()
                  end

                  DAE.CREF_QUAL(identType = DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _)))  => begin
                    Face.OUTSIDE()
                  end

                  DAE.CREF_QUAL(identType = DAE.T_ARRAY(ty = DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _))))  => begin
                    Face.OUTSIDE()
                  end

                  DAE.CREF_QUAL(__)  => begin
                    Face.INSIDE()
                  end
                end
              end
               #=  is a non-qualified cref => OUTSIDE
               =#
               #=  is a qualified cref and is a connector => OUTSIDE
               =#
               #=  is a qualified cref and is an array of connectors => OUTSIDE
               =#
               #=  is a qualified cref and is NOT a connector => INSIDE
               =#
          outFace
        end

         #= Checks if a connector class is balanced or not, according to the rules in the
          Modelica 3.2 specification. =#
        function checkConnectorBalance(vars::List{<:DAE.Var}, path::Absyn.Path, info::SourceInfo)
              local potentials::ModelicaInteger
              local flows::ModelicaInteger
              local streams::ModelicaInteger

              (potentials, flows, streams) = countConnectorVars(vars)
              @match true = checkConnectorBalance2(potentials, flows, streams, path, info)
               #= print(AbsynUtil.pathString(path) + \" has:\\n\\t\" +
               =#
               #=   String(potentials) + \" potential variables\\n\\t\" +
               =#
               #=   String(flows) + \" flow variables\\n\\t\" +
               =#
               #=   String(streams) + \" stream variables\\n\\n\");
               =#
        end

        function checkConnectorBalance2(potentialVars::ModelicaInteger, flowVars::ModelicaInteger, streamVars::ModelicaInteger, path::Absyn.Path, info::SourceInfo) ::Bool
              local isBalanced::Bool = true

              local error_str::String
              local flow_str::String
              local potential_str::String
              local class_str::String

               #=  Don't check connector balance for language version 2.x and earlier.
               =#
              if Config.languageStandardAtMost(Config.LanguageStandard.S2_x)
                return isBalanced
              end
               #=  Modelica 3.2 section 9.3.1:
               =#
               #=  For each non-partial connector class the number of flow variables shall
               =#
               #=  be equal to the number of variables that are neither parameter, constant,
               =#
               #=  input, output, stream nor flow.
               =#
              if potentialVars != flowVars
                flow_str = String(flowVars)
                potential_str = String(potentialVars)
                class_str = AbsynUtil.pathString(path)
                error_str = stringAppendList(list("The number of potential variables (", potential_str, ") is not equal to the number of flow variables (", flow_str, ")."))
                Error.addSourceMessage(Error.UNBALANCED_CONNECTOR, list(class_str, error_str), info)
              end
               #=  This should be a hard error, but there are models that contain such
               =#
               #=  connectors. So we print an error but return that the connector is balanced.
               =#
               #=  Modelica 3.2 section 15.1:
               =#
               #=  A stream connector must have exactly one scalar variable with the flow prefix.
               =#
              if streamVars > 0 && flowVars != 1
                flow_str = String(flowVars)
                class_str = AbsynUtil.pathString(path)
                error_str = stringAppendList(list("A stream connector must have exactly one flow variable, this connector has ", flow_str, " flow variables."))
                Error.addSourceMessage(Error.INVALID_STREAM_CONNECTOR, list(class_str, error_str), info)
                isBalanced = false
              end
          isBalanced
        end

         #= Given a list of connector variables, this function counts how many potential,
          flow and stream variables it contains. =#
        function countConnectorVars(vars::List{<:DAE.Var}) ::Tuple{ModelicaInteger, ModelicaInteger, ModelicaInteger}
              local streamVars::ModelicaInteger = 0
              local flowVars::ModelicaInteger = 0
              local potentialVars::ModelicaInteger = 0

              local ty::DAE.Type
              local ty2::DAE.Type
              local attr::DAE.Attributes
              local n::ModelicaInteger
              local p::ModelicaInteger
              local f::ModelicaInteger
              local s::ModelicaInteger

              for var in vars
                @match DAE.TYPES_VAR(ty = ty, attributes = attr) = var
                ty2 = Types.arrayElementType(ty)
                if Types.isConnector(ty2)
                  n = product(dim for dim in Types.getDimensionSizes(ty))
                  (p, f, s) = countConnectorVars(Types.getConnectorVars(ty2))
                  if AbsynUtil.isInputOrOutput(DAEUtil.getAttrDirection(attr))
                    p = 0
                  end
                  potentialVars = potentialVars + p * n
                  flowVars = flowVars + f * n
                  streamVars = streamVars + s * n
                else
                  _ = begin
                    @match attr begin
                      DAE.ATTR(connectorType = DAE.FLOW(__))  => begin
                           #=  Check if we have a connector inside a connector.
                           =#
                           #=  If we have an array of connectors, count the elements.
                           =#
                           #=  Count the number of different variables inside the connector, and then
                           =#
                           #=  multiply those numbers with the dimensions of the array.
                           =#
                           #=  If the variable is input/output we don't count potential variables.
                           =#
                           #=  A flow variable.
                           =#
                          flowVars = flowVars + sizeOfType(var.ty)
                        ()
                      end

                      DAE.ATTR(connectorType = DAE.STREAM(__))  => begin
                           #=  A stream variable.
                           =#
                          streamVars = streamVars + sizeOfType(var.ty)
                        ()
                      end

                      DAE.ATTR(direction = Absyn.BIDIR(__), variability = SCode.VAR(__))  => begin
                           #=  A potential variable.
                           =#
                          potentialVars = potentialVars + sizeOfType(var.ty)
                        ()
                      end

                      _  => begin
                          ()
                      end
                    end
                  end
                end
              end
          (potentialVars, flowVars, streamVars)
        end

         #= Calls sizeOfVariable on a list of variables, and adds up the results. =#
        function sizeOfVariableList(vars::List{<:DAE.Var}) ::ModelicaInteger
              local size::ModelicaInteger = 0

              for var in vars
                size = size + sizeOfType(var.ty)
              end
          size
        end

         #= Different types of variables have different size, for example arrays. This
           function checks the size of one variable. =#
        function sizeOfType(ty::DAE.Type) ::ModelicaInteger
              local size::ModelicaInteger

              size = begin
                  local n::ModelicaInteger
                  local t::DAE.Type
                  local v::List{DAE.Var}
                   #=  Scalar values consist of one element.
                   =#
                @match ty begin
                  DAE.T_INTEGER(__)  => begin
                    1
                  end

                  DAE.T_REAL(__)  => begin
                    1
                  end

                  DAE.T_STRING(__)  => begin
                    1
                  end

                  DAE.T_BOOL(__)  => begin
                    1
                  end

                  DAE.T_ENUMERATION(index = NONE())  => begin
                    1
                  end

                  DAE.T_ARRAY(__)  => begin
                    intMul(Expression.dimensionSize(dim) for dim in ty.dims) * sizeOfType(ty.ty)
                  end

                  DAE.T_COMPLEX(varLst = v, equalityConstraint = NONE())  => begin
                    sizeOfVariableList(v)
                  end

                  DAE.T_COMPLEX(equalityConstraint = SOME((_, n, _)))  => begin
                    n
                  end

                  DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
                    0
                  end

                  DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
                    sizeOfType(t)
                  end

                  _  => begin
                         #=  The size of an array is its dimension multiplied with the size of its type.
                         =#
                         #=  The size of a complex type without an equalityConstraint (such as a
                         =#
                         #=  record), is the sum of the sizes of its components.
                         =#
                         #=  The size of a complex type with an equalityConstraint function is
                         =#
                         #=  determined by the size of the return value of that function.
                         =#
                         #=  The size of a basic subtype with equality constraint is ZERO.
                         =#
                         #=  The size of a basic subtype is the size of the extended type.
                         =#
                         #=  Anything we forgot?
                         =#
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- ConnectUtil.sizeOfType failed on " + Types.printTypeStr(ty))
                      fail()
                  end
                end
              end
          size
        end

         #= Checks a short connector definition that has extended a basic type, i.e.
           connector C = Real;. =#
        function checkShortConnectorDef(state::ClassInf.SMNode, attributes::SCode.Attributes, info::SourceInfo) ::Bool
              local isValid::Bool

              isValid = begin
                  local pv::ModelicaInteger = 0
                  local fv::ModelicaInteger = 0
                  local sv::ModelicaInteger = 0
                  local ct::SCode.ConnectorType
                   #=  Extended from bidirectional basic type, which means that it can't be
                   =#
                   #=  balanced.
                   =#
                @match (state, attributes) begin
                  (ClassInf.CONNECTOR(__), SCode.ATTR(connectorType = ct, direction = Absyn.BIDIR(__)))  => begin
                       #=  The connector might be either flow, stream or neither.
                       =#
                       #=  This will set either fv, sv, or pv to 1, and the rest to 0, and
                       =#
                       #=  checkConnectorBalance2 will then be called to provide the appropriate
                       =#
                       #=  error message (or might actually succeed if +std=2.x or 1.x).
                       =#
                      if SCodeUtil.flowBool(ct)
                        fv = 1
                      elseif SCodeUtil.streamBool(ct)
                        sv = 1
                      else
                        pv = 1
                      end
                    checkConnectorBalance2(pv, fv, sv, state.path, info)
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  All other cases are ok.
               =#
          isValid
        end

        function isReferenceInConnects(connects::List{<:ConnectorElement}, cref::DAE.ComponentRef) ::Bool
              local isThere::Bool = false

              for ce in connects
                if ComponentReference.crefPrefixOf(cref, ce.name)
                  isThere = true
                  return isThere
                end
              end
          isThere
        end

        function removeReferenceFromConnects(connects::List{<:ConnectorElement}, cref::DAE.ComponentRef) ::Tuple{List{ConnectorElement}, Bool}
              local wasRemoved::Bool


              local oe::Option{ConnectorElement}

              (connects, oe) = ListUtil.deleteMemberOnTrue(cref, connects, removeReferenceFromConnects2)
              wasRemoved = isSome(oe)
          (connects, wasRemoved)
        end

        function removeReferenceFromConnects2(cref::DAE.ComponentRef, element::ConnectorElement) ::Bool
              local matches::Bool

              matches = ComponentReference.crefPrefixOf(cref, element.name)
          matches
        end

         #= Prints a Sets to a String. =#
        function printSetsStr(sets::Sets) ::String
              local string::String

              string = String(sets.setCount) + " sets:\\n"
              string = string + printSetTrieStr(sets.sets, "\\t")
              string = string + "Connected sets:\\n"
              string = string + printSetConnections(sets.connections) + "\\n"
          string
        end

         #= Prints a SetTrie to a String. =#
        function printSetTrieStr(trie::SetTrie, accumName::String) ::String
              local string::String

              string = begin
                  local name::String
                  local res::String
                @match trie begin
                  SetTrieNode.SET_TRIE_LEAF(__)  => begin
                      res = accumName + "." + trie.name + ":"
                      res = res + printLeafElementStr(trie.insideElement)
                      res = res + printLeafElementStr(trie.outsideElement)
                      res = res + printOptFlowAssociation(trie.flowAssociation) + "\\n"
                    res
                  end

                  SetTrieNode.SET_TRIE_NODE(name = "")  => begin
                    stringAppendList(ListUtil.map1(trie.nodes, printSetTrieStr, accumName))
                  end

                  SetTrieNode.SET_TRIE_NODE(__)  => begin
                      name = accumName + "." + trie.name
                      res = stringAppendList(ListUtil.map1(trie.nodes, printSetTrieStr, name))
                    res
                  end
                end
              end
          string
        end

         #= Prints an optional connector element to a String. =#
        function printLeafElementStr(element::Option{<:ConnectorElement}) ::String
              local string::String

              string = begin
                  local e::ConnectorElement
                  local res::String
                @match element begin
                  SOME(e && ConnectorElement.CONNECTOR_ELEMENT(__))  => begin
                      res = " " + printFaceStr(e.face) + " "
                      res = res + printConnectorTypeStr(e.ty) + " [" + String(e.set) + "]"
                    res
                  end

                  _  => begin
                      ""
                  end
                end
              end
          string
        end

         #= Prints a connector element to a String. =#
        function printElementStr(element::ConnectorElement) ::String
              local string::String

              string = ComponentReference.printComponentRefStr(element.name) + " "
              string = string + printFaceStr(element.face) + " "
              string = string + printConnectorTypeStr(element.ty) + " [" + String(element.set) + "]"
          string
        end

         #= Prints the Face to a String. =#
        function printFaceStr(face::Face) ::String
              local string::String

              string = begin
                @match face begin
                  Face.INSIDE(__)  => begin
                    "inside"
                  end

                  Face.OUTSIDE(__)  => begin
                    "outside"
                  end

                  Face.NO_FACE(__)  => begin
                    "unknown"
                  end
                end
              end
          string
        end

         #= Prints the connector type to a String. =#
        function printConnectorTypeStr(ty::ConnectorType) ::String
              local string::String

              string = begin
                @match ty begin
                  ConnectorType.EQU(__)  => begin
                    "equ"
                  end

                  ConnectorType.FLOW(__)  => begin
                    "flow"
                  end

                  ConnectorType.STREAM(__)  => begin
                    "stream"
                  end
                end
              end
          string
        end

         #= Print an optional flow association to a String. =#
        function printOptFlowAssociation(cref::Option{<:DAE.ComponentRef}) ::String
              local string::String

              string = begin
                  local cr::DAE.ComponentRef
                @match cref begin
                  NONE()  => begin
                    ""
                  end

                  SOME(cr)  => begin
                    " associated flow: " + ComponentReference.printComponentRefStr(cr)
                  end
                end
              end
          string
        end

         #= Prints a list of set connection to a String. =#
        function printSetConnections(connections::List{<:SetConnection}) ::String
              local string::String

              string = stringAppendList(ListUtil.map(connections, printSetConnection))
          string
        end

         #= Prints a set connection to a String. =#
        function printSetConnection(connection::SetConnection) ::String
              local string::String

              local set1::ModelicaInteger
              local set2::ModelicaInteger

              (set1, set2) = connection
              string = "\\t" + String(set1) + " connected to " + intString(set2) + "\\n"
          string
        end

         #= Prints a Set to a String. =#
        function printSetStr(set::Set) ::String
              local string::String

              string = begin
                @match set begin
                  Set.SET(__)  => begin
                    stringDelimitList(ListUtil.map(set.elements, printElementStr), ", ")
                  end

                  Set.SET_POINTER(__)  => begin
                    "pointer to set " + intString(set.index)
                  end
                end
              end
          string
        end

         #= @author: adrpo
         return all crefs present in EQU sets =#
        function getAllEquCrefs(sets::List{<:Set}) ::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef} = nil

              for set in sets
                _ = begin
                  @match set begin
                    Set.SET(ty = ConnectorType.EQU(__))  => begin
                        for e in set.elements
                          crefs = _cons(e.name, crefs)
                        end
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
          crefs
        end

         #= @author: adrpo
         this function will remove all unconnected/unused/unnecessary expandable variables and connections from the DAE.
         NOTE that this is not so obvious:
         1. collect all expandable variables crefs
         2. collect all expandable crefs used in the DAE (with the expandable variables THAT HAVE NO BINDING removed)
         3. get all expandable crefs that are connected ONLY with expandable
         4. substract: (3)-(2)
         5. remove (4) from the DAE and connection sets
         6. get all the connected potential variables
         7. substract (2) from (1)
         8. substract (6) from (7)
         9. remove (8) from the DAE (5) =#
        function removeUnusedExpandableVariablesAndConnections(sets::List{<:Set}, DAE::DAE.DAElist) ::Tuple{List{Set}, DAE.DAElist}



              local elems::List{DAE.Element}
              local expandableVars::List{DAE.ComponentRef}
              local unnecessary::List{DAE.ComponentRef}
              local usedInDAE::List{DAE.ComponentRef}
              local onlyExpandableConnected::List{DAE.ComponentRef}
              local equVars::List{DAE.ComponentRef}
              local dae::DAE.DAElist
              local setsAsCrefs::List{List{DAE.ComponentRef}}

              @match DAE.DAE(elems) = DAE
               #=  1 - get all expandable crefs
               =#
              expandableVars = getExpandableVariablesWithNoBinding(elems)
               #=  print(\"All expandable (1):\\n  \" + stringDelimitList(List.map(expandableVars, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
               #=  2 - remove all expandable without binding from the dae
               =#
              dae = DAEUtil.removeVariables(DAE, expandableVars)
               #=  2 - get all expandable crefs used in the dae (without the expandable vars)
               =#
              usedInDAE = DAEUtil.getAllExpandableCrefsFromDAE(dae)
               #=  print(\"Used in the DAE (2):\\n  \" + stringDelimitList(List.map(usedInDAE, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
               #=  3 - get all expandable crefs that are connected ONLY with expandable
               =#
              setsAsCrefs = getExpandableEquSetsAsCrefs(sets)
              setsAsCrefs = mergeEquSetsAsCrefs(setsAsCrefs)
               #=  TODO! FIXME! maybe we should do fixpoint here??
               =#
              setsAsCrefs = mergeEquSetsAsCrefs(setsAsCrefs)
              onlyExpandableConnected = getOnlyExpandableConnectedCrefs(setsAsCrefs)
               #=  print(\"All expandable - expandable connected (3):\\n  \" + stringDelimitList(List.map(onlyExpandableConnected, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
               #=  4 - subtract (2) from (3)
               =#
              unnecessary = ListUtil.setDifferenceOnTrue(onlyExpandableConnected, usedInDAE, ComponentReference.crefEqualWithoutSubs)
               #=  print(\"REMOVE: (3)-(2):\\n  \" + stringDelimitList(List.map(unnecessary, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
               #=  5 - remove unnecessary variables form the DAE
               =#
              DAE = DAEUtil.removeVariables(DAE, unnecessary)
               #=  5 - remove unnecessary variables form the connection sets
               =#
              sets = removeCrefsFromSets(sets, unnecessary)
              equVars = getAllEquCrefs(sets)
               #=  print(\"(6):\\n  \" + stringDelimitList(List.map(equVars, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
              expandableVars = ListUtil.setDifferenceOnTrue(expandableVars, usedInDAE, ComponentReference.crefEqualWithoutSubs)
               #=  print(\"(1)-(2)=(7):\\n  \" + stringDelimitList(List.map(equVars, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
              unnecessary = ListUtil.setDifferenceOnTrue(expandableVars, equVars, ComponentReference.crefEqualWithoutSubs)
               #=  print(\"REMOVE: (7)-(6):\\n  \" + stringDelimitList(List.map(unnecessary, ComponentReference.printComponentRefStr), \"\\n  \") + \"\\n\");
               =#
              DAE = DAEUtil.removeVariables(DAE, unnecessary)
          (sets, DAE)
        end

        function isEquType(ty::ConnectorType) ::Bool
              local isEqu::Bool

              isEqu = begin
                @match ty begin
                  ConnectorType.EQU(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isEqu
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

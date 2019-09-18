  module ConnectionGraph


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl ConnectionGraphType

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

        import DAE

        import DAEUtil

        import HashTable

        import HashTable3

        import HashTableCG

        import Connect

        Edge = Tuple  #= an edge is a tuple with two component references =#

        Edges = List  #= A list of edges =#

        DaeEdge = Tuple  #= a tuple with two crefs and dae elements for equatityConstraint function call =#

        DaeEdges = List{DaeEdge}  #= A list of edges, each edge associated with two lists of DAE elements
         (these elements represent equations to be added if the edge
         is broken) =#
         
        export DaeEdge, DaeEdges

        DefiniteRoot = DAE.ComponentRef  #= root defined with Connection.root =#

        DefiniteRoots = List  #= roots defined with Connection.root =#

        UniqueRoots = List  #= roots defined with Connection.uniqueRoot =#

        PotentialRoot = Tuple  #= potential root defined with Connections.potentialRoot =#

        PotentialRoots = List  #= potential roots defined with Connections.potentialRoot =#

          #= Input structure for connection breaking algorithm. It is collected during instantiation phase. =#
         @Uniontype ConnectionGraphType begin
              @Record GRAPH begin

                       updateGraph::Bool
                       definiteRoots #= Roots defined with Connection.root =#::DefiniteRoots
                       potentialRoots #= Roots defined with Connection.potentialRoot =#::PotentialRoots
                       uniqueRoots #= Roots defined with Connection.uniqueRoot =#::UniqueRoots
                       branches #= Edges defined with Connection.branch =#::Edges
                       connections #= Edges defined with connect statement =#::DaeEdges
              end
         end

         const EMPTY = GRAPH(true, nil, nil, nil, nil, nil) #= Initial connection graph with no edges in it. =#::ConnectionGraphType

         const NOUPDATE_EMPTY = GRAPH(false, nil, nil, nil, nil, nil) #= Initial connection graph with updateGraph set to false. =#::ConnectionGraphType

         #= author: adrpo
         this function gets the connection graph and the existing DAE and:
         - returns a list of broken connects and one list of connected connects
         - evaluates Connections.isRoot in the input DAE
         - evaluates Connections.uniqueRootIndices in the input DAE
         - evaluates the rooted operator in the input DAE =#
        function handleOverconstrainedConnections(inGraph::ConnectionGraphType, modelNameQualified::String, inDAE::DAE.DAElist) ::Tuple{DAE.DAElist, DaeEdges, DaeEdges}
              local outBroken::DaeEdges
              local outConnected::DaeEdges
              local outDAE::DAE.DAElist

              (outDAE, outConnected, outBroken) = begin
                  local graph::ConnectionGraphType
                  local elts::List{DAE.Element}
                  local roots::List{DAE.ComponentRef}
                  local broken::DaeEdges
                  local connected::DaeEdges
                   #=  empty graph gives you the same dae
                   =#
                @matchcontinue (inGraph, modelNameQualified, inDAE) begin
                  (GRAPH(_,  nil(),  nil(),  nil(),  nil(),  nil()), _, _)  => begin
                    (inDAE, nil, nil)
                  end

                  (graph, _, DAE.DAE(elts))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("Summary: \\n\\t" + "Nr Roots:           " + intString(listLength(getDefiniteRoots(graph))) + "\\n\\t" + "Nr Potential Roots: " + intString(listLength(getPotentialRoots(graph))) + "\\n\\t" + "Nr Unique Roots:    " + intString(listLength(getUniqueRoots(graph))) + "\\n\\t" + "Nr Branches:        " + intString(listLength(getBranches(graph))) + "\\n\\t" + "Nr Connections:     " + intString(listLength(getConnections(graph))))
                      end
                      (roots, connected, broken) = findResultGraph(graph, modelNameQualified)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("Roots: " + stringDelimitList(ListUtil.map(roots, ComponentReference.printComponentRefStr), ", "))
                        Debug.traceln("Broken connections: " + stringDelimitList(ListUtil.map1(broken, printConnectionStr, "broken"), ", "))
                        Debug.traceln("Allowed connections: " + stringDelimitList(ListUtil.map1(connected, printConnectionStr, "allowed"), ", "))
                      end
                      elts = evalConnectionsOperators(roots, graph, elts)
                    (DAE.DAE(elts), connected, broken)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.handleOverconstrainedConnections failed for model: " + modelNameQualified)
                      fail()
                  end
                end
              end
               #=  handle the connection breaking
               =#
          (outDAE, outConnected, outBroken)
        end

         #= Adds a new definite root to ConnectionGraph =#
        function addDefiniteRoot(inGraph::ConnectionGraphType, inRoot::DAE.ComponentRef) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local root::DAE.ComponentRef
                  local definiteRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                @match (inGraph, inRoot) begin
                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), root)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.addDefiniteRoot(" + ComponentReference.printComponentRefStr(root) + ")")
                      end
                    GRAPH(updateGraph, _cons(root, definiteRoots), potentialRoots, uniqueRoots, branches, connections)
                  end
                end
              end
          outGraph
        end

         #= Adds a new potential root to ConnectionGraphType =#
        function addPotentialRoot(inGraph::ConnectionGraphType, inRoot::DAE.ComponentRef, inPriority::ModelicaReal) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local root::DAE.ComponentRef
                  local priority::ModelicaReal
                  local definiteRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                @match (inGraph, inRoot, inPriority) begin
                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), root, priority)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.addPotentialRoot(" + ComponentReference.printComponentRefStr(root) + ", " + realString(priority) + ")")
                      end
                    GRAPH(updateGraph, definiteRoots, _cons((root, priority), potentialRoots), uniqueRoots, branches, connections)
                  end
                end
              end
          outGraph
        end

         #= Adds a new definite root to ConnectionGraph =#
        function addUniqueRoots(inGraph::ConnectionGraphType, inRoots::DAE.Exp, inMessage::DAE.Exp) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local root::DAE.ComponentRef
                  local roots::DAE.Exp
                  local definiteRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                  local graph::ConnectionGraphType
                  local ty::DAE.Type
                  local scalar::Bool
                  local rest::List{DAE.Exp}
                   #=  just one component reference
                   =#
                @match (inGraph, inRoots, inMessage) begin
                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), DAE.CREF(root, _), _)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.addUniqueRoots(" + ComponentReference.printComponentRefStr(root) + ", " + ExpressionDump.printExpStr(inMessage) + ")")
                      end
                    GRAPH(updateGraph, definiteRoots, potentialRoots, _cons((root, inMessage), uniqueRoots), branches, connections)
                  end

                  (GRAPH(__), DAE.ARRAY(_, _,  nil()), _)  => begin
                    inGraph
                  end

                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), DAE.ARRAY(ty, scalar, DAE.CREF(root, _) <| rest), _)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.addUniqueRoots(" + ComponentReference.printComponentRefStr(root) + ", " + ExpressionDump.printExpStr(inMessage) + ")")
                      end
                      graph = GRAPH(updateGraph, definiteRoots, potentialRoots, _cons((root, inMessage), uniqueRoots), branches, connections)
                      graph = addUniqueRoots(graph, DAE.ARRAY(ty, scalar, rest), inMessage)
                    graph
                  end

                  (_, _, _)  => begin
                    inGraph
                  end
                end
              end
               #=  TODO! FIXME! print some meaningful error message here that the input is not an array of roots or a cref
               =#
          outGraph
        end

         #= Adds a new branch to ConnectionGraph =#
        function addBranch(inGraph::ConnectionGraphType, inRef1::DAE.ComponentRef, inRef2::DAE.ComponentRef) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local definiteRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                @match (inGraph, inRef1, inRef2) begin
                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), ref1, ref2)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.addBranch(" + ComponentReference.printComponentRefStr(ref1) + ", " + ComponentReference.printComponentRefStr(ref2) + ")")
                      end
                    GRAPH(updateGraph, definiteRoots, potentialRoots, uniqueRoots, _cons((ref1, ref2), branches), connections)
                  end
                end
              end
          outGraph
        end

         #= Adds a new connection to ConnectionGraph =#
        function addConnection(inGraph::ConnectionGraphType, inRef1::DAE.ComponentRef, inRef2::DAE.ComponentRef, inDae::List{<:DAE.Element}) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local dae::List{DAE.Element}
                  local definiteRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                @match (inGraph, inRef1, inRef2, inDae) begin
                  (GRAPH(updateGraph = updateGraph, definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), ref1, ref2, dae)  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.trace("- ConnectionGraph.addConnection(" + ComponentReference.printComponentRefStr(ref1) + ", " + ComponentReference.printComponentRefStr(ref2) + ")\\n")
                      end
                    GRAPH(updateGraph, definiteRoots, potentialRoots, uniqueRoots, branches, _cons((ref1, ref2, dae), connections))
                  end
                end
              end
          outGraph
        end

         #=  *************************************
         =#
         #=  ********* protected section *********
         =#
         #=  *************************************
         =#

        import BaseHashTable

        import ComponentReference

        import ConnectUtil

        import Debug

        import ExpressionDump

        import Flags

        import ListUtil

        import Util

        import System

        import IOStream

        import Settings

         #= Returns the canonical element of the component where input element belongs to.
         See explanation at the top of file. =#
        function canonical(inPartition::HashTableCG.HashTable, inRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outCanonical::DAE.ComponentRef

              outCanonical = begin
                   #= /*outPartition,*/ =#
                  local partition::HashTableCG.HashTable
                  local ref::DAE.ComponentRef
                  local parent::DAE.ComponentRef
                  local parentCanonical::DAE.ComponentRef
                @matchcontinue (inPartition, inRef) begin
                  (partition, ref)  => begin
                      parent = BaseHashTable.get(ref, partition)
                      parentCanonical = canonical(partition, parent)
                    parentCanonical
                  end

                  (_, ref)  => begin
                    ref
                  end
                end
              end
               #= fprintln(Flags.CGRAPH,
               =#
               #=   \"- ConnectionGraph.canonical_case1(\" + ComponentReference.printComponentRefStr(ref) + \") = \" +
               =#
               #=   ComponentReference.printComponentRefStr(parentCanonical));
               =#
               #= partition2 = BaseHashTable.add((ref, parentCanonical), partition);
               =#
               #= fprintln(Flags.CGRAPH,
               =#
               #=   \"- ConnectionGraph.canonical_case2(\" + ComponentReference.printComponentRefStr(ref) + \") = \" +
               =#
               #=   ComponentReference.printComponentRefStr(ref));
               =#
          outCanonical
        end

         #= Tells whether the elements belong to the same component.
         See explanation at the top of file. =#
        function areInSameComponent(inPartition::HashTableCG.HashTable, inRef1::DAE.ComponentRef, inRef2::DAE.ComponentRef) ::Bool
              local outResult::Bool

               #=  canonical(inPartition,inRef1) = canonical(inPartition,inRef2);
               =#
              outResult = begin
                  local partition::HashTableCG.HashTable
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local canon1::DAE.ComponentRef
                  local canon2::DAE.ComponentRef
                @matchcontinue (inPartition, inRef1, inRef2) begin
                  (partition, ref1, ref2)  => begin
                      canon1 = canonical(partition, ref1)
                      canon2 = canonical(partition, ref2)
                      @match true = ComponentReference.crefEqualNoStringCompare(canon1, canon2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outResult
        end

         #= Tries to connect two components whose elements are given. Depending
         on wheter the connection success or not (i.e are the components already
         connected), adds either inConnectionDae or inBreakDae to the list of
         DAE elements. =#
        function connectBranchComponents(inPartition::HashTableCG.HashTable, inRef1::DAE.ComponentRef, inRef2::DAE.ComponentRef) ::HashTableCG.HashTable
              local outPartition::HashTableCG.HashTable

              outPartition = begin
                  local partition::HashTableCG.HashTable
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local canon1::DAE.ComponentRef
                  local canon2::DAE.ComponentRef
                   #=  can connect them
                   =#
                @matchcontinue (inPartition, inRef1, inRef2) begin
                  (partition, ref1, ref2)  => begin
                      canon1 = canonical(partition, ref1)
                      canon2 = canonical(partition, ref2)
                      @match (partition, true) = connectCanonicalComponents(partition, canon1, canon2)
                    partition
                  end

                  (partition, _, _)  => begin
                    partition
                  end
                end
              end
               #=  cannot connect them
               =#
          outPartition
        end

         #= Tries to connect two components whose elements are given. Depending
         on wheter the connection success or not (i.e are the components already
         connected), adds either inConnectionDae or inBreakDae to the list of
         DAE elements. =#
        function connectComponents(inPartition::HashTableCG.HashTable, inDaeEdge::DaeEdge) ::Tuple{HashTableCG.HashTable, DaeEdges, DaeEdges}
              local outBrokenConnections::DaeEdges
              local outConnectedConnections::DaeEdges
              local outPartition::HashTableCG.HashTable

              (outPartition, outConnectedConnections, outBrokenConnections) = begin
                  local partition::HashTableCG.HashTable
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local canon1::DAE.ComponentRef
                  local canon2::DAE.ComponentRef
                   #=  leave the connect(ref1,ref2)
                   =#
                @matchcontinue (inPartition, inDaeEdge) begin
                  (partition, (ref1, _, _))  => begin
                      @shouldFail _ = canonical(partition, ref1)
                    (partition, list(inDaeEdge), nil)
                  end

                  (partition, (_, ref2, _))  => begin
                      @shouldFail _ = canonical(partition, ref2)
                    (partition, list(inDaeEdge), nil)
                  end

                  (partition, (ref1, ref2, _))  => begin
                      canon1 = canonical(partition, ref1)
                      canon2 = canonical(partition, ref2)
                      @match (partition, true) = connectCanonicalComponents(partition, canon1, canon2)
                    (partition, list(inDaeEdge), nil)
                  end

                  (partition, (ref1, ref2, _))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.trace("- ConnectionGraph.connectComponents: should remove equations generated from: connect(" + ComponentReference.printComponentRefStr(ref1) + ", " + ComponentReference.printComponentRefStr(ref2) + ") and add {0, ..., 0} = equalityConstraint(cr1, cr2) instead.\\n")
                      end
                    (partition, nil, list(inDaeEdge))
                  end
                end
              end
          (outPartition, outConnectedConnections, outBrokenConnections)
        end

         #= Tries to connect two components whose canonical elements are given.
         Helper function for connectionComponents. =#
        function connectCanonicalComponents(inPartition::HashTableCG.HashTable, inRef1::DAE.ComponentRef, inRef2::DAE.ComponentRef) ::Tuple{HashTableCG.HashTable, Bool}
              local outReallyConnected::Bool
              local outPartition::HashTableCG.HashTable

              (outPartition, outReallyConnected) = begin
                  local partition::HashTableCG.HashTable
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                   #=  they are the same
                   =#
                @matchcontinue (inPartition, inRef1, inRef2) begin
                  (partition, ref1, ref2)  => begin
                      @match true = ComponentReference.crefEqualNoStringCompare(ref1, ref2)
                    (partition, false)
                  end

                  (partition, ref1, ref2)  => begin
                      partition = BaseHashTable.add((ref1, ref2), partition)
                    (partition, true)
                  end
                end
              end
               #=  not the same, add it
               =#
          (outPartition, outReallyConnected)
        end

         #= Adds a root the the graph. This is implemented by connecting the root to inFirstRoot element. =#
        function addRootsToTable(inTable::HashTableCG.HashTable, inRoots::List{<:DAE.ComponentRef}, inFirstRoot::DAE.ComponentRef) ::HashTableCG.HashTable
              local outTable::HashTableCG.HashTable

              outTable = begin
                  local table::HashTableCG.HashTable
                  local root::DAE.ComponentRef
                  local firstRoot::DAE.ComponentRef
                  local tail::List{DAE.ComponentRef}
                @match (inTable, inRoots, inFirstRoot) begin
                  (table, root <| tail, firstRoot)  => begin
                      table = BaseHashTable.add((root, firstRoot), table)
                      table = addRootsToTable(table, tail, firstRoot)
                    table
                  end

                  (table,  nil(), _)  => begin
                    table
                  end
                end
              end
          outTable
        end

         #= Creates an initial graph with given definite roots. =#
        function resultGraphWithRoots(roots::List{<:DAE.ComponentRef}) ::HashTableCG.HashTable
              local outTable::HashTableCG.HashTable

              local table0::HashTableCG.HashTable
              local dummyRoot::DAE.ComponentRef

              dummyRoot = ComponentReference.makeCrefIdent("__DUMMY_ROOT", DAE.T_INTEGER_DEFAULT, nil)
              table0 = HashTableCG.emptyHashTable()
              outTable = addRootsToTable(table0, roots, dummyRoot)
          outTable
        end

         #= Adds all branches to the graph. =#
        function addBranchesToTable(inTable::HashTableCG.HashTable, inBranches::Edges) ::HashTableCG.HashTable
              local outTable::HashTableCG.HashTable

              outTable = begin
                  local table::HashTableCG.HashTable
                  local table1::HashTableCG.HashTable
                  local table2::HashTableCG.HashTable
                  local ref1::DAE.ComponentRef
                  local ref2::DAE.ComponentRef
                  local tail::Edges
                @match (inTable, inBranches) begin
                  (table, (ref1, ref2) <| tail)  => begin
                      table1 = connectBranchComponents(table, ref1, ref2)
                      table2 = addBranchesToTable(table1, tail)
                    table2
                  end

                  (table,  nil())  => begin
                    table
                  end
                end
              end
          outTable
        end

         #= An ordering function for potential roots. =#
        function ord(inEl1::PotentialRoot, inEl2::PotentialRoot) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local s1::String
                  local s2::String
                @matchcontinue (inEl1, inEl2) begin
                  ((c1, r1), (c2, r2))  => begin
                      @match true = realEq(r1, r2)
                      s1 = ComponentReference.printComponentRefStr(c1)
                      s2 = ComponentReference.printComponentRefStr(c2)
                      @match 1 = stringCompare(s1, s2)
                    true
                  end

                  ((_, r1), (_, r2))  => begin
                    r1 > r2
                  end
                end
              end
               #=  if equal order by cref
               =#
          outBoolean
        end

         #= Adds all potential roots to graph. =#
        function addPotentialRootsToTable(inTable::HashTableCG.HashTable, inPotentialRoots::PotentialRoots, inRoots::DefiniteRoots, inFirstRoot::DAE.ComponentRef) ::Tuple{HashTableCG.HashTable, DefiniteRoots}
              local outRoots::DefiniteRoots
              local outTable::HashTableCG.HashTable

              (outTable, outRoots) = begin
                  local table::HashTableCG.HashTable
                  local potentialRoot::DAE.ComponentRef
                  local firstRoot::DAE.ComponentRef
                  local canon1::DAE.ComponentRef
                  local canon2::DAE.ComponentRef
                  local roots::DefiniteRoots
                  local finalRoots::DefiniteRoots
                  local tail::PotentialRoots
                @matchcontinue (inTable, inPotentialRoots, inRoots, inFirstRoot) begin
                  (table,  nil(), roots, _)  => begin
                    (table, roots)
                  end

                  (table, (potentialRoot, _) <| tail, roots, firstRoot)  => begin
                      canon1 = canonical(table, potentialRoot)
                      canon2 = canonical(table, firstRoot)
                      @match (table, true) = connectCanonicalComponents(table, canon1, canon2)
                      (table, finalRoots) = addPotentialRootsToTable(table, tail, _cons(potentialRoot, roots), firstRoot)
                    (table, finalRoots)
                  end

                  (table, _ <| tail, roots, firstRoot)  => begin
                      (table, finalRoots) = addPotentialRootsToTable(table, tail, roots, firstRoot)
                    (table, finalRoots)
                  end
                end
              end
          (outTable, outRoots)
        end

         #= Adds all connections to graph. =#
        function addConnections(inTable::HashTableCG.HashTable, inConnections::DaeEdges) ::Tuple{HashTableCG.HashTable, DaeEdges, DaeEdges}
              local outBrokenConnections::DaeEdges
              local outConnectedConnections::DaeEdges
              local outTable::HashTableCG.HashTable

              (outTable, outConnectedConnections, outBrokenConnections) = begin
                  local table::HashTableCG.HashTable
                  local tail::DaeEdges
                  local broken1::DaeEdges
                  local broken2::DaeEdges
                  local broken::DaeEdges
                  local connected1::DaeEdges
                  local connected2::DaeEdges
                  local connected::DaeEdges
                  local e::DaeEdge
                   #=  empty case
                   =#
                @match (inTable, inConnections) begin
                  (table,  nil())  => begin
                    (table, nil, nil)
                  end

                  (table, e <| tail)  => begin
                      (table, connected1, broken1) = connectComponents(table, e)
                      (table, connected2, broken2) = addConnections(table, tail)
                      connected = listAppend(connected1, connected2)
                      broken = listAppend(broken1, broken2)
                    (table, connected, broken)
                  end
                end
              end
               #=  normal case
               =#
          (outTable, outConnectedConnections, outBrokenConnections)
        end

         #= Given ConnectionGraph structure, breaks all connections,
         determines roots and generates a list of dae elements. =#
        function findResultGraph(inGraph::ConnectionGraphType, modelNameQualified::String) ::Tuple{DefiniteRoots, DaeEdges, DaeEdges}
              local outBrokenConnections::DaeEdges
              local outConnectedConnections::DaeEdges
              local outRoots::DefiniteRoots

              (outRoots, outConnectedConnections, outBrokenConnections) = begin
                  local definiteRoots::DefiniteRoots
                  local finalRoots::DefiniteRoots
                  local potentialRoots::PotentialRoots
                  local orderedPotentialRoots::PotentialRoots
                  local uniqueRoots::UniqueRoots
                  local branches::Edges
                  local connections::DaeEdges
                  local broken::DaeEdges
                  local connected::DaeEdges
                  local table::HashTableCG.HashTable
                  local dummyRoot::DAE.ComponentRef
                  local brokenConnectsViaGraphViz::String
                  local userBrokenLst::List{String}
                  local userBrokenLstLst::List{List{String}}
                  local userBrokenTplLst::List{Tuple{String, String}}
                   #=  deal with empty connection graph
                   =#
                @matchcontinue (inGraph, modelNameQualified) begin
                  (GRAPH(definiteRoots =  nil(), potentialRoots =  nil(), uniqueRoots =  nil(), branches =  nil(), connections =  nil()), _)  => begin
                    (nil, nil, nil)
                  end

                  (GRAPH(definiteRoots = definiteRoots, potentialRoots = potentialRoots, uniqueRoots = uniqueRoots, branches = branches, connections = connections), _)  => begin
                      connections = listReverse(connections)
                      table = resultGraphWithRoots(definiteRoots)
                      table = addBranchesToTable(table, branches)
                      orderedPotentialRoots = ListUtil.sort(potentialRoots, ord)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("Ordered Potential Roots: " + stringDelimitList(ListUtil.map(orderedPotentialRoots, printPotentialRootTuple), ", "))
                      end
                      (table, connected, broken) = addConnections(table, connections)
                      dummyRoot = ComponentReference.makeCrefIdent("__DUMMY_ROOT", DAE.T_INTEGER_DEFAULT, nil)
                      (table, finalRoots) = addPotentialRootsToTable(table, orderedPotentialRoots, definiteRoots, dummyRoot)
                      brokenConnectsViaGraphViz = generateGraphViz(modelNameQualified, definiteRoots, potentialRoots, uniqueRoots, branches, connections, finalRoots, broken)
                      if stringEq(brokenConnectsViaGraphViz, "")
                      else
                        userBrokenLst = Util.stringSplitAtChar(brokenConnectsViaGraphViz, "#")
                        userBrokenLstLst = ListUtil.map1(userBrokenLst, Util.stringSplitAtChar, "|")
                        userBrokenTplLst = makeTuple(userBrokenLstLst)
                        Debug.traceln("User selected the following connect edges for breaking:\\n\\t" + stringDelimitList(ListUtil.map(userBrokenTplLst, printTupleStr), "\\n\\t"))
                        printDaeEdges(connections)
                        connections = orderConnectsGuidedByUser(connections, userBrokenTplLst)
                        connections = listReverse(connections)
                        print("\\nAfer ordering:\\n")
                        (finalRoots, connected, broken) = findResultGraph(GRAPH(false, definiteRoots, potentialRoots, uniqueRoots, branches, connections), modelNameQualified)
                      end
                    (finalRoots, connected, broken)
                  end
                end
              end
          (outRoots, outConnectedConnections, outBrokenConnections)
        end

        function orderConnectsGuidedByUser(inConnections::DaeEdges, inUserSelectedBreaking::List{<:Tuple{<:String, String}}) ::DaeEdges
              local outOrderedConnections::DaeEdges

              local front::DaeEdges = nil
              local back::DaeEdges = nil
              local c1::DAE.ComponentRef
              local c2::DAE.ComponentRef
              local sc1::String
              local sc2::String

              for e in inConnections
                (c1, c2, _) = e
                sc1 = ComponentReference.printComponentRefStr(c1)
                sc2 = ComponentReference.printComponentRefStr(c2)
                if listMember((sc1, sc2), inUserSelectedBreaking) || listMember((sc2, sc1), inUserSelectedBreaking)
                  back = _cons(e, back)
                else
                  front = _cons(e, front)
                end
              end
               #=  put them at the end to be tried last (more chance to be broken)
               =#
               #=  put them at the front to be tried first (less chance to be broken)
               =#
              outOrderedConnections = ListUtil.append_reverse(front, back)
          outOrderedConnections
        end

        function printTupleStr(inTpl::Tuple{<:String, String}) ::String
              local out::String

              out = begin
                  local c1::String
                  local c2::String
                @match inTpl begin
                  (c1, c2)  => begin
                    c1 + " -- " + c2
                  end
                end
              end
          out
        end

        function makeTuple(inLstLst::List{<:List{<:String}}) ::List{Tuple{String, String}}
              local outLst::List{Tuple{String, String}}

              outLst = begin
                  local c1::String
                  local c2::String
                  local rest::List{List{String}}
                  local lst::List{Tuple{String, String}}
                  local bad::List{String}
                   #=  empty case
                   =#
                @matchcontinue inLstLst begin
                   nil()  => begin
                    nil
                  end

                  c1 <| c2 <|  nil() <| rest  => begin
                      lst = makeTuple(rest)
                    _cons((c1, c2), lst)
                  end

                  "" <|  nil() <| rest  => begin
                      lst = makeTuple(rest)
                    lst
                  end

                   nil() <| rest  => begin
                      lst = makeTuple(rest)
                    lst
                  end

                  bad <| rest  => begin
                      Debug.traceln("The following output from GraphViz OpenModelica assistant cannot be parsed:" + stringDelimitList(bad, ", ") + "\\nExpected format from GrapViz: cref1|cref2#cref3|cref4#. Ignoring malformed input.")
                      lst = makeTuple(rest)
                    lst
                  end
                end
              end
               #=  somthing case
               =#
               #=  ignore empty strings
               =#
               #=  ignore empty list
               =#
               #=  somthing case
               =#
          outLst
        end

        function printPotentialRootTuple(potentialRoot::PotentialRoot) ::String
              local outStr::String

              outStr = begin
                  local cr::DAE.ComponentRef
                  local priority::ModelicaReal
                  local str::String
                @match potentialRoot begin
                  (cr, priority)  => begin
                      str = ComponentReference.printComponentRefStr(cr) + "(" + realString(priority) + ")"
                    str
                  end
                end
              end
          outStr
        end

        function setRootDistance(finalRoots::List{<:DAE.ComponentRef}, table::HashTable3.HashTable, distance::ModelicaInteger, nextLevel::List{<:DAE.ComponentRef}, irooted::HashTable.HashTableType) ::HashTable.HashTableType
              local orooted::HashTable.HashTableType

              orooted = begin
                  local rooted::HashTable.HashTableType
                  local rest::List{DAE.ComponentRef}
                  local next::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                @matchcontinue (finalRoots, table, distance, nextLevel, irooted) begin
                  ( nil(), _, _,  nil(), _)  => begin
                    irooted
                  end

                  ( nil(), _, _, _, _)  => begin
                    setRootDistance(nextLevel, table, distance + 1, nil, irooted)
                  end

                  (cr <| rest, _, _, _, _)  => begin
                      @match false = BaseHashTable.hasKey(cr, irooted)
                      rooted = BaseHashTable.add((cr, distance), irooted)
                      next = BaseHashTable.get(cr, table)
                      next = listAppend(nextLevel, next)
                    setRootDistance(rest, table, distance, next, rooted)
                  end

                  (cr <| rest, _, _, _, _)  => begin
                      @match false = BaseHashTable.hasKey(cr, irooted)
                      rooted = BaseHashTable.add((cr, distance), irooted)
                    setRootDistance(rest, table, distance, nextLevel, rooted)
                  end

                  (_ <| rest, _, _, _, _)  => begin
                    setRootDistance(rest, table, distance, nextLevel, irooted)
                  end
                end
              end
               #= print(\"- ConnectionGraph.setRootDistance: Set Distance \" +
               =#
               #=    ComponentReference.printComponentRefStr(cr) + \" , \" + intString(distance) + \"\\n\");
               =#
               #= print(\"- ConnectionGraph.setRootDistance: add \" +
               =#
               #=    stringDelimitList(List.map(next,ComponentReference.printComponentRefStr),\"\\n\") + \" to the queue\\n\");
               =#
               #= print(\"- ConnectionGraph.setRootDistance: Set Distance \" +
               =#
               #=    ComponentReference.printComponentRefStr(cr) + \" , \" + intString(distance) + \"\\n\");
               =#
               #= /*    case(cr::rest,_,_,_,_)
                    equation
                      i = BaseHashTable.get(cr, irooted);
                      print(\"- ConnectionGraph.setRootDistance: found \" +
                         ComponentReference.printComponentRefStr(cr) + \" twice, value is \" + intString(i) + \"\\n\");
                    then
                      setRootDistance(rest,table,distance,nextLevel,irooted);
              */ =#
               #= equation
               =#
               #=   print(\"- ConnectionGraph.setRootDistance: cannot found \" + ComponentReference.printComponentRefStr(cr) + \"\\n\");
               =#
          orooted
        end

        function addBranches(edge::Edge, itable::HashTable3.HashTable) ::HashTable3.HashTable
              local otable::HashTable3.HashTable

              local cref1::DAE.ComponentRef
              local cref2::DAE.ComponentRef

              (cref1, cref2) = edge
              otable = addConnectionRooted(cref1, cref2, itable)
              otable = addConnectionRooted(cref2, cref1, otable)
          otable
        end

        function addConnectionsRooted(connection::DaeEdge, itable::HashTable3.HashTable) ::HashTable3.HashTable
              local otable::HashTable3.HashTable

              local cref1::DAE.ComponentRef
              local cref2::DAE.ComponentRef

              (cref1, cref2, _) = connection
              otable = addConnectionRooted(cref1, cref2, itable)
              otable = addConnectionRooted(cref2, cref1, otable)
          otable
        end

        function addConnectionRooted(cref1::DAE.ComponentRef, cref2::DAE.ComponentRef, itable::HashTable3.HashTable) ::HashTable3.HashTable
              local otable::HashTable3.HashTable

              otable = begin
                  local table::HashTable3.HashTable
                  local crefs::List{DAE.ComponentRef}
                @match (cref1, cref2, itable) begin
                  (_, _, _)  => begin
                      crefs = begin
                        @matchcontinue () begin
                          ()  => begin
                            BaseHashTable.get(cref1, itable)
                          end

                          _  => begin
                              nil
                          end
                        end
                      end
                      table = BaseHashTable.add((cref1, _cons(cref2, crefs)), itable)
                    table
                  end
                end
              end
          otable
        end

         #= evaluation of Connections.rooted, Connections.isRoot, Connections.uniqueRootIndices
         - replaces all [Connections.]rooted calls by true or false depending on wheter branche frame_a or frame_b is closer to root
         - return true or false for Connections.isRoot operator if is a root or not
         - return an array of indices for Connections.uniqueRootIndices, see Modelica_StateGraph2
           See Modelica_StateGraph2:
            https:github.com/modelica/Modelica_StateGraph2 and
            https:trac.modelica.org/Modelica/ticket/984 and
            http:www.ep.liu.se/ecp/043/041/ecp09430108.pdf
           for a specification of this operator =#
        function evalConnectionsOperators(inRoots::List{<:DAE.ComponentRef}, graph::ConnectionGraphType, inDae::List{<:DAE.Element}) ::List{DAE.Element}
              local outDae::List{DAE.Element}

              outDae = begin
                  local rooted::HashTable.HashTableType
                  local table::HashTable3.HashTable
                  local branches::Edges
                  local connections::DaeEdges
                @matchcontinue (inRoots, graph, inDae) begin
                  (_, _,  nil())  => begin
                    nil
                  end

                  _  => begin
                        table = HashTable3.emptyHashTable()
                        branches = getBranches(graph)
                        table = ListUtil.fold(branches, addBranches, table)
                        connections = getConnections(graph)
                        table = ListUtil.fold(connections, addConnectionsRooted, table)
                        rooted = setRootDistance(inRoots, table, 0, nil, HashTable.emptyHashTable())
                        (outDae, _) = DAEUtil.traverseDAEElementList(inDae, evalConnectionsOperatorsHelper, (rooted, inRoots, graph))
                      outDae
                  end
                end
              end
               #=  built table
               =#
               #=  add branches to table
               =#
               #=  add connections to table
               =#
               #=  get distanste to root
               =#
               #=   print(\"Roots: \" + stringDelimitList(List.map(inRoots,ComponentReference.printComponentRefStr),\"\\n\") + \"\\n\");
               =#
               #=   BaseHashTable.dumpHashTable(table);
               =#
               #=   BaseHashTable.dumpHashTable(rooted);
               =#
          outDae
        end

         #= Helper function for evaluation of Connections.rooted, Connections.isRoot, Connections.uniqueRootIndices =#
        function evalConnectionsOperatorsHelper(inExp::DAE.Exp, inRoots::Tuple{<:HashTable.HashTableType, List{<:DAE.ComponentRef}, ConnectionGraphType}) ::Tuple{DAE.Exp, Tuple{HashTable.HashTableType, List{DAE.ComponentRef}, ConnectionGraphType}}
              local outRoots::Tuple{HashTable.HashTableType, List{DAE.ComponentRef}, ConnectionGraphType}
              local outExp::DAE.Exp

              (outExp, outRoots) = begin
                  local graph::ConnectionGraphType
                  local exp::DAE.Exp
                  local uroots::DAE.Exp
                  local nodes::DAE.Exp
                  local message::DAE.Exp
                  local rooted::HashTable.HashTableType
                  local cref::DAE.ComponentRef
                  local cref1::DAE.ComponentRef
                  local result::Bool
                  local branches::Edges
                  local roots::List{DAE.ComponentRef}
                  local lst::List{DAE.Exp}
                   #=  handle rooted - with zero size array
                   =#
                @matchcontinue (inExp, inRoots) begin
                  (DAE.CALL(path = Absyn.IDENT("rooted"), expLst = DAE.ARRAY(array =  nil()) <|  nil()), (rooted, roots, graph))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = false")
                      end
                    (DAE.BCONST(false), (rooted, roots, graph))
                  end

                  (DAE.CALL(path = Absyn.IDENT("rooted"), expLst = DAE.CREF(componentRef = cref) <|  nil()), (rooted, roots, graph))  => begin
                      branches = getBranches(graph)
                      cref1 = getEdge(cref, branches)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: Found Branche Partner " + ComponentReference.printComponentRefStr(cref) + ", " + ComponentReference.printComponentRefStr(cref1))
                      end
                      result = getRooted(cref, cref1, rooted)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = " + boolString(result))
                      end
                    (DAE.BCONST(result), (rooted, roots, graph))
                  end

                  (exp, (rooted, roots &&  nil(), graph))  => begin
                    (exp, (rooted, roots, graph))
                  end

                  (DAE.CALL(path = Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), expLst = DAE.ARRAY(array =  nil()) <|  nil()), (rooted, roots, graph))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = false")
                      end
                    (DAE.BCONST(false), (rooted, roots, graph))
                  end

                  (DAE.LUNARY(DAE.NOT(_), DAE.CALL(path = Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), expLst = DAE.ARRAY(array =  nil()) <|  nil())), (rooted, roots, graph))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = false")
                      end
                    (DAE.BCONST(false), (rooted, roots, graph))
                  end

                  (DAE.CALL(path = Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), expLst = DAE.CREF(componentRef = cref) <|  nil()), (rooted, roots, graph))  => begin
                      result = ListUtil.isMemberOnTrue(cref, roots, ComponentReference.crefEqualNoStringCompare)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = " + boolString(result))
                      end
                    (DAE.BCONST(result), (rooted, roots, graph))
                  end

                  (DAE.LUNARY(DAE.NOT(_), DAE.CALL(path = Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), expLst = DAE.CREF(componentRef = cref) <|  nil())), (rooted, roots, graph))  => begin
                      result = ListUtil.isMemberOnTrue(cref, roots, ComponentReference.crefEqualNoStringCompare)
                      result = boolNot(result)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: " + ExpressionDump.printExpStr(inExp) + " = " + boolString(result))
                      end
                    (DAE.BCONST(result), (rooted, roots, graph))
                  end

                  (DAE.CALL(path = Absyn.QUALIFIED("Connections", Absyn.IDENT("uniqueRootIndices")), expLst = uroots && DAE.ARRAY(array = lst) <| nodes <| message <|  nil()), (rooted, roots, graph))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.evalConnectionsOperatorsHelper: Connections.uniqueRootsIndicies(" + ExpressionDump.printExpStr(uroots) + "," + ExpressionDump.printExpStr(nodes) + "," + ExpressionDump.printExpStr(message) + ")")
                      end
                      lst = ListUtil.fill(DAE.ICONST(1), listLength(lst))
                    (DAE.ARRAY(DAE.T_INTEGER_DEFAULT, false, lst), (rooted, roots, graph))
                  end

                  _  => begin
                      (inExp, inRoots)
                  end
                end
              end
               #=  TODO! FIXME! actually implement this correctly
               =#
               #=  no replacement needed
               =#
               #=  fprintln(Flags.CGRAPH, ExpressionDump.printExpStr(exp) + \" not found in roots!\");
               =#
          (outExp, outRoots)
        end

        function getRooted(cref1::DAE.ComponentRef, cref2::DAE.ComponentRef, rooted::HashTable.HashTableType) ::Bool
              local result::Bool

              result = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                @matchcontinue (cref1, cref2, rooted) begin
                  (_, _, _)  => begin
                      i1 = BaseHashTable.get(cref1, rooted)
                      i2 = BaseHashTable.get(cref2, rooted)
                    intLt(i1, i2)
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  in faile case return true
               =#
          result
        end

         #= return the Edge partner of a edge, fails if not found =#
        function getEdge(cr::DAE.ComponentRef, edges::Edges) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              ocr = begin
                  local rest::Edges
                  local cref1::DAE.ComponentRef
                  local cref2::DAE.ComponentRef
                @matchcontinue (cr, edges) begin
                  (_, (cref1, cref2) <| _)  => begin
                      cref1 = getEdge1(cr, cref1, cref2)
                    cref1
                  end

                  (_, _ <| rest)  => begin
                    getEdge(cr, rest)
                  end
                end
              end
          ocr
        end

         #= return the Edge partner of a edge, fails if not found =#
        function getEdge1(cr::DAE.ComponentRef, cref1::DAE.ComponentRef, cref2::DAE.ComponentRef) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              ocr = begin
                @matchcontinue (cr, cref1, cref2) begin
                  (_, _, _)  => begin
                      @match true = ComponentReference.crefEqualNoStringCompare(cr, cref1)
                    cref2
                  end

                  _  => begin
                        @match true = ComponentReference.crefEqualNoStringCompare(cr, cref2)
                      cref1
                  end
                end
              end
          ocr
        end

         #= prints the connection str =#
        function printConnectionStr(connectTuple::DaeEdge, ty::String) ::String
              local outStr::String

              outStr = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local str::String
                @match (connectTuple, ty) begin
                  ((c1, c2, _), _)  => begin
                      str = ty + "(" + ComponentReference.printComponentRefStr(c1) + ", " + ComponentReference.printComponentRefStr(c2) + ")"
                    str
                  end
                end
              end
          outStr
        end

         #= Prints a list of edges to stdout. =#
        function printEdges(inEdges::Edges)
              _ = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local tail::Edges
                @match inEdges begin
                   nil()  => begin
                    ()
                  end

                  (c1, c2) <| tail  => begin
                      print("    ")
                      print(ComponentReference.printComponentRefStr(c1))
                      print(" -- ")
                      print(ComponentReference.printComponentRefStr(c2))
                      print("\\n")
                      printEdges(tail)
                    ()
                  end
                end
              end
        end

         #= Prints a list of dae edges to stdout. =#
        function printDaeEdges(inEdges::DaeEdges)
              _ = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local tail::DaeEdges
                @match inEdges begin
                   nil()  => begin
                    ()
                  end

                  (c1, c2, _) <| tail  => begin
                      print("    ")
                      print(ComponentReference.printComponentRefStr(c1))
                      print(" -- ")
                      print(ComponentReference.printComponentRefStr(c2))
                      print("\\n")
                      printDaeEdges(tail)
                    ()
                  end
                end
              end
        end

         #= Prints the content of ConnectionGraph structure. =#
        function printConnectionGraph(inGraph::ConnectionGraphType)
              _ = begin
                  local connections::DaeEdges
                  local branches::Edges
                @match inGraph begin
                  GRAPH(connections = connections, branches = branches)  => begin
                      print("Connections:\\n")
                      printDaeEdges(connections)
                      print("Branches:\\n")
                      printEdges(branches)
                    ()
                  end
                end
              end
        end

         #= Accessor for ConnectionGraph.definiteRoots. =#
        function getDefiniteRoots(inGraph::ConnectionGraphType) ::DefiniteRoots
              local outResult::DefiniteRoots

              outResult = begin
                  local result::DefiniteRoots
                @match inGraph begin
                  GRAPH(definiteRoots = result)  => begin
                    result
                  end
                end
              end
          outResult
        end

         #= Accessor for ConnectionGraph.uniqueRoots. =#
        function getUniqueRoots(inGraph::ConnectionGraphType) ::UniqueRoots
              local outResult::UniqueRoots

              outResult = begin
                  local result::UniqueRoots
                @match inGraph begin
                  GRAPH(uniqueRoots = result)  => begin
                    result
                  end
                end
              end
          outResult
        end

         #= Accessor for ConnectionGraph.potentialRoots. =#
        function getPotentialRoots(inGraph::ConnectionGraphType) ::PotentialRoots
              local outResult::PotentialRoots

              outResult = begin
                  local result::PotentialRoots
                @match inGraph begin
                  GRAPH(potentialRoots = result)  => begin
                    result
                  end
                end
              end
          outResult
        end

         #= Accessor for ConnectionGraph.branches. =#
        function getBranches(inGraph::ConnectionGraphType) ::Edges
              local outResult::Edges

              outResult = begin
                  local result::Edges
                @match inGraph begin
                  GRAPH(branches = result)  => begin
                    result
                  end
                end
              end
          outResult
        end

         #= Accessor for ConnectionGraph.connections. =#
        function getConnections(inGraph::ConnectionGraphType) ::DaeEdges
              local outResult::DaeEdges

              outResult = begin
                  local result::DaeEdges
                @match inGraph begin
                  GRAPH(connections = result)  => begin
                    result
                  end
                end
              end
          outResult
        end

         #= merge two ConnectionGraphs =#
        function merge(inGraph1::ConnectionGraphType, inGraph2::ConnectionGraphType) ::ConnectionGraphType
              local outGraph::ConnectionGraphType

              outGraph = begin
                  local updateGraph::Bool
                  local updateGraph1::Bool
                  local updateGraph2::Bool
                  local definiteRoots::DefiniteRoots
                  local definiteRoots1::DefiniteRoots
                  local definiteRoots2::DefiniteRoots
                  local uniqueRoots::UniqueRoots
                  local uniqueRoots1::UniqueRoots
                  local uniqueRoots2::UniqueRoots
                  local potentialRoots::PotentialRoots
                  local potentialRoots1::PotentialRoots
                  local potentialRoots2::PotentialRoots
                  local branches::Edges
                  local branches1::Edges
                  local branches2::Edges
                  local connections::DaeEdges
                  local connections1::DaeEdges
                  local connections2::DaeEdges
                   #=  left is empty, return right
                   =#
                @matchcontinue (inGraph1, inGraph2) begin
                  (_, GRAPH(definiteRoots =  nil(), potentialRoots =  nil(), uniqueRoots =  nil(), branches =  nil(), connections =  nil()))  => begin
                    inGraph1
                  end

                  (GRAPH(definiteRoots =  nil(), potentialRoots =  nil(), uniqueRoots =  nil(), branches =  nil(), connections =  nil()), _)  => begin
                    inGraph2
                  end

                  (_, _)  => begin
                      equality(inGraph1, inGraph2)
                    inGraph1
                  end

                  (GRAPH(updateGraph = updateGraph1, definiteRoots = definiteRoots1, potentialRoots = potentialRoots1, uniqueRoots = uniqueRoots1, branches = branches1, connections = connections1), GRAPH(updateGraph = updateGraph2, definiteRoots = definiteRoots2, potentialRoots = potentialRoots2, uniqueRoots = uniqueRoots2, branches = branches2, connections = connections2))  => begin
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.trace("- ConnectionGraph.merge()\\n")
                      end
                      updateGraph = boolOr(updateGraph1, updateGraph2)
                      definiteRoots = ListUtil.union(definiteRoots1, definiteRoots2)
                      potentialRoots = ListUtil.union(potentialRoots1, potentialRoots2)
                      uniqueRoots = ListUtil.union(uniqueRoots1, uniqueRoots2)
                      branches = ListUtil.union(branches1, branches2)
                      connections = ListUtil.union(connections1, connections2)
                    GRAPH(updateGraph, definiteRoots, potentialRoots, uniqueRoots, branches, connections)
                  end
                end
              end
          outGraph
        end

         #= /***********************************************************************************************************************/ =#
         #= /******************************************* GraphViz generation *******************************************************/ =#
         #= /***********************************************************************************************************************/ =#

        function graphVizEdge(inEdge::Edge) ::String
              local out::String

              out = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local strEdge::String
                @match inEdge begin
                  (c1, c2)  => begin
                      strEdge = "\\" + ComponentReference.printComponentRefStr(c1) + "\\ -- \\" + ComponentReference.printComponentRefStr(c2) + "\\" + " [color = blue, dir = \\none\\, fontcolor=blue, label = \\branch\\];\\n\\t"
                    strEdge
                  end
                end
              end
          out
        end

        function graphVizDaeEdge(inDaeEdge::DaeEdge, inBrokenDaeEdges::DaeEdges) ::String
              local out::String

              out = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local sc1::String
                  local sc2::String
                  local strDaeEdge::String
                  local label::String
                  local labelFontSize::String
                  local decorate::String
                  local color::String
                  local style::String
                  local fontColor::String
                  local isBroken::Bool
                @match (inDaeEdge, inBrokenDaeEdges) begin
                  ((c1, c2, _), _)  => begin
                      isBroken = listMember(inDaeEdge, inBrokenDaeEdges)
                      label = if isBroken
                            "[[broken connect]]"
                          else
                            "connect"
                          end
                      color = if isBroken
                            "red"
                          else
                            "green"
                          end
                      style = if isBroken
                            "\\bold, dashed\\"
                          else
                            "solid"
                          end
                      decorate = boolString(isBroken)
                      fontColor = if isBroken
                            "red"
                          else
                            "green"
                          end
                      labelFontSize = if isBroken
                            "labelfontsize = 20.0, "
                          else
                            ""
                          end
                      sc1 = ComponentReference.printComponentRefStr(c1)
                      sc2 = ComponentReference.printComponentRefStr(c2)
                      strDaeEdge = stringAppendList(list("\\", sc1, "\\ -- \\", sc2, "\\ [", "dir = \\none\\, ", "style = ", style, ", ", "decorate = ", decorate, ", ", "color = ", color, ", ", labelFontSize, "fontcolor = ", fontColor, ", ", "label = \\", label, "\\", "];\\n\\t"))
                    strDaeEdge
                  end
                end
              end
          out
        end

        function graphVizDefiniteRoot(inDefiniteRoot::DefiniteRoot, inFinalRoots::DefiniteRoots) ::String
              local out::String

              out = begin
                  local c::DAE.ComponentRef
                  local strDefiniteRoot::String
                  local isSelectedRoot::Bool
                @match (inDefiniteRoot, inFinalRoots) begin
                  (c, _)  => begin
                      isSelectedRoot = listMember(c, inFinalRoots)
                      strDefiniteRoot = "\\" + ComponentReference.printComponentRefStr(c) + "\\" + " [fillcolor = red, rank = \\source\\, label = " + "\\" + ComponentReference.printComponentRefStr(c) + "\\, " + (if isSelectedRoot
                            "shape=polygon, sides=8, distortion=\\0.265084\\, orientation=26, skew=\\0.403659\\"
                          else
                            "shape=box"
                          end) + "];\\n\\t"
                    strDefiniteRoot
                  end
                end
              end
          out
        end

        function graphVizPotentialRoot(inPotentialRoot::PotentialRoot, inFinalRoots::DefiniteRoots) ::String
              local out::String

              out = begin
                  local c::DAE.ComponentRef
                  local priority::ModelicaReal
                  local strPotentialRoot::String
                  local isSelectedRoot::Bool
                @match (inPotentialRoot, inFinalRoots) begin
                  ((c, priority), _)  => begin
                      isSelectedRoot = listMember(c, inFinalRoots)
                      strPotentialRoot = "\\" + ComponentReference.printComponentRefStr(c) + "\\" + " [fillcolor = orangered, rank = \\min\\ label = " + "\\" + ComponentReference.printComponentRefStr(c) + "\\\\n" + realString(priority) + "\\, " + (if isSelectedRoot
                            "shape=ploygon, sides=7, distortion=\\0.265084\\, orientation=26, skew=\\0.403659\\"
                          else
                            "shape=box"
                          end) + "];\\n\\t"
                    strPotentialRoot
                  end
                end
              end
          out
        end

         #= @author: adrpo
          Generate a graphviz file out of the connection graph =#
        function generateGraphViz(modelNameQualified::String, definiteRoots::DefiniteRoots, potentialRoots::PotentialRoots, uniqueRoots::UniqueRoots, branches::Edges, connections::DaeEdges, finalRoots::DefiniteRoots, broken::DaeEdges) ::String
              local brokenConnectsViaGraphViz::String

              brokenConnectsViaGraphViz = begin
                  local fileName::String
                  local i::String
                  local nrDR::String
                  local nrPR::String
                  local nrUR::String
                  local nrBR::String
                  local nrCO::String
                  local nrFR::String
                  local nrBC::String
                  local timeStr::String
                  local infoNodeStr::String
                  local brokenConnects::String
                  local tStart::ModelicaReal
                  local tEnd::ModelicaReal
                  local t::ModelicaReal
                  local graphVizStream::IOStream.IOStream
                  local infoNode::List{String}
                   #=  don't do anything if we don't have -d=cgraphGraphVizFile or -d=cgraphGraphVizShow
                   =#
                @matchcontinue (modelNameQualified, definiteRoots, potentialRoots, uniqueRoots, branches, connections, finalRoots, broken) begin
                  (_, _, _, _, _, _, _, _)  => begin
                      @match false = boolOr(Flags.isSet(Flags.CGRAPH_GRAPHVIZ_FILE), Flags.isSet(Flags.CGRAPH_GRAPHVIZ_SHOW))
                    ""
                  end

                  (_, _, _, _, _, _, _, _)  => begin
                      tStart = clock()
                      i = "\\t"
                      fileName = stringAppend(modelNameQualified, ".gv")
                      graphVizStream = IOStream.create(fileName, IOStream.LIST())
                      nrDR = intString(listLength(definiteRoots))
                      nrPR = intString(listLength(potentialRoots))
                      nrUR = intString(listLength(uniqueRoots))
                      nrBR = intString(listLength(branches))
                      nrCO = intString(listLength(connections))
                      nrFR = intString(listLength(finalRoots))
                      nrBC = intString(listLength(broken))
                      infoNode = list("// Generated by OpenModelica. \\n", "// Overconstrained connection graph for model: \\n//    ", modelNameQualified, "\\n", "// \\n", "// Summary: \\n", "//   Roots:              ", nrDR, "\\n", "//   Potential Roots:    ", nrPR, "\\n", "//   Unique Roots:       ", nrUR, "\\n", "//   Branches:           ", nrBR, "\\n", "//   Connections:        ", nrCO, "\\n", "//   Final Roots:        ", nrFR, "\\n", "//   Broken Connections: ", nrBC, "\\n")
                      infoNodeStr = stringAppendList(infoNode)
                      infoNodeStr = System.stringReplace(infoNodeStr, "\\n", "\\\\l")
                      infoNodeStr = System.stringReplace(infoNodeStr, "\\t", " ")
                      infoNodeStr = System.stringReplace(infoNodeStr, "/", "")
                      graphVizStream = IOStream.appendList(graphVizStream, infoNode)
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list("graph \\", modelNameQualified, "\\\\n{\\n\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list(i, "overlap=false;\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list(i, "layout=dot;\\n\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list(i, "node [", "fillcolor = \\lightsteelblue1\\, ", "shape = box, ", "style = \\bold, filled\\, ", "rank = \\max\\", "]\\n\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list(i, "edge [", "color = \\black\\, ", "style = bold", "]\\n\\n"))
                      graphVizStream = IOStream.appendList(graphVizStream, list(i, "graph [fontsize=20, fontname = \\Courier Bold\\ label= \\\\\\n\\\\n", infoNodeStr, "\\, size=\\6,6\\];\\n", i))
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n", i, "// Definite Roots (Connections.root)", "\\n", i))
                      graphVizStream = IOStream.appendList(graphVizStream, ListUtil.map1(definiteRoots, graphVizDefiniteRoot, finalRoots))
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n", i, "// Potential Roots (Connections.potentialRoot)", "\\n", i))
                      graphVizStream = IOStream.appendList(graphVizStream, ListUtil.map1(potentialRoots, graphVizPotentialRoot, finalRoots))
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n", i, "// Branches (Connections.branch)", "\\n", i))
                      graphVizStream = IOStream.appendList(graphVizStream, ListUtil.map(branches, graphVizEdge))
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n", i, "// Connections (connect)", "\\n", i))
                      graphVizStream = IOStream.appendList(graphVizStream, ListUtil.map1(connections, graphVizDaeEdge, broken))
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n}\\n"))
                      tEnd = clock()
                      t = tEnd - tStart
                      timeStr = realString(t)
                      graphVizStream = IOStream.appendList(graphVizStream, list("\\n\\n\\n// graph generation took: ", timeStr, " seconds\\n"))
                      System.writeFile(fileName, IOStream.string(graphVizStream))
                      Debug.traceln("GraphViz with connection graph for model: " + modelNameQualified + " was writen to file: " + fileName)
                      brokenConnects = showGraphViz(fileName, modelNameQualified)
                    brokenConnects
                  end
                end
              end
               #=  create a stream
               =#
               #=  replace \\n with \\\\l (left align), replace \\t with \" \"
               =#
               #=  replace / with \"\"
               =#
               #=  output header
               =#
               #=  output command to be used
               =#
               #=  output graphviz header
               =#
               #=  output global settings
               =#
               #=  output settings for nodes
               =#
               #=  output settings for edges
               =#
               #=  output summary node
               =#
               #=  output definite roots
               =#
               #=  output potential roots
               =#
               #=  output branches
               =#
               #=  output connections
               =#
               #=  output graphviz footer
               =#
          brokenConnectsViaGraphViz
        end

        function showGraphViz(fileNameGraphViz::String, modelNameQualified::String) ::String
              local brokenConnectsViaGraphViz::String

              brokenConnectsViaGraphViz = begin
                  local leftyCMD::String
                  local fileNameTraceRemovedConnections::String
                  local omhome::String
                  local brokenConnects::String
                  local leftyExitStatus::ModelicaInteger
                   #=  do not start graphviz if we don't have -d=cgraphGraphVizShow
                   =#
                @matchcontinue (fileNameGraphViz, modelNameQualified) begin
                  (_, _)  => begin
                      @match false = Flags.isSet(Flags.CGRAPH_GRAPHVIZ_SHOW)
                    ""
                  end

                  _  => begin
                        fileNameTraceRemovedConnections = modelNameQualified + "_removed_connections.txt"
                        Debug.traceln("Tyring to start GraphViz *lefty* to visualize the graph. You need to have lefty in your PATH variable")
                        Debug.traceln("Make sure you quit GraphViz *lefty* via Right Click->quit to be sure the process will be exited.")
                        Debug.traceln("If you quit the GraphViz *lefty* window via X, please kill the process in task manager to continue.")
                        omhome = Settings.getInstallationDirectoryPath()
                        omhome = System.stringReplace(omhome, "\\", "")
                        leftyCMD = "load('" + omhome + "/share/omc/scripts/openmodelica.lefty');" + "openmodelica.init();openmodelica.createviewandgraph('" + fileNameGraphViz + "','file',null,null);txtview('off');"
                        Debug.traceln("Running command: " + "lefty -e " + leftyCMD + " > " + fileNameTraceRemovedConnections)
                        leftyExitStatus = System.systemCall("lefty -e " + leftyCMD, fileNameTraceRemovedConnections)
                        Debug.traceln("GraphViz *lefty* exited with status:" + intString(leftyExitStatus))
                        brokenConnects = System.readFile(fileNameTraceRemovedConnections)
                        Debug.traceln("GraphViz OpenModelica assistant returned the following broken connects: " + brokenConnects)
                      brokenConnects
                  end
                end
              end
               #=  omhome = System.stringReplace(omhome, \"\\\\\", \"/\");
               =#
               #=  create a lefty command and execute it
               =#
               #=  execute lefty
               =#
               #=  show the exit status
               =#
          brokenConnectsViaGraphViz
        end

         #= @author adrpo:
         this function BROKEN removes the connects from the connection set
         and keeps the CONNECTED ones.
         Basically is implmented like this:
         1. remove all the broken connects from the inConnects -> newConnects
         2. add all the connected connects BACK to newConnects =#
        function removeBrokenConnects(inConnects::List{<:Connect.ConnectorElement}, inConnected::DaeEdges, inBroken::DaeEdges) ::List{List{Connect.ConnectorElement}}
              local outConnects::List{List{Connect.ConnectorElement}} #= we return a list of lists of elements as a particular connection set might be broken into several! =#

              outConnects = begin
                  local toRemove::List{DAE.ComponentRef}
                  local toKeep::List{DAE.ComponentRef}
                  local intersect::List{DAE.ComponentRef}
                  local cset::List{Connect.ConnectorElement}
                  local csets::List{List{Connect.ConnectorElement}}
                   #=  if we have no broken then we don't care!
                   =#
                @match (inConnects, inConnected, inBroken) begin
                  (_, _,  nil())  => begin
                    list(inConnects)
                  end

                  (_, _, _)  => begin
                      toRemove = filterFromSet(inConnects, inBroken, nil, "removed")
                      if listEmpty(toRemove)
                        csets = list(inConnects)
                      else
                        toKeep = filterFromSet(inConnects, inConnected, nil, "allowed")
                        intersect = ListUtil.intersectionOnTrue(toRemove, toKeep, ComponentReference.crefEqualNoStringCompare)
                        if Flags.isSet(Flags.CGRAPH)
                          Debug.traceln("- ConnectionGraph.removeBrokenConnects: CS: " + stringDelimitList(ListUtil.map(inConnects, ConnectUtil.printElementStr), "\\n"))
                          Debug.traceln("- ConnectionGraph.removeBrokenConnects: keep: " + stringDelimitList(ListUtil.map(toKeep, ComponentReference.printComponentRefStr), ", "))
                          Debug.traceln("- ConnectionGraph.removeBrokenConnects: delete: " + stringDelimitList(ListUtil.map(toRemove, ComponentReference.printComponentRefStr), ", "))
                          Debug.traceln("- ConnectionGraph.removeBrokenConnects: allow = remove - keep: " + stringDelimitList(ListUtil.map(intersect, ComponentReference.printComponentRefStr), ", "))
                        end
                        toRemove = ListUtil.setDifference(toRemove, intersect)
                        if Flags.isSet(Flags.CGRAPH)
                          Debug.traceln("- ConnectionGraph.removeBrokenConnects: allow - delete: " + stringDelimitList(ListUtil.map(toRemove, ComponentReference.printComponentRefStr), ", "))
                        end
                        cset = removeFromConnects(inConnects, toRemove)
                        csets = splitSetByAllowed(cset, inConnected)
                      end
                    csets
                  end
                end
              end
          outConnects #= we return a list of lists of elements as a particular connection set might be broken into several! =#
        end

        function splitSetByAllowed(inConnects::List{<:Connect.ConnectorElement}, inConnected::DaeEdges) ::List{List{Connect.ConnectorElement}}
              local outConnects::List{List{Connect.ConnectorElement}} #= we return a list of lists of elements as a particular connection set might be broken into several! =#

              local cset::List{Connect.ConnectorElement}
              local csets::List{List{Connect.ConnectorElement}}
              local e::DaeEdge
              local cr1::DAE.ComponentRef
              local cr2::DAE.ComponentRef
              local ce::Connect.ConnectorElement
              local ce1::Connect.ConnectorElement
              local ce2::Connect.ConnectorElement

              csets = nil
              for e in inConnected
                cset = nil
                (cr1, cr2, _) = e
                for ce in inConnects
                  if ComponentReference.crefPrefixOf(cr1, ce.name)
                    cset = _cons(ce, cset)
                  end
                  if ComponentReference.crefPrefixOf(cr2, ce.name)
                    cset = _cons(ce, cset)
                  end
                end
                if ! listEmpty(cset)
                  csets = _cons(cset, csets)
                end
              end
              outConnects = csets
          outConnects #= we return a list of lists of elements as a particular connection set might be broken into several! =#
        end

         #= @author: adrpo
         given an EQU set filter the given DaeEdges =#
        function filterFromSet(inConnects::List{<:Connect.ConnectorElement}, inFilter::DaeEdges, inAcc::List{<:DAE.ComponentRef}, msg::String) ::List{DAE.ComponentRef}
              local filteredCrefs::List{DAE.ComponentRef}

              filteredCrefs = begin
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local rest::DaeEdges
                  local filtered::List{DAE.ComponentRef}
                @matchcontinue (inConnects, inFilter, inAcc) begin
                  (_,  nil(), _)  => begin
                    ListUtil.unique(inAcc)
                  end

                  (_, (c1, c2, _) <| rest, _)  => begin
                      @match true = ConnectUtil.isReferenceInConnects(inConnects, c1)
                      @match true = ConnectUtil.isReferenceInConnects(inConnects, c2)
                      if Flags.isSet(Flags.CGRAPH)
                        Debug.traceln("- ConnectionGraph.filterFromSet: " + msg + " connect(" + ComponentReference.printComponentRefStr(c1) + ", " + ComponentReference.printComponentRefStr(c2) + ")")
                      end
                      filtered = filterFromSet(inConnects, rest, _cons(c1, _cons(c2, inAcc)), msg)
                    filtered
                  end

                  (_, _ <| rest, _)  => begin
                      filtered = filterFromSet(inConnects, rest, inAcc, msg)
                    filtered
                  end
                end
              end
               #=  some are not there, move forward ...
               =#
          filteredCrefs
        end

        function removeFromConnects(inConnects::List{<:Connect.ConnectorElement}, inToRemove::List{<:DAE.ComponentRef}) ::List{Connect.ConnectorElement}
              local outConnects::List{Connect.ConnectorElement}

              outConnects = begin
                  local c::DAE.ComponentRef
                  local rest::List{DAE.ComponentRef}
                  local cset::List{Connect.ConnectorElement}
                @match (inConnects, inToRemove) begin
                  (_,  nil())  => begin
                    inConnects
                  end

                  (cset, c <| rest)  => begin
                      @match (cset, true) = ConnectUtil.removeReferenceFromConnects(cset, c)
                      cset = removeFromConnects(cset, rest)
                    cset
                  end
                end
              end
          outConnects
        end

         #= @author: adrpo
         adds all the equalityConstraint equations from broken connections =#
        function addBrokenEqualityConstraintEquations(inDAE::DAE.DAElist, inBroken::DaeEdges) ::DAE.DAElist
              local outDAE::DAE.DAElist

              outDAE = begin
                  local equalityConstraintElements::List{DAE.Element}
                  local dae::DAE.DAElist
                @matchcontinue (inDAE, inBroken) begin
                  (_,  nil())  => begin
                    inDAE
                  end

                  _  => begin
                        equalityConstraintElements = ListUtil.flatten(ListUtil.map(inBroken, Util.tuple33))
                        dae = DAEUtil.joinDaes(DAE.DAE(equalityConstraintElements), inDAE)
                      dae
                  end
                end
              end
          outDAE
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  #=TODO: Originally partial =# module DisjointSets 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    EntryHash = Function
    EntryEqual = Function
    EntryString = Function
    @UniontypeDecl Sets 
    FuncHash = Function
    FuncEq = Function
    FuncKeyString = Function
    FuncValString = Function

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
        import ArrayUtil
        import BaseHashTable
        import Util

        Entry = ModelicaInteger 







          #= This is a disjoint sets data structure. The nodes are stored in an array of
            Integers. The root elements of a set is given a negative value that
            corresponds to its rank, while other elements are given positive values that
            corresponds to the index of their parent in the array. The hashtable is used
            to look up the array index of a entry, and is also used to store the entries. =#
         @Uniontype Sets begin
              @Record DISJOINT_SETS begin

                       nodes #= An array of nodes =#::Array{ModelicaInteger}
                       elements #= A Entry->Integer hashtable, see bottom of file. =#::IndexTable
                       nodeCount #= The number of nodes stored in the sets. =#::ModelicaInteger
              end
         end

         #= Creates a new disjoint-sets structure. =#
        function emptySets(setCount::ModelicaInteger) ::Sets 
              local sets::Sets

              local nodes::Array{ModelicaInteger}
              local elements::IndexTable
              local sz::ModelicaInteger

               #=  Create an array as large as the number of sets given, or at least 3 to
               =#
               #=  avoid issues.
               =#
              sz = max(setCount, 3)
               #=  Fill the array with -1, which is the value of a newly added element.
               =#
              nodes = arrayCreate(sz, -1)
              elements = emptyIndexTableSized(Util.nextPrime(sz))
              sets = Sets.DISJOINT_SETS(nodes, elements, 0)
          sets
        end

         #= Adds an entry to the disjoint-sets forest. This function assumes that the
           entry does not already exist in the forest. If the entry might exist already,
           use find instead. =#
        function add(entry::Entry, sets::Sets) ::Tuple{Sets, ModelicaInteger} 
              local index::ModelicaInteger


              local nodes::Array{ModelicaInteger}
              local elements::IndexTable
              local node_count::ModelicaInteger

              @match Sets.DISJOINT_SETS(nodes, elements, node_count) = sets
              index = node_count + 1
               #=  Make sure that we have enough space in the node array. New nodes have the
               =#
               #=  value -1, so we don't actually need to add a node to the array, just expand
               =#
               #=  it and fill the new places with -1.
               =#
              if index > arrayLength(nodes)
                nodes = ArrayUtil.expand(realInt(intReal(index) * 1.4), nodes, -1)
              end
               #=  Register the node index in the index table.
               =#
              elements = BaseHashTable.addNoUpdCheck((entry, index), elements)
              sets = Sets.DISJOINT_SETS(nodes, elements, index)
          (sets, index)
        end

         #= Adds a list of entries to the disjoint-sets forest, in a more efficient
           manner than calling add repeatedly. This function assumes that the entries
           does not already exist in the forest. If the entries might exist already, use
           find instead. =#
        function addList(entries::List{<:Entry}, sets::Sets) ::Sets 


              local nodes::Array{ModelicaInteger}
              local elements::IndexTable
              local node_count::ModelicaInteger
              local sz::ModelicaInteger
              local index::ModelicaInteger

              @match Sets.DISJOINT_SETS(nodes, elements, node_count) = sets
              sz = listLength(entries)
              index = node_count + 1
              node_count = node_count + sz
              if node_count > arrayLength(nodes)
                nodes = ArrayUtil.expand(realInt(intReal(node_count) * 1.4), nodes, -1)
              end
              for e in entries
                elements = BaseHashTable.addNoUpdCheck((e, index), elements)
                index = index + 1
              end
              sets = Sets.DISJOINT_SETS(nodes, elements, node_count)
          sets
        end

         #= This function finds and returns the set that the given entry belongs to.
           The set is represented by the root node of the tree. If the entry does not
           have a corresponding node in the forest, then a new set with the entry as the
           only element will be added to the forest and returned.

           The reason why this function also returns the sets is because it does path
           compression, and the disjoint-set structure may therefore be changed during
           look up. =#
        function findSet(entry::Entry, sets::Sets) ::Tuple{ModelicaInteger, Sets} 
              local updatedSets::Sets
              local set::ModelicaInteger

              local index::ModelicaInteger

               #=  Look up the index of the entry.
               =#
              (updatedSets, index) = find(entry, sets)
               #=  Return the index of the root of the tree that the entry belongs to.
               =#
              set = findRoot(index, updatedSets.nodes)
          (set, updatedSets)
        end

         #= Returns the index of the set the entry belongs to, or fails if the
           entry doesn't belong to a set. =#
        function findSetArrayIndex(entry::Entry, sets::Sets) ::ModelicaInteger 
              local set::ModelicaInteger

               #=  Look up the index of the given entry.
               =#
              set = BaseHashTable.get(entry, sets.elements)
               #=  Follow the indices until a negative index is found, which is the set index.
               =#
              while set > 0
                set = sets.nodes[set]
              end
               #=  Negate the index to get the actual set index.
               =#
              set = -set
          set
        end

         #= myMerges the two sets that the given entry belong to. =#
        function myMerge(entry1::Entry, entry2::Entry, sets::Sets) ::Sets 


              local set1::ModelicaInteger
              local set2::ModelicaInteger

              (set1, sets) = findSet(entry1, sets)
              (set2, sets) = findSet(entry2, sets)
              sets = union(set1, set2, sets)
          sets
        end

         #= This function finds and returns the node associated with a given entry.
           If the entry does not a have a node in the forest, then a new node will be
           added and returned.

           The reason why this function also returns the sets is because it does path
           compression, and the disjoint-set structure may therefore be changed during
           look up. =#
        function find(entry::Entry, sets::Sets) ::Tuple{Sets, ModelicaInteger} 
              local index::ModelicaInteger


              try
                index = BaseHashTable.get(entry, sets.elements)
              catch
                (sets, index) = add(entry, sets)
              end
               #=  Check if a node already exists in the forest.
               =#
               #=  If a node doesn't already exist, create a new one.
               =#
          (sets, index)
        end

         #= Returns the index of the root of the tree that a node belongs to. =#
        function findRoot(nodeIndex::ModelicaInteger, nodes::Array{<:ModelicaInteger}) ::ModelicaInteger 
              local rootIndex::ModelicaInteger = nodeIndex

              local parent::ModelicaInteger = nodes[nodeIndex]
              local idx::ModelicaInteger = nodeIndex

               #=  Follow the parent indices until we find a negative index, which indicates a root.
               =#
              while parent > 0
                rootIndex = parent
                parent = nodes[parent]
              end
               #=  Path compression. Attach each of the traversed nodes directly to the root,
               =#
               #=  to speed up repeated calls.
               =#
              parent = nodes[nodeIndex]
              while parent > 0
                arrayUpdate(nodes, idx, rootIndex)
                idx = parent
                parent = nodes[parent]
              end
          rootIndex
        end

         #= myMerges two sets into one. This is done by attaching one set-tree to the
           other. The ranks are compared to determine which of the trees is the
           smallest, and that one is attached to the larger one to keep the trees as
           flat as possible. =#
        function union(set1::ModelicaInteger, set2::ModelicaInteger, sets::Sets) ::Sets 


              local rank1::ModelicaInteger
              local rank2::ModelicaInteger

              if set1 != set2
                rank1 = sets.nodes[set1]
                rank2 = sets.nodes[set2]
                if rank1 > rank2
                  arrayUpdate(sets.nodes, set2, set1)
                elseif rank1 < rank2
                  arrayUpdate(sets.nodes, set1, set2)
                else
                  arrayUpdate(sets.nodes, set1, sets.nodes[set1] - 1)
                  arrayUpdate(sets.nodes, set2, set1)
                end
              end
               #=  Assume that the indices actually point to root nodes, in which case the
               =#
               #=  entries in the node array is actually the ranks of the nodes.
               =#
               #=  First set is smallest, attach it to the second set.
               =#
               #=  Second set is smallest, attach it to the first set.
               =#
               #=  Both sets are the same size. Attach the second to the first, and
               =#
               #=  increase the rank of the first with one (which means decreasing it,
               =#
               #=  since the rank is stored as a negative number).
               =#
          sets
        end

         #= Returns the number of nodes in the disjoint-set forest. =#
        function getNodeCount(sets::Sets) ::ModelicaInteger 
              local nodeCount::ModelicaInteger = sets.nodeCount
          nodeCount
        end

         #= Extracts all the sets from the disjoint sets structure, and returns
           them as an array. The function also returns a new DisjointSets structure where
           all roots have been assigned a set index, which can be used for looking up
           sets in the array with findSetArrayIndex. =#
        function extractSets(sets::Sets) ::Tuple{Array{List{Entry}}, Sets} 
              local assignedSets::Sets #= Sets with the roots assigned to sets. =#
              local setsArray::Array{List{Entry}} #= An array with all the sets. =#

              local nodes::Array{ModelicaInteger}
              local set_idx::ModelicaInteger = 0
              local idx::ModelicaInteger
              local entries::List{Tuple{Entry, ModelicaInteger}}
              local e::Entry

              nodes = sets.nodes
               #=  Go through each node and assign a unique set index to each root node.
               =#
               #=  The index is stored as a negative number to mark the node as a root.
               =#
              for i in 1:sets.nodeCount
                if nodes[i] < 0
                  set_idx = set_idx + 1
                  nodes[i] = -set_idx
                end
              end
               #=  Create an array of lists to store the sets in, and fetch the list of
               =#
               #=  entry-index pairs stored in the hashtable.
               =#
              setsArray = arrayCreate(set_idx, nil)
              entries = BaseHashTable.hashTableListReversed(sets.elements)
               #=  Go through each entry-index pair.
               =#
              for p in entries
                (e, idx) = p
                set_idx = nodes[idx]
                while set_idx > 0
                  set_idx = nodes[set_idx]
                end
                set_idx = -set_idx
                setsArray[set_idx] = _cons(e, setsArray[set_idx])
              end
               #=  Follow the parent indices until we find the root.
               =#
               #=  Negate the set index to get the actual index.
               =#
               #=  Add the entry to the list pointed to by the set index.
               =#
              assignedSets = Sets.DISJOINT_SETS(nodes, sets.elements, sets.nodeCount)
          (setsArray #= An array with all the sets. =#, assignedSets #= Sets with the roots assigned to sets. =#)
        end

         #= Print out the sets for debugging. =#
        function printSets(sets::Sets)  
              local nodes::Array{ModelicaInteger}
              local entries::List{Tuple{Entry, ModelicaInteger}}
              local e::Entry
              local i::ModelicaInteger

              print(intString(sets.nodeCount) + " sets:\\n")
              nodes = sets.nodes
              entries = BaseHashTable.hashTableList(sets.elements)
              for p in entries
                (e, i) = p
                print("[")
                print(StringFunction(i))
                print("]")
                print(EntryString(e))
                print(" -> ")
                print(StringFunction(nodes[i]))
                print("\\n")
              end
        end

         #=  Hashtable used by the DisjointSets structure.
         =#
        HashValue = ModelicaInteger 
        IndexTable = Tuple 









         #= Creates an empty index table with the given size. =#
        function emptyIndexTableSized(tableSize::ModelicaInteger) ::IndexTable 
              local table::IndexTable

              table = BaseHashTable.emptyHashTableWork(tableSize, (EntryHash, EntryEqual, EntryString, intString))
          table
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
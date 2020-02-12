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

module InnerOuterTypes


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    import Setfield

    @UniontypeDecl InstResult
    @UniontypeDecl InstInner
    @UniontypeDecl OuterPrefix
    @UniontypeDecl TopInstance
    @UniontypeDecl InstHierarchyHashTable
    @UniontypeDecl ValueArray
    const InstHierarchy = List
    const emptyInstHierarchy = nil #= an empty instance hierarchy =#::InstHierarchy


        @importDBG Absyn
        @importDBG ConnectionGraph
        @importDBG DAE
        @importDBG FCore
        @importDBG Prefix
        @importDBG SCode
        @importDBG UnitAbsyn
        @importDBG HashSet
        @importDBG ArrayUtil

        @importDBG CrefForHashTable

        @importDBG ListUtil

        @importDBG Util

        Cache = FCore.Cache

         @Uniontype InstResult begin
              @Record INST_RESULT begin

                       outCache::Cache
                       outEnv::FCore.Graph
                       outStore::UnitAbsyn.InstStore
                       outDae::DAE.DAElist
                       outSets::DAE.Sets
                       outType::DAE.Type
                       outGraph::ConnectionGraph.ConnectionGraphType
              end
         end

         @Uniontype InstInner begin
              @Record INST_INNER begin

                       innerPrefix #= the prefix of the inner. we need it to prefix the outer variables with it! =#::Prefix.PrefixType
                       name::SCode.Ident
                       io::Absyn.InnerOuter
                       fullName #= full inner component name =#::String
                       typePath #= the type of the inner =#::Absyn.Path
                       scope #= the scope of the inner =#::String
                       instResult::Option{InstResult}
                       outers #= which outers are referencing this inner =#::List{DAE.ComponentRef}
                       innerElement #= class or component =#::Option{SCode.Element}
              end
         end

         @Uniontype OuterPrefix begin
              @Record OUTER begin

                       outerComponentRef #= the prefix of this outer + component name =#::DAE.ComponentRef
                       innerComponentRef #= the coresponding prefix for this outer + component name =#::DAE.ComponentRef
              end
         end

        OuterPrefixes = List
         const emptyOuterPrefixes = nil #= empty outer prefixes =#::OuterPrefixes

        Key = DAE.ComponentRef  #= the prefix + '.' + the component name =#
        Value = InstInner  #= the inputs of the instantiation function and the results =#

          #= a top instance is an instance of a model thar resides at top level =#
         @Uniontype TopInstance begin
              @Record TOP_INSTANCE begin

                       path #= top model path =#::Option{Absyn.Path}
                       ht #= hash table with fully qualified components =#::InstHierarchyHashTable
                       outerPrefixes #= the outer prefixes help us prefix the outer components with the correct prefix of inner component directly =#::OuterPrefixes
                       sm #= Set of synchronous SM states (fully qualified components) =#::HashSet.HashSetType
              end
         end

         #= /
         =#
         #=  hash table implementation for InnerOuterTypes instance hierarchy
         =#
         #= /
         =#

         #= author: PA
          Calculates a hash value for DAE.ComponentRef =#
        function hashFunc(k::Key) ::ModelicaInteger
              local res::ModelicaInteger

              res = stringHashDjb2(CrefForHashTable.printComponentRefStr(k))
          res
        end

        function keyEqual(key1::Key, key2::Key) ::Bool
              local res::Bool

              res = CrefForHashTable.crefEqualNoStringCompare(key1, key2)
          res
        end

         #=  =#
        function dumpInstHierarchyHashTable(t::InstHierarchyHashTable)
              print("InstHierarchyHashTable:\\n")
              print(stringDelimitList(ListUtil.map(hashTableList(t), dumpTuple), "\\n"))
              print("\\n")
        end

        function dumpTuple(tpl::Tuple{<:Key, Value}) ::String
              local str::String

              str = begin
                  local k::Key
                  local v::Value
                @match tpl begin
                  (k, _)  => begin
                      str = "{" + CrefForHashTable.crefStr(k) + " opaque InstInner for now, implement printing. " + "}\\n"
                    str
                  end
                end
              end
          str
        end

         #= /* end of InstHierarchyHashTable instance specific code */ =#
         #= /* Generic hashtable code below!! */ =#

         @Uniontype InstHierarchyHashTable begin
              @Record HASHTABLE begin

                       hashTable #=  hashtable to translate Key to array indx =#::Array{List{Tuple{Key, ModelicaInteger}}}
                       valueArr #= Array of values =#::ValueArray
                       bucketSize #= bucket size =#::ModelicaInteger
                       numberOfEntries #= number of entries in hashtable =#::ModelicaInteger
              end
         end

          #= array of values are expandable, to amortize the
          cost of adding elements in a more efficient manner =#
         @Uniontype ValueArray begin
              @Record VALUE_ARRAY begin

                       numberOfElements #= number of elements in hashtable =#::ModelicaInteger
                       valueArray #= array of values =#::Array{Option{Tuple{Key, Value}}}
              end
         end

         #= Author BZ 2008-06
         Make a stand-alone-copy of hashtable. =#
        function cloneInstHierarchyHashTable(inHash::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHash::InstHierarchyHashTable

              outHash = begin
                  local arg1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local arg1_2::Array{List{Tuple{Key, ModelicaInteger}}}
                  local arg3::ModelicaInteger
                  local arg4::ModelicaInteger
                  local arg3_2::ModelicaInteger
                  local arg4_2::ModelicaInteger
                  local arg21::ModelicaInteger
                  local arg21_2::ModelicaInteger
                  local arg22::Array{Option{Tuple{Key, Value}}}
                  local arg22_2::Array{Option{Tuple{Key, Value}}}
                @match inHash begin
                  HASHTABLE(arg1, VALUE_ARRAY(arg21, arg22), arg3, arg4)  => begin
                      arg1_2 = arrayCopy(arg1)
                      arg21_2 = arg21
                      arg22_2 = arrayCopy(arg22)
                      arg3_2 = arg3
                      arg4_2 = arg4
                    HASHTABLE(arg1_2, VALUE_ARRAY(arg21_2, arg22_2), arg3_2, arg4_2)
                  end
                end
              end
          outHash
        end

         #= author: PA
          Returns an empty InstHierarchyHashTable.
          Using the bucketsize 100 and array size 10. =#
        function emptyInstHierarchyHashTable() ::InstHierarchyHashTable
              local hashTable::InstHierarchyHashTable

              local arr::Array{List{Tuple{Key, ModelicaInteger}}}
              local lst::List{Option{Tuple{Key, Value}}}
              local emptyarr::Array{Option{Tuple{Key, Value}}}

              arr = arrayCreate(1000, nil)
              emptyarr = arrayCreate(100, NONE())
              hashTable = HASHTABLE(arr, VALUE_ARRAY(0, emptyarr), 1000, 0)
          hashTable
        end

         #= Returns true if hashtable is empty =#
        function isEmpty(hashTable::InstHierarchyHashTable) ::Bool
              local res::Bool

              res = begin
                @match hashTable begin
                  HASHTABLE(_, _, _, 0)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= author: PA
          Add a Key-Value tuple to hashtable.
          If the Key-Value tuple already exists, the function updates the Value. =#
        function add(entry::Tuple{<:Key, Value}, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local key::Key
                  local value::Value
                   #= /* Adding when not existing previously */ =#
                @matchcontinue (entry, hashTable) begin
                  (v && (key, _), HASHTABLE(hashvec, varr, bsize, _))  => begin
                      @shouldFail _ = get(key, hashTable)
                      hval = hashFunc(key)
                      indx = intMod(hval, bsize)
                      newpos = valueArrayLength(varr)
                      varr_1 = valueArrayAdd(varr, v)
                      indexes = hashvec[indx + 1]
                      hashvec_1 = arrayUpdate(hashvec, indx + 1, _cons((key, newpos), indexes))
                      n_1 = valueArrayLength(varr_1)
                    HASHTABLE(hashvec_1, varr_1, bsize, n_1)
                  end

                  (newv && (key, _), HASHTABLE(hashvec, varr, bsize, n))  => begin
                      (_, indx) = get1(key, hashTable)
                      varr_1 = valueArraySetnth(varr, indx, newv)
                    HASHTABLE(hashvec, varr_1, bsize, n)
                  end

                  _  => begin
                        print("- InnerOuterTypes.add failed\\n")
                      fail()
                  end
                end
              end
               #=  print(\"Added NEW to IH: key:\" + CrefForHashTable.printComponentRefStr(key) + \" value: \" + printInnerDefStr(value) + \"\\n\");
               =#
               #= /* adding when already present => Updating value */ =#
               #= print(\"adding when present, indx =\" );print(intString(indx));print(\"\\n\");
               =#
               #=  print(\"Updated NEW to IH: key:\" + CrefForHashTable.printComponentRefStr(key) + \" value: \" + printInnerDefStr(value) + \"\\n\");
               =#
          outHashTable
        end

         #= author: PA
          Add a Key-Value tuple to hashtable.
          If the Key-Value tuple already exists, the function updates the Value. =#
        function addNoUpdCheck(entry::Tuple{<:Key, Value}, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local name_str::String
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local key::Key
                  local value::Value
                   #=  Adding when not existing previously
                   =#
                @matchcontinue (entry, hashTable) begin
                  (v && (key, _), HASHTABLE(hashvec, varr, bsize, _))  => begin
                      hval = hashFunc(key)
                      indx = intMod(hval, bsize)
                      newpos = valueArrayLength(varr)
                      varr_1 = valueArrayAdd(varr, v)
                      indexes = hashvec[indx + 1]
                      hashvec_1 = arrayUpdate(hashvec, indx + 1, _cons((key, newpos), indexes))
                      n_1 = valueArrayLength(varr_1)
                    HASHTABLE(hashvec_1, varr_1, bsize, n_1)
                  end

                  _  => begin
                        print("- InnerOuterTypes.addNoUpdCheck failed\\n")
                      fail()
                  end
                end
              end
          outHashTable
        end

         #= author: PA
          delete the Value associatied with Key from the InstHierarchyHashTable.
          Note: This function does not delete from the index table, only from the ValueArray.
          This means that a lot of deletions will not make the InstHierarchyHashTable more compact, it
          will still contain a lot of incices information. =#
        function delete(key::Key, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local name_str::String
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local value::Value
                   #=  adding when already present => Updating value
                   =#
                @matchcontinue (key, hashTable) begin
                  (_, HASHTABLE(hashvec, varr, bsize, n))  => begin
                      (_, indx) = get1(key, hashTable)
                      varr_1 = valueArrayClearnth(varr, indx)
                    HASHTABLE(hashvec, varr_1, bsize, n)
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.delete failed\\n")
                        print("content:")
                        dumpInstHierarchyHashTable(hashTable)
                      fail()
                  end
                end
              end
          outHashTable
        end

         #= author: PA
          Returns a Value given a Key and a InstHierarchyHashTable. =#
        function get(key::Key, hashTable::InstHierarchyHashTable) ::Value
              local value::Value

              (value, _) = get1(key, hashTable)
          value
        end

         #= help function to get =#
        function get1(key::Key, hashTable::InstHierarchyHashTable) ::Tuple{Value, ModelicaInteger}
              local indx::ModelicaInteger
              local value::Value

              (value, indx) = begin
                  local hval::ModelicaInteger
                  local hashindx::ModelicaInteger
                  local bsize::ModelicaInteger
                  local n::ModelicaInteger
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local v::Value
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local varr::ValueArray
                  local k::Key
                @match (key, hashTable) begin
                  (_, HASHTABLE(hashvec, varr, bsize, _))  => begin
                      hval = hashFunc(key)
                      hashindx = intMod(hval, bsize)
                      indexes = hashvec[hashindx + 1]
                      indx = get2(key, indexes)
                      (k, v) = valueArrayNth(varr, indx)
                      @match true = keyEqual(k, key)
                    (v, indx)
                  end
                end
              end
          (value, indx)
        end

         #= author: PA
          Helper function to get =#
        function get2(key::Key, keyIndices::List{<:Tuple{<:Key, ModelicaInteger}}) ::ModelicaInteger
              local index::ModelicaInteger

              index = begin
                  local key2::Key
                  local xs::List{Tuple{Key, ModelicaInteger}}
                @matchcontinue (key, keyIndices) begin
                  (_, (key2, index) <| _)  => begin
                      @match true = keyEqual(key, key2)
                    index
                  end

                  (_, _ <| xs)  => begin
                      index = get2(key, xs)
                    index
                  end
                end
              end
          index
        end

         #= return the Value entries as a list of Values =#
        function hashTableValueList(hashTable::InstHierarchyHashTable) ::List{Value}
              local valLst::List{Value}

              valLst = ListUtil.map(hashTableList(hashTable), Util.tuple22)
          valLst
        end

         #= return the Key entries as a list of Keys =#
        function hashTableKeyList(hashTable::InstHierarchyHashTable) ::List{Key}
              local valLst::List{Key}

              valLst = ListUtil.map(hashTableList(hashTable), Util.tuple21)
          valLst
        end

         #= returns the entries in the hashTable as a list of tuple<Key,Value> =#
        function hashTableList(hashTable::InstHierarchyHashTable) ::List{Tuple{Key, Value}}
              local tplLst::List{Tuple{Key, Value}}

              tplLst = begin
                  local varr::ValueArray
                @match hashTable begin
                  HASHTABLE(valueArr = varr)  => begin
                      tplLst = valueArrayList(varr)
                    tplLst
                  end
                end
              end
          tplLst
        end

         #= author: PA
          Transforms a ValueArray to a tuple<Key,Value> list =#
        function valueArrayList(valueArray::ValueArray) ::List{Tuple{Key, Value}}
              local tplLst::List{Tuple{Key, Value}}

              tplLst = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local elt::Tuple{Key, Value}
                  local lastpos::ModelicaInteger
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                  local lst::List{Tuple{Key, Value}}
                @matchcontinue valueArray begin
                  VALUE_ARRAY(numberOfElements = 0)  => begin
                    nil
                  end

                  VALUE_ARRAY(numberOfElements = 1, valueArray = arr)  => begin
                      @match SOME(elt) = arr[0 + 1]
                    list(elt)
                  end

                  VALUE_ARRAY(numberOfElements = n, valueArray = arr)  => begin
                      lastpos = n - 1
                      lst = valueArrayList2(arr, 0, lastpos)
                    lst
                  end
                end
              end
          tplLst
        end

         #= Helper function to valueArrayList =#
        function valueArrayList2(inVarOptionArray1::Array{<:Option{<:Tuple{<:Key, Value}}}, inInteger2::ModelicaInteger, inInteger3::ModelicaInteger) ::List{Tuple{Key, Value}}
              local outVarLst::List{Tuple{Key, Value}}

              outVarLst = begin
                  local v::Tuple{Key, Value}
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local pos::ModelicaInteger
                  local lastpos::ModelicaInteger
                  local pos_1::ModelicaInteger
                  local res::List{Tuple{Key, Value}}
                @matchcontinue (inVarOptionArray1, inInteger2, inInteger3) begin
                  (arr, pos, lastpos)  => begin
                      if !(pos == lastpos)
                        fail()
                      end
                      @match SOME(v) = arr[pos + 1]
                    list(v)
                  end

                  (arr, pos, lastpos)  => begin
                      pos_1 = pos + 1
                      @match SOME(v) = arr[pos + 1]
                      res = valueArrayList2(arr, pos_1, lastpos)
                    _cons(v, res)
                  end

                  (arr, pos, lastpos)  => begin
                      pos_1 = pos + 1
                      @match NONE() = arr[pos + 1]
                      res = valueArrayList2(arr, pos_1, lastpos)
                    res
                  end
                end
              end
          outVarLst
        end

         #= author: PA
          Returns the number of elements in the ValueArray =#
        function valueArrayLength(valueArray::ValueArray) ::ModelicaInteger
              local size::ModelicaInteger

              size = begin
                @match valueArray begin
                  VALUE_ARRAY(numberOfElements = size)  => begin
                    size
                  end
                end
              end
          size
        end

         #= author: PA
          Adds an entry last to the ValueArray, increasing
          array size if no space left by factor 1.4 =#
        function valueArrayAdd(valueArray::ValueArray, entry::Tuple{<:Key, Value}) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local n_1::ModelicaInteger
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                  local expandsize::ModelicaInteger
                  local expandsize_1::ModelicaInteger
                  local newsize::ModelicaInteger
                  local arr_1::Array{Option{Tuple{Key, Value}}}
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local arr_2::Array{Option{Tuple{Key, Value}}}
                  local rsize::ModelicaReal
                  local rexpandsize::ModelicaReal
                @matchcontinue (valueArray, entry) begin
                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      if !(n < arrayLength(arr))
                        fail() #= Have space to add array elt. =#
                      end #= Have space to add array elt. =#
                      n_1 = n + 1
                      arr_1 = arrayUpdate(arr, n + 1, SOME(entry))
                    VALUE_ARRAY(n_1, arr_1)
                  end

                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      size = arrayLength(arr)
                      if (n < size)
                        fail() #= Do NOT have splace to add array elt. Expand with factor 1.4 =#
                      end #= Do NOT have splace to add array elt. Expand with factor 1.4 =#
                      rsize = intReal(size)
                      rexpandsize = rsize * 0.4
                      expandsize = realInt(rexpandsize)
                      expandsize_1 = intMax(expandsize, 1)
                      arr_1 = ArrayUtil.expand(expandsize_1, arr, NONE())
                      n_1 = n + 1
                      arr_2 = arrayUpdate(arr_1, n + 1, SOME(entry))
                    VALUE_ARRAY(n_1, arr_2)
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArrayAdd failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Set the n:th variable in the ValueArray to value. =#
        function valueArraySetnth(valueArray::ValueArray, pos::ModelicaInteger, entry::Tuple{<:Key, Value}) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                @matchcontinue (valueArray, pos, entry) begin
                  (VALUE_ARRAY(_, arr), _, _)  => begin
                      if !(pos < arrayLength(arr))
                        fail()
                      end
                      arrayUpdate(arr, pos + 1, SOME(entry))
                    valueArray
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArraySetnth failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Clears the n:th variable in the ValueArray (set to NONE()). =#
        function valueArrayClearnth(valueArray::ValueArray, pos::ModelicaInteger) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                @matchcontinue (valueArray, pos) begin
                  (VALUE_ARRAY(_, arr), _)  => begin
                      if !(pos < arrayLength(arr))
                        fail()
                      end
                      arrayUpdate(arr, pos + 1, NONE())
                    valueArray
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArrayClearnth failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Retrieve the n:th Vale from ValueArray, index from 0..n-1. =#
        function valueArrayNth(valueArray::ValueArray, pos::ModelicaInteger) ::Tuple{Key, Value}
              local value::Value
              local key::Key

              (key, value) = begin
                  local k::Key
                  local v::Value
                  local n::ModelicaInteger
                  local arr::Array{Option{Tuple{Key, Value}}}
                @match (valueArray, pos) begin
                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      if !(pos < n)
                        fail()
                      end
                      @match SOME((k, v)) = arr[pos + 1]
                    (k, v)
                  end
                end
              end
          (key, value)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

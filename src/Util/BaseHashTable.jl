  module BaseHashTable


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

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
         #=  Below is the instance specific code. For each hashtable the user must define:
         =#
         #=  Key      - The key used to uniquely define elements in a hashtable
         =#
         #=  Value    - The data to associate with each key
         =#
         #=  hashFunc - A function that maps a key to a positive integer.
         =#
         #=  keyEqual - A comparison function between two keys, returns true if equal.
         =#

        import ArrayUtil
        import Error
        import ListUtil
         #=  Generic hashtable code below
         =#
         #=  adrpo: use a prime here (pick your poison):
         =#
         #=         3   5   7  11  13  17  19  23  29  31  37  41  43  47  53  59  61  67
         =#
         #=        71  73  79  83  89  97 101 103 107 109 113 127 131 137 139 149 151 157
         =#
         #=       163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251 257
         =#
         #=       263 269 271 277 281 283 293 307 311 313 317 331 337 347 349 353 359 367
         =#
         #=       373 379 383 389 397 401 409 419 421 431 433 439 443 449 457 461 463 467
         =#
         #=       479 487 491 499 503 509 521 523 541 547 557 563 569 571 577 587 593 599
         =#
         #=       601 607 613 617 619 631 641 643 647 653 659 661 673 677 683 691 701 709
         =#
         #=       719 727 733 739 743 751 757 761 769 773 787 797 809 811 821 823 827 829
         =#
         #=       839 853 857 859 863 877 881 883 887 907 911 919 929 937 941 947 953 967
         =#
         #=       971 977 983 991 997 1013 2053 3023 4013 4999 5051 5087 24971
         =#
         #=
         =#
         #=  You can also use Util.nextPrime if you know exactly how large the hash table
         =#
         #=  should be.
         =#

         const lowBucketSize = 257::ModelicaInteger

         const avgBucketSize = 2053::ModelicaInteger

         const bigBucketSize = 4013::ModelicaInteger

         const biggerBucketSize = 25343::ModelicaInteger

         const hugeBucketSize = 536870879 #= 2^29 - 33 is prime :) =#::ModelicaInteger

         const defaultBucketSize = avgBucketSize::ModelicaInteger

        Key = Any
        Value = Any
        HashEntry = Tuple
        HashNode = List
        HashTable = Tuple
        HashVector = Array
        ValueArray = Tuple
        FuncsTuple = Tuple









         #= calculate the values array size based on the bucket size =#
        function bucketToValuesSize(szBucket::ModelicaInteger) ::ModelicaInteger
              local szArr::ModelicaInteger

              szArr = realInt(realMul(intReal(szBucket), 0.6))
               #=  intDiv(szBucket, 10);
               =#
          szArr
        end

        function emptyHashTableWork(szBucket::ModelicaInteger, fntpl::FuncsTuple) ::HashTable
              local hashTable::HashTable

              local arr::Array{List{Tuple{Key, ModelicaInteger}}}
              local lst::List{Option{Tuple{Key, Value}}}
              local emptyarr::Array{Option{Tuple{Key, Value}}}

              local szArr::ModelicaInteger

              if szBucket < 1
                Error.addInternalError("Got internal hash table size " + intString(szBucket) + " <1", sourceInfo())
                fail()
              end
              arr = arrayCreate(szBucket, nil)
              szArr = bucketToValuesSize(szBucket)
              emptyarr = arrayCreate(szArr, NONE())
              hashTable = (arr, (0, szArr, emptyarr), szBucket, fntpl)
          hashTable
        end

         #= Add a Key-Value tuple to hashtable.
           If the Key-Value tuple already exists, the function updates the Value. =#
        function add(entry::HashEntry, hashTable::HashTable) ::HashTable
              local outHashTable::HashTable

              local hashvec::HashVector
              local varr::ValueArray
              local bsize::ModelicaInteger
              local hash_idx::ModelicaInteger
              local arr_idx::ModelicaInteger
              local new_pos::ModelicaInteger
              local fntpl::FuncsTuple
              local hashFunc::FuncHash
              local keyEqual::FuncEq
              local key::Key
              local key2::Key
              local val::Value
              local indices::HashNode

              (key, _) = entry
              @match (hashvec, varr, bsize, fntpl) = hashTable
              @match (hashFunc, keyEqual, _, _) = fntpl
              hash_idx = hashFunc(key, bsize) + 1
              indices = hashvec[hash_idx]
              for i in indices
                (key2, _) = i
                if keyEqual(key, key2)
                  (_, arr_idx) = i
                  valueArraySet(varr, arr_idx, entry)
                  outHashTable = hashTable
                  return outHashTable
                end
              end
              (varr, new_pos) = valueArrayAdd(varr, entry)
              arrayUpdate(hashvec, hash_idx, _cons((key, new_pos), indices))
              outHashTable = (hashvec, varr, bsize, fntpl)
          outHashTable
        end

         #=
        author: PA.
        dump statistics on how many entries per hash value. Useful to see how hash function behaves =#
        function dumpHashTableStatistics(hashTable::HashTable)
              _ = begin
                  local hvec::HashVector
                @match hashTable begin
                  (hvec, _, _, _)  => begin
                      print("index list lengths:\\n")
                      print(stringDelimitList(list(intString(listLength(l)) for l in hvec), ","))
                      print("\\n")
                      print("non-zero: " + String(sum(1 for l in hvec if ! listEmpty(l))) + "/" + String(arrayLength(hvec)) + "\\n")
                      print("max element: " + String(max(listLength(l) for l in hvec)) + "\\n")
                      print("total entries: " + String(sum(listLength(l) for l in hvec)) + "\\n")
                    ()
                  end
                end
              end
        end

         #= Add a Key-Value tuple to hashtable, without checking if it already exists.
           This function is thus more efficient than add if you already know that the
           Key-Value tuple doesn't already exist in the hashtable. =#
        function addNoUpdCheck(entry::HashEntry, hashTable::HashTable) ::HashTable
              local outHashTable::HashTable

              outHashTable = begin
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local bsize::ModelicaInteger
                  local varr::ValueArray
                  local indexes::HashNode
                  local hashvec::HashVector
                  local v::Tuple{Key, Value}
                  local key::Key
                  local value::Value
                  local fntpl::FuncsTuple
                  local hashFunc::FuncHash
                   #=  Adding when not existing previously
                   =#
                @matchcontinue (entry, hashTable) begin
                  (v && (key, _), (hashvec, varr, bsize, fntpl && (hashFunc, _, _, _)))  => begin
                      indx = hashFunc(key, bsize) + 1
                      (varr, newpos) = valueArrayAdd(varr, v)
                      indexes = hashvec[indx]
                      hashvec = arrayUpdate(hashvec, indx, _cons((key, newpos), indexes))
                    (hashvec, varr, bsize, fntpl)
                  end

                  _  => begin
                        print("- BaseHashTable.addNoUpdCheck failed\\n")
                      fail()
                  end
                end
              end
          outHashTable
        end

         #= Add a Key-Value tuple to hashtable. If the Key is already used it fails. =#
        function addUnique(entry::HashEntry, hashTable::HashTable) ::HashTable
              local outHashTable::HashTable

              local indx::ModelicaInteger
              local newpos::ModelicaInteger
              local bsize::ModelicaInteger
              local varr::ValueArray
              local indexes::HashNode
              local hashvec::HashVector
              local key::Key
              local fntpl::FuncsTuple
              local hashFunc::FuncHash

               #=  Adding when not existing previously
               =#
              (key, _) = entry
              @match (hashvec, varr, bsize, (@match (hashFunc, _, _, _) = fntpl)) = hashTable
              @shouldFail _ = get(key, hashTable)
              indx = hashFunc(key, bsize) + 1
              (varr, newpos) = valueArrayAdd(varr, entry)
              indexes = hashvec[indx]
              hashvec = arrayUpdate(hashvec, indx, _cons((key, newpos), indexes))
              outHashTable = (hashvec, varr, bsize, fntpl)
          outHashTable
        end

         #= Updates an already existing value in the hashtable. Fails if the entry does
           not exist. =#
        function update(entry::HashEntry, hashTable::HashTable)
              local varr::ValueArray
              local index::ModelicaInteger
              local key::Key

              (key, _) = entry
              (_, varr, _, _) = hashTable
              index = hasKeyIndex(key, hashTable)
              @match true = valueArrayKeyIndexExists(varr, index)
              valueArraySet(varr, index, entry)
        end

         #= Deletes the Value associatied with Key from the HashTable.
           Note: This function does not delete from the index table, only from the
           ValueArray. This means that a lot of deletions will not make the HashTable
           more compact, it will still contain a lot of incices information. =#
        function delete(key::Key, hashTable::HashTable)
              local indx::ModelicaInteger
              local varr::ValueArray

              indx = hasKeyIndex(key, hashTable)
              (_, varr, _, _) = hashTable
              if ! valueArrayKeyIndexExists(varr, indx)
                print("BaseHashTable.delete failed\\n")
                fail()
              end
              valueArrayClear(varr, indx)
        end

         #= checks if the given key is in the hashTable =#
        function hasKey(key::Key, hashTable::HashTable) ::Bool
              local b::Bool

              local varr::ValueArray

              (_, varr, _, _) = hashTable
              b = valueArrayKeyIndexExists(varr, hasKeyIndex(key, hashTable))
          b
        end

         #= Returns true if any of the keys are present in the hashtable. Stops and returns true upon first occurence =#
        function anyKeyInHashTable(keys::List{<:Key}, ht::HashTable) ::Bool
              local res::Bool

              for key in keys
                if hasKey(key, ht)
                  res = true
                  return res
                end
              end
              res = false
          res
        end

         #= Returns a Value given a Key and a HashTable. =#
        function get(key::Key, hashTable::HashTable) ::Value
              local value::Value

              local i::ModelicaInteger
              local varr::ValueArray

              i = hasKeyIndex(key, hashTable)
              @match false = i == (-1)
              (_, varr, _, _) = hashTable
              (_, value) = getValueArray(varr, i)
          value
        end

         #= help function to get and hasKey =#
        function hasKeyIndex(key::Key, hashTable::HashTable) ::ModelicaInteger
              local indx::ModelicaInteger

              local hashindx::ModelicaInteger
              local bsize::ModelicaInteger
              local indexes::HashNode
              local hashvec::HashVector
              local keyEqual::FuncEq
              local hashFunc::FuncHash

              (hashvec, _, bsize, (hashFunc, keyEqual, _, _)) = hashTable
              hashindx = hashFunc(key, bsize) + 1
              indexes = hashvec[hashindx]
              indx = hasKeyIndex2(key, indexes, keyEqual)
          indx
        end

         #= Helper function to get =#
        function hasKeyIndex2(key::Key, keyIndices::HashNode, keyEqual::FuncEq) ::ModelicaInteger
              local index::ModelicaInteger #= Returns -1 on failure =#

              local key2::Key

              for keyIndex in keyIndices
                (key2, index) = keyIndex
                if keyEqual(key, key2)
                  return index #= Returns -1 on failure =#
                end
              end
              index = -1 #= Mark the failure so we can do hasKey without matchcontinue =#
          index #= Returns -1 on failure =#
        end

        function dumpHashTable(t::HashTable)
              local printKey::FuncKeyString
              local printValue::FuncValString
              local k::Key
              local v::Value

              (_, _, _, (_, _, printKey, printValue)) = t
              print("HashTable:\\n")
              for entry in hashTableList(t)
                (k, v) = entry
                print("{")
                print(printKey(k))
                print(",{")
                print(printValue(v))
                print("}}\\n")
              end
        end

        function debugDump(ht::HashTable)
              local printKey::FuncKeyString
              local printValue::FuncValString
              local k::Key
              local v::Value
              local n::ModelicaInteger
              local size::ModelicaInteger
              local i::ModelicaInteger
              local j::ModelicaInteger
              local szBucket::ModelicaInteger
              local arr::Array{Option{HashEntry}}
              local he::HashEntry
              local hashVector::Array{HashNode}

              (hashVector, (n, size, arr), szBucket, (_, _, printKey, printValue)) = ht
              print("Debug HashTable:\\n")
              print("szBucket: " + intString(szBucket) + "\\n")
              print("Debug ValueArray:\\n")
              print("number of entires: " + intString(n) + "\\n")
              print("size: " + intString(size) + "\\n")
              i = 0
              for entry in arr
                i = i + 1
                if isSome(entry)
                  @match SOME(he) = entry
                  print(intString(i) + ": " + dumpTuple(he, printKey, printValue) + "\\n")
                end
              end
              print("Debug HashVector:\\n")
              i = 0
              for node in hashVector
                i = i + 1
                if ! listEmpty(node)
                  print(intString(i) + ":")
                  for n in node
                    (k, j) = n
                    print(" {" + printKey(k) + ", " + intString(j) + "}")
                  end
                  print("\\n")
                end
              end
        end

        function dumpTuple(tpl::HashEntry, printKey::FuncKeyString, printValue::FuncValString) ::String
              local str::String

              local k::Key
              local v::Value
              local sk::String
              local sv::String

              (k, v) = tpl
              sk = printKey(k)
              sv = printValue(v)
              str = stringAppendList(list("{", sk, ",{", sv, "}}"))
          str
        end

         #= Returns the Value entries as a list of Values. =#
        function hashTableValueList(hashTable::HashTable) ::List{Value}
              local valLst::List{Value}

              valLst = ListUtil.unzipSecond(hashTableList(hashTable))
          valLst
        end

         #= Returns the Key entries as a list of Keys. =#
        function hashTableKeyList(hashTable::HashTable) ::List{Key}
              local valLst::List{Key}

              valLst = ListUtil.unzipFirst(hashTableList(hashTable))
          valLst
        end

         #= Returns the entries in the hashTable as a list of HashEntries. =#
        function hashTableList(hashTable::HashTable) ::List{HashEntry}
              local outEntries::List{HashEntry}

              local varr::ValueArray

              (_, varr, _, _) = hashTable
              outEntries = valueArrayList(varr)
          outEntries
        end

         #= Returns the entries in the hashTable as a list of HashEntries, in reverse
           order. =#
        function hashTableListReversed(hashTable::HashTable) ::List{HashEntry}
              local entries::List{HashEntry}

              local varr::ValueArray

              (_, varr, _, _) = hashTable
              entries = valueArrayListReversed(varr)
          entries
        end

         #= Transforms a ValueArray to a HashEntry list. =#
        function valueArrayList(valueArray::ValueArray) ::List{HashEntry}
              local outEntries::List{HashEntry}

              local arr::Array{Option{HashEntry}}

              (_, _, arr) = valueArray
              outEntries = ArrayUtil.fold(arr, ListUtil.consOption, nil)
              outEntries = listReverse(outEntries)
          outEntries
        end

         #= Transforms a ValueArray to a HashEntry list, in reverse order compared to
           valueArrayList. =#
        function valueArrayListReversed(valueArray::ValueArray) ::List{HashEntry}
              local entries::List{HashEntry}

              local arr::Array{Option{HashEntry}}

              (_, _, arr) = valueArray
              entries = ArrayUtil.fold(arr, ListUtil.consOption, nil)
          entries
        end

         #= Returns the number of elements inserted into the table =#
        function hashTableCurrentSize(hashTable::HashTable) ::ModelicaInteger
              local sz::ModelicaInteger

              local va::ValueArray

              (_, va, _, _) = hashTable
              sz = valueArrayLength(va)
          sz
        end

         #= Returns the number of elements in the ValueArray =#
        function valueArrayLength(valueArray::ValueArray) ::ModelicaInteger
              local sz::ModelicaInteger

              (sz, _, _) = valueArray
          sz
        end

         #= Adds an entry last to the ValueArray, increasing array size if no space left
           by factor 1.4 =#
        function valueArrayAdd(valueArray::ValueArray, entry::HashEntry) ::Tuple{ValueArray, ModelicaInteger}
              local newpos::ModelicaInteger
              local outValueArray::ValueArray

              (outValueArray, newpos) = begin
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                  local expandsize::ModelicaInteger
                  local newsize::ModelicaInteger
                  local arr::Array{Option{HashEntry}}
                  local rsize::ModelicaReal
                  local rexpandsize::ModelicaReal
                @matchcontinue (valueArray, entry) begin
                  ((n, size, arr), _)  => begin
                      if !(n < size)
                        fail() #= Have space to add array elt. =#
                      end #= Have space to add array elt. =#
                      n = n + 1
                      arr = arrayUpdate(arr, n, SOME(entry))
                    ((n, size, arr), n)
                  end

                  ((n, size, arr), _)  => begin
                      if (n < size)
                        fail() #= Do NOT have space to add array elt. Expand with factor 1.4 =#
                      end #= Do NOT have space to add array elt. Expand with factor 1.4 =#
                      rsize = intReal(size)
                      rexpandsize = rsize * 0.4
                      expandsize = realInt(rexpandsize)
                      expandsize = intMax(expandsize, 1)
                      newsize = expandsize + size
                      arr = ArrayUtil.expand(expandsize, arr, NONE())
                      n = n + 1
                      arr = arrayUpdate(arr, n, SOME(entry))
                    ((n, newsize, arr), n)
                  end

                  _  => begin
                        print("-HashTable.valueArrayAdd failed\\n")
                      fail()
                  end
                end
              end
          (outValueArray, newpos)
        end

         #= Set the n:th variable in the ValueArray to value. =#
        function valueArraySet(valueArray::ValueArray, pos::ModelicaInteger, entry::HashEntry) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local arr::Array{Option{HashEntry}}
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                @matchcontinue (valueArray, pos, entry) begin
                  ((n, size, arr), _, _)  => begin
                      @match true = pos <= size
                      arr = arrayUpdate(arr, pos, SOME(entry))
                    (n, size, arr)
                  end

                  ((_, size, arr), _, _)  => begin
                      Error.addInternalError("HashTable.valueArraySet(pos=" + String(pos) + ") size=" + String(size) + " arrSize=" + String(arrayLength(arr)) + " failed\\n", sourceInfo())
                    fail()
                  end
                end
              end
          outValueArray
        end

         #= Clears the n:th variable in the ValueArray (set to NONE()). =#
        function valueArrayClear(valueArray::ValueArray, pos::ModelicaInteger)
              local arr::Array{Option{HashEntry}}
              local size::ModelicaInteger

              (_, size, arr) = valueArray
              @match true = pos <= size
               #=  TODO: Needed? arrayUpdate checks bounds and we should more reasonably check n?
               =#
              arrayUpdate(arr, pos, NONE())
        end

         #= Retrieve the n:th Value from ValueArray, index from 1..n. =#
        function getValueArray(valueArray::ValueArray, pos::ModelicaInteger) ::Tuple{Key, Value}
              local value::Value
              local key::Key

              local arr::Array{Option{HashEntry}}
              local n::ModelicaInteger

              (n, _, arr) = valueArray
              @match true = pos <= n
               #=  In case the user sends in higher values and we did not clear the array properly?
               =#
              @match SOME((key, value)) = arrayGet(arr, pos)
          (key, value)
        end

         #= Checks if the given index exists in the value array =#
        function valueArrayKeyIndexExists(valueArray::ValueArray, pos::ModelicaInteger) ::Bool
              local b::Bool

              b = begin
                  local k::Key
                  local v::Value
                  local n::ModelicaInteger
                  local arr::Array{Option{HashEntry}}
                @match (valueArray, pos) begin
                  (_, #= AbsynDumpTpl.dumpPattern: UNHANDLED Abyn.Exp  =#)  => begin
                    false
                  end

                  ((n, _, arr), _)  => begin
                    if pos <= n
                          isSome(arr[pos])
                        else
                          false
                        end
                  end
                end
              end
          b
        end

         #= Makes a copy of a hashtable. =#
        function copy(inHashTable::HashTable) ::HashTable
              local outCopy::HashTable

              local hv::HashVector
              local bs::ModelicaInteger
              local sz::ModelicaInteger
              local vs::ModelicaInteger
              local ve::ModelicaInteger
              local ft::FuncsTuple
              local vae::Array{Option{HashEntry}}

              (hv, (vs, ve, vae), bs, ft) = inHashTable
              hv = arrayCopy(hv)
              vae = arrayCopy(vae)
              outCopy = (hv, (vs, ve, vae), bs, ft)
          outCopy
        end

         #= Clears the hashtable. =#
        function clear(ht::HashTable) ::HashTable


              local hv::HashVector
              local bs::ModelicaInteger
              local sz::ModelicaInteger
              local vs::ModelicaInteger
              local ve::ModelicaInteger
              local hash_idx::ModelicaInteger
              local ft::FuncsTuple
              local hashFunc::FuncHash
              local key::Key
              local vae::Array{Option{HashEntry}}

              @match (hv, (vs, ve, vae), bs, (@match (hashFunc, _, _, _) = ft)) = ht
              for i in 1:vs
                _ = begin
                  @match arrayGet(vae, i) begin
                    SOME((key, _))  => begin
                        hash_idx = hashFunc(key, bs) + 1
                        arrayUpdate(hv, hash_idx, nil)
                        arrayUpdate(vae, i, NONE())
                      ()
                    end

                    _  => begin
                        ()
                    end
                  end
                end
              end
              ht = (hv, (0, ve, vae), bs, ft)
          ht
        end

         #= Clears a HashTable that has not been properly stored, but was known to never delete an element (making the values sequential SOME() for as long as there are elements). NOTE: Does not handle arrays that were expanded? =#
        function clearAssumeNoDelete(ht::HashTable)
              local hv::HashVector
              local bs::ModelicaInteger
              local sz::ModelicaInteger
              local vs::ModelicaInteger
              local ve::ModelicaInteger
              local hash_idx::ModelicaInteger
              local ft::FuncsTuple
              local hashFunc::FuncHash
              local key::Key
              local vae::Array{Option{HashEntry}}
              local workaroundForBug::Bool = true #= TODO: Make it impossible to update a value by not updating n (fully mutable HT instead of this hybrid) =#
              local debug::Bool = false

              @match (hv, (vs, ve, vae), bs, (@match (hashFunc, _, _, _) = ft)) = ht
              for i in 1:ve
                _ = begin
                  @match arrayGet(vae, i) begin
                    SOME((key, _))  => begin
                        if ! workaroundForBug
                          hash_idx = hashFunc(key, bs) + 1
                          arrayUpdate(hv, hash_idx, nil)
                        end
                        arrayUpdate(vae, i, NONE())
                      ()
                    end

                    _  => begin
                          if ! workaroundForBug
                            return nothing
                          end
                        ()
                    end
                  end
                end
              end
              if debug
                for i in vae
                  if isSome(i)
                    print("vae not empty\\n")
                    break
                  end
                end
              end
              if workaroundForBug
                for i in 1:arrayLength(hv)
                  if ! listEmpty(arrayGet(hv, i))
                    if debug
                      print("hv not empty\\n")
                    end
                    arrayUpdate(hv, i, nil)
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

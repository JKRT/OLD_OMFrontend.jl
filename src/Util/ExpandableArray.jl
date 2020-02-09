    #= Implementation of an expandable array

   This provides a generic implementation of an expandable array. It basically
   behaves like an ordinary array, which means all elements can get accessed via
   index. When the array runs out of space, it get automatically resized. It is
   also possible to delete an element from any position. =#

   import Setfield

   @Uniontype ExpandableArray begin
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

        @Record EXPANDABLE_ARRAY begin

                 numberOfElements #= This is an array of one Integer, to make numberOfElements mutable =#::Array{ModelicaInteger}
                 lastUsedIndex #= This is an array of one Integer, to make numberOfElements mutable =#::Array{ModelicaInteger}
                 capacity #= This is an array of one Integer, to make capacity mutable =#::Array{ModelicaInteger}
                 data #= This is an array of one array<Option<T>>, to make data mutable =#::Array{Array{Option{T}}}
        end

        import ArrayUtil
        import MetaModelica.Dangerous
        import Util

         #= O(n)
          Creates a new empty ExpandableArray with a certain capacity. =#
        function new(capacity::ModelicaInteger, dummy::T #= This is needed to determine the type information, the actual value is not used =#) ::ExpandableArray{T}
              local exarray::ExpandableArray{T}

              exarray = EXPANDABLE_ARRAY(arrayCreate(1, 0), arrayCreate(1, 0), arrayCreate(1, capacity), arrayCreate(1, arrayCreate(capacity, NONE())))
          exarray
        end

         #= O(n)
          Deletes all elements. =#
        function clear(exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local n::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              Dangerous.arrayUpdateNoBoundsChecking(exarray.numberOfElements, 1, 0)
              Dangerous.arrayUpdateNoBoundsChecking(exarray.lastUsedIndex, 1, 0)
              for i in 1:lastUsedIndex
                if isSome(Dangerous.arrayGetNoBoundsChecking(data, i))
                  n = n - 1
                  Dangerous.arrayUpdateNoBoundsChecking(data, i, NONE())
                  if n == 0
                    return exarray
                  end
                end
              end
          exarray
        end

        function copy(inExarray::ExpandableArray{<:T}, dummy::T #= This is needed to determine the type information, the actual value is not used =#) ::ExpandableArray{T}
              local outExarray::ExpandableArray{T}

              outExarray = new(inExarray.capacity[1], dummy)
              Setfield.@set outExarray.numberOfElements = arrayCopy(inExarray.numberOfElements)
              Setfield.@set outExarray.lastUsedIndex = arrayCopy(inExarray.lastUsedIndex)
              Setfield.@set outExarray.capacity = arrayCopy(inExarray.capacity)
              Setfield.@set outExarray.data = arrayCreate(1, arrayCopy(Dangerous.arrayGetNoBoundsChecking(inExarray.data, 1)))
          outExarray
        end

         #= O(1)
          Returns if the element at the given index is occupied or not. =#
        function occupied(index::ModelicaInteger, exarray::ExpandableArray{<:T}) ::Bool
              local b::Bool

              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              b = index >= 1 && index <= lastUsedIndex && isSome(Dangerous.arrayGetNoBoundsChecking(data, index))
          b
        end

         #= O(1)
          Returns the value of the element at the given index.
          Fails if there is nothing assigned to the given index. =#
        function get(index::ModelicaInteger, exarray::ExpandableArray{<:T}) ::T
              local value::T

              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if occupied(index, exarray)
                @match SOME(value) = Dangerous.arrayGetNoBoundsChecking(data, index)
              else
                fail()
              end
          value
        end

         #= O(n)
          Expands an array to the given size, or does nothing if the array is already
          large enough. =#
        function expandToSize(minCapacity::ModelicaInteger, exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local capacity::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.capacity, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if minCapacity > capacity
                Dangerous.arrayUpdateNoBoundsChecking(exarray.capacity, 1, minCapacity)
                data = ArrayUtil.expandToSize(minCapacity, data, NONE())
                Dangerous.arrayUpdateNoBoundsChecking(exarray.data, 1, data)
              end
          exarray
        end

         #= if index <= capacity then O(1) otherwise O(n)
          Sets the element at the given index to the given value.
          Fails if the index is already used. =#
        function set(index::ModelicaInteger, value::T, exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local capacity::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.capacity, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if index > 0 && (index > capacity || isNone(Dangerous.arrayGetNoBoundsChecking(data, index)))
                if index > capacity
                  expandToSize(index, exarray)
                  data = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)
                end
                arrayUpdate(data, index, SOME(value))
                Dangerous.arrayUpdateNoBoundsChecking(exarray.numberOfElements, 1, numberOfElements + 1)
                if index > lastUsedIndex
                  Dangerous.arrayUpdateNoBoundsChecking(exarray.lastUsedIndex, 1, index)
                end
              else
                fail()
              end
          exarray
        end

         #= if index <= capacity then O(1) otherwise O(n)
          Sets the first unused element to the given value. =#
        function add(value::T, exarray::ExpandableArray{<:T}) ::Tuple{ExpandableArray{T}, ModelicaInteger}
              local index::ModelicaInteger


              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)

              index = lastUsedIndex + 1
              exarray = set(index, value, exarray)
          (exarray, index)
        end

         #= O(1)
          Deletes the value of the element at the given index.
          Fails if there is no value stored at the given index. =#
        function delete(index::ModelicaInteger, exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if index >= 1 && index <= lastUsedIndex && isSome(Dangerous.arrayGetNoBoundsChecking(data, index))
                arrayUpdate(data, index, NONE())
                Dangerous.arrayUpdateNoBoundsChecking(exarray.numberOfElements, 1, numberOfElements - 1)
                if index == lastUsedIndex
                  lastUsedIndex = lastUsedIndex - 1
                  while lastUsedIndex > 0 && isNone(Dangerous.arrayGetNoBoundsChecking(data, lastUsedIndex))
                    lastUsedIndex = lastUsedIndex - 1
                  end
                  Dangerous.arrayUpdateNoBoundsChecking(exarray.lastUsedIndex, 1, lastUsedIndex)
                end
              else
                fail()
              end
          exarray
        end

         #= O(1)
          Overrides the value of the element at the given index.
          Fails if there is no value stored at the given index. =#
        function update(index::ModelicaInteger, value::T, exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if index >= 1 && index <= lastUsedIndex && isSome(Dangerous.arrayGetNoBoundsChecking(data, index))
                arrayUpdate(data, index, SOME(value))
              else
                fail()
              end
          exarray
        end

        function toList(exarray::ExpandableArray{<:T}) ::List{T}
              local listT::List{T}

              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local capacity::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.capacity, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              if numberOfElements == 0
                listT = nil
              elseif capacity == 1
                listT = list(Util.getOption(data[1]))
              else
                listT = list(Util.getOption(data[i]) for i in 1:capacity if isSome(data[i]))
              end
          listT
        end

         #= O(n)
          Reorders the elements in order to remove all the gaps.
          Be careful: This changes the indices of the elements. =#
        function compress(exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)
              local i::ModelicaInteger = 0

              while lastUsedIndex > numberOfElements
                i = i + 1
                if isNone(Dangerous.arrayGetNoBoundsChecking(data, i))
                  Dangerous.arrayUpdateNoBoundsChecking(data, i, Dangerous.arrayGetNoBoundsChecking(data, lastUsedIndex))
                  Dangerous.arrayUpdateNoBoundsChecking(data, lastUsedIndex, NONE())
                  lastUsedIndex = lastUsedIndex - 1
                  while isNone(Dangerous.arrayGetNoBoundsChecking(data, lastUsedIndex))
                    lastUsedIndex = lastUsedIndex - 1
                  end
                end
              end
              Dangerous.arrayUpdateNoBoundsChecking(exarray.lastUsedIndex, 1, lastUsedIndex)
          exarray
        end

         #= O(n)
          Reduces the capacity of the ExpandableArray to the number of elements.
          Be careful: This may change the indices of the elements. =#
        function shrink(exarray::ExpandableArray{<:T}) ::ExpandableArray{T}


              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)
              local newData::Array{Option{T}}

              exarray = compress(exarray)
              Dangerous.arrayUpdateNoBoundsChecking(exarray.capacity, 1, numberOfElements)
              newData = Dangerous.arrayCreateNoInit(numberOfElements, Dangerous.arrayGetNoBoundsChecking(data, 1))
              for i in 1:numberOfElements
                Dangerous.arrayUpdateNoBoundsChecking(newData, i, Dangerous.arrayGetNoBoundsChecking(data, i))
              end
              Dangerous.arrayUpdateNoBoundsChecking(exarray.data, 1, newData)
          exarray
        end

         #= O(n)
          Dumps all elements with the given print function. =#
        function dump(exarray::ExpandableArray{<:T}, header::String, func::PrintFunction)
              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
              local capacity::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.capacity, 1)
              local value::T
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)

              print(header + " (" + intString(numberOfElements) + "/" + intString(capacity) + ")\\n")
              print("========================================\\n")
              if numberOfElements == 0
                print("<empty>\\n")
              else
                for i in 1:capacity
                  if isSome(Dangerous.arrayGetNoBoundsChecking(data, i))
                    @match SOME(value) = Dangerous.arrayGetNoBoundsChecking(data, i)
                    numberOfElements = numberOfElements - 1
                    print(intString(i) + ": " + func(value) + "\\n")
                    if numberOfElements == 0
                      return
                    end
                  end
                end
              end
        end

        function getNumberOfElements(exarray::ExpandableArray{<:T}) ::ModelicaInteger
              local numberOfElements::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.numberOfElements, 1)
          numberOfElements
        end

        function getLastUsedIndex(exarray::ExpandableArray{<:T}) ::ModelicaInteger
              local lastUsedIndex::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.lastUsedIndex, 1)
          lastUsedIndex
        end

        function getCapacity(exarray::ExpandableArray{<:T}) ::ModelicaInteger
              local capacity::ModelicaInteger = Dangerous.arrayGetNoBoundsChecking(exarray.capacity, 1)
          capacity
        end

        function getData(exarray::ExpandableArray{<:T}) ::Array{Option{T}}
              local data::Array{Option{T}} = Dangerous.arrayGetNoBoundsChecking(exarray.data, 1)
          data
        end
   end

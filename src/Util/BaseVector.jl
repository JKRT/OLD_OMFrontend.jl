  #=TODO: Originally partial =# module BaseVector


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    using Setfield

    @UniontypeDecl VectorInternal

    MapFunc = Function

    FoldFunc = Function

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
        T = ModelicaInteger
         #=  Should be Any.
         =#
         const defaultValue::T
         const growthFactor = 2::ModelicaReal
         const freePolicy = FreePolicy.ON_DELETION::FreePolicy


        import MetaModelica.Dangerous

         #=  The Vector type is an array of one VectorInternal, to make it completely mutable.
         =#
        Vector = Array

         @Uniontype VectorInternal begin
              @Record VECTOR begin

                       data::Array{T}
                       size #= The number of stored elements. =#::ModelicaInteger
                       capacity #= The number of elements that can be stored. =#::ModelicaInteger
              end
         end

         #= Creates a new empty Vector with a certain capacity. =#
        function new(inSize::ModelicaInteger = 1) ::Vector
              local outVector::Vector

              local data::Array{T}

              assert(growthFactor > 1.0, "growthFactor must be larger than 1")
              data = Dangerous.arrayCreateNoInit(inSize, defaultValue)
              outVector = arrayCreate(1, VECTOR(data, 0, inSize))
          outVector
        end

         #= Creates a new Vector filled with the given value. =#
        function newFill(inSize::ModelicaInteger, inFillValue::T) ::Vector
              local outVector::Vector

              local data::Array{T}

              assert(growthFactor > 1.0, "growthFactor must be larger than 1")
              data = arrayCreate(inSize, inFillValue)
              outVector = arrayCreate(1, VECTOR(data, inSize, inSize))
          outVector
        end

         #= Appends a value to the end of the Vector. =#
        function add(inVector::Vector, inValue::T)
              local vec::VectorInternal = inVector[1]
              local capacity::ModelicaInteger

              @set vec.size = vec.size + 1
              if vec.size > vec.capacity
                @set vec.capacity = integer(ceil(intReal(vec.capacity) * growthFactor))
                @set vec.data = copyArray(vec.data, vec.capacity)
              end
              Dangerous.arrayUpdateNoBoundsChecking(vec.data, vec.size, inValue)
              Dangerous.arrayUpdateNoBoundsChecking(inVector, 1, vec)
        end

         #= Removes the last element in the Vector. =#
        function pop(inVector::Vector)
              local vec::VectorInternal = inVector[1]

              if freePolicy == FreePolicy.ON_DELETION
                arrayUpdate(vec.data, vec.size, defaultValue)
              end
              @set vec.size = max(vec.size - 1, 0)
              Dangerous.arrayUpdateNoBoundsChecking(inVector, 1, vec)
        end

         #= Sets the element at the given index to the given value. Fails if the index is
           out of bounds. =#
        function set(inVector::Vector, inIndex::ModelicaInteger, inValue::T)
              local vec::VectorInternal = inVector[1]

              if inIndex > 0 && inIndex <= vec.size
                Dangerous.arrayUpdateNoBoundsChecking(vec.data, inIndex, inValue)
              else
                fail()
              end
        end

         #= Returns the value of the element at the given index. Fails if the index is
           out of bounds. =#
        function get(inVector::Vector, inIndex::ModelicaInteger) ::T
              local outValue::T

              local vec::VectorInternal = inVector[1]

              if inIndex > 0 && inIndex <= vec.size
                outValue = Dangerous.arrayGetNoBoundsChecking(vec.data, inIndex)
              else
                fail()
              end
          outValue
        end

        function last(inVector::Vector) ::T
              local outValue::T

              local vec::VectorInternal = inVector[1]

              if vec.size > 0
                outValue = vec.data[vec.size]
              else
                fail()
              end
          outValue
        end

         #= Returns the number of elements in the Vector. =#
        function size(inVector::Vector) ::ModelicaInteger
              local outSize::ModelicaInteger = inVector.size
          outSize
        end

         #=  Alias for size, since size can't be used inside this package (the compiler
         =#
         #=  mistakes it for the builtin size).
         =#
          @ExtendedFunction length size()

         #= Return the number of elements the Vector can store without having to allocate
           more memory. =#
        function capacity(inVector::Vector) ::ModelicaInteger
              local outCapacity::ModelicaInteger = inVector.capacity
          outCapacity
        end

         #= Returns true if the Vector is empty, otherwise false. =#
        function isEmpty(inVector::Vector) ::Bool
              local outIsEmpty::Bool = inVector.size == 0
          outIsEmpty
        end

         #= Increases the capacity of the Vector to the given amount of elements.
           Does nothing if the Vector's capacity is already large enough. =#
        function reserve(inVector::Vector, inSize::ModelicaInteger)
              local vec::VectorInternal = inVector[1]

              if inSize > vec.capacity
                @set vec.data = copyArray(vec.data, inSize)
                @set vec.capacity = inSize
                Dangerous.arrayUpdateNoBoundsChecking(inVector, 1, vec)
              end
        end

         #= Resizes the Vector. If the new size is larger than the previous size, then
           new elements will be added to the Vector until it reaches the given size.
           This can trigger a reallocation. If the new size is smaller than the previous
           size, then the Vector is shrunk to the given size. This only shrinks the size
           of the Vector, not its capacity. =#
        function resize(inVector::Vector, inNewSize::ModelicaInteger, inFillValue::T = defaultValue)
              local vec::VectorInternal = inVector[1]

              if inNewSize <= 0
                fail()
              elseif inNewSize > vec.size
                if inNewSize > vec.capacity
                  @set vec.data = copyArray(vec.data, inNewSize)
                  @set vec.capacity = inNewSize
                end
                fillArray(vec.data, inFillValue, vec.size + 1, inNewSize)
              elseif freePolicy == FreePolicy.ON_DELETION
                fillArray(vec.data, defaultValue, inNewSize + 1, vec.capacity)
              end
               #=  Increase the capacity if the new size is larger than the capacity.
               =#
               #=  Fill the space between the last element and the new end of the array.
               =#
              @set vec.size = inNewSize
              Dangerous.arrayUpdateNoBoundsChecking(inVector, 1, vec)
        end

         #= Shrinks the capacity of the Vector to the actual number of elements it
           contains. To avoid a costly reallocation when the memory gain would be small
           this is only done when the size is smaller than the capacity by a certain
           threshold. The default threshold is 0.9, i.e. the Vector is only trimmed if
           it's less than 90% full. =#
        function trim(inVector::Vector, inThreshold::ModelicaReal = 0.9)
              local vec::VectorInternal = inVector[1]

              if vec.size < integer(intReal(vec.capacity) * inThreshold)
                @set vec.data = copyArray(vec.data, vec.size)
                @set vec.capacity = vec.size
                Dangerous.arrayUpdateNoBoundsChecking(inVector, 1, vec)
              end
        end

         #= Fills the given interval with the given value. Fails if the start or end
           position is out of bounds. Does nothing if start is larger than end. =#
        function fill(inVector::Vector, inFillValue::T, inStart::ModelicaInteger = 1, inEnd::ModelicaInteger = length(inVector))
              local vec::VectorInternal = inVector[1]

              if inStart < 1 || inEnd < 1 || inEnd > length(inVector)
                fail()
              end
              fillArray(vec.data, inFillValue, inStart, inEnd)
        end

         #= Creates a Vector from a list. =#
        function fromList(inList::List{<:T}) ::Vector
              local outVector::Vector = fromArray(listArray(inList))
          outVector
        end

         #= Converts a Vector to a list. =#
        function toList(inVector::Vector) ::List{T}
              local outList::List{T}

              local data::Array{T}
              local sz::ModelicaInteger
              local capacity::ModelicaInteger

              @match VECTOR(data = data, size = sz, capacity = capacity) = inVector[1]
              if sz == capacity
                outList = arrayList(data)
              else
                outList = list(data[i] for i in 1:sz)
              end
               #=  If Vector is filled to capacity, convert the whole array to a list.
               =#
               #=  Otherwise, make a list of only the stored elements.
               =#
          outList
        end

         #= Creates a Vector from an array. The array is copied, so changes to the
           Vector's internal array will not affect the given array. =#
        function fromArray(inArray::Array{<:T}) ::Vector
              local outVector::Vector

              local sz::ModelicaInteger = arrayLength(inArray)

              outVector = arrayCreate(1, VECTOR(arrayCopy(inArray), sz, sz))
          outVector
        end

         #= Converts a Vector to an array. This makes a copy of the Vector's internal
           array, so changing the returned array will not affect the Vector. =#
        function toArray(inVector::Vector) ::Array{T}
              local outArray::Array{T}

              local data::Array{T}
              local sz::ModelicaInteger
              local capacity::ModelicaInteger

              @match VECTOR(data = data, size = sz, capacity = capacity) = inVector[1]
              if sz == capacity
                outArray = arrayCopy(data)
              else
                outArray = Dangerous.arrayCreateNoInit(sz, defaultValue)
                for i in 1:sz
                  Dangerous.arrayUpdateNoBoundsChecking(outArray, i, Dangerous.arrayGetNoBoundsChecking(data, i))
                end
              end
               #=  If Vector is filled to capacity, make a copy of the internal array.
               =#
               #=  Otherwise, make a new array and copy all stored elements from the
               =#
               #=  internal array to it.
               =#
          outArray
        end

         #= Applies the given function to each element in the Vector, changing each
           element's value to the result of the call. =#
        function map(inVector::Vector, inFunc::MapFunc)
              local data::Array{T}
              local sz::ModelicaInteger
              local old_val::T
              local new_val::T

              @match VECTOR(data = data, size = sz) = inVector[1]
              for i in 1:sz
                old_val = data[i]
                new_val = inFunc(old_val)
                if ! referenceEq(old_val, new_val)
                  Dangerous.arrayUpdateNoBoundsChecking(data, i, new_val)
                end
              end
        end

         #= Applies the given function to each element in the Vector, updating the given
           argument as it goes along. =#
        function fold(inVector::Vector, inFunc::FoldFunc, inStartValue::FT)  where {FT}
              local outResult::FT = inStartValue

              local data::Array{T}
              local sz::ModelicaInteger

              @match VECTOR(data = data, size = sz) = inVector[1]
              for i in 1:sz
                outResult = inFunc(data[i], outResult)
              end
          outResult
        end

         #= Creates a clone of the given Vector. =#
        function clone(inVector::Vector) ::Vector
              local outVector::Vector

              local vec::VectorInternal = inVector[1]

              @set vec.data = arrayCopy(vec.data)
              outVector = arrayCreate(1, vec)
          outVector
        end

         #= Allocates a new array with the given size, and copies elements from the given
           array to the new array until either all elements have been copied or the new
           array has been filled. =#
        function copyArray(inArray::Array{<:T}, inNewSize::ModelicaInteger) ::Array{T}
              local outArray::Array{T}

              outArray = Dangerous.arrayCreateNoInit(inNewSize, defaultValue)
              for i in 1:min(inNewSize, arrayLength(inArray))
                Dangerous.arrayUpdateNoBoundsChecking(outArray, i, Dangerous.arrayGetNoBoundsChecking(inArray, i))
              end
          outArray
        end

         #= Fills an array with the given value. =#
        function fillArray(inArray::Array{<:T}, inValue::T, inStart::ModelicaInteger, inEnd::ModelicaInteger)
              for i in inStart:inEnd
                Dangerous.arrayUpdateNoBoundsChecking(inArray, i, inValue)
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

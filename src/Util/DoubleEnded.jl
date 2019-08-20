  module DoubleEnded 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl MutableList 

    MapFunc = Function

    MapFunc = Function

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

        import MutableType

         @Uniontype MutableList begin
              @Record LIST begin

                       length::MutableType{ModelicaInteger}
                       front::MutableType{List{T}}
                       back::MutableType{List{T}}
              end
         end

        import GC
        import MetaModelica.Dangerous

        function new(first::T)  where {T}
              local delst::MutableList{T}

              local lst::List{T} = list(first)

              delst = LIST(Mutable.create(1), Mutable.create(lst), Mutable.create(lst))
          delst
        end

        function fromList(lst::List{T})  where {T}
              local delst::MutableList{T}

              local head::List{T}
              local tail::List{T}
              local tmp::List{T}
              local length::ModelicaInteger
              local t::T

              if listEmpty(lst)
                delst = LIST(Mutable.create(0), Mutable.create(nil), Mutable.create(nil))
                return delst
              end
              @match _cons(t, tmp) = lst
              head = list(t)
              tail = head
              length = 1
              for l in tmp
                tmp = list(l)
                Dangerous.listSetRest(tail, tmp)
                tail = tmp
                length = length + 1
              end
              delst = LIST(Mutable.create(length), Mutable.create(head), Mutable.create(tail))
          delst
        end

        function empty(dummy::T)  where {T}
              local delst::MutableList{T}

              delst = LIST(Mutable.create(0), Mutable.create(nil), Mutable.create(nil))
          delst
        end

        function length(delst::MutableList{T})  where {T}
              local length::ModelicaInteger

              length = Mutable.access(delst.length)
          length
        end

        function pop_front(delst::MutableList{T})  where {T}
              local elt::T

              local length::ModelicaInteger = Mutable.access(delst.length)
              local lst::List{T}

              @match true = length > 0
              Mutable.update(delst.length, length - 1)
              if length == 1
                Mutable.update(delst.front, nil)
                Mutable.update(delst.back, nil)
                return elt
              end
              @match _cons(elt, lst) = Mutable.access(delst.front)
              Mutable.update(delst.front, lst)
          elt
        end

        function currentBackCell(delst::MutableList{T})  where {T}
              local last::List{T}

              last = Mutable.access(delst.back)
          last
        end

        function push_front(delst::MutableList{T}, elt::T)  where {T}
              local length::ModelicaInteger = Mutable.access(delst.length)
              local lst::List{T}

              Mutable.update(delst.length, length + 1)
              if length == 0
                lst = list(elt)
                Mutable.update(delst.front, lst)
                Mutable.update(delst.back, lst)
                return 
              end
              lst = Mutable.access(delst.front)
              Mutable.update(delst.front, _cons(elt, lst))
        end

        function push_list_front(delst::MutableList{T}, lst::List{T})  where {T}
              local length::ModelicaInteger = Mutable.access(delst.length)
              local lstLength::ModelicaInteger
              local work::List{T}
              local oldHead::List{T}
              local tmp::List{T}
              local head::List{T}
              local t::T

              lstLength = listLength(lst)
              if lstLength == 0
                return 
              end
              Mutable.update(delst.length, length + lstLength)
              @match _cons(t, tmp) = lst
              head = list(t)
              oldHead = Mutable.access(delst.front)
              Mutable.update(delst.front, head)
              for l in tmp
                work = list(l)
                Dangerous.listSetRest(head, work)
                head = work
              end
              if length == 0
                Mutable.update(delst.back, head)
              else
                Dangerous.listSetRest(head, oldHead)
              end
        end

        function push_back(delst::MutableList{T}, elt::T)  where {T}
              local length::ModelicaInteger = Mutable.access(delst.length)
              local lst::List{T}

              Mutable.update(delst.length, length + 1)
              if length == 0
                lst = list(elt)
                Mutable.update(delst.front, lst)
                Mutable.update(delst.back, lst)
                return 
              end
              lst = list(elt)
              Dangerous.listSetRest(Mutable.access(delst.back), lst)
              Mutable.update(delst.back, lst)
        end

        function push_list_back(delst::MutableList{T}, lst::List{T})  where {T}
              local length::ModelicaInteger = Mutable.access(delst.length)
              local lstLength::ModelicaInteger
              local tail::List{T}
              local tmp::List{T}
              local t::T

              lstLength = listLength(lst)
              if lstLength == 0
                return 
              end
              Mutable.update(delst.length, length + lstLength)
              t = listGet(lst, 1)
              tmp = list(t)
              if length == 0
                Mutable.update(delst.front, tmp)
              else
                Dangerous.listSetRest(Mutable.access(delst.back), tmp)
              end
              tail = tmp
              for l in listRest(lst)
                tmp = list(l)
                Dangerous.listSetRest(tail, tmp)
                tail = tmp
              end
              Mutable.update(delst.back, tail)
        end

        function toListAndClear(delst::MutableList{T}, prependToList::List{T} = nil)  where {T}
              local res::List{T}

              if Mutable.access(delst.length) == 0
                res = prependToList
                return res
              end
              res = Mutable.access(delst.front)
              if ! listEmpty(prependToList)
                Dangerous.listSetRest(Mutable.access(delst.back), prependToList)
              end
              Mutable.update(delst.back, nil)
              Mutable.update(delst.front, nil)
              Mutable.update(delst.length, 0)
          res
        end

         #= Returns the working list, which may be changed later on! =#
        function toListNoCopyNoClear(delst::MutableList{T})  where {T}
              local res::List{T}

              res = Mutable.access(delst.front)
          res
        end

        function clear(delst::MutableList{T})  where {T}
              local lst::List{T}

              lst = Mutable.access(delst.front)
              Mutable.update(delst.back, nil)
              Mutable.update(delst.front, nil)
              Mutable.update(delst.length, 0)
              for l in lst
                GC.free(l)
              end
        end

        function mapNoCopy_1(delst::MutableList{T}, inMapFunc::MapFunc, inArg1::ArgT1)  where {T, ArgT1}
              local lst::List{T} = Mutable.access(delst.front)

              while ! listEmpty(lst)
                Dangerous.listSetFirst(lst, inMapFunc(listGet(lst, 1), inArg1))
                @match _cons(_, lst) = lst
              end
        end

        function mapFoldNoCopy(delst::MutableList{T}, inMapFunc::MapFunc, arg::ArgT1)  where {T, ArgT1}


              local element::T
              local lst::List{T} = Mutable.access(delst.front)

              while ! listEmpty(lst)
                (element, arg) = inMapFunc(listGet(lst, 1), arg)
                Dangerous.listSetFirst(lst, element)
                @match _cons(_, lst) = lst
              end
          arg
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
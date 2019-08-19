  module JSONExt 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

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

         #= @author: adrpo
         this function will serialize anything you give it in JSON format
         and will filter out any with the names given in the filter =#
        function serialize(any::T, filter::List{String})  where {T}
              local s::String = ""

              local name::String
              local components::List{String}
              local lst::List{String}
              local no::ModelicaInteger = 1

              if isInteger(any)
                s = intString(getInteger(any))
                return s
              end
              if isReal(any)
                s = realString(getReal(any))
                return s
              end
              if isString(any)
                s = "\\" + getString(any) + "\\"
                return s
              end
              if isRecord(any)
                components = getRecordNames(any)
                @match _cons(name, components) = components
                s = "{\\" + name + "\\:{"
                no = 1
                lst = nil
                for c in components
                  if ! listMember(c, filter)
                    lst = _cons("\\" + c + "\\:" + serialize(getRecordComponent(any, no), filter), lst)
                  end
                  no = no + 1
                end
                lst = listReverse(lst)
                s = s + stringDelimitList(lst, ",") + "}}"
                return s
              end
               #=  get the records and the component names
               =#
               #=  if is not in the filter output it
               =#
              if isNil(any)
                s = "[]"
                return s
              end
              if isCons(any)
                s = s + "["
                no = 1
                lst = nil
                for c in getList(any)
                  lst = _cons(serialize(c, filter), lst)
                end
                lst = listReverse(lst)
                s = s + stringDelimitList(lst, ",") + "]"
                return s
              end
              if isNONE(any)
                s = s + "[]"
                return s
              end
              if isSOME(any)
                s = s + "[" + serialize(getSome(any), filter) + "]"
                return s
              end
              if isTuple(any)
                s = s + "{\\Tuple\\:{"
                no = 1
                lst = nil
                for i in 1:getTupleSize(any)
                  lst = _cons("\\" + intString(i) + "\\:" + serialize(getListElement(any, no), filter), lst)
                end
                lst = listReverse(lst)
                s = s + stringDelimitList(lst, ",") + "}} "
                return s
              end
              s = "UNKNOWN(" + anyString(any) + ")"
          s
        end

        function isInteger(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isReal(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isString(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isArray(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isRecord(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isTuple(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isNONE(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isSOME(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isNil(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function isCons(any::T)  where {T}
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function getRecordNames(any::T)  where {T}
              local nameAndComponentsNames::List{String} = listReverse(getRecordNamesHelper(any))
          nameAndComponentsNames
        end

        function getRecordNamesHelper(any::T)  where {T}
              local nameAndComponentsNames::List{String}

            #= TODO: Defined in the runtime =#
          nameAndComponentsNames
        end

        function getRecordComponent(iany::TIN, offset::ModelicaInteger)  where {TIN, TOUT}
              local oany::TOUT

            #= TODO: Defined in the runtime =#
          oany
        end

        function getInteger(a::T)  where {T}
              local i::ModelicaInteger

            #= TODO: Defined in the runtime =#
          i
        end

        function getReal(a::T)  where {T}
              local r::ModelicaReal

            #= TODO: Defined in the runtime =#
          r
        end

        function getString(a::T)  where {T}
              local s::String

            #= TODO: Defined in the runtime =#
          s
        end

        function getSome(a::TIN)  where {TIN, TOUT}
              local o::TOUT

            #= TODO: Defined in the runtime =#
          o
        end

        function getTupleSize(any::T)  where {T}
              local sz::ModelicaInteger

            #= TODO: Defined in the runtime =#
          sz
        end

        function getList(iany::TIN)  where {TIN, TOUT}
              local oany::List{TOUT}

            #= TODO: Defined in the runtime =#
          oany
        end

        function getListElement(iany::TIN, offset::ModelicaInteger)  where {TIN, TOUT}
              local oany::TOUT

            #= TODO: Defined in the runtime =#
          oany
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
  module NFInstDump 


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
         #= public import NFConnect2;
         =#

        import NFInstTypes

        import NFInstDumpTpl

        import ListUtil

        import Tpl

        function modelStr(inName::String, inClass::NFInstTypes.Class) ::String 
              local outString::String

              outString = Tpl.tplString2(NFInstDumpTpl.dumpModel, inName, inClass)
          outString
        end

        function elementStr(inElement::NFInstTypes.Element) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpElement, inElement)
          outString
        end

        function componentStr(inComponent::NFInstTypes.Component) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpComponent, inComponent)
          outString
        end

        function bindingStr(inBinding::NFInstTypes.Binding) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpBinding, inBinding)
          outString
        end

        function prefixStr(inPrefix::NFInstTypes.Prefix) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpPrefix, inPrefix)
          outString
        end

        function equationStr(inEquation::NFInstTypes.Equation) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpEquation, inEquation)
          outString
        end

         #= public function connectionsStr
         =#
         #=   input NFConnect2.Connections inConnections;
         =#
         #=   output String outString;
         =#
         #= algorithm
         =#
         #=   outString := Tpl.tplString(NFInstDumpTpl.dumpConnections, inConnections);
         =#
         #= end connectionsStr;
         =#

        function dimensionStr(inDimension::NFInstTypes.Dimension) ::String 
              local outString::String

              outString = Tpl.tplString(NFInstDumpTpl.dumpDimension, inDimension)
          outString
        end

        function dumpUntypedComponentDims(inComponent::NFInstTypes.Component) ::String 
              local outString::String

              outString = begin
                  local adims::Array{NFInstTypes.Dimension}
                  local ldims::List{NFInstTypes.Dimension}
                  local dims_str::String
                @match inComponent begin
                  NFInstTypes.UNTYPED_COMPONENT(dimensions = adims)  => begin
                      ldims = arrayList(adims)
                      dims_str = ListUtil.toString(ldims, dimensionStr, "", "[", ", ", "]", false)
                    dims_str
                  end
                end
              end
          outString
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
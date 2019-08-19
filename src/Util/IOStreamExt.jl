  module IOStreamExt 


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

        function createFile(fileName::String) ::ModelicaInteger 
              local fileID::ModelicaInteger

            #= TODO: Defined in the runtime =#
          fileID
        end

        function closeFile(fileID::ModelicaInteger)  
            #= TODO: Defined in the runtime =#
        end

        function deleteFile(fileID::ModelicaInteger)  
            #= TODO: Defined in the runtime =#
        end

        function clearFile(fileID::ModelicaInteger)  
            #= TODO: Defined in the runtime =#
        end

        function appendFile(fileID::ModelicaInteger, inString::String)  
            #= TODO: Defined in the runtime =#
        end

        function readFile(fileID::ModelicaInteger) ::String 
              local outString::String

            #= TODO: Defined in the runtime =#
          outString
        end

        function printFile(fileID::ModelicaInteger, whereToPrint::ModelicaInteger #= stdout:1, stderr:2 =#)  
            #= TODO: Defined in the runtime =#
        end

        function createBuffer() ::ModelicaInteger 
              local bufferID::ModelicaInteger

            #= TODO: Defined in the runtime =#
          bufferID
        end

        function appendBuffer(bufferID::ModelicaInteger, inString::String)  
            #= TODO: Defined in the runtime =#
        end

        function deleteBuffer(bufferID::ModelicaInteger)  
            #= TODO: Defined in the runtime =#
        end

        function clearBuffer(bufferID::ModelicaInteger)  
            #= TODO: Defined in the runtime =#
        end

        function readBuffer(bufferID::ModelicaInteger) ::String 
              local outString::String

            #= TODO: Defined in the runtime =#
          outString
        end

        function printBuffer(bufferID::ModelicaInteger, whereToPrint::ModelicaInteger #= stdout:1, stderr:2 =#)  
            #= TODO: Defined in the runtime =#
        end

        function appendReversedList(inStringLst::List{<:String}) ::String 
              local outString::String

            #= TODO: Defined in the runtime =#
          outString
        end

        function printReversedList(inStringLst::List{<:String}, whereToPrint::ModelicaInteger #= stdout:1, stderr:2 =#)  
            #= TODO: Defined in the runtime =#
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
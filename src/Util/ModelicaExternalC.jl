  module ModelicaExternalC 


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

        function Streams_print(string::String, fileName::String)  
            #= TODO: Defined in the runtime =#
        end

        function Streams_readLine(fileName::String, lineNumber::ModelicaInteger) ::Tuple{String, Bool} 
              local endOfFile::Bool
              local string::String

            #= TODO: Defined in the runtime =#
          (string, endOfFile)
        end

        function Streams_countLines(fileName::String) ::ModelicaInteger 
              local numberOfLines::ModelicaInteger

            #= TODO: Defined in the runtime =#
          numberOfLines
        end

        function File_fullPathName(fileName::String) ::String 
              local outName::String

            #= TODO: Defined in the runtime =#
          outName
        end

        function File_stat(name::String) ::ModelicaInteger 
              local fileType::ModelicaInteger

            #= TODO: Defined in the runtime =#
          fileType
        end

        function Streams_close(fileName::String)  
            #= TODO: Defined in the runtime =#
        end

        function Strings_compare(string1::String, string2::String, caseSensitive::Bool) ::ModelicaInteger 
              local result::ModelicaInteger

            #= TODO: Defined in the runtime =#
          result
        end

        function Strings_advanced_scanReal(string::String, startIndex::ModelicaInteger, unsigned::Bool) ::Tuple{ModelicaInteger, ModelicaReal} 
              local number::ModelicaReal
              local nextIndex::ModelicaInteger

            #= TODO: Defined in the runtime =#
          (nextIndex, number)
        end

        function Strings_advanced_skipWhiteSpace(string::String, startIndex::ModelicaInteger(min = 1) = 1) ::ModelicaInteger 
              local nextIndex::ModelicaInteger

            #= TODO: Defined in the runtime =#
          nextIndex
        end

        function ModelicaIO_readMatrixSizes(fileName::String, matrixName::String) ::ModelicaInteger 
              local dim::ModelicaInteger

            #= TODO: Defined in the runtime =#
          dim
        end

        function ModelicaIO_readRealMatrix(fileName::String, matrixName::String, nrow::ModelicaInteger, ncol::ModelicaInteger, verboseRead::Bool = true) ::ModelicaReal 
              local matrix::ModelicaReal

            #= TODO: Defined in the runtime =#
          matrix
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
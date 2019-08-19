  module IOStream 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl IOStreamType 
    @UniontypeDecl IOStreamData 
    @UniontypeDecl IOStream 

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

          #= TODO! change these to X_TYPE =#
         @Uniontype IOStreamType begin
              @Record FILE begin

                       name::String
              end

              @Record LIST begin

              end

              @Record BUFFER begin

              end
         end

         @Uniontype IOStreamData begin
              @Record FILE_DATA begin

                       data::ModelicaInteger
              end

              @Record LIST_DATA begin

                       data::List{String}
              end

              @Record BUFFER_DATA begin

                       data::ModelicaInteger
              end
         end

         @Uniontype IOStream begin
              @Record IOSTREAM begin

                       name::String
                       ty::IOStreamType
                       data::IOStreamData
              end
         end

         const stdInput = 0::ModelicaInteger
         const stdOutput = 1::ModelicaInteger
         const stdError = 2::ModelicaInteger
         const emptyStreamOfTypeList = IOSTREAM("emptyStreamOfTypeList", LIST(), LIST_DATA(nil))::IOStream

        import IOStreamExt

        import MetaModelica.ListUtil

        function create(streamName::String, streamType::IOStreamType) ::IOStream 
              local outStream::IOStream

              outStream = begin
                  local fileName::String
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                @match (streamName, streamType) begin
                  (_, FILE(fileName))  => begin
                      fileID = IOStreamExt.createFile(fileName)
                    IOSTREAM(streamName, streamType, FILE_DATA(fileID))
                  end
                  
                  (_, LIST(__))  => begin
                    IOSTREAM(streamName, streamType, LIST_DATA(nil))
                  end
                  
                  (_, BUFFER(__))  => begin
                      bufferID = IOStreamExt.createBuffer()
                    IOSTREAM(streamName, streamType, BUFFER_DATA(bufferID))
                  end
                end
              end
          outStream
        end

        function append(inStream::IOStream, inString::String) ::IOStream 
              local outStream::IOStream

              outStream = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                  local streamName::String
                  local streamType::IOStreamType
                @match (inStream, inString) begin
                  (fStream && IOSTREAM(data = FILE_DATA(fileID)), _)  => begin
                      IOStreamExt.appendFile(fileID, inString)
                    fStream
                  end
                  
                  (IOSTREAM(streamName, streamType, LIST_DATA(listData)), _)  => begin
                    IOSTREAM(streamName, streamType, LIST_DATA(_cons(inString, listData)))
                  end
                  
                  (bStream && IOSTREAM(data = BUFFER_DATA(bufferID)), _)  => begin
                      IOStreamExt.appendBuffer(bufferID, inString)
                    bStream
                  end
                end
              end
          outStream
        end

        function appendList(inStream::IOStream, inStringList::List{<:String}) ::IOStream 
              local outStream::IOStream

              outStream = ListUtil.foldr(inStringList, append, inStream)
          outStream
        end

        function close(inStream::IOStream) ::IOStream 
              local outStream::IOStream

              outStream = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                @matchcontinue inStream begin
                  fStream && IOSTREAM(data = FILE_DATA(fileID))  => begin
                      IOStreamExt.closeFile(fileID)
                    fStream
                  end
                  
                  _  => begin
                      inStream
                  end
                end
              end
               #=  close does nothing for list or buffer streams
               =#
          outStream
        end

        function delete(inStream::IOStream)  
              _ = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                @match inStream begin
                  IOSTREAM(data = FILE_DATA(fileID))  => begin
                      IOStreamExt.deleteFile(fileID)
                    ()
                  end
                  
                  IOSTREAM(data = LIST_DATA(__))  => begin
                    ()
                  end
                  
                  IOSTREAM(data = BUFFER_DATA(bufferID))  => begin
                      IOStreamExt.deleteBuffer(bufferID)
                    ()
                  end
                end
              end
        end

        function clear(inStream::IOStream) ::IOStream 
              local outStream::IOStream

              outStream = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                  local name::String
                  local data::IOStreamData
                  local ty::IOStreamType
                @matchcontinue inStream begin
                  fStream && IOSTREAM(data = FILE_DATA(fileID))  => begin
                      IOStreamExt.clearFile(fileID)
                    fStream
                  end
                  
                  IOSTREAM(name, ty, _)  => begin
                    IOSTREAM(name, ty, LIST_DATA(nil))
                  end
                  
                  bStream && IOSTREAM(data = BUFFER_DATA(bufferID))  => begin
                      IOStreamExt.clearBuffer(bufferID)
                    bStream
                  end
                end
              end
          outStream
        end

        function string(inStream::IOStream) ::String 
              local string::String

              string = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                  local str::String
                @match inStream begin
                  IOSTREAM(data = FILE_DATA(fileID))  => begin
                      str = IOStreamExt.readFile(fileID)
                    str
                  end
                  
                  IOSTREAM(data = LIST_DATA(listData))  => begin
                      str = IOStreamExt.appendReversedList(listData)
                    str
                  end
                  
                  IOSTREAM(data = BUFFER_DATA(bufferID))  => begin
                      str = IOStreamExt.readBuffer(bufferID)
                    str
                  end
                end
              end
          string
        end

         #= @author: adrpo
          This function will print a string depending on the second argument
          to the standard output (1) or standard error (2).
          Use IOStream.stdOutput, IOStream.stdError constants =#
        function print(inStream::IOStream, whereToPrint::ModelicaInteger)  
              _ = begin
                  local listData::List{String}
                  local fileID::ModelicaInteger
                  local bufferID::ModelicaInteger
                  local fStream::IOStream
                  local lStream::IOStream
                  local bStream::IOStream
                @match (inStream, whereToPrint) begin
                  (IOSTREAM(data = FILE_DATA(fileID)), _)  => begin
                      IOStreamExt.printFile(fileID, whereToPrint)
                    ()
                  end
                  
                  (IOSTREAM(data = BUFFER_DATA(bufferID)), _)  => begin
                      IOStreamExt.printBuffer(bufferID, whereToPrint)
                    ()
                  end
                  
                  (IOSTREAM(data = LIST_DATA(listData)), _)  => begin
                      IOStreamExt.printReversedList(listData, whereToPrint)
                    ()
                  end
                end
              end
        end

         #= /*
        TODO! Global Streams to be implemented later
        IOStream.remember(IOStream, id);
        IOStream = IOStream.aquire(id);
        IOStream.forget(IOStream, id);
        */ =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
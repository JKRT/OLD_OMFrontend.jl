  module GraphStream 


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

        import Values

        import Autoconf
        import GraphStreamExt
        import System
        import Settings

        function startExternalViewer(host::String, port::ModelicaInteger) ::ModelicaInteger 
              local status::ModelicaInteger

              status = begin
                  local omhome::String
                  local command::String
                  local commandWin::String
                  local commandLinux::String
                @matchcontinue (host, port) begin
                  (_, _)  => begin
                      omhome = Settings.getInstallationDirectoryPath()
                      commandWin = "start /b java -jar " + omhome + "/share/omc/java/org.omc.graphstream.jar"
                      commandLinux = "java -jar " + omhome + "/share/omc/java/org.omc.graphstream.jar &"
                      command = if "Windows_NT" == Autoconf.os
                            commandWin
                          else
                            commandLinux
                          end
                      status = System.systemCall(command, "")
                      @match true = status == 0
                    status
                  end
                  
                  _  => begin
                        print("GraphStream: failed to start the external viewer!\\n")
                      fail()
                  end
                end
              end
          status
        end

        function newStream(streamName::String, host::String, port::ModelicaInteger, debug::Bool)  
              GraphStreamExt.newStream(streamName, host, port, debug)
        end

        function addNode(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeId::String)  
              GraphStreamExt.addNode(streamName, sourceId, timeId, nodeId)
        end

        function addEdge(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeIdSource::String, nodeIdTarget::String, directed::Bool)  
              GraphStreamExt.addEdge(streamName, sourceId, timeId, nodeIdSource, nodeIdTarget, directed)
        end

        function addNodeAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeId::String, attributeName::String, attributeValue::Values.Value)  
              GraphStreamExt.addNodeAttribute(streamName, sourceId, timeId, nodeId, attributeName, attributeValue)
        end

        function changeNodeAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeId::String, attributeName::String, attributeValueOld::Values.Value, attributeValueNew::Values.Value)  
              GraphStreamExt.changeNodeAttribute(streamName, sourceId, timeId, nodeId, attributeName, attributeValueOld, attributeValueNew)
        end

        function addEdgeAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeIdSource::String, nodeIdTarget::String, attributeName::String, attributeValue::Values.Value)  
              GraphStreamExt.addEdgeAttribute(streamName, sourceId, timeId, nodeIdSource, nodeIdTarget, attributeName, attributeValue)
        end

        function changeEdgeAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, nodeIdSource::String, nodeIdTarget::String, attributeName::String, attributeValueOld::Values.Value, attributeValueNew::Values.Value)  
              GraphStreamExt.changeEdgeAttribute(streamName, sourceId, timeId, nodeIdSource, nodeIdTarget, attributeName, attributeValueOld, attributeValueNew)
        end

        function addGraphAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, attributeName::String, attributeValue::Values.Value)  
              GraphStreamExt.addGraphAttribute(streamName, sourceId, timeId, attributeName, attributeValue)
        end

        function changeGraphAttribute(streamName::String, sourceId::String, timeId::ModelicaInteger, attributeName::String, attributeValueOld::Values.Value, attributeValueNew::Values.Value)  
              GraphStreamExt.changeGraphAttribute(streamName, sourceId, timeId, attributeName, attributeValueOld, attributeValueNew)
        end

        function cleanup()  
              GraphStreamExt.cleanup()
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
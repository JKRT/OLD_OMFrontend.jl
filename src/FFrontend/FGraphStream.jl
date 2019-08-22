  module FGraphStream 


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
         #=  public imports
         =#

        import FCore
        import FNode

        import Flags
        import GraphStream
        import FGraphDump
        import Values

        Name = FCore.Name 
        Id = FCore.Id 
        Seq = FCore.Seq 
        Next = FCore.Next 
        Node = FCore.Node 
        Data = FCore.Data 
        Kind = FCore.Kind 
        Ref = FCore.Ref 
        Refs = FCore.Refs 
        Children = FCore.Children 
        Parents = FCore.Parents 
        Graph = FCore.Graph 
        Extra = FCore.Extra 
        Visited = FCore.Visited 

        function start()  
              if Flags.isSet(Flags.GRAPH_INST_SHOW_GRAPH)
                GraphStream.startExternalViewer("localhost", 2001)
                GraphStream.newStream("default", "localhost", 2001, false)
                GraphStream.addGraphAttribute("default", "omc", -1, "stylesheet", Values.STRING("node{fill-mode:plain;fill-color:#567;size:6px;}"))
              end
               #=  GraphStream.addGraphAttribute(\"default\", \"omc\", -1, \"ui.antialias\", Values.BOOL(true));
               =#
               #=  GraphStream.addGraphAttribute(\"default\", \"omc\", -1, \"layout.stabilization-limit\", Values.INTEGER(0));
               =#
        end

        function finish()  
              if Flags.isSet(Flags.GRAPH_INST_SHOW_GRAPH)
                GraphStream.cleanup()
              end
        end

        function node(n::Node)  
              _ = begin
                  local color::String
                  local nds::String
                  local id::String
                @matchcontinue n begin
                  _  => begin
                      @match true = Flags.isSet(Flags.GRAPH_INST_SHOW_GRAPH)
                      @match false = FNode.isBasicType(n)
                      @match false = FNode.isIn(n, FNode.isRefBasicType)
                      @match false = FNode.isBuiltin(n)
                      @match false = FNode.isIn(n, FNode.isRefBuiltin)
                      @match false = FNode.isIn(n, FNode.isRefSection)
                      @match false = FNode.isIn(n, FNode.isRefMod)
                      @match false = FNode.isIn(n, FNode.isRefDims)
                      id = intString(FNode.id(n))
                      (_, _, nds) = FGraphDump.graphml(n, false)
                      GraphStream.addNode("default", "omc", -1, id)
                      GraphStream.addNodeAttribute("default", "omc", -1, id, "ui.label", Values.STRING(nds))
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  filter basic types, builtins and things in sections, modifers or dimensions
               =#
        end

        function edge(name::Name, source::Node, target::Node)  
              _ = begin
                @matchcontinue (name, source, target) begin
                  (_, _, _)  => begin
                      @match true = Flags.isSet(Flags.GRAPH_INST_SHOW_GRAPH)
                      @match false = FNode.isBasicType(source)
                      @match false = FNode.isBasicType(target)
                      @match false = FNode.isIn(source, FNode.isRefBasicType)
                      @match false = FNode.isIn(target, FNode.isRefBasicType)
                      @match false = FNode.isBuiltin(source)
                      @match false = FNode.isBuiltin(target)
                      @match false = FNode.isIn(source, FNode.isRefBuiltin)
                      @match false = FNode.isIn(target, FNode.isRefBuiltin)
                      @match false = FNode.isIn(source, FNode.isRefSection)
                      @match false = FNode.isIn(source, FNode.isRefMod)
                      @match false = FNode.isIn(source, FNode.isRefDims)
                      @match false = FNode.isIn(target, FNode.isRefSection)
                      @match false = FNode.isIn(target, FNode.isRefMod)
                      @match false = FNode.isIn(target, FNode.isRefDims)
                      GraphStream.addEdge("default", "omc", -1, intString(FNode.id(source)), intString(FNode.id(target)), false)
                      GraphStream.addEdgeAttribute("default", "omc", -1, intString(FNode.id(source)), intString(FNode.id(target)), "ui.label", Values.STRING(name))
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  filter basic types, builtins and things in sections, modifers or dimensions
               =#
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
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

module FGraphStream

using MetaModelica
using ExportAll
  
@importDBG FCore
@importDBG FNodeUtil
@importDBG Flags
@importDBG GraphStream
#@importDBG FGraphDump
@importDBG Values

Name = FCore.Name 
Id = FCore.Id 
Seq = FCore.Seq 
Next = FCore.Next 
Node = FCore.Node 
Data = FCore.Data 
Kind = FCore.Kind 
Ref = FCore.MMRef 
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
        @match false = FNodeUtil.isBasicType(n)
        @match false = FNodeUtil.isIn(n, FNodeUtil.isRefBasicType)
        @match false = FNodeUtil.isBuiltin(n)
        @match false = FNodeUtil.isIn(n, FNodeUtil.isRefBuiltin)
        @match false = FNodeUtil.isIn(n, FNodeUtil.isRefSection)
        @match false = FNodeUtil.isIn(n, FNodeUtil.isRefMod)
        @match false = FNodeUtil.isIn(n, FNodeUtil.isRefDims)
        id = intString(FNodeUtil.id(n))
        (_, _, nds) = "someNodeName" #Must be a smart way to get this crap FGraphDump.graphml(n, false)
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
        @match false = FNodeUtil.isBasicType(source)
        @match false = FNodeUtil.isBasicType(target)
        @match false = FNodeUtil.isIn(source, FNodeUtil.isRefBasicType)
        @match false = FNodeUtil.isIn(target, FNodeUtil.isRefBasicType)
        @match false = FNodeUtil.isBuiltin(source)
        @match false = FNodeUtil.isBuiltin(target)
        @match false = FNodeUtil.isIn(source, FNodeUtil.isRefBuiltin)
        @match false = FNodeUtil.isIn(target, FNodeUtil.isRefBuiltin)
        @match false = FNodeUtil.isIn(source, FNodeUtil.isRefSection)
        @match false = FNodeUtil.isIn(source, FNodeUtil.isRefMod)
        @match false = FNodeUtil.isIn(source, FNodeUtil.isRefDims)
        @match false = FNodeUtil.isIn(target, FNodeUtil.isRefSection)
        @match false = FNodeUtil.isIn(target, FNodeUtil.isRefMod)
        @match false = FNodeUtil.isIn(target, FNodeUtil.isRefDims)
        GraphStream.addEdge("default", "omc", -1, intString(FNodeUtil.id(source)), intString(FNodeUtil.id(target)), false)
        GraphStream.addEdgeAttribute("default", "omc", -1, intString(FNodeUtil.id(source)), intString(FNodeUtil.id(target)), "ui.label", Values.STRING(name))
        ()
      end
      
      _  => begin
        ()
      end
    end
  end
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

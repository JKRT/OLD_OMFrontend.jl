  module FExpand 


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

        import Absyn
        import AbsynUtil
        import FCore

        import System
        import FResolve
        import FGraph
        import ListUtil

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
        Scope = FCore.Scope 
        ImportTable = FCore.ImportTable 
        Graph = FCore.Graph 
        Extra = FCore.Extra 
        Visited = FCore.Visited 
        Import = FCore.Import 
        Msg = Option 

         #= @author: adrpo
         expand a path in the graph. =#
        function path(inGraph::Graph, inPath::Absyn.Path) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local t::Ref
                  local g::Graph
                @match (inGraph, inPath) begin
                  (g, _)  => begin
                      t = FGraph.top(g)
                      r = t
                    (g, r)
                  end
                end
              end
          (outGraph, outRef)
        end

         #= @author: adrpo
         expand all references in the graph. =#
        function all(inGraph::Graph) ::Graph 
              local outGraph::Graph

              outGraph = begin
                  local lst::List{ModelicaReal}
                  local g::Graph
                @match inGraph begin
                  g  => begin
                      lst = nil
                      System.startTimer()
                      g = FResolve.ext(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("Extends:        " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.derived(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("Derived:        " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.cc(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("ConstrainedBy:  " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.clsext(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("ClassExtends:   " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.ty(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("ComponentTypes: " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.cr(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("Comp Refs:      " + realString(listHead(lst)) + "\\n")
                      System.startTimer()
                      g = FResolve.mod(FGraph.top(g), g)
                      System.stopTimer()
                      lst = ListUtil.consr(lst, System.getTimerIntervalTime())
                      print("Modifiers:      " + realString(listHead(lst)) + "\\n")
                      print("FExpand.all:    " + realString(ListUtil.fold(lst, realAdd, 0.0)) + "\\n")
                    g
                  end
                end
              end
               #=  resolve extends
               =#
               #=  resolve derived
               =#
               #=  resolve type paths for constrain classes
               =#
               #=  resolve class extends nodes
               =#
               #=  resolve type paths
               =#
               #=  resolve all component references
               =#
               #=  resolve all modifier lhs (thisOne = binding)
               =#
          outGraph
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
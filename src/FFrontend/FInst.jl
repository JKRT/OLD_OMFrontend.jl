  module FInst 


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
        import SCode
        import DAE
        import FCore

        import ClockIndexes
        import FBuiltin
        import FGraph
        import FExpand
        import FGraphBuild
        import FGraphDump
        import System
        import InstUtil
        import Flags
        import ListUtil
        import FNode

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
        ImportTable = FCore.ImportTable 
        Graph = FCore.Graph 
        Extra = FCore.Extra 
        Visited = FCore.Visited 
        Import = FCore.Import 
        Msg = Option 

         #= @author: adrpo
         instantiate an entire program =#
        function inst(inPath::Absyn.Path, inProgram::SCode.Program) ::DAE.DAElist 
              local dae::DAE.DAElist

              dae = begin
                  local g::Graph
                  local gclone::Graph
                  local p::SCode.Program
                  local lst::List{ModelicaReal}
                @matchcontinue (inPath, inProgram) begin
                  (_, _)  => begin
                      p = doSCodeDep(inProgram, inPath)
                      lst = nil
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      (_, g) = FBuiltin.initialGraph(FCoreUtil.emptyCache())
                      g = FGraphBuild.mkProgramGraph(p, FCore.USERDEFINED(), g)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("SCode->FGraph:  " + realString(listHead(lst)) + "\\n")
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      g = FExpand.all(g)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("Total time:     " + realString(ListUtil.fold(lst, realAdd, 0.0)) + "\\n")
                      FGraphDump.dumpGraph(g, "F:\\\\dev\\\\" + AbsynUtil.pathString(inPath) + ".graph.graphml")
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      _ = FGraph.clone(g)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("FGraph->clone:  " + realString(listHead(lst)) + "\\n")
                    DAE.emptyDae
                  end
                  
                  (_, _)  => begin
                      print("FInst.inst failed!\\n")
                    DAE.emptyDae
                  end
                end
              end
               #= print(\"FGraph nodes:   \" + intString(listLength(FNode.dfs(FGraph.top(g)))) + \"\\n\");
               =#
               #= print(\"FGraph refs:    \" + intString(listLength(FNode.dfs_filter(FGraph.top(g), FNode.isRefReference))) + \"\\n\");
               =#
               #=  resolve all
               =#
               #= print(\"FGraph nodes:   \" + intString(listLength(FNode.dfs(FGraph.top(g)))) + \"\\n\");
               =#
               #= print(\"FGraph refs:    \" + intString(listLength(FNode.dfs_filter(FGraph.top(g), FNode.isRefReference))) + \"\\n\");
               =#
               #=  FGraphDump.dumpGraph(gclone, \"F:\\\\dev\\\\\" + AbsynUtil.pathString(inPath) + \".graph.clone.graphml\");
               =#
          dae
        end

         #= @author: adrpo
         instantiate path in program =#
        function instPath(inPath::Absyn.Path, inProgram::SCode.Program) ::DAE.DAElist 
              local dae::DAE.DAElist

              dae = begin
                  local g::Graph
                  local r::Ref
                  local p::SCode.Program
                  local lst::List{ModelicaReal}
                @matchcontinue (inPath, inProgram) begin
                  (_, _)  => begin
                    inst(inPath, inProgram)
                  end
                  
                  (_, _)  => begin
                      lst = nil
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      p = doSCodeDep(inProgram, inPath)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("SCode depend:   " + realString(listHead(lst)) + "\\n")
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      (_, g) = FBuiltin.initialGraph(FCoreUtil.emptyCache())
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("Initial graph:  " + realString(listHead(lst)) + "\\n")
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      g = FGraphBuild.mkProgramGraph(p, FCore.USERDEFINED(), g)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("SCode->FGraph:  " + realString(listHead(lst)) + "\\n")
                      System.realtimeTick(ClockIndexes.RT_CLOCK_FINST)
                      (g, _) = FExpand.path(g, inPath)
                      lst = ListUtil.consr(lst, System.realtimeTock(ClockIndexes.RT_CLOCK_FINST))
                      print("FExpand.path:   " + realString(listHead(lst)) + "\\n")
                      print("Total time:     " + realString(ListUtil.fold(lst, realAdd, 0.0)) + "\\n")
                      FGraphDump.dumpGraph(g, "F:\\\\dev\\\\" + AbsynUtil.pathString(inPath) + ".graph.graphml")
                    DAE.emptyDae
                  end
                  
                  (_, _)  => begin
                      print("FInst.inst failed!\\n")
                    DAE.emptyDae
                  end
                end
              end
               #=  resolve all references on path
               =#
               #=  print(\"FGraph nodes:   \" + intString(FGraph.lastId(g)) + \"\\n\");
               =#
          dae
        end

         #= do or not do scode dependency based on a flag =#
        function doSCodeDep(inProgram::SCode.Program, inPath::Absyn.Path) ::SCode.Program 
              local outProgram::SCode.Program

              outProgram = begin
                @matchcontinue (inProgram, inPath) begin
                  (_, _)  => begin
                      @match true = Flags.isSet(Flags.GRAPH_INST_RUN_DEP)
                      outProgram = InstUtil.scodeFlatten(inProgram, inPath)
                    outProgram
                  end
                  
                  _  => begin
                      inProgram
                  end
                end
              end
          outProgram
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
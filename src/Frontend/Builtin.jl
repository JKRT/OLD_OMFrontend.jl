  module Builtin 


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
        import Absyn
        import DAE
        import SCode
        import FCore
        import FCoreUtil
        import FGraph

        import ClassInf
        import Config
        import FBuiltin
        import Flags
        import FGraphBuildEnv
        import Global
        import Util

         #= Returns true if cref is a builtin variable.
          Currently only 'time' is a builtin variable. =#
        function variableIsBuiltin(cref::DAE.ComponentRef) ::Bool 
              local b::Bool

              b = begin
                  local id::String
                @match cref begin
                  DAE.CREF_IDENT(ident = id)  => begin
                    variableNameIsBuiltin(id)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if cref is a builtin variable.
          Currently only 'time' is a builtin variable. =#
        function variableNameIsBuiltin(name::String) ::Bool 
              local b::Bool

              b = begin
                @match name begin
                  "time"  => begin
                    true
                  end
                  
                  "startTime"  => begin
                    Config.acceptOptimicaGrammar()
                  end
                  
                  "finalTime"  => begin
                    Config.acceptOptimicaGrammar()
                  end
                  
                  "objective"  => begin
                    Config.acceptOptimicaGrammar()
                  end
                  
                  "objectiveIntegrand"  => begin
                    Config.acceptOptimicaGrammar()
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #= If accepting Optimica then these variabels are also builtin
               =#
          b
        end

        function isDer(inPath::Absyn.Path)  
              _ = begin
                  local path::Absyn.Path
                @match inPath begin
                  Absyn.IDENT(name = "der")  => begin
                    ()
                  end
                  
                  Absyn.FULLYQUALIFIED(path)  => begin
                      isDer(path)
                    ()
                  end
                end
              end
        end

         #= The initial environment where instantiation takes place is built
          up using this function.  It creates an empty environment and adds
          all the built-in definitions to it.
          NOTE:
            The following built in operators can not be described in
            the type system, since they e.g. have arbitrary arguments, etc.
          - fill
          - cat
            These operators are catched in the elabBuiltinHandler, along with all
            others. =#
        function initialGraph(inCache::FCore.Cache) ::Tuple{FCore.Cache, FGraph.Graph} 
              local graph::FGraph.Graph
              local outCache::FCore.Cache

              local cache::FCore.Cache
              local anyNonExpandableConnector2int::DAE.Type = DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE(SOME(ClassInf.CONNECTOR(Absyn.IDENT("dummy"), false))), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("cardinality"))
              local anyExpandableConnector2int::DAE.Type = DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE(SOME(ClassInf.CONNECTOR(Absyn.IDENT("dummy"), true))), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_BUILTIN, Absyn.IDENT("cardinality"))

              (outCache, graph) = begin
                  local initialClasses::List{Absyn.Class}
                  local initialProgram::SCode.Program
                  local types::List{SCode.Element}
                   #=  First look for cached version
                   =#
                @matchcontinue inCache begin
                  cache  => begin
                      graph = FCoreUtil.getCachedInitialGraph(cache)
                      graph = FGraph.clone(graph)
                    (cache, graph)
                  end
                  
                  cache  => begin
                      graph = getSetInitialGraph(NONE())
                    (cache, graph)
                  end
                  
                  cache  => begin
                      graph = FGraph.new("graph", FCore.dummyTopModel)
                      graph = FGraphBuildEnv.mkProgramGraph(FBuiltin.getBasicTypes(), FCore.BASIC_TYPE(), graph)
                      graph = FBuiltin.initialGraphModelica(graph, FGraphBuildEnv.mkTypeNode, FGraphBuildEnv.mkCompNode)
                      (_, initialProgram) = FBuiltin.getInitialFunctions()
                      graph = FGraphBuildEnv.mkProgramGraph(initialProgram, FCore.BUILTIN(), graph)
                      graph = FBuiltin.initialGraphOptimica(graph, FGraphBuildEnv.mkCompNode)
                      graph = FBuiltin.initialGraphMetaModelica(graph, FGraphBuildEnv.mkTypeNode)
                      cache = FCoreUtil.setCachedInitialGraph(cache, graph)
                      _ = getSetInitialGraph(SOME(graph))
                      graph = FGraph.clone(graph)
                    (cache, graph)
                  end
                end
              end
               #=  we have references in the graph so we need to clone it before giving it away
               =#
               #=  then look in the global roots[builtinEnvIndex]
               =#
               #=  if no cached version found create initial graph.
               =#
               #=  add the ModelicaBuiltin/MetaModelicaBuiltin classes in the initial graph
               =#
               #=  we have references in the graph so we need to clone it before returning it
               =#
          (outCache, graph)
        end

         #= gets/sets the initial environment depending on grammar flags =#
        function getSetInitialGraph(inEnvOpt::Option{<:FGraph.Graph}) ::FGraph.Graph 
              local initialEnv::FGraph.Graph

              initialEnv = begin
                  local assocLst::List{Tuple{ModelicaInteger, FGraph.Graph}}
                  local graph::FGraph.Graph
                  local f::ModelicaInteger
                   #=  nothing there
                   =#
                @matchcontinue inEnvOpt begin
                  _  => begin
                      @shouldFail _ = getGlobalRoot(Global.builtinGraphIndex)
                      setGlobalRoot(Global.builtinGraphIndex, nil)
                    fail()
                  end
                  
                  NONE()  => begin
                      assocLst = getGlobalRoot(Global.builtinGraphIndex)
                      graph = FGraph.clone(Util.assoc(Flags.getConfigEnum(Flags.GRAMMAR), assocLst))
                    graph
                  end
                  
                  SOME(graph)  => begin
                      assocLst = getGlobalRoot(Global.builtinGraphIndex)
                      f = Flags.getConfigEnum(Flags.GRAMMAR)
                      assocLst = if f == Flags.METAMODELICA
                            _cons((Flags.METAMODELICA, graph), assocLst)
                          else
                            if f == Flags.PARMODELICA
                                  _cons((Flags.PARMODELICA, graph), assocLst)
                                else
                                  if f == Flags.MODELICA
                                        _cons((Flags.MODELICA, graph), assocLst)
                                      else
                                        assocLst
                                      end
                                end
                          end
                      setGlobalRoot(Global.builtinGraphIndex, assocLst)
                    graph
                  end
                end
              end
               #=  return the correct graph depending on flags
               =#
               #=  we have references in the graph so we need to clone it before giving it away
               =#
          initialEnv
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
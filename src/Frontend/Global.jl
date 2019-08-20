  module Global 


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
         const recursionDepthLimit = 256::ModelicaInteger
         const maxFunctionFileLength = 50::ModelicaInteger
         #=  Thread-local roots
         =#
         const instOnlyForcedFunctions = 0::ModelicaInteger
         const simulationData = 0 #= For simulations =#::ModelicaInteger
         const codegenTryThrowIndex = 1::ModelicaInteger
         const codegenFunctionList = 2::ModelicaInteger
         const symbolTable = 3::ModelicaInteger
         #=  Global roots start at index=9
         =#
         const instHashIndex = 9::ModelicaInteger
         const instNFInstCacheIndex = 10::ModelicaInteger
         const instNFNodeCacheIndex = 11::ModelicaInteger
         const builtinIndex = 12::ModelicaInteger
         const builtinEnvIndex = 13::ModelicaInteger
         const profilerTime1Index = 14::ModelicaInteger
         const profilerTime2Index = 15::ModelicaInteger
         const flagsIndex = 16::ModelicaInteger
         const builtinGraphIndex = 17::ModelicaInteger
         const rewriteRulesIndex = 18::ModelicaInteger
         const stackoverFlowIndex = 19::ModelicaInteger
         const gcProfilingIndex = 20::ModelicaInteger
         const inlineHashTable = 21::ModelicaInteger
         #=  TODO: Should be a local root?
         =#
         const currentInstVar = 22::ModelicaInteger
         const operatorOverloadingCache = 23::ModelicaInteger
         const optionSimCode = 24::ModelicaInteger
         const interactiveCache = 25::ModelicaInteger
         const isInStream = 26::ModelicaInteger
         const MMToJLListIndex = 27::ModelicaInteger
         #=  indexes in System.tick
         =#
         #=  ----------------------
         =#
         #=  temp vars index
         =#
         const tmpVariableIndex = 4::ModelicaInteger
         #=  file seq
         =#
         const backendDAE_fileSequence = 20::ModelicaInteger
         #=  jacobian name
         =#
         const backendDAE_jacobianSeq = 21::ModelicaInteger
         #=  nodeId
         =#
         const fgraph_nextId = 22::ModelicaInteger
         #=  csevar name
         =#
         const backendDAE_cseIndex = 23::ModelicaInteger
         #=  strong component index
         =#
         const strongComponent_index = 24::ModelicaInteger
         #=  class extends
         =#
         const classExtends_index = 25::ModelicaInteger
         #=  ----------------------
         =#

         #= Called to initialize global roots (when needed) =#
        function initialize()  
              setGlobalRoot(instOnlyForcedFunctions, NONE())
              setGlobalRoot(rewriteRulesIndex, NONE())
              setGlobalRoot(stackoverFlowIndex, NONE())
              setGlobalRoot(inlineHashTable, NONE())
              setGlobalRoot(currentInstVar, NONE())
              setGlobalRoot(interactiveCache, NONE())
              setGlobalRoot(instNFInstCacheIndex, nil)
              setGlobalRoot(instNFNodeCacheIndex, nil)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
  
  module Connect 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Face 
    @UniontypeDecl ConnectorType 
    @UniontypeDecl ConnectorElement 
    @UniontypeDecl SetTrieNode 
    @UniontypeDecl OuterConnect 
    @UniontypeDecl Sets 
    @UniontypeDecl Set 

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

        import DAE

        import Prefix

        import Absyn

         const NEW_SET = -1 #= The index used for new sets which have not
           yet been assigned a set index. =#::ModelicaInteger

          #= This type indicates whether a connector is an inside or an outside connector.
            Note: this is not the same as inner and outer references.
            A connector is inside if it connects from the outside into a component and it
            is outside if it connects out from the component.  This is important when
            generating equations for flow variables, where outside connectors are
            multiplied with -1 (since flow is always into a component). =#
         @Uniontype Face begin
              @Record INSIDE begin

              end

              @Record OUTSIDE begin

              end

              @Record NO_FACE begin

              end
         end

          #= The type of a connector element. =#
         @Uniontype ConnectorType begin
              @Record EQU begin

              end

              @Record FLOW begin

              end

              @Record STREAM begin

                       associatedFlow::Option{DAE.ComponentRef}
              end

              @Record NO_TYPE begin

              end
         end

         @Uniontype ConnectorElement begin
              @Record CONNECTOR_ELEMENT begin

                       name::DAE.ComponentRef
                       face::Face
                       ty::ConnectorType
                       source::DAE.ElementSource
                       set #= Which set this element belongs to. =#::ModelicaInteger
              end
         end

         @Uniontype SetTrieNode begin
              @Record SET_TRIE_NODE begin

                       name::String
                       cref::DAE.ComponentRef
                       nodes::List{SetTrieNode}
                       connectCount::ModelicaInteger
              end

              @Record SET_TRIE_LEAF begin

                       name::String
                       insideElement #= The inside element. =#::Option{ConnectorElement}
                       outsideElement #= The outside element. =#::Option{ConnectorElement}
                       flowAssociation #= The name of the associated flow
                             variable, if the leaf represents a stream variable. =#::Option{DAE.ComponentRef}
                       connectCount #= How many times this connector has been connected. =#::ModelicaInteger
              end
         end

        SetTrie = SetTrieNode  #= A trie, a.k.a. prefix tree, that maps crefs to sets. =#

        SetConnection = Tuple  #= A connection between two sets. =#

         @Uniontype OuterConnect begin
              @Record OUTERCONNECT begin

                       scope #= the scope where this connect was created =#::Prefix.Prefix
                       cr1 #= the lhs component reference =#::DAE.ComponentRef
                       io1 #= inner/outer attribute for cr1 component =#::Absyn.InnerOuter
                       f1 #= the face of the lhs component =#::Face
                       cr2 #= the rhs component reference =#::DAE.ComponentRef
                       io2 #= inner/outer attribute for cr2 component =#::Absyn.InnerOuter
                       f2 #= the face of the rhs component =#::Face
                       source #= the element origin =#::DAE.ElementSource
              end
         end

         @Uniontype Sets begin
              @Record SETS begin

                       sets::SetTrie
                       setCount #= How many sets the trie contains. =#::ModelicaInteger
                       connections::List{SetConnection}
                       outerConnects #= Connect statements to propagate upwards. =#::List{OuterConnect}
              end
         end

          #= A set of connection elements. =#
         @Uniontype Set begin
              @Record SET begin

                       ty::ConnectorType
                       elements::List{ConnectorElement}
              end

              @Record SET_POINTER begin

                       index::ModelicaInteger
              end
         end

         const emptySet = SETS(SET_TRIE_NODE("", DAE.WILD(), nil, 0), 0, nil, nil)::Sets

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
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
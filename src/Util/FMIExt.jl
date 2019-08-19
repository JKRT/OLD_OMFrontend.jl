  module FMIExt 


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

        import FMI

        function initializeFMIImport(inFileName::String, inWorkingDirectory::String, inFMILogLevel::ModelicaInteger, inInputConnectors::Bool, inOutputConnectors::Bool, inIsModelDescriptionImport::Bool = false) ::Tuple{Bool, Option{ModelicaInteger}, Option{ModelicaInteger}, FMI.Info, List{FMI.TypeDefinitions}, FMI.ExperimentAnnotation, Option{ModelicaInteger}, List{FMI.ModelVariables}} 
              local outModelVariablesList::List{FMI.ModelVariables}
              local outModelVariablesInstance::Option{ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#
              local outExperimentAnnotation::FMI.ExperimentAnnotation
              local outTypeDefinitionsList::List{FMI.TypeDefinitions}
              local outFMIInfo::FMI.Info
              local outFMIInstance::Option{ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#
              local outFMIContext::Option{ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#
              local result::Bool

            #= TODO: Defined in the runtime =#
          (result, outFMIContext #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, outFMIInstance #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, outFMIInfo, outTypeDefinitionsList, outExperimentAnnotation, outModelVariablesInstance #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, outModelVariablesList)
        end

        function releaseFMIImport(inFMIModelVariablesInstance::Option{<:ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, inFMIInstance::Option{<:ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, inFMIContext::Option{<:ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#, inFMIVersion::String)  
            #= TODO: Defined in the runtime =#
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
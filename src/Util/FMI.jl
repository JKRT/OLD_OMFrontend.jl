  module FMI 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Info 
    @UniontypeDecl TypeDefinitions 
    @UniontypeDecl EnumerationItem 
    @UniontypeDecl ExperimentAnnotation 
    @UniontypeDecl ModelVariables 
    @UniontypeDecl FmiImport 

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

        import ListUtil

         @Uniontype Info begin
              @Record INFO begin

                       fmiVersion::String
                       fmiType::ModelicaInteger
                       fmiModelName::String
                       fmiModelIdentifier::String
                       fmiGuid::String
                       fmiDescription::String
                       fmiGenerationTool::String
                       fmiGenerationDateAndTime::String
                       fmiVariableNamingConvention::String
                       fmiNumberOfContinuousStates::List{ModelicaInteger}
                       fmiNumberOfEventIndicators::List{ModelicaInteger}
              end
         end

         @Uniontype TypeDefinitions begin
              @Record ENUMERATIONTYPE begin

                       name::String
                       description::String
                       quantity::String
                       min::ModelicaInteger
                       max::ModelicaInteger
                       items::List{EnumerationItem}
              end
         end

         @Uniontype EnumerationItem begin
              @Record ENUMERATIONITEM begin

                       name::String
                       description::String
              end
         end

         @Uniontype ExperimentAnnotation begin
              @Record EXPERIMENTANNOTATION begin

                       fmiExperimentStartTime::ModelicaReal
                       fmiExperimentStopTime::ModelicaReal
                       fmiExperimentTolerance::ModelicaReal
              end
         end

         @Uniontype ModelVariables begin
              @Record REALVARIABLE begin

                       instance::ModelicaInteger
                       name::String
                       description::String
                       baseType::String
                       variability::String
                       causality::String
                       hasStartValue::Bool
                       startValue::ModelicaReal
                       isFixed::Bool
                       valueReference::ModelicaReal
                       x1Placement::ModelicaInteger
                       x2Placement::ModelicaInteger
                       y1Placement::ModelicaInteger
                       y2Placement::ModelicaInteger
              end

              @Record INTEGERVARIABLE begin

                       instance::ModelicaInteger
                       name::String
                       description::String
                       baseType::String
                       variability::String
                       causality::String
                       hasStartValue::Bool
                       startValue::ModelicaInteger
                       isFixed::Bool
                       valueReference::ModelicaReal
                       x1Placement::ModelicaInteger
                       x2Placement::ModelicaInteger
                       y1Placement::ModelicaInteger
                       y2Placement::ModelicaInteger
              end

              @Record BOOLEANVARIABLE begin

                       instance::ModelicaInteger
                       name::String
                       description::String
                       baseType::String
                       variability::String
                       causality::String
                       hasStartValue::Bool
                       startValue::Bool
                       isFixed::Bool
                       valueReference::ModelicaReal
                       x1Placement::ModelicaInteger
                       x2Placement::ModelicaInteger
                       y1Placement::ModelicaInteger
                       y2Placement::ModelicaInteger
              end

              @Record STRINGVARIABLE begin

                       instance::ModelicaInteger
                       name::String
                       description::String
                       baseType::String
                       variability::String
                       causality::String
                       hasStartValue::Bool
                       startValue::String
                       isFixed::Bool
                       valueReference::ModelicaReal
                       x1Placement::ModelicaInteger
                       x2Placement::ModelicaInteger
                       y1Placement::ModelicaInteger
                       y2Placement::ModelicaInteger
              end

              @Record ENUMERATIONVARIABLE begin

                       instance::ModelicaInteger
                       name::String
                       description::String
                       baseType::String
                       variability::String
                       causality::String
                       hasStartValue::Bool
                       startValue::ModelicaInteger
                       isFixed::Bool
                       valueReference::ModelicaReal
                       x1Placement::ModelicaInteger
                       x2Placement::ModelicaInteger
                       y1Placement::ModelicaInteger
                       y2Placement::ModelicaInteger
              end
         end

         @Uniontype FmiImport begin
              @Record FMIIMPORT begin

                       platform::String
                       fmuFileName::String
                       fmuWorkingDirectory::String
                       fmiLogLevel::ModelicaInteger
                       fmiDebugOutput::Bool
                       fmiContext::Option{ModelicaInteger}
                       fmiInstance::Option{ModelicaInteger}
                       fmiInfo::Info
                       fmiTypeDefinitionsList::List{TypeDefinitions}
                       fmiExperimentAnnotation::ExperimentAnnotation
                       fmiModelVariablesInstance::Option{ModelicaInteger}
                       fmiModelVariablesList::List{ModelVariables}
                       generateInputConnectors::Bool
                       generateOutputConnectors::Bool
              end
         end

        function getFMIModelIdentifier(inFMIInfo::Info) ::String 
              local fmiModelIdentifier::String

              fmiModelIdentifier = begin
                  local modelIdentifier::String
                @match inFMIInfo begin
                  INFO(fmiModelIdentifier = modelIdentifier)  => begin
                    modelIdentifier
                  end
                end
              end
          fmiModelIdentifier
        end

        function getFMIType(inFMIInfo::Info) ::String 
              local fmiType::String

              fmiType = begin
                @match inFMIInfo begin
                  INFO(fmiVersion = "1.0", fmiType = 0)  => begin
                    "me"
                  end
                  
                  INFO(fmiVersion = "1.0", fmiType = 1)  => begin
                    "cs_st"
                  end
                  
                  INFO(fmiVersion = "1.0", fmiType = 2)  => begin
                    "cs_tool"
                  end
                  
                  INFO(fmiVersion = "2.0", fmiType = 1)  => begin
                    "me"
                  end
                  
                  INFO(fmiVersion = "2.0", fmiType = 2)  => begin
                    "cs"
                  end
                  
                  INFO(fmiVersion = "2.0", fmiType = 3)  => begin
                    "me_cs"
                  end
                end
              end
          fmiType
        end

        function getFMIVersion(inFMIInfo::Info) ::String 
              local fmiVersion::String

              fmiVersion = begin
                  local version::String
                @match inFMIInfo begin
                  INFO(fmiVersion = version)  => begin
                    version
                  end
                end
              end
          fmiVersion
        end

         #= Checks if the FMU version is supported. =#
        function checkFMIVersion(inFMIVersion::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMIVersion begin
                  "1.0"  => begin
                    true
                  end
                  
                  "2.0"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

         #= Checks if the FMI version is 1.0. =#
        function isFMIVersion10(inFMUVersion::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMUVersion begin
                  "1.0"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

         #= Checks if the FMI version is 2.0. =#
        function isFMIVersion20(inFMUVersion::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMUVersion begin
                  "2.0"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

         #= Checks if the FMU type is supported. =#
        function checkFMIType(inFMIType::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMIType begin
                  "me"  => begin
                    true
                  end
                  
                  "cs"  => begin
                    true
                  end
                  
                  "me_cs"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

        function canExportFMU(inFMUVersion::String, inFMIType::String) ::Bool 
              local success::Bool

              success = begin
                @match (inFMUVersion, inFMIType) begin
                  ("1.0", "me")  => begin
                    true
                  end
                  
                  ("2.0", "me")  => begin
                    true
                  end
                  
                  ("2.0", "cs")  => begin
                    true
                  end
                  
                  ("2.0", "me_cs")  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

         #= Checks if FMU type is model exchange =#
        function isFMIMEType(inFMIType::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMIType begin
                  "me"  => begin
                    true
                  end
                  
                  "me_cs"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

         #= Checks if FMU type is co-simulation =#
        function isFMICSType(inFMIType::String) ::Bool 
              local success::Bool

              success = begin
                @match inFMIType begin
                  "cs"  => begin
                    true
                  end
                  
                  "me_cs"  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          success
        end

        function getEnumerationTypeFromTypes(inTypeDefinitionsList::List{<:TypeDefinitions}, inBaseType::String) ::String 
              local outEnumerationType::String

              outEnumerationType = begin
                  local xs::List{TypeDefinitions}
                  local name_::String
                  local baseType::String
                @match (inTypeDefinitionsList, inBaseType) begin
                  (ENUMERATIONTYPE(name = name_) <| _, baseType) where (stringEqual(name_, baseType))  => begin
                    name_
                  end
                  
                  (_ <| xs, baseType)  => begin
                      name_ = getEnumerationTypeFromTypes(xs, baseType)
                    name_
                  end
                  
                  ( nil(), _)  => begin
                    ""
                  end
                end
              end
          outEnumerationType
        end

        function filterModelVariables(inModelVariables::List{<:ModelVariables}, tipe::String, variableCausality::String) ::List{ModelVariables} 
              local outModelVariables::List{ModelVariables}

              outModelVariables = ListUtil.filter2OnTrue(inModelVariables, filterModelVariable, tipe, variableCausality)
          outModelVariables
        end

        function filterModelVariable(modelVar::ModelVariables, tipe::String, variableCausality::String) ::Bool 
              local result::Bool

              result = begin
                  local causality::String
                @match modelVar begin
                  REALVARIABLE(causality = causality) where (tipe == "real" && causality == variableCausality)  => begin
                    true
                  end
                  
                  INTEGERVARIABLE(causality = causality) where (tipe == "integer" && causality == variableCausality)  => begin
                    true
                  end
                  
                  BOOLEANVARIABLE(causality = causality) where (tipe == "boolean" && causality == variableCausality)  => begin
                    true
                  end
                  
                  STRINGVARIABLE(causality = causality) where (tipe == "string" && causality == variableCausality)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
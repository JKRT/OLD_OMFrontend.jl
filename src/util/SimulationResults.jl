  module SimulationResults 


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

        import MetaModelica.ListUtil
        import ValuesUtil

        function val(filename::String, varname::String, timeStamp::ModelicaReal) ::ModelicaReal 
              local val::ModelicaReal

            #= TODO: Defined in the runtime =#
          val
        end

        function readVariables(filename::String, readParameters::Bool = true, openmodelicaStyle::Bool = false) ::List{String} 
              local vars::List{String}

            #= TODO: Defined in the runtime =#
          vars
        end

        function readDataset(filename::String, vars::List{<:String}, dimsize::ModelicaInteger) ::Values.Value 
              local val::Values.Value

              local rvals::List{List{ModelicaReal}}
              local vals::List{List{Values.Value}}
              local rows::List{Values.Value}

              function readDataset_work(filename::String, vars::List{<:String}, dimsize::ModelicaInteger) ::List{List{ModelicaReal}} 
                    local outMatrix::List{List{ModelicaReal}}

                  #= TODO: Defined in the runtime =#
                outMatrix
              end

              rvals = readDataset_work(filename, vars, dimsize)
              vals = ListUtil.mapListReverse(rvals, ValuesUtil.makeReal)
              rows = ListUtil.mapReverse(vals, ValuesUtil.makeArray)
              val = ValuesUtil.makeArray(rows)
          val
        end

        function readSimulationResultSize(filename::String) ::ModelicaInteger 
              local size::ModelicaInteger

            #= TODO: Defined in the runtime =#
          size
        end

        function close()  
            #= TODO: Defined in the runtime =#
        end

        function cmpSimulationResults(runningTestsuite::Bool, filename::String, reffilename::String, logfilename::String, refTol::ModelicaReal, absTol::ModelicaReal, vars::List{<:String}) ::List{String} 
              local res::List{String}

            #= TODO: Defined in the runtime =#
          res
        end

        function deltaSimulationResults(filename::String, reffilename::String, method::String, vars::List{<:String}) ::ModelicaReal 
              local res::ModelicaReal

            #= TODO: Defined in the runtime =#
          res
        end

        function diffSimulationResults(runningTestsuite::Bool, filename::String, reffilename::String, prefix::String, refTol::ModelicaReal, relTolDiffMaxMin::ModelicaReal, rangeDelta::ModelicaReal, vars::List{<:String}, keepEqualResults::Bool) ::Tuple{Bool, List{String}} 
              local res::List{String}
              local success::Bool

            #= TODO: Defined in the runtime =#
          (success, res)
        end

        function diffSimulationResultsHtml(runningTestsuite::Bool, filename::String, reffilename::String, refTol::ModelicaReal, relTolDiffMaxMin::ModelicaReal, rangeDelta::ModelicaReal, var::String) ::String 
              local html::String

            #= TODO: Defined in the runtime =#
          html
        end

        function filterSimulationResults(inFile::String, outFile::String, vars::List{<:String}, numberOfIntervals::ModelicaInteger = 0, removeDescription::Bool) ::Bool 
              local result::Bool

            #= TODO: Defined in the runtime =#
          result
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
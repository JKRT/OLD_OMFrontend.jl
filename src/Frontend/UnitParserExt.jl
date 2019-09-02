  module UnitParserExt 


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

         #= initialize the UnitParser with the SI units =#
        function initSIUnits()  
            #= TODO: Defined in the runtime =#
        end

         #= Translate a unit to a string =#
        function unit2str(noms::List{<:ModelicaInteger} #= nominators =#, denoms::List{<:ModelicaInteger} #= denominators =#, tpnoms::List{<:ModelicaInteger}, tpdenoms::List{<:ModelicaInteger}, tpstrs::List{<:String}, scaleFactor::ModelicaReal, offset::ModelicaReal) ::String 
              local res::String

            #= TODO: Defined in the runtime =#
          res
        end

         #= Translate a unit string to a unit =#
        function str2unit(res::String) ::Tuple{List{ModelicaInteger}, List{ModelicaInteger}, List{ModelicaInteger}, List{ModelicaInteger}, List{String}, ModelicaReal, ModelicaReal} 
              local offset::ModelicaReal
              local scaleFactor::ModelicaReal
              local tpstrs::List{String}
              local tpdenoms::List{ModelicaInteger}
              local tpnoms::List{ModelicaInteger}
              local denoms::List{ModelicaInteger}
              local noms::List{ModelicaInteger}

            #= TODO: Defined in the runtime =#
          (noms, denoms, tpnoms, tpdenoms, tpstrs, scaleFactor, offset)
        end

        function allUnitSymbols() ::List{String} 
              local unitSymbols::List{String}

            #= TODO: Defined in the runtime =#
          unitSymbols
        end

         #= adds a base unit without weight =#
        function addBase(name::String)  
            #= TODO: Defined in the runtime =#
        end

         #= registers a weight to be multiplied with the weigth factor of a derived unit =#
        function registerWeight(name::String, weight::ModelicaReal)  
            #= TODO: Defined in the runtime =#
        end

         #= adds a derived unit without weight =#
        function addDerived(name::String, exp::String)  
            #= TODO: Defined in the runtime =#
        end

         #= adds a derived unit with weight =#
        function addDerivedWeight(name::String, exp::String, weight::ModelicaReal)  
            #= TODO: Defined in the runtime =#
        end

         #= copies all unitparser information to allow changing unit weights locally for a component =#
        function checkpoint()  
            #= TODO: Defined in the runtime =#
        end

         #= rollback the copy made in checkPoint call =#
        function rollback()  
            #= TODO: Defined in the runtime =#
        end

         #= clears the unitparser from stored units =#
        function clear()  
            #= TODO: Defined in the runtime =#
        end

         #= commits all units, must be run before doing unit checking and after last unit has been added
        with addBase or addDerived. =#
        function commit()  
            #= TODO: Defined in the runtime =#
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
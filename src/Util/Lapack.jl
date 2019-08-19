  module Lapack 


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

        function dgeev(inJOBVL::String, inJOBVR::String, inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inLDVL::ModelicaInteger, inLDVR::ModelicaInteger, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaReal}, List{ModelicaReal}, List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outVR::List{List{ModelicaReal}}
              local outVL::List{List{ModelicaReal}}
              local outWI::List{ModelicaReal}
              local outWR::List{ModelicaReal}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outWR, outWI, outVL, outVR, outWORK, outINFO)
        end

        function dgegv(inJOBVL::String, inJOBVR::String, inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger, inLDVL::ModelicaInteger, inLDVR::ModelicaInteger, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{ModelicaReal}, List{ModelicaReal}, List{ModelicaReal}, List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outVR::List{List{ModelicaReal}}
              local outVL::List{List{ModelicaReal}}
              local outBETA::List{ModelicaReal}
              local outALPHAI::List{ModelicaReal}
              local outALPHAR::List{ModelicaReal}

            #= TODO: Defined in the runtime =#
          (outALPHAR, outALPHAI, outBETA, outVL, outVR, outWORK, outINFO)
        end

        function dgels(inTRANS::String, inM::ModelicaInteger, inN::ModelicaInteger, inNRHS::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outB::List{List{ModelicaReal}}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outB, outWORK, outINFO)
        end

        function dgelsx(inM::ModelicaInteger, inN::ModelicaInteger, inNRHS::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger, inJPVT::List{<:ModelicaInteger}, inRCOND::ModelicaReal, inWORK::List{<:ModelicaReal}) ::Tuple{List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaInteger}, ModelicaInteger, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outRANK::ModelicaInteger
              local outJPVT::List{ModelicaInteger}
              local outB::List{List{ModelicaReal}}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outB, outJPVT, outRANK, outINFO)
        end

        function dgelsy(inM::ModelicaInteger, inN::ModelicaInteger, inNRHS::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger, inJPVT::List{<:ModelicaInteger}, inRCOND::ModelicaReal, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaInteger}, ModelicaInteger, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outRANK::ModelicaInteger
              local outJPVT::List{ModelicaInteger}
              local outB::List{List{ModelicaReal}}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outB, outJPVT, outRANK, outWORK, outINFO)
        end

        function dgesv(inN::ModelicaInteger, inNRHS::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaInteger}, List{List{ModelicaReal}}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outB::List{List{ModelicaReal}}
              local outIPIV::List{ModelicaInteger}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outIPIV, outB, outINFO)
        end

        function dgglse(inM::ModelicaInteger, inN::ModelicaInteger, inP::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger, inC::List{<:ModelicaReal}, inD::List{<:ModelicaReal}, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaReal}, List{ModelicaReal}, List{ModelicaReal}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outX::List{ModelicaReal}
              local outD::List{ModelicaReal}
              local outC::List{ModelicaReal}
              local outB::List{List{ModelicaReal}}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outB, outC, outD, outX, outWORK, outINFO)
        end

        function dgtsv(inN::ModelicaInteger, inNRHS::ModelicaInteger, inDL::List{<:ModelicaReal}, inD::List{<:ModelicaReal}, inDU::List{<:ModelicaReal}, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger) ::Tuple{List{ModelicaReal}, List{ModelicaReal}, List{ModelicaReal}, List{List{ModelicaReal}}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outB::List{List{ModelicaReal}}
              local outDU::List{ModelicaReal}
              local outD::List{ModelicaReal}
              local outDL::List{ModelicaReal}

            #= TODO: Defined in the runtime =#
          (outDL, outD, outDU, outB, outINFO)
        end

        function dgbsv(inN::ModelicaInteger, inKL::ModelicaInteger, inKU::ModelicaInteger, inNRHS::ModelicaInteger, inAB::List{<:List{<:ModelicaReal}}, inLDAB::ModelicaInteger, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaInteger}, List{List{ModelicaReal}}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outB::List{List{ModelicaReal}}
              local outIPIV::List{ModelicaInteger}
              local outAB::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outAB, outIPIV, outB, outINFO)
        end

        function dgesvd(inJOBU::String, inJOBVT::String, inM::ModelicaInteger, inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inLDU::ModelicaInteger, inLDVT::ModelicaInteger, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaReal}, List{List{ModelicaReal}}, List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outVT::List{List{ModelicaReal}}
              local outU::List{List{ModelicaReal}}
              local outS::List{ModelicaReal}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outS, outU, outVT, outWORK, outINFO)
        end

        function dgetrf(inM::ModelicaInteger, inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaInteger}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outIPIV::List{ModelicaInteger}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outIPIV, outINFO)
        end

        function dgetrs(inTRANS::String, inN::ModelicaInteger, inNRHS::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inIPIV::List{<:ModelicaInteger}, inB::List{<:List{<:ModelicaReal}}, inLDB::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outB::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outB, outINFO)
        end

        function dgetri(inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inIPIV::List{<:ModelicaInteger}, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outWORK, outINFO)
        end

        function dgeqpf(inM::ModelicaInteger, inN::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inJPVT::List{<:ModelicaInteger}, inWORK::List{<:ModelicaReal}) ::Tuple{List{List{ModelicaReal}}, List{ModelicaInteger}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outTAU::List{ModelicaReal}
              local outJPVT::List{ModelicaInteger}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outJPVT, outTAU, outINFO)
        end

        function dorgqr(inM::ModelicaInteger, inN::ModelicaInteger, inK::ModelicaInteger, inA::List{<:List{<:ModelicaReal}}, inLDA::ModelicaInteger, inTAU::List{<:ModelicaReal}, inWORK::List{<:ModelicaReal}, inLWORK::ModelicaInteger) ::Tuple{List{List{ModelicaReal}}, List{ModelicaReal}, ModelicaInteger} 
              local outINFO::ModelicaInteger
              local outWORK::List{ModelicaReal}
              local outA::List{List{ModelicaReal}}

            #= TODO: Defined in the runtime =#
          (outA, outWORK, outINFO)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
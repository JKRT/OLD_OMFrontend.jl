  module ExpressionSimplifyTypes 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Evaluate 
    SymbolTableLookupValue = Function
    SymbolTableLookupVariability = Function
    SymbolTableAddScope = Function
    SymbolTableRemoveScope = Function
    @UniontypeDecl IntOp 

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
         * THIS OSMC LICENSE (OSMC-PL) VERSION 1.2.
         * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
         * RECIPIENT'S ACCEPTANCE OF THE OSMC LICENSE OR THE GPL VERSION 3,
         * ACCORDING TO RECIPIENTS CHOICE.
         *
         * The OpenModelica software and the Open Source Modelica
         * Consortium (OSMC) License (OSMC-PL) are obtained
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
         * See the full OSMC License conditions for more details.
         *
         */ =#
        import DAE
        import SCode

          #= The expression should be evaluated to a literal value; return an error if this fails =#
         @Uniontype Evaluate begin
              @Record NO_EVAL begin

              end

              @Record DO_EVAL begin

              end
         end

        SymbolTable = ModelicaInteger 
         #= /* TODO: Make replaceable type or specialized package for bootstrapping */ =#
        SymbolTableInterface = Tuple 









        Options = Tuple  #= I am a stupid tuple because MM does not like type variables in records =#

         @Uniontype IntOp begin
              @Record MULOP begin

              end

              @Record DIVOP begin

              end

              @Record ADDOP begin

              end

              @Record SUBOP begin

              end

              @Record POWOP begin

              end
         end

         const optionSimplifyOnly = (NONE(), NO_EVAL())::Options

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
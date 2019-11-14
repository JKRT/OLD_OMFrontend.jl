  module DAEUtilMinimal


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

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

        @importDBG Absyn
        @importDBG DAE

        function varName(var::DAE.Element) ::String
              local name::String

              @match DAE.VAR(componentRef = DAE.CREF_IDENT(ident = name)) = var
          name
        end

        function typeVarIdent(var::DAE.Var) ::DAE.Ident
              local name::DAE.Ident

              @match DAE.TYPES_VAR(name = name) = var
          name
        end

        function typeVarIdentEqual(var::DAE.Var, name::String) ::Bool
              local b::Bool

              local name2::String

              @match DAE.TYPES_VAR(name = name2) = var
              b = stringEq(name, name2)
          b
        end

        #= returns true if type is array type
       Alternative names: isArrayType, isExpTypeArray =#
       function expTypeArray(tp::DAE.Type) ::Bool
             local isArray::Bool

             isArray = begin
               @match tp begin
                 DAE.T_ARRAY(__)  => begin
                   true
                 end

                 _  => begin
                     false
                 end
               end
             end
         isArray
       end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

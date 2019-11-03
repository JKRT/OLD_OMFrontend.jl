  module SCodeDumpUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl SCodeDumpOptions

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

        import SCode

        import ListUtil

         @Uniontype SCodeDumpOptions begin
              @Record OPTIONS begin

                       stripAlgorithmSections::Bool
                       stripProtectedImports::Bool
                       stripProtectedClasses::Bool
                       stripProtectedComponents::Bool
                       stripMetaRecords #= The automatically generated records that change scope from uniontype to the package =#::Bool
                       stripGraphicalAnnotations::Bool
                       stripStringComments::Bool
                       stripExternalDecl::Bool
                       stripOutputBindings::Bool
              end
         end

        const defaultOptions = OPTIONS(false, false, false, false, true, true, false, false, false)::SCodeDumpOptions

        function filterElements(elements::List{<:SCode.Element}, options::SCodeDumpOptions) ::List{SCode.Element}
              local outElements::List{SCode.Element}

              outElements = ListUtil.select1(elements, filterElement, options)
          outElements
        end


    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

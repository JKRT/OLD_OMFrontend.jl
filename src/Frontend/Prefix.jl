  module Prefix


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl ComponentPrefix
    @UniontypeDecl ClassPrefix

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

        import SCode

        import ClassInf

        import DAE

          #= A Prefix has a component prefix and a class prefix.
         The component prefix consist of a name an a list of constant valued subscripts.
         The class prefix contains the variability of the class, i.e unspecified, parameter or constant. =#
         @Uniontype PrefixType begin
              @Record NOPRE begin

              end

              @Record PREFIX begin

                       compPre #= component prefixes are stored in inverse order c.b.a =#::ComponentPrefix
                       classPre #= the class prefix, i.e. variability, var, discrete, param, const =#::ClassPrefix
              end
         end

        ComponentPrefixOpt = Option  #= a type alias for an optional component prefix =#

          #= Prefix for component name, e.g. a.b[2].c.
          NOTE: Component prefixes are stored in inverse order c.b[2].a! =#
         @Uniontype ComponentPrefix begin
              @Record PRE begin

                       prefix #= prefix name =#::String
                       dimensions #= dimensions =#::List{DAE.Dimension}
                       subscripts #= subscripts =#::List{DAE.Subscript}
                       next #= next prefix =#::ComponentPrefix
                       ci_state #= to be able to at least partially fill in type information properly for DAE.VAR =#::ClassInf.State
                       info::SourceInfo
              end

              @Record NOCOMPPRE begin

              end
         end

          #= Prefix for classes is its variability =#
         @Uniontype ClassPrefix begin
              @Record CLASSPRE begin

                       variability #= VAR, DISCRETE, PARAM, or CONST =#::SCode.Variability
              end
         end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

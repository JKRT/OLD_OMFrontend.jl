  module UnitAbsyn


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl UnitCheckResult
    @UniontypeDecl SpecUnit
    @UniontypeDecl TypeParameter
    @UniontypeDecl Unit
    @UniontypeDecl UnitTerm
    @UniontypeDecl Store
    @UniontypeDecl InstStore

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

        import DAE

        import MMath

        import HashTable

         @Uniontype UnitCheckResult begin
              @Record CONSISTENT begin

              end

               #=  May be complete or incomplete
               =#

              @Record INCONSISTENT begin

                       u1::SpecUnit
                       #= Left unit
                       =#
                       u2::SpecUnit
                       #= Right unit
                       =#
              end
         end

         @Uniontype SpecUnit begin
              @Record SPECUNIT begin

                       typeParameters #= A type parameter also has an exponent. =#::List{Tuple{MMath.Rational, TypeParameter}}
                       units #= first seven elements are the SI base units =#::List{MMath.Rational}
              end
         end

         @Uniontype TypeParameter begin
              @Record TYPEPARAMETER begin

                       name #= a type parameter name has the form identifier followed by a apostrophe, e.g. p'  =#::String
                       indx #= indx in Store =#::ModelicaInteger
              end
         end

          #= A unit is either specified (including type parameters) or unspecified =#
         @Uniontype Unit begin
              @Record SPECIFIED begin

                       specified::SpecUnit
              end

              @Record UNSPECIFIED begin

              end
         end

          #= A unit term is either
          - a binary operation, e.g. multiplication, addition, etc.
          - an equation (equality)
          - a location with unique id
           =#
         @Uniontype UnitTerm begin
              @Record ADD begin

                       ut1 #= left =#::UnitTerm
                       ut2 #= right =#::UnitTerm
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record SUB begin

                       ut1 #= left =#::UnitTerm
                       ut2 #= right =#::UnitTerm
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record MUL begin

                       ut1 #= left =#::UnitTerm
                       ut2 #= right =#::UnitTerm
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record DIV begin

                       ut1 #= nominator =#::UnitTerm
                       ut2 #= denominator =#::UnitTerm
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record EQN begin

                       ut1::UnitTerm
                       ut2::UnitTerm
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record LOC begin

                       loc #= location is an integer(index in vector) =#::ModelicaInteger
                       origExp #= for proper error reporting =#::DAE.Exp
              end

              @Record POW begin

                       ut1::UnitTerm
                       exponent #= ut^exponent =#::MMath.Rational
                       origExp #= for proper error reporting =#::DAE.Exp
              end
         end

        UnitTerms = List

         @Uniontype Store begin
              @Record STORE begin

                       storeVector::Array{Option{Unit}}
                       numElts #= Number of elements stored in vector =#::ModelicaInteger
              end
         end

          #= A store used in Inst.mo
         requires a mapping from variable names to locations. Unit checking can be turned off using NOSTORE
          =#
         @Uniontype InstStore begin
              @Record INSTSTORE begin

                       store::Store
                       ht::HashTable.HashTableType
                       checkResult #= when a check is done the result is stored here =#::Option{UnitCheckResult}
              end

              @Record NOSTORE begin

              end
         end

         const noStore = NOSTORE()::InstStore

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

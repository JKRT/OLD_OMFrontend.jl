  module InstTypes 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl CallingScope 
    @UniontypeDecl SearchStrategy 
    @UniontypeDecl SplicedExpData 

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

          #= 
         Calling scope is used to determine when unconnected flow variables should be set to zero. =#
         @Uniontype CallingScope begin
              @Record TOP_CALL begin

              end

              @Record INNER_CALL begin

              end

              @Record TYPE_CALL begin

              end
         end

        PolymorphicBindings = List 
         const alwaysUnroll = true::Bool
         const neverUnroll = false::Bool

         @Uniontype SearchStrategy begin
              @Record SEARCH_LOCAL_ONLY begin

              end

              @Record SEARCH_ALSO_BUILTIN begin

              end
         end

         @Uniontype SplicedExpData begin
              @Record SPLICEDEXPDATA begin

                       splicedExp #= the spliced expression =#::Option{DAE.Exp}
                       identType #= the type of the variable without subscripts, needed for vectorization =#::DAE.Type
              end
         end

        TypeMemoryEntry = Tuple 
        TypeMemoryEntryList = List 
        TypeMemoryEntryListArray = Array 
        InstDims = List  #= Changed from list<Subscript> to list<list<Subscript>>. One list for each scope.
         This so when instantiating classes extending from primitive types can collect the dimension of -one- surrounding scope to create type.
         E.g. RealInput p[3]; gives the list {3} for this scope and other lists for outer (in instance hierachy) scopes =#

        function callingScopeStr(inCallingScope::CallingScope) ::String 
              local str::String

              str = begin
                @match inCallingScope begin
                  TOP_CALL(__)  => begin
                    "topCall"
                  end
                  
                  INNER_CALL(__)  => begin
                    "innerCall"
                  end
                  
                  TYPE_CALL(__)  => begin
                    "typeCall"
                  end
                end
              end
          str
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
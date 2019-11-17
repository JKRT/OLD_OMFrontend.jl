module ConnectUtilMinimal


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    using Setfield


    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    UpdateFunc = Function

    FuncType = Function

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
         #=  public imports
         =#

        import Absyn
        import ClassInf
        import DAE

        import DAE.Face
        import DAE.ConnectorElement
        import DAE.ConnectorType
        import DAE.SetTrieNode
        import DAE.SetTrie
        import DAE.SetConnection
        import DAE.OuterConnect
        import DAE.Sets
        import DAE.CSet
         #=  CSet graph represented as an adjacency list.
         =#

        DaeEdges = List # ConnectionGraph.DaeEdges # this doesn't seem to work, it says DaeEdges is undefined!

         #= Test for face equality. =#
        function faceEqual(face1::Face, face2::Face) ::Bool
              local sameFaces::Bool = valueEq(face1, face2)
          sameFaces
        end

        #= Author: BZ, 2008-12
         Same functionalty as componentFace, with the difference that
         this function checks ident-type rather then env->lookup ==> type.
         Rules:
           qualified cref and connector     => OUTSIDE
           non-qualifed cref                => OUTSIDE
           qualified cref and non-connector => INSIDE

         Modelica Specification 4.0
         Section: 9.1.2 Inside and Outside Connectors
         In an element instance M, each connector element of M is called an outside connector with respect to M.
         All other connector elements that are hierarchically inside M, but not in one of the outside connectors
         of M, is called an inside connector with respect to M. This is done **BEFORE** resolving outer elements
         to corresponding inner ones. =#
       function componentFaceType(inComponentRef::DAE.ComponentRef) ::Face
             local outFace::Face

             outFace = begin
               @match inComponentRef begin
                 DAE.CREF_IDENT(__)  => begin
                   DAE.OUTSIDE()
                 end

                 DAE.CREF_QUAL(identType = DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _)))  => begin
                   DAE.OUTSIDE()
                 end

                 DAE.CREF_QUAL(identType = DAE.T_ARRAY(ty = DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, _))))  => begin
                   DAE.OUTSIDE()
                 end

                 DAE.CREF_QUAL(__)  => begin
                   DAE.INSIDE()
                 end
               end
             end
              #=  is a non-qualified cref => OUTSIDE
              =#
              #=  is a qualified cref and is a connector => OUTSIDE
              =#
              #=  is a qualified cref and is an array of connectors => OUTSIDE
              =#
              #=  is a qualified cref and is NOT a connector => INSIDE
              =#
         outFace
       end

       #= @author: adrpo
        this function checks if the given type is an expandable connector =#
      function isExpandableConnector(ty::DAE.Type) ::Bool
            local isExpandable::Bool

            isExpandable = begin
              @match ty begin
                DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, true))  => begin
                  true
                end

                DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(_, true))  => begin
                  true
                end

                _  => begin
                    false
                end
              end
            end
             #=  TODO! check if subtype is needed here
             =#
        isExpandable
      end

       function isExpandable(name::DAE.ComponentRef) ::Bool
             local expandableConnector::Bool

             expandableConnector = begin
               @match name begin
                 DAE.CREF_IDENT(__)  => begin
                   isExpandableConnector(name.identType)
                 end

                 DAE.CREF_QUAL(__)  => begin
                   isExpandableConnector(name.identType) || isExpandable(name.componentRef)
                 end

                 _  => begin
                     false
                 end
               end
             end
         expandableConnector
       end


    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  module FTraverse 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl WalkOptions 
    @UniontypeDecl VisitOptions 
    @UniontypeDecl Options 

    Walker = Function

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

        import AbsynUtil

        import FNode

        import FVisit

        import FGraph
         #=  protected imports
         =#

        Ident = String  #=  An identifier is just a string  =#
        Import = Absyn.Import 
        Node = FNode.Node 
        Ref = FNode.Ref 
        Data = FNode.Data 
        Visited = FVisit.Visited 
        Graph = FGraph.Graph 
        Extra = Any 

         @Uniontype WalkOptions begin
              @Record BFS begin

              end

              @Record DFS begin

              end
         end

         @Uniontype VisitOptions begin
              @Record VISIT begin

              end

              @Record NO_VISIT begin

              end
         end

         @Uniontype Options begin
              @Record NO_OPTIONS begin

              end

              @Record OPTIONS begin

                       ws::WalkOptions
                       vs::VisitOptions
              end
         end

         #= walk each node in the graph =#
        function walk(inGraph::Graph, inWalker::Walker, inExtra::Extra, inOptions::Options) ::Tuple{Graph, Extra} 
              local outExtra::Extra
              local outGraph::Graph

              (outGraph, outExtra) = begin
                @match (inGraph, inWalker, inExtra, inOptions) begin
                  (_, _, _, _)  => begin
                    (inGraph, inExtra)
                  end
                end
              end
          (outGraph, outExtra)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
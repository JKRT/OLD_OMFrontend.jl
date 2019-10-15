  module FGraphDump


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

        import SCode
        import DAE
        import FCore
        import FNode
        import FGraph
        import GraphML

        const Name = FCore.Name
        const Id = FCore.Id
        const Seq = FCore.Seq
        const Next = FCore.Next
        const Node = FCore.Node
        const Data = FCore.Data
        const Kind = FCore.Kind
        const Ref = FCore.MMRef
        const Refs = FCore.Refs
        const RefTree = FCore.RefTree
        const Children = FCore.Children
        const Parents = FCore.Parents
        const ImportTable = FCore.ImportTable
        const Extra = FCore.Extra
        const Visited = FCore.Visited
        const Import = FCore.Import
        const Graph = FCore.Graph
        const Type = DAE.Type
        const Types = List

        import Flags
        import Dump
        import Absyn
        import AbsynUtil
        import SCodeUtil
        import Util

        function dumpGraph(inGraph::Graph, fileName::String)
              _ = begin
                  local g::ModelicaInteger
                  local gi::GraphML.GraphInfo
                  local nr::Ref
                @matchcontinue (inGraph, fileName) begin
                  (_, _)  => begin
                      @match false = Flags.isSet(Flags.GRAPH_INST_GEN_GRAPH)
                    ()
                  end

                  (_, _)  => begin
                      gi = GraphML.createGraphInfo()
                      (gi, (_, g)) = GraphML.addGraph("G", false, gi)
                      nr = FGraph.top(inGraph)
                      (gi, g) = addNodes((gi, g), list(nr))
                      print("Dumping graph file: " + fileName + " ....\\n")
                      GraphML.dumpGraph(gi, fileName)
                      print("Dumped\\n")
                    ()
                  end
                end
              end
        end

        function addNodes(gin::Tuple{<:GraphML.GraphInfo, ModelicaInteger}, inRefs::List{<:Ref}) ::Tuple{GraphML.GraphInfo, ModelicaInteger}
              local gout::Tuple{GraphML.GraphInfo, ModelicaInteger}

              gout = begin
                  local g::Tuple{GraphML.GraphInfo, ModelicaInteger}
                  local rest::List{Ref}
                  local n::Ref
                @match (gin, inRefs) begin
                  (_,  nil())  => begin
                    gin
                  end

                  (g, n <| rest) where (! FNode.isRefTop(n) && ! FNode.isRefUserDefined(n))  => begin
                    addNodes(g, rest)
                  end

                  (g, n <| rest)  => begin
                      g = addNode(g, FNode.fromRef(n))
                    addNodes(g, rest)
                  end
                end
              end
               #=  if not userdefined or top, skip it
               =#
          gout
        end

        function addNode(gin::Tuple{<:GraphML.GraphInfo, ModelicaInteger}, node::Node) ::Tuple{GraphML.GraphInfo, ModelicaInteger}
              local gout::Tuple{GraphML.GraphInfo, ModelicaInteger}

              gout = begin
                  local gi::GraphML.GraphInfo
                  local i::ModelicaInteger
                  local id::ModelicaInteger
                  local kids::Children
                  local name::Name
                  local nd::Data
                  local n::String
                  local nds::String
                  local color::String
                  local labelText::String
                  local shape::GraphML.ShapeType
                  local nr::Ref
                  local target::Ref
                  local nrefs::List{Ref}
                  local label::GraphML.NodeLabel
                  local elabel::GraphML.EdgeLabel
                   #=  top node
                   =#
                @match (gin, node) begin
                  ((gi, i), FCore.N(parents =  nil(), children = kids))  => begin
                      (color, shape, nds) = graphml(node, true)
                      labelText = nds
                      label = GraphML.NODELABEL_INTERNAL(labelText, NONE(), GraphML.FONTPLAIN())
                      (gi, _) = GraphML.addNode("n" + intString(FNode.id(node)), color, GraphML.BORDERWIDTH_STANDARD, list(label), shape, NONE(), nil, i, gi)
                      nrefs = RefTree.listValues(kids)
                      (gi, i) = addNodes((gi, i), nrefs)
                    (gi, i)
                  end

                  ((gi, i), FCore.N(parents = nr <| _, children = kids, data = FCore.REF( nil())))  => begin
                      (color, shape, nds) = graphml(node, true)
                      labelText = nds
                      label = GraphML.NODELABEL_INTERNAL(labelText, NONE(), GraphML.FONTPLAIN())
                      (gi, _) = GraphML.addNode("n" + intString(FNode.id(node)), color, GraphML.BORDERWIDTH_STANDARD, list(label), shape, NONE(), nil, i, gi)
                      (gi, _) = GraphML.addEdge("r" + intString(FNode.id(node)), "n" + intString(FNode.id(node)), "n" + intString(FNode.id(FNode.fromRef(nr))), GraphML.COLOR_RED, GraphML.LINE(), GraphML.LINEWIDTH_STANDARD, false, nil, (GraphML.ARROWNONE(), GraphML.ARROWSTANDART()), nil, gi)
                      nrefs = RefTree.listValues(kids)
                      (gi, i) = addNodes((gi, i), nrefs)
                    (gi, i)
                  end

                  ((gi, i), FCore.N(parents = nr <| _, children = kids, data = FCore.REF(_ <| _)))  => begin
                      (color, shape, nds) = graphml(node, true)
                      labelText = nds
                      label = GraphML.NODELABEL_INTERNAL(labelText, NONE(), GraphML.FONTPLAIN())
                      (gi, _) = GraphML.addNode("n" + intString(FNode.id(node)), color, GraphML.BORDERWIDTH_STANDARD, list(label), shape, NONE(), nil, i, gi)
                      (gi, _) = GraphML.addEdge("r" + intString(FNode.id(node)), "n" + intString(FNode.id(node)), "n" + intString(FNode.id(FNode.fromRef(nr))), GraphML.COLOR_GREEN, GraphML.LINE(), GraphML.LINEWIDTH_STANDARD, false, nil, (GraphML.ARROWNONE(), GraphML.ARROWSTANDART()), nil, gi)
                      nrefs = RefTree.listValues(kids)
                      (gi, i) = addNodes((gi, i), nrefs)
                    (gi, i)
                  end

                  ((gi, i), FCore.N(parents = _ <| _, data = FCore.VR(__)))  => begin
                    (gi, i)
                  end

                  ((gi, i), FCore.N(parents = nr <| _, children = kids))  => begin
                      (color, shape, nds) = graphml(node, true)
                      labelText = nds
                      label = GraphML.NODELABEL_INTERNAL(labelText, NONE(), GraphML.FONTPLAIN())
                      (gi, _) = GraphML.addNode("n" + intString(FNode.id(node)), color, GraphML.BORDERWIDTH_STANDARD, list(label), shape, NONE(), nil, i, gi)
                      (gi, _) = GraphML.addEdge("e" + intString(FNode.id(node)), "n" + intString(FNode.id(node)), "n" + intString(FNode.id(FNode.fromRef(nr))), GraphML.COLOR_BLACK, GraphML.LINE(), GraphML.LINEWIDTH_STANDARD, false, nil, (GraphML.ARROWNONE(), GraphML.ARROWNONE()), nil, gi)
                      nrefs = RefTree.listValues(kids)
                      (gi, i) = addNodes((gi, i), nrefs)
                    (gi, i)
                  end
                end
              end
               #=  empty REF node, add it with red as is unresolveds
               =#
               #=  {elabel},
               =#
               #= /*/ add ref edge
                      (gi, _) = GraphML.addEdge(
                                 \"r\" + intString(FNode.id(node)),
                                 \"n\" + intString(FNode.id(FNode.fromRef(target))),
                                 \"n\" + intString(FNode.id(FNode.fromRef(nr))),
                                 GraphML.COLOR_RED,
                                 GraphML.DASHED(),
                                 GraphML.LINEWIDTH_STANDARD,
                                 false,
                                 {elabel},
                                 (GraphML.ARROWNONE(),GraphML.ARROWSTANDART()),
                                 {},
                                 gi);*/ =#
               #=  something REF node, either add it as a new node or an edge (commented out)
               =#
               #=  {elabel},
               =#
               #= /*/ add ref edge
                      (gi, _) = GraphML.addEdge(
                                 \"r\" + intString(FNode.id(node)),
                                 \"n\" + intString(FNode.id(FNode.fromRef(target))),
                                 \"n\" + intString(FNode.id(FNode.fromRef(nr))),
                                 GraphML.COLOR_RED,
                                 GraphML.DASHED(),
                                 GraphML.LINEWIDTH_STANDARD,
                                 false,
                                 {elabel},
                                 (GraphML.ARROWNONE(),GraphML.ARROWSTANDART()),
                                 {},
                                 gi);*/ =#
               #=  ignore coref nodes
               =#
               #=  other nodes
               =#
               #=  {elabel},
               =#
          gout
        end

        function graphml(node::Node, escape::Bool) ::Tuple{String, GraphML.ShapeType, String}
              local nname::String
              local shape::GraphML.ShapeType
              local color::String

              (color, shape, nname) = begin
                  local kids::Children
                  local p::Parents
                  local name::Name
                  local id::ModelicaInteger
                  local n::Name
                  local nd::Data
                  local e::SCode.Element
                  local exp::Absyn.Exp
                  local r::Absyn.ComponentRef
                  local s::String
                  local dims::Absyn.ArrayDim
                  local target::Ref
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                   #=  redeclare replaceable class
                   =#
                @matchcontinue (node, escape) begin
                  (FCore.N(_, _, _, _, FCore.CL(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementRedeclare(e)
                      @match true = SCodeUtil.isElementReplaceable(e)
                      b = FNode.isClassExtends(node)
                      s = if b
                            "rdrpCE:"
                          else
                            "rdrpC:"
                          end
                      s = s + FNode.name(node)
                    (GraphML.COLOR_YELLOW, GraphML.HEXAGON(), s)
                  end

                  (FCore.N(_, _, _, _, FCore.CL(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementRedeclare(e)
                      b = FNode.isClassExtends(node)
                      s = if b
                            "rdCE:"
                          else
                            "rdC:"
                          end
                      s = s + FNode.name(node)
                    (GraphML.COLOR_YELLOW, GraphML.HEXAGON(), s)
                  end

                  (FCore.N(_, _, _, _, FCore.CL(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementReplaceable(e)
                      s = "rpC:" + FNode.name(node)
                    (GraphML.COLOR_RED, GraphML.RECTANGLE(), s)
                  end

                  (FCore.N(_, _, _, _, FCore.CO(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementRedeclare(e)
                      @match true = SCodeUtil.isElementReplaceable(e)
                      s = "rdrpc:" + FNode.name(node)
                    (GraphML.COLOR_YELLOW, GraphML.ELLIPSE(), s)
                  end

                  (FCore.N(_, _, _, _, FCore.CO(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementRedeclare(e)
                      s = "rdc:" + FNode.name(node)
                    (GraphML.COLOR_YELLOW, GraphML.ELLIPSE(), s)
                  end

                  (FCore.N(_, _, _, _, FCore.CO(e = e)), _)  => begin
                      @match true = SCodeUtil.isElementReplaceable(e)
                      s = "rpc:" + FNode.name(node)
                    (GraphML.COLOR_RED, GraphML.ELLIPSE(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.CL(__)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.name(node)
                    (GraphML.COLOR_GRAY, GraphML.RECTANGLE(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.CO(__)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.name(node)
                    (GraphML.COLOR_WHITE, GraphML.ELLIPSE(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.EX(__)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.name(node)
                    (GraphML.COLOR_GREEN, GraphML.ROUNDRECTANGLE(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.EXP(e = exp)), _)  => begin
                      s = Dump.printExpStr(exp)
                      s = FNode.dataStr(nd) + ":" + (if escape
                            Util.escapeModelicaStringToXmlString(s)
                          else
                            Util.stringTrunc(s, 100)
                          end)
                    (GraphML.COLOR_PURPLE, GraphML.HEXAGON(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.DIMS(dims = dims)), _)  => begin
                      s = Dump.printArraydimStr(dims)
                      s = FNode.dataStr(nd) + ":" + (if escape
                            Util.escapeModelicaStringToXmlString(s)
                          else
                            Util.stringTrunc(s, 100)
                          end)
                    (GraphML.COLOR_PINK, GraphML.TRIANGLE(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.CR(r = r)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + AbsynUtil.printComponentRefStr(r)
                    (GraphML.COLOR_PURPLE, GraphML.OCTAGON(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.ASSERT(s)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.name(node)
                    (GraphML.COLOR_RED, GraphML.PARALLELOGRAM(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.REF( nil())), _)  => begin
                      s = FNode.dataStr(nd) + ":" + "UNRESOLVED"
                    (GraphML.COLOR_RED, GraphML.PARALLELOGRAM(), s)
                  end

                  (FCore.N(_, _, _, _, nd && FCore.REF(target <| _)), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.toPathStr(FNode.fromRef(target))
                    (GraphML.COLOR_GREEN, GraphML.TRAPEZOID(), s)
                  end

                  (FCore.N(_, _, _, _, nd), _)  => begin
                      s = FNode.dataStr(nd) + ":" + FNode.name(node)
                    (GraphML.COLOR_BLUE, GraphML.ELLIPSE(), s)
                  end
                end
              end
               #=  redeclare class
               =#
               #=  replaceable class
               =#
               #=  redeclare replaceable component
               =#
               #=  redeclare component
               =#
               #=  replaceable component
               =#
               #=  class
               =#
               #=  component
               =#
               #=  extends
               =#
               #=  expressions: bindings, condition in conditional components, array dim, etc
               =#
               #=  dimensions
               =#
               #=  component references
               =#
               #=  ASSERT nodes
               =#
               #=  empty REF nodes
               =#
               #=  non empty REF nodes
               =#
               #=  all others
               =#
          (color, shape, nname)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

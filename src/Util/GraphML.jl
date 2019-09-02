  module GraphML


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl GraphInfo
    @UniontypeDecl Graph
    @UniontypeDecl Node
    @UniontypeDecl Edge
    @UniontypeDecl Attribute
    @UniontypeDecl NodeLabel
    @UniontypeDecl EdgeLabel
    @UniontypeDecl FontStyle
    @UniontypeDecl ShapeType
    @UniontypeDecl LineType
    @UniontypeDecl ArrowType
    @UniontypeDecl AttributeType
    @UniontypeDecl AttributeTarget

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

        import ListUtil

        import Tpl

        import Util
         #= TODO: Use HashTable for nodes to prevent duplicates
         =#
         #=  -------------------------
         =#
         #=  Constant types
         =#
         #=  -------------------------
         =#

         const COLOR_BLACK = "000000"::String

         const COLOR_BLUE = "0000FF"::String

         const COLOR_GREEN = "339966"::String

         const COLOR_RED = "FF0000"::String

         const COLOR_DARKRED = "800000"::String

         const COLOR_WHITE = "FFFFFF"::String

         const COLOR_YELLOW = "FFFF00"::String

         const COLOR_GRAY = "C0C0C0"::String

         const COLOR_PURPLE = "993366"::String

         const COLOR_ORANGE = "FFCC00"::String

         const COLOR_ORANGE2 = "FF6600"::String

         const COLOR_DARKGRAY = "666666"::String

         const COLOR_RED2 = "F0988E"::String

         const COLOR_GREEN2 = "98B954"::String

         const COLOR_CYAN = "46BED8"::String

         const COLOR_PINK = "CF8CB7"::String

         const COLOR_GREEN3 = "008080"::String

         const LINEWIDTH_STANDARD = 2.0::ModelicaReal

         const LINEWIDTH_BOLD = 4.0::ModelicaReal

         const FONTSIZE_STANDARD = 12::ModelicaInteger

         const FONTSIZE_BIG = 20::ModelicaInteger

         const FONTSIZE_SMALL = 8::ModelicaInteger

         const BORDERWIDTH_STANDARD = 1.0::ModelicaReal

         const BORDERWIDTH_BOLD = 4.0::ModelicaReal
         #=  -------------------------
         =#
         #=  Data structures
         =#
         #=  -------------------------
         =#

         @Uniontype GraphInfo begin
              @Record GRAPHINFO begin

                       graphs::List{Graph}
                       graphCount::ModelicaInteger
                       #= number of graphs in the graphs list
                       =#
                       nodes::List{Node}
                       nodeCount::ModelicaInteger
                       #= number of nodes in the nodes list
                       =#
                       edges::List{Edge}
                       edgeCount::ModelicaInteger
                       #= number of edges in the edge list
                       =#
                       attributes::List{Attribute}
                       graphNodeKey::String
                       graphEdgeKey::String
              end

              @Record GRAPHINFOARR begin

                       #= This structure is used by Susan
                       =#
                       graphs::Array{Graph}
                       nodes::Array{Node}
                       edges::List{Edge}
                       attributes::Array{Attribute}
                       graphNodeKey::String
                       graphEdgeKey::String
              end
         end

         @Uniontype Graph begin
              @Record GRAPH begin

                       id::String
                       directed::Bool
                       nodeIdc::List{ModelicaInteger}
                       #= attention: reversed indices --> to get real idx for value i, calculate graph.nodeCount - i
                       =#
                       attValues::List{Tuple{ModelicaInteger, String}}
                       #= values of custom attributes (see GRAPHINFO definition). <attributeIndex,attributeValue>
                       =#
              end
         end

         @Uniontype Node begin
              @Record NODE begin

                       id::String
                       color::String
                       border::ModelicaReal
                       nodeLabels::List{NodeLabel}
                       shapeType::ShapeType
                       optDesc::Option{String}
                       attValues::List{Tuple{ModelicaInteger, String}}
                       #= values of custom attributes (see GRAPH definition). <attributeIndex,attributeValue>
                       =#
              end

              @Record GROUPNODE begin

                       id::String
                       internalGraphIdx::ModelicaInteger
                       isFolded::Bool
                       header::String
              end
         end

         @Uniontype Edge begin
              @Record EDGE begin

                       id::String
                       target::String
                       source::String
                       color::String
                       lineType::LineType
                       lineWidth::ModelicaReal
                       smooth::Bool
                       edgeLabels::List{EdgeLabel}
                       arrows::Tuple{ArrowType, ArrowType}
                       attValues::List{Tuple{ModelicaInteger, String}}
                       #= values of custom attributes (see GRAPH definition). <attributeIndex,attributeValue>
                       =#
              end
         end

         @Uniontype Attribute begin
              @Record ATTRIBUTE begin

                       attIdx::ModelicaInteger
                       defaultValue::String
                       name::String
                       attType::AttributeType
                       attTarget::AttributeTarget
              end
         end

         @Uniontype NodeLabel begin
              @Record NODELABEL_INTERNAL begin

                       text::String
                       backgroundColor::Option{String}
                       fontStyle::FontStyle
              end

              @Record NODELABEL_CORNER begin

                       text::String
                       backgroundColor::Option{String}
                       fontStyle::FontStyle
                       position::String
                       #= for example \"se\" for south east
                       =#
              end
         end

         @Uniontype EdgeLabel begin
              @Record EDGELABEL begin

                       text::String
                       backgroundColor::Option{String}
                       fontSize::ModelicaInteger
              end
         end

         @Uniontype FontStyle begin
              @Record FONTPLAIN begin

              end

              @Record FONTBOLD begin

              end

              @Record FONTITALIC begin

              end

              @Record FONTBOLDITALIC begin

              end
         end

         @Uniontype ShapeType begin
              @Record RECTANGLE begin

              end

              @Record ROUNDRECTANGLE begin

              end

              @Record ELLIPSE begin

              end

              @Record PARALLELOGRAM begin

              end

              @Record HEXAGON begin

              end

              @Record TRIANGLE begin

              end

              @Record OCTAGON begin

              end

              @Record DIAMOND begin

              end

              @Record TRAPEZOID begin

              end

              @Record TRAPEZOID2 begin

              end
         end

         @Uniontype LineType begin
              @Record LINE begin

              end

              @Record DASHED begin

              end

              @Record DASHEDDOTTED begin

              end
         end

         @Uniontype ArrowType begin
              @Record ARROWSTANDART begin

              end

              @Record ARROWNONE begin

              end

              @Record ARROWCONCAVE begin

              end
         end

         @Uniontype AttributeType begin
              @Record TYPE_STRING begin

              end

              @Record TYPE_BOOLEAN begin

              end

              @Record TYPE_INTEGER begin

              end

              @Record TYPE_DOUBLE begin

              end
         end

         @Uniontype AttributeTarget begin
              @Record TARGET_NODE begin

              end

              @Record TARGET_EDGE begin

              end

              @Record TARGET_GRAPH begin

              end
         end

         #=  -------------------------
         =#
         #=  Logic
         =#
         #=  -------------------------
         =#

         #= author: marcusw
          Creates a new and empty graphInfo. =#
        function createGraphInfo() ::GraphInfo
              local oGraphInfo::GraphInfo

              oGraphInfo = GRAPHINFO(nil, 0, nil, 0, nil, 0, nil, "gi1", "gi2")
          oGraphInfo
        end

         #= author: marcusw
          Adds a new graph to the given graphInfo. =#
        function addGraph(id::String, directed::Bool, iGraphInfo::GraphInfo) ::Tuple{GraphInfo, Tuple{Graph, ModelicaInteger}}
              local oGraph::Tuple{Graph, ModelicaInteger}
              local oGraphInfo::GraphInfo

              local tmpGraph::Graph
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              graphCount = graphCount + 1
              tmpGraph = GRAPH(id, directed, nil, nil)
              graphs = _cons(tmpGraph, graphs)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
              oGraph = (tmpGraph, graphCount)
          (oGraphInfo, oGraph)
        end

         #= author: marcusw
          Adds a new node to the given graph which is part of the given graphInfo. =#
        function addNode(id::String, backgroundColor::String, borderWidth::ModelicaReal, nodeLabels::List{<:NodeLabel}, shapeType::ShapeType, optDesc::Option{<:String}, attValues::List{<:Tuple{<:ModelicaInteger, String}}, iGraphIdx::ModelicaInteger, iGraphInfo::GraphInfo) ::Tuple{GraphInfo, Tuple{Node, ModelicaInteger}}
              local oNode::Tuple{Node, ModelicaInteger}
              local oGraphInfo::GraphInfo

              local tmpNode::Node
               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String
               #= values of graph
               =#
              local iGraph::Graph
              local gid::String
              local directed::Bool
              local nodeIdc::List{ModelicaInteger}
              local gAttValues::List{Tuple{ModelicaInteger, String}}

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              iGraph = listGet(graphs, graphCount - iGraphIdx + 1)
              @match GRAPH(gid, directed, nodeIdc, gAttValues) = iGraph
              nodeCount = nodeCount + 1
              tmpNode = NODE(id, backgroundColor, borderWidth, nodeLabels, shapeType, optDesc, attValues)
              nodes = _cons(tmpNode, nodes)
              nodeIdc = _cons(nodeCount, nodeIdc)
              iGraph = GRAPH(gid, directed, nodeIdc, gAttValues)
              graphs = ListUtil.set(graphs, graphCount - iGraphIdx + 1, iGraph)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
              oNode = (tmpNode, nodeCount)
          (oGraphInfo, oNode)
        end

         #= author: marcusw
          Adds a new group node to the given graphInfo. The created node contains a new graph which is returned as second output-argument. =#
        function addGroupNode(id::String, iGraphIdx::ModelicaInteger, isFolded::Bool, iHeader::String, iGraphInfo::GraphInfo) ::Tuple{GraphInfo, Tuple{Node, ModelicaInteger}, Tuple{Graph, ModelicaInteger}}
              local oGraph::Tuple{Graph, ModelicaInteger}
              local oNode::Tuple{Node, ModelicaInteger}
              local oGraphInfo::GraphInfo

              local tmpGraphInfo::GraphInfo
              local tmpNode::Node
               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String
               #= values of graph
               =#
              local iGraph::Graph
              local newGraph::Graph
              local gid::String
              local directed::Bool
              local newGraphIdx::ModelicaInteger
              local nodeIdc::List{ModelicaInteger}
              local attValues::List{Tuple{ModelicaInteger, String}}
               #= values of custom attributes (see GRAPHINFO definition). <attributeIndex,attributeValue>
               =#

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              iGraph = listGet(graphs, graphCount - iGraphIdx + 1)
              @match GRAPH(gid, directed, nodeIdc, attValues) = iGraph
               #= Add new sub graph
               =#
              (tmpGraphInfo, (newGraph, newGraphIdx)) = addGraph("g" + id, directed, iGraphInfo)
              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = tmpGraphInfo
               #= Append node to graph
               =#
              nodeCount = nodeCount + 1
              tmpNode = GROUPNODE(id, newGraphIdx, isFolded, iHeader)
              nodes = _cons(tmpNode, nodes)
              nodeIdc = _cons(nodeCount, nodeIdc)
              iGraph = GRAPH(gid, directed, nodeIdc, attValues)
              graphs = ListUtil.set(graphs, graphCount - iGraphIdx + 1, iGraph)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
              oNode = (tmpNode, nodeCount)
              oGraph = (newGraph, newGraphIdx)
          (oGraphInfo, oNode, oGraph)
        end

         #= author: marcusw
          Adds a new edge to the graphInfo-structure. Edges are always added to the top-level graph. =#
        function addEdge(id::String, target::String, source::String, color::String, lineType::LineType, lineWidth::ModelicaReal, smooth::Bool, labels::List{<:EdgeLabel}, arrows::Tuple{<:ArrowType, ArrowType}, attValues::List{<:Tuple{<:ModelicaInteger, String}}, iGraphInfo::GraphInfo) ::Tuple{GraphInfo, Tuple{Edge, ModelicaInteger}}
              local oEdge::Tuple{Edge, ModelicaInteger}
              local oGraphInfo::GraphInfo

              local tmpEdge::Edge
               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              edgeCount = edgeCount + 1
              tmpEdge = EDGE(id, target, source, color, lineType, lineWidth, smooth, labels, arrows, attValues)
              edges = _cons(tmpEdge, edges)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
              oEdge = (tmpEdge, edgeCount)
          (oGraphInfo, oEdge)
        end

         #= author: marcusw
          Adds a new attribute to the given graphInfo.
          These attributes can be used by graphs, nodes and edges to display some additional informations. =#
        function addAttribute(defaultValue::String, name::String, attType::AttributeType, attTarget::AttributeTarget, iGraphInfo::GraphInfo) ::Tuple{GraphInfo, Tuple{Attribute, ModelicaInteger}}
              local oAttribute::Tuple{Attribute, ModelicaInteger}
              local oGraphInfo::GraphInfo

              local tmpAttribute::Attribute
              local attIdx::ModelicaInteger
               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              attIdx = listLength(attributes) + 1
              tmpAttribute = ATTRIBUTE(attIdx, defaultValue, name, attType, attTarget)
              attributes = _cons(tmpAttribute, attributes)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
              oAttribute = (tmpAttribute, attIdx)
          (oGraphInfo, oAttribute)
        end

         #= author: marcusw
          Adds a new value for a given attribute to the graph. =#
        function addGraphAttributeValue(iValue::Tuple{<:ModelicaInteger, String}, iGraphIdx::ModelicaInteger, iGraphInfo::GraphInfo) ::GraphInfo
              local oGraphInfo::GraphInfo

               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String
               #= values of graph
               =#
              local iGraph::Graph
              local gid::String
              local directed::Bool
              local newGraphIdx::ModelicaInteger
              local nodeIdc::List{ModelicaInteger}
              local attValues::List{Tuple{ModelicaInteger, String}}
               #= values of custom attributes (see GRAPHINFO definition). <attributeIndex,attributeValue>
               =#

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              iGraph = listGet(graphs, graphCount - iGraphIdx + 1)
              @match GRAPH(gid, directed, nodeIdc, attValues) = iGraph
               #= Append attribute to graph
               =#
              attValues = _cons(iValue, attValues)
              iGraph = GRAPH(gid, directed, nodeIdc, attValues)
              graphs = ListUtil.set(graphs, graphCount - iGraphIdx + 1, iGraph)
              oGraphInfo = GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey)
          oGraphInfo
        end

         #=  -------------------------
         =#
         #=  Helper
         =#
         #=  -------------------------
         =#

         #= author: marcusw
          This function will return the top-level graph (usually with index 1) if there is one in the graphInfo-structure.
          Otherwise it will return NONE(). =#
        function getMainGraph(iGraphInfo::GraphInfo) ::Option{Tuple{ModelicaInteger, Graph}}
              local oGraph::Option{Tuple{ModelicaInteger, Graph}}

              local graphs::List{Graph}
              local firstGraph::Graph

              oGraph = begin
                @match iGraphInfo begin
                  GRAPHINFO(graphCount = 0)  => begin
                    NONE()
                  end

                  GRAPHINFO(graphs = graphs)  => begin
                      firstGraph = listHead(graphs)
                    SOME((1, firstGraph))
                  end
                end
              end
          oGraph
        end

        function getAttributeByNameAndTarget(iAttributeName::String, iAttributeTarget::AttributeTarget, iGraphInfo::GraphInfo) ::Option{Tuple{Attribute, ModelicaInteger}}
              local oAttribute::Option{Tuple{Attribute, ModelicaInteger}}

              local attributes::List{Attribute}
              local tmpRes::Option{Tuple{Attribute, ModelicaInteger}}

              oAttribute = begin
                @match (iAttributeName, iAttributeTarget, iGraphInfo) begin
                  (_, _, GRAPHINFO(attributes = attributes))  => begin
                      tmpRes = getAttributeByNameAndTargetTail(attributes, iAttributeName, iAttributeTarget)
                    tmpRes
                  end

                  (_, _, GRAPHINFO(attributes = attributes))  => begin
                      tmpRes = getAttributeByNameAndTargetTail(attributes, iAttributeName, iAttributeTarget)
                    tmpRes
                  end
                end
              end
          oAttribute
        end

        function getAttributeByNameAndTargetTail(iList::List{<:Attribute}, iAttributeName::String, iAttributeTarget::AttributeTarget) ::Option{Tuple{Attribute, ModelicaInteger}}
              local oAttribute::Option{Tuple{Attribute, ModelicaInteger}}

              local rest::List{Attribute}
              local attIdx::ModelicaInteger
              local name::String
              local head::Attribute
              local attTarget::AttributeTarget
              local tmpAttribute::Option{Tuple{Attribute, ModelicaInteger}}

              oAttribute = begin
                @matchcontinue (iList, iAttributeName, iAttributeTarget) begin
                  (head && ATTRIBUTE(attIdx = attIdx, name = name, attTarget = attTarget) <| rest, _, _)  => begin
                      @match true = stringEq(name, iAttributeName)
                      @match true = compareAttributeTargets(iAttributeTarget, attTarget)
                    SOME((head, attIdx))
                  end

                  (head <| rest, _, _)  => begin
                      tmpAttribute = getAttributeByNameAndTargetTail(rest, iAttributeName, iAttributeTarget)
                    tmpAttribute
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          oAttribute
        end

        function compareAttributeTargets(iTarget1::AttributeTarget, iTarget2::AttributeTarget) ::Bool
              local oEqual::Bool

              local tarInt1::ModelicaInteger
              local tarInt2::ModelicaInteger

              tarInt1 = compareAttributeTarget0(iTarget1)
              tarInt2 = compareAttributeTarget0(iTarget2)
              oEqual = intEq(tarInt1, tarInt2)
          oEqual
        end

        function compareAttributeTarget0(iTarget::AttributeTarget) ::ModelicaInteger
              local oCodec::ModelicaInteger

              oCodec = begin
                @match iTarget begin
                  TARGET_NODE(__)  => begin
                    0
                  end

                  TARGET_EDGE(__)  => begin
                    1
                  end

                  TARGET_GRAPH(__)  => begin
                    1
                  end
                end
              end
          oCodec
        end

         #=  -------------------------
         =#
         #=  Dump
         =#
         #=  -------------------------
         =#

         #= author: marcusw
          Dumps the graph into a *.graphml-file. =#
        function dumpGraph(iGraphInfo::GraphInfo, iFileName::String)
        end

         #= author: marcusw
          Converts the given GRAPHINFO-object into a GRAPHINFOARR-object. =#
        function convertToGraphInfoArr(iGraphInfo::GraphInfo) ::GraphInfo
              local oGraphInfo::GraphInfo

               #= values of graphinfo
               =#
              local graphs::List{Graph}
              local graphsArr::Array{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodesArr::Array{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local attributesArr::Array{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String

              @match GRAPHINFO(graphs, graphCount, nodes, nodeCount, edges, edgeCount, attributes, graphNodeKey, graphEdgeKey) = iGraphInfo
              graphsArr = listArray(graphs)
              nodesArr = listArray(nodes)
              attributesArr = ListUtil.listArrayReverse(attributes)
              oGraphInfo = GRAPHINFOARR(graphsArr, nodesArr, edges, attributesArr, graphNodeKey, graphEdgeKey)
          oGraphInfo
        end

         #=  -------------------------
         =#
         #=  debug prints
         =#
         #=  -------------------------
         =#

        function printGraphInfo(iGraphInfo::GraphInfo)
              local graphs::List{Graph}
              local graphCount::ModelicaInteger
               #= number of graphs in the graphs list
               =#
              local nodes::List{Node}
              local nodeCount::ModelicaInteger
               #= number of nodes in the nodes list
               =#
              local edges::List{Edge}
              local edgeCount::ModelicaInteger
               #= number of edges in the edge list
               =#
              local attributes::List{Attribute}
              local graphNodeKey::String
              local graphEdgeKey::String

              @match GRAPHINFO(graphs = graphs, graphCount = graphCount, nodes = nodes, nodeCount = nodeCount, attributes = attributes, graphNodeKey = graphNodeKey, graphEdgeKey = graphEdgeKey) = iGraphInfo
              ListUtil.map_0(nodes, printNode)
              print("nodeCount: " + intString(nodeCount) + "\\n")
              print("graphCount: " + intString(graphCount) + "\\n")
        end

        function printNode(node::Node)
              local id::String
              local atts::String
              local color::String
              local nodeLabels::List{NodeLabel}
              local shapeType::ShapeType
              local optDesc::Option{String}
              local attValues::List{Tuple{ModelicaInteger, String}}
               #= values of custom attributes (see GRAPH definition). <attributeIndex,attributeValue>
               =#

              @match NODE(id = id, optDesc = optDesc, attValues = attValues) = node
              atts = stringDelimitList(ListUtil.map(attValues, Util.tuple22), " | ")
              print("node: " + id + " desc: " + Util.getOption(optDesc) + "\\n\\tatts: " + atts + "\\n")
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

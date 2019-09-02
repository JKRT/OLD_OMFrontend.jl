  module Constants 


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
         #=  ************************ Modelica 1.x Annotations! *********************** 
         =#

         const annotationsModelica_1_x = "\n\npackage GraphicalAnnotationsProgram____ end GraphicalAnnotationsProgram____;\n\n// Not implemented yet!\n"::String
         #=  ************************ Modelica 2.x Annotations! *********************** 
         =#

         const annotationsModelica_2_x = "\n\npackage GraphicalAnnotationsProgram____  end GraphicalAnnotationsProgram____;\n\n// Constants.diagramProgram:\nrecord GraphicItem\n  Boolean visible=true;\nend GraphicItem;\n\nrecord CoordinateSystem\n  Real extent[2,2];\nend CoordinateSystem;\n\nrecord Diagram\n  CoordinateSystem coordinateSystem(extent={{-100.0,-100.0},{100.0,100.0}});\nend Diagram;\n\ntype LinePattern= enumeration(None, Solid, Dash, Dot, DashDot, DashDotDot );\ntype Arrow= enumeration(None, Open, Filled , Half );\ntype FillPattern= enumeration(None, Solid, Horizontal, Vertical, Cross, Forward, Backward, CrossDiag, HorizontalCylinder, VerticalCylinder, Sphere );\ntype BorderPattern= enumeration(None, Raised, Sunken, Engraved );\ntype TextStyle= enumeration(Bold, Italic, Underline );\n\nrecord Line\n  Boolean visible=true;\n  Real points[:,2];\n  Integer color[3]={0,0,0};\n  LinePattern pattern=LinePattern.Solid;\n  Real thickness=0.25;\n  Arrow arrow[2]={Arrow.None,Arrow.None};\n  Real arrowSize=3.0;\n  Boolean smooth=false;\nend Line;\n\nrecord Polygon\n  Boolean visible=true;\n  Integer lineColor[3]={0,0,0};\n  Integer fillColor[3]={0,0,0};\n  LinePattern pattern=LinePattern.Solid;\n  FillPattern fillPattern=FillPattern.None;\n  Real lineThickness=0.25;\n  Real points[:,2];\n  Boolean smooth=false;\nend Polygon;\n\nrecord Rectangle\n  Boolean visible=true;\n  Integer lineColor[3]={0,0,0};\n  Integer fillColor[3]={0,0,0};\n  LinePattern pattern=LinePattern.Solid;\n  FillPattern fillPattern=FillPattern.None;\n  Real lineThickness=0.25;\n  BorderPattern borderPattern=BorderPattern.None;\n  Real extent[2,2];\n  Real radius=0.0;\nend Rectangle;\n\nrecord Ellipse\n  Boolean visible=true;\n  Integer lineColor[3]={0,0,0};\n  Integer fillColor[3]={0,0,0};\n  LinePattern pattern=LinePattern.Solid;\n  FillPattern fillPattern=FillPattern.None;\n  Real lineThickness=0.25;\n  Real extent[2,2];\nend Ellipse;\n\nrecord Text\n  Boolean visible=true;\n  Integer lineColor[3]={0,0,0};\n  Integer fillColor[3]={0,0,0};\n  LinePattern pattern=LinePattern.Solid;\n  FillPattern fillPattern=FillPattern.None;\n  Real lineThickness=0.25;\n  Real extent[2,2];\n  String textString;\n  Real fontSize=0.0;\n  String fontName=\\\\;\n  TextStyle textStyle[:];\nend Text;\n\nrecord Bitmap\n  Boolean visible=true;\n  Real extent[2,2];\n  String fileName=\\\\;\n  String imageSource=\\\\;\nend Bitmap;\n\n// Constants.iconProgram:\nrecord Icon\n  CoordinateSystem coordinateSystem(extent={{-10.0,-10.0},{10.0,10.0}});\nend Icon;\n\n// Constants.graphicsProgram\n// ...\n// Constants.lineProgram\n// ...\n\n// Constants.placementProgram:\nrecord Transformation\n  Real x=0.0;\n  Real y=0.0;\n  Real scale=1.0;\n  Real aspectRatio=1.0;\n  Boolean flipHorizontal=false;\n  Boolean flipVertical=false;\n  Real rotation=0.0;\nend Transformation;\n\nrecord Placement\n  Boolean visible=true;\n  Transformation transformation;\n  Transformation iconTransformation;\nend Placement;\n\n"::String
         #=  ************************ Modelica 3.x Annotations! *********************** 
         =#

         const annotationsModelica_3_x = "\n\npackage GraphicalAnnotationsProgram____ end     GraphicalAnnotationsProgram____;\n\n// type DrawingUnit = Real/*(final unit=\\mm\\)*/;\n// type Point = DrawingUnit[2] \\{x, y}\\;\n// type Extent = Point[2] \\Defines a rectangular area {{x1, y1}, {x2, y2}}\\;\n\n//partial\nrecord GraphicItem\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation(quantity=\\angle\\, unit=\\deg\\)=0;\nend GraphicItem;\n\nrecord CoordinateSystem\n  Real extent[2,2]/*(each final unit=\\mm\\)*/;\n  Boolean preserveAspectRatio=true;\n  Real initialScale = 0.1;\n  Real grid[2]/*(each final unit=\\mm\\)*/ = {2.0, 2.0};\nend CoordinateSystem;\n\n// example\n// CoordinateSystem(extent = {{-10, -10}, {10, 10}});\n// i.e. a coordinate system with width 20 units and height 20 units.\n\nrecord Icon \\Representation of the icon layer\\\n  CoordinateSystem coordinateSystem(extent = {{-100, -100}, {100, 100}});\n  //GraphicItem[:] graphics;\nend Icon;\n\nrecord Diagram \\Representation of the diagram layer\\\n  CoordinateSystem coordinateSystem(extent = {{-100, -100}, {100, 100}});\n  //GraphicItem[:] graphics;\nend Diagram;\n\ntype Color = Integer[3](each min=0, each max=255) \\RGB representation\\;\n// constant Color Black = {0, 0, 0}; // zeros(3);\ntype LinePattern = enumeration(None, Solid, Dash, Dot, DashDot, DashDotDot);\ntype FillPattern = enumeration(None, Solid, Horizontal, Vertical, Cross, Forward, Backward, CrossDiag, HorizontalCylinder, VerticalCylinder, Sphere);\ntype BorderPattern = enumeration(None, Raised, Sunken, Engraved);\ntype Smooth = enumeration(None, Bezier);\n\ntype Arrow = enumeration(None, Open, Filled, Half);\ntype TextStyle = enumeration(Bold, Italic, UnderLine);\ntype TextAlignment = enumeration(Left, Center, Right);\n\n// Filled shapes have the following attributes for the border and interior.\nrecord FilledShape \\Style attributes for filled shapes\\\n  Integer lineColor[3] = {0, 0, 0} \\Color of border line\\;\n  Integer fillColor[3] = {0, 0, 0} \\Interior fill color\\;\n  LinePattern pattern = LinePattern.Solid \\Border line pattern\\;\n  FillPattern fillPattern = FillPattern.None \\Interior fill pattern\\;\n  Real lineThickness = 0.25 \\Line thickness\\;\nend FilledShape;\n\nrecord Transformation\n  Real origin[2]/*(each final unit=\\mm\\)*/;\n  Real extent[2,2]/*(each final unit=\\mm\\)*/;\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/;\nend Transformation;\n\nrecord Placement\n  Boolean visible = true;\n  Transformation transformation \\Placement in the dagram layer\\;\n  Transformation iconTransformation \\Placement in the icon layer\\;\nend Placement;\n\nrecord IconMap\n  Real extent[2,2]/*(each final unit=\\mm\\)*/ = {{0, 0}, {0, 0}};\n  Boolean primitivesVisible = true;\nend IconMap;\n\nrecord DiagramMap\n  Real extent[2,2]/*(each final unit=\\mm\\)*/ = {{0, 0}, {0, 0}};\n  Boolean primitivesVisible = true;\nend DiagramMap;\n\nrecord Line\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/ = 0;\n  // end GraphicItem\n\n  Real points[:, 2]/*(each final unit=\\mm\\)*/;\n  Integer color[3] = {0, 0, 0};\n  LinePattern pattern = LinePattern.Solid;\n  Real thickness/*(final unit=\\mm\\)*/ = 0.25;\n  Arrow arrow[2] = {Arrow.None, Arrow.None} \\{start arrow, end arrow}\\;\n  Real arrowSize/*(final unit=\\mm\\)*/ = 3;\n  Smooth smooth = Smooth.None \\Spline\\;\nend Line;\n\nrecord Polygon\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/ = 0;\n  // end GraphicItem\n\n  //extends FilledShape;\n  Integer lineColor[3] = {0, 0, 0} \\Color of border line\\;\n  Integer fillColor[3] = {0, 0, 0} \\Interior fill color\\;\n  LinePattern pattern = LinePattern.Solid \\Border line pattern\\;\n  FillPattern fillPattern = FillPattern.None \\Interior fill pattern\\;\n  Real lineThickness = 0.25 \\Line thickness\\;\n  // end FilledShape\n\n  Real points[:,2]/*(each final unit=\\mm\\)*/;\n  Smooth smooth = Smooth.None \\Spline outline\\;\nend Polygon;\n\nrecord Rectangle\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/ = 0;\n  // end GraphicItem\n\n  //extends FilledShape;\n  Integer lineColor[3] = {0, 0, 0} \\Color of border line\\;\n  Integer fillColor[3] = {0, 0, 0} \\Interior fill color\\;\n  LinePattern pattern = LinePattern.Solid \\Border line pattern\\;\n  FillPattern fillPattern = FillPattern.None \\Interior fill pattern\\;\n  Real lineThickness = 0.25 \\Line thickness\\;\n  // end FilledShape\n\n  BorderPattern borderPattern = BorderPattern.None;\n  Real extent[2,2]/*(each final unit=\\mm\\)*/;\n  Real radius/*(final unit=\\mm\\)*/ = 0 \\Corner radius\\;\nend Rectangle;\n\nrecord Ellipse\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/=0;\n  // end GraphicItem\n\n  //extends FilledShape;\n  Integer lineColor[3] = {0, 0, 0} \\Color of border line\\;\n  Integer fillColor[3] = {0, 0, 0} \\Interior fill color\\;\n  LinePattern pattern = LinePattern.Solid \\Border line pattern\\;\n  FillPattern fillPattern = FillPattern.None \\Interior fill pattern\\;\n  Real lineThickness = 0.25 \\Line thickness\\;\n  // end FilledShape\n\n  Real extent[2,2]/*(each final unit=\\mm\\)*/;\n  Real startAngle/*(quantity=\\angle\\, unit=\\deg\\)*/ = 0;\n  Real endAngle/*(quantity=\\angle\\, unit=\\deg\\)*/ = 360;\nend Ellipse;\n\nrecord Text\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/ = 0;\n  // end GraphicItem\n\n  //extends FilledShape;\n  Integer lineColor[3] = {0, 0, 0} \\Color of border line\\;\n  Integer fillColor[3] = {0, 0, 0} \\Interior fill color\\;\n  LinePattern pattern = LinePattern.Solid \\Border line pattern\\;\n  FillPattern fillPattern = FillPattern.None \\Interior fill pattern\\;\n  Real lineThickness = 0.25 \\Line thickness\\;\n  // end FilledShape\n\n  Real extent[2,2]/*(each final unit=\\mm\\)*/ = {{-10, -10}, {10, 10}};\n  String textString = \\\\;\n  Real fontSize = 0 \\unit pt\\;\n  Integer textColor[3] = {-1, -1, -1} \\defaults to fillColor\\;\n  String fontName = \\\\;\n  TextStyle textStyle[:] = fill(TextStyle.Bold, 0);\n  TextAlignment horizontalAlignment = TextAlignment.Center;\nend Text;\n\nrecord Bitmap\n  //extends GraphicItem;\n  Boolean visible = true;\n  Real origin[2]/*(each final unit=\\mm\\)*/ = {0.0, 0.0};\n  Real rotation/*(quantity=\\angle\\, unit=\\deg\\)*/=0;\n  // end GraphicItem\n\n  Real extent[2,2]/*(each final unit=\\mm\\)*/;\n  String fileName = \\\\ \\Name of bitmap file\\;\n  String imageSource =  \\\\ \\Base64 representation of bitmap\\;\nend Bitmap;\n\n// dynamic annotations\n// annotation (\n//   Icon(graphics={Rectangle(\n//     extent=DynamicSelect({{0,0},{20,20}},{{0,0},{20,level}}),\n//     fillColor=DynamicSelect({0,0,255},\n//     if overflow then {255,0,0} else {0,0,255}))}\n//   );\n\n// events & interaction\nrecord OnMouseDownSetBoolean\n   Boolean variable \\Name of variable to change when mouse button pressed\\;\n   Boolean value \\Assigned value\\;\nend OnMouseDownSetBoolean;\n\n// interaction={OnMouseDown(on, true), OnMouseUp(on, false)};\nrecord OnMouseMoveXSetReal\n   Real xVariable \\Name of variable to change when cursor moved in x direction\\;\n   Real minValue;\n   Real maxValue;\nend OnMouseMoveXSetReal;\n\n//\nrecord OnMouseMoveYSetReal\n   Real yVariable \\Name of variable to change when cursor moved in y direction\\;\n   Real minValue;\n   Real maxValue;\nend OnMouseMoveYSetReal;\n\nrecord OnMouseDownEditInteger\n   Integer variable \\Name of variable to change\\;\nend OnMouseDownEditInteger;\n\nrecord OnMouseDownEditReal\n   Real variable \\Name of variable to change\\;\nend OnMouseDownEditReal;\n\n//\nrecord OnMouseDownEditString\n   String variable \\Name of variable to change\\;\nend OnMouseDownEditString;\n\n//\n// annotation(defaultComponentName = \\name\\)\n// annotation(missingInnerMessage = \\message\\)\n//\n// model World\n//   annotation(defaultComponentName = \\world\\,\n//   defaultComponentPrefixes = \\inner replaceable\\,\n//   missingInnerMessage = \\The World object is missing\\);\n// ...\n// end World;\n//\n// inner replaceable World world;\n//\n// annotation(unassignedMessage = \\message\\);\n//\n// annotation(Dialog(enable = parameter-expression, tab = \\tab\\, group = \\group\\));\n//\nrecord Dialog\n   parameter String tab = \\General\\;\n   parameter String group = \\Parameters\\;\n   parameter Boolean enable = true;\n   parameter Boolean showStartAttribute = false;\n   parameter Boolean colorSelector = false;\n   parameter Selector loadSelector;\n   parameter Selector saveSelector;\n   parameter String groupImage = \\\\;\n   parameter Boolean connectorSizing = false;\nend Dialog;\n\nrecord Selector\n  parameter String filter;\n  parameter String caption;\nend Selector;\n\nrecord choices\n  Boolean checkBox = false;\n  Boolean __Dymola_checkBox = false;\nend choices;\n\n//\n// connector Frame \\Frame of a mechanical system\\\n//   ...\n//   flow Modelica.SIunits.Force f[3] annotation(unassignedMessage =\n//    \\All Forces cannot be uniquely calculated. The reason could be that the\n//      mechanism contains a planar loop or that joints constrain the same motion.\n//      For planar loops, use in one revolute joint per loop the option\n//      PlanarCutJoint=true in the Advanced menu.\\);\n// end Frame;\n//\n// model BodyShape\n//   ...\n//   parameter Boolean animation = true;\n//   parameter SI.Length length \\Length of shape\\\n//   annotation(Dialog(enable = animation, tab = \\Animation\\,\n//   group = \\Shape definition\\));\n//   ...\n// end BodyShape;\n"::String
         #= /*
        partial record GraphicItem
          Boolean visible = true;
          Point origin = {0, 0};
          Real rotation(quantity=\"angle\", unit=\"deg\")=0;
        end GraphicItem;

        record CoordinateSystem
          Extent extent;
          Boolean preserveAspectRatio=true;
          Real initialScale = 0.1;
          DrawingUnit grid[2];
        end CoordinateSystem;

         example
         CoordinateSystem(extent = {{-10, -10}, {10, 10}});
         i.e. a coordinate system with width 20 units and height 20 units.

        record Icon \"Representation of the icon layer\"
          CoordinateSystem coordinateSystem(extent = {{-100, -100}, {100, 100}});
          GraphicItem[:] graphics;
        end Icon;

        record Diagram \"Representation of the diagram layer\"
          CoordinateSystem coordinateSystem(extent = {{-100, -100}, {100, 100}});
          GraphicItem[:] graphics;
        end Diagram;

        type Color = Integer[3](min=0, max=255) \"RGB representation\";
        constant Color Black = zeros(3);
        type LinePattern = enumeration(None, Solid, Dash, Dot, DashDot, DashDotDot);
        type FillPattern = enumeration(None, Solid, Horizontal, Vertical, Cross, Forward, Backward, CrossDiag, HorizontalCylinder, VerticalCylinder, Sphere);
        type BorderPattern = enumeration(None, Raised, Sunken, Engraved);
        type Smooth = enumeration(None, Bezier);

        type Arrow = enumeration(None, Open, Filled, Half);
        type TextStyle = enumeration(Bold, Italic, UnderLine);
        type TextAlignment = enumeration(Left, Center, Right);

         Filled shapes have the following attributes for the border and interior.

        record FilledShape \"Style attributes for filled shapes\"
          Color lineColor = Black \"Color of border line\";
          Color fillColor = Black \"Interior fill color\";
          LinePattern pattern = LinePattern.Solid \"Border line pattern\";
          FillPattern fillPattern = FillPattern.None \"Interior fill pattern\";
          DrawingUnit lineThickness = 0.25 \"Line thickness\";
        end FilledShape;

        record Transformation
          Point origin = {0, 0};
          Extent extent;
          Real rotation(quantity=\"angle\", unit=\"deg\")=0;
        end Transformation;

        record Placement
          Boolean visible = true;
          Transformation transformation \"Placement in the dagram layer\";
          Transformation iconTransformation \"Placement in the icon layer\";
        end Placement;

        record IconMap
          Extent extent = {{0, 0}, {0, 0}};
          Boolean primitivesVisible = true;
        end IconMap;

        record DiagramMap
          Extent extent = {{0, 0}, {0, 0}};
          Boolean primitivesVisible = true;
        end DiagramMap;

        record Line
          extends GraphicItem;
          Point points[:];
          Color color = Black;
          LinePattern pattern = LinePattern.Solid;
          DrawingUnit thickness = 0.25;
          Arrow arrow[2] = {Arrow.None, Arrow.None} \"{start arrow, end arrow}\";
          DrawingUnit arrowSize=3;
          Smooth smooth = Smooth.None \"Spline\";
        end Line;

        record Polygon
          extends GraphicItem;
          extends FilledShape;
          Point points[:];
          Smooth smooth = Smooth.None \"Spline outline\";
        end Polygon;

        record Ellipse
          extends GraphicItem;
          extends FilledShape;
          Extent extent;
          Real startAngle(quantity=\"angle\", unit=\"deg\")=0;
          Real endAngle(quantity=\"angle\", unit=\"deg\")=360;
        end Ellipse;

        record Text
          extends GraphicItem;
          extends FilledShape;
          Extent extent;
          String textString;
          Real fontSize = 0 \"unit pt\";
          String fontName;
          TextStyle textStyle[:];
          TextAlignment horizontalAlignment = TextAlignment.Center;
        end Text;

        record Bitmap
          extends GraphicItem;
          Extent extent;
          String fileName \"Name of bitmap file\";
          String imageSource \"Base64 representation of bitmap\";
        end Bitmap;
        */ =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
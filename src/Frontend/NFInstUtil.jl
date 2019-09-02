  module NFInstUtil 


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

        import DAE

        import SCode

        import Absyn

        function daeToSCodeConnectorType(inConnectorType::DAE.ConnectorType) ::SCode.ConnectorType 
              local outConnectorType::SCode.ConnectorType

              outConnectorType = begin
                @match inConnectorType begin
                  DAE.NON_CONNECTOR(__)  => begin
                    SCode.POTENTIAL()
                  end
                  
                  DAE.POTENTIAL(__)  => begin
                    SCode.POTENTIAL()
                  end
                  
                  DAE.FLOW(__)  => begin
                    SCode.FLOW()
                  end
                  
                  DAE.STREAM(__)  => begin
                    SCode.STREAM()
                  end
                end
              end
          outConnectorType
        end

        function daeToSCodeParallelism(inParallelism::DAE.VarParallelism) ::SCode.Parallelism 
              local outParallelism::SCode.Parallelism

              outParallelism = begin
                @match inParallelism begin
                  DAE.PARGLOBAL(__)  => begin
                    SCode.PARGLOBAL()
                  end
                  
                  DAE.PARLOCAL(__)  => begin
                    SCode.PARLOCAL()
                  end
                  
                  DAE.NON_PARALLEL(__)  => begin
                    SCode.NON_PARALLEL()
                  end
                end
              end
          outParallelism
        end

        function daeToSCodeVariability(inVariability::DAE.VarKind) ::SCode.Variability 
              local outVariability::SCode.Variability

              outVariability = begin
                @match inVariability begin
                  DAE.VARIABLE(__)  => begin
                    SCode.VAR()
                  end
                  
                  DAE.DISCRETE(__)  => begin
                    SCode.DISCRETE()
                  end
                  
                  DAE.PARAM(__)  => begin
                    SCode.PARAM()
                  end
                  
                  DAE.CONST(__)  => begin
                    SCode.CONST()
                  end
                end
              end
          outVariability
        end

        function daeToAbsynDirection(inDirection::DAE.VarDirection) ::Absyn.Direction 
              local outDirection::Absyn.Direction

              outDirection = begin
                @match inDirection begin
                  DAE.BIDIR(__)  => begin
                    Absyn.BIDIR()
                  end
                  
                  DAE.INPUT(__)  => begin
                    Absyn.INPUT()
                  end
                  
                  DAE.OUTPUT(__)  => begin
                    Absyn.OUTPUT()
                  end
                end
              end
          outDirection
        end

        function daeToAbsynInnerOuter(inInnerOuter::DAE.VarInnerOuter) ::Absyn.InnerOuter 
              local outInnerOuter::Absyn.InnerOuter

              outInnerOuter = begin
                @match inInnerOuter begin
                  DAE.INNER(__)  => begin
                    Absyn.INNER()
                  end
                  
                  DAE.INNER_OUTER(__)  => begin
                    Absyn.INNER_OUTER()
                  end
                  
                  DAE.OUTER(__)  => begin
                    Absyn.OUTER()
                  end
                  
                  DAE.NOT_INNER_OUTER(__)  => begin
                    Absyn.NOT_INNER_OUTER()
                  end
                end
              end
          outInnerOuter
        end

        function daeToSCodeVisibility(inVisibility::DAE.VarVisibility) ::SCode.Visibility 
              local outVisibility::SCode.Visibility

              outVisibility = begin
                @match inVisibility begin
                  DAE.PUBLIC(__)  => begin
                    SCode.PUBLIC()
                  end
                  
                  DAE.PROTECTED(__)  => begin
                    SCode.PROTECTED()
                  end
                end
              end
          outVisibility
        end

        function translateConnectorType(inConnectorType::SCode.ConnectorType) ::DAE.ConnectorType 
              local outConnectorType::DAE.ConnectorType

              outConnectorType = begin
                @match inConnectorType begin
                  SCode.FLOW(__)  => begin
                    DAE.FLOW()
                  end
                  
                  SCode.STREAM(__)  => begin
                    DAE.STREAM(NONE())
                  end
                  
                  _  => begin
                      DAE.NON_CONNECTOR()
                  end
                end
              end
          outConnectorType
        end

        function translateParallelism(inParallelism::SCode.Parallelism) ::DAE.VarParallelism 
              local outParallelism::DAE.VarParallelism

              outParallelism = begin
                @match inParallelism begin
                  SCode.PARGLOBAL(__)  => begin
                    DAE.PARGLOBAL()
                  end
                  
                  SCode.PARLOCAL(__)  => begin
                    DAE.PARLOCAL()
                  end
                  
                  SCode.NON_PARALLEL(__)  => begin
                    DAE.NON_PARALLEL()
                  end
                end
              end
          outParallelism
        end

        function translateVariability(inVariability::SCode.Variability) ::DAE.VarKind 
              local outVariability::DAE.VarKind

              outVariability = begin
                @match inVariability begin
                  SCode.VAR(__)  => begin
                    DAE.VARIABLE()
                  end
                  
                  SCode.PARAM(__)  => begin
                    DAE.PARAM()
                  end
                  
                  SCode.CONST(__)  => begin
                    DAE.CONST()
                  end
                  
                  SCode.DISCRETE(__)  => begin
                    DAE.DISCRETE()
                  end
                end
              end
          outVariability
        end

        function translateDirection(inDirection::Absyn.Direction) ::DAE.VarDirection 
              local outDirection::DAE.VarDirection

              outDirection = begin
                @match inDirection begin
                  Absyn.BIDIR(__)  => begin
                    DAE.BIDIR()
                  end
                  
                  Absyn.OUTPUT(__)  => begin
                    DAE.OUTPUT()
                  end
                  
                  Absyn.INPUT(__)  => begin
                    DAE.INPUT()
                  end
                end
              end
          outDirection
        end

        function translateInnerOuter(inInnerOuter::Absyn.InnerOuter) ::DAE.VarInnerOuter 
              local outInnerOuter::DAE.VarInnerOuter

              outInnerOuter = begin
                @match inInnerOuter begin
                  Absyn.INNER(__)  => begin
                    DAE.INNER()
                  end
                  
                  Absyn.INNER_OUTER(__)  => begin
                    DAE.INNER_OUTER()
                  end
                  
                  Absyn.OUTER(__)  => begin
                    DAE.OUTER()
                  end
                  
                  Absyn.NOT_INNER_OUTER(__)  => begin
                    DAE.NOT_INNER_OUTER()
                  end
                end
              end
          outInnerOuter
        end

        function translateVisibility(inVisibility::SCode.Visibility) ::DAE.VarVisibility 
              local outVisibility::DAE.VarVisibility

              outVisibility = begin
                @match inVisibility begin
                  SCode.PUBLIC(__)  => begin
                    DAE.PUBLIC()
                  end
                  
                  _  => begin
                      DAE.PROTECTED()
                  end
                end
              end
          outVisibility
        end

         #= Translates SCode.Variability to DAE.Const =#
        function toConst(inVar::SCode.Variability) ::DAE.Const 
              local outConst::DAE.Const

              outConst = begin
                @match inVar begin
                  SCode.CONST(__)  => begin
                    DAE.C_CONST()
                  end
                  
                  SCode.PARAM(__)  => begin
                    DAE.C_PARAM()
                  end
                  
                  _  => begin
                      DAE.C_VAR()
                  end
                end
              end
          outConst
        end

         #= Returns the most variable of two VarKinds. =#
        function variabilityAnd(var1::DAE.VarKind, var2::DAE.VarKind) ::DAE.VarKind 
              local var::DAE.VarKind

              var = begin
                @match (var1, var2) begin
                  (DAE.VarKind.VARIABLE(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.VARIABLE(__))  => begin
                    var2
                  end
                  
                  (DAE.VarKind.DISCRETE(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.DISCRETE(__))  => begin
                    var2
                  end
                  
                  (DAE.VarKind.PARAM(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.PARAM(__))  => begin
                    var2
                  end
                  
                  _  => begin
                      var1
                  end
                end
              end
          var
        end

         #= Returns the least variable of two VarKinds. =#
        function variabilityOr(var1::DAE.VarKind, var2::DAE.VarKind) ::DAE.VarKind 
              local var::DAE.VarKind

              var = begin
                @match (var1, var2) begin
                  (DAE.VarKind.CONST(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.CONST(__))  => begin
                    var2
                  end
                  
                  (DAE.VarKind.PARAM(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.PARAM(__))  => begin
                    var2
                  end
                  
                  (DAE.VarKind.DISCRETE(__), _)  => begin
                    var1
                  end
                  
                  (_, DAE.VarKind.DISCRETE(__))  => begin
                    var2
                  end
                  
                  _  => begin
                      var1
                  end
                end
              end
          var
        end

        function variabilityString(var::DAE.VarKind) ::String 
              local string::String

              string = begin
                @match var begin
                  DAE.VarKind.CONST(__)  => begin
                    "constant"
                  end
                  
                  DAE.VarKind.PARAM(__)  => begin
                    "parameter"
                  end
                  
                  DAE.VarKind.DISCRETE(__)  => begin
                    "discrete"
                  end
                  
                  DAE.VarKind.VARIABLE(__)  => begin
                    "continuous"
                  end
                end
              end
          string
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
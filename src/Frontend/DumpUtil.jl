  module DumpUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl DumpOptions

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
        
         #=  protected imports
         =#

         @Uniontype DumpOptions begin
              @Record DUMPOPTIONS begin

                       fileName::String
              end
         end

         const defaultDumpOptions = DUMPOPTIONS("")::DumpOptions

         #= Returns true if the filename in the SOURCEINFO should be unparsed =#
        function boolUnparseFileFromInfo(info::SourceInfo, options::DumpOptions) ::Bool
              local b::Bool

              b = begin
                @match (options, info) begin
                  (DUMPOPTIONS(fileName = ""), _)  => begin
                    true
                  end

                  (DUMPOPTIONS(__), SOURCEINFO(__))  => begin
                    options.fileName == info.fileName
                  end
                end
              end
               #=  The default is to not filter
               =#
          b
        end

         #= Determines whether an operand in an expression needs parentheses around it. =#
        function shouldParenthesize(inOperand::Absyn.Exp, inOperator::Absyn.Exp, inLhs::Bool) ::Bool
              local outShouldParenthesize::Bool

              outShouldParenthesize = begin
                  local diff::ModelicaInteger
                @match (inOperand, inOperator, inLhs) begin
                  (Absyn.UNARY(__), _, _)  => begin
                    true
                  end

                  _  => begin
                        diff = Util.intCompare(expPriority(inOperand, inLhs), expPriority(inOperator, inLhs))
                      shouldParenthesize2(diff, inOperand, inLhs)
                  end
                end
              end
          outShouldParenthesize
        end

        function shouldParenthesize2(inPrioDiff::ModelicaInteger, inOperand::Absyn.Exp, inLhs::Bool) ::Bool
              local outShouldParenthesize::Bool

              outShouldParenthesize = begin
                @match (inPrioDiff, inOperand, inLhs) begin
                  (1, _, _)  => begin
                    true
                  end

                  (0, _, false)  => begin
                    ! isAssociativeExp(inOperand)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outShouldParenthesize
        end

        function isClassdef(inElement::Absyn.Element) ::Bool
              local b::Bool

              b = begin
                @match inElement begin
                  Absyn.ELEMENT(specification = Absyn.CLASSDEF(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

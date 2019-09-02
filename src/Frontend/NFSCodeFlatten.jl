  module NFSCodeFlatten 


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

        import Absyn

        import AbsynUtil

        import SCode

        import NFSCodeDependency

        import NFSCodeEnv

        import NFSCodeFlattenImports

        import Debug

        import NFEnvExtends

        import Flags

        import ListUtil

        import System

        Env = NFSCodeEnv.Env 

         #= Flattens the last class in a program. =#
        function flattenProgram(inProgram::SCode.Program) ::SCode.Program 
              local outProgram::SCode.Program

              local cls_path::Absyn.Path

              cls_path = getLastClassNameInProgram(inProgram)
              (outProgram, _) = flattenClassInProgram(cls_path, inProgram)
          outProgram
        end

         #= Returns the name of the last class in the program. =#
        function getLastClassNameInProgram(inProgram::SCode.Program) ::Absyn.Path 
              local outClassName::Absyn.Path

              local prog::SCode.Program
              local name::String

              prog = listReverse(inProgram)
              @match SCode.CLASS(name = name) = ListUtil.find(prog, isClass)
              outClassName = Absyn.IDENT(name)
          outClassName
        end

         #= Checks if the given SCode.Class is a class, i.e. not a function. =#
        function isClass(inClass::SCode.Element) ::Bool 
              local outIsClass::Bool

              outIsClass = begin
                @match inClass begin
                  SCode.CLASS(restriction = SCode.R_FUNCTION(_))  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          outIsClass
        end

         #= Flattens a single class. =#
        function flattenClass(inClass::SCode.Element) ::SCode.Element 
              local outClass::SCode.Element

              @match list(outClass) = flattenProgram(list(inClass))
          outClass
        end

         #= Flattens a specific class in a program. =#
        function flattenClassInProgram(inClassName::Absyn.Path, inProgram::SCode.Program) ::Tuple{SCode.Program, Env} 
              local outEnv::Env
              local outProgram::SCode.Program

              (outProgram, outEnv) = begin
                  local env::Env
                  local prog::SCode.Program
                @matchcontinue (inClassName, inProgram) begin
                  (_, prog)  => begin
                      System.tmpTickResetIndex(0, NFSCodeEnv.tmpTickIndex)
                      System.tmpTickResetIndex(1, NFSCodeEnv.extendsTickIndex)
                      System.setUsesCardinality(false)
                      env = NFSCodeEnv.buildInitialEnv()
                      env = NFSCodeEnv.extendEnvWithClasses(prog, env)
                      env = NFEnvExtends.update(env)
                      (prog, env) = NFSCodeDependency.analyse(inClassName, env, prog)
                      if ! Flags.isSet(Flags.SCODE_INST)
                        (prog, env) = NFSCodeFlattenImports.flattenProgram(prog, env)
                      end
                    (prog, env)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("NFSCodeFlatten.flattenClassInProgram failed on " + AbsynUtil.pathString(inClassName))
                      fail()
                  end
                end
              end
               #= System.stopTimer();
               =#
               #= Debug.traceln(\"NFSCodeFlatten.flattenClassInProgram took \" +
               =#
               #=   realString(System.getTimerIntervalTime()) + \" seconds\");
               =#
          (outProgram, outEnv)
        end

        function flattenCompleteProgram(inProgram::SCode.Program) ::SCode.Program 
              local outProgram::SCode.Program

              outProgram = begin
                  local env::Env
                  local prog::SCode.Program
                @matchcontinue inProgram begin
                  prog  => begin
                      env = NFSCodeEnv.buildInitialEnv()
                      env = NFSCodeEnv.extendEnvWithClasses(prog, env)
                      env = NFEnvExtends.update(env)
                      (prog, env) = NFSCodeFlattenImports.flattenProgram(prog, env)
                    prog
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("NFSCodeFlatten.flattenCompleteProgram failed\\n")
                      fail()
                  end
                end
              end
          outProgram
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
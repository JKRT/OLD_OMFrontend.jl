  module NFEnvExtends 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl ExtendsWrapper 

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

        import NFSCodeEnv

        import Debug

        import Error

        import Flags

        import ListUtil

        import NFSCodeCheck

        import SCodeDump
        import SCodeUtil

        import NFSCodeFlattenRedeclare

        import NFSCodeLookup

        import System

        import Util

        Env = NFSCodeEnv.Env 

        ClassType = NFSCodeEnv.ClassType 

        Extends = NFSCodeEnv.Extends 

        Frame = NFSCodeEnv.Frame 

        FrameType = NFSCodeEnv.FrameType 

        Import = Absyn.Import 

        Item = NFSCodeEnv.Item 

        ExtendsTableArray = Array 
        import NFSCodeEnv.EnvTree

         const BASECLASS_NOT_FOUND_ERROR = "1"::String

         const BASECLASS_INHERITED_ERROR = "2"::String

         const BASECLASS_REPLACEABLE_ERROR = "3"::String

         const BASECLASS_IS_VAR_ERROR = "4"::String

         const BASECLASS_UNKNOWN_ERROR = "5"::String

         @Uniontype ExtendsWrapper begin
              @Record UNQUALIFIED_EXTENDS begin

                       ext::Extends
              end

              @Record QUALIFIED_EXTENDS begin

                       ext::Extends
              end

              @Record NO_EXTENDS begin

              end
         end

         #= While building the environment some extends information is stored that needs
           to be updated once the environment is complete, since we can't reliably look
           things up in an incomplete environment. This includes fully qualifying the
           names of the extended classes, updating the class extends base classes and
           inserting element redeclares into the proper extends. =#
        function update(inEnv::Env) ::Env 
              local outEnv::Env

              local env::Env

               #= System.startTimer();
               =#
              env = qualify(inEnv)
              outEnv = update2(env)
               #= System.stopTimer();
               =#
               #= print(\"Updating extends took \" + realString(System.getTimerIntervalTime()) + \" seconds.\\n\");
               =#
          outEnv
        end

         #= Fully qualified all base class names using in extends clauses. This is done
           to avoid some cases where the lookup might exhibit exponential complexity
           with regards to the nesting depth of classes. One such case is the pattern
           used in the MSL, where every class extends from a class in Modelica.Icons:

             package Modelica
               package Icons end Icons;

               package A
                 extends Modelica.Icons.foo;
                 package B
                   extends Modelica.Icons.bar;
                   package C
                     ...
                   end C;
                end B;
              end A;

           To look a name up in C that references a name in the top scope we need to
           first look in C. When the name is not found there we look in B, which extends
           Modelica.Icons.bar. We then need to look for Modelica in B, and then Modelica
           in A, which extends Modelica.Icons.foo. We then need to follow that extends,
           and look for Modelica in A, etc. This means that we need to look up 2^n
           extends to find a relative name at the top scope. By fully qualifying the
           base class names we avoid these problems. =#
        function qualify(inEnv::Env) ::Env 
              local outEnv::Env

              outEnv = begin
                  local ext_count::ModelicaInteger
                  local ext_table::ExtendsTableArray
                @matchcontinue inEnv begin
                  _  => begin
                      ext_count = System.tmpTickIndex(NFSCodeEnv.extendsTickIndex)
                      ext_table = createExtendsTable(ext_count)
                    qualify2(inEnv, NFSCodeEnv.USERDEFINED(), ext_table)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFEnvExtends.qualify failed.")
                      fail()
                  end
                end
              end
          outEnv
        end

        function qualify2(inEnv::Env, inClassType::ClassType, inExtendsTable::ExtendsTableArray) ::Env 
              local outEnv::Env

              local exts::List{Extends}
              local re::List{SCode.Element}
              local cei::Option{SCode.Element}
              local env::Env
              local tree::EnvTree.Tree

               #=  Qualify the extends in this scope.
               =#
              env = qualifyLocalScope(inEnv, inClassType, inExtendsTable)
               #=  Recurse down the tree.
               =#
              @match _cons(NFSCodeEnv.FRAME(clsAndVars = tree), _) = env
              tree = EnvTree.map(tree, (env, inExtendsTable) -> qualify3(inEnv = env, inExtendsTable = inExtendsTable))
              outEnv = NFSCodeEnv.setEnvClsAndVars(tree, env)
          outEnv
        end

        function qualify3(name::String, item::Item, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Item 


              item = begin
                  local cls::SCode.Element
                  local cls_env::Frame
                  local cls_ty::ClassType
                  local env::Env
                  local rest_env::Env
                @match item begin
                  NFSCodeEnv.CLASS(cls, cls_env <|  nil(), cls_ty)  => begin
                      env = NFSCodeEnv.enterFrame(cls_env, inEnv)
                      @match _cons(cls_env, _) = qualify2(env, cls_ty, inExtendsTable)
                    NFSCodeEnv.CLASS(cls, list(cls_env), cls_ty)
                  end
                  
                  _  => begin
                      item
                  end
                end
              end
          item
        end

        function qualifyLocalScope(inEnv::Env, inClassType::ClassType, inExtendsTable::ExtendsTableArray) ::Env 
              local outEnv::Env

              local exts::List{Extends}
              local re::List{SCode.Element}
              local cei::Option{SCode.Element}

              @match NFSCodeEnv.EXTENDS_TABLE(exts, re, cei) = NFSCodeEnv.getEnvExtendsTable(inEnv)
              exts = qualifyExtendsList(exts, inClassType, inEnv, inExtendsTable)
              outEnv = NFSCodeEnv.setEnvExtendsTable(NFSCodeEnv.EXTENDS_TABLE(exts, re, cei), inEnv)
          outEnv
        end

        function qualifyExtendsList(inExtends::List{<:Extends}, inClassType::ClassType, inEnv::Env, inExtendsTable::ExtendsTableArray) ::List{Extends} 
              local outExtends::List{Extends}

              outExtends = begin
                  local ext::Extends
                  local extl::List{Extends}
                   #=  Skip the first extends in a class extends, since it's added by the
                   =#
                   #=  compiler itself and shouldn't be qualified.
                   =#
                @match (inExtends, inClassType, inEnv, inExtendsTable) begin
                  (ext <| extl, NFSCodeEnv.CLASS_EXTENDS(__), _, _)  => begin
                      extl = ListUtil.map2Reverse(extl, qualifyExtends, inEnv, inExtendsTable)
                    _cons(ext, extl)
                  end
                  
                  _  => begin
                        extl = ListUtil.map2Reverse(inExtends, qualifyExtends, inEnv, inExtendsTable)
                      extl
                  end
                end
              end
               #=  Otherwise, qualify all the extends.
               =#
          outExtends
        end

        function qualifyExtends(inExtends::Extends, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Extends 
              local outExtends::Extends

              outExtends = begin
                  local id::Absyn.Ident
                  local ext::Extends
                  local bc::Absyn.Path
                   #=  Check if the base class is a built in type such as Real, then we don't
                   =#
                   #=  need to do anything.
                   =#
                @matchcontinue (inExtends, inEnv, inExtendsTable) begin
                  (NFSCodeEnv.EXTENDS(baseClass = Absyn.IDENT(name = id)), _, _)  => begin
                      _ = NFSCodeLookup.lookupBuiltinType(id)
                    inExtends
                  end
                  
                  (_, _, _)  => begin
                      @match SOME(ext) = qualifyExtends2(inExtends, inEnv, inExtendsTable)
                    ext
                  end
                  
                  (NFSCodeEnv.EXTENDS(baseClass = bc), _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- NFEnvExtends.qualifyExtends failed on " + AbsynUtil.pathString(bc) + "\\n")
                    fail()
                  end
                end
              end
          outExtends
        end

        function qualifyExtends2(inExtends::Extends, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Option{Extends} 
              local outExtends::Option{Extends}

              outExtends = begin
                  local bc::Absyn.Path
                  local rl::List{NFSCodeEnv.Redeclaration}
                  local index::ModelicaInteger
                  local info::SourceInfo
                  local ext::Extends
                  local env::Env
                @matchcontinue (inExtends, inEnv, inExtendsTable) begin
                  (NFSCodeEnv.EXTENDS(index = index), _, _)  => begin
                    lookupQualifiedExtends(index, inExtendsTable)
                  end
                  
                  (NFSCodeEnv.EXTENDS(bc, rl, index, info), _, _)  => begin
                      addUnqualifiedToTable(inExtends, index, inExtendsTable)
                      env = NFSCodeEnv.removeExtendFromLocalScope(bc, inEnv)
                      bc = qualifyExtends3(bc, env, inExtendsTable, true, bc, info, NONE())
                      ListUtil.map2_0(rl, NFSCodeCheck.checkRedeclareModifier, bc, inEnv)
                      ext = NFSCodeEnv.EXTENDS(bc, rl, index, info)
                      updateQualifiedInTable(ext, index, inExtendsTable)
                    SOME(ext)
                  end
                end
              end
               #= /*********************************************************************/ =#
               #=  TODO: Convert this check to the delayed error system.
               =#
               #= /*********************************************************************/ =#
          outExtends
        end

        function qualifyExtends3(inBaseClass::Absyn.Path, inEnv::Env, inExtendsTable::ExtendsTableArray, inIsFirst::Bool, inFullPath::Absyn.Path, inInfo::SourceInfo, inErrorPath::Option{<:Absyn.Path}) ::Absyn.Path 
              local outBaseClass::Absyn.Path

              outBaseClass = begin
                  local name::String
                  local bc::Absyn.Path
                  local rest_path::Absyn.Path
                  local env::Env
                  local ep::Option{Absyn.Path}
                  local opath::Option{Absyn.Path}
                @match (inBaseClass, inEnv, inExtendsTable, inIsFirst, inFullPath, inInfo, inErrorPath) begin
                  (_, _, _, _, _, _, SOME(bc))  => begin
                    bc
                  end
                  
                  (Absyn.IDENT(name = name), _, _, _, _, _, _)  => begin
                      (opath, env, ep) = qualifyExtendsPart(name, inEnv, inExtendsTable, inIsFirst, inFullPath, inInfo)
                    makeExtendsPath(opath, NONE(), env, ep, inIsFirst)
                  end
                  
                  (Absyn.QUALIFIED(name = name, path = rest_path), _, _, _, _, _, _)  => begin
                      (opath, env, ep) = qualifyExtendsPart(name, inEnv, inExtendsTable, inIsFirst, inFullPath, inInfo)
                      rest_path = qualifyExtends3(rest_path, env, inExtendsTable, false, inFullPath, inInfo, ep)
                    makeExtendsPath(opath, SOME(rest_path), env, ep, inIsFirst)
                  end
                  
                  (Absyn.FULLYQUALIFIED(path = rest_path), _, _, _, _, _, _)  => begin
                      env = NFSCodeEnv.getEnvTopScope(inEnv)
                    qualifyExtends3(rest_path, env, inExtendsTable, inIsFirst, rest_path, inInfo, NONE())
                  end
                end
              end
          outBaseClass
        end

        function makeExtendsPath(inFirstPath::Option{<:Absyn.Path}, inRestPath::Option{<:Absyn.Path}, inEnv::Env, inErrorPath::Option{<:Absyn.Path}, inIsFirst::Bool) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local path::Absyn.Path
                   #=  If an error has occured, return the error path.
                   =#
                @match (inFirstPath, inRestPath, inEnv, inErrorPath, inIsFirst) begin
                  (_, _, _, SOME(path), _)  => begin
                    path
                  end
                  
                  (_, SOME(path && Absyn.QUALIFIED(name = "$E")), _, _, _)  => begin
                    path
                  end
                  
                  (_, SOME(path && Absyn.FULLYQUALIFIED(__)), _, _, _)  => begin
                    path
                  end
                  
                  (_, _, _, _, true)  => begin
                      path = NFSCodeEnv.getEnvPath(inEnv)
                      path = AbsynUtil.joinPathsOptSuffix(path, inRestPath)
                      path = AbsynUtil.makeFullyQualified(path)
                    path
                  end
                  
                  (SOME(path), _, _, _, _)  => begin
                    AbsynUtil.joinPathsOptSuffix(path, inRestPath)
                  end
                end
              end
               #=  If the rest of the path is fully qualified it overwrites everything before.
               =#
               #=  If inFirstPath is the very first part of the path, use the environment to
               =#
               #=  get the whole path.
               =#
               #=  Otherwise, just join them.
               =#
          outPath
        end

        function qualifyExtendsPart(inName::String, inEnv::Env, inExtendsTable::ExtendsTableArray, inIsFirst::Bool, inFullPath::Absyn.Path, inInfo::SourceInfo) ::Tuple{Option{Absyn.Path}, Env, Option{Absyn.Path}} 
              local outErrorPath::Option{Absyn.Path}
              local outEnv::Env
              local outPath::Option{Absyn.Path}

              local oitem::Option{Item}
              local oenv::Option{Env}
              local fe::Bool

              (oitem, outPath, oenv, fe) = lookupSimpleName(inName, inEnv, inExtendsTable)
              (outEnv, outErrorPath) = qualifyExtendsPart2(Absyn.IDENT(inName), oitem, oenv, inEnv, inIsFirst, fe, inFullPath)
          (outPath, outEnv, outErrorPath)
        end

        function qualifyExtendsPart2(inPartName::Absyn.Path, inItem::Option{<:Item}, inFoundEnv::Option{<:Env}, inOriginEnv::Env, inIsFirst::Bool, inFromExtends::Bool, inFullPath::Absyn.Path) ::Tuple{Env, Option{Absyn.Path}} 
              local outErrorPath::Option{Absyn.Path}
              local outEnv::Env

              (outEnv, outErrorPath) = begin
                  local item::Item
                  local env::Env
                  local ep::Option{Absyn.Path}
                @match (inPartName, inItem, inFoundEnv, inOriginEnv, inIsFirst, inFromExtends, inFullPath) begin
                  (_, SOME(item), SOME(env), _, _, _, _)  => begin
                      ep = checkExtendsPart(inIsFirst, inFromExtends, inPartName, item, inFullPath, env, inOriginEnv)
                      env = NFSCodeEnv.mergeItemEnv(item, env)
                    (env, ep)
                  end
                  
                  _  => begin
                      (NFSCodeEnv.emptyEnv, makeExtendsError(inFullPath, inPartName, BASECLASS_NOT_FOUND_ERROR))
                  end
                end
              end
          (outEnv, outErrorPath)
        end

        function makeExtendsError(inBaseClass::Absyn.Path, inPart::Absyn.Path, inError::String) ::Option{Absyn.Path} 
              local outError::Option{Absyn.Path}

              outError = begin
                  local path::Absyn.Path
                @match (inBaseClass, inPart, inError) begin
                  (_, _, _)  => begin
                      path = AbsynUtil.joinPaths(inPart, Absyn.QUALIFIED("bc", inBaseClass))
                      path = Absyn.QUALIFIED("E", Absyn.QUALIFIED(inError, path))
                    SOME(path)
                  end
                end
              end
          outError
        end

         #= This function checks that part of a base class name is correct. If it is not
           correct it returns an error path on the form $E.$N.part_path.$bc.base_class.
           $N, where N is an integer, defined the actual error as defined by the error
           constants at the beginning of this file. part_path is the path of the part
           which the error occured in, and base_class is the path of the base class as
           declared in the code. This is used by printExtendsError to print an
           appropriate error when needed. =#
        function checkExtendsPart(inIsFirst::Bool, inFromExtends::Bool, inPartName::Absyn.Path, inItem::Item, inBaseClass::Absyn.Path, inFoundEnv::Env, inOriginEnv::Env) ::Option{Absyn.Path} 
              local outErrorPath::Option{Absyn.Path}

              outErrorPath = begin
                  local part::Absyn.Path
                   #=  The first part of the base class name may not be inherited.
                   =#
                @matchcontinue (inIsFirst, inFromExtends, inPartName, inItem, inBaseClass, inFoundEnv, inOriginEnv) begin
                  (true, true, _, _, _, _, _)  => begin
                    makeExtendsError(inBaseClass, inPartName, BASECLASS_INHERITED_ERROR)
                  end
                  
                  (_, _, _, NFSCodeEnv.CLASS(__), _, _, _)  => begin
                    NONE()
                  end
                  
                  (_, _, _, NFSCodeEnv.VAR(__), _, _, _)  => begin
                      part = NFSCodeEnv.mergePathWithEnvPath(inPartName, inFoundEnv)
                    makeExtendsError(inBaseClass, part, BASECLASS_IS_VAR_ERROR)
                  end
                  
                  _  => begin
                      makeExtendsError(inBaseClass, inPartName, BASECLASS_UNKNOWN_ERROR)
                  end
                end
              end
               #=  Not inherited class, ok!
               =#
               #=  The base class part is actually not a class but a component, which is not
               =#
               #=  allowed either.
               =#
               #=  We shouldn't get here.
               =#
          outErrorPath
        end

        function splitExtendsErrorPath(inPath::Absyn.Path) ::Tuple{Absyn.Path, Absyn.Path} 
              local outPartPath::Absyn.Path
              local outBaseClass::Absyn.Path

              (outBaseClass, outPartPath) = begin
                  local part_str::String
                  local part::Absyn.Path
                  local bc::Absyn.Path
                @match inPath begin
                  Absyn.QUALIFIED(part_str, Absyn.QUALIFIED("$bc", bc))  => begin
                    (bc, Absyn.IDENT(part_str))
                  end
                  
                  Absyn.QUALIFIED(part_str, part)  => begin
                      (bc, part) = splitExtendsErrorPath(part)
                    (bc, Absyn.QUALIFIED(part_str, part))
                  end
                end
              end
          (outBaseClass, outPartPath)
        end

        function printExtendsError(inErrorPath::Absyn.Path, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local err_str::String
                  local bc::Absyn.Path
                  local part::Absyn.Path
                  local env::Env
                @matchcontinue (inErrorPath, inEnv, inInfo) begin
                  (Absyn.QUALIFIED(name = "$E", path = Absyn.QUALIFIED(name = err_str, path = bc)), _, _)  => begin
                      (bc, part) = splitExtendsErrorPath(bc)
                      env = NFSCodeEnv.removeExtendFromLocalScope(inErrorPath, inEnv)
                      printExtendsError2(err_str, bc, part, env, inInfo)
                    ()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFEnvExtends.printExtendsError failed to print error " + AbsynUtil.pathString(inErrorPath))
                      fail()
                  end
                end
              end
        end

        function printExtendsError2(inError::String, inBaseClass::Absyn.Path, inPartPath::Absyn.Path, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local bc_str::String
                  local env_str::String
                  local part::String
                  local exts::List{Extends}
                  local msg::Error.Message
                  local info::SourceInfo
                @matchcontinue (inError, inBaseClass, inPartPath, inEnv, inInfo) begin
                  (_, _, _, _, _)  => begin
                      @match true = stringEq(inError, BASECLASS_NOT_FOUND_ERROR)
                      bc_str = AbsynUtil.pathString(inBaseClass)
                      env_str = NFSCodeEnv.getEnvName(inEnv)
                      Error.addSourceMessage(Error.LOOKUP_BASECLASS_ERROR, list(bc_str, env_str), inInfo)
                    ()
                  end
                  
                  (_, _, Absyn.IDENT(part), _, _)  => begin
                      @match true = stringEq(inError, BASECLASS_INHERITED_ERROR)
                      bc_str = AbsynUtil.pathString(inBaseClass)
                      Error.addSourceMessage(Error.INHERITED_EXTENDS, list(bc_str), inInfo)
                      exts = NFSCodeEnv.getEnvExtendsFromTable(inEnv)
                      printInheritedExtendsError(part, exts, inEnv)
                    ()
                  end
                  
                  (_, _, _, _, _)  => begin
                      @match true = stringEq(inError, BASECLASS_REPLACEABLE_ERROR)
                      @match (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = part, info = info)), _, _) = NFSCodeLookup.lookupFullyQualified(inPartPath, inEnv)
                      bc_str = AbsynUtil.pathString(inBaseClass)
                      msg = if bc_str == part
                            Error.REPLACEABLE_BASE_CLASS_SIMPLE
                          else
                            Error.REPLACEABLE_BASE_CLASS
                          end
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, inInfo)
                      Error.addSourceMessage(msg, list(part, bc_str), info)
                    ()
                  end
                  
                  (_, _, _, _, _)  => begin
                      @match true = stringEq(inError, BASECLASS_IS_VAR_ERROR)
                      @match (NFSCodeEnv.VAR(var = SCode.COMPONENT(name = part, info = info)), _, _) = NFSCodeLookup.lookupFullyQualified(inPartPath, inEnv)
                      bc_str = AbsynUtil.pathString(inBaseClass)
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, info)
                      Error.addSourceMessage(Error.EXTEND_THROUGH_COMPONENT, list(part, bc_str), inInfo)
                    ()
                  end
                end
              end
        end

        function printInheritedExtendsError(inName::String, inExtends::List{<:Extends}, inEnv::Env)  
              _ = begin
                  local rest_ext::List{Extends}
                  local ext::Extends
                  local item::Item
                  local info1::SourceInfo
                  local info2::SourceInfo
                  local bc::Absyn.Path
                  local bc_str::String
                @matchcontinue (inName, inExtends, inEnv) begin
                  (_, ext && NFSCodeEnv.EXTENDS(baseClass = bc, info = info2) <| rest_ext, _)  => begin
                      @match (SOME(item), _, _) = NFSCodeLookup.lookupInBaseClasses3(inName, ext, inEnv, inEnv, NFSCodeLookup.IGNORE_REDECLARES(), nil)
                      info1 = NFSCodeEnv.getItemInfo(item)
                      @match NFSCodeEnv.EXTENDS(baseClass = bc, info = info2) = ext
                      bc = AbsynUtil.makeNotFullyQualified(bc)
                      bc_str = AbsynUtil.pathString(bc)
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, info1)
                      Error.addSourceMessage(Error.EXTENDS_INHERITED_FROM_LOCAL_EXTENDS, list(inName, bc_str), info2)
                      printInheritedExtendsError(inName, rest_ext, inEnv)
                    ()
                  end
                  
                  (_, _ <| rest_ext, _)  => begin
                      printInheritedExtendsError(inName, rest_ext, inEnv)
                    ()
                  end
                  
                  (_,  nil(), _)  => begin
                    ()
                  end
                end
              end
        end

        function lookupSimpleName(inName::String, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}, Bool} 
              local outFromExtends::Bool
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv, outFromExtends) = begin
                  local frame_type::FrameType
                  local env::Env
                  local opt_item::Option{Item}
                  local opt_env::Option{Env}
                  local opt_path::Option{Absyn.Path}
                  local fe::Bool
                @matchcontinue (inName, inEnv, inExtendsTable) begin
                  (_, _, _)  => begin
                      (opt_item, opt_path, opt_env, fe) = lookupInLocalScope(inName, inEnv, inExtendsTable)
                    (opt_item, opt_path, opt_env, fe)
                  end
                  
                  (_, NFSCodeEnv.FRAME(frameType = frame_type) <| env, _)  => begin
                      NFSCodeLookup.frameNotEncapsulated(frame_type)
                      (opt_item, opt_path, opt_env, _) = lookupSimpleName(inName, env, inExtendsTable)
                    (opt_item, opt_path, opt_env, false)
                  end
                  
                  _  => begin
                      (NONE(), NONE(), NONE(), false)
                  end
                end
              end
          (outItem, outPath, outEnv, outFromExtends)
        end

        function lookupInLocalScope(inName::String, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}, Bool} 
              local outFromExtends::Bool
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv, outFromExtends) = begin
                  local item::Item
                  local env::Env
                  local oitem::Option{Item}
                  local opath::Option{Absyn.Path}
                  local oenv::Option{Env}
                  local bcl::List{Extends}
                  local imps::List{Import}
                @matchcontinue (inName, inEnv, inExtendsTable) begin
                  (_, _, _)  => begin
                      (item, env) = NFSCodeLookup.lookupInClass(inName, inEnv)
                    (SOME(item), SOME(Absyn.IDENT(inName)), SOME(env), false)
                  end
                  
                  (_, NFSCodeEnv.FRAME(extendsTable = NFSCodeEnv.EXTENDS_TABLE(baseClasses = bcl && _ <| _)) <| _, _)  => begin
                      (oitem, oenv) = lookupInBaseClasses(inName, bcl, inEnv, inExtendsTable)
                    (oitem, SOME(Absyn.IDENT(inName)), oenv, true)
                  end
                  
                  (_, NFSCodeEnv.FRAME(importTable = NFSCodeEnv.IMPORT_TABLE(hidden = false, qualifiedImports = imps)) <| _, _)  => begin
                      (oitem, opath, oenv) = lookupInQualifiedImports(inName, imps, inEnv, inExtendsTable)
                    (oitem, opath, oenv, false)
                  end
                  
                  (_, NFSCodeEnv.FRAME(importTable = NFSCodeEnv.IMPORT_TABLE(hidden = false, unqualifiedImports = imps)) <| _, _)  => begin
                      (oitem, opath, oenv) = lookupInUnqualifiedImports(inName, imps, inEnv, inExtendsTable)
                    (oitem, opath, oenv, false)
                  end
                end
              end
          (outItem, outPath, outEnv, outFromExtends)
        end

        function lookupInBaseClasses(inName::String, inExtends::List{<:Extends}, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Env}} 
              local outEnv::Option{Env}
              local outItem::Option{Item}

              (outItem, outEnv) = begin
                  local ext::Extends
                  local rest_ext::List{Extends}
                  local opt_ext::Option{Extends}
                  local opt_item::Option{Item}
                  local opt_env::Option{Env}
                  local env::Env
                @matchcontinue (inName, inExtends, inEnv, inExtendsTable) begin
                  (_, ext <| _, _, _)  => begin
                      env = NFSCodeEnv.setImportTableHidden(inEnv, false)
                      opt_ext = qualifyExtends2(ext, env, inExtendsTable)
                      (opt_item, opt_env) = lookupInBaseClasses2(inName, opt_ext, env, inExtendsTable)
                    (opt_item, opt_env)
                  end
                  
                  (_, _ <| rest_ext, _, _)  => begin
                      (opt_item, opt_env) = lookupInBaseClasses(inName, rest_ext, inEnv, inExtendsTable)
                    (opt_item, opt_env)
                  end
                end
              end
               #=  Unhide the imports, otherwise we might not be able to find the base
               =#
               #=  classes.
               =#
          (outItem, outEnv)
        end

        function lookupInBaseClasses2(inName::String, inExtends::Option{<:Extends}, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Env}} 
              local outEnv::Option{Env}
              local outItem::Option{Item}

              (outItem, outEnv) = begin
                  local bc::Absyn.Path
                  local item::Item
                  local env::Env
                  local opt_item::Option{Item}
                  local opt_env::Option{Env}
                @match (inName, inExtends, inEnv, inExtendsTable) begin
                  (_, SOME(NFSCodeEnv.EXTENDS(baseClass = Absyn.FULLYQUALIFIED(bc))), _, _)  => begin
                      (item, env) = lookupFullyQualified(bc, inEnv, inExtendsTable)
                      env = NFSCodeEnv.mergeItemEnv(item, env)
                      env = NFSCodeEnv.setImportTableHidden(env, true)
                      (opt_item, _, opt_env, _) = lookupInLocalScope(inName, env, inExtendsTable)
                    (opt_item, opt_env)
                  end
                end
              end
               #=  Hide the imports to make sure we don't find any elements through
               =#
               #=  them, since imports are not inherited.
               =#
          (outItem, outEnv)
        end

        function lookupInQualifiedImports(inName::String, inImports::List{<:Import}, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local name::Absyn.Ident
                  local path::Absyn.Path
                  local item::Item
                  local rest_imps::List{Import}
                  local opt_item::Option{Item}
                  local opt_path::Option{Absyn.Path}
                  local opt_env::Option{Env}
                  local env::Env
                @matchcontinue (inName, inImports, inEnv, inExtendsTable) begin
                  (_, Absyn.NAMED_IMPORT(name = name) <| rest_imps, _, _)  => begin
                      @match false = stringEqual(inName, name)
                      (opt_item, opt_path, opt_env) = lookupInQualifiedImports(inName, rest_imps, inEnv, inExtendsTable)
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, Absyn.NAMED_IMPORT(name = name, path = path) <| _, _, _)  => begin
                      @match true = stringEqual(inName, name)
                      (item, env) = lookupFullyQualified(path, inEnv, inExtendsTable)
                      path = NFSCodeEnv.prefixIdentWithEnv(inName, env)
                      path = AbsynUtil.makeFullyQualified(path)
                    (SOME(item), SOME(path), SOME(env))
                  end
                  
                  (_, Absyn.NAMED_IMPORT(name = name) <| _, _, _)  => begin
                      @match true = stringEqual(inName, name)
                    (NONE(), NONE(), NONE())
                  end
                end
              end
          (outItem, outPath, outEnv)
        end

        function lookupInUnqualifiedImports(inName::Absyn.Ident, inImports::List{<:Import}, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local item::Item
                  local path::Absyn.Path
                  local rest_imps::List{Import}
                  local env::Env
                  local opt_item::Option{Item}
                  local opt_path::Option{Absyn.Path}
                  local opt_env::Option{Env}
                @matchcontinue (inName, inImports, inEnv, inExtendsTable) begin
                  (_, Absyn.UNQUAL_IMPORT(path = path) <| _, _, _)  => begin
                      (item, env) = lookupFullyQualified(path, inEnv, inExtendsTable)
                      env = NFSCodeEnv.mergeItemEnv(item, env)
                      (item, env) = lookupFullyQualified2(Absyn.IDENT(inName), env, inExtendsTable)
                      path = NFSCodeEnv.prefixIdentWithEnv(inName, env)
                      path = AbsynUtil.makeFullyQualified(path)
                    (SOME(item), SOME(path), SOME(env))
                  end
                  
                  (_, _ <| rest_imps, _, _)  => begin
                      (opt_item, opt_path, opt_env) = lookupInUnqualifiedImports(inName, rest_imps, inEnv, inExtendsTable)
                    (opt_item, opt_path, opt_env)
                  end
                end
              end
          (outItem, outPath, outEnv)
        end

        function lookupFullyQualified(inName::Absyn.Path, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              local env::Env

              env = NFSCodeEnv.getEnvTopScope(inEnv)
              (outItem, outEnv) = lookupFullyQualified2(inName, env, inExtendsTable)
          (outItem, outEnv)
        end

        function lookupFullyQualified2(inName::Absyn.Path, inEnv::Env, inExtendsTable::ExtendsTableArray) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local name::String
                  local rest_path::Absyn.Path
                  local item::Item
                  local env::Env
                @match (inName, inEnv, inExtendsTable) begin
                  (Absyn.IDENT(name = name), _, _)  => begin
                      @match (SOME(item), _, SOME(env), _) = lookupInLocalScope(name, inEnv, inExtendsTable)
                    (item, env)
                  end
                  
                  (Absyn.QUALIFIED(name = name, path = rest_path), _, _)  => begin
                      @match (SOME(item), _, SOME(env), _) = lookupInLocalScope(name, inEnv, inExtendsTable)
                      env = NFSCodeEnv.mergeItemEnv(item, env)
                      (item, env) = lookupFullyQualified2(rest_path, env, inExtendsTable)
                    (item, env)
                  end
                end
              end
          (outItem, outEnv)
        end

        function createExtendsTable(inSize::ModelicaInteger) ::ExtendsTableArray 
              local outTable::ExtendsTableArray

              outTable = arrayCreate(inSize, NO_EXTENDS())
          outTable
        end

        function lookupQualifiedExtends(inIndex::ModelicaInteger, inExtendsTable::ExtendsTableArray) ::Option{Extends} 
              local outExtends::Option{Extends}

              local ext::ExtendsWrapper

              ext = arrayGet(inExtendsTable, inIndex)
              outExtends = lookupQualifiedExtends2(ext, inExtendsTable)
          outExtends
        end

        function lookupQualifiedExtends2(inExtends::ExtendsWrapper, inExtendsTable::ExtendsTableArray) ::Option{Extends} 
              local outExtends::Option{Extends}

              outExtends = begin
                  local ext::Extends
                  local bc::Absyn.Path
                @match (inExtends, inExtendsTable) begin
                  (QUALIFIED_EXTENDS(ext = ext), _)  => begin
                    SOME(ext)
                  end
                  
                  (UNQUALIFIED_EXTENDS(ext = NFSCodeEnv.EXTENDS(__)), _)  => begin
                    NONE()
                  end
                end
              end
          outExtends
        end

        function addUnqualifiedToTable(inExtends::Extends, inIndex::ModelicaInteger, inExtendsTable::ExtendsTableArray)  
              _ = arrayUpdate(inExtendsTable, inIndex, UNQUALIFIED_EXTENDS(inExtends))
        end

        function updateQualifiedInTable(inExtends::Extends, inIndex::ModelicaInteger, inExtendsTable::ExtendsTableArray)  
              _ = arrayUpdate(inExtendsTable, inIndex, QUALIFIED_EXTENDS(inExtends))
        end

        function update2(inEnv::Env) ::Env 
              local outEnv::Env

              local env::Env
              local rest_env::Env
              local name::Option{String}
              local ty::FrameType
              local tree::EnvTree.Tree
              local bcl::List{Extends}
              local re::List{SCode.Element}
              local imps::NFSCodeEnv.ImportTable
              local iu::Option{MutableType{Bool}}

              @match _cons(NFSCodeEnv.FRAME(name, ty, tree, NFSCodeEnv.EXTENDS_TABLE(bcl, re, _), imps, iu), rest_env) = inEnv
              tree = EnvTree.map(tree, (inEnv) -> update3(inEnv = inEnv))
              env = _cons(NFSCodeEnv.FRAME(name, ty, tree, NFSCodeEnv.EXTENDS_TABLE(bcl, nil, NONE()), imps, iu), rest_env)
              outEnv = NFSCodeFlattenRedeclare.addElementRedeclarationsToEnv(re, env)
          outEnv
        end

        function update3(name::String, item::Item, inEnv::Env) ::Item 


              () = begin
                  local rest_env::Env
                  local env::Env
                  local cls::SCode.Element
                  local cls_ty::ClassType
                  local cls_env::Frame
                @match item begin
                  NFSCodeEnv.CLASS(cls, cls_env <|  nil(), cls_ty)  => begin
                       #=  Enter the class' frame and update the class extends in it.
                       =#
                      env = NFSCodeEnv.enterFrame(cls_env, inEnv)
                      (cls, env) = updateClassExtends(cls, env, cls_ty)
                       #=  Call update2 on the class' environment to update the extends.
                       =#
                      @match _cons(cls_env, _) = update2(env)
                       #=  Rebuild the class item with the updated information.
                       =#
                      item = NFSCodeEnv.CLASS(cls, list(cls_env), cls_ty)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
          item
        end

        function updateClassExtends(inClass::SCode.Element, inEnv::Env, inClassType::ClassType) ::Tuple{SCode.Element, Env} 
              local outEnv::Env
              local outClass::SCode.Element

              (outClass, outEnv) = begin
                  local name::String
                  local env::Env
                  local mods::SCode.Mod
                  local info::SourceInfo
                  local cls::SCode.Element
                  local ext::SCode.Element
                @match (inClass, inEnv, inClassType) begin
                  (_, NFSCodeEnv.FRAME(name = SOME(name), extendsTable = NFSCodeEnv.EXTENDS_TABLE(classExtendsInfo = SOME(ext))) <| _, NFSCodeEnv.CLASS_EXTENDS(__))  => begin
                      @match SCode.EXTENDS(modifications = mods, info = info) = ext
                      (cls, env) = updateClassExtends2(inClass, name, mods, info, inEnv)
                    (cls, env)
                  end
                  
                  _  => begin
                      (inClass, inEnv)
                  end
                end
              end
          (outClass, outEnv)
        end

        function updateClassExtends2(inClass::SCode.Element, inName::String, inMods::SCode.Mod, inInfo::SourceInfo, inEnv::Env) ::Tuple{SCode.Element, Env} 
              local outEnv::Env
              local outClass::SCode.Element

              (outClass, outEnv) = begin
                  local ext::SCode.Element
                  local cls_frame::Frame
                  local env::Env
                  local cls::SCode.Element
                  local item::Item
                  local path::Absyn.Path
                @matchcontinue (inClass, inName, inMods, inInfo, inEnv) begin
                  (_, _, _, _, cls_frame <| env)  => begin
                      (path, _) = lookupClassExtendsBaseClass(inName, env, inInfo)
                      ext = SCode.EXTENDS(path, SCode.PUBLIC(), inMods, NONE(), inInfo)
                      @match list(cls_frame) = NFSCodeEnv.extendEnvWithExtends(ext, list(cls_frame))
                      cls = SCodeUtil.addElementToClass(ext, inClass)
                    (cls, _cons(cls_frame, env))
                  end
                  
                  _  => begin
                      (inClass, inEnv)
                  end
                end
              end
          (outClass, outEnv)
        end

         #= This function takes the name of a base class and looks up that name suffixed
           with the base class suffix defined in NFSCodeEnv. I.e. it looks up the real base
           class of a class extends, and not the alias introduced when adding replaceable
           classes to the environment in NFSCodeEnv.extendEnvWithClassDef. It returns the
           path and the item for that base class. =#
        function lookupClassExtendsBaseClass(inName::String, inEnv::Env, inInfo::SourceInfo) ::Tuple{Absyn.Path, Item} 
              local outItem::Item
              local outPath::Absyn.Path

              (outPath, outItem) = begin
                  local path::Absyn.Path
                  local item::Item
                  local basename::String
                   #=  Add the base class suffix to the name and try to look it up.
                   =#
                @matchcontinue (inName, inEnv, inInfo) begin
                  (_, _, _)  => begin
                      basename = inName + NFSCodeEnv.BASE_CLASS_SUFFIX
                      (item, _) = NFSCodeLookup.lookupInheritedName(basename, inEnv)
                      path = Absyn.QUALIFIED("ce", Absyn.IDENT(basename))
                    (path, item)
                  end
                  
                  (_, _, _)  => begin
                      (item, _) = NFSCodeLookup.lookupInheritedName(inName, inEnv)
                      path = Absyn.IDENT(inName)
                    (path, item)
                  end
                  
                  _  => begin
                        Error.addSourceMessage(Error.INVALID_REDECLARATION_OF_CLASS, list(inName), inInfo)
                      fail()
                  end
                end
              end
               #=  Use a special $ce qualified so that we can find the correct class
               =#
               #=  with NFSCodeLookup.lookupBaseClassName.
               =#
               #=  The previous case will fail if we try to class extend a
               =#
               #=  non-replaceable class, because they don't have aliases. To get the
               =#
               #=  correct error message later we look the class up via the non-alias name
               =#
               #=  instead and return that result if found.
               =#
               #=  If the class doesn't even exist, show an error.
               =#
          (outPath, outItem)
        end

         #= Extends the environment with the given class extends element. =#
        function extendEnvWithClassExtends(inClassExtends::SCode.Element, inEnv::Env) ::Env 
              local outEnv::Env

              outEnv = begin
                  local pp::SCode.Partial
                  local ep::SCode.Encapsulated
                  local res::SCode.Restriction
                  local prefixes::SCode.Prefixes
                  local info::SourceInfo
                  local env::Env
                  local cls_env::Env
                  local mods::SCode.Mod
                  local cdef::SCode.ClassDef
                  local cls::SCode.Element
                  local ext::SCode.Element
                  local name::String
                  local el_str::String
                  local env_str::String
                  local err_msg::String
                  local cmt::SCode.Comment
                   #=  When a 'class extends X' is encountered we insert a 'class X extends
                   =#
                   #=  BaseClass.X' into the environment, with the same elements as the class
                   =#
                   #=  extends clause. BaseClass is the class that class X is inherited from.
                   =#
                   #=  This allows us to look up elements in class extends, because lookup can
                   =#
                   #=  handle normal extends. This is the first phase where the CLASS_EXTENDS is
                   =#
                   #=  converted to a PARTS and added to the environment, and the extends is
                   =#
                   #=  added to the class environment's extends table. The rest of the work is
                   =#
                   #=  done later in updateClassExtends when we have a complete environment.
                   =#
                @match (inClassExtends, inEnv) begin
                  (SCode.CLASS(name = name, prefixes = prefixes, encapsulatedPrefix = ep, partialPrefix = pp, restriction = res, classDef = SCode.CLASS_EXTENDS(modifications = mods, composition = cdef), cmt = cmt, info = info), _)  => begin
                      cls = SCode.CLASS(name, prefixes, ep, pp, res, cdef, cmt, info)
                      cls_env = NFSCodeEnv.makeClassEnvironment(cls, false)
                      ext = SCode.EXTENDS(Absyn.IDENT(name), SCode.PUBLIC(), mods, NONE(), info)
                      cls_env = addClassExtendsInfoToEnv(ext, cls_env)
                      env = NFSCodeEnv.extendEnvWithItem(NFSCodeEnv.newClassItem(cls, cls_env, NFSCodeEnv.CLASS_EXTENDS()), inEnv, name)
                    env
                  end
                  
                  (_, _)  => begin
                      info = SCodeUtil.elementInfo(inClassExtends)
                      el_str = SCodeDump.unparseElementStr(inClassExtends, SCodeDump.defaultOptions)
                      env_str = NFSCodeEnv.getEnvName(inEnv)
                      err_msg = "NFSCodeFlattenRedeclare.extendEnvWithClassExtends failed on unknown element " + el_str + " in " + env_str
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(err_msg), info)
                    fail()
                  end
                end
              end
               #=  Construct a new PARTS class with the data from the class extends.
               =#
               #=  Construct the class environment and add the new extends to it.
               =#
               #=  Finally add the class to the environment.
               =#
          outEnv
        end

         #= Adds a class extends to the environment. =#
        function addClassExtendsInfoToEnv(inClassExtends::SCode.Element, inEnv::Env) ::Env 
              local outEnv::Env

              outEnv = begin
                  local bcl::List{Extends}
                  local re::List{SCode.Element}
                  local estr::String
                  local ext::NFSCodeEnv.ExtendsTable
                @matchcontinue (inClassExtends, inEnv) begin
                  (_, _)  => begin
                      @match NFSCodeEnv.EXTENDS_TABLE(bcl, re, NONE()) = NFSCodeEnv.getEnvExtendsTable(inEnv)
                      ext = NFSCodeEnv.EXTENDS_TABLE(bcl, re, SOME(inClassExtends))
                    NFSCodeEnv.setEnvExtendsTable(ext, inEnv)
                  end
                  
                  _  => begin
                        estr = "- NFEnvExtends.addClassExtendsInfoToEnv: Trying to overwrite " + "existing class extends information, this should not happen!."
                        Error.addMessage(Error.INTERNAL_ERROR, list(estr))
                      fail()
                  end
                end
              end
          outEnv
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
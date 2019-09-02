  module NFSCodeDependency 


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

        import NFInstPrefix

        import NFSCodeEnv

        Env = NFSCodeEnv.Env 

        import Config

        import Debug

        import Error

        import Flags

        import ListUtil

        import MutableType

        import NFSCodeCheck

        import NFSCodeFlattenRedeclare

        import NFSCodeLookup

        import SCodeDump
        import SCodeUtil

        import System

        import Util

        Item = NFSCodeEnv.Item 

        Extends = NFSCodeEnv.Extends 

        FrameType = NFSCodeEnv.FrameType 

        Import = Absyn.Import 

        import NFSCodeEnv.EnvTree

         #= This is the entry point of the dependency analysis. The dependency analysis
          is done in three steps: first it analyses the program and marks each element in
          the program that's used. The it goes through the used classes and checks if
          they contain any class extends, and if so it checks of those class extends are
          used or not. Finally it collects the used elements and builds a new program
          and environment that only contains those elements. =#
        function analyse(inClassName::Absyn.Path, inEnv::Env, inProgram::SCode.Program) ::Tuple{SCode.Program, Env} 
              local outEnv::Env
              local outProgram::SCode.Program

              analyseClass(inClassName, inEnv, AbsynUtil.dummyInfo)
              analyseClassExtends(inEnv)
              (outEnv, outProgram) = collectUsedProgram(inEnv, inProgram, inClassName)
          (outProgram, outEnv)
        end

         #= Analyses a class by looking up the class, marking it as used and recursively
          analysing it's contents. =#
        function analyseClass(inClassName::Absyn.Path, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local item::Item
                  local env::Env
                @matchcontinue (inClassName, inEnv, inInfo) begin
                  (_, _, _)  => begin
                      (item, env) = lookupClass(inClassName, inEnv, true, inInfo, SOME(Error.LOOKUP_ERROR))
                      checkItemIsClass(item)
                      analyseItem(item, env)
                    ()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeDependency.analyseClass failed for " + AbsynUtil.pathString(inClassName) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
        end

         #= Lookup a class in the environment. The reason why SCodeLookup is not used
          directly is because we need to look up each part of the class path and mark
          them as used. =#
        function lookupClass(inPath::Absyn.Path, inEnv::Env, inBuiltinPossible::Bool #= True if the path can be a builtin, otherwise false. =#, inInfo::SourceInfo, inErrorType::Option{<:Error.Message}) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local item::Item
                  local env::Env
                  local name_str::String
                  local env_str::String
                  local error_id::Error.Message
                @matchcontinue (inPath, inEnv, inBuiltinPossible, inInfo, inErrorType) begin
                  (_, _, _, _, _)  => begin
                      (item, env) = lookupClass2(inPath, inEnv, inBuiltinPossible, inInfo, inErrorType)
                      (item, env, _) = NFSCodeEnv.resolveRedeclaredItem(item, env)
                    (item, env)
                  end
                  
                  (_, _, _, _, SOME(error_id))  => begin
                      name_str = AbsynUtil.pathString(inPath)
                      env_str = NFSCodeEnv.getEnvName(inEnv)
                      Error.addSourceMessage(error_id, list(name_str, env_str), inInfo)
                    fail()
                  end
                end
              end
          (outItem, outEnv)
        end

         #= Help function to lookupClass, does the actual look up. =#
        function lookupClass2(inPath::Absyn.Path, inEnv::Env, inBuiltinPossible::Bool, inInfo::SourceInfo, inErrorType::Option{<:Error.Message}) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local item::Item
                  local env::Env
                  local id::String
                  local rest_path::Absyn.Path
                @match (inPath, inEnv, inBuiltinPossible, inInfo, inErrorType) begin
                  (Absyn.IDENT(__), _, true, _, _)  => begin
                      (item, _, env) = NFSCodeLookup.lookupNameSilent(inPath, inEnv, inInfo)
                    (item, env)
                  end
                  
                  (Absyn.IDENT(__), _, false, _, _)  => begin
                      (item, _, env) = NFSCodeLookup.lookupNameSilentNoBuiltin(inPath, inEnv, inInfo)
                    (item, env)
                  end
                  
                  (Absyn.QUALIFIED(name = "$ce", path = Absyn.IDENT(name = id)), _ <| env, _, _, _)  => begin
                      (item, env) = NFSCodeLookup.lookupInheritedName(id, env)
                    (item, env)
                  end
                  
                  (Absyn.QUALIFIED(name = id, path = rest_path), _, _, _, _)  => begin
                      (item, _, env) = NFSCodeLookup.lookupNameSilent(Absyn.IDENT(id), inEnv, inInfo)
                      (item, env, _) = NFSCodeEnv.resolveRedeclaredItem(item, env)
                      analyseItem(item, env)
                      (item, env) = lookupNameInItem(rest_path, item, env, inErrorType)
                    (item, env)
                  end
                  
                  (Absyn.FULLYQUALIFIED(path = rest_path), _, _, _, _)  => begin
                      env = NFSCodeEnv.getEnvTopScope(inEnv)
                      (item, env) = lookupClass2(rest_path, env, false, inInfo, inErrorType)
                    (item, env)
                  end
                end
              end
               #=  Special case for the baseclass of a class extends. Should be looked up
               =#
               #=  among the inherited elements of the enclosing class.
               =#
          (outItem, outEnv)
        end

        function lookupNameInItem(inName::Absyn.Path, inItem::Item, inEnv::Env, inErrorType::Option{<:Error.Message}) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local type_path::Absyn.Path
                  local mods::SCode.Mod
                  local info::SourceInfo
                  local env::Env
                  local type_env::Env
                  local class_env::NFSCodeEnv.Frame
                  local redeclares::List{NFSCodeEnv.Redeclaration}
                  local item::Item
                @match (inName, inItem, inEnv, inErrorType) begin
                  (_, _,  nil(), _)  => begin
                    (inItem, inEnv)
                  end
                  
                  (_, NFSCodeEnv.VAR(var = SCode.COMPONENT(typeSpec = Absyn.TPATH(path = type_path), modifications = mods, info = info)), _, _)  => begin
                      (item, type_env) = lookupClass(type_path, inEnv, true, info, inErrorType)
                      @match true = NFSCodeEnv.isClassItem(item)
                      redeclares = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
                      (item, type_env, _) = NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv(redeclares, item, type_env, inEnv, NFInstPrefix.emptyPrefix)
                      (item, env) = lookupNameInItem(inName, item, type_env, inErrorType)
                    (item, env)
                  end
                  
                  (_, NFSCodeEnv.CLASS(cls = SCode.CLASS(info = info), env = class_env <|  nil()), _, _)  => begin
                      env = NFSCodeEnv.enterFrame(class_env, inEnv)
                      (item, env) = lookupClass(inName, env, false, info, inErrorType)
                    (item, env)
                  end
                end
              end
          (outItem, outEnv)
        end

         #= Checks that the found item really is a class, otherwise prints an error
          message. =#
        function checkItemIsClass(inItem::Item)  
              _ = begin
                  local name::String
                  local info::SourceInfo
                @match inItem begin
                  NFSCodeEnv.CLASS(__)  => begin
                    ()
                  end
                  
                  NFSCodeEnv.VAR(var = SCode.COMPONENT(name = name, info = info))  => begin
                      Error.addSourceMessage(Error.LOOKUP_TYPE_FOUND_COMP, list(name), info)
                    fail()
                  end
                end
              end
               #=  We found a component instead, which might happen if the user tries to use
               =#
               #=  a variable name as a type.
               =#
        end

         #= Analyses an item. =#
        function analyseItem(inItem::Item, inEnv::Env)  
               #=  Check if the item is already marked as used, then we can stop here.
               =#
              if NFSCodeEnv.isItemUsed(inItem)
                return 
              end
              _ = begin
                  local cdef::SCode.ClassDef
                  local cls_env::NFSCodeEnv.Frame
                  local env::Env
                  local info::SourceInfo
                  local res::SCode.Restriction
                  local cls::SCode.Element
                  local cmt::SCode.Comment
                   #=  A component, mark it and it's environment as used.
                   =#
                @match (inItem, inEnv) begin
                  (NFSCodeEnv.VAR(__), env)  => begin
                      markItemAsUsed(inItem, env)
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(classType = NFSCodeEnv.BASIC_TYPE(__)), _)  => begin
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(cls = cls && SCode.CLASS(classDef = cdef, restriction = res, info = info, cmt = cmt), env = cls_env <|  nil()), env)  => begin
                      markItemAsUsed(inItem, env)
                      env = NFSCodeEnv.enterFrame(cls_env, env)
                      if if cls.name == "cardinality"
                            begin
                              @match inEnv begin
                                NFSCodeEnv.FRAME(name = NONE()) <|  nil()  => begin
                                  true
                                end
                                
                                _  => begin
                                    false
                                end
                              end
                            end
                          else
                            false
                          end
                        System.setUsesCardinality(true)
                      end
                      analyseClassDef(cdef, res, env, false, info)
                      analyseMetaType(res, env, info)
                      analyseComment(cmt, env, info)
                      @match _cons(_, env) = env
                      analyseRedeclaredClass(cls, env)
                    ()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeDependency.analyseItem failed on " + NFSCodeEnv.getItemName(inItem) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
        end

         #= Analyses an item again if there were some redeclares applied to the environment =#
        function analyseItemIfRedeclares(inRepls::NFSCodeFlattenRedeclare.Replacements, inItem::Item, inEnv::Env)  
              _ = begin
                  local i::Item
                  local cls_frm::NFSCodeEnv.Frame
                  local env::Env
                   #=  no replacements happened on the environemnt! do nothing
                   =#
                @matchcontinue (inRepls, inItem, inEnv) begin
                  ( nil(), _, _)  => begin
                    ()
                  end
                  
                  (_, _, _)  => begin
                      @match _cons(_, env) = inEnv
                      analyseItemNoStopOnUsed(inItem, env)
                    ()
                  end
                end
              end
               #= i = NFSCodeEnv.setItemEnv(inItem, {cls_frm});
               =#
        end

         #= Analyses an item. =#
        function analyseItemNoStopOnUsed(inItem::Item, inEnv::Env)  
              _ = begin
                  local cdef::SCode.ClassDef
                  local cls_env::NFSCodeEnv.Frame
                  local env::Env
                  local info::SourceInfo
                  local res::SCode.Restriction
                  local cls::SCode.Element
                  local cmt::SCode.Comment
                   #=  A component, mark it and it's environment as used.
                   =#
                @matchcontinue (inItem, inEnv) begin
                  (NFSCodeEnv.VAR(__), env)  => begin
                      markItemAsUsed(inItem, env)
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(classType = NFSCodeEnv.BASIC_TYPE(__)), _)  => begin
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(cls = cls && SCode.CLASS(classDef = cdef, restriction = res, info = info, cmt = cmt), env = cls_env <|  nil()), env)  => begin
                      markItemAsUsed(inItem, env)
                      env = NFSCodeEnv.enterFrame(cls_env, env)
                      analyseClassDef(cdef, res, env, false, info)
                      analyseMetaType(res, env, info)
                      analyseComment(cmt, env, info)
                      @match _cons(_, env) = env
                      analyseRedeclaredClass(cls, env)
                    ()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeDependency.analyseItemNoStopOnUsed failed on " + NFSCodeEnv.getItemName(inItem) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
               #=  A basic type, nothing to be done.
               =#
               #=  A normal class, mark it and it's environment as used, and recursively
               =#
               #=  analyse it's contents.
               =#
        end

         #= Marks an item and it's environment as used. =#
        function markItemAsUsed(inItem::Item, inEnv::Env)  
              _ = begin
                  local cls_env::NFSCodeEnv.Frame
                  local is_used::MutableType{Bool}
                  local name::String
                @match (inItem, inEnv) begin
                  (NFSCodeEnv.VAR(isUsed = SOME(is_used)), _)  => begin
                      Mutable.update(is_used, true)
                      markEnvAsUsed(inEnv)
                    ()
                  end
                  
                  (NFSCodeEnv.VAR(isUsed = NONE()), _)  => begin
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(env = cls_env <|  nil(), cls = SCode.CLASS(__)), _)  => begin
                      markFrameAsUsed(cls_env)
                      markEnvAsUsed(inEnv)
                    ()
                  end
                end
              end
        end

         #= Marks a single frame as used. =#
        function markFrameAsUsed(inFrame::NFSCodeEnv.Frame)  
              _ = begin
                  local is_used::MutableType{Bool}
                @match inFrame begin
                  NFSCodeEnv.FRAME(isUsed = SOME(is_used))  => begin
                      Mutable.update(is_used, true)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Marks an environment as used. This is done by marking each frame as used, and
          for each frame we also analyse the class it represents to make sure we don't
          miss anything in the enclosing scopes of an item. =#
        function markEnvAsUsed(inEnv::Env)  
              _ = begin
                  local is_used::MutableType{Bool}
                  local rest_env::Env
                  local f::NFSCodeEnv.Frame
                @matchcontinue inEnv begin
                  f && NFSCodeEnv.FRAME(isUsed = SOME(is_used)) <| rest_env  => begin
                      @match false = Mutable.access(is_used)
                      markEnvAsUsed2(f, rest_env)
                      Mutable.update(is_used, true)
                      markEnvAsUsed(rest_env)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Helper function to markEnvAsUsed. Checks if the given frame belongs to a
          class, and if that's the case calls analyseClass on that class. =#
        function markEnvAsUsed2(inFrame::NFSCodeEnv.Frame, inEnv::NFSCodeEnv.Env)  
              _ = begin
                  local name::String
                @match (inFrame, inEnv) begin
                  (NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)), _)  => begin
                    ()
                  end
                  
                  (NFSCodeEnv.FRAME(name = SOME(name)), _)  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, AbsynUtil.dummyInfo)
                    ()
                  end
                end
              end
        end

         #= Analyses the contents of a class definition. =#
        function analyseClassDef(inClassDef::SCode.ClassDef, inRestriction::SCode.Restriction, inEnv::Env, inInModifierScope::Bool, inInfo::SourceInfo)  
              _ = begin
                  local el::List{SCode.Element}
                  local bc::Absyn.Ident
                  local mods::SCode.Mod
                  local ty::Absyn.TypeSpec
                  local nel::List{SCode.Equation}
                  local iel::List{SCode.Equation}
                  local nal::List{SCode.AlgorithmSection}
                  local ial::List{SCode.AlgorithmSection}
                  local cmt::SCode.Comment
                  local annl::List{SCode.Annotation}
                  local ext_decl::Option{SCode.ExternalDecl}
                  local ty_env::Env
                  local env::Env
                  local nore_env::Env
                  local ty_item::Item
                  local attr::SCode.Attributes
                  local paths::List{Absyn.Path}
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local repls::NFSCodeFlattenRedeclare.Replacements
                   #=  A class made of parts, analyse elements, equation, algorithms, etc.
                   =#
                @matchcontinue (inClassDef, inRestriction, inEnv, inInModifierScope, inInfo) begin
                  (SCode.PARTS(elementLst = el, normalEquationLst = nel, initialEquationLst = iel, normalAlgorithmLst = nal, initialAlgorithmLst = ial, externalDecl = ext_decl), _, _, _, _)  => begin
                      analyseElements(el, inEnv, inRestriction)
                      ListUtil.map1_0(nel, analyseEquation, inEnv)
                      ListUtil.map1_0(iel, analyseEquation, inEnv)
                      ListUtil.map1_0(nal, analyseAlgorithm, inEnv)
                      ListUtil.map1_0(ial, analyseAlgorithm, inEnv)
                      analyseExternalDecl(ext_decl, inEnv, inInfo)
                    ()
                  end
                  
                  (SCode.PARTS(elementLst = el), _, _, _, _)  => begin
                      isExternalObject(el, inEnv, inInfo)
                      analyseClass(Absyn.IDENT("constructor"), inEnv, inInfo)
                      analyseClass(Absyn.IDENT("destructor"), inEnv, inInfo)
                    ()
                  end
                  
                  (SCode.CLASS_EXTENDS(__), _, _, _, _)  => begin
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list("NFSCodeDependency.analyseClassDef failed on CLASS_EXTENDS"), inInfo)
                    fail()
                  end
                  
                  (SCode.DERIVED(typeSpec = ty, modifications = mods), _, _ <| env, _, _)  => begin
                      env = if inInModifierScope
                            inEnv
                          else
                            env
                          end
                      nore_env = NFSCodeEnv.removeRedeclaresFromLocalScope(env)
                      analyseTypeSpec(ty, nore_env, inInfo)
                      (ty_item, _, ty_env) = NFSCodeLookup.lookupTypeSpec(ty, env, inInfo)
                      (ty_item, ty_env, _) = NFSCodeEnv.resolveRedeclaredItem(ty_item, ty_env)
                      ty_env = NFSCodeEnv.mergeItemEnv(ty_item, ty_env)
                      redecls = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
                      (ty_item, ty_env, repls) = NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv(redecls, ty_item, ty_env, inEnv, NFInstPrefix.emptyPrefix)
                      analyseItemIfRedeclares(repls, ty_item, ty_env)
                      analyseModifier(mods, inEnv, ty_env, inInfo)
                    ()
                  end
                  
                  (SCode.ENUMERATION(__), _, _, _, _)  => begin
                    ()
                  end
                  
                  (SCode.OVERLOAD(pathLst = paths), _, _, _, _)  => begin
                       #=  The previous case failed, which might happen for an external object.
                       =#
                       #=  Check if the class definition is an external object and analyse it if
                       =#
                       #=  that's the case.
                       =#
                       #=  A class extends.
                       =#
                       #=  A derived class definition.
                       =#
                       #=  Other cases which doesn't need to be analysed.
                       =#
                      if ! Config.synchronousFeaturesAllowed() && AbsynUtil.pathFirstIdent(listHead(paths)) == "OMC_NO_CLOCK"
                        ListUtil.map2_0(list(listHead(paths)), analyseClass, inEnv, inInfo)
                      else
                        ListUtil.map2_0(paths, analyseClass, inEnv, inInfo)
                      end
                    ()
                  end
                  
                  (SCode.PDER(__), _, _, _, _)  => begin
                    ()
                  end
                end
              end
        end

         #= Checks if a class definition is an external object. =#
        function isExternalObject(inElements::List{<:SCode.Element}, inEnv::Env, inInfo::SourceInfo)  
              local el::List{SCode.Element}
              local el_names::List{String}

               #=  Remove all 'extends ExternalObject'.
               =#
              el = ListUtil.filterOnTrue(inElements, isNotExternalObject)
               #=  Check if length of the new list is different to the old, i.e. if we
               =#
               #=  actually found and removed any 'extends ExternalObject'.
               =#
              @match false = listLength(el) == listLength(inElements)
               #=  Ok, we have an external object, check that it's valid.
               =#
              el_names = ListUtil.filterMap(el, elementName)
              checkExternalObject(el_names, inEnv, inInfo)
        end

        function elementName(inElement::SCode.Element) ::String 
              local outString::String

              outString = begin
                  local name::String
                  local bc::Absyn.Path
                @match inElement begin
                  SCode.COMPONENT(name = name)  => begin
                    name
                  end
                  
                  SCode.CLASS(name = name)  => begin
                    name
                  end
                  
                  SCode.DEFINEUNIT(name = name)  => begin
                    name
                  end
                  
                  SCode.EXTENDS(baseClassPath = bc)  => begin
                      name = AbsynUtil.pathString(bc)
                      name = "extends " + name
                    name
                  end
                end
              end
          outString
        end

         #= False on 'extends ExternalObject', otherwise true. =#
        function isNotExternalObject(inElement::SCode.Element) ::Bool 
              local b::Bool

              b = begin
                @match inElement begin
                  SCode.EXTENDS(baseClassPath = Absyn.IDENT("ExternalObject"))  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          b
        end

         #= Checks that an external object is valid, i.e. has exactly one constructor and
          one destructor. =#
        function checkExternalObject(inElements::List{<:String}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local env_str::String
                  local has_con::Bool
                  local has_des::Bool
                   #=  Ok, we have both a constructor and a destructor.
                   =#
                @match (inElements, inEnv, inInfo) begin
                  ("constructor" <| "destructor" <|  nil(), _, _)  => begin
                    ()
                  end
                  
                  ("destructor" <| "constructor" <|  nil(), _, _)  => begin
                    ()
                  end
                  
                  _  => begin
                        has_con = ListUtil.isMemberOnTrue("constructor", inElements, stringEqual)
                        has_des = ListUtil.isMemberOnTrue("destructor", inElements, stringEqual)
                        env_str = NFSCodeEnv.getEnvName(inEnv)
                        checkExternalObject2(inElements, has_con, has_des, env_str, inInfo)
                      fail()
                  end
                end
              end
               #=  Otherwise it's not valid, so print an error message.
               =#
        end

         #= Helper function to checkExternalObject. Prints an error message depending on
          what the external object contained. =#
        function checkExternalObject2(inElements::List{<:String}, inHasConstructor::Bool, inHasDestructor::Bool, inObjectName::String, inInfo::SourceInfo)  
              _ = begin
                  local el::List{String}
                  local el_str::String
                   #=  The external object contains both a constructor and a destructor, so it
                   =#
                   #=  has to also contain some invalid elements.
                   =#
                @match (inElements, inHasConstructor, inHasDestructor, inObjectName, inInfo) begin
                  (el, true, true, _, _)  => begin
                      (el, _) = ListUtil.deleteMemberOnTrue("constructor", el, stringEqual)
                      (el, _) = ListUtil.deleteMemberOnTrue("destructor", el, stringEqual)
                      el_str = stringDelimitList(el, ", ")
                      el_str = "contains invalid elements: " + el_str
                      Error.addSourceMessage(Error.INVALID_EXTERNAL_OBJECT, list(inObjectName, el_str), inInfo)
                    ()
                  end
                  
                  (_, false, true, _, _)  => begin
                      Error.addSourceMessage(Error.INVALID_EXTERNAL_OBJECT, list(inObjectName, "missing constructor"), inInfo)
                    ()
                  end
                  
                  (_, true, false, _, _)  => begin
                      Error.addSourceMessage(Error.INVALID_EXTERNAL_OBJECT, list(inObjectName, "missing destructor"), inInfo)
                    ()
                  end
                  
                  (_, false, false, _, _)  => begin
                      Error.addSourceMessage(Error.INVALID_EXTERNAL_OBJECT, list(inObjectName, "missing both constructor and destructor"), inInfo)
                    ()
                  end
                end
              end
               #=  Remove the constructor and destructor from the list of elements.
               =#
               #=  Print an error message with the rest of the elements.
               =#
               #=  The external object is missing a constructor.
               =#
               #=  The external object is missing a destructor.
               =#
               #=  The external object is missing both a constructor and a destructor.
               =#
        end

         #= If a metarecord is analysed we need to also analyse it's parent uniontype. =#
        function analyseMetaType(inRestriction::SCode.Restriction, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local union_name::Absyn.Path
                @match (inRestriction, inEnv, inInfo) begin
                  (SCode.R_METARECORD(name = union_name), _, _)  => begin
                      analyseClass(union_name, inEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= If a class is a redeclaration of an inherited class we need to also analyse
          the inherited class. =#
        function analyseRedeclaredClass(inClass::SCode.Element, inEnv::Env)  
              _ = begin
                  local item::Item
                  local name::String
                @matchcontinue (inClass, inEnv) begin
                  (SCode.CLASS(__), _)  => begin
                      @match false = SCodeUtil.isElementRedeclare(inClass)
                    ()
                  end
                  
                  (SCode.CLASS(__), _)  => begin
                      item = NFSCodeEnv.CLASS(inClass, NFSCodeEnv.emptyEnv, NFSCodeEnv.USERDEFINED())
                      analyseRedeclaredClass2(item, inEnv)
                    ()
                  end
                end
              end
        end

        function analyseRedeclaredClass2(inItem::Item, inEnv::Env)  
              _ = begin
                  local name::String
                  local item::Item
                  local env::Env
                  local cls::SCode.Element
                  local info::SourceInfo
                @matchcontinue (inItem, inEnv) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(info = info)), _)  => begin
                      (item, env) = NFSCodeLookup.lookupRedeclaredClassByItem(inItem, inEnv, info)
                      analyseItem(item, env)
                    ()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeDependency.analyseRedeclaredClass2 failed for " + NFSCodeEnv.getItemName(inItem) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
        end

        function analyseElements(inElements::List{<:SCode.Element}, inEnv::Env, inClassRestriction::SCode.Restriction)  
              local exts::List{Extends}

              exts = NFSCodeEnv.getEnvExtendsFromTable(inEnv)
              analyseElements2(inElements, inEnv, exts, inClassRestriction)
        end

        function analyseElements2(inElements::List{<:SCode.Element}, inEnv::Env, inExtends::List{<:Extends}, inClassRestriction::SCode.Restriction)  
              _ = begin
                  local el::SCode.Element
                  local rest_el::List{SCode.Element}
                  local exts::List{Extends}
                @match (inElements, inEnv, inExtends, inClassRestriction) begin
                  (el <| rest_el, _, _, _)  => begin
                      exts = analyseElement(el, inEnv, inExtends, inClassRestriction)
                      analyseElements2(rest_el, inEnv, exts, inClassRestriction)
                    ()
                  end
                  
                  ( nil(), _, _, _)  => begin
                    ()
                  end
                end
              end
        end

         #= Analyses an element. =#
        function analyseElement(inElement::SCode.Element, inEnv::Env, inExtends::List{<:Extends}, inClassRestriction::SCode.Restriction) ::List{Extends} 
              local outExtends::List{Extends}

              outExtends = begin
                  local bc::Absyn.Path
                  local bc2::Absyn.Path
                  local mods::SCode.Mod
                  local ty::Absyn.TypeSpec
                  local info::SourceInfo
                  local attr::SCode.Attributes
                  local cond_exp::Option{Absyn.Exp}
                  local ty_item::Item
                  local ty_env::Env
                  local name::SCode.Ident
                  local prefixes::SCode.Prefixes
                  local res::SCode.Restriction
                  local str::String
                  local exts::List{Extends}
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local repls::NFSCodeFlattenRedeclare.Replacements
                   #=  Fail on 'extends ExternalObject' so we can handle it as a special case in
                   =#
                   #=  analyseClassDef.
                   =#
                @match (inElement, inEnv, inExtends, inClassRestriction) begin
                  (SCode.EXTENDS(baseClassPath = Absyn.IDENT("ExternalObject")), _, _, _)  => begin
                    fail()
                  end
                  
                  (SCode.EXTENDS(modifications = mods, info = info), _, NFSCodeEnv.EXTENDS(baseClass = bc) <| exts, _)  => begin
                      (ty_item, _, ty_env) = NFSCodeLookup.lookupBaseClassName(bc, inEnv, info)
                      analyseExtends(bc, inEnv, info)
                      ty_env = NFSCodeEnv.mergeItemEnv(ty_item, ty_env)
                      analyseModifier(mods, inEnv, ty_env, info)
                    exts
                  end
                  
                  (SCode.COMPONENT(name = name, attributes = attr, typeSpec = ty, modifications = mods, condition = cond_exp, prefixes = prefixes, info = info), _, _, _)  => begin
                      markAsUsedOnRestriction(name, inClassRestriction, inEnv, info)
                      analyseAttributes(attr, inEnv, info)
                      analyseTypeSpec(ty, inEnv, info)
                      (ty_item, _, ty_env) = NFSCodeLookup.lookupTypeSpec(ty, inEnv, info)
                      (ty_item, ty_env, _) = NFSCodeEnv.resolveRedeclaredItem(ty_item, ty_env)
                      ty_env = NFSCodeEnv.mergeItemEnv(ty_item, ty_env)
                      NFSCodeCheck.checkRecursiveComponentDeclaration(name, info, ty_env, ty_item, inEnv)
                      redecls = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
                      (ty_item, ty_env, _) = NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv(redecls, ty_item, ty_env, inEnv, NFInstPrefix.emptyPrefix)
                      analyseModifier(mods, inEnv, ty_env, info)
                      analyseOptExp(cond_exp, inEnv, info)
                      analyseConstrainClass(SCodeUtil.replaceableOptConstraint(SCodeUtil.prefixesReplaceable(prefixes)), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, restriction = SCode.R_OPERATOR(__), info = info), _, _, SCode.R_RECORD(true))  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, restriction = SCode.R_OPERATOR(__), info = info), _, _, _)  => begin
                      str = SCodeDump.restrString(inClassRestriction)
                      Error.addSourceMessage(Error.OPERATOR_FUNCTION_NOT_EXPECTED, list(name, str), info)
                    fail()
                  end
                  
                  (SCode.CLASS(name = name, restriction = SCode.R_FUNCTION(SCode.FR_OPERATOR_FUNCTION(__)), info = info), _, _, SCode.R_RECORD(true))  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, restriction = SCode.R_FUNCTION(SCode.FR_OPERATOR_FUNCTION(__)), info = info), _, _, _)  => begin
                      str = SCodeDump.restrString(inClassRestriction)
                      Error.addSourceMessage(Error.OPERATOR_FUNCTION_NOT_EXPECTED, list(name, str), info)
                    fail()
                  end
                  
                  (SCode.CLASS(name = name, restriction = res, info = info), _, _, SCode.R_OPERATOR(__))  => begin
                      @match true = SCodeUtil.isFunctionOrExtFunctionRestriction(res)
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, restriction = res, info = info), _, _, SCode.R_OPERATOR(__))  => begin
                      @match false = SCodeUtil.isFunctionOrExtFunctionRestriction(res)
                      str = SCodeDump.restrString(res)
                      Error.addSourceMessage(Error.OPERATOR_FUNCTION_EXPECTED, list(name, str), info)
                    fail()
                  end
                  
                  (SCode.CLASS(name = name && "equalityConstraint", info = info), _, _, _)  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, info = info, classDef = SCode.CLASS_EXTENDS(__)), _, _, _)  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, prefixes = SCode.PREFIXES(innerOuter = Absyn.INNER(__)), info = info), _, _, _)  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  (SCode.CLASS(name = name, prefixes = SCode.PREFIXES(innerOuter = Absyn.INNER_OUTER(__)), info = info), _, _, _)  => begin
                      analyseClass(Absyn.IDENT(name), inEnv, info)
                    inExtends
                  end
                  
                  _  => begin
                      inExtends
                  end
                end
              end
               #=  An extends-clause.
               =#
               #= print(\"bc = \" + AbsynUtil.pathString(bc) + \"\\n\");
               =#
               #= print(\"bc2 = \" + AbsynUtil.pathString(bc2) + \"\\n\");
               =#
               #=  A component.
               =#
               #=  *always* keep constants and parameters!
               =#
               #=  markAsUsedOnConstant(name, attr, inEnv, info);
               =#
               #=  analyseItemIfRedeclares(repls, ty_item, ty_env);
               =#
               #= operators in operator record might be used later.
               =#
               #= operators in any other class type are error.
               =#
               #= operator functions in operator record might be used later.
               =#
               #= operators functions in any other class type are error.
               =#
               #= functions in operator might be used later.
               =#
               #=  Allowing external functions to be used operator functions
               =#
               #= operators should only contain function definitions
               =#
               #=  equalityConstraints may not be explicitly used but might be needed anyway
               =#
               #=  (if the record is used in a connect for example), so always mark it as used.
               =#
               #=  inner/innerouter classes may not be explicitly used but might be needed anyway
               =#
               #=  inner/innerouter classes may not be explicitly used but might be needed anyway
               =#
          outExtends
        end

        function markAsUsedOnConstant(inName::SCode.Ident, inAttr::SCode.Attributes, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local cls_and_vars::EnvTree.Tree
                  local is_used::MutableType{Bool}
                  local var::SCode.Variability
                @matchcontinue (inName, inAttr, inEnv, inInfo) begin
                  (_, SCode.ATTR(variability = var), NFSCodeEnv.FRAME(clsAndVars = cls_and_vars) <| _, _)  => begin
                      @match true = SCodeUtil.isParameterOrConst(var)
                      @match NFSCodeEnv.VAR(isUsed = SOME(is_used)) = EnvTree.get(cls_and_vars, inName)
                      Mutable.update(is_used, true)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function markAsUsedOnRestriction(inName::SCode.Ident, inRestriction::SCode.Restriction, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local cls_and_vars::EnvTree.Tree
                  local is_used::MutableType{Bool}
                @matchcontinue (inName, inRestriction, inEnv, inInfo) begin
                  (_, _, NFSCodeEnv.FRAME(clsAndVars = cls_and_vars) <| _, _)  => begin
                      @match true = markAsUsedOnRestriction2(inRestriction)
                      @match NFSCodeEnv.VAR(isUsed = SOME(is_used)) = EnvTree.get(cls_and_vars, inName)
                      Mutable.update(is_used, true)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function markAsUsedOnRestriction2(inRestriction::SCode.Restriction) ::Bool 
              local isRestricted::Bool

              isRestricted = begin
                @match inRestriction begin
                  SCode.R_CONNECTOR(__)  => begin
                    true
                  end
                  
                  SCode.R_RECORD(_)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          isRestricted
        end

         #= Analyses an extends-clause. =#
        function analyseExtends(inClassName::Absyn.Path, inEnv::Env, inInfo::SourceInfo)  
              local item::Item
              local env::Env

              (item, env) = lookupClass(inClassName, inEnv, true, inInfo, NONE())
              analyseItem(item, env)
        end

         #= Analyses a components attributes (actually only the array dimensions). =#
        function analyseAttributes(inAttributes::SCode.Attributes, inEnv::Env, inInfo::SourceInfo)  
              local ad::Absyn.ArrayDim

              @match SCode.ATTR(arrayDims = ad) = inAttributes
              ListUtil.map2_0(ad, analyseSubscript, inEnv, inInfo)
        end

         #= Analyses a modifier. =#
        function analyseModifier(inModifier::SCode.Mod, inEnv::Env, inTypeEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local el::SCode.Element
                  local sub_mods::List{SCode.SubMod}
                  local bind_exp::Option{Absyn.Exp}
                   #=  No modifier.
                   =#
                @match (inModifier, inEnv, inTypeEnv, inInfo) begin
                  (SCode.NOMOD(__), _, _, _)  => begin
                    ()
                  end
                  
                  (SCode.MOD(subModLst = sub_mods, binding = bind_exp), _, _, _)  => begin
                      ListUtil.map2_0(sub_mods, analyseSubMod, (inEnv, inTypeEnv), inInfo)
                      analyseModBinding(bind_exp, inEnv, inInfo)
                    ()
                  end
                  
                  (SCode.REDECL(element = el), _, _, _)  => begin
                      analyseRedeclareModifier(el, inEnv, inTypeEnv)
                    ()
                  end
                end
              end
               #=  A normal modifier, analyse it's submodifiers and optional binding.
               =#
               #=  A redeclaration modifier, analyse the redeclaration.
               =#
        end

         #= Analyses a redeclaration modifier element. =#
        function analyseRedeclareModifier(inElement::SCode.Element, inEnv::Env, inTypeEnv::Env)  
              _ = begin
                  local cdef::SCode.ClassDef
                  local info::SourceInfo
                  local restr::SCode.Restriction
                  local prefixes::SCode.Prefixes
                  local ts::Absyn.TypeSpec
                  local item::Item
                  local env::Env
                   #=  call analyseClassDef
                   =#
                @matchcontinue (inElement, inEnv, inTypeEnv) begin
                  (SCode.CLASS(prefixes = prefixes, classDef = cdef, restriction = restr, info = info), _, _)  => begin
                      analyseClassDef(cdef, restr, inEnv, true, info)
                      analyseConstrainClass(SCodeUtil.replaceableOptConstraint(SCodeUtil.prefixesReplaceable(prefixes)), inEnv, info)
                    ()
                  end
                  
                  _  => begin
                        _ = analyseElement(inElement, inEnv, nil, SCode.R_CLASS())
                      ()
                  end
                end
              end
               #=  Otherwise we can just use analyseElements.
               =#
        end

         #= Analyses a constrain class, i.e. given by constrainedby. =#
        function analyseConstrainClass(inCC::Option{<:SCode.ConstrainClass}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local path::Absyn.Path
                  local mod::SCode.Mod
                  local env::Env
                @match (inCC, inEnv, inInfo) begin
                  (SOME(SCode.CONSTRAINCLASS(constrainingClass = path, modifier = mod)), _, _)  => begin
                      analyseClass(path, inEnv, inInfo)
                      (_, env) = lookupClass(path, inEnv, true, inInfo, SOME(Error.LOOKUP_ERROR))
                      analyseModifier(mod, inEnv, env, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Analyses a submodifier. =#
        function analyseSubMod(inSubMod::SCode.SubMod, inEnv::Tuple{<:Env, Env}, inInfo::SourceInfo)  
              _ = begin
                  local ident::SCode.Ident
                  local m::SCode.Mod
                  local subs::List{SCode.Subscript}
                  local env::Env
                  local ty_env::Env
                @match (inSubMod, inEnv, inInfo) begin
                  (SCode.NAMEMOD(ident = ident, mod = m), (env, ty_env), _)  => begin
                      analyseNameMod(ident, env, ty_env, m, inInfo)
                    ()
                  end
                end
              end
        end

        function analyseNameMod(inIdent::SCode.Ident, inEnv::Env, inTypeEnv::Env, inMod::SCode.Mod, inInfo::SourceInfo)  
              local item::Option{Item}
              local env::Option{Env}

              (item, env) = lookupNameMod(Absyn.IDENT(inIdent), inTypeEnv, inInfo)
              analyseNameMod2(inIdent, item, env, inEnv, inTypeEnv, inMod, inInfo)
        end

        function analyseNameMod2(inIdent::SCode.Ident, inItem::Option{<:Item}, inItemEnv::Option{<:Env}, inEnv::Env, inTypeEnv::Env, inModifier::SCode.Mod, inInfo::SourceInfo)  
              _ = begin
                  local item::Item
                  local env::Env
                @match (inIdent, inItem, inItemEnv, inEnv, inTypeEnv, inModifier, inInfo) begin
                  (_, SOME(item), SOME(env), _, _, _, _)  => begin
                      NFSCodeCheck.checkModifierIfRedeclare(item, inModifier, inInfo)
                      analyseItem(item, env)
                      env = NFSCodeEnv.mergeItemEnv(item, env)
                      analyseModifier(inModifier, inEnv, env, inInfo)
                    ()
                  end
                  
                  _  => begin
                        analyseModifier(inModifier, inEnv, inTypeEnv, inInfo)
                      ()
                  end
                end
              end
        end

        function lookupNameMod(inPath::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Option{Item}, Option{Env}} 
              local outEnv::Option{Env}
              local outItem::Option{Item}

              (outItem, outEnv) = begin
                  local item::Item
                  local env::Env
                @matchcontinue (inPath, inEnv, inInfo) begin
                  (_, _, _)  => begin
                      (item, _, env) = NFSCodeLookup.lookupNameSilent(inPath, inEnv, inInfo)
                      (item, env, _) = NFSCodeEnv.resolveRedeclaredItem(item, env)
                    (SOME(item), SOME(env))
                  end
                  
                  _  => begin
                      (NONE(), NONE())
                  end
                end
              end
          (outItem, outEnv)
        end

         #= Analyses a subscript. =#
        function analyseSubscript(inSubscript::SCode.Subscript, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local sub_exp::Absyn.Exp
                @match (inSubscript, inEnv, inInfo) begin
                  (Absyn.NOSUB(__), _, _)  => begin
                    ()
                  end
                  
                  (Absyn.SUBSCRIPT(sub_exp), _, _)  => begin
                      analyseExp(sub_exp, inEnv, inInfo)
                    ()
                  end
                end
              end
        end

         #= Analyses an optional modifier binding. =#
        function analyseModBinding(inBinding::Option{<:Absyn.Exp}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local bind_exp::Absyn.Exp
                @match inBinding begin
                  NONE()  => begin
                    ()
                  end
                  
                  SOME(bind_exp)  => begin
                      analyseExp(bind_exp, inEnv, inInfo)
                    ()
                  end
                end
              end
        end

         #= Analyses a type specificer. =#
        function analyseTypeSpec(inTypeSpec::Absyn.TypeSpec, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local type_path::Absyn.Path
                  local tys::List{Absyn.TypeSpec}
                  local ad::Option{Absyn.ArrayDim}
                   #=  A normal type.
                   =#
                @match (inTypeSpec, inEnv, inInfo) begin
                  (Absyn.TPATH(path = type_path, arrayDim = ad), _, _)  => begin
                      analyseClass(type_path, inEnv, inInfo)
                      analyseTypeSpecDims(ad, inEnv, inInfo)
                    ()
                  end
                  
                  (Absyn.TCOMPLEX(path = Absyn.IDENT("polymorphic")), _, _)  => begin
                    ()
                  end
                  
                  (Absyn.TCOMPLEX(typeSpecs = tys), _, _)  => begin
                      ListUtil.map2_0(tys, analyseTypeSpec, inEnv, inInfo)
                    ()
                  end
                end
              end
               #=  A polymorphic type, i.e. replaceable type Type subtypeof Any.
               =#
               #=  A MetaModelica type such as list or tuple.
               =#
        end

        function analyseTypeSpecDims(inDims::Option{<:Absyn.ArrayDim}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local dims::Absyn.ArrayDim
                @match (inDims, inEnv, inInfo) begin
                  (SOME(dims), _, _)  => begin
                      ListUtil.map2_0(dims, analyseTypeSpecDim, inEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function analyseTypeSpecDim(inDim::Absyn.Subscript, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local dim::Absyn.Exp
                @match (inDim, inEnv, inInfo) begin
                  (Absyn.NOSUB(__), _, _)  => begin
                    ()
                  end
                  
                  (Absyn.SUBSCRIPT(subscript = dim), _, _)  => begin
                      analyseExp(dim, inEnv, inInfo)
                    ()
                  end
                end
              end
        end

         #= Analyses an external declaration. =#
        function analyseExternalDecl(inExtDecl::Option{<:SCode.ExternalDecl}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local ann::SCode.Annotation
                  local args::List{Absyn.Exp}
                   #=  An external declaration might have arguments that we need to analyse.
                   =#
                @match (inExtDecl, inEnv, inInfo) begin
                  (SOME(SCode.EXTERNALDECL(args = args, annotation_ = NONE())), _, _)  => begin
                      ListUtil.map2_0(args, analyseExp, inEnv, inInfo)
                    ()
                  end
                  
                  (SOME(SCode.EXTERNALDECL(args = args, annotation_ = SOME(ann))), _, _)  => begin
                      ListUtil.map2_0(args, analyseExp, inEnv, inInfo)
                      analyseAnnotation(ann, inEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  An external declaration might have arguments and an annotation that we need to analyse.
               =#
        end

         #= Analyses an optional comment. =#
        function analyseComment(inComment::SCode.Comment, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local ann::SCode.Annotation
                   #=  A comment might have an annotation that we need to analyse.
                   =#
                @match (inComment, inEnv, inInfo) begin
                  (SCode.COMMENT(annotation_ = SOME(ann)), _, _)  => begin
                      analyseAnnotation(ann, inEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Analyses an annotation. =#
        function analyseAnnotation(inAnnotation::SCode.Annotation, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local mods::SCode.Mod
                  local sub_mods::List{SCode.SubMod}
                @match (inAnnotation, inEnv, inInfo) begin
                  (SCode.ANNOTATION(modification = SCode.MOD(subModLst = sub_mods)), _, _)  => begin
                      ListUtil.map2_0(sub_mods, analyseAnnotationMod, inEnv, inInfo)
                    ()
                  end
                end
              end
        end

         #= Analyses an annotation modifier. =#
        function analyseAnnotationMod(inMod::SCode.SubMod, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local mods::SCode.Mod
                  local id::String
                   #=  derivative is a bit special since it's not a builtin function, so just
                   =#
                   #=  analyse it's modifier to make sure that we get the derivation function.
                   =#
                @matchcontinue (inMod, inEnv, inInfo) begin
                  (SCode.NAMEMOD(ident = "derivative", mod = mods), _, _)  => begin
                      analyseModifier(mods, inEnv, NFSCodeEnv.emptyEnv, inInfo)
                    ()
                  end
                  
                  (SCode.NAMEMOD(ident = id, mod = mods), _, _)  => begin
                      analyseAnnotationName(id, inEnv, inInfo)
                      analyseModifier(mods, inEnv, NFSCodeEnv.emptyEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  Otherwise, try to analyse the modifier name, and if that succeeds also
               =#
               #=  try and analyse the rest of the modification. This is needed for example
               =#
               #=  for the graphical annotations such as Icon.
               =#
        end

         #= Analyses an annotation name, such as Icon or Line. =#
        function analyseAnnotationName(inName::SCode.Ident, inEnv::Env, inInfo::SourceInfo)  
              local item::Item
              local env::Env

              (item, _, env) = NFSCodeLookup.lookupNameSilent(Absyn.IDENT(inName), inEnv, inInfo)
              (item, env, _) = NFSCodeEnv.resolveRedeclaredItem(item, env)
              analyseItem(item, env)
        end

         #= Recursively analyses an expression. =#
        function analyseExp(inExp::Absyn.Exp, inEnv::Env, inInfo::SourceInfo)  
              (_, _) = AbsynUtil.traverseExpBidir(inExp, analyseExpTraverserEnter, analyseExpTraverserExit, (inEnv, inInfo))
        end

         #= Recursively analyses an optional expression. =#
        function analyseOptExp(inExp::Option{<:Absyn.Exp}, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local exp::Absyn.Exp
                @match (inExp, inEnv, inInfo) begin
                  (SOME(exp), _, _)  => begin
                      analyseExp(exp, inEnv, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Traversal enter function for use in analyseExp. =#
        function analyseExpTraverserEnter(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              local env::Env
              local info::SourceInfo

              (env, info) = inTuple
              env = analyseExp2(inExp, env, info)
              outExp = inExp
              outTuple = (env, info)
          (outExp, outTuple)
        end

         #= Helper function to analyseExp, does the actual work. =#
        function analyseExp2(inExp::Absyn.Exp, inEnv::Env, inInfo::SourceInfo) ::Env 
              local outEnv::Env

              outEnv = begin
                  local cref::Absyn.ComponentRef
                  local args::Absyn.FunctionArgs
                  local iters::Absyn.ForIterators
                  local env::Env
                @match (inExp, inEnv, inInfo) begin
                  (Absyn.CREF(componentRef = cref), _, _)  => begin
                      analyseCref(cref, inEnv, inInfo)
                    inEnv
                  end
                  
                  (Absyn.CALL(function_ = cref, functionArgs = Absyn.FOR_ITER_FARG(iterators = iters)), _, _)  => begin
                      analyseCref(cref, inEnv, inInfo)
                      env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv)
                    env
                  end
                  
                  (Absyn.CALL(function_ = cref), _, _)  => begin
                      analyseCref(cref, inEnv, inInfo)
                    inEnv
                  end
                  
                  (Absyn.PARTEVALFUNCTION(function_ = cref), _, _)  => begin
                      analyseCref(cref, inEnv, inInfo)
                    inEnv
                  end
                  
                  (Absyn.MATCHEXP(__), _, _)  => begin
                      env = NFSCodeEnv.extendEnvWithMatch(inExp, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), inEnv)
                    env
                  end
                  
                  _  => begin
                      inEnv
                  end
                end
              end
               #=  For user-defined reductions
               =#
          outEnv
        end

         #= Analyses a component reference. =#
        function analyseCref(inCref::Absyn.ComponentRef, inEnv::Env, inInfo::SourceInfo)  
              _ = begin
                  local path::Absyn.Path
                  local item::Item
                  local env::Env
                @matchcontinue (inCref, inEnv, inInfo) begin
                  (Absyn.WILD(__), _, _)  => begin
                    ()
                  end
                  
                  (_, _, _)  => begin
                      path = AbsynUtil.crefToPathIgnoreSubs(inCref)
                      (item, env) = lookupClass(path, inEnv, true, inInfo, NONE())
                      analyseItem(item, env)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  We want to use lookupClass since we need the item and environment, and
               =#
               #=  we don't care about any subscripts, so convert the cref to a path.
               =#
        end

         #= Traversal exit function for use in analyseExp. =#
        function analyseExpTraverserExit(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              (outExp, outTuple) = begin
                  local e::Absyn.Exp
                  local env::Env
                  local info::SourceInfo
                   #=  Remove any scopes added by the enter function.
                   =#
                @match (inExp, inTuple) begin
                  (Absyn.CALL(functionArgs = Absyn.FOR_ITER_FARG(__)), (NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)) <| env, info))  => begin
                    (inExp, (env, info))
                  end
                  
                  (Absyn.MATCHEXP(__), (NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)) <| env, info))  => begin
                    (inExp, (env, info))
                  end
                  
                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
          (outExp, outTuple)
        end

         #= Analyses an equation. =#
        function analyseEquation(inEquation::SCode.Equation, inEnv::Env)  
              local equ::SCode.EEquation

              @match SCode.EQUATION(equ) = inEquation
              (_, _) = SCodeUtil.traverseEEquations(equ, (analyseEEquationTraverser, inEnv))
        end

         #= Traversal function for use in analyseEquation. =#
        function analyseEEquationTraverser(inTuple::Tuple{<:SCode.EEquation, Env}) ::Tuple{SCode.EEquation, Env} 
              local outTuple::Tuple{SCode.EEquation, Env}

              outTuple = begin
                  local equ::SCode.EEquation
                  local iter_name::SCode.Ident
                  local env::Env
                  local info::SourceInfo
                  local cref1::Absyn.ComponentRef
                @match inTuple begin
                  (equ && SCode.EQ_FOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                  
                  (equ && SCode.EQ_REINIT(cref = Absyn.CREF(componentRef = cref1), info = info), env)  => begin
                      analyseCref(cref1, env, info)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                  
                  (equ, env)  => begin
                      info = SCodeUtil.getEEquationInfo(equ)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                end
              end
          outTuple
        end

         #= Traversal function used by analyseEEquationTraverser and
          analyseStatementTraverser. =#
        function traverseExp(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              (outExp, outTuple) = AbsynUtil.traverseExpBidir(inExp, analyseExpTraverserEnter, analyseExpTraverserExit, inTuple)
          (outExp, outTuple)
        end

         #= Analyses an algorithm. =#
        function analyseAlgorithm(inAlgorithm::SCode.AlgorithmSection, inEnv::Env)  
              local stmts::List{SCode.Statement}

              @match SCode.ALGORITHM(stmts) = inAlgorithm
              ListUtil.map1_0(stmts, analyseStatement, inEnv)
        end

         #= Analyses a statement in an algorithm. =#
        function analyseStatement(inStatement::SCode.Statement, inEnv::Env)  
              (_, _) = SCodeUtil.traverseStatements(inStatement, (analyseStatementTraverser, inEnv))
        end

         #= Traversal function used by analyseStatement. =#
        function analyseStatementTraverser(inTuple::Tuple{<:SCode.Statement, Env}) ::Tuple{SCode.Statement, Env} 
              local outTuple::Tuple{SCode.Statement, Env}

              outTuple = begin
                  local env::Env
                  local stmt::SCode.Statement
                  local info::SourceInfo
                  local parforBody::List{SCode.Statement}
                  local iter_name::String
                @match inTuple begin
                  (stmt && SCode.ALG_FOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (_, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                  
                  (stmt && SCode.ALG_PARFOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (_, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                  
                  (stmt, env)  => begin
                      info = SCodeUtil.getStatementInfo(stmt)
                      (_, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                end
              end
          outTuple
        end

         #= Goes through the environment and checks if class extends are used or not.
          This is done since class extends are sometimes implicitly used (see for
          example the test case mofiles/ClassExtends3.mo), so only going through the
          first phase of the dependency analysis is not enough to find all class extends
          that are used. Adding all class extends would also be problematic, since we
          would have to make sure that any class extend and it's dependencies are marked
          as used.

          This phase goes through all used classes, and if it finds a class extends in
          one of them it sets the use flag to the same as the base class. This is not a
          perfect solution since it means that all class extends that extend a certain
          base class will be marked as used, even if only one of them actually use the
          base class. So we might get some extra dependencies that are actually not
          used, but it's still better then marking all class extends in the program as
          used. =#
        function analyseClassExtends(inEnv::Env)  
              local tree::EnvTree.Tree

              @match _cons(NFSCodeEnv.FRAME(clsAndVars = tree), _) = inEnv
              _ = EnvTree.foldCond(tree, analyseAvlValue, inEnv)
        end

         #= Helper function to analyseClassExtends. Analyses a value in the EnvTree. =#
        function analyseAvlValue(key::String, value::Item, env::Env) ::Tuple{Env, Bool} 
              local cont::Bool


              cont = begin
                  local key_str::String
                  local cls_env::NFSCodeEnv.Frame
                  local env2::Env
                  local cls::SCode.Element
                  local cls_ty::NFSCodeEnv.ClassType
                  local is_used::MutableType{Bool}
                   #=  Check if the current environment is not used, we can quit here if that's
                   =#
                   #=  the case.
                   =#
                @matchcontinue (value, env) begin
                  (_, NFSCodeEnv.FRAME(name = SOME(_), isUsed = SOME(is_used)) <| _)  => begin
                      @match false = Mutable.access(is_used)
                    false
                  end
                  
                  (NFSCodeEnv.CLASS(cls = cls, env = cls_env <|  nil(), classType = cls_ty), _)  => begin
                      env2 = NFSCodeEnv.enterFrame(cls_env, env)
                      analyseClassExtendsDef(cls, cls_ty, env2)
                      analyseClassExtends(env2)
                    true
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
               #=  Check all classes inside of this class too.
               =#
          (env, cont)
        end

         #= Analyses a class extends definition. =#
        function analyseClassExtendsDef(inClass::SCode.Element, inClassType::NFSCodeEnv.ClassType, inEnv::Env)  
              _ = begin
                  local item::Item
                  local info::SourceInfo
                  local bc::Absyn.Path
                  local cls_name::String
                  local env::Env
                @matchcontinue (inClass, inClassType, inEnv) begin
                  (SCode.CLASS(name = cls_name, classDef = SCode.PARTS(elementLst = SCode.EXTENDS(baseClassPath = bc) <| _), info = info), NFSCodeEnv.CLASS_EXTENDS(__), _)  => begin
                      (item, _, env) = NFSCodeLookup.lookupBaseClassName(bc, inEnv, info)
                      @match true = NFSCodeEnv.isItemUsed(item)
                      @match _cons(_, env) = inEnv
                      analyseClass(Absyn.IDENT(cls_name), env, info)
                    ()
                  end
                  
                  (SCode.CLASS(name = cls_name, info = info), NFSCodeEnv.USERDEFINED(__), _)  => begin
                      @match true = SCodeUtil.isElementRedeclare(inClass)
                      @match _cons(_, env) = inEnv
                      item = NFSCodeEnv.CLASS(inClass, NFSCodeEnv.emptyEnv, inClassType)
                      (item, _) = NFSCodeLookup.lookupRedeclaredClassByItem(item, env, info)
                      @match true = NFSCodeEnv.isItemUsed(item)
                      analyseClass(Absyn.IDENT(cls_name), env, info)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
               #=  Look up the base class of the class extends, and check if it's used.
               =#
               #=  Ok, the base is used, analyse the class extends to mark it and it's
               =#
               #=  dependencies as used.
               =#
        end

         #= Entry point for the second phase in the dependency analysis. Goes through the
           environment and collects the used elements in a new program and environment.
           Also returns a list of all global constants. =#
        function collectUsedProgram(inEnv::Env, inProgram::SCode.Program, inClassName::Absyn.Path) ::Tuple{Env, SCode.Program} 
              local outProgram::SCode.Program
              local outEnv::Env

              local env::Env
              local cls_and_vars::EnvTree.Tree

              env = NFSCodeEnv.buildInitialEnv()
              @match _cons(NFSCodeEnv.FRAME(clsAndVars = cls_and_vars), _) = inEnv
              (outProgram, outEnv) = collectUsedProgram2(cls_and_vars, inEnv, inProgram, inClassName, env)
          (outEnv, outProgram)
        end

         #= Helper function to collectUsedProgram2. Goes through each top-level class in
          the program and collects them if they are used. This is to preserve the order
          of the classes in the new program. Another alternative would have been to just
          traverse the environment and collect the used classes, which would have been a
          bit faster but would not have preserved the order of the program. =#
        function collectUsedProgram2(clsAndVars::EnvTree.Tree, inEnv::Env, inProgram::SCode.Program, inClassName::Absyn.Path, inAccumEnv::Env) ::Tuple{SCode.Program, Env} 
              local outAccumEnv::Env
              local outProgram::SCode.Program

              (outProgram, outAccumEnv) = begin
                  local cls_el::SCode.Element
                  local cls::SCode.Element
                  local rest_prog::SCode.Program
                  local name::String
                  local env::Env
                   #=  We're done!
                   =#
                @matchcontinue (clsAndVars, inEnv, inProgram, inClassName, inAccumEnv) begin
                  (_, _,  nil(), _, _)  => begin
                    (inProgram, inAccumEnv)
                  end
                  
                  (_, _, cls && SCode.CLASS(name = name) <| rest_prog, _, env)  => begin
                      @match ((@match SCode.CLASS() = cls_el), env) = collectUsedClass(cls, inEnv, clsAndVars, inClassName, env, Absyn.IDENT(name))
                      (rest_prog, env) = collectUsedProgram2(clsAndVars, inEnv, rest_prog, inClassName, env)
                    (_cons(cls_el, rest_prog), env)
                  end
                  
                  (_, _, SCode.CLASS(__) <| rest_prog, _, env)  => begin
                      (rest_prog, env) = collectUsedProgram2(clsAndVars, inEnv, rest_prog, inClassName, env)
                    (rest_prog, env)
                  end
                end
              end
               #=  Try to collect the first class in the list.
               =#
               #=  Could not collect the class (i.e. it's not used), continue with the rest.
               =#
          (outProgram, outAccumEnv)
        end

         #= Checks if the given class is used in the program, and if that's the case it
          adds the class to the accumulated environment. Otherwise it just fails. =#
        function collectUsedClass(inClass::SCode.Element, inEnv::Env, inClsAndVars::EnvTree.Tree, inClassName::Absyn.Path, inAccumEnv::Env, inAccumPath::Absyn.Path) ::Tuple{SCode.Element, Env} 
              local outAccumEnv::Env
              local outClass::SCode.Element

              (outClass, outAccumEnv) = begin
                  local name::SCode.Ident
                  local basename::SCode.Ident
                  local prefixes::SCode.Prefixes
                  local res::SCode.Restriction
                  local cdef::SCode.ClassDef
                  local ep::SCode.Encapsulated
                  local pp::SCode.Partial
                  local info::SourceInfo
                  local item::Item
                  local resolved_item::Item
                  local class_frame::NFSCodeEnv.Frame
                  local class_env::Env
                  local env::Env
                  local enclosing_env::Env
                  local cc::Option{SCode.ConstrainClass}
                  local cls::SCode.Element
                  local cmt::SCode.Comment
                @match (inClass, inEnv, inClsAndVars, inClassName, inAccumEnv, inAccumPath) begin
                  (SCode.CLASS(name, prefixes && SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_)), ep, pp, res, cdef, cmt, info), _, _, _, _, _)  => begin
                      item = EnvTree.get(inClsAndVars, name)
                      (resolved_item, _) = NFSCodeLookup.resolveAlias(item, inEnv)
                      @match true = checkClassUsed(resolved_item, cdef)
                      @match list(class_frame) = NFSCodeEnv.getItemEnv(resolved_item)
                      enclosing_env = NFSCodeEnv.enterScope(inEnv, name)
                      (cdef, class_env) = collectUsedClassDef(cdef, enclosing_env, class_frame, inClassName, inAccumPath)
                      cls = SCode.CLASS(name, prefixes, ep, pp, res, cdef, cmt, info)
                      resolved_item = updateItemEnv(resolved_item, cls, class_env)
                      basename = name + NFSCodeEnv.BASE_CLASS_SUFFIX
                      env = NFSCodeEnv.extendEnvWithItem(resolved_item, inAccumEnv, basename)
                      env = NFSCodeEnv.extendEnvWithItem(item, env, name)
                    (cls, env)
                  end
                  
                  (SCode.CLASS(name, prefixes, ep, pp, res, cdef, cmt, info), _, _, _, _, _)  => begin
                      _ = SCodeUtil.replaceableOptConstraint(SCodeUtil.prefixesReplaceable(prefixes))
                      item = EnvTree.get(inClsAndVars, name)
                      @match true = checkClassUsed(item, cdef)
                      @match list(class_frame) = NFSCodeEnv.getItemEnv(item)
                      enclosing_env = NFSCodeEnv.enterScope(inEnv, name)
                      (cdef, class_env) = collectUsedClassDef(cdef, enclosing_env, class_frame, inClassName, inAccumPath)
                      cls = SCode.CLASS(name, prefixes, ep, pp, res, cdef, cmt, info)
                      item = updateItemEnv(item, cls, class_env)
                      env = NFSCodeEnv.extendEnvWithItem(item, inAccumEnv, name)
                    (cls, env)
                  end
                end
              end
               #= /*********************************************************************/ =#
               #=  TODO: Fix the usage of alias items in this case.
               =#
               #= /*********************************************************************/ =#
               #=  Check if the class is used.
               =#
               #=  The class is used, recursively collect its contents.
               =#
               #=  TODO! FIXME! add cc to the used classes!
               =#
               #=  Check if the class is used.
               =#
               #=  The class is used, recursively collect it's contents.
               =#
               #=  Add the class to the new environment.
               =#
          (outClass, outAccumEnv)
        end

         #= Given the environment item and definition for a class, returns whether the
          class is used or not. =#
        function checkClassUsed(inItem::Item, inClassDef::SCode.ClassDef) ::Bool 
              local isUsed::Bool

              isUsed = begin
                @match (inItem, inClassDef) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = "GraphicalAnnotationsProgram____")), _)  => begin
                    true
                  end
                  
                  _  => begin
                      NFSCodeEnv.isItemUsed(inItem)
                  end
                end
              end
               #=  GraphicalAnnotationsProgram____ is a special case, since it's not used by
               =#
               #=  anything, but needed during instantiation.
               =#
               #=  Otherwise, use the environment item to determine if the class is used or
               =#
               #=  not.
               =#
          isUsed
        end

         #= Replaces the class and environment in an environment item, preserving the
          item's type. =#
        function updateItemEnv(inItem::Item, inClass::SCode.Element, inEnv::Env) ::Item 
              local outItem::Item

              outItem = begin
                  local cls_ty::NFSCodeEnv.ClassType
                @match (inItem, inClass, inEnv) begin
                  (NFSCodeEnv.CLASS(classType = cls_ty), _, _)  => begin
                    NFSCodeEnv.CLASS(inClass, inEnv, cls_ty)
                  end
                end
              end
          outItem
        end

         #= Collects the contents of a class definition. =#
        function collectUsedClassDef(classDef::SCode.ClassDef, env::Env, inClassEnv::NFSCodeEnv.Frame, inClassName::Absyn.Path, inAccumPath::Absyn.Path) ::Tuple{SCode.ClassDef, Env} 



              () = begin
                  local el::List{SCode.Element}
                  local cdef::SCode.ClassDef
                @match classDef begin
                  SCode.PARTS(elementLst = el)  => begin
                      (el, env) = collectUsedElements(el, env, inClassEnv, inClassName, inAccumPath)
                      classDef.elementLst = el
                    ()
                  end
                  
                  SCode.CLASS_EXTENDS(composition = cdef)  => begin
                      (cdef, env) = collectUsedClassDef(cdef, env, inClassEnv, inClassName, inAccumPath)
                      classDef.composition = cdef
                    ()
                  end
                  
                  _  => begin
                        env = list(inClassEnv)
                      ()
                  end
                end
              end
          (classDef, env)
        end

         #= Collects a class definition's elements. =#
        function collectUsedElements(inElements::List{<:SCode.Element}, inEnv::Env, inClassEnv::NFSCodeEnv.Frame, inClassName::Absyn.Path, inAccumPath::Absyn.Path) ::Tuple{List{SCode.Element}, Env} 
              local outNewEnv::Env
              local outUsedElements::List{SCode.Element}

              local empty_class_env::NFSCodeEnv.Frame
              local cls_and_vars::EnvTree.Tree
              local collect_constants::Bool

               #=  Create a new class environment that preserves the imports and extends.
               =#
              (empty_class_env, cls_and_vars) = NFSCodeEnv.removeClsAndVarsFromFrame(inClassEnv)
               #=  Collect all constants in the top class, even if they're not used.
               =#
               #=  This makes it easier to write test cases.
               =#
              collect_constants = AbsynUtil.pathEqual(inClassName, inAccumPath)
              (outUsedElements, outNewEnv) = collectUsedElements2(inElements, inEnv, cls_and_vars, nil, list(empty_class_env), inClassName, inAccumPath, collect_constants)
              outNewEnv = removeUnusedRedeclares(outNewEnv, inEnv)
          (outUsedElements, outNewEnv)
        end

         #= Helper function to collectUsedElements2. Goes through the given list of
          elements and tries to collect them. =#
        function collectUsedElements2(inElements::List{<:SCode.Element}, inEnclosingEnv::Env, inClsAndVars::EnvTree.Tree, inAccumElements::List{<:SCode.Element}, inAccumEnv::Env, inClassName::Absyn.Path, inAccumPath::Absyn.Path, inCollectConstants::Bool) ::Tuple{List{SCode.Element}, Env} 
              local accum_env::Env = inAccumEnv
              local outAccumElements::List{SCode.Element} = nil

              local accum_el::SCode.Element

              for el in inElements
                try
                  (accum_el, accum_env) = collectUsedElement(el, inEnclosingEnv, inClsAndVars, accum_env, inClassName, inAccumPath, inCollectConstants)
                  outAccumElements = _cons(accum_el, outAccumElements)
                catch
                end
              end
               #=  Skip this element
               =#
              outAccumElements = listReverse(outAccumElements)
          (outAccumElements, accum_env)
        end

         #= Collects a class element. =#
        function collectUsedElement(inElement::SCode.Element, inEnclosingEnv::Env, inClsAndVars::EnvTree.Tree, inAccumEnv::Env, inClassName::Absyn.Path, inAccumPath::Absyn.Path, inCollectConstants::Bool) ::Tuple{SCode.Element, Env} 
              local outAccumEnv::Env
              local outElement::SCode.Element

              (outElement, outAccumEnv) = begin
                  local name::SCode.Ident
                  local cls::SCode.Element
                  local env::Env
                  local item::Item
                  local cls_path::Absyn.Path
                   #=  A class definition, just use collectUsedClass.
                   =#
                @match (inElement, inEnclosingEnv, inClsAndVars, inAccumEnv, inClassName, inAccumPath, inCollectConstants) begin
                  (SCode.CLASS(name = name), _, _, env, _, _, _)  => begin
                      cls_path = AbsynUtil.joinPaths(inAccumPath, Absyn.IDENT(name))
                      (cls, env) = collectUsedClass(inElement, inEnclosingEnv, inClsAndVars, inClassName, env, cls_path)
                    (cls, env)
                  end
                  
                  (SCode.COMPONENT(name = name, attributes = SCode.ATTR(variability = SCode.CONST(__))), _, _, _, _, _, _)  => begin
                      item = EnvTree.get(inClsAndVars, name)
                      @match true = inCollectConstants || NFSCodeEnv.isItemUsed(item)
                      env = NFSCodeEnv.extendEnvWithItem(item, inAccumEnv, name)
                    (inElement, env)
                  end
                  
                  (SCode.COMPONENT(name = name), _, _, _, _, _, _)  => begin
                      item = NFSCodeEnv.newVarItem(inElement, true)
                      env = NFSCodeEnv.extendEnvWithItem(item, inAccumEnv, name)
                    (inElement, env)
                  end
                  
                  _  => begin
                      (inElement, inAccumEnv)
                  end
                end
              end
               #=  A constant.
               =#
               #=  Class components are always collected, regardless of whether they are
               =#
               #=  used or not.
               =#
          (outElement, outAccumEnv)
        end

         #= An unused element might be redeclared, but it's still not actually used. This
           function removes such redeclares from extends clauses, so that it's safe to
           remove those elements. =#
        function removeUnusedRedeclares(inEnv::Env, inTotalEnv::Env) ::Env 
              local outEnv::Env

              local name::Option{String}
              local ty::NFSCodeEnv.FrameType
              local cls_and_vars::EnvTree.Tree
              local bcl::List{NFSCodeEnv.Extends}
              local re::List{SCode.Element}
              local cei::Option{SCode.Element}
              local imps::NFSCodeEnv.ImportTable
              local is_used::Option{MutableType{Bool}}
              local env::Env

              @match list(NFSCodeEnv.FRAME(name, ty, cls_and_vars, NFSCodeEnv.EXTENDS_TABLE(bcl, re, cei), imps, is_used)) = inEnv
              env = NFSCodeEnv.removeRedeclaresFromLocalScope(inTotalEnv)
              bcl = ListUtil.map1(bcl, removeUnusedRedeclares2, env)
              outEnv = list(NFSCodeEnv.FRAME(name, ty, cls_and_vars, NFSCodeEnv.EXTENDS_TABLE(bcl, re, cei), imps, is_used))
          outEnv
        end

        function removeUnusedRedeclares2(inExtends::NFSCodeEnv.Extends, inEnv::Env) ::NFSCodeEnv.Extends 
              local outExtends::NFSCodeEnv.Extends

              local bc::Absyn.Path
              local redeclares::List{NFSCodeEnv.Redeclaration}
              local index::ModelicaInteger
              local info::SourceInfo
              local env::Env

              @match NFSCodeEnv.EXTENDS(bc, redeclares, index, info) = inExtends
              redeclares = ListUtil.filter1(redeclares, removeUnusedRedeclares3, inEnv)
              outExtends = NFSCodeEnv.EXTENDS(bc, redeclares, index, info)
          outExtends
        end

        function removeUnusedRedeclares3(inRedeclare::NFSCodeEnv.Redeclaration, inEnv::Env)  
              local name::String
              local item::Item

              (name, _) = NFSCodeEnv.getRedeclarationNameInfo(inRedeclare)
              (item, _, _) = NFSCodeLookup.lookupSimpleName(name, inEnv)
              @match true = NFSCodeEnv.isItemUsed(item)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
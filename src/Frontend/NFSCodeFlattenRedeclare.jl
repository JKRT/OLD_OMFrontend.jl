  module NFSCodeFlattenRedeclare 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Replacement 

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

        import NFInstPrefix

        import NFInstTypes

        import NFSCodeLookup

        Env = NFSCodeEnv.Env 

        Item = NFSCodeEnv.Item 

        Extends = NFSCodeEnv.Extends 

        Prefix = NFInstTypes.Prefix 
        import NFSCodeEnv.EnvTree

         @Uniontype Replacement begin
              @Record REPLACED begin

                       name::SCode.Ident
                       old::Item
                       new::Item
                       env::Env
              end

              @Record PUSHED begin

                       name::SCode.Ident
                       redeclaredItem::Item
                       baseClasses::List{Absyn.Path}
                       old::NFSCodeEnv.ExtendsTable
                       new::NFSCodeEnv.ExtendsTable
                       env::Env
              end
         end

        Replacements = List 

         const emptyReplacements = nil::Replacements

        import Debug

        import Error

        import Flags

        import ListUtil

        import NFSCodeCheck

        import Util

        import SCodeDump
        import SCodeUtil

        function addElementRedeclarationsToEnv(inRedeclares::List{<:SCode.Element}, inEnv::Env) ::Env 
              local outEnv::Env

              outEnv = ListUtil.fold(inRedeclares, addElementRedeclarationsToEnv2, inEnv)
          outEnv
        end

        function addElementRedeclarationsToEnv2(inRedeclare::SCode.Element, inEnv::Env) ::Env 
              local outEnv::Env

              outEnv = begin
                  local name::SCode.Ident
                  local info::SourceInfo
                  local env_path::Absyn.Path
                  local ext_pathl::List{Absyn.Path}
                  local env::Env
                  local item::Item
                @matchcontinue (inRedeclare, inEnv) begin
                  (_, _)  => begin
                      name = SCodeUtil.elementName(inRedeclare)
                      info = SCodeUtil.elementInfo(inRedeclare)
                      ext_pathl = lookupElementRedeclaration(name, inEnv, info)
                      env_path = NFSCodeEnv.getEnvPath(inEnv)
                      item = NFSCodeEnv.ALIAS(name, SOME(env_path), info)
                      env = addRedeclareToEnvExtendsTable(item, ext_pathl, inEnv, info)
                    env
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeFlattenRedeclare.addElementRedeclarationsToEnv failed for " + SCodeUtil.elementName(inRedeclare) + " in " + NFSCodeEnv.getEnvName(inEnv) + "\\n")
                      fail()
                  end
                end
              end
          outEnv
        end

        function lookupElementRedeclaration(inName::SCode.Ident, inEnv::Env, inInfo::SourceInfo) ::List{Absyn.Path} 
              local outPaths::List{Absyn.Path}

              outPaths = begin
                  local paths::List{Absyn.Path}
                @matchcontinue (inName, inEnv, inInfo) begin
                  (_, _, _)  => begin
                      paths = NFSCodeLookup.lookupBaseClasses(inName, inEnv)
                    paths
                  end
                  
                  _  => begin
                        Error.addSourceMessage(Error.REDECLARE_NONEXISTING_ELEMENT, list(inName), inInfo)
                      fail()
                  end
                end
              end
          outPaths
        end

        function addRedeclareToEnvExtendsTable(inRedeclaredElement::Item, inBaseClasses::List{<:Absyn.Path}, inEnv::Env, inInfo::SourceInfo) ::Env 
              local outEnv::Env

              local bcl::List{Extends}
              local re::List{SCode.Element}
              local cei::Option{SCode.Element}

              @match NFSCodeEnv.EXTENDS_TABLE(bcl, re, cei) = NFSCodeEnv.getEnvExtendsTable(inEnv)
              bcl = addRedeclareToEnvExtendsTable2(inRedeclaredElement, inBaseClasses, bcl)
              outEnv = NFSCodeEnv.setEnvExtendsTable(NFSCodeEnv.EXTENDS_TABLE(bcl, re, cei), inEnv)
          outEnv
        end

        function addRedeclareToEnvExtendsTable2(inRedeclaredElement::Item, inBaseClasses::List{<:Absyn.Path}, inExtends::List{<:Extends}) ::List{Extends} 
              local outExtends::List{Extends}

              outExtends = begin
                  local ex::Extends
                  local exl::List{Extends}
                  local bc1::Absyn.Path
                  local bc2::Absyn.Path
                  local rest_bc::List{Absyn.Path}
                  local el::List{NFSCodeEnv.Redeclaration}
                  local index::ModelicaInteger
                  local info::SourceInfo
                  local redecl::NFSCodeEnv.Redeclaration
                @matchcontinue (inRedeclaredElement, inBaseClasses, inExtends) begin
                  (_, bc1 <| rest_bc, NFSCodeEnv.EXTENDS(bc2, el, index, info) <| exl)  => begin
                      @match true = AbsynUtil.pathEqual(bc1, bc2)
                      redecl = NFSCodeEnv.PROCESSED_MODIFIER(inRedeclaredElement)
                      NFSCodeCheck.checkDuplicateRedeclarations(redecl, el)
                      ex = NFSCodeEnv.EXTENDS(bc2, _cons(redecl, el), index, info)
                      exl = addRedeclareToEnvExtendsTable2(inRedeclaredElement, rest_bc, exl)
                    _cons(ex, exl)
                  end
                  
                  (_,  nil(), _)  => begin
                    inExtends
                  end
                  
                  (_, _, ex <| exl)  => begin
                      exl = addRedeclareToEnvExtendsTable2(inRedeclaredElement, inBaseClasses, exl)
                    _cons(ex, exl)
                  end
                end
              end
          outExtends
        end

         #= Processes a raw redeclare modifier into a processed form. =#
        function processRedeclare(inRedeclare::NFSCodeEnv.Redeclaration, inEnv::Env, inPrefix::NFInstTypes.Prefix) ::NFSCodeEnv.Redeclaration 
              local outRedeclare::NFSCodeEnv.Redeclaration

              outRedeclare = begin
                  local el_item::Item
                  local redecl_item::Item
                  local el::SCode.Element
                  local cls_env::Env
                @matchcontinue (inRedeclare, inEnv, inPrefix) begin
                  (NFSCodeEnv.RAW_MODIFIER(modifier = el && SCode.CLASS(__)), _, _)  => begin
                      cls_env = NFSCodeEnv.makeClassEnvironment(el, true)
                      el_item = NFSCodeEnv.newClassItem(el, cls_env, NFSCodeEnv.USERDEFINED())
                      redecl_item = NFSCodeEnv.REDECLARED_ITEM(el_item, inEnv)
                    NFSCodeEnv.PROCESSED_MODIFIER(redecl_item)
                  end
                  
                  (NFSCodeEnv.RAW_MODIFIER(modifier = el && SCode.COMPONENT(__)), _, _)  => begin
                      el_item = NFSCodeEnv.newVarItem(el, true)
                      redecl_item = NFSCodeEnv.REDECLARED_ITEM(el_item, inEnv)
                    NFSCodeEnv.PROCESSED_MODIFIER(redecl_item)
                  end
                  
                  (NFSCodeEnv.PROCESSED_MODIFIER(__), _, _)  => begin
                    inRedeclare
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeFlattenRedeclare.processRedeclare failed on " + SCodeDump.unparseElementStr(NFSCodeEnv.getRedeclarationElement(inRedeclare), SCodeDump.defaultOptions) + " in " + AbsynUtil.pathString(NFSCodeEnv.getEnvPath(inEnv)))
                      fail()
                  end
                end
              end
          outRedeclare
        end

         #= Replaces redeclares in the environment. This function takes a list of
           redeclares, the item and environment of the class in which they should be
           redeclared, and the environment in which the modified element was declared
           (used to qualify the redeclares). The redeclares are then either replaced if
           they can be found in the immediate local environment of the class, or pushed
           into the correct extends clauses if they are inherited. =#
        function replaceRedeclares(inRedeclares::List{<:NFSCodeEnv.Redeclaration}, inClassItem::Item #= The item of the class to be modified. =#, inClassEnv::Env #= The environment of the class to be modified. =#, inElementEnv::Env #= The environment in which the modified element was declared. =#, inReplaceRedeclares::NFSCodeLookup.RedeclareReplaceStrategy) ::Tuple{Option{Item}, Option{Env}} 
              local outEnv::Option{Env}
              local outItem::Option{Item}

              (outItem, outEnv) = begin
                  local item::Item
                  local env::Env
                @matchcontinue (inRedeclares, inClassItem, inClassEnv, inElementEnv, inReplaceRedeclares) begin
                  (_, _, _, _, NFSCodeLookup.IGNORE_REDECLARES(__))  => begin
                    (SOME(inClassItem), SOME(inClassEnv))
                  end
                  
                  (_, _, _, _, NFSCodeLookup.INSERT_REDECLARES(__))  => begin
                      (item, env, _) = replaceRedeclaredElementsInEnv(inRedeclares, inClassItem, inClassEnv, inElementEnv, NFInstPrefix.emptyPrefix)
                    (SOME(item), SOME(env))
                  end
                  
                  _  => begin
                      (NONE(), NONE())
                  end
                end
              end
          (outItem, outEnv)
        end

         #= If a variable or extends clause has modifications that redeclare classes in
           it's instance we need to replace those classes in the environment so that the
           lookup finds the right classes. This function takes a list of redeclares from
           an elements' modifications and applies them to the environment of the
           elements type. =#
        function replaceRedeclaredElementsInEnv(inRedeclares::List{<:NFSCodeEnv.Redeclaration} #= The redeclares from the modifications. =#, inItem::Item #= The type of the element. =#, inTypeEnv::Env #= The enclosing scopes of the type. =#, inElementEnv::Env #= The environment in which the element was declared. =#, inPrefix::NFInstTypes.Prefix) ::Tuple{Item, Env, Replacements} 
              local outReplacements::Replacements #= what replacements where performed if any =#
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv, outReplacements) = begin
                  local cls::SCode.Element
                  local env::Env
                  local item_env::NFSCodeEnv.Frame
                  local cls_ty::NFSCodeEnv.ClassType
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local repl::Replacements
                   #=  No redeclares!
                   =#
                @matchcontinue (inRedeclares, inItem, inTypeEnv, inElementEnv, inPrefix) begin
                  ( nil(), _, _, _, _)  => begin
                    (inItem, inTypeEnv, nil)
                  end
                  
                  (_, NFSCodeEnv.CLASS(cls = cls, env = item_env <|  nil(), classType = cls_ty), _, _, _)  => begin
                      env = NFSCodeEnv.enterFrame(item_env, inTypeEnv)
                      redecls = ListUtil.map2(inRedeclares, processRedeclare, inElementEnv, inPrefix)
                      (env, repl) = ListUtil.fold(redecls, replaceRedeclaredElementInEnv, (env, emptyReplacements))
                      @match _cons(item_env, env) = env
                    (NFSCodeEnv.CLASS(cls, list(item_env), cls_ty), env, repl)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv failed for:\\n\\t")
                        Debug.traceln("redeclares: " + stringDelimitList(ListUtil.map(inRedeclares, NFSCodeEnv.printRedeclarationStr), "\\n---------\\n") + "\\n\\titem: " + NFSCodeEnv.itemStr(inItem) + "\\n\\tin scope:" + NFSCodeEnv.getEnvName(inElementEnv))
                      fail()
                  end
                end
              end
               #=  Merge the types environment with it's enclosing scopes to get the
               =#
               #=  enclosing scopes of the classes we need to replace.
               =#
          (outItem, outEnv, outReplacements #= what replacements where performed if any =#)
        end

         #= Returns a list of redeclare elements given a redeclaration modifier. =#
        function extractRedeclaresFromModifier(inMod::SCode.Mod) ::List{NFSCodeEnv.Redeclaration} 
              local outRedeclares::List{NFSCodeEnv.Redeclaration}

              outRedeclares = begin
                  local sub_mods::List{SCode.SubMod}
                  local redeclares::List{NFSCodeEnv.Redeclaration}
                @match inMod begin
                  SCode.MOD(subModLst = sub_mods)  => begin
                      redeclares = ListUtil.fold(sub_mods, extractRedeclareFromSubMod, nil)
                    redeclares
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outRedeclares
        end

         #= Checks a submodifier and adds the redeclare element to the list of redeclares
          if the modifier is a redeclaration modifier. =#
        function extractRedeclareFromSubMod(inMod::SCode.SubMod, inRedeclares::List{<:NFSCodeEnv.Redeclaration}) ::List{NFSCodeEnv.Redeclaration} 
              local outRedeclares::List{NFSCodeEnv.Redeclaration}

              outRedeclares = begin
                  local el::SCode.Element
                  local redecl::NFSCodeEnv.Redeclaration
                @match (inMod, inRedeclares) begin
                  (SCode.NAMEMOD(mod = SCode.REDECL(element = el)), _)  => begin
                      redecl = NFSCodeEnv.RAW_MODIFIER(el)
                      NFSCodeCheck.checkDuplicateRedeclarations(redecl, inRedeclares)
                    _cons(redecl, inRedeclares)
                  end
                  
                  _  => begin
                      inRedeclares
                  end
                end
              end
               #=  Skip modifiers that are not redeclarations.
               =#
          outRedeclares
        end

         #= Replaces a redeclaration in the environment. =#
        function replaceRedeclaredElementInEnv(inRedeclare::NFSCodeEnv.Redeclaration, inEnv::Tuple{<:Env, Replacements}) ::Tuple{Env, Replacements} 
              local outEnv::Tuple{Env, Replacements}

              outEnv = begin
                  local name::SCode.Ident
                  local scope_name::SCode.Ident
                  local item::Item
                  local info::SourceInfo
                  local bcl::List{Absyn.Path}
                  local envRpl::Tuple{Env, Replacements}
                   #=  Try to redeclare this element in the current scope.
                   =#
                @matchcontinue (inRedeclare, inEnv) begin
                  (NFSCodeEnv.PROCESSED_MODIFIER(modifier = item), _)  => begin
                      name = NFSCodeEnv.getItemName(item)
                      envRpl = pushRedeclareIntoExtendsNoFail(name, item, inEnv)
                    replaceElementInScope(name, item, envRpl)
                  end
                  
                  (NFSCodeEnv.PROCESSED_MODIFIER(modifier = item), _)  => begin
                      name = NFSCodeEnv.getItemName(item)
                      bcl = NFSCodeLookup.lookupBaseClasses(name, Util.tuple21(inEnv))
                    pushRedeclareIntoExtends(name, item, bcl, inEnv)
                  end
                  
                  (NFSCodeEnv.PROCESSED_MODIFIER(modifier = item), _)  => begin
                      scope_name = NFSCodeEnv.getScopeName(Util.tuple21(inEnv))
                      name = NFSCodeEnv.getItemName(item)
                      info = NFSCodeEnv.getItemInfo(item)
                      Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(name, scope_name), info)
                    fail()
                  end
                end
              end
               #=  do not asume the story ends here
               =#
               #=  you have to push into extends again
               =#
               #=  even if you find it in the local scope!
               =#
               #=  If the previous case failed, see if we can find the redeclared element in
               =#
               #=  any of the base classes. If so, push the redeclare into those base
               =#
               #=  classes instead, i.e. add them to the list of redeclares in the
               =#
               #=  appropriate extends in the extends table.
               =#
               #=  The redeclared element could not be found, show an error.
               =#
          outEnv
        end

         #= Pushes a redeclare into the given extends in the environment if it can.
         if not just returns the same tuple<env, repl> =#
        function pushRedeclareIntoExtendsNoFail(inName::SCode.Ident, inRedeclare::Item, inEnv::Tuple{<:Env, Replacements}) ::Tuple{Env, Replacements} 
              local outEnv::Tuple{Env, Replacements}

              outEnv = begin
                  local bcl::List{Absyn.Path}
                  local envRpl::Tuple{Env, Replacements}
                @matchcontinue (inName, inRedeclare, inEnv) begin
                  (_, _, _)  => begin
                      bcl = NFSCodeLookup.lookupBaseClasses(inName, Util.tuple21(inEnv))
                      envRpl = pushRedeclareIntoExtends(inName, inRedeclare, bcl, inEnv)
                    envRpl
                  end
                  
                  _  => begin
                      inEnv
                  end
                end
              end
          outEnv
        end

         #= Pushes a redeclare into the given extends in the environment. =#
        function pushRedeclareIntoExtends(inName::SCode.Ident, inRedeclare::Item, inBaseClasses::List{<:Absyn.Path}, inEnv::Tuple{<:Env, Replacements}) ::Tuple{Env, Replacements} 
              local outEnv::Tuple{Env, Replacements}

              local exts::List{NFSCodeEnv.Extends}
              local re::List{SCode.Element}
              local cei::Option{SCode.Element}
              local etNew::NFSCodeEnv.ExtendsTable
              local etOld::NFSCodeEnv.ExtendsTable
              local name::String
              local env::Env
              local repl::Replacements

              (env, repl) = inEnv
              @match _cons(NFSCodeEnv.FRAME(extendsTable = (@match NFSCodeEnv.EXTENDS_TABLE(exts, re, cei) = etOld)), _) = env
              exts = pushRedeclareIntoExtends2(inName, inRedeclare, inBaseClasses, exts)
              etNew = NFSCodeEnv.EXTENDS_TABLE(exts, re, cei)
              env = NFSCodeEnv.setEnvExtendsTable(etNew, env)
              repl = _cons(PUSHED(inName, inRedeclare, inBaseClasses, etOld, etNew, env), repl)
              outEnv = (env, repl)
               #=  tracePushRedeclareIntoExtends(inName, inRedeclare, inBaseClasses, env, etOld, etNew);
               =#
          outEnv
        end

         #= This function takes a redeclare item and a list of base class paths that the
           redeclare item should be added to. It goes through the given list of
           extends and pushes the redeclare into each one that's in the list of the
           base class paths. It assumes that the list of base class paths and extends
           are sorted in the same order. =#
        function pushRedeclareIntoExtends2(inName::String, inRedeclare::Item, inBaseClasses::List{<:Absyn.Path}, inExtends::List{<:NFSCodeEnv.Extends}) ::List{NFSCodeEnv.Extends} 
              local outExtends::List{NFSCodeEnv.Extends}

              outExtends = begin
                  local bc1::Absyn.Path
                  local bc2::Absyn.Path
                  local rest_bc::List{Absyn.Path}
                  local ext::NFSCodeEnv.Extends
                  local rest_exts::List{NFSCodeEnv.Extends}
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local index::ModelicaInteger
                  local info::SourceInfo
                  local bc_strl::List{String}
                  local bcl_str::String
                  local err_msg::String
                   #=  See if the first base class path matches the first extends. Push the
                   =#
                   #=  redeclare into that extends if so.
                   =#
                @match (inName, inRedeclare, inBaseClasses, inExtends) begin
                  (_, _, bc1 <| rest_bc, NFSCodeEnv.EXTENDS(bc2, redecls, index, info) <| rest_exts) where (AbsynUtil.pathEqual(bc1, bc2))  => begin
                      redecls = pushRedeclareIntoExtends3(inRedeclare, inName, redecls, nil)
                      rest_exts = pushRedeclareIntoExtends2(inName, inRedeclare, rest_bc, rest_exts)
                    _cons(NFSCodeEnv.EXTENDS(bc2, redecls, index, info), rest_exts)
                  end
                  
                  (_, _, rest_bc, ext <| rest_exts)  => begin
                      rest_exts = pushRedeclareIntoExtends2(inName, inRedeclare, rest_bc, rest_exts)
                    _cons(ext, rest_exts)
                  end
                  
                  (_, _,  nil(), _)  => begin
                    inExtends
                  end
                  
                  (_, _, _,  nil())  => begin
                      bc_strl = list(AbsynUtil.pathString(p) for p in inBaseClasses)
                      bcl_str = stringDelimitList(bc_strl, ", ")
                      err_msg = "NFSCodeFlattenRedeclare.pushRedeclareIntoExtends2 couldn't find the base classes {" + bcl_str + "} for " + inName
                      Error.addMessage(Error.INTERNAL_ERROR, list(err_msg))
                    fail()
                  end
                end
              end
               #=  The extends didn't match, continue with the rest of them.
               =#
               #=  No more base class paths to match means we're done.
               =#
               #=  No more extends means that we couldn't find all the base classes. This
               =#
               #=  shouldn't happen.
               =#
          outExtends
        end

         #= Given the item and name of a redeclare, try to find the redeclare in the
           given list of redeclares. If found, replace the redeclare in the list.
           Otherwise, add a new redeclare to the list. =#
        function pushRedeclareIntoExtends3(inRedeclare::Item, inName::String, inRedeclares::List{<:NFSCodeEnv.Redeclaration}, inOutRedeclares::List{<:NFSCodeEnv.Redeclaration}) ::List{NFSCodeEnv.Redeclaration} 
              local outRedeclares::List{NFSCodeEnv.Redeclaration}

              outRedeclares = begin
                  local item::Item
                  local redecl::NFSCodeEnv.Redeclaration
                  local rest_redecls::List{NFSCodeEnv.Redeclaration}
                  local name::String
                @match (inRedeclare, inName, inRedeclares) begin
                  (_, _, NFSCodeEnv.PROCESSED_MODIFIER(modifier = item) <| rest_redecls) where (stringEqual(NFSCodeEnv.getItemName(item), inName))  => begin
                    ListUtil.append_reverse(inOutRedeclares, _cons(NFSCodeEnv.PROCESSED_MODIFIER(inRedeclare), rest_redecls))
                  end
                  
                  (_, _, redecl <| rest_redecls)  => begin
                    pushRedeclareIntoExtends3(inRedeclare, inName, rest_redecls, _cons(redecl, inOutRedeclares))
                  end
                  
                  (_, _,  nil())  => begin
                    listReverse(_cons(NFSCodeEnv.PROCESSED_MODIFIER(inRedeclare), inOutRedeclares))
                  end
                end
              end
          outRedeclares
        end

         #= Replaces an element in the current scope. =#
        function replaceElementInScope(inElementName::SCode.Ident, inElement::Item, inEnv::Tuple{<:Env, Replacements}) ::Tuple{Env, Replacements} 
              local outEnv::Tuple{Env, Replacements}

              outEnv = begin
                  local tree::EnvTree.Tree
                  local old_item::Item
                  local new_item::Item
                  local env::Env
                  local repl::Replacements
                @match (inElementName, inElement, inEnv) begin
                  (_, _, (env && NFSCodeEnv.FRAME(clsAndVars = tree) <| _, repl))  => begin
                      old_item = EnvTree.get(tree, inElementName)
                      new_item = propagateItemPrefixes(old_item, inElement)
                      new_item = NFSCodeEnv.linkItemUsage(old_item, new_item)
                      tree = EnvTree.add(tree, inElementName, new_item, EnvTree.addConflictReplace)
                      env = NFSCodeEnv.setEnvClsAndVars(tree, env)
                      repl = _cons(REPLACED(inElementName, old_item, new_item, env), repl)
                    (env, repl)
                  end
                end
              end
               #= /*********************************************************************/ =#
               #=  TODO: Check if this is actually needed
               =#
               #= /*********************************************************************/ =#
               #=  traceReplaceElementInScope(inElementName, old_item, new_item, env);
               =#
          outEnv
        end

        function propagateItemPrefixes(inOriginalItem::Item, inNewItem::Item) ::Item 
              local outNewItem::Item

              outNewItem = begin
                  local el1::SCode.Element
                  local el2::SCode.Element
                  local iu1::Option{MutableType #= {Bool} =#}
                  local iu2::Option{MutableType #= {Bool} =#}
                  local env1::Env
                  local env2::Env
                  local ty1::NFSCodeEnv.ClassType
                  local ty2::NFSCodeEnv.ClassType
                  local item::Item
                @match (inOriginalItem, inNewItem) begin
                  (NFSCodeEnv.VAR(var = el1), NFSCodeEnv.VAR(var = el2, isUsed = iu2))  => begin
                      el2 = propagateAttributesVar(el1, el2)
                    NFSCodeEnv.VAR(el2, iu2)
                  end
                  
                  (NFSCodeEnv.CLASS(cls = el1), NFSCodeEnv.CLASS(cls = el2, env = env2, classType = ty2))  => begin
                      el2 = propagateAttributesClass(el1, el2)
                    NFSCodeEnv.CLASS(el2, env2, ty2)
                  end
                  
                  (NFSCodeEnv.ALIAS(__), _)  => begin
                    inNewItem
                  end
                  
                  (_, NFSCodeEnv.ALIAS(__))  => begin
                    inNewItem
                  end
                  
                  (NFSCodeEnv.REDECLARED_ITEM(item = item), _)  => begin
                    propagateItemPrefixes(item, inNewItem)
                  end
                  
                  (_, NFSCodeEnv.REDECLARED_ITEM(item = item, declaredEnv = env1))  => begin
                      item = propagateItemPrefixes(inOriginalItem, item)
                    NFSCodeEnv.REDECLARED_ITEM(item, env1)
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("NFSCodeFlattenRedeclare.propagateAttributes failed on unknown item."))
                      fail()
                  end
                end
              end
               #= /*************************************************************************/ =#
               #=  TODO: Attributes should probably be propagated for alias items too. If
               =#
               #=  the original is an alias, look up the referenced item and use those
               =#
               #=  attributes. If the new item is an alias, look up the referenced item and
               =#
               #=  apply the attributes to it.
               =#
               #= /*************************************************************************/ =#
          outNewItem
        end

        function propagateAttributesVar(inOriginalVar::SCode.Element, inNewVar::SCode.Element) ::SCode.Element 
              local outNewVar::SCode.Element

              local name::SCode.Ident
              local pref1::SCode.Prefixes
              local pref2::SCode.Prefixes
              local attr1::SCode.Attributes
              local attr2::SCode.Attributes
              local ty::Absyn.TypeSpec
              local mod::SCode.Mod
              local cmt::SCode.Comment
              local cond::Option{Absyn.Exp}
              local info::SourceInfo

              @match SCode.COMPONENT(prefixes = pref1, attributes = attr1) = inOriginalVar
              @match SCode.COMPONENT(name, pref2, attr2, ty, mod, cmt, cond, info) = inNewVar
              pref2 = propagatePrefixes(pref1, pref2)
              attr2 = propagateAttributes(attr1, attr2)
              outNewVar = SCode.COMPONENT(name, pref2, attr2, ty, mod, cmt, cond, info)
          outNewVar
        end

        function propagateAttributesClass(inOriginalClass::SCode.Element, inNewClass::SCode.Element) ::SCode.Element 
              local outNewClass::SCode.Element

              local name::SCode.Ident
              local pref1::SCode.Prefixes
              local pref2::SCode.Prefixes
              local ep::SCode.Encapsulated
              local pp::SCode.Partial
              local res::SCode.Restriction
              local cdef::SCode.ClassDef
              local info::SourceInfo
              local cmt::SCode.Comment

              @match SCode.CLASS(prefixes = pref1) = inOriginalClass
              @match SCode.CLASS(name, pref2, ep, pp, res, cdef, cmt, info) = inNewClass
              pref2 = propagatePrefixes(pref1, pref2)
              outNewClass = SCode.CLASS(name, pref2, ep, pp, res, cdef, cmt, info)
          outNewClass
        end

        function propagatePrefixes(inOriginalPrefixes::SCode.Prefixes, inNewPrefixes::SCode.Prefixes) ::SCode.Prefixes 
              local outNewPrefixes::SCode.Prefixes

              local vis1::SCode.Visibility
              local vis2::SCode.Visibility
              local io1::Absyn.InnerOuter
              local io2::Absyn.InnerOuter
              local rdp::SCode.Redeclare
              local fp::SCode.Final
              local rpp::SCode.Replaceable

              @match SCode.PREFIXES(visibility = vis1, innerOuter = io1) = inOriginalPrefixes
              @match SCode.PREFIXES(vis2, rdp, fp, io2, rpp) = inNewPrefixes
              io2 = propagatePrefixInnerOuter(io1, io2)
              outNewPrefixes = SCode.PREFIXES(vis2, rdp, fp, io2, rpp)
          outNewPrefixes
        end

        function propagatePrefixInnerOuter(inOriginalIO::Absyn.InnerOuter, inIO::Absyn.InnerOuter) ::Absyn.InnerOuter 
              local outIO::Absyn.InnerOuter

              outIO = begin
                @match (inOriginalIO, inIO) begin
                  (_, Absyn.NOT_INNER_OUTER(__))  => begin
                    inOriginalIO
                  end
                  
                  _  => begin
                      inIO
                  end
                end
              end
          outIO
        end

        function propagateAttributes(inOriginalAttributes::SCode.Attributes, inNewAttributes::SCode.Attributes) ::SCode.Attributes 
              local outNewAttributes::SCode.Attributes

              local dims1::Absyn.ArrayDim
              local dims2::Absyn.ArrayDim
              local ct1::SCode.ConnectorType
              local ct2::SCode.ConnectorType
              local prl1::SCode.Parallelism
              local prl2::SCode.Parallelism
              local var1::SCode.Variability
              local var2::SCode.Variability
              local dir1::Absyn.Direction
              local dir2::Absyn.Direction
              local isf1::Absyn.IsField
              local isf2::Absyn.IsField

              @match SCode.ATTR(dims1, ct1, prl1, var1, dir1, isf1) = inOriginalAttributes
              @match SCode.ATTR(dims2, ct2, prl2, var2, dir2, isf2) = inNewAttributes
              dims2 = propagateArrayDimensions(dims1, dims2)
              ct2 = propagateConnectorType(ct1, ct2)
              prl2 = propagateParallelism(prl1, prl2)
              var2 = propagateVariability(var1, var2)
              dir2 = propagateDirection(dir1, dir2)
              isf2 = propagateIsField(isf1, isf2)
              outNewAttributes = SCode.ATTR(dims2, ct2, prl2, var2, dir2, isf2)
          outNewAttributes
        end

        function propagateArrayDimensions(inOriginalDims::Absyn.ArrayDim, inNewDims::Absyn.ArrayDim) ::Absyn.ArrayDim 
              local outNewDims::Absyn.ArrayDim

              outNewDims = begin
                @match (inOriginalDims, inNewDims) begin
                  (_,  nil())  => begin
                    inOriginalDims
                  end
                  
                  _  => begin
                      inNewDims
                  end
                end
              end
          outNewDims
        end

        function propagateConnectorType(inOriginalConnectorType::SCode.ConnectorType, inNewConnectorType::SCode.ConnectorType) ::SCode.ConnectorType 
              local outNewConnectorType::SCode.ConnectorType

              outNewConnectorType = begin
                @match (inOriginalConnectorType, inNewConnectorType) begin
                  (_, SCode.POTENTIAL(__))  => begin
                    inOriginalConnectorType
                  end
                  
                  _  => begin
                      inNewConnectorType
                  end
                end
              end
          outNewConnectorType
        end

        function propagateParallelism(inOriginalParallelism::SCode.Parallelism, inNewParallelism::SCode.Parallelism) ::SCode.Parallelism 
              local outNewParallelism::SCode.Parallelism

              outNewParallelism = begin
                @match (inOriginalParallelism, inNewParallelism) begin
                  (_, SCode.NON_PARALLEL(__))  => begin
                    inOriginalParallelism
                  end
                  
                  _  => begin
                      inNewParallelism
                  end
                end
              end
          outNewParallelism
        end

        function propagateVariability(inOriginalVariability::SCode.Variability, inNewVariability::SCode.Variability) ::SCode.Variability 
              local outNewVariability::SCode.Variability

              outNewVariability = begin
                @match (inOriginalVariability, inNewVariability) begin
                  (_, SCode.VAR(__))  => begin
                    inOriginalVariability
                  end
                  
                  _  => begin
                      inNewVariability
                  end
                end
              end
          outNewVariability
        end

        function propagateDirection(inOriginalDirection::Absyn.Direction, inNewDirection::Absyn.Direction) ::Absyn.Direction 
              local outNewDirection::Absyn.Direction

              outNewDirection = begin
                @match (inOriginalDirection, inNewDirection) begin
                  (_, Absyn.BIDIR(__))  => begin
                    inOriginalDirection
                  end
                  
                  _  => begin
                      inNewDirection
                  end
                end
              end
          outNewDirection
        end

        function propagateIsField(inOriginalIsField::Absyn.IsField, inNewIsField::Absyn.IsField) ::Absyn.IsField 
              local outNewIsField::Absyn.IsField

              outNewIsField = begin
                @match (inOriginalIsField, inNewIsField) begin
                  (_, Absyn.NONFIELD(__))  => begin
                    inOriginalIsField
                  end
                  
                  _  => begin
                      inNewIsField
                  end
                end
              end
          outNewIsField
        end

         #= @author: adrpo
         good for debugging redeclares.
         uncomment it in replaceElementInScope to activate it =#
        function traceReplaceElementInScope(inElementName::SCode.Ident, inOldItem::Item, inNewItem::Item, inEnv::Env)  
              _ = begin
                @matchcontinue (inElementName, inOldItem, inNewItem, inEnv) begin
                  (_, _, _, _)  => begin
                      print("replacing element: " + inElementName + " env: " + NFSCodeEnv.getEnvName(inEnv) + "\\n\\t")
                      print("Old Element:" + NFSCodeEnv.itemStr(inOldItem) + " env: " + NFSCodeEnv.getEnvName(NFSCodeEnv.getItemEnvNoFail(inOldItem)) + "\\n\\t")
                      print("New Element:" + NFSCodeEnv.itemStr(inNewItem) + " env: " + NFSCodeEnv.getEnvName(NFSCodeEnv.getItemEnvNoFail(inNewItem)) + "\\n===============\\n")
                    ()
                  end
                  
                  _  => begin
                        print("traceReplaceElementInScope failed on element: " + inElementName + "\\n")
                      ()
                  end
                end
              end
        end

         #= @author: adrpo
         good for debugging redeclares.
         uncomment it in pushRedeclareIntoExtends to activate it =#
        function tracePushRedeclareIntoExtends(inName::SCode.Ident, inRedeclare::NFSCodeEnv.Item, inBaseClasses::List{<:Absyn.Path}, inEnv::Env, inEtNew::NFSCodeEnv.ExtendsTable, inEtOld::NFSCodeEnv.ExtendsTable)  
              _ = begin
                @matchcontinue (inName, inRedeclare, inBaseClasses, inEnv, inEtNew, inEtOld) begin
                  (_, _, _, _, _, _)  => begin
                      print("pushing: " + inName + " redeclare: " + NFSCodeEnv.itemStr(inRedeclare) + "\\n\\t")
                      print("into baseclases: " + stringDelimitList(list(AbsynUtil.pathString(p) for p in inBaseClasses), ", ") + "\\n\\t")
                      print("called from env: " + NFSCodeEnv.getEnvName(inEnv) + "\\n")
                      print("-----------------\\n")
                    ()
                  end
                  
                  _  => begin
                        print("tracePushRedeclareIntoExtends failed on element: " + inName + "\\n")
                      ()
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
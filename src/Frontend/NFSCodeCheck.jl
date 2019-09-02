  module NFSCodeCheck 


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

        import NFInstTypes

        import SCode

        import NFSCodeEnv

        import Debug

        import Dump

        import Error

        import Flags

        import NFInstDump

        import SCodeDump
        import SCodeUtil
        import NFSCodeEnv.EnvTree

        function checkRecursiveShortDefinition(inTypeSpec::Absyn.TypeSpec, inTypeName::String, inTypeEnv::NFSCodeEnv.Env, inInfo::SourceInfo)  
              _ = begin
                  local ts_path::Absyn.Path
                  local ty_path::Absyn.Path
                  local ty::String
                @matchcontinue (inTypeSpec, inTypeName, inTypeEnv, inInfo) begin
                  (_, _,  nil(), _)  => begin
                    ()
                  end
                  
                  (_, _, _ <| _, _)  => begin
                      ts_path = AbsynUtil.typeSpecPath(inTypeSpec)
                      ty_path = NFSCodeEnv.getEnvPath(inTypeEnv)
                      @match false = isSelfReference(inTypeName, ty_path, ts_path)
                    ()
                  end
                  
                  _  => begin
                        ty = Dump.unparseTypeSpec(inTypeSpec)
                        Error.addSourceMessage(Error.RECURSIVE_SHORT_CLASS_DEFINITION, list(inTypeName, ty), inInfo)
                      fail()
                  end
                end
              end
        end

        function isSelfReference(inTypeName::String, inTypePath::Absyn.Path, inReferencedName::Absyn.Path) ::Bool 
              local selfRef::Bool

              selfRef = begin
                  local p1::Absyn.Path
                  local p2::Absyn.Path
                @match (inTypeName, inTypePath, inReferencedName) begin
                  (_, p1, Absyn.FULLYQUALIFIED(p2))  => begin
                    AbsynUtil.pathEqual(AbsynUtil.joinPaths(p1, Absyn.IDENT(inTypeName)), p2)
                  end
                  
                  (_, _, p2)  => begin
                    stringEqual(AbsynUtil.pathLastIdent(inTypePath), AbsynUtil.pathFirstIdent(p2))
                  end
                end
              end
          selfRef
        end

        function checkClassExtendsReplaceability(inBaseClass::NFSCodeEnv.Item, inOriginInfo::SourceInfo)  
              _ = begin
                  local info::SourceInfo
                  local name::String
                @match (inBaseClass, inOriginInfo) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(__)))), _)  => begin
                    ()
                  end
                end
              end
               #= case (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name, prefixes = SCode.PREFIXES(
               =#
               #=     replaceablePrefix = SCode.NOT_REPLACEABLE()), info = info)), _)
               =#
               #=   equation
               =#
               #=     Error.addSourceMessage(Error.ERROR_FROM_HERE, {}, inOriginInfo);
               =#
               #=     Error.addSourceMessage(Error.NON_REPLACEABLE_CLASS_EXTENDS,
               =#
               #=       {name}, info);
               =#
               #=   then
               =#
               #=     fail();
               =#
        end

        function checkRedeclareModifier(inModifier::NFSCodeEnv.Redeclaration, inBaseClass::Absyn.Path, inEnv::NFSCodeEnv.Env)  
              _ = begin
                  local e::SCode.Element
                @match (inModifier, inBaseClass, inEnv) begin
                  (NFSCodeEnv.RAW_MODIFIER(e && SCode.CLASS(classDef = SCode.DERIVED(__))), _, _)  => begin
                      checkRedeclareModifier2(e, inBaseClass, inEnv)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkRedeclareModifier2(inModifier::SCode.Element, inBaseClass::Absyn.Path, inEnv::NFSCodeEnv.Env)  
              _ = begin
                  local ty::Absyn.TypeSpec
                  local info::SourceInfo
                  local name::String
                  local ty_str::String
                  local ty_path::Absyn.Path
                @matchcontinue (inModifier, inBaseClass, inEnv) begin
                  (SCode.CLASS(name = name, classDef = SCode.DERIVED(typeSpec = ty)), _, _)  => begin
                      ty_path = AbsynUtil.typeSpecPath(ty)
                      @match false = isSelfReference(name, inBaseClass, ty_path)
                    ()
                  end
                  
                  (SCode.CLASS(name = name, classDef = SCode.DERIVED(typeSpec = ty), info = info), _, _)  => begin
                      ty_str = Dump.unparseTypeSpec(ty)
                      Error.addSourceMessage(Error.RECURSIVE_SHORT_CLASS_DEFINITION, list(name, ty_str), info)
                    fail()
                  end
                end
              end
        end

        function checkModifierIfRedeclare(inItem::NFSCodeEnv.Item, inModifier::SCode.Mod, inInfo::SourceInfo)  
              _ = begin
                  local el::SCode.Element
                @match (inItem, inModifier, inInfo) begin
                  (_, SCode.REDECL(element = el), _)  => begin
                      checkRedeclaredElementPrefix(inItem, el, inInfo)
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Checks that an element that is being redeclared is declared as replaceable
          and non-final, otherwise an error is printed. =#
        function checkRedeclaredElementPrefix(inItem::NFSCodeEnv.Item, inReplacement::SCode.Element, inInfo::SourceInfo)  
              _ = begin
                  local repl::SCode.Replaceable
                  local fin::SCode.Final
                  local name::SCode.Ident
                  local info::SourceInfo
                  local var::SCode.Variability
                  local res::SCode.Restriction
                  local vis1::SCode.Visibility
                  local vis2::SCode.Visibility
                  local ty::String
                  local ty1::Absyn.TypeSpec
                  local ty2::Absyn.TypeSpec
                  local ok::Bool
                @match (inItem, inReplacement) begin
                  (NFSCodeEnv.VAR(var = SCode.COMPONENT(name = name, prefixes = SCode.PREFIXES(finalPrefix = fin, replaceablePrefix = repl), attributes = SCode.ATTR(variability = var), typeSpec = ty1, info = info)), SCode.COMPONENT(prefixes = SCode.PREFIXES(__), typeSpec = ty2))  => begin
                      ty = "component"
                      ok = checkCompRedeclarationReplaceable(name, repl, ty1, ty2, inInfo, info)
                      ok = checkRedeclarationFinal(name, ty, fin, inInfo, info) && ok
                      ok = checkRedeclarationVariability(name, ty, var, inInfo, info) && ok
                       #= checkRedeclarationVisibility(name, ty, vis1, vis2, inInfo, info);
                       =#
                      @match true = ok
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name, prefixes = SCode.PREFIXES(finalPrefix = fin, replaceablePrefix = repl), restriction = res, info = info)), SCode.CLASS(prefixes = SCode.PREFIXES(__)))  => begin
                      ty = SCodeDump.restrictionStringPP(res)
                      ok = checkClassRedeclarationReplaceable(name, ty, repl, inInfo, info)
                      ok = checkRedeclarationFinal(name, ty, fin, inInfo, info) && ok
                       #= checkRedeclarationVisibility(name, ty, vis1, vis2, inInfo, info);
                       =#
                      @match true = ok
                    ()
                  end
                  
                  (NFSCodeEnv.VAR(var = SCode.COMPONENT(name = name, info = info)), SCode.CLASS(restriction = res))  => begin
                      ty = SCodeDump.restrictionStringPP(res)
                      ty = "a " + ty
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE_AS, list("component", name, ty), list(inInfo, info))
                    fail()
                  end
                  
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(restriction = res, info = info)), SCode.COMPONENT(name = name))  => begin
                      ty = SCodeDump.restrictionStringPP(res)
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE_AS, list(ty, name, "a component"), list(inInfo, info))
                    fail()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkClassRedeclarationReplaceable(inName::SCode.Ident, inType::String, inReplaceable::SCode.Replaceable, inOriginInfo::SourceInfo, inInfo::SourceInfo) ::Bool 
              local isValid::Bool

              isValid = begin
                @match inReplaceable begin
                  SCode.NOT_REPLACEABLE(__) where (! Flags.getConfigBool(Flags.IGNORE_REPLACEABLE))  => begin
                      Error.addMultiSourceMessage(Error.REDECLARE_NON_REPLACEABLE, list(inType, inName), list(inOriginInfo, inInfo))
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          isValid
        end

        function checkCompRedeclarationReplaceable(inName::SCode.Ident, inReplaceable::SCode.Replaceable, inType1::Absyn.TypeSpec, inType2::Absyn.TypeSpec, inOriginInfo::SourceInfo, inInfo::SourceInfo) ::Bool 
              local isValid::Bool

              isValid = begin
                @match inReplaceable begin
                  SCode.NOT_REPLACEABLE(__) where (AbsynUtil.pathEqual(AbsynUtil.typeSpecPath(inType1), AbsynUtil.typeSpecPath(inType2)))  => begin
                    true
                  end
                  
                  SCode.NOT_REPLACEABLE(__) where (! Flags.getConfigBool(Flags.IGNORE_REPLACEABLE))  => begin
                      Error.addMultiSourceMessage(Error.REDECLARE_NON_REPLACEABLE, list("component", inName), list(inOriginInfo, inInfo))
                    fail()
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          isValid
        end

        function checkRedeclarationFinal(inName::SCode.Ident, inType::String, inFinal::SCode.Final, inOriginInfo::SourceInfo, inInfo::SourceInfo) ::Bool 
              local isValid::Bool

              isValid = begin
                @match inFinal begin
                  SCode.NOT_FINAL(__)  => begin
                    true
                  end
                  
                  SCode.FINAL(__)  => begin
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE, list("final", inType, inName), list(inOriginInfo, inInfo))
                    false
                  end
                end
              end
          isValid
        end

        function checkRedeclarationVariability(inName::SCode.Ident, inType::String, inVariability::SCode.Variability, inOriginInfo::SourceInfo, inInfo::SourceInfo) ::Bool 
              local isValid::Bool

              isValid = begin
                @match inVariability begin
                  SCode.CONST(__)  => begin
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE, list("constant", inType, inName), list(inOriginInfo, inInfo))
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          isValid
        end

        function checkRedeclarationVisibility(inName::SCode.Ident, inType::String, inOriginalVisibility::SCode.Visibility, inNewVisibility::SCode.Visibility, inOriginInfo::SourceInfo, inNewInfo::SourceInfo) ::Bool 
              local isValid::Bool

              isValid = begin
                @match (inOriginalVisibility, inNewVisibility) begin
                  (SCode.PUBLIC(__), SCode.PROTECTED(__))  => begin
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE_AS, list("public element", inName, "protected"), list(inNewInfo, inOriginInfo))
                    false
                  end
                  
                  (SCode.PROTECTED(__), SCode.PUBLIC(__))  => begin
                      Error.addMultiSourceMessage(Error.INVALID_REDECLARE_AS, list("protected element", inName, "public"), list(inNewInfo, inOriginInfo))
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          isValid
        end

         #= Checks if a redeclaration already exists in a list of redeclarations. =#
        function checkDuplicateRedeclarations(inRedeclare::NFSCodeEnv.Redeclaration, inRedeclarations::List{<:NFSCodeEnv.Redeclaration})  
              local el::SCode.Element
              local el_name::String
              local el_info::SourceInfo

              (el_name, el_info) = NFSCodeEnv.getRedeclarationNameInfo(inRedeclare)
              @match false = checkDuplicateRedeclarations2(el_name, el_info, inRedeclarations)
        end

         #= Helper function to checkDuplicateRedeclarations. =#
        function checkDuplicateRedeclarations2(inRedeclareName::String, inRedeclareInfo::SourceInfo, inRedeclarations::List{<:NFSCodeEnv.Redeclaration}) ::Bool 
              local outIsDuplicate::Bool

              outIsDuplicate = begin
                  local redecl::NFSCodeEnv.Redeclaration
                  local rest_redecls::List{NFSCodeEnv.Redeclaration}
                  local el_name::String
                  local el_info::SourceInfo
                @matchcontinue (inRedeclareName, inRedeclareInfo, inRedeclarations) begin
                  (_, _,  nil())  => begin
                    false
                  end
                  
                  (_, _, redecl <| _)  => begin
                      (el_name, el_info) = NFSCodeEnv.getRedeclarationNameInfo(redecl)
                      @match true = stringEqual(inRedeclareName, el_name)
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, el_info)
                      Error.addSourceMessage(Error.DUPLICATE_REDECLARATION, list(inRedeclareName), inRedeclareInfo)
                    true
                  end
                  
                  (_, _, _ <| rest_redecls)  => begin
                    checkDuplicateRedeclarations2(inRedeclareName, inRedeclareInfo, rest_redecls)
                  end
                end
              end
          outIsDuplicate
        end

         #= Checks if a component is declared with a type that is one of the enclosing
           classes, e.g:
             class A
               class B
                 A a;
               end B;
             end A;
           =#
        function checkRecursiveComponentDeclaration(inComponentName::String, inComponentInfo::SourceInfo, inTypeEnv::NFSCodeEnv.Env, inTypeItem::NFSCodeEnv.Item, inComponentEnv::NFSCodeEnv.Env)  
              _ = begin
                  local cls_name::String
                  local ty_name::String
                  local tree::EnvTree.Tree
                  local el::SCode.Element
                   #=  No environment means one of the basic types.
                   =#
                @matchcontinue (inComponentName, inComponentInfo, inTypeEnv, inTypeItem, inComponentEnv) begin
                  (_, _,  nil(), _, _)  => begin
                    ()
                  end
                  
                  (_, _, _, _, _)  => begin
                      @match false = NFSCodeEnv.envPrefixOf(inTypeEnv, inComponentEnv)
                    ()
                  end
                  
                  (_, _, _, _, NFSCodeEnv.FRAME(name = SOME(cls_name)) <| NFSCodeEnv.FRAME(clsAndVars = tree) <| _)  => begin
                      @match NFSCodeEnv.CLASS(cls = el) = EnvTree.get(tree, cls_name)
                      @match true = SCodeUtil.isFunction(el)
                    ()
                  end
                  
                  _  => begin
                        ty_name = NFSCodeEnv.getItemName(inTypeItem)
                        Error.addSourceMessage(Error.RECURSIVE_DEFINITION, list(inComponentName, ty_name), inComponentInfo)
                      fail()
                  end
                end
              end
               #=  Check that the environment of the components type is not an enclosing
               =#
               #=  scope of the component itself.
               =#
               #=  Make an exception for components in functions.
               =#
        end

         #= Checks that a simple identifier is not the same as a type name. =#
        function checkIdentNotEqTypeName(inIdent::String, inTypeName::Absyn.TypeSpec, inInfo::SourceInfo) ::Bool 
              local outIsNotEq::Bool

              outIsNotEq = begin
                  local id::String
                  local ty::String
                @matchcontinue (inIdent, inTypeName, inInfo) begin
                  (id, Absyn.TPATH(path = Absyn.IDENT(ty)), _)  => begin
                      @match true = stringEq(id, ty)
                      Error.addSourceMessage(Error.LOOKUP_TYPE_FOUND_COMP, list(id), inInfo)
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          outIsNotEq
        end

        function checkComponentsEqual(inComponent1::NFInstTypes.Component, inComponent2::NFInstTypes.Component)  
              _ = begin
                @match (inComponent1, inComponent2) begin
                  (_, _)  => begin
                      print("Found duplicate component\\n")
                    ()
                  end
                end
              end
        end

        function checkInstanceRestriction(inItem::NFSCodeEnv.Item, inPrefix::NFInstTypes.Prefix, inInfo::SourceInfo)  
              _ = begin
                  local res::SCode.Restriction
                  local pre_str::String
                  local res_str::String
                @matchcontinue (inItem, inPrefix, inInfo) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(restriction = res)), _, _)  => begin
                      @match true = SCodeUtil.isInstantiableClassRestriction(res)
                    ()
                  end
                  
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(restriction = res)), _, _)  => begin
                      res_str = SCodeDump.restrictionStringPP(res)
                      pre_str = NFInstDump.prefixStr(inPrefix)
                      Error.addSourceMessage(Error.INVALID_CLASS_RESTRICTION, list(res_str, pre_str), inInfo)
                    fail()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeCheck.checkInstanceRestriction failed on unknown item.")
                      fail()
                  end
                end
              end
        end

         #= Checks if the given item is partial, and prints out an error message in that
           case. =#
        function checkPartialInstance(inItem::NFSCodeEnv.Item, inInfo::SourceInfo)  
              _ = begin
                  local name::String
                @match (inItem, inInfo) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name, partialPrefix = SCode.PARTIAL(__))), _)  => begin
                      Error.addSourceMessage(Error.INST_PARTIAL_CLASS, list(name), inInfo)
                    fail()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
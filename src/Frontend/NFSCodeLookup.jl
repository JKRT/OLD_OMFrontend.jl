  module NFSCodeLookup 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl RedeclareReplaceStrategy 
    @UniontypeDecl LookupStrategy 

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

        import Error

        import NFInstPrefix

        import SCode

        import NFSCodeEnv

        import Config

        import Debug

        import NFEnvExtends

        import Flags

        import ListUtil

        import NFSCodeFlattenImports

        import NFSCodeFlattenRedeclare
        import NFSCodeEnv.EnvTree

        Env = NFSCodeEnv.Env 

        Item = NFSCodeEnv.Item 

        Extends = NFSCodeEnv.Extends 

        Frame = NFSCodeEnv.Frame 

        FrameType = NFSCodeEnv.FrameType 

        Import = Absyn.Import 

         @Uniontype RedeclareReplaceStrategy begin
              @Record INSERT_REDECLARES begin

              end

              @Record IGNORE_REDECLARES begin

              end
         end

         @Uniontype LookupStrategy begin
              @Record NO_BUILTIN_TYPES begin

              end

              @Record LOOKUP_ANY begin

              end
         end

         #=  Default parts of the declarations for builtin elements and types.
         =#

         const BUILTIN_PREFIXES = SCode.PREFIXES(SCode.PUBLIC(), SCode.NOT_REDECLARE(), SCode.NOT_FINAL(), Absyn.NOT_INNER_OUTER(), SCode.NOT_REPLACEABLE())::SCode.Prefixes

         const BUILTIN_ATTRIBUTES = SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD())::SCode.Attributes

         const BUILTIN_CONST_ATTRIBUTES = SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.CONST(), Absyn.BIDIR(), Absyn.NONFIELD())::SCode.Attributes

         const BUILTIN_EMPTY_CLASS = SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE())::SCode.ClassDef
         #=  Metatypes used to define the builtin types.
         =#

         const BUILTIN_REALTYPE = SCode.CLASS("RealType", BUILTIN_PREFIXES, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_REAL(), BUILTIN_EMPTY_CLASS, SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_INTEGERTYPE = SCode.CLASS("IntegerType", BUILTIN_PREFIXES, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_INTEGER(), BUILTIN_EMPTY_CLASS, SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_BOOLEANTYPE = SCode.CLASS("BooleanType", BUILTIN_PREFIXES, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_BOOLEAN(), BUILTIN_EMPTY_CLASS, SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STRINGTYPE = SCode.CLASS("StringType", BUILTIN_PREFIXES, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_STRING(), BUILTIN_EMPTY_CLASS, SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ENUMTYPE = SCode.CLASS("EnumType", BUILTIN_PREFIXES, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_PREDEFINED_ENUMERATION(), BUILTIN_EMPTY_CLASS, SCode.noComment, AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_REALTYPE_ITEM = NFSCodeEnv.VAR(BUILTIN_REALTYPE, NONE())::Item

         const BUILTIN_INTEGERTYPE_ITEM = NFSCodeEnv.VAR(BUILTIN_INTEGERTYPE, NONE())::Item

         const BUILTIN_BOOLEANTYPE_ITEM = NFSCodeEnv.VAR(BUILTIN_BOOLEANTYPE, NONE())::Item

         const BUILTIN_STRINGTYPE_ITEM = NFSCodeEnv.VAR(BUILTIN_STRINGTYPE, NONE())::Item

         const BUILTIN_ENUMTYPE_ITEM = NFSCodeEnv.VAR(BUILTIN_ENUMTYPE, NONE())::Item

         const BUILTIN_REALTYPE_SPEC = Absyn.TPATH(Absyn.IDENT("RealType"), NONE())::Absyn.TypeSpec

         const BUILTIN_INTEGERTYPE_SPEC = Absyn.TPATH(Absyn.IDENT("IntegerType"), NONE())::Absyn.TypeSpec

         const BUILTIN_BOOLEANTYPE_SPEC = Absyn.TPATH(Absyn.IDENT("BooleanType"), NONE())::Absyn.TypeSpec

         const BUILTIN_STRINGTYPE_SPEC = Absyn.TPATH(Absyn.IDENT("StringType"), NONE())::Absyn.TypeSpec

         const BUILTIN_ENUMTYPE_SPEC = Absyn.TPATH(Absyn.IDENT("EnumType"), NONE())::Absyn.TypeSpec

         const BUILTIN_STATESELECT_SPEC = Absyn.TPATH(Absyn.IDENT("StateSelect"), NONE())::Absyn.TypeSpec
         #=  Parts of the builtin types.
         =#
         #=  Generic elements:
         =#

         const BUILTIN_ATTR_QUANTITY = SCode.COMPONENT("quantity", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_STRINGTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ATTR_UNIT = SCode.COMPONENT("unit", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_STRINGTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ATTR_DISPLAYUNIT = SCode.COMPONENT("displayUnit", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_STRINGTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ATTR_FIXED = SCode.COMPONENT("fixed", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_BOOLEANTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ATTR_STATESELECT = SCode.COMPONENT("stateSelect", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_STATESELECT_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  Real-specific elements:
         =#

         const BUILTIN_REAL_MIN = SCode.COMPONENT("min", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_REALTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_REAL_MAX = SCode.COMPONENT("max", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_REALTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_REAL_START = SCode.COMPONENT("start", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_REALTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_REAL_NOMINAL = SCode.COMPONENT("nominal", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_REALTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  Integer-specific elements:
         =#

         const BUILTIN_INTEGER_MIN = SCode.COMPONENT("min", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_INTEGERTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_INTEGER_MAX = SCode.COMPONENT("max", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_INTEGERTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_INTEGER_START = SCode.COMPONENT("start", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_INTEGERTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  Boolean-specific elements:
         =#

         const BUILTIN_BOOLEAN_START = SCode.COMPONENT("start", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_BOOLEANTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  String-specific elements:
         =#

         const BUILTIN_STRING_START = SCode.COMPONENT("start", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_STRINGTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  StateSelect-specific elements:
         =#

         const BUILTIN_ENUM_MIN = SCode.COMPONENT("min", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ENUM_MAX = SCode.COMPONENT("max", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_ENUM_START = SCode.COMPONENT("start", BUILTIN_PREFIXES, BUILTIN_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STATESELECT_NEVER = SCode.COMPONENT("never", BUILTIN_PREFIXES, BUILTIN_CONST_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STATESELECT_AVOID = SCode.COMPONENT("avoid", BUILTIN_PREFIXES, BUILTIN_CONST_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STATESELECT_DEFAULT = SCode.COMPONENT("default", BUILTIN_PREFIXES, BUILTIN_CONST_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STATESELECT_PREFER = SCode.COMPONENT("prefer", BUILTIN_PREFIXES, BUILTIN_CONST_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element

         const BUILTIN_STATESELECT_ALWAYS = SCode.COMPONENT("always", BUILTIN_PREFIXES, BUILTIN_CONST_ATTRIBUTES, BUILTIN_ENUMTYPE_SPEC, SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo)::SCode.Element
         #=  Environments for the builtin types:
         =#

         const BUILTIN_REAL_ENV = list(NFSCodeEnv.FRAME(SOME("Real"), NFSCodeEnv.NORMAL_SCOPE(), NFSCodeEnv.EnvTree.Tree.NODE("nominal", NFSCodeEnv.VAR(BUILTIN_REAL_NOMINAL, NONE()), 3, NFSCodeEnv.EnvTree.Tree.NODE("max", NFSCodeEnv.VAR(BUILTIN_REAL_MAX, NONE()), 2, NFSCodeEnv.EnvTree.Tree.NODE("fixed", NFSCodeEnv.VAR(BUILTIN_ATTR_FIXED, NONE()), 1, NFSCodeEnv.EnvTree.Tree.LEAF("displayUnit", NFSCodeEnv.VAR(BUILTIN_ATTR_DISPLAYUNIT, NONE())), NFSCodeEnv.EnvTree.Tree.EMPTY()), NFSCodeEnv.EnvTree.Tree.LEAF("min", NFSCodeEnv.VAR(BUILTIN_REAL_MIN, NONE()))), NFSCodeEnv.EnvTree.Tree.NODE("start", NFSCodeEnv.VAR(BUILTIN_REAL_START, NONE()), 2, NFSCodeEnv.EnvTree.Tree.LEAF("quantity", NFSCodeEnv.VAR(BUILTIN_ATTR_QUANTITY, NONE())), NFSCodeEnv.EnvTree.Tree.NODE("stateSelect", NFSCodeEnv.VAR(BUILTIN_ATTR_STATESELECT, NONE()), 1, NFSCodeEnv.EnvTree.Tree.EMPTY(), NFSCodeEnv.EnvTree.Tree.LEAF("unit", NFSCodeEnv.VAR(BUILTIN_ATTR_UNIT, NONE()))))), NFSCodeEnv.EXTENDS_TABLE(nil, nil, NONE()), NFSCodeEnv.IMPORT_TABLE(false, nil, nil), NONE()))::Env

         const BUILTIN_INTEGER_ENV = list(NFSCodeEnv.FRAME(SOME("Integer"), NFSCodeEnv.NORMAL_SCOPE(), NFSCodeEnv.EnvTree.Tree.NODE("quantity", NFSCodeEnv.VAR(BUILTIN_ATTR_QUANTITY, NONE()), 2, NFSCodeEnv.EnvTree.Tree.NODE("max", NFSCodeEnv.VAR(BUILTIN_INTEGER_MAX, NONE()), 1, NFSCodeEnv.EnvTree.Tree.LEAF("fixed", NFSCodeEnv.VAR(BUILTIN_ATTR_FIXED, NONE())), NFSCodeEnv.EnvTree.Tree.LEAF("min", NFSCodeEnv.VAR(BUILTIN_INTEGER_MIN, NONE()))), NFSCodeEnv.EnvTree.Tree.LEAF("start", NFSCodeEnv.VAR(BUILTIN_INTEGER_START, NONE()))), NFSCodeEnv.EXTENDS_TABLE(nil, nil, NONE()), NFSCodeEnv.IMPORT_TABLE(false, nil, nil), NONE()))::Env

         const BUILTIN_BOOLEAN_ENV = list(NFSCodeEnv.FRAME(SOME("Boolean"), NFSCodeEnv.NORMAL_SCOPE(), NFSCodeEnv.EnvTree.Tree.NODE("quantity", NFSCodeEnv.VAR(BUILTIN_ATTR_QUANTITY, NONE()), 1, NFSCodeEnv.EnvTree.Tree.LEAF("fixed", NFSCodeEnv.VAR(BUILTIN_ATTR_FIXED, NONE())), NFSCodeEnv.EnvTree.Tree.LEAF("start", NFSCodeEnv.VAR(BUILTIN_BOOLEAN_START, NONE()))), NFSCodeEnv.EXTENDS_TABLE(nil, nil, NONE()), NFSCodeEnv.IMPORT_TABLE(false, nil, nil), NONE()))::Env

         const BUILTIN_STRING_ENV = list(NFSCodeEnv.FRAME(SOME("String"), NFSCodeEnv.NORMAL_SCOPE(), NFSCodeEnv.EnvTree.Tree.NODE("quantity", NFSCodeEnv.VAR(BUILTIN_ATTR_QUANTITY, NONE()), 2, NFSCodeEnv.EnvTree.Tree.EMPTY(), NFSCodeEnv.EnvTree.Tree.LEAF("start", NFSCodeEnv.VAR(BUILTIN_STRING_START, NONE()))), NFSCodeEnv.EXTENDS_TABLE(nil, nil, NONE()), NFSCodeEnv.IMPORT_TABLE(false, nil, nil), NONE()))::Env

         const BUILTIN_STATESELECT_ENV = list(NFSCodeEnv.FRAME(SOME("StateSelect"), NFSCodeEnv.NORMAL_SCOPE(), NFSCodeEnv.EnvTree.Tree.NODE("max", NFSCodeEnv.VAR(BUILTIN_ENUM_MAX, NONE()), 3, NFSCodeEnv.EnvTree.Tree.NODE("default", NFSCodeEnv.VAR(BUILTIN_STATESELECT_DEFAULT, NONE()), 2, NFSCodeEnv.EnvTree.Tree.NODE("avoid", NFSCodeEnv.VAR(BUILTIN_STATESELECT_AVOID, NONE()), 1, NFSCodeEnv.EnvTree.Tree.LEAF("always", NFSCodeEnv.VAR(BUILTIN_STATESELECT_ALWAYS, NONE())), NFSCodeEnv.EnvTree.Tree.EMPTY()), NFSCodeEnv.EnvTree.Tree.LEAF("fixed", NFSCodeEnv.VAR(BUILTIN_ATTR_FIXED, NONE()))), NFSCodeEnv.EnvTree.Tree.NODE("never", NFSCodeEnv.VAR(BUILTIN_STATESELECT_NEVER, NONE()), 2, NFSCodeEnv.EnvTree.Tree.LEAF("min", NFSCodeEnv.VAR(BUILTIN_ENUM_MIN, NONE())), NFSCodeEnv.EnvTree.Tree.NODE("quantity", NFSCodeEnv.VAR(BUILTIN_ATTR_QUANTITY, NONE()), 1, NFSCodeEnv.EnvTree.Tree.LEAF("prefer", NFSCodeEnv.VAR(BUILTIN_STATESELECT_PREFER, NONE())), NFSCodeEnv.EnvTree.Tree.LEAF("start", NFSCodeEnv.VAR(BUILTIN_ENUM_START, NONE()))))), NFSCodeEnv.EXTENDS_TABLE(nil, nil, NONE()), NFSCodeEnv.IMPORT_TABLE(false, nil, nil), NONE()))::Env
         #=  The builtin types:
         =#

         const BUILTIN_REAL = NFSCodeEnv.CLASS(SCode.CLASS("Real", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), BUILTIN_REAL_ENV, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_INTEGER = NFSCodeEnv.CLASS(SCode.CLASS("Integer", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), BUILTIN_INTEGER_ENV, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_BOOLEAN = NFSCodeEnv.CLASS(SCode.CLASS("Boolean", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), BUILTIN_BOOLEAN_ENV, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_STRING = NFSCodeEnv.CLASS(SCode.CLASS("String", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), BUILTIN_STRING_ENV, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_STATESELECT = NFSCodeEnv.CLASS(SCode.CLASS("StateSelect", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_CLASS(), SCode.ENUMERATION(list(SCode.ENUM("never", SCode.noComment), SCode.ENUM("avoid", SCode.noComment), SCode.ENUM("default", SCode.noComment), SCode.ENUM("prefer", SCode.noComment), SCode.ENUM("always", SCode.noComment))), SCode.noComment, AbsynUtil.dummyInfo), BUILTIN_STATESELECT_ENV, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_EXTERNALOBJECT = NFSCodeEnv.CLASS(SCode.CLASS("ExternalObject", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.PARTIAL(), SCode.R_CLASS(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), NFSCodeEnv.emptyEnv, NFSCodeEnv.BASIC_TYPE())::Item

         const BUILTIN_CLOCK = NFSCodeEnv.CLASS(SCode.CLASS("Clock", SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.PARTIAL(), SCode.R_CLASS(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo), NFSCodeEnv.emptyEnv, NFSCodeEnv.BASIC_TYPE())::Item

         #= Looks up a simple identifier in the environment and returns the environment
          item, the path, and the enclosing scope of the name. =#
        function lookupSimpleName(inName::Absyn.Ident, inEnv::Env) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outPath::Absyn.Path
              local outItem::Item

              @match (SOME(outItem), SOME(outPath), SOME(outEnv)) = lookupSimpleName2(inName, inEnv, nil)
          (outItem, outPath, outEnv)
        end

         #= Helper function to lookupSimpleName. Looks up a simple identifier in the
          environment. =#
        function lookupSimpleName2(inName::Absyn.Ident, inEnv::Env, inVisitedScopes::List{<:String}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local frame_type::FrameType
                  local rest_env::Env
                  local opt_item::Option{Item}
                  local opt_path::Option{Absyn.Path}
                  local opt_env::Option{Env}
                  local scope_name::String
                   #=  Check the local scope.
                   =#
                @matchcontinue (inName, inEnv, inVisitedScopes) begin
                  (_, _, _)  => begin
                      (opt_item, opt_path, opt_env) = lookupInLocalScope(inName, inEnv, inVisitedScopes)
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, NFSCodeEnv.FRAME(name = SOME(scope_name), frameType = frame_type) <| rest_env, _)  => begin
                      frameNotEncapsulated(frame_type)
                      (opt_item, opt_path, opt_env) = lookupSimpleName2(inName, rest_env, _cons(scope_name, inVisitedScopes))
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, NFSCodeEnv.FRAME(frameType = NFSCodeEnv.ENCAPSULATED_SCOPE(__)) <| rest_env, _)  => begin
                      rest_env = NFSCodeEnv.getEnvTopScope(rest_env)
                      (opt_item, opt_path, opt_env) = lookupSimpleName2(inName, rest_env, nil)
                      checkBuiltinItem(opt_item)
                    (opt_item, opt_path, opt_env)
                  end
                end
              end
               #=  If not found in the local scope, check the next frame unless the current
               =#
               #=  frame is encapsulated.
               =#
               #=  If the current frame is encapsulated, check for builtin types and
               =#
               #=  functions in the top scope.
               =#
          (outItem, outPath, outEnv)
        end

         #= Fails if the frame type is encapsulated, otherwise succeeds. =#
        function frameNotEncapsulated(frameType::FrameType)  
              _ = begin
                @match frameType begin
                  NFSCodeEnv.ENCAPSULATED_SCOPE(__)  => begin
                    fail()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkBuiltinItem(inItem::Option{<:Item})  
              _ = begin
                @match inItem begin
                  SOME(NFSCodeEnv.CLASS(classType = NFSCodeEnv.BUILTIN(__)))  => begin
                    ()
                  end
                  
                  NONE()  => begin
                    ()
                  end
                end
              end
        end

         #= Looks up a simple identifier in the environment. Returns SOME(item) if an
          item is found, NONE() if a partial match was found (for example when the name
          matches the import name of an import, but the imported class couldn't be
          found), or fails if no match is found. =#
        function lookupInLocalScope(inName::Absyn.Ident, inEnv::Env, inVisitedScopes::List{<:String}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local rest_env::Env
                  local env::Env
                  local item::Item
                  local opt_item::Option{Item}
                  local opt_path::Option{Absyn.Path}
                  local imps::List{Import}
                  local path::Absyn.Path
                  local opt_env::Option{Env}
                   #=  Look among the locally declared components.
                   =#
                @matchcontinue (inName, inEnv, inVisitedScopes) begin
                  (_, _, _)  => begin
                      (item, env) = lookupInClass(inName, inEnv)
                    (SOME(item), SOME(Absyn.IDENT(inName)), SOME(env))
                  end
                  
                  (_, _, _)  => begin
                      (opt_item, opt_path, opt_env) = lookupInBaseClasses(inName, inEnv, INSERT_REDECLARES(), inVisitedScopes)
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, NFSCodeEnv.FRAME(importTable = NFSCodeEnv.IMPORT_TABLE(hidden = false, qualifiedImports = imps)) <| _, _)  => begin
                      (opt_item, opt_path, opt_env) = lookupInQualifiedImports(inName, imps, inEnv)
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, NFSCodeEnv.FRAME(importTable = NFSCodeEnv.IMPORT_TABLE(hidden = false, unqualifiedImports = imps)) <| _, _)  => begin
                      (item, path, env) = lookupInUnqualifiedImports(inName, imps, inEnv)
                    (SOME(item), SOME(path), SOME(env))
                  end
                  
                  (_, NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)) <| rest_env, _)  => begin
                      (opt_item, opt_path, opt_env) = lookupInLocalScope(inName, rest_env, inVisitedScopes)
                    (opt_item, opt_path, opt_env)
                  end
                end
              end
               #=  Look among the inherited components.
               =#
               #=  Look among the qualified imports.
               =#
               #=  Look among the unqualified imports.
               =#
               #=  Look in the next scope only if the current scope is an implicit scope
               =#
               #=  (for example a for or match/matchcontinue scope).
               =#
          (outItem, outPath, outEnv)
        end

        function lookupInClass(inName::Absyn.Ident, inEnv::Env) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              local tree::EnvTree.Tree

              @match _cons(NFSCodeEnv.FRAME(clsAndVars = tree), _) = inEnv
              outItem = EnvTree.get(tree, inName)
              (outItem, outEnv) = resolveAlias(outItem, inEnv)
          (outItem, outEnv)
        end

         #= Resolved an alias by looking up the aliased item recursively in the
           environment until a non-alias item is found. =#
        function resolveAlias(inItem::Item, inEnv::Env) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local name::String
                  local item::Item
                  local path::Absyn.Path
                  local env::Env
                  local tree::EnvTree.Tree
                @match (inItem, inEnv) begin
                  (NFSCodeEnv.ALIAS(name = name, path = NONE()), NFSCodeEnv.FRAME(clsAndVars = tree) <| _)  => begin
                      item = EnvTree.get(tree, name)
                      (item, env) = resolveAlias(item, inEnv)
                    (item, env)
                  end
                  
                  (NFSCodeEnv.ALIAS(name = name, path = SOME(path)), _)  => begin
                      env = NFSCodeEnv.getEnvTopScope(inEnv)
                      env = NFSCodeEnv.enterScopePath(env, path)
                      @match _cons(NFSCodeEnv.FRAME(clsAndVars = tree), _) = env
                      item = EnvTree.get(tree, name)
                      (item, env) = resolveAlias(item, env)
                    (item, env)
                  end
                  
                  _  => begin
                      (inItem, inEnv)
                  end
                end
              end
          (outItem, outEnv)
        end

         #= Looks up an identifier by following the extends clauses in a scope. =#
        function lookupInBaseClasses(inName::Absyn.Ident, inEnv::Env, inReplaceRedeclares::RedeclareReplaceStrategy, inVisitedScopes::List{<:String}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              local env::Env
              local bcl::List{Extends}

              @match _cons(NFSCodeEnv.FRAME(extendsTable = NFSCodeEnv.EXTENDS_TABLE(baseClasses = (@match _cons(_, _) = bcl))), _) = inEnv
               #=  Remove the extends, base class names should not be inherited.
               =#
              env = NFSCodeEnv.removeExtendsFromLocalScope(inEnv)
               #=  Unhide the imports in case they've been hidden so we can find the base
               =#
               #=  classes.
               =#
              env = NFSCodeEnv.setImportTableHidden(env, false)
              (outItem, outPath, outEnv) = lookupInBaseClasses2(inName, bcl, env, inEnv, inReplaceRedeclares, inVisitedScopes)
          (outItem, outPath, outEnv)
        end

         #= Helper function to lookupInBaseClasses. Tries to find an identifier by
           looking in the extended classes in a scope. =#
        function lookupInBaseClasses2(inName::Absyn.Ident, inBaseClasses::List{<:Extends}, inEnv::Env, inEnvWithExtends::Env, inReplaceRedeclares::RedeclareReplaceStrategy, inVisitedScopes::List{<:String}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local ext::Extends
                  local rest_ext::List{Extends}
                  local item::Option{Item}
                  local path::Option{Absyn.Path}
                  local env::Option{Env}
                @matchcontinue (inName, inBaseClasses, inEnv, inEnvWithExtends, inReplaceRedeclares, inVisitedScopes) begin
                  (_, ext <| _, _, _, _, _)  => begin
                      (item, path, env) = lookupInBaseClasses3(inName, ext, inEnv, inEnvWithExtends, inReplaceRedeclares, inVisitedScopes)
                    (item, path, env)
                  end
                  
                  (_, _ <| rest_ext, _, _, _, _)  => begin
                      (item, path, env) = lookupInBaseClasses2(inName, rest_ext, inEnv, inEnvWithExtends, inReplaceRedeclares, inVisitedScopes)
                    (item, path, env)
                  end
                end
              end
          (outItem, outPath, outEnv)
        end

         #= Helper function to lookupInBaseClasses2. Looks up an identifier in the given
           extended class. =#
        function lookupInBaseClasses3(inName::Absyn.Ident, inBaseClass::Extends, inEnv::Env, inEnvWithExtends::Env, inReplaceRedeclares::RedeclareReplaceStrategy, inVisitedScopes::List{<:String}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local bc::Absyn.Path
                  local path::Absyn.Path
                  local item::Item
                  local env::Env
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local info::SourceInfo
                  local opt_path::Option{Absyn.Path}
                  local opt_item::Option{Item}
                  local opt_env::Option{Env}
                @match (inName, inBaseClass, inEnv, inEnvWithExtends, inReplaceRedeclares, inVisitedScopes) begin
                  (_, NFSCodeEnv.EXTENDS(baseClass = bc && Absyn.QUALIFIED(name = "$E"), info = info), _, _, _, _)  => begin
                      NFEnvExtends.printExtendsError(bc, inEnvWithExtends, info)
                    (NONE(), NONE(), NONE())
                  end
                  
                  (_, NFSCodeEnv.EXTENDS(baseClass = bc, redeclareModifiers = redecls, info = info), _, _, _, _)  => begin
                      (item, path, env) = lookupBaseClassName(bc, inEnv, info)
                      @match true = checkVisitedScopes(inVisitedScopes, inEnv, path)
                      item = NFSCodeEnv.setImportsInItemHidden(item, true)
                      (opt_item, opt_env) = NFSCodeFlattenRedeclare.replaceRedeclares(redecls, item, env, inEnvWithExtends, inReplaceRedeclares)
                      (opt_item, opt_path, opt_env) = lookupInBaseClasses4(Absyn.IDENT(inName), opt_item, opt_env)
                    (opt_item, opt_path, opt_env)
                  end
                end
              end
               #=  Look in the first base class.
               =#
               #=  Find the base class.
               =#
               #=  Hide the imports to make sure that we don't find the name via them
               =#
               #=  (imports are not inherited).
               =#
               #=  Look in the base class.
               =#
          (outItem, outPath, outEnv)
        end

         #= Checks if we are trying to look up a base class that we are coming from when
           going up in the environment, to avoid infinite loops. =#
        function checkVisitedScopes(inVisitedScopes::List{<:String}, inEnv::Env, inBaseClass::Absyn.Path) ::Bool 
              local outRes::Bool

              outRes = begin
                  local env_path::Absyn.Path
                  local visited_path::Absyn.Path
                  local bc_path::Absyn.Path
                @matchcontinue (inVisitedScopes, inEnv, inBaseClass) begin
                  ( nil(), _, _)  => begin
                    true
                  end
                  
                  (_, _, _)  => begin
                      env_path = NFSCodeEnv.getEnvPath(inEnv)
                      bc_path = AbsynUtil.removePrefix(env_path, inBaseClass)
                      visited_path = AbsynUtil.stringListPath(inVisitedScopes)
                      @match true = AbsynUtil.pathPrefixOf(visited_path, bc_path)
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          outRes
        end

         #= Helper function to lookupInBaseClasses3. Tries to find the name in the given
           item. =#
        function lookupInBaseClasses4(inName::Absyn.Path, inItem::Option{<:Item}, inEnv::Option{<:Env}) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
              local outEnv::Option{Env}
              local outPath::Option{Absyn.Path}
              local outItem::Option{Item}

              (outItem, outPath, outEnv) = begin
                  local item::Item
                  local path::Absyn.Path
                  local env::Env
                   #=  If the item and env is NONE it means that an error occured (hopefully a
                   =#
                   #=  user error), and we should stop searching.
                   =#
                @match (inName, inItem, inEnv) begin
                  (_, NONE(), NONE())  => begin
                    (NONE(), NONE(), NONE())
                  end
                  
                  (_, SOME(item), SOME(env))  => begin
                      (item, path, env) = lookupNameInItem(inName, item, env)
                    (SOME(item), SOME(path), SOME(env))
                  end
                end
              end
               #=  Otherwise, try to find the name in the given item. If the name can not be
               =#
               #=  found we fail, so that we can continue to look in other base classes.
               =#
          (outItem, outPath, outEnv)
        end

         #= Looks up a name through the qualified imports in a scope. If it finds the
          name it returns the item, path, and environment for the name. It can also find
          a partial match, in which case it returns NONE() to signal that the lookup
          shouldn't look further. This can happen if the have an 'import A.B' and an
          element 'B.C', but C is not in A.B. Finally it can also fail to find anything,
          in which case it simply fails as normal. =#
        function lookupInQualifiedImports(inName::Absyn.Ident, inImports::List{<:Import}, inEnv::Env) ::Tuple{Option{Item}, Option{Absyn.Path}, Option{Env}} 
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
                   #=  No match, search the rest of the list of imports.
                   =#
                @matchcontinue (inName, inImports, inEnv) begin
                  (_, Absyn.NAMED_IMPORT(name = name) <| rest_imps, _)  => begin
                      @match false = stringEqual(inName, name)
                      (opt_item, opt_path, opt_env) = lookupInQualifiedImports(inName, rest_imps, inEnv)
                    (opt_item, opt_path, opt_env)
                  end
                  
                  (_, Absyn.NAMED_IMPORT(name = name, path = path) <| _, _)  => begin
                      @match true = stringEqual(inName, name)
                      (item, path, env) = lookupFullyQualified(path, inEnv)
                    (SOME(item), SOME(path), SOME(env))
                  end
                  
                  (_, Absyn.NAMED_IMPORT(name = name) <| _, _)  => begin
                      @match true = stringEqual(inName, name)
                    (NONE(), NONE(), NONE())
                  end
                end
              end
               #=  Match, look up the fully qualified import path.
               =#
               #=  Partial match, return NONE(). This is when only part of the import path
               =#
               #=  can be found, in which case we should stop looking further.
               =#
          (outItem, outPath, outEnv)
        end

         #= Looks up a name through the qualified imports in a scope. If it finds the
          name it returns the item, path, and environment for the name, otherwise it
          fails. =#
        function lookupInUnqualifiedImports(inName::Absyn.Ident, inImports::List{<:Import}, inEnv::Env) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outPath::Absyn.Path
              local outItem::Item

              (outItem, outPath, outEnv) = begin
                  local item::Item
                  local path::Absyn.Path
                  local path2::Absyn.Path
                  local rest_imps::List{Import}
                  local env::Env
                   #=  For each unqualified import we have to look up the package the import
                   =#
                   #=  points to, and then look among the public member of the package for the
                   =#
                   #=  name we are looking for.
                   =#
                @matchcontinue (inName, inImports, inEnv) begin
                  (_, Absyn.UNQUAL_IMPORT(path = path) <| _, _)  => begin
                      (item, path, env) = lookupFullyQualified(path, inEnv)
                      (item, path2, env) = lookupNameInItem(Absyn.IDENT(inName), item, env)
                      path = joinPaths(path, path2)
                    (item, path, env)
                  end
                  
                  (_, _ <| rest_imps, _)  => begin
                      (item, path, env) = lookupInUnqualifiedImports(inName, rest_imps, inEnv)
                    (item, path, env)
                  end
                end
              end
               #=  Look up the import path.
               =#
               #=  Look up the name among the public member of the found package.
               =#
               #=  Combine the paths for the name and the package it was found in.
               =#
               #=  No match, continue with the rest of the imports.
               =#
          (outItem, outPath, outEnv)
        end

         #= Looks up a fully qualified path in the environment, returning the
          environment item, path and environment of the name if found. =#
        function lookupFullyQualified(inName::Absyn.Path, inEnv::Env) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outPath::Absyn.Path
              local outItem::Item

              local env::Env

              env = NFSCodeEnv.getEnvTopScope(inEnv)
              (outItem, outPath, outEnv) = lookupNameInPackage(inName, env)
              outPath = AbsynUtil.makeFullyQualified(outPath)
          (outItem, outPath, outEnv)
        end

         #= Looks up a name inside the environment of a package, returning the
          environment item, path and environment of the name if found. =#
        function lookupNameInPackage(inName::Absyn.Path, inEnv::Env) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outPath::Absyn.Path
              local outItem::Item

              (outItem, outPath, outEnv) = begin
                  local name::Absyn.Ident
                  local path::Absyn.Path
                  local new_path::Absyn.Path
                  local top_scope::Frame
                  local env::Env
                  local item::Item
                   #=  Simple name, look in the local scope.
                   =#
                @match (inName, inEnv) begin
                  (Absyn.IDENT(name = name), _)  => begin
                      @match (SOME(item), SOME(path), SOME(env)) = lookupInLocalScope(name, inEnv, nil)
                      env = NFSCodeEnv.setImportTableHidden(env, false)
                    (item, path, env)
                  end
                  
                  (Absyn.QUALIFIED(name = name, path = path), _ <| _)  => begin
                      @match (SOME(item), SOME(new_path), SOME(env)) = lookupInLocalScope(name, inEnv, nil)
                      env = NFSCodeEnv.setImportTableHidden(env, false)
                      (item, path, env) = lookupNameInItem(path, item, env)
                      path = joinPaths(new_path, path)
                    (item, path, env)
                  end
                end
              end
               #=  Qualified name.
               =#
               #=  Look up the name in the local scope.
               =#
               #=  Look for the rest of the path in the found item.
               =#
          (outItem, outPath, outEnv)
        end

         #= Looks up a component reference inside the environment of a package, returning
          the environment item, path and environment of the reference if found. =#
        function lookupCrefInPackage(inCref::Absyn.ComponentRef, inEnv::Env) ::Tuple{Item, Absyn.ComponentRef} 
              local outCref::Absyn.ComponentRef
              local outItem::Item

              (outItem, outCref) = begin
                  local name::Absyn.Ident
                  local new_path::Absyn.Path
                  local subs::List{Absyn.Subscript}
                  local cref::Absyn.ComponentRef
                  local cref_rest::Absyn.ComponentRef
                  local item::Item
                  local env::Env
                   #=  Simple identifier, look in the local scope.
                   =#
                @matchcontinue (inCref, inEnv) begin
                  (Absyn.CREF_IDENT(name = name, subscripts = subs), _)  => begin
                      @match (SOME(item), SOME(new_path), _) = lookupInLocalScope(name, inEnv, nil)
                      cref = AbsynUtil.pathToCrefWithSubs(new_path, subs)
                    (item, cref)
                  end
                  
                  (Absyn.CREF_QUAL(name = name, subscripts = subs, componentRef = cref_rest), _)  => begin
                      @match (SOME(item), SOME(new_path), SOME(env)) = lookupInLocalScope(name, inEnv, nil)
                      (item, cref_rest) = lookupCrefInItem(cref_rest, item, env)
                      @shouldFail @match Absyn.CREF_FULLYQUALIFIED(_) = cref_rest
                      cref = AbsynUtil.pathToCrefWithSubs(new_path, subs)
                      cref = AbsynUtil.joinCrefs(cref, cref_rest)
                    (item, cref)
                  end
                  
                  (Absyn.CREF_QUAL(name = name, componentRef = cref_rest), _)  => begin
                      @match (SOME(item), SOME(_), SOME(env)) = lookupInLocalScope(name, inEnv, nil)
                      @match (item, (@match Absyn.CREF_FULLYQUALIFIED(_) = cref_rest)) = lookupCrefInItem(cref_rest, item, env)
                      cref = cref_rest
                    (item, cref)
                  end
                end
              end
               #=  Qualified identifier, what we get back is not fully qualified
               =#
               #=  Look in the local scope.
               =#
               #=  Look for the rest of the reference in the found item.
               =#
               #=  not fully qualified
               =#
               #=  Qualified identifier, what we get back is fully qualified, i.e. from import!
               =#
               #=  Look in the local scope.
               =#
               #=  Look for the rest of the reference in the found item, fully qualified
               =#
          (outItem, outCref)
        end

         #= Looks up a name inside of an item, which can be either a variable or a
          class. =#
        function lookupNameInItem(inName::Absyn.Path, inItem::Item, inEnv::Env) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outPath::Absyn.Path
              local outItem::Item

              (outItem, outPath, outEnv) = begin
                  local item::Item
                  local path::Absyn.Path
                  local class_env::Frame
                  local env::Env
                  local type_env::Env
                  local type_spec::Absyn.TypeSpec
                  local mods::SCode.Mod
                  local redeclares::List{NFSCodeEnv.Redeclaration}
                  local info::SourceInfo
                   #=  A variable.
                   =#
                @match (inName, inItem, inEnv) begin
                  (_, NFSCodeEnv.VAR(var = SCode.COMPONENT(typeSpec = type_spec, modifications = mods, info = info)), env)  => begin
                      (item, _, type_env) = lookupTypeSpec(type_spec, env, info)
                      redeclares = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
                      (item, type_env, _) = NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv(redeclares, item, type_env, inEnv, NFInstPrefix.emptyPrefix)
                      (item, path, env) = lookupNameInItem(inName, item, type_env)
                    (item, path, env)
                  end
                  
                  (_, NFSCodeEnv.CLASS(env = class_env <|  nil()), _)  => begin
                      env = NFSCodeEnv.enterFrame(class_env, inEnv)
                      (item, path, env) = lookupNameInPackage(inName, env)
                    (item, path, env)
                  end
                  
                  (_, NFSCodeEnv.REDECLARED_ITEM(item = item, declaredEnv = env), _)  => begin
                      (item, path, env) = lookupNameInItem(inName, item, env)
                    (item, path, env)
                  end
                end
              end
               #= env = NFSCodeEnv.setImportTableHidden(env, false);
               =#
               #=  Look up the variable type.
               =#
               #=  Apply redeclares to the type and look for the name inside the type.
               =#
               #=  A class.
               =#
               #=  Look in the class's environment.
               =#
          (outItem, outPath, outEnv)
        end

         #= Looks up a component reference inside of an item, which can be either a
          variable or a class. =#
        function lookupCrefInItem(inCref::Absyn.ComponentRef, inItem::Item, inEnv::Env) ::Tuple{Item, Absyn.ComponentRef} 
              local outCref::Absyn.ComponentRef
              local outItem::Item

              (outItem, outCref) = begin
                  local item::Item
                  local cref::Absyn.ComponentRef
                  local class_env::Frame
                  local env::Env
                  local type_env::Env
                  local type_spec::Absyn.TypeSpec
                  local mods::SCode.Mod
                  local redeclares::List{NFSCodeEnv.Redeclaration}
                  local info::SourceInfo
                   #=  A variable.
                   =#
                @match (inCref, inItem, inEnv) begin
                  (_, NFSCodeEnv.VAR(var = SCode.COMPONENT(typeSpec = type_spec, modifications = mods, info = info)), _)  => begin
                      (item, _, type_env) = lookupTypeSpec(type_spec, inEnv, info)
                      redeclares = NFSCodeFlattenRedeclare.extractRedeclaresFromModifier(mods)
                      (item, type_env, _) = NFSCodeFlattenRedeclare.replaceRedeclaredElementsInEnv(redeclares, item, type_env, inEnv, NFInstPrefix.emptyPrefix)
                      (item, cref) = lookupCrefInItem(inCref, item, type_env)
                    (item, cref)
                  end
                  
                  (_, NFSCodeEnv.CLASS(env = class_env <|  nil()), _)  => begin
                      env = NFSCodeEnv.enterFrame(class_env, inEnv)
                      (item, cref) = lookupCrefInPackage(inCref, env)
                    (item, cref)
                  end
                  
                  (_, NFSCodeEnv.REDECLARED_ITEM(item = item, declaredEnv = env), _)  => begin
                      (item, cref) = lookupCrefInItem(inCref, item, env)
                    (item, cref)
                  end
                end
              end
               #=  Look up the variable's type.
               =#
               #=  Apply redeclares to the type and look for the name inside the type.
               =#
               #=  A class.
               =#
               #=  Look in the class's environment.
               =#
          (outItem, outCref)
        end

         #= Looks up the given name, and returns a list of all the base classes in the
           current scope that the name was found in. =#
        function lookupBaseClasses(inName::SCode.Ident, inEnv::Env) ::List{Absyn.Path} 
              local outBaseClasses::List{Absyn.Path}

              local bcl::List{Extends}

              @match _cons(NFSCodeEnv.FRAME(extendsTable = NFSCodeEnv.EXTENDS_TABLE(baseClasses = (@match _cons(_, _) = bcl))), _) = inEnv
              (_, outBaseClasses) = ListUtil.fold22(bcl, lookupBaseClasses2, inName, inEnv, nil, nil)
              @match false = listEmpty(outBaseClasses)
              outBaseClasses = listReverse(outBaseClasses)
          outBaseClasses
        end

         #= Helper function to lookupBaseClasses. Tries to find a name in the given base
           class, and appends the base class path to the given list if found. Otherwise
           returns the unchanged list. =#
        function lookupBaseClasses2(inBaseClass::Extends, inName::SCode.Ident, inEnv::Env, items::List{<:Item}, bcl::List{<:Absyn.Path}) ::Tuple{List{Item}, List{Absyn.Path}} 



              (items, bcl) = begin
                  local bc::Absyn.Path
                  local redecls::List{NFSCodeEnv.Redeclaration}
                  local info::SourceInfo
                  local env::Env
                  local item::Item
                @matchcontinue (inBaseClass, inName, inEnv) begin
                  (NFSCodeEnv.EXTENDS(baseClass = bc, info = info), _, _)  => begin
                      (item, _, env) = lookupBaseClassName(bc, inEnv, info)
                      item = NFSCodeEnv.setImportsInItemHidden(item, true)
                      (item, _, _) = lookupNameInItem(Absyn.IDENT(inName), item, env)
                    (_cons(item, items), _cons(bc, bcl))
                  end
                  
                  _  => begin
                      (items, bcl)
                  end
                end
              end
               #=  Look up the base class.
               =#
               #=  Hide the imports to make sure that we don't find the name via them
               =#
               #=  (imports are not inherited).
               =#
               #=  Note that we don't need to apply any redeclares here, since no part
               =#
               #=  of the base class path may be replaceable. The element we're looking
               =#
               #=  for may have been replaced, but that doesn't matter since we only
               =#
               #=  want to check if it can be found or not.
               =#
               #=  Check if we can find the name in the base class. If so, add the base
               =#
               #=  class path to the list.
               =#
          (items, bcl)
        end

         #= Looks up an inherited name by searching the extends in the local scope. =#
        function lookupInheritedName(inName::SCode.Ident, inEnv::Env) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              @match (SOME(outItem), _, SOME(outEnv)) = lookupInBaseClasses(inName, inEnv, INSERT_REDECLARES(), nil)
          (outItem, outEnv)
        end

        function lookupInheritedNameAndBC(inName::SCode.Ident, inEnv::Env) ::Tuple{List{Item}, List{Absyn.Path}} 
              local outBaseClasses::List{Absyn.Path}
              local outItems::List{Item}

              local bcl::List{Extends}

              @match _cons(NFSCodeEnv.FRAME(extendsTable = NFSCodeEnv.EXTENDS_TABLE(baseClasses = (@match _cons(_, _) = bcl))), _) = inEnv
              (outItems, outBaseClasses) = ListUtil.fold22(bcl, lookupBaseClasses2, inName, inEnv, nil, nil)
              outBaseClasses = listReverse(outBaseClasses)
              outItems = listReverse(outItems)
          (outItems, outBaseClasses)
        end

        function lookupRedeclaredClassByItem(inItem::Item, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local name::SCode.Ident
                  local item::Item
                  local env::Env
                  local rdp::SCode.Redeclare
                  local rpp::SCode.Replaceable
                @matchcontinue (inItem, inEnv, inInfo) begin
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name)), _, _)  => begin
                      @match (SOME(item), _, SOME(env)) = lookupInBaseClasses(name, inEnv, IGNORE_REDECLARES(), nil)
                      @match SCode.PREFIXES(redeclarePrefix = rdp, replaceablePrefix = rpp) = NFSCodeEnv.getItemPrefixes(item)
                      (item, env) = lookupRedeclaredClass2(item, rdp, rpp, env, inInfo)
                    (item, env)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeLookup.lookupRedeclaredClassByItem failed on " + NFSCodeEnv.getItemName(inItem) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
               #=  No error message is output if the previous case fails. This is because
               =#
               #=  lookupInBaseClasses is used by NFSCodeEnv.extendEnvWithClassExtends when
               =#
               #=  adding the redeclaration to the environment, and lookupRedeclaredClass2
               =#
               #=  outputs its own errors.
               =#
          (outItem, outEnv)
        end

        function lookupRedeclaredClass2(inItem::Item, inRedeclarePrefix::SCode.Redeclare, inReplaceablePrefix::SCode.Replaceable, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local name::SCode.Ident
                  local item::Item
                  local env::Env
                  local info::SourceInfo
                  local rdp::SCode.Redeclare
                  local rpp::SCode.Replaceable
                   #=  Replaceable element which is not a redeclaration => return the element.
                   =#
                @matchcontinue (inItem, inRedeclarePrefix, inReplaceablePrefix, inEnv, inInfo) begin
                  (_, SCode.NOT_REDECLARE(__), SCode.REPLACEABLE(__), _, _)  => begin
                    (inItem, inEnv)
                  end
                  
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name)), SCode.REDECLARE(__), SCode.REPLACEABLE(__), _, _)  => begin
                      @match (SOME(item), _, SOME(env)) = lookupInBaseClasses(name, inEnv, IGNORE_REDECLARES(), nil)
                      @match SCode.PREFIXES(redeclarePrefix = rdp, replaceablePrefix = rpp) = NFSCodeEnv.getItemPrefixes(item)
                      (item, env) = lookupRedeclaredClass2(item, rdp, rpp, env, inInfo)
                    (item, env)
                  end
                  
                  (NFSCodeEnv.REDECLARED_ITEM(item, env), _, _, _, _)  => begin
                      (item, env) = lookupRedeclaredClass2(item, inRedeclarePrefix, inReplaceablePrefix, env, inInfo)
                    (item, env)
                  end
                  
                  (NFSCodeEnv.CLASS(cls = SCode.CLASS(name = name, info = info)), _, SCode.NOT_REPLACEABLE(__), _, _)  => begin
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, inInfo)
                      Error.addSourceMessage(Error.REDECLARE_NON_REPLACEABLE, list("class", name), info)
                    fail()
                  end
                  
                  (NFSCodeEnv.VAR(var = SCode.COMPONENT(name = name, info = info)), _, _, _, _)  => begin
                      Error.addSourceMessage(Error.ERROR_FROM_HERE, nil, inInfo)
                      Error.addSourceMessage(Error.INVALID_REDECLARE_AS, list("component", name, "a class"), info)
                    fail()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeLookup.lookupRedeclaredClass2 failed on " + NFSCodeEnv.getItemName(inItem) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
               #=  Replaceable element which is a redeclaration => continue.
               =#
               #=  Non-replaceable element => error.
               =#
               #=  Redeclaration of class to component => error.
               =#
          (outItem, outEnv)
        end

         #= Checks if a name references a builtin type, and returns an environment item
          for that type or fails. =#
        function lookupBuiltinType(inName::Absyn.Ident) ::Item 
              local outItem::Item

              outItem = begin
                @match inName begin
                  "Real"  => begin
                    BUILTIN_REAL
                  end
                  
                  "Integer"  => begin
                    BUILTIN_INTEGER
                  end
                  
                  "Boolean"  => begin
                    BUILTIN_BOOLEAN
                  end
                  
                  "String"  => begin
                    BUILTIN_STRING
                  end
                  
                  "StateSelect"  => begin
                    BUILTIN_STATESELECT
                  end
                  
                  "ExternalObject"  => begin
                    BUILTIN_EXTERNALOBJECT
                  end
                  
                  "Clock"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    BUILTIN_CLOCK
                  end
                  
                  "$RealType"  => begin
                    BUILTIN_REALTYPE_ITEM
                  end
                  
                  "$IntegerType"  => begin
                    BUILTIN_INTEGERTYPE_ITEM
                  end
                  
                  "$BooleanType"  => begin
                    BUILTIN_BOOLEANTYPE_ITEM
                  end
                  
                  "$StringType"  => begin
                    BUILTIN_STRINGTYPE_ITEM
                  end
                  
                  "$EnumType"  => begin
                    BUILTIN_ENUMTYPE_ITEM
                  end
                end
              end
          outItem
        end

        function lookupBuiltinName(inName::Absyn.Path) ::Tuple{Item, Env} 
              local outEnv::Env
              local outItem::Item

              (outItem, outEnv) = begin
                  local id::Absyn.Ident
                  local item::Item
                   #=  A builtin type.
                   =#
                @match inName begin
                  Absyn.IDENT(name = id)  => begin
                      item = lookupBuiltinType(id)
                    (item, NFSCodeEnv.emptyEnv)
                  end
                  
                  Absyn.QUALIFIED(name = "StateSelect", path = Absyn.IDENT(id))  => begin
                      (item, _) = lookupInClass(id, BUILTIN_STATESELECT_ENV)
                    (item, BUILTIN_STATESELECT_ENV)
                  end
                end
              end
               #=  Builtin type StateSelect. The only builtin type that can be qualified,
               =#
               #=  i.e. StateSelect.always.
               =#
          (outItem, outEnv)
        end

         #= Looks up a simple or qualified name in the environment and returns the
          environment item corresponding to the name, the path for the name and
          optionally the enclosing scope of the name if the name references a class.
          This function doesn't know what kind of thing the name references, so to get
          meaningful error messages you should use one of the lookup****Name below
          instead. =#
        function lookupName(inName::Absyn.Path, inEnv::Env, inLookupStrategy::LookupStrategy, inInfo::SourceInfo, inErrorType::Option{<:Error.Message}) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = begin
                  local id::Absyn.Ident
                  local item::Item
                  local path::Absyn.Path
                  local new_path::Absyn.Path
                  local env::Env
                  local name_str::String
                  local env_str::String
                  local error_id::Error.Message
                   #=  Builtin types.
                   =#
                @matchcontinue (inName, inEnv, inLookupStrategy, inInfo, inErrorType) begin
                  (_, _, LOOKUP_ANY(__), _, _)  => begin
                      (item, env) = lookupBuiltinName(inName)
                    (item, inName, env)
                  end
                  
                  (Absyn.IDENT(name = id), _, _, _, _)  => begin
                      (item, new_path, env) = lookupSimpleName(id, inEnv)
                    (item, new_path, env)
                  end
                  
                  (Absyn.QUALIFIED(name = id, path = path), _, _, _, _)  => begin
                      (item, new_path, env) = lookupSimpleName(id, inEnv)
                      (item, path, env) = lookupNameInItem(path, item, env)
                      path = joinPaths(new_path, path)
                    (item, path, env)
                  end
                  
                  (Absyn.FULLYQUALIFIED(path = path), _, _, _, _)  => begin
                      (item, path, env) = lookupFullyQualified(path, inEnv)
                    (item, path, env)
                  end
                  
                  (_, _, _, _, SOME(error_id))  => begin
                      name_str = AbsynUtil.pathString(inName)
                      env_str = NFSCodeEnv.getEnvName(inEnv)
                      Error.addSourceMessage(error_id, list(name_str, env_str), inInfo)
                    fail()
                  end
                end
              end
               #=  Simple name.
               =#
               #=  Qualified name.
               =#
               #=  Look up the first identifier.
               =#
               #=  Look up the rest of the name in the environment of the first
               =#
               #=  identifier.
               =#
          (outItem, outName, outEnv)
        end

         #= Joins two paths, like AbsynUtil.joinPaths but not with quite the same behaviour.
           If the second path is fully qualified it just returns the cref, because then
           it has been looked up through an import and already points directly at the
           class. If the first path is fully qualified it joins the paths, and return a
           fully qualified path. Otherwise it has the same behaviour as AbsynUtil.joinPaths,
           i.e. it simply joins the paths. =#
        function joinPaths(inPath1::Absyn.Path, inPath2::Absyn.Path) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local id::Absyn.Ident
                  local path::Absyn.Path
                   #=  The second path is fully qualified, return only that path.
                   =#
                @match (inPath1, inPath2) begin
                  (_, Absyn.FULLYQUALIFIED(__))  => begin
                    inPath2
                  end
                  
                  (Absyn.IDENT(name = id), _)  => begin
                    Absyn.QUALIFIED(id, inPath2)
                  end
                  
                  (Absyn.QUALIFIED(name = id, path = path), _)  => begin
                      path = joinPaths(path, inPath2)
                    Absyn.QUALIFIED(id, path)
                  end
                  
                  (Absyn.FULLYQUALIFIED(path = path), _)  => begin
                      path = joinPaths(path, inPath2)
                    AbsynUtil.makeFullyQualified(path)
                  end
                end
              end
               #=  Neither of the paths are fully qualified, just join them.
               =#
               #=  The first path is fully qualified, myMerge it with the second path and
               =#
               #=  return the result as a fully qualified path.
               =#
          outPath
        end

         #= Looks up a name, but doesn't print an error message if it fails. =#
        function lookupNameSilent(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = lookupName(inName, inEnv, LOOKUP_ANY(), inInfo, NONE())
          (outItem, outName, outEnv)
        end

        function lookupNameSilentNoBuiltin(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = lookupName(inName, inEnv, NO_BUILTIN_TYPES(), inInfo, NONE())
          (outItem, outName, outEnv)
        end

         #= Calls lookupName with the 'Class not found' error message. =#
        function lookupClassName(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = lookupName(inName, inEnv, LOOKUP_ANY(), inInfo, SOME(Error.LOOKUP_ERROR))
          (outItem, outName, outEnv)
        end

         #= Calls lookupName with the 'Baseclass not found' error message. =#
        function lookupBaseClassName(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = begin
                  local id::Absyn.Ident
                  local env::Env
                  local item::Item
                  local path::Absyn.Path
                   #=  Special case for the baseclass of a class extends. Should be looked up
                   =#
                   #=  among the inherited elements of the enclosing class.
                   =#
                @match (inName, inEnv, inInfo) begin
                  (Absyn.QUALIFIED(name = "$ce", path = path && Absyn.IDENT(name = id)), _ <| env, _)  => begin
                      (item, env) = lookupInheritedName(id, env)
                    (item, path, env)
                  end
                  
                  (Absyn.QUALIFIED(name = "$E"), _, _)  => begin
                      NFEnvExtends.printExtendsError(inName, inEnv, inInfo)
                    fail()
                  end
                  
                  _  => begin
                        (item, path, env) = lookupName(inName, inEnv, LOOKUP_ANY(), inInfo, SOME(Error.LOOKUP_BASECLASS_ERROR))
                      (item, path, env)
                  end
                end
              end
               #=  The extends was marked as erroneous in the qualifying phase, print an error.
               =#
               #=  Normal baseclass.
               =#
          (outItem, outName, outEnv)
        end

         #= Calls lookupName with the 'Variable not found' error message. =#
        function lookupVariableName(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = lookupName(inName, inEnv, NO_BUILTIN_TYPES(), inInfo, SOME(Error.LOOKUP_VARIABLE_ERROR))
          (outItem, outName, outEnv)
        end

         #= Calls lookupName with the 'Function not found' error message. =#
        function lookupFunctionName(inName::Absyn.Path, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.Path, Env} 
              local outEnv::Env
              local outName::Absyn.Path
              local outItem::Item

              (outItem, outName, outEnv) = lookupName(inName, inEnv, NO_BUILTIN_TYPES(), inInfo, SOME(Error.LOOKUP_FUNCTION_ERROR))
          (outItem, outName, outEnv)
        end

         #= Removes the entire environment prefix from the given component reference, or
          returns the unchanged reference. This is done because models might import
          local packages, for example:

            package P
              import myP = InsideP;

              package InsideP
                function f end f;
              end InsideP;

              constant c = InsideP.f();
            end P;

            package P2
              extends P;
            end P2;

          When P2 is instantiated all elements from P will be brought into P2's scope
          due to the extends. The binding of c will still point to P.InsideP.f though, so
          the lookup will try to instantiate P which might fail if P is a partial
          package or for other reasons. This is really a bug in Lookup (it shouldn't
          need to instantiate the whole package just to find a function), but to work
          around this problem for now this function will remove the environment prefix
          when InsideP.f is looked up in P, so that it resolves to InsideP.f and not
          P.InsideP.f. This allows P2 to find it in the local scope instead, since the
          InsideP package has been inherited from P. =#
        function crefStripEnvPrefix(inCref::Absyn.ComponentRef, inEnv::Env) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local env_path::Absyn.Path
                  local cref1::Absyn.ComponentRef
                  local cref2::Absyn.ComponentRef
                @matchcontinue (inCref, inEnv) begin
                  (_, _)  => begin
                      @match false = Flags.isSet(Flags.STRIP_PREFIX)
                    inCref
                  end
                  
                  (_, _)  => begin
                      @match false = Flags.isSet(Flags.SCODE_INST)
                      env_path = NFSCodeEnv.getEnvPath(inEnv)
                      cref1 = AbsynUtil.unqualifyCref(inCref)
                      cref2 = crefStripEnvPrefix2(cref1, env_path)
                      @match false = AbsynUtil.crefEqual(cref1, cref2)
                    cref2
                  end
                  
                  _  => begin
                      inCref
                  end
                end
              end
               #=  Don't do this if -d=newInst is used, it messed up the new
               =#
               #=  instantiation which handles this correctly.
               =#
               #=  try to strip as much as possible
               =#
               #=  check if we really did anything, fail if we did nothing!
               =#
          outCref
        end

        function crefStripEnvPrefix2(inCref::Absyn.ComponentRef, inEnvPath::Absyn.Path) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local id1::Absyn.Ident
                  local id2::Absyn.Ident
                  local cref::Absyn.ComponentRef
                  local env_path::Absyn.Path
                @matchcontinue (inCref, inEnvPath) begin
                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil(), componentRef = cref), Absyn.QUALIFIED(name = id2, path = env_path))  => begin
                      @match true = stringEqual(id1, id2)
                    crefStripEnvPrefix2(cref, env_path)
                  end
                  
                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil(), componentRef = cref), Absyn.IDENT(name = id2))  => begin
                      @match true = stringEqual(id1, id2)
                    cref
                  end
                  
                  (Absyn.CREF_QUAL(name = id1, subscripts =  nil()), Absyn.IDENT(name = id2))  => begin
                      @match false = stringEqual(id1, id2)
                    inCref
                  end
                end
              end
               #=  adrpo: leave it as stripped as you can if you can't match it above!
               =#
          outCref
        end

         #= Look up a component reference in the environment and returns it fully
          qualified. =#
        function lookupComponentRef(inCref::Absyn.ComponentRef, inEnv::Env, inInfo::SourceInfo) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local cref::Absyn.ComponentRef
                  local env::Env
                   #=  Special case for StateSelect, do nothing.
                   =#
                @matchcontinue (inCref, inEnv, inInfo) begin
                  (Absyn.CREF_QUAL(name = "StateSelect", subscripts =  nil(), componentRef = Absyn.CREF_IDENT(__)), _, _)  => begin
                    inCref
                  end
                  
                  (Absyn.WILD(__), _, _)  => begin
                    inCref
                  end
                  
                  (_, _, _)  => begin
                      cref = NFSCodeFlattenImports.flattenComponentRefSubs(inCref, inEnv, inInfo)
                      (cref, _) = lookupComponentRef2(cref, inEnv)
                      cref = crefStripEnvPrefix(cref, inEnv)
                    cref
                  end
                  
                  _  => begin
                      inCref
                  end
                end
              end
               #=  Wildcard.
               =#
               #=  All other component references.
               =#
               #=  First look up all subscripts, because all subscripts should be found
               =#
               #=  in the enclosing scope of the component reference.
               =#
               #=  Then look up the component reference itself.
               =#
          outCref
        end

         #= Helper function to lookupComponentRef. Does the actual look up of the
          component reference. =#
        function lookupComponentRef2(inCref::Absyn.ComponentRef, inEnv::Env) ::Tuple{Absyn.ComponentRef, Env} 
              local outEnv::Env
              local outCref::Absyn.ComponentRef

              (outCref, outEnv) = begin
                  local cref::Absyn.ComponentRef
                  local rest_cref::Absyn.ComponentRef
                  local name::Absyn.Ident
                  local subs::List{Absyn.Subscript}
                  local path::Absyn.Path
                  local new_path::Absyn.Path
                  local env::Env
                  local item::Item
                   #=  A simple name.
                   =#
                @match (inCref, inEnv) begin
                  (Absyn.CREF_IDENT(name, subs), _)  => begin
                      (_, path, env) = lookupSimpleName(name, inEnv)
                      cref = AbsynUtil.pathToCrefWithSubs(path, subs)
                    (cref, env)
                  end
                  
                  (Absyn.CREF_QUAL(name, subs, rest_cref), _)  => begin
                      (item, new_path, env) = lookupSimpleName(name, inEnv)
                      cref = AbsynUtil.pathToCrefWithSubs(new_path, subs)
                      (item, rest_cref) = lookupCrefInItem(rest_cref, item, env)
                      cref = joinCrefs(cref, rest_cref)
                    (cref, env)
                  end
                  
                  (Absyn.CREF_FULLYQUALIFIED(componentRef = cref), _)  => begin
                      cref = lookupCrefFullyQualified(cref, inEnv)
                      env = NFSCodeEnv.getEnvTopScope(inEnv)
                    (cref, env)
                  end
                end
              end
               #=  A qualified name.
               =#
               #=  Lookup the first identifier.
               =#
               #=  Lookup the rest of the cref in the enclosing scope of the first
               =#
               #=  identifier.
               =#
               #=  A fully qualified name.
               =#
          (outCref, outEnv)
        end

        function lookupCrefFullyQualified(inCref::Absyn.ComponentRef, inEnv::Env) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              local env::Env

              env = NFSCodeEnv.getEnvTopScope(inEnv)
              (_, outCref) = lookupCrefInPackage(inCref, inEnv)
              outCref = AbsynUtil.crefMakeFullyQualified(outCref)
          outCref
        end

         #= Joins two component references. If the second cref is fully qualified it just
          returns the cref, because then it has been looked up through an import and
          already points directly at the class. Otherwise it just calls AbsynUtil.joinCrefs. =#
        function joinCrefs(inCref1::Absyn.ComponentRef, inCref2::Absyn.ComponentRef) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                @match (inCref1, inCref2) begin
                  (_, Absyn.CREF_FULLYQUALIFIED(__))  => begin
                    inCref2
                  end
                  
                  _  => begin
                      AbsynUtil.joinCrefs(inCref1, inCref2)
                  end
                end
              end
          outCref
        end

         #= Looks up a type specification and returns the environment item and enclosing
          scopes of the type. =#
        function lookupTypeSpec(inTypeSpec::Absyn.TypeSpec, inEnv::Env, inInfo::SourceInfo) ::Tuple{Item, Absyn.TypeSpec, Env} 
              local outTypeEnv::Env
              local outTypeSpec::Absyn.TypeSpec
              local outItem::Item

              (outItem, outTypeSpec, outTypeEnv) = begin
                  local path::Absyn.Path
                  local newpath::Absyn.Path
                  local name::Absyn.Ident
                  local item::Item
                  local env::Env
                  local cls::SCode.Element
                  local ad::Option{Absyn.ArrayDim}
                   #=  A normal type.
                   =#
                @match (inTypeSpec, inEnv, inInfo) begin
                  (Absyn.TPATH(path, ad), _, _)  => begin
                      (item, newpath, env) = lookupClassName(path, inEnv, inInfo)
                    (item, Absyn.TPATH(newpath, ad), env)
                  end
                  
                  (Absyn.TCOMPLEX(path = Absyn.IDENT(name = name)), _, _)  => begin
                      cls = makeDummyMetaType(name)
                    (NFSCodeEnv.CLASS(cls, NFSCodeEnv.emptyEnv, NFSCodeEnv.BASIC_TYPE()), inTypeSpec, NFSCodeEnv.emptyEnv)
                  end
                end
              end
               #=  A MetaModelica type such as list or tuple.
               =#
          (outItem, outTypeSpec, outTypeEnv)
        end

        function makeDummyMetaType(inTypeName::String) ::SCode.Element 
              local outClass::SCode.Element

              outClass = SCode.CLASS(inTypeName, SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.PARTS(nil, nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, AbsynUtil.dummyInfo)
          outClass
        end

         #= Qualifies a path by looking up a path in the environment, and merging the
          resulting path with it's environment. =#
        function qualifyPath(inPath::Absyn.Path, inEnv::Env, inInfo::SourceInfo, inErrorType::Option{<:Error.Message}) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local id::Absyn.Ident
                  local path::Absyn.Path
                  local env::Env
                   #=  Never fully qualify builtin types.
                   =#
                @matchcontinue (inPath, inEnv, inInfo, inErrorType) begin
                  (Absyn.IDENT(name = id), _, _, _)  => begin
                      _ = lookupBuiltinType(id)
                    inPath
                  end
                  
                  (_, _, _, _)  => begin
                      (_, path, env) = lookupName(inPath, inEnv, NO_BUILTIN_TYPES(), inInfo, inErrorType)
                      path = NFSCodeEnv.myMergePathWithEnvPath(path, env)
                      path = AbsynUtil.makeFullyQualified(path)
                    path
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeLookup.qualifyPath failed on " + AbsynUtil.pathString(inPath) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
          outPath
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
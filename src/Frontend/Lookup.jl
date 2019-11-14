  module Lookup


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

        import ClassInf

        import DAE

        import FCore

        import HashTableStringToPath

        import InstTypes

        import SCode

        import Util

        import Types

        import BaseHashTable

        import Builtin

        import CrefForHashTable

        import Config

        # import Connect

        import ConnectionGraph

        import Debug

        import Error

        import Expression

        import ExpressionDump

        import Flags

        import FGraphUtil

        import FNode

        import Inst

        import InstExtends

        import InstFunction

        import InstUtil

        import InnerOuterTypes

        import ListUtil

        import Mod

        import Mutable

        import Prefix

        import PrefixUtil
        import SCodeUtil

        import Static

        import UnitAbsyn

        import SCodeDump

        import ErrorExt

        import ValuesUtil

        import Values

        MutableType = Mutable.MutableType


         #= /*   - Lookup functions

          These functions look up class and variable names in the environment.
          The names are supplied as a path, and if the path is qualified, a
          variable named as the first part of the path is searched for, and the
          name is looked for in it.

         */ =#

         #=  This function finds a specified type in the environment.
          If it finds a function instead, this will be implicitly instantiated
          and lookup will start over.
         =#
        function lookupType(inCache::FCore.Cache, inEnv::FCore.Graph #= environment to search in =#, inPath::Absyn.Path #= type to look for =#, msg::Option{<:SourceInfo} #= Messaage flag, SOME() outputs lookup error messages =#) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local env::FCore.Graph #= The environment the type was found in =#
              local t::DAE.Type #= the found type =#
              local cache::FCore.Cache

              (cache, t, env) = begin
                @match inPath begin
                  Absyn.IDENT(__)  => begin
                      (cache, t, env) = lookupTypeIdent(inCache, inEnv, inPath.name, msg)
                    (cache, t, env)
                  end

                  _  => begin
                        (cache, t, env) = lookupTypeQual(inCache, inEnv, inPath, msg)
                      (cache, t, env)
                  end
                end
              end
          (cache, t #= the found type =#, env #= The environment the type was found in =#)
        end

         #=  This function finds a specified type in the environment.
          If it finds a function instead, this will be implicitly instantiated
          and lookup will start over.
         =#
        function lookupTypeQual(inCache::FCore.Cache, inEnv::FCore.Graph #= environment to search in =#, inPath::Absyn.Path #= type to look for =#, msg::Option{<:SourceInfo} #= Messaage flag, SOME() outputs lookup error messages =#) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph #= The environment the type was found in =#
              local outType::DAE.Type #= the found type =#
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local t::DAE.Type
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local env_2::FCore.Graph
                  local path::Absyn.Path
                  local c::SCode.Element
                  local classname::String
                  local scope::String
                  local cache::FCore.Cache
                  local info::SourceInfo
                   #=  Special handling for Connections.isRoot
                   =#
                @matchcontinue (inCache, inEnv, inPath, msg) begin
                  (cache, env, Absyn.QUALIFIED("Connections", Absyn.IDENT("isRoot")), _)  => begin
                      t = DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_DEFAULT, inPath)
                    (cache, t, env)
                  end

                  (cache, env, Absyn.QUALIFIED("Connections", Absyn.IDENT("uniqueRootIndices")), _)  => begin
                      t = DAE.T_FUNCTION(list(DAE.FUNCARG("roots", DAE.T_ARRAY(DAE.T_ANYTYPE_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("nodes", DAE.T_ARRAY(DAE.T_ANYTYPE_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE()), DAE.FUNCARG("message", DAE.T_STRING_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_UNKNOWN())), DAE.FUNCTION_ATTRIBUTES_DEFAULT, inPath)
                    (cache, t, env)
                  end

                  (cache, env, path, _)  => begin
                      (cache, c, env_1) = lookupClass(cache, env, path)
                      (cache, t, env_2) = lookupType2(cache, env_1, c)
                    (cache, t, env_2)
                  end

                  (_, env, path, SOME(info))  => begin
                      classname = AbsynUtil.pathString(path)
                      classname = stringAppend(classname, " (its type) ")
                      scope = FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.LOOKUP_ERROR, list(classname, scope), info)
                    fail()
                  end
                end
              end
               #=  Special handling for Connections.uniqueRootIndices
               =#
               #=  Special classes (function, record, metarecord, external object)
               =#
               #=  Error for type not found
               =#
          (outCache, outType #= the found type =#, outEnv #= The environment the type was found in =#)
        end

         #=  This function finds a specified type in the environment.
          If it finds a function instead, this will be implicitly instantiated
          and lookup will start over.
         =#
        function lookupTypeIdent(inCache::FCore.Cache, inEnv::FCore.Graph #= environment to search in =#, ident::String #= type to look for =#, msg::Option{<:SourceInfo} #= Messaage flag, SOME() outputs lookup error messages =#) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph #= The environment the type was found in =#
              local outType::DAE.Type #= the found type =#
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local t::DAE.Type
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local env_2::FCore.Graph
                  local path::Absyn.Path
                  local c::SCode.Element
                  local classname::String
                  local scope::String
                  local cache::FCore.Cache
                  local info::SourceInfo
                   #=  Special handling for MultiBody 3.x rooted() operator
                   =#
                @matchcontinue (inCache, inEnv, ident, msg) begin
                  (cache, env, "rooted", _)  => begin
                      t = DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_ANYTYPE_DEFAULT, DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_BOOL_DEFAULT, DAE.FUNCTION_ATTRIBUTES_DEFAULT, Absyn.IDENT("rooted"))
                    (cache, t, env)
                  end

                  (cache, env, _, _)  => begin
                      (cache, t, env_1) = lookupTypeInEnv(cache, env, ident)
                    (cache, t, env_1)
                  end

                  (cache, env, _, _)  => begin
                      (cache, c, env_1) = lookupClassIdent(cache, env, ident)
                      (cache, t, env_2) = lookupType2(cache, env_1, c)
                    (cache, t, env_2)
                  end

                  (_, env, _, SOME(info))  => begin
                      classname = stringAppend(ident, " (its type) ")
                      scope = FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.LOOKUP_ERROR, list(classname, scope), info)
                    fail()
                  end
                end
              end
               #=  For simple names
               =#
               #=  Special classes (function, record, metarecord, external object)
               =#
               #=  Error for type not found
               =#
          (outCache, outType #= the found type =#, outEnv #= The environment the type was found in =#)
        end

         #=  This function handles the case when we looked up a class, but need to
        check if it is function, record, metarecord, etc.
         =#
        function lookupType2(inCache::FCore.Cache, inEnv::FCore.Graph #= environment to search in =#, inClass::SCode.Element #= the class lookupType found =#) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph #= The environment the type was found in =#
              local outType::DAE.Type #= the found type =#
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local t::DAE.Type
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local env_3::FCore.Graph
                  local path::Absyn.Path
                  local c::SCode.Element
                  local id::String
                  local cache::FCore.Cache
                  local r::SCode.Restriction
                  local types::List{DAE.Var}
                  local names::List{String}
                  local ci_state::ClassInf.SMNode
                  local encflag::SCode.Encapsulated
                  local mod::DAE.Mod
                   #=  Record constructors
                   =#
                @matchcontinue (inCache, inEnv, inClass) begin
                  (cache, env_1, c && SCode.CLASS(restriction = SCode.R_RECORD(_)))  => begin
                      (cache, env_1, t) = buildRecordType(cache, env_1, c)
                    (cache, t, env_1)
                  end

                  (cache, env_1, c && SCode.CLASS(name = id, encapsulatedPrefix = encflag, restriction = r && SCode.R_ENUMERATION(__)))  => begin
                      env_2 = FGraphUtil.openScope(env_1, encflag, id, SOME(FCore.CLASS_SCOPE()))
                      ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env_2))
                      mod = Mod.getClassModifier(env_1, id)
                      (cache, env_3, _, _, _, _, _, types, _, _, _, _) = Inst.instClassIn(cache, env_2, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, mod, Prefix.NOPRE(), ci_state, c, SCode.PUBLIC(), nil, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet, NONE())
                      (_, names) = SCodeUtil.getClassComponents(c)
                      Types.checkEnumDuplicateLiterals(names, c.info)
                      path = FGraphUtil.getGraphName(env_3)
                      t = DAE.T_ENUMERATION(NONE(), path, names, types, nil)
                      env_3 = FGraphUtil.mkTypeNode(env_3, id, t)
                    (cache, t, env_3)
                  end

                  (cache, env_1, SCode.CLASS(restriction = SCode.R_TYPE(__), classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(name = "Real")))))  => begin
                      t = DAE.T_REAL_DEFAULT
                    (cache, t, env_1)
                  end

                  (cache, env_1, SCode.CLASS(restriction = SCode.R_TYPE(__), classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(name = "Integer")))))  => begin
                      t = DAE.T_INTEGER_DEFAULT
                    (cache, t, env_1)
                  end

                  (cache, env_1, SCode.CLASS(restriction = SCode.R_TYPE(__), classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(name = "Boolean")))))  => begin
                      t = DAE.T_BOOL_DEFAULT
                    (cache, t, env_1)
                  end

                  (cache, env_1, SCode.CLASS(restriction = SCode.R_TYPE(__), classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = Absyn.IDENT(name = "String")))))  => begin
                      t = DAE.T_STRING_DEFAULT
                    (cache, t, env_1)
                  end

                  (cache, env_1, c && SCode.CLASS(restriction = SCode.R_METARECORD(__)))  => begin
                      (cache, env_2, t) = buildMetaRecordType(cache, env_1, c)
                    (cache, t, env_2)
                  end

                  (cache, env_1, c)  => begin
                      @match true = SCodeUtil.classIsExternalObject(c)
                      (cache, env_1, _, _, _, _, _, _, _, _) = Inst.instClass(cache, env_1, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), c, nil, false, InstTypes.TOP_CALL(), ConnectionGraph.EMPTY, DAE.emptySet)
                      @match SCode.CLASS(name = id) = c
                      (env_1, _) = FGraphUtil.stripLastScopeRef(env_1)
                      (cache, t, env_2) = lookupTypeInEnv(cache, env_1, id)
                    (cache, t, env_2)
                  end

                  (cache, env_1, c && SCode.CLASS(name = id, restriction = SCode.R_FUNCTION(_)))  => begin
                      (cache, env_2, _) = InstFunction.implicitFunctionTypeInstantiation(cache, env_1, InnerOuterTypes.emptyInstHierarchy, c)
                      (cache, t, env_3) = lookupTypeInEnv(cache, env_2, id)
                    (cache, t, env_3)
                  end
                end
              end
               #=  lookup of an enumeration type
               =#
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP TYPE ICD: \" + FGraphUtil.printGraphPathStr(env_1) + \" path:\" + AbsynUtil.pathString(path));
               =#
               #=  build names
               =#
               #=  generate the enumeration type
               =#
               #=  Real Type
               =#
               #=  Integer Type
               =#
               #=  Boolean Type
               =#
               #=  String Type
               =#
               #=  Metamodelica extension, Uniontypes
               =#
               #=  Classes that are external objects. Implicitly instantiate to get type
               =#
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP TYPE ICD: \" + FGraphUtil.printGraphPathStr(env_1) + \" path:\" + AbsynUtil.pathString(path));
               =#
               #=  If we find a class definition that is a function or external function
               =#
               #=  with the same name then we implicitly instantiate that function, look
               =#
               #=  up the type.
               =#
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP TYPE ICD: \" + FGraphUtil.printGraphPathStr(env_1) + \" path:\" + AbsynUtil.pathString(path));
               =#
          (outCache, outType #= the found type =#, outEnv #= The environment the type was found in =#)
        end

         #= Takes a list of paths to Uniontypes. Use this list to create a list of T_METARECORD.
        The function is guarded against recursive definitions by accumulating all paths it
        starts to traverse. =#
        function lookupMetarecordsRecursive(inCache::FCore.Cache, inEnv::FCore.Graph, inUniontypePaths::List{<:Absyn.Path}) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outMetarecordTypes::List{DAE.Type}
              local outCache::FCore.Cache

              (outCache, _, outMetarecordTypes) = lookupMetarecordsRecursive2(inCache, inEnv, inUniontypePaths, HashTableStringToPath.emptyHashTable(), nil)
          (outCache, outMetarecordTypes)
        end

         #= Takes a list of paths to Uniontypes. Use this list to create a list of T_METARECORD.
        The function is guarded against recursive definitions by accumulating all paths it
        starts to traverse. =#
        function lookupMetarecordsRecursive2(inCache::FCore.Cache, inEnv::FCore.Graph, inUniontypePaths::List{<:Absyn.Path}, inHt::HashTableStringToPath.HashTable, inAcc::List{<:DAE.Type}) ::Tuple{FCore.Cache, HashTableStringToPath.HashTable, List{DAE.Type}}
              local outMetarecordTypes::List{DAE.Type}
              local outHt::HashTableStringToPath.HashTable
              local outCache::FCore.Cache

              (outCache, outHt, outMetarecordTypes) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local first::Absyn.Path
                  local rest::List{Absyn.Path}
                  local ht::HashTableStringToPath.HashTable
                  local acc::List{DAE.Type}
                @match (inCache, inEnv, inUniontypePaths, inHt, inAcc) begin
                  (cache, _,  nil(), ht, acc)  => begin
                    (cache, ht, acc)
                  end

                  (cache, env, first <| rest, ht, acc)  => begin
                      (cache, ht, acc) = lookupMetarecordsRecursive3(cache, env, first, AbsynUtil.pathString(first), ht, acc)
                      (cache, ht, acc) = lookupMetarecordsRecursive2(cache, env, rest, ht, acc)
                    (cache, ht, acc)
                  end
                end
              end
          (outCache, outHt, outMetarecordTypes)
        end

         #= Takes a list of paths to Uniontypes. Use this list to create a list of T_METARECORD.
        The function is guarded against recursive definitions by accumulating all paths it
        starts to traverse. =#
        function lookupMetarecordsRecursive3(inCache::FCore.Cache, inEnv::FCore.Graph, path::Absyn.Path, str::String, inHt::HashTableStringToPath.HashTable, inAcc::List{<:DAE.Type}) ::Tuple{FCore.Cache, HashTableStringToPath.HashTable, List{DAE.Type}}
              local outMetarecordTypes::List{DAE.Type}
              local outHt::HashTableStringToPath.HashTable
              local outCache::FCore.Cache

              (outCache, outHt, outMetarecordTypes) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local uniontypePaths::List{Absyn.Path}
                  local uniontypeTypes::List{DAE.Type}
                  local ty::DAE.Type
                  local acc::List{DAE.Type}
                  local ht::HashTableStringToPath.HashTable
                @match (inCache, inEnv, path, str, inHt, inAcc) begin
                  (cache, _, _, _, ht, acc) where (BaseHashTable.hasKey(str, ht))  => begin
                    (cache, ht, acc)
                  end

                  (cache, env, _, _, ht, acc)  => begin
                      ht = BaseHashTable.add((str, path), ht)
                      (cache, ty, _) = lookupType(cache, env, path, SOME(AbsynUtil.dummyInfo))
                      acc = _cons(ty, acc)
                      uniontypeTypes = Types.getAllInnerTypesOfType(ty, Types.uniontypeFilter)
                      uniontypePaths = ListUtil.flatten(ListUtil.map(uniontypeTypes, Types.getUniontypePaths))
                      (cache, ht, acc) = lookupMetarecordsRecursive2(cache, env, uniontypePaths, ht, acc)
                    (cache, ht, acc)
                  end
                end
              end
          (outCache, outHt, outMetarecordTypes)
        end

         #= Tries to find a specified class in an environment =#
        function lookupClass(inCache::FCore.Cache, inEnv::FCore.Graph #= Where to look =#, inPath::Absyn.Path #= Path of the class to look for =#, inInfo::Option{<:SourceInfo} = NONE()) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph}
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv) = begin
                  local p::Absyn.Path
                  local id::Absyn.Path
                  local name::String
                  local className::String
                  local cenv::FGraphUtil.Graph
                   #= /*
                      case (_,_,_,_)
                        equation
                          print(\"CL: \" + AbsynUtil.pathString(inPath) + \" env: \" + FGraphUtil.printGraphPathStr(inEnv) + \" msg: \" + boolString(msg) + \"\\n\");
                        then
                          fail();*/ =#
                   #=  see if the first path ident is a component
                   =#
                   #=  we might have a component reference, i.e. world.gravityAcceleration
                   =#
                @matchcontinue (inCache, inEnv, inPath) begin
                  (_, _, Absyn.QUALIFIED(name, id))  => begin
                      ErrorExt.setCheckpoint("functionViaComponentRef2")
                      (outCache, _, _, _, _, _, _, cenv, _) = lookupVarIdent(inCache, inEnv, name, nil)
                      (outCache, outClass, outEnv) = lookupClass(outCache, cenv, id)
                      ErrorExt.rollBack("functionViaComponentRef2")
                    (outCache, outClass, outEnv)
                  end

                  (_, _, Absyn.QUALIFIED(_, _))  => begin
                      ErrorExt.rollBack("functionViaComponentRef2")
                    fail()
                  end

                  (_, _, _)  => begin
                      (outCache, outClass, outEnv, _) = lookupClass1(inCache, inEnv, inPath, nil, Mutable.create(false), inInfo)
                    (outCache, outClass, outEnv)
                  end
                end
              end
               #=  normal case
               =#
               #=  print(\"CLRET: \" + SCodeUtil.elementName(outClass) + \" outenv: \" + FGraphUtil.printGraphPathStr(outEnv) + \"\\n\");
               =#
               #=  print(\"Lookup C2: \" + \" outenv: \" + FGraphUtil.printGraphPathStr(outEnv) + \"\\n\");
               =#
          (outCache, outClass, outEnv)
        end

         #= Like lookupClass, but takes a String as ident for input (avoids Absyn.IDENT() creation) =#
        function lookupClassIdent(inCache::FCore.Cache, inEnv::FCore.Graph #= Where to look =#, ident::String, inInfo::Option{<:SourceInfo} = NONE()) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph}
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv) = lookupClassInEnv(inCache, inEnv, ident, nil, Mutable.create(false), inInfo)
          (outCache, outClass, outEnv)
        end

         #= help function to lookupClass, does all the work. =#
        function lookupClass1(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path #= The path of the class to lookup =#, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in previous frames of the environment =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph #= The environment in which the class was found (not the environment inside the class) =#
              local outClass::SCode.Element
              local outCache::FCore.Cache

              local errors::ModelicaInteger = Error.getNumErrorMessages()
              local info::SourceInfo

              try
                (outCache, outClass, outEnv, outPrevFrames) = lookupClass2(inCache, inEnv, inPath, inPrevFrames, inState, inInfo)
              catch
                if isSome(inInfo) && errors == Error.getNumErrorMessages()
                  Error.addSourceMessage(Error.LOOKUP_ERROR, list(AbsynUtil.pathString(inPath), FGraphUtil.printGraphPathStr(inEnv)), Util.getOption(inInfo))
                end
                fail()
              end
          (outCache, outClass, outEnv #= The environment in which the class was found (not the environment inside the class) =#, outPrevFrames)
        end

         #= help function to lookupClass, does all the work. =#
        function lookupClass2(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path #= The path of the class to lookup =#, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in previous frames of the environment =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph #= The environment in which the class was found (not the environment inside the class) =#
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local f::FCore.Node
                  local r::FCore.MMRef
                  local cache::FCore.Cache
                  local c::SCode.Element
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local fs::FCore.Graph
                  local prevFrames::FCore.Scope
                  local path::Absyn.Path
                  local p::Absyn.Path
                  local scope::Absyn.Path
                  local id::String
                  local pack::String
                  local optFrame::Option{FCore.MMRef}
                   #=  Fully qualified names are looked up in top scope. With previous frames remembered.
                   =#
                @match (inCache, inEnv, inPath, inPrevFrames) begin
                  (cache, env, Absyn.FULLYQUALIFIED(path),  nil())  => begin
                      @match _cons(r, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      Mutable.update(inState, true)
                      env = FGraphUtil.setScope(env, list(r))
                      (cache, c, env_1, prevFrames) = lookupClass2(cache, env, path, prevFrames, inState, inInfo)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, env, Absyn.QUALIFIED(name = pack, path = path), prevFrames)  => begin
                      (optFrame, prevFrames) = lookupPrevFrames(pack, prevFrames)
                      (cache, c, env_2, prevFrames) = lookupClassQualified(cache, env, pack, path, optFrame, prevFrames, inState, inInfo)
                    (cache, c, env_2, prevFrames)
                  end

                  (cache, env, Absyn.IDENT(name = id), prevFrames)  => begin
                      (cache, c, env_1, prevFrames) = lookupClassInEnv(cache, env, id, prevFrames, inState, inInfo)
                    (cache, c, env_1, prevFrames)
                  end
                end
              end
               #=  Qualified names are handled in a special function in order to avoid infinite recursion.
               =#
               #=  Simple names
               =#
               #= /*
                  case (cache,env,p,_,_,_)
                    equation
                      Debug.traceln(\"lookupClass failed \" + AbsynUtil.pathString(p) + \" \" + FGraphUtil.printGraphPathStr(env));
                    then fail();
                  */ =#
          (outCache, outClass, outEnv #= The environment in which the class was found (not the environment inside the class) =#, outPrevFrames)
        end

        function lookupClassQualified(inCache::FCore.Cache, inEnv::FCore.Graph, id::String, path::Absyn.Path, inOptFrame::Option{<:FCore.MMRef}, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in previous frames of the environment =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph #= The environment in which the class was found (not the environment inside the class) =#
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local c::SCode.Element
                  local scope::Absyn.Path
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local prevFrames::FCore.Scope
                  local frame::FCore.MMRef
                  local optFrame::Option{FCore.MMRef}
                   #=  Qualified names first identifier cached in previous frames
                   =#
                @match (inCache, inEnv, id, path, inOptFrame, inPrevFrames) begin
                  (cache, env, _, _, SOME(frame), prevFrames)  => begin
                      Mutable.update(inState, true)
                      env = FGraphUtil.pushScopeRef(env, frame)
                      (cache, c, env, prevFrames) = lookupClass2(cache, env, path, prevFrames, inState, inInfo)
                    (cache, c, env, prevFrames)
                  end

                  (cache, env, _, _, NONE(), _)  => begin
                      (cache, c, env, prevFrames) = lookupClassInEnv(cache, env, id, nil, inState, inInfo)
                      (optFrame, prevFrames) = lookupPrevFrames(id, prevFrames)
                      (cache, c, env, prevFrames) = lookupClassQualified2(cache, env, path, c, optFrame, prevFrames, inState, inInfo)
                    (cache, c, env, prevFrames)
                  end
                end
              end
               #=  Qualified names in package and non-package
               =#
          (outCache, outClass, outEnv #= The environment in which the class was found (not the environment inside the class) =#, outPrevFrames)
        end

        function lookupClassQualified2(inCache::FCore.Cache, inEnv::FCore.Graph, path::Absyn.Path, inC::SCode.Element, optFrame::Option{<:FCore.MMRef}, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in previous frames of the environment =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph #= The environment in which the class was found (not the environment inside the class) =#
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local prevFrames::FCore.Scope
                  local frame::FCore.MMRef
                  local restr::SCode.Restriction
                  local ci_state::ClassInf.SMNode
                  local encflag::SCode.Encapsulated
                  local id::String
                  local c::SCode.Element
                  local r::FCore.MMRef
                  local mod::DAE.Mod
                @matchcontinue (inCache, inEnv, path, inC, optFrame, inPrevFrames) begin
                  (cache, env, _, _, SOME(frame), prevFrames)  => begin
                      env = FGraphUtil.pushScopeRef(env, frame)
                      (cache, c, env, prevFrames) = lookupClass2(cache, env, path, prevFrames, inState, inInfo)
                    (cache, c, env, prevFrames)
                  end

                  (cache, env, _, SCode.CLASS(name = id), NONE(), _)  => begin
                      r = FNode.child(FGraphUtil.lastScopeRef(env), id)
                      @match FCore.CL(status = FCore.CLS_INSTANCE(_)) = FNode.refData(r)
                      (cache, env) = Inst.getCachedInstance(cache, env, id, r)
                      (cache, c, env, prevFrames) = lookupClass2(cache, env, path, nil, inState, inInfo)
                    (cache, c, env, prevFrames)
                  end

                  (cache, env, _, SCode.CLASS(name = id, encapsulatedPrefix = encflag, restriction = restr), NONE(), _)  => begin
                      env = FGraphUtil.openScope(env, encflag, id, FGraphUtil.restrictionToScopeType(restr))
                      ci_state = ClassInf.start(restr, FGraphUtil.getGraphName(env))
                      mod = Mod.getClassModifier(inEnv, id)
                      (cache, env, _, _, _) = Inst.partialInstClassIn(cache, env, InnerOuterTypes.emptyInstHierarchy, mod, Prefix.NOPRE(), ci_state, inC, SCode.PUBLIC(), nil, 0)
                      checkPartialScope(env, inEnv, cache, inInfo)
                      (cache, c, env, prevFrames) = lookupClass2(cache, env, path, nil, inState, inInfo)
                    (cache, c, env, prevFrames)
                  end
                end
              end
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP CLASS QUALIFIED FRAME: \" + FGraphUtil.printGraphPathStr(env) + \" path: \" + AbsynUtil.pathString(path) + \" class: \" + SCodeDump.shortElementStr(c));
               =#
               #=  class is an instance of a component
               =#
               #=  fetch the env
               =#
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP CLASS QUALIFIED PARTIALICD: \" + FGraphUtil.printGraphPathStr(env) + \" path: \" + AbsynUtil.pathString(path) + \" class: \" + SCodeDump.shortElementStr(c));
               =#
          (outCache, outClass, outEnv #= The environment in which the class was found (not the environment inside the class) =#, outPrevFrames)
        end

        function checkPartialScope(inEnv::FCore.Graph, inParentEnv::FCore.Graph, inCache::FCore.Cache, inInfo::Option{<:SourceInfo})
              local el::SCode.Element
              local pre::Prefix.PrefixType
              local name::String
              local pre_str::String
              local cc_str::String
              local cls_info::SourceInfo
              local pre_info::SourceInfo
              local info::SourceInfo

              if isSome(inInfo) && FGraphUtil.isPartialScope(inEnv) && Config.languageStandardAtLeast(Config.LanguageStandard.S3_2)
                @match FCore.N(data = FCore.CL(e = el, pre = pre)) = FNode.fromRef(FGraphUtil.lastScopeRef(inEnv))
                name = SCodeUtil.elementName(el)
                if FGraphUtil.graphPrefixOf(inParentEnv, inEnv) && ! PrefixUtil.isNoPrefix(pre)
                  pre_str = PrefixUtil.printPrefixStr(pre)
                  cls_info = SCodeUtil.elementInfo(el)
                  pre_info = PrefixUtil.getPrefixInfo(pre)
                  cc_str = getConstrainingClass(el, FGraphUtil.stripLastScopeRef(inEnv), inCache)
                  Error.addMultiSourceMessage(Error.USE_OF_PARTIAL_CLASS, list(pre_str, name, cc_str), list(cls_info, pre_info))
                  fail()
                else
                  @match SOME(info) = inInfo
                  if ! Config.getGraphicsExpMode()
                    Error.addSourceMessage(Error.LOOKUP_IN_PARTIAL_CLASS, list(name), info)
                  end
                end
              end
               #=  We should fail here, but the MSL 3.2.1 contains such errors. So just
               =#
               #=  print an error and continue anyway for now.
               =#
        end

        function getConstrainingClass(inClass::SCode.Element, inEnv::FCore.Graph, inCache::FCore.Cache) ::String
              local outPath::String

              outPath = begin
                  local cc_path::Absyn.Path
                  local ts::Absyn.TypeSpec
                  local el::SCode.Element
                  local env::FCore.Graph
                @matchcontinue inClass begin
                  SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(cc = SOME(SCode.CONSTRAINCLASS(constrainingClass = cc_path)))))  => begin
                    AbsynUtil.pathString(cc_path)
                  end

                  SCode.CLASS(classDef = SCode.DERIVED(typeSpec = ts))  => begin
                      (_, el, env) = lookupClass(inCache, inEnv, AbsynUtil.typeSpecPath(ts))
                    getConstrainingClass(el, env, inCache)
                  end

                  _  => begin
                      FGraphUtil.printGraphPathStr(inEnv) + "." + SCodeUtil.elementName(inClass)
                  end
                end
              end
          outPath
        end

        function lookupPrevFrames(id::String, inPrevFrames::FCore.Scope) ::Tuple{Option{FCore.MMRef}, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outFrame::Option{FCore.MMRef}

              (outFrame, outPrevFrames) = begin
                  local sid::String
                  local prevFrames::FCore.Scope
                  local ref::FCore.MMRef
                @matchcontinue (id, inPrevFrames) begin
                  (_, ref <| prevFrames)  => begin
                      @match false = FNode.isRefTop(ref)
                      sid = FNode.refName(ref)
                      @match true = id == sid
                    (SOME(ref), prevFrames)
                  end

                  _  => begin
                      (NONE(), nil)
                  end
                end
              end
          (outFrame, outPrevFrames)
        end

         #= author: PA
          Looking up variables (constants) imported using qualified imports,
          i.e. import Modelica.Constants.PI; =#
        function lookupQualifiedImportedVarInFrame(inImports::List{<:Absyn.Import}, ident::SCode.Ident) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::String
                  local rest::List{Absyn.Import}
                  local path::Absyn.Path
                   #=  For imported simple name, e.g. A, not possible to assert sub-path package
                   =#
                @matchcontinue (inImports, ident) begin
                  (Absyn.QUAL_IMPORT(path = path) <| _, _)  => begin
                      id = AbsynUtil.pathLastIdent(path)
                      @match true = id == ident
                    CrefForHashTable.pathToCref(path)
                  end

                  (Absyn.NAMED_IMPORT(name = id, path = path) <| _, _)  => begin
                      @match true = id == ident
                    CrefForHashTable.pathToCref(path)
                  end

                  (_ <| rest, _)  => begin
                    lookupQualifiedImportedVarInFrame(rest, ident)
                  end
                end
              end
               #=  Named imports, e.g. import A = B.C;
               =#
               #=  Check next frame.
               =#
          outCref
        end

         #= Helper function for lookup_unqualified_imported_var_in_frame. Returns
          true if there are unqualified imports that matches a sought constant. =#
        function moreLookupUnqualifiedImportedVarInFrame(inCache::FCore.Cache, inImports::List{<:Absyn.Import}, inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{FCore.Cache, Bool}
              local outBoolean::Bool
              local outCache::FCore.Cache

              (outCache, outBoolean) = begin
                  local f::FCore.MMRef
                  local ident::String
                  local res::Bool
                  local env::FCore.Graph
                  local prevFrames::FCore.Scope
                  local rest::List{Absyn.Import}
                  local cache::FCore.Cache
                  local cref::DAE.ComponentRef
                  local path::Absyn.Path
                @matchcontinue (inCache, inImports, inEnv, inIdent) begin
                  (cache, Absyn.UNQUAL_IMPORT(path = path) <| _, env, ident)  => begin
                      @match _cons(f, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      cref = CrefForHashTable.pathToCref(path)
                      cref = CrefForHashTable.crefPrependIdent(cref, ident, nil, DAE.T_UNKNOWN_DEFAULT)
                      env = FGraphUtil.setScope(env, list(f))
                      (cache, _, _, _, _, _, _, _, _) = lookupVarInPackages(cache, env, cref, prevFrames, Mutable.create(false))
                    (cache, true)
                  end

                  (cache, _ <| rest, env, ident)  => begin
                      (cache, res) = moreLookupUnqualifiedImportedVarInFrame(cache, rest, env, ident)
                    (cache, res)
                  end

                  (cache,  nil(), _, _)  => begin
                    (cache, false)
                  end
                end
              end
               #=  look into the parent scope
               =#
               #=  we reached the end, no more lookup
               =#
          (outCache, outBoolean)
        end

         #= Find a variable from an unqualified import locally in a frame =#
        function lookupUnqualifiedImportedVarInFrame(inCache::FCore.Cache, inImports::List{<:Absyn.Import}, inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{FCore.Cache, FCore.Graph, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, Bool, InstTypes.SplicedExpData, FCore.Graph, String}
              local name::String
              local outComponentEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData
              local outBoolean::Bool
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outClassEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange, outBoolean, splicedExpData, outComponentEnv, name) = begin
                  local f::FCore.MMRef
                  local cref::DAE.ComponentRef
                  local ident::String
                  local more::Bool
                  local unique::Bool
                  local env::FCore.Graph
                  local classEnv::FCore.Graph
                  local componentEnv::FCore.Graph
                  local env2::FCore.Graph
                  local prevFrames::FCore.Scope
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local bind::DAE.Binding
                  local rest::List{Absyn.Import}
                  local cache::FCore.Cache
                  local path::Absyn.Path
                  local cnstForRange::Option{DAE.Const}
                   #=  unique
                   =#
                @matchcontinue (inCache, inImports, inEnv, inIdent) begin
                  (cache, Absyn.UNQUAL_IMPORT(path = path) <| rest, env, ident)  => begin
                      @match _cons(f, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      cref = CrefForHashTable.pathToCref(path)
                      cref = CrefForHashTable.crefPrependIdent(cref, ident, nil, DAE.T_UNKNOWN_DEFAULT)
                      env2 = FGraphUtil.setScope(env, list(f))
                      (cache, classEnv, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env2, cref, prevFrames, Mutable.create(false))
                      (cache, more) = moreLookupUnqualifiedImportedVarInFrame(cache, rest, env, ident)
                      unique = boolNot(more)
                    (cache, classEnv, attr, ty, bind, cnstForRange, unique, splicedExpData, componentEnv, name)
                  end

                  (cache, _ <| rest, env, ident)  => begin
                      (cache, classEnv, attr, ty, bind, cnstForRange, unique, splicedExpData, componentEnv, name) = lookupUnqualifiedImportedVarInFrame(cache, rest, env, ident)
                    (cache, classEnv, attr, ty, bind, cnstForRange, unique, splicedExpData, componentEnv, name)
                  end
                end
              end
               #=  search in the parent scopes
               =#
          (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, outBoolean, splicedExpData, outComponentEnv, name)
        end

         #= Helper function to lookupQualifiedImportedClassInEnv. =#
        function lookupQualifiedImportedClassInFrame(inCache::FCore.Cache, inImport::List{<:Absyn.Import}, inEnv::FCore.Graph, inIdent::SCode.Ident, inState::MutableType #= {<:Bool} =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local fr::FCore.Node
                  local r::FCore.MMRef
                  local c::SCode.Element
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local prevFrames::FCore.Scope
                  local id::String
                  local ident::String
                  local rest::List{Absyn.Import}
                  local path::Absyn.Path
                  local cache::FCore.Cache
                @matchcontinue (inCache, inImport, inEnv, inIdent, inState) begin
                  (cache, Absyn.QUAL_IMPORT(path = Absyn.IDENT(name = id)) <| _, env, ident, _)  => begin
                      @match true = id == ident #= For imported paths A, not possible to assert sub-path package =#
                      Mutable.update(inState, true)
                      @match _cons(r, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      env = FGraphUtil.setScope(env, list(r))
                      (cache, c, env_1, prevFrames) = lookupClassInEnv(cache, env, id, prevFrames, Mutable.create(false), inInfo)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, Absyn.QUAL_IMPORT(path = path) <| _, env, ident, _)  => begin
                      id = AbsynUtil.pathLastIdent(path) #= For imported path A.B.C, assert A.B is package =#
                      @match true = id == ident
                      Mutable.update(inState, true)
                      @match _cons(r, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      env = FGraphUtil.setScope(env, list(r))
                      (cache, c, env_1, prevFrames) = lookupClass2(cache, env, path, prevFrames, Mutable.create(false), inInfo)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, Absyn.NAMED_IMPORT(name = id, path = path) <| _, env, ident, _)  => begin
                      @match true = id == ident #= Named imports =#
                      Mutable.update(inState, true)
                      @match _cons(r, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      env = FGraphUtil.setScope(env, list(r))
                      (cache, c, env_1, prevFrames) = lookupClass2(cache, env, path, prevFrames, Mutable.create(false), inInfo)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, _ <| rest, env, ident, _)  => begin
                      (cache, c, env_1, prevFrames) = lookupQualifiedImportedClassInFrame(cache, rest, env, ident, inState, inInfo)
                    (cache, c, env_1, prevFrames)
                  end
                end
              end
               #=  strippath = AbsynUtil.stripLast(path);
               =#
               #=  (cache,c2,env_1,_) = lookupClass2(cache,{fr},strippath,prevFrames,Mutable.create(false),true);
               =#
               #=  strippath = AbsynUtil.stripLast(path);
               =#
               #=  Debug.traceln(\"named import \" + id + \" is \" + AbsynUtil.pathString(path));
               =#
               #=  (cache,c2,env_1,prevFrames) = lookupClass2(cache,{fr},strippath,prevFrames,Mutable.create(false),true);
               =#
          (outCache, outClass, outEnv, outPrevFrames)
        end

         #= Helper function for lookupUnqualifiedImportedClassInFrame =#
        function moreLookupUnqualifiedImportedClassInFrame(inCache::FCore.Cache, inImports::List{<:Absyn.Import}, inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{FCore.Cache, Bool}
              local outBoolean::Bool
              local outCache::FCore.Cache

              (outCache, outBoolean) = begin
                  local fr::FCore.Node
                  local f::FCore.Node
                  local c::SCode.Element
                  local id::String
                  local ident::String
                  local encflag::SCode.Encapsulated
                  local res::Bool
                  local restr::SCode.Restriction
                  local env_1::FCore.Graph
                  local env2::FCore.Graph
                  local env::FCore.Graph
                  local ci_state::ClassInf.SMNode
                  local path::Absyn.Path
                  local firstIdent::Absyn.Ident
                  local rest::List{Absyn.Import}
                  local cache::FCore.Cache
                  local r::FCore.MMRef
                  local mod::DAE.Mod
                   #=  Not found, instantiate
                   =#
                @matchcontinue (inCache, inImports, inEnv, inIdent) begin
                  (cache, Absyn.UNQUAL_IMPORT(path = path) <| _, env, ident)  => begin
                      env = FGraphUtil.topScope(env)
                      @match (cache, (@match SCode.CLASS(name = id, encapsulatedPrefix = encflag, restriction = restr) = c), env_1) = lookupClass(cache, env, path)
                      env2 = FGraphUtil.openScope(env_1, encflag, id, FGraphUtil.restrictionToScopeType(restr))
                      ci_state = ClassInf.start(restr, FGraphUtil.getGraphName(env2))
                      mod = Mod.getClassModifier(env_1, id)
                      (cache, env, _, _, _) = Inst.partialInstClassIn(cache, env2, InnerOuterTypes.emptyInstHierarchy, mod, Prefix.NOPRE(), ci_state, c, SCode.PUBLIC(), nil, 0)
                      r = FGraphUtil.lastScopeRef(env)
                      env = FGraphUtil.setScope(env, list(r))
                      (cache, _, _) = lookupClass(cache, env, Absyn.IDENT(ident))
                    (cache, true)
                  end

                  (cache, _ <| rest, env, ident)  => begin
                      (cache, res) = moreLookupUnqualifiedImportedClassInFrame(cache, rest, env, ident)
                    (cache, res)
                  end

                  (cache,  nil(), _, _)  => begin
                    (cache, false)
                  end
                end
              end
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP MORE UNQUALIFIED IMPORTED ICD: \" + FGraphUtil.printGraphPathStr(env) + \".\" + ident);
               =#
               #=  Look in the parent scope
               =#
          (outCache, outBoolean)
        end

         #= Finds a class from an unqualified import locally in a frame =#
        function lookupUnqualifiedImportedClassInFrame(inCache::FCore.Cache, inImports::List{<:Absyn.Import}, inEnv::FCore.Graph, inIdent::SCode.Ident, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope, Bool}
              local outBoolean::Bool
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames, outBoolean) = begin
                  local fr::FCore.Node
                  local r::FCore.MMRef
                  local c::SCode.Element
                  local c_1::SCode.Element
                  local id::String
                  local ident::String
                  local encflag::SCode.Encapsulated
                  local more::Bool
                  local unique::Bool
                  local restr::SCode.Restriction
                  local env_1::FCore.Graph
                  local env2::FCore.Graph
                  local env::FCore.Graph
                  local env3::FCore.Graph
                  local prevFrames::FCore.Scope
                  local ci_state::ClassInf.SMNode
                  local cistate1::ClassInf.SMNode
                  local path::Absyn.Path
                  local rest::List{Absyn.Import}
                  local cache::FCore.Cache
                  local firstIdent::Absyn.Ident
                  local mod::DAE.Mod
                   #=  Not in cache, instantiate, unique
                   =#
                @matchcontinue (inCache, inImports, inEnv, inIdent) begin
                  (cache, Absyn.UNQUAL_IMPORT(path = path) <| rest, env, ident)  => begin
                      @match _cons(r, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                      env3 = FGraphUtil.setScope(env, list(r))
                      @match (cache, (@match SCode.CLASS(name = id, encapsulatedPrefix = encflag, restriction = restr) = c), env_1, prevFrames) = lookupClass2(cache, env3, path, prevFrames, Mutable.create(false), inInfo)
                      env2 = FGraphUtil.openScope(env_1, encflag, id, FGraphUtil.restrictionToScopeType(restr))
                      ci_state = ClassInf.start(restr, FGraphUtil.getGraphName(env2))
                      mod = Mod.getClassModifier(env_1, id)
                      (cache, env2, _, _, _) = Inst.partialInstClassIn(cache, env2, InnerOuterTypes.emptyInstHierarchy, mod, Prefix.NOPRE(), ci_state, c, SCode.PUBLIC(), nil, 0)
                      (cache, c_1, env2, prevFrames) = lookupClassInEnv(cache, env2, ident, prevFrames, Mutable.create(true), inInfo) #= Restrict import to the imported scope only, not its parents... =#
                      (cache, more) = moreLookupUnqualifiedImportedClassInFrame(cache, rest, env, ident)
                      unique = boolNot(more)
                    (cache, c_1, env2, prevFrames, unique)
                  end

                  (cache, _ <| rest, env, ident)  => begin
                      (cache, c, env_1, prevFrames, unique) = lookupUnqualifiedImportedClassInFrame(cache, rest, env, ident, inInfo)
                    (cache, c, env_1, prevFrames, unique)
                  end
                end
              end
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP UNQUALIFIED IMPORTED ICD: \" + FGraphUtil.printGraphPathStr(env) + \".\" + ident);
               =#
               #=  Restrict import to the imported scope only, not its parents, thus {f} below
               =#
               #=  Look in the parent scope
               =#
          (outCache, outClass, outEnv, outPrevFrames, outBoolean)
        end

         #= Searches for a record constructor implicitly defined by a record class. =#
        function lookupRecordConstructorClass(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph}
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv) = begin
                  local c::SCode.Element
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local path::Absyn.Path
                  local name::String
                  local cache::FCore.Cache
                @match (inCache, inEnv, inPath) begin
                  (cache, env, path)  => begin
                      (cache, c, env_1) = lookupClass(cache, env, path)
                      @match SCode.CLASS(restriction = SCode.R_RECORD(_)) = c
                      (cache, _, c) = buildRecordConstructorClass(cache, env_1, c)
                    (cache, c, env_1)
                  end
                end
              end
          (outCache, outClass, outEnv)
        end

         #= Simplified lookup of connector references. The lookup will stop if it finds a
           deleted component, so if status is VAR_DELETED() then attr and ty will belong
           to the deleted component instead of the looked for component. =#
        function lookupConnectorVar(env::FCore.Graph, cr::DAE.ComponentRef, firstId::Bool = true) ::Tuple{DAE.Attributes, DAE.Type, FCore.Status, Bool}
              local isExpandable::Bool = false
              local status::FCore.Status
              local ty::DAE.Type
              local attr::DAE.Attributes

              local comp_env::FCore.Graph
              local parent_attr::DAE.Attributes

              (attr, ty, status) = begin
                @match cr begin
                  DAE.CREF_IDENT(__)  => begin
                      @match (DAE.TYPES_VAR(attributes = attr, ty = ty), status, _) = lookupConnectorVar2(env, cr.ident)
                      ty = checkSubscripts(ty, cr.subscriptLst)
                    (attr, ty, status)
                  end

                  DAE.CREF_QUAL(__)  => begin
                      @match (DAE.TYPES_VAR(attributes = parent_attr, ty = ty), status, comp_env) = lookupConnectorVar2(env, cr.ident)
                      if FCore.isDeletedComp(status)
                        attr = parent_attr
                      else
                        try
                          (attr, ty, status, isExpandable) = lookupConnectorVar(comp_env, cr.componentRef, false)
                        catch
                          if Types.isExpandableConnector(ty)
                            attr = parent_attr
                            isExpandable = true
                          else
                            fail()
                          end
                        end
                        attr = DAEUtil.setAttrVariability(attr, SCodeUtil.variabilityOr(DAEUtil.getAttrVariability(attr), DAEUtil.getAttrVariability(parent_attr)))
                        if firstId
                          attr = DAEUtil.setAttrInnerOuter(attr, DAEUtil.getAttrInnerOuter(parent_attr))
                        end
                      end
                       #=  Stop if we find a deleted component.
                       =#
                       #=  Propagate variability.
                       =#
                       #=  Use the inner/outer from the first identifier.
                       =#
                    (attr, ty, status)
                  end
                end
              end
          (attr, ty, status, isExpandable)
        end

         #= Helper function to lookupConnectorVar. =#
        function lookupConnectorVar2(env::FCore.Graph, name::String) ::Tuple{DAE.Var, FCore.Status, FCore.Graph}
              local compEnv::FCore.Graph
              local status::FCore.Status
              local var::DAE.Var

              local scope::FCore.Scope
              local ht::FCore.Children

              @match FCore.G(scope = scope) = env
               #=  Connectors are not allowed to be constant, so we don't need to look outside
               =#
               #=  the local scope. But we do need to check outside implicit scopes, e.g.
               =#
               #=  for-scopes.
               =#
              for r in scope
                ht = FNode.children(FNode.fromRef(r))
                try
                  (var, _, _, status, compEnv) = lookupVar2(ht, name, env)
                  return (var, status, compEnv)
                catch
                  @match true = FNode.isImplicitRefName(r)
                end
              end
               #=  Continue to the next scope only if the current scope is implicit.
               =#
              fail()
          (var, status, compEnv)
        end

         #= LS: when looking up qualified component reference, lookupVar only
           checks variables when looking for the prefix, i.e. for Constants.PI
           where Constants is a package and is implicitly instantiated, PI is not
           found since Constants is not a variable (it is a type and/or class).

           1) One option is to make it a variable and put it in the global frame.
           2) Another option is to add a lookup rule that also looks in types.

           Now implicitly instantiated packages exists both as a class and as a
           type (see implicit_instantiation in Inst.mo). Is this correct?

           lookupVar is modified to implement 2. Is this correct?

           old lookupVar is changed to lookupVarInternal and a new lookupVar
           is written, that first tests the old lookupVar, and if not found
           looks in the types

           function: lookupVar

           This function tries to finds a variable in the environment

           Arg1: The environment to search in
           Arg2: The variable to search for. =#
        function lookupVar(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, FCore.Graph, String}
              local name::String #= so the FQ path can be constructed =#
              local outComponentEnv::FCore.Graph #= only used for package constants =#
              local outClassEnv::FCore.Graph #= only used for package constants =#
              local outSplicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, outSplicedExpData, outClassEnv, outComponentEnv, name) = begin
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local classEnv::FCore.Graph
                  local cref::DAE.ComponentRef
                  local cache::FCore.Cache
                  local splicedExpData::InstTypes.SplicedExpData
                  local cnstForRange::Option{DAE.Const}
                   #= /*/ debugging
                      case (cache,env,cref)
                        equation
                          print(\"CO: \" + CrefForHashTable.printComponentRefStr(cref) + \" env: \" + FGraphUtil.printGraphPathStr(env) + \"\\n\");
                        then
                          fail();*/ =#
                   #=  try the old lookupVarInternal
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef) begin
                  (cache, env, cref)  => begin
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name) = lookupVarInternal(cache, env, cref, InstTypes.SEARCH_ALSO_BUILTIN())
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name)
                  end

                  (cache, env, cref)  => begin
                      (cache, classEnv, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env, cref, nil, Mutable.create(false))
                      checkPackageVariableConstant(env, classEnv, componentEnv, attr, ty, cref)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name)
                  end

                  (cache, env, _) where (Config.getGraphicsExpMode())  => begin
                    (cache, DAE.dummyAttrConst, DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE(), InstTypes.SPLICEDEXPDATA(NONE(), DAE.T_UNKNOWN_DEFAULT), env, env, "#varNotFound#")
                  end
                end
              end
               #=  then look in classes (implicitly instantiated packages)
               =#
               #=  optional Expression.exp to return
               =#
               #= /*/ fail if we couldn't find it
                  case (_,env,cref)
                    equation
                      fprintln(Flags.FAILTRACE,  \"- Lookup.lookupVar failed:\\n\" +
                        CrefForHashTable.printComponentRefStr(cref) + \" in:\\n\" +
                        FGraphUtil.printGraphPathStr(env));
                    then fail();*/ =#
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, outSplicedExpData, outClassEnv #= only used for package constants =#, outComponentEnv #= only used for package constants =#, name #= so the FQ path can be constructed =#)
        end

         #= Like lookupVar, but takes only an ident+subscript. =#
        function lookupVarIdent(inCache::FCore.Cache, inEnv::FCore.Graph, ident::String, ss::List{<:DAE.Subscript} = nil) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, FCore.Graph, String}
              local name::String #= so the FQ path can be constructed =#
              local outComponentEnv::FCore.Graph #= only used for package constants =#
              local outClassEnv::FCore.Graph #= only used for package constants =#
              local outSplicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, outSplicedExpData, outClassEnv, outComponentEnv, name) = begin
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local classEnv::FCore.Graph
                  local cref::DAE.ComponentRef
                  local cache::FCore.Cache
                  local splicedExpData::InstTypes.SplicedExpData
                  local cnstForRange::Option{DAE.Const}
                   #=  try the old lookupVarInternal
                   =#
                @matchcontinue (inCache, inEnv) begin
                  (cache, env)  => begin
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name) = lookupVarInternalIdent(cache, env, ident, ss, InstTypes.SEARCH_ALSO_BUILTIN())
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name)
                  end

                  (cache, env)  => begin
                      cref = CrefForHashTable.makeCrefIdent(ident, DAE.T_UNKNOWN_DEFAULT, ss)
                      (cache, classEnv, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env, cref, nil, Mutable.create(false))
                      checkPackageVariableConstant(env, classEnv, componentEnv, attr, ty, cref)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, classEnv, componentEnv, name)
                  end
                end
              end
               #=  then look in classes (implicitly instantiated packages)
               =#
               #=  TODO: Skip makeCrefIdent by rewriting lookupVarInPackages
               =#
               #=  optional Expression.exp to return
               =#
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, outSplicedExpData, outClassEnv #= only used for package constants =#, outComponentEnv #= only used for package constants =#, name #= so the FQ path can be constructed =#)
        end

         #=
        Variables in packages must be constant. This function produces an error message and fails
        if variable is not constant. =#
        function checkPackageVariableConstant(parentEnv::FCore.Graph, classEnv::FCore.Graph, componentEnv::FCore.Graph, attr::DAE.Attributes, tp::DAE.Type, cref::DAE.ComponentRef)
              _ = begin
                  local s1::String
                  local s2::String
                  local cl::SCode.Element
                   #=  do not fail if is a constant
                   =#
                @matchcontinue (parentEnv, classEnv, componentEnv, attr, tp, cref) begin
                  (_, _, _, DAE.ATTR(variability = SCode.CONST(__)), _, _)  => begin
                    ()
                  end

                  _  => begin
                        s1 = CrefForHashTable.printComponentRefStr(cref)
                        s2 = FGraphUtil.printGraphPathStr(classEnv)
                        Error.addMessage(Error.PACKAGE_VARIABLE_NOT_CONSTANT, list(s1, s2))
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Lookup.checkPackageVariableConstant failed: " + s1 + " in " + s2)
                      fail()
                  end
                end
              end
               #= /*/ do not fail if is a parameter in non-package
                  case (_, _, _,DAE.ATTR(variability = SCode.PARAM()),_,_)
                    equation
                      FCore.CL(e = cl) = FNode.refData(FGraphUtil.lastScopeRef(classEnv));
                      false = SCodeUtil.isPackage(cl);
                       print(\"cref:  \" + CrefForHashTable.printComponentRefStr(cref) + \"\\nprenv: \" + FGraphUtil.getGraphNameStr(parentEnv) + \"\\nclenv: \" + FGraphUtil.getGraphNameStr(classEnv) + \"\\ncoenv: \" + FGraphUtil.getGraphNameStr(componentEnv) + \"\\n\");
                    then
                      ();*/ =#
               #=  fail if is not a constant
               =#
        end

         #= Helper function to lookupVar. Searches the frames for variables. =#
        function lookupVarInternal(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, searchStrategy::InstTypes.SearchStrategy #= if SEARCH_LOCAL_ONLY it won't search in the builtin scope =#) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, FCore.Graph, String}
              local name::String
              local outComponentEnv::FCore.Graph #= the component environment of the variable =#
              local outClassEnv::FCore.Graph #= the environment of the variable, typically the same as input, but e.g. for loop scopes can be 'stripped' =#
              local splicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outClassEnv, outComponentEnv, name) = begin
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local sid::Option{String}
                  local ht::FCore.Children
                  local ref::DAE.ComponentRef
                  local cache::FCore.Cache
                  local cnstForRange::Option{DAE.Const}
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                   #=  look into the current frame
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, searchStrategy) begin
                  (cache, FCore.G(scope = r <| _), ref, _)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarF(cache, ht, ref, inEnv)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, inEnv, componentEnv, name)
                  end

                  (cache, FCore.G(scope = r <| _), ref, _)  => begin
                      @match true = FNode.isImplicitRefName(r)
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name) = lookupVarInternal(cache, env, ref, searchStrategy)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name)
                  end

                  (cache, FCore.G(scope = _ <| _ <| _), ref, InstTypes.SEARCH_ALSO_BUILTIN(__))  => begin
                      @match true = Builtin.variableIsBuiltin(ref)
                      env = FGraphUtil.topScope(inEnv)
                      ht = FNode.children(FNode.fromRef(FGraphUtil.lastScopeRef(env)))
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarF(cache, ht, ref, env)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name)
                  end
                end
              end
               #=  look in the next frame, only if current frame is a for loop scope.
               =#
               #=  If not in top scope, look in top scope for builtin variables, e.g. time.
               =#
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData, outClassEnv #= the environment of the variable, typically the same as input, but e.g. for loop scopes can be 'stripped' =#, outComponentEnv #= the component environment of the variable =#, name)
        end

         #= Helper function to lookupVar. Searches the frames for variables. =#
        function lookupVarInternalIdent(inCache::FCore.Cache, inEnv::FCore.Graph, ident::String, ss::List{<:DAE.Subscript} = nil, searchStrategy::InstTypes.SearchStrategy = InstTypes.SEARCH_LOCAL_ONLY() #= if SEARCH_LOCAL_ONLY it won't search in the builtin scope =#) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, FCore.Graph, String}
              local name::String
              local outComponentEnv::FCore.Graph #= the component environment of the variable =#
              local outClassEnv::FCore.Graph #= the environment of the variable, typically the same as input, but e.g. for loop scopes can be 'stripped' =#
              local splicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outClassEnv, outComponentEnv, name) = begin
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local sid::Option{String}
                  local ht::FCore.Children
                  local ref::DAE.ComponentRef
                  local cache::FCore.Cache
                  local cnstForRange::Option{DAE.Const}
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                   #=  look into the current frame
                   =#
                @matchcontinue (inCache, inEnv, searchStrategy) begin
                  (cache, FCore.G(scope = r <| _), _)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarFIdent(cache, ht, ident, ss, inEnv)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, inEnv, componentEnv, name)
                  end

                  (cache, FCore.G(scope = r <| _), _)  => begin
                      @match true = FNode.isImplicitRefName(r)
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name) = lookupVarInternalIdent(cache, env, ident, ss, searchStrategy)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name)
                  end

                  (cache, FCore.G(scope = _ <| _ <| _), InstTypes.SEARCH_ALSO_BUILTIN(__))  => begin
                      @match true = Builtin.variableNameIsBuiltin(ident)
                      env = FGraphUtil.topScope(inEnv)
                      ht = FNode.children(FNode.fromRef(FGraphUtil.lastScopeRef(env)))
                      (cache, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name) = lookupVarFIdent(cache, ht, ident, ss, env)
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, env, componentEnv, name)
                  end
                end
              end
               #=  look in the next frame, only if current frame is a for loop scope.
               =#
               #=  If not in top scope, look in top scope for builtin variables, e.g. time.
               =#
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData, outClassEnv #= the environment of the variable, typically the same as input, but e.g. for loop scopes can be 'stripped' =#, outComponentEnv #= the component environment of the variable =#, name)
        end

         #= returns true if the frame is a for-loop scope or a valueblock scope.
        This is indicated by the name of the frame. =#
        function frameIsImplAddedScope(f::FCore.Node) ::Bool
              local b::Bool

              b = begin
                  local oname::FCore.Name
                @match f begin
                  FCore.N(name = oname)  => begin
                    FCore.isImplicitScope(oname)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= This function is called when a lookup of a variable with qualified names
          does not have the first element as a component, e.g. A.B.C is looked up
          where A is not a component. This implies that A is a class, and this
          class should be temporary instantiated, and the lookup should
          be performed within that class. I.e. the function performs lookup of
          variables in the class hierarchy.

          Note: the splicedExpData is currently not relevant, since constants are always evaluated to a value.
                However, this might change in the future since it makes more sense to calculate the constants
                during setup in runtime (to gain precision and postpone choice of precision to runtime). =#
        function lookupVarInPackages(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in a lower scope. =#) ::Tuple{FCore.Cache, FCore.Graph, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, String}
              local name::String #= We only return the environment the component was found in; not its FQ name. =#
              local outComponentEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData #= currently not relevant for constants, but might be used in the future =#
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outClassEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outComponentEnv, name) = begin
                  local c::SCode.Element
                  local n::String
                  local id::String
                  local encflag::SCode.Encapsulated
                  local r::SCode.Restriction
                  local env2::FCore.Graph
                  local env3::FCore.Graph
                  local env5::FCore.Graph
                  local env::FCore.Graph
                  local p_env::FCore.Graph
                  local classEnv::FCore.Graph
                  local componentEnv::FCore.Graph
                  local prevFrames::FCore.Scope
                  local fs::FCore.Scope
                  local node::FCore.Node
                  local ci_state::ClassInf.SMNode
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local bind::DAE.Binding
                  local cref::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local sb::List{DAE.Subscript}
                  local sid::Option{String}
                  local f::FCore.MMRef
                  local rr::FCore.MMRef
                  local of::Option{FCore.MMRef}
                  local cache::FCore.Cache
                  local cnstForRange::Option{DAE.Const}
                  local path::Absyn.Path
                  local scope::Absyn.Path
                  local unique::Bool
                  local ht::FCore.Children
                  local qimports::List{Absyn.Import}
                  local uqimports::List{Absyn.Import}
                  local mod::DAE.Mod
                   #=  If we search for A1.A2....An.x while in scope A1.A2...An, just search for x.
                   =#
                   #=  Must do like this to ensure finite recursion
                   =#
                @matchcontinue (inCache, inEnv, inComponentRef, inPrevFrames, inState) begin
                  (cache, env, DAE.CREF_QUAL(ident = id, subscriptLst =  nil(), componentRef = cref), prevFrames, _)  => begin
                      (of, prevFrames) = lookupPrevFrames(id, prevFrames)
                      _ = begin
                        @match of begin
                          SOME(f)  => begin
                              Mutable.update(inState, true)
                              env5 = FGraphUtil.pushScopeRef(env, f)
                            ()
                          end

                          NONE()  => begin
                              @match (cache, (@match SCode.CLASS(name = n, encapsulatedPrefix = encflag, restriction = r) = c), env2, prevFrames) = lookupClassInEnv(cache, env, id, prevFrames, Mutable.create(true), NONE())
                              Mutable.update(inState, true)
                              rr = FNode.child(FGraphUtil.lastScopeRef(env2), id)
                              if FNode.isRefInstance(rr)
                                (cache, env5) = Inst.getCachedInstance(cache, env2, id, rr)
                              else
                                env3 = FGraphUtil.openScope(env2, encflag, n, FGraphUtil.restrictionToScopeType(r))
                                ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env3))
                                mod = Mod.getClassModifier(env2, n)
                                (cache, env5, _, _, _, _, _, _, _, _, _, _) = Inst.instClassIn(cache, env3, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, mod, Prefix.NOPRE(), ci_state, c, SCode.PUBLIC(), nil, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet, NONE())
                              end
                            ()
                          end
                        end
                      end
                      (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env5, cref, prevFrames, inState)
                      splicedExpData = prefixSplicedExp(CrefForHashTable.crefFirstCref(inComponentRef), splicedExpData)
                    (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, env, cr && DAE.CREF_IDENT(__), _, _)  => begin
                      (cache, env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackagesIdent(cache, env, cr.ident, cr.subscriptLst, inPrevFrames, inState)
                    (cache, env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, env, cr && DAE.CREF_QUAL(__), _, _)  => begin
                      ht = FNode.children(FNode.fromRef(FGraphUtil.lastScopeRef(env)))
                      (cache, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarF(cache, ht, cr, env)
                    (cache, env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, FCore.G(scope = f <| fs), cr && DAE.CREF_QUAL(__), prevFrames, _)  => begin
                      @match false = Mutable.access(inState)
                      env = FGraphUtil.setScope(inEnv, fs)
                      (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env, cr, _cons(f, prevFrames), inState)
                    (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  Add the class name to the spliced exp so that the name is correct.
               =#
               #=  Why is this done? It is already done done in lookupVar!
               =#
               #=  BZ: This is due to recursive call when it might become DAE.CREF_IDENT calls.
               =#
               #=  Lookup where the first identifier is a component.
               =#
               #=  Search parent scopes
               =#
               #= true = Flags.isSet(Flags.FAILTRACE);
               =#
               #= Debug.traceln(\"- Lookup.lookupVarInPackages failed on exp:\" + CrefForHashTable.printComponentRefStr(cr) + \" in scope: \" + FGraphUtil.printGraphPathStr(env));
               =#
          (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData #= currently not relevant for constants, but might be used in the future =#, outComponentEnv, name #= We only return the environment the component was found in; not its FQ name. =#)
        end

         #= This function is called when a lookup of a variable with qualified names
          does not have the first element as a component, e.g. A.B.C is looked up
          where A is not a component. This implies that A is a class, and this
          class should be temporary instantiated, and the lookup should
          be performed within that class. I.e. the function performs lookup of
          variables in the class hierarchy.

          Note: the splicedExpData is currently not relevant, since constants are always evaluated to a value.
                However, this might change in the future since it makes more sense to calculate the constants
                during setup in runtime (to gain precision and postpone choice of precision to runtime). =#
        function lookupVarInPackagesIdent(inCache::FCore.Cache, inEnv::FCore.Graph, id::String, ss::List{<:DAE.Subscript}, inPrevFrames::FCore.Scope #= Environment in reverse order. Contains frames we previously had in the scope. Will be looked up instead of the environment in order to avoid infinite recursion. =#, inState::MutableType #= {<:Bool} =# #= If true, we have found a class. If the path was qualified, we should no longer look in a lower scope. =#) ::Tuple{FCore.Cache, FCore.Graph, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, String}
              local name::String #= We only return the environment the component was found in; not its FQ name. =#
              local outComponentEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData #= currently not relevant for constants, but might be used in the future =#
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outClassEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outComponentEnv, name) = begin
                  local c::SCode.Element
                  local n::String
                  local encflag::SCode.Encapsulated
                  local r::SCode.Restriction
                  local env2::FCore.Graph
                  local env3::FCore.Graph
                  local env5::FCore.Graph
                  local env::FCore.Graph
                  local p_env::FCore.Graph
                  local classEnv::FCore.Graph
                  local componentEnv::FCore.Graph
                  local prevFrames::FCore.Scope
                  local fs::FCore.Scope
                  local node::FCore.Node
                  local ci_state::ClassInf.SMNode
                  local attr::DAE.Attributes
                  local ty::DAE.Type
                  local bind::DAE.Binding
                  local cref::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local sb::List{DAE.Subscript}
                  local sid::Option{String}
                  local f::FCore.MMRef
                  local rr::FCore.MMRef
                  local of::Option{FCore.MMRef}
                  local cache::FCore.Cache
                  local cnstForRange::Option{DAE.Const}
                  local path::Absyn.Path
                  local scope::Absyn.Path
                  local unique::Bool
                  local ht::FCore.Children
                  local qimports::List{Absyn.Import}
                  local uqimports::List{Absyn.Import}
                  local mod::DAE.Mod
                   #=  Why is this done? It is already done done in lookupVar!
                   =#
                   #=  BZ: This is due to recursive call when it might become DAE.CREF_IDENT calls.
                   =#
                @matchcontinue (inCache, inEnv, inPrevFrames, inState) begin
                  (cache, env, _, _)  => begin
                      (cache, attr, ty, bind, cnstForRange, splicedExpData, _, componentEnv, name) = lookupVarInternalIdent(cache, env, id, ss)
                      Mutable.update(inState, true)
                    (cache, env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, env, _, _)  => begin
                      ht = FNode.children(FNode.fromRef(FGraphUtil.lastScopeRef(env)))
                      (cache, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarFIdent(cache, ht, id, ss, env)
                    (cache, env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, env, prevFrames, _)  => begin
                      node = FNode.fromRef(FGraphUtil.lastScopeRef(env))
                      (qimports, uqimports) = FNode.imports(node)
                      _ = begin
                        @matchcontinue (qimports, uqimports) begin
                          (_ <| _, _)  => begin
                              cr = lookupQualifiedImportedVarInFrame(qimports, id)
                              Mutable.update(inState, true)
                              cr = if FNode.name(FNode.fromRef(FGraphUtil.lastScopeRef(env))) == CrefForHashTable.crefFirstIdent(cr)
                                    CrefForHashTable.crefStripFirstIdent(cr)
                                  else
                                    cr
                                  end
                              @match _cons(f, prevFrames) = listReverse(FGraphUtil.currentScope(env))
                              env = FGraphUtil.setScope(env, list(f))
                              (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackages(cache, env, cr, prevFrames, inState)
                            ()
                          end

                          (_, _ <| _)  => begin
                              (cache, p_env, attr, ty, bind, cnstForRange, unique, splicedExpData, componentEnv, name) = lookupUnqualifiedImportedVarInFrame(cache, uqimports, env, id)
                              reportSeveralNamesError(unique, id)
                              Mutable.update(inState, true)
                            ()
                          end
                        end
                      end
                    (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  (cache, FCore.G(scope = f <| fs), prevFrames, _)  => begin
                      @match false = Mutable.access(inState)
                      env = FGraphUtil.setScope(inEnv, fs)
                      (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name) = lookupVarInPackagesIdent(cache, env, id, ss, _cons(f, prevFrames), inState)
                    (cache, p_env, attr, ty, bind, cnstForRange, splicedExpData, componentEnv, name)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  Lookup where the first identifier is a component.
               =#
               #=  Search among imports
               =#
               #=  Search among qualified imports, e.g. import A.B; or import D=A.B;
               =#
               #=  if the first name of the import A.B is equal with the scope we are in, skip it!
               =#
               #=  Search among unqualified imports, e.g. import A.B.*
               =#
               #=  Search parent scopes
               =#
               #= true = Flags.isSet(Flags.FAILTRACE);
               =#
               #= Debug.traceln(\"- Lookup.lookupVarInPackages failed on exp:\" + CrefForHashTable.printComponentRefStr(cr) + \" in scope: \" + FGraphUtil.printGraphPathStr(env));
               =#
          (outCache, outClassEnv, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData #= currently not relevant for constants, but might be used in the future =#, outComponentEnv, name #= We only return the environment the component was found in; not its FQ name. =#)
        end

         #= This function is very similar to `lookup_var\\', but it only looks
          in the topmost environment frame, which means that it only finds
          names defined in the local scope.
          ----EXCEPTION---: When the topmost scope is the scope of a for loop, the lookup
          continues on the next scope. This to allow variables in the local scope to
          also be found even if inside a for scope.
          Arg1: The environment to search in
          Arg2: The variable to search for. =#
        function lookupVarLocal(inCache::FCore.Cache, inEnv::FCore.Graph, inComponentRef::DAE.ComponentRef) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, FCore.Graph, String}
              local name::String
              local outComponentEnv::FCore.Graph
              local outClassEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

               #=  adrpo: use lookupVarInternal as is the SAME but it doesn't search in the builtin scope!
               =#
              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outClassEnv, outComponentEnv, name) = lookupVarInternal(inCache, inEnv, inComponentRef, InstTypes.SEARCH_LOCAL_ONLY())
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData, outClassEnv, outComponentEnv, name)
        end

         #= Searches for a variable in the local scope. =#
        function lookupIdentLocal(inCache::FCore.Cache, inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{FCore.Cache, DAE.Var, SCode.Element, DAE.Mod, FCore.Status, FCore.Graph}
              local outComponentEnv::FCore.Graph
              local instStatus::FCore.Status
              local outMod::DAE.Mod
              local outElement::SCode.Element
              local outVar::DAE.Var
              local outCache::FCore.Cache

              (outCache, outVar, outElement, outMod, instStatus, outComponentEnv) = begin
                  local fv::DAE.Var
                  local c::SCode.Element
                  local m::DAE.Mod
                  local i::FCore.Status
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                  local env::FCore.Graph
                  local componentEnv::FCore.Graph
                  local sid::Option{String}
                  local ht::FCore.Children
                  local id::String
                  local cache::FCore.Cache
                   #=  component environment
                   =#
                @matchcontinue (inCache, inEnv, inIdent) begin
                  (cache, FCore.G(scope = r <| _), id)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      (fv, c, m, i, componentEnv) = lookupVar2(ht, id, inEnv)
                    (cache, fv, c, m, i, componentEnv)
                  end

                  (cache, FCore.G(scope = r <| _), id)  => begin
                      @match true = FNode.isImplicitRefName(r)
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (cache, fv, c, m, i, componentEnv) = lookupIdentLocal(cache, env, id)
                    (cache, fv, c, m, i, componentEnv)
                  end
                end
              end
               #=  Look in the next frame, if the current frame is a for loop scope.
               =#
          (outCache, outVar, outElement, outMod, instStatus, outComponentEnv)
        end

         #= Searches for a class definition in the local scope. =#
        function lookupClassLocal(inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{SCode.Element, FCore.Graph}
              local outEnv::FCore.Graph
              local outClass::SCode.Element

              (outClass, outEnv) = begin
                  local cl::SCode.Element
                  local env::FCore.Graph
                  local sid::Option{String}
                  local ht::FCore.Children
                  local id::String
                  local r::FCore.MMRef
                @match (inEnv, inIdent) begin
                  (env && FCore.G(scope = r <| _), id)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      r = FCore.RefTree.get(ht, id)
                      @match FCore.N(data = FCore.CL(e = cl)) = FNode.fromRef(r)
                    (cl, env)
                  end
                end
              end
          (outClass, outEnv)
        end

         #= Same as lookupIdentLocal, except check all frames =#
        function lookupIdent(inCache::FCore.Cache, inEnv::FCore.Graph, inIdent::SCode.Ident) ::Tuple{FCore.Cache, DAE.Var, SCode.Element, DAE.Mod, FCore.Status, FCore.Graph}
              local outEnv::FCore.Graph #= the env where we found the ident =#
              local instStatus::FCore.Status
              local outMod::DAE.Mod
              local outElement::SCode.Element
              local outVar::DAE.Var
              local outCache::FCore.Cache

              (outCache, outVar, outElement, outMod, instStatus, outEnv) = begin
                  local fv::DAE.Var
                  local c::SCode.Element
                  local m::DAE.Mod
                  local i::FCore.Status
                  local sid::Option{String}
                  local ht::FCore.Children
                  local id::String
                  local e::FCore.Graph
                  local cache::FCore.Cache
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                @matchcontinue (inCache, inEnv, inIdent) begin
                  (cache, FCore.G(scope = r <| _), id)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      (fv, c, m, i, _) = lookupVar2(ht, id, inEnv)
                    (cache, fv, c, m, i, inEnv)
                  end

                  (cache, FCore.G(scope = _ <| _), id)  => begin
                      (e, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (cache, fv, c, m, i, e) = lookupIdent(cache, e, id)
                    (cache, fv, c, m, i, e)
                  end
                end
              end
          (outCache, outVar, outElement, outMod, instStatus, outEnv #= the env where we found the ident =#)
        end

         #=  Function lookup
         =#

         #= Returns a list of types that the function has. =#
        function lookupFunctionsInEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inId::Absyn.Path, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outTypesTypeLst::List{DAE.Type}
              local outCache::FCore.Cache

              (outCache, outTypesTypeLst) = begin
                  local env_1::FCore.Graph
                  local cenv::FCore.Graph
                  local env::FCore.Graph
                  local fs::FCore.Graph
                  local f::FCore.Node
                  local res::List{DAE.Type}
                  local names::List{Absyn.Path}
                  local httypes::FCore.Children
                  local ht::FCore.Children
                  local str::String
                  local name::String
                  local cache::FCore.Cache
                  local id::Absyn.Path
                  local scope::Absyn.Path
                  local info::SourceInfo
                   #= /*
                      case (cache,env,id,info)
                        equation
                          print(\"Looking up: \" + AbsynUtil.pathString(id) + \" in env: \" + FGraphUtil.printGraphPathStr(env) + \"\\n\");
                        then
                          fail();*/ =#
                   #= /*/ strip env if path is fully qualified in env
                      case (cache,env,id,info)
                        equation
                          id = Env.pathStripEnvIfFullyQualifedInEnv(id, env);
                          (cache,res) = lookupFunctionsInEnv(cache,env,id,info);
                        then
                          (cache,res);*/ =#
                   #=  we might have a component reference, i.e. world.gravityAcceleration
                   =#
                @matchcontinue (inCache, inEnv, inId, inInfo) begin
                  (cache, env, Absyn.QUALIFIED(name, id), info)  => begin
                      ErrorExt.setCheckpoint("functionViaComponentRef")
                      (cache, _, _, _, _, _, _, cenv, _) = lookupVarIdent(cache, env, name, nil)
                      (cache, res) = lookupFunctionsInEnv(cache, cenv, id, info)
                      ErrorExt.rollBack("functionViaComponentRef")
                    (cache, res)
                  end

                  (_, _, Absyn.QUALIFIED(_, _), _)  => begin
                      ErrorExt.rollBack("functionViaComponentRef")
                    fail()
                  end

                  (cache, env, id, _)  => begin
                      env = FGraphUtil.selectScope(env, id)
                      name = AbsynUtil.pathLastIdent(id)
                      (cache, res) = lookupFunctionsInEnv(cache, env, Absyn.IDENT(name), inInfo)
                    (cache, res)
                  end

                  (cache, env, Absyn.IDENT(name = str), info)  => begin
                      _ = Static.elabBuiltinHandler(str) #= Check for builtin operators =#
                      env = FGraphUtil.topScope(env)
                      ht = FNode.children(FNode.fromRef(FGraphUtil.lastScopeRef(env)))
                      httypes = getHtTypes(FGraphUtil.lastScopeRef(env))
                      (cache, res) = lookupFunctionsInFrame(cache, ht, httypes, env, str, info)
                    (cache, res)
                  end

                  (cache, env, Absyn.IDENT(name = str && "cardinality"), _)  => begin
                      env = FGraphUtil.topScope(env)
                      res = createGenericBuiltinFunctions(env, str)
                    (cache, res)
                  end

                  (cache, env, id, info)  => begin
                      @shouldFail @match Absyn.FULLYQUALIFIED(_) = id
                      (cache, res) = lookupFunctionsInEnv2(cache, env, id, false, info)
                    (cache, res)
                  end

                  (cache, env, Absyn.FULLYQUALIFIED(id), info)  => begin
                      env = FGraphUtil.topScope(env)
                      (cache, res) = lookupFunctionsInEnv2(cache, env, id, true, info)
                    (cache, res)
                  end

                  (cache, env, id, _)  => begin
                      id = begin
                        @match id begin
                          Absyn.IDENT("Clock")  => begin
                            Absyn.QUALIFIED("OpenModelica", Absyn.QUALIFIED("Internal", Absyn.IDENT("ClockConstructor")))
                          end

                          _  => begin
                              id
                          end
                        end
                      end
                      @match (cache, SCode.CLASS(classDef = SCode.OVERLOAD(pathLst = names), info = info), env_1) = lookupClass(cache, env, id)
                      (cache, res) = lookupFunctionsListInEnv(cache, env_1, names, info, nil)
                    (cache, res)
                  end

                  (cache, _, _, _)  => begin
                    (cache, nil)
                  end

                  (_, _, id, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("lookupFunctionsInEnv failed on: " + AbsynUtil.pathString(id))
                    fail()
                  end
                end
              end
               #=  here we do some bad things which unfortunately are needed for some MSL models (MoistAir1)
               =#
               #=  we search the environment in reverse instead of finding out where the first id of the path is
               =#
               #=  Builtin operators are looked up in top frame directly
               =#
               #=  Check for cardinality that can not be represented in the environment.
               =#
               #=  not fully qualified!
               =#
               #=  fullyqual
               =#
               #=  print(stringDelimitList(List.map(res,Types.unparseType),\"\\n###\\n\"));
               =#
          (outCache, outTypesTypeLst)
        end

        function lookupFunctionsListInEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inIds::List{<:Absyn.Path}, info::SourceInfo, inAcc::List{<:DAE.Type}) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outTypesTypeLst::List{DAE.Type}
              local outCache::FCore.Cache

              (outCache, outTypesTypeLst) = begin
                  local id::Absyn.Path
                  local res::List{DAE.Type}
                  local str::String
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ids::List{Absyn.Path}
                  local acc::List{DAE.Type}
                @matchcontinue (inCache, inEnv, inIds, info, inAcc) begin
                  (cache, _,  nil(), _, acc)  => begin
                    (cache, listReverse(acc))
                  end

                  (cache, env, id <| ids, _, acc)  => begin
                      @match (cache, res && _ <| _) = lookupFunctionsInEnv(cache, env, id, info)
                      (cache, acc) = lookupFunctionsListInEnv(cache, env, ids, info, listAppend(res, acc))
                    (cache, acc)
                  end

                  (_, env, id <| _, _, _)  => begin
                      str = AbsynUtil.pathString(id) + " not found in scope: " + FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, outTypesTypeLst)
        end

         #= Returns a list of types that the function has. =#
        function lookupFunctionsInEnv2(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path, followedQual::Bool #= cannot pop frames if we followed a qualified path at any point =#, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outTypesTypeLst::List{DAE.Type}
              local outCache::FCore.Cache

              (outCache, outTypesTypeLst) = begin
                  local id::Absyn.Path
                  local path::Absyn.Path
                  local sid::Option{String}
                  local httypes::FCore.Children
                  local ht::FCore.Children
                  local res::List{DAE.Type}
                  local env::FCore.Graph
                  local fs::FCore.Graph
                  local env_1::FCore.Graph
                  local env2::FCore.Graph
                  local env_2::FCore.Graph
                  local pack::String
                  local str::String
                  local c::SCode.Element
                  local encflag::SCode.Encapsulated
                  local restr::SCode.Restriction
                  local ci_state::ClassInf.SMNode
                  local cistate1::ClassInf.SMNode
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                  local cache::FCore.Cache
                  local mod::DAE.Mod
                   #=  Simple name, search frame
                   =#
                @matchcontinue (inCache, inEnv, inPath, followedQual, info) begin
                  (cache, FCore.G(scope = r <| _), Absyn.IDENT(name = str), _, _)  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      httypes = getHtTypes(r)
                      @match (cache, res && _ <| _) = lookupFunctionsInFrame(cache, ht, httypes, inEnv, str, info)
                    (cache, res)
                  end

                  (cache, FCore.G(scope = r <| _), id && Absyn.IDENT(__), _, _)  => begin
                      @match (cache, c, env_1) = lookupClass(cache, inEnv, id)
                      @match SCode.CLASS(name = str, restriction = restr) = c
                      @match true = SCodeUtil.isFunctionRestriction(restr)
                      @match (cache, env_2, _) = InstFunction.implicitFunctionTypeInstantiation(cache, env_1, InnerOuterTypes.emptyInstHierarchy, c)
                      @match FCore.G(scope = r <| _) = env_2
                      ht = FNode.children(FNode.fromRef(r))
                      httypes = getHtTypes(r)
                      @match (cache, res && _ <| _) = lookupFunctionsInFrame(cache, ht, httypes, env_2, str, info)
                    (cache, res)
                  end

                  (cache, FCore.G(scope = r <| _), Absyn.QUALIFIED(name = pack, path = path), _, _)  => begin
                      @match (cache, c, env_1) = lookupClass(cache, inEnv, Absyn.IDENT(pack))
                      @match SCode.CLASS(name = str, encapsulatedPrefix = encflag, restriction = restr) = c
                      r = FNode.child(FGraphUtil.lastScopeRef(env_1), str)
                      if FNode.isRefInstance(r)
                        (cache, env2) = Inst.getCachedInstance(cache, env_1, str, r)
                      else
                        env2 = FGraphUtil.openScope(env_1, encflag, str, FGraphUtil.restrictionToScopeType(restr))
                        ci_state = ClassInf.start(restr, FGraphUtil.getGraphName(env2))
                        mod = Mod.getClassModifier(env_1, str)
                        (cache, env2, _, _, _) = Inst.partialInstClassIn(cache, env2, InnerOuterTypes.emptyInstHierarchy, mod, Prefix.NOPRE(), ci_state, c, SCode.PUBLIC(), nil, 0)
                      end
                      (cache, res) = lookupFunctionsInEnv2(cache, env2, path, true, info)
                    (cache, res)
                  end

                  (cache, FCore.G(scope = r <| _), id, false, _)  => begin
                      @match false = FNode.isEncapsulated(FNode.fromRef(r))
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (cache, res) = lookupFunctionsInEnv2(cache, env, id, false, info)
                    (cache, res)
                  end

                  (cache, FCore.G(scope = r <| _), id && Absyn.IDENT(__), false, _)  => begin
                      @match true = FNode.isEncapsulated(FNode.fromRef(r))
                      env = FGraphUtil.topScope(inEnv)
                      (cache, res) = lookupFunctionsInEnv2(cache, env, id, true, info)
                    (cache, res)
                  end
                end
              end
               #=  Did not match. Search next frame.
               =#
               #=  (cache,env) = Builtin.initialGraph(cache);
               =#
          (outCache, outTypesTypeLst)
        end

         #= author: PA
          This function creates function types on-the-fly for special builtin
          operators/functions which can not be represented in the builtin
          environment. =#
        function createGenericBuiltinFunctions(inEnv::FCore.Graph, inString::String) ::List{DAE.Type}
              local outTypesTypeLst::List{DAE.Type}

              outTypesTypeLst = begin
                  local env::FCore.Graph
                   #=  function_name cardinality
                   =#
                @match (inEnv, inString) begin
                  (_, "cardinality")  => begin
                    list(DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_COMPLEX(ClassInf.CONNECTOR(Absyn.IDENT(""), false), nil, NONE()), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_DEFAULT, Absyn.IDENT("cardinality")), DAE.T_FUNCTION(list(DAE.FUNCARG("x", DAE.T_COMPLEX(ClassInf.CONNECTOR(Absyn.IDENT(""), true), nil, NONE()), DAE.C_VAR(), DAE.NON_PARALLEL(), NONE())), DAE.T_INTEGER_DEFAULT, DAE.FUNCTION_ATTRIBUTES_DEFAULT, Absyn.IDENT("cardinality")))
                  end
                end
              end
          outTypesTypeLst
        end

         #=  - Internal functions
         =#
         #=    Type lookup
         =#

         #= function: lookupTypeInEnv =#
        function lookupTypeInEnv(inCache::FCore.Cache, inEnv::FCore.Graph, id::String) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph
              local outType::DAE.Type
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local c::DAE.Type
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local fs::FCore.Graph
                  local sid::Option{String}
                  local httypes::FCore.Children
                  local ht::FCore.Children
                  local cache::FCore.Cache
                  local path::Absyn.Path
                  local r::FCore.MMRef
                @matchcontinue (inCache, inEnv) begin
                  (cache, env && FCore.G(scope = r <| _))  => begin
                      ht = FNode.children(FNode.fromRef(r))
                      httypes = getHtTypes(r)
                      (cache, c, env_1) = lookupTypeInFrame(cache, ht, httypes, env, id)
                    (cache, c, env_1)
                  end

                  (cache, env && FCore.G(scope = r <| _))  => begin
                      (env, _) = FGraphUtil.stripLastScopeRef(env)
                      (cache, c, env_1) = lookupTypeInEnv(cache, env, id)
                      env_1 = FGraphUtil.pushScopeRef(env_1, r)
                    (cache, c, env_1)
                  end
                end
              end
          (outCache, outType, outEnv)
        end

        function getHtTypes(inParentRef::FCore.MMRef) ::FCore.Children
              local ht::FCore.Children

              ht = begin
                  local r::FCore.MMRef
                   #=  there is a ty node
                   =#
                @matchcontinue inParentRef begin
                  _  => begin
                      r = FNode.child(inParentRef, FNode.tyNodeName)
                      ht = FNode.children(FNode.fromRef(r))
                    ht
                  end

                  _  => begin
                      FCore.RefTree.new()
                  end
                end
              end
               #=  no ty node
               =#
          ht
        end

         #= Searches a frame for a type. =#
        function lookupTypeInFrame(inCache::FCore.Cache, inBinTree1::FCore.Children, inBinTree2::FCore.Children, inEnv3::FCore.Graph, inIdent4::SCode.Ident) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph
              local outType::DAE.Type
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local t::DAE.Type
                  local httypes::FCore.Children
                  local ht::FCore.Children
                  local env::FCore.Graph
                  local id::String
                  local cache::FCore.Cache
                  local item::FCore.Node
                @match (inCache, inBinTree1, inBinTree2, inEnv3, inIdent4) begin
                  (cache, _, httypes, env, id)  => begin
                      item = FNode.fromRef(FCore.RefTree.get(httypes, id))
                      (cache, t, env) = lookupTypeInFrame2(cache, item, env, id)
                    (cache, t, env)
                  end
                end
              end
          (outCache, outType, outEnv)
        end

         #= Searches a frame for a type. =#
        function lookupTypeInFrame2(inCache::FCore.Cache, item::FCore.Node, inEnv3::FCore.Graph, inIdent4::SCode.Ident) ::Tuple{FCore.Cache, DAE.Type, FCore.Graph}
              local outEnv::FCore.Graph
              local outType::DAE.Type
              local outCache::FCore.Cache

              (outCache, outType, outEnv) = begin
                  local t::DAE.Type
                  local ty::DAE.Type
                  local env::FCore.Graph
                  local cenv::FCore.Graph
                  local env_1::FCore.Graph
                  local env_3::FCore.Graph
                  local id::String
                  local n::String
                  local cdef::SCode.Element
                  local comp::SCode.Element
                  local cache::FCore.Cache
                  local info::SourceInfo
                @match (inCache, item, inEnv3, inIdent4) begin
                  (cache, FCore.N(data = FCore.FT(t <| _)), env, _)  => begin
                    (cache, t, env)
                  end

                  (_, FCore.N(data = FCore.CO(e = comp)), _, id)  => begin
                      info = SCodeUtil.elementInfo(comp)
                      Error.addSourceMessage(Error.LOOKUP_TYPE_FOUND_COMP, list(id), info)
                    fail()
                  end

                  (cache, FCore.N(data = FCore.CL(e = cdef && SCode.CLASS(restriction = SCode.R_RECORD(_)))), env, _)  => begin
                      (cache, env_3, ty) = buildRecordType(cache, env, cdef)
                    (cache, ty, env_3)
                  end

                  (cache, FCore.N(data = FCore.CL(e = cdef && SCode.CLASS(restriction = SCode.R_METARECORD(__)))), env, _)  => begin
                      (cache, env_3, ty) = buildMetaRecordType(cache, env, cdef)
                    (cache, ty, env_3)
                  end

                  (cache, FCore.N(data = FCore.CL(e = cdef && SCode.CLASS(restriction = SCode.R_FUNCTION(_)))), env, id)  => begin
                      cenv = env
                      (cache, env_1, _) = InstFunction.implicitFunctionInstantiation(cache, cenv, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), cdef, nil)
                      (cache, ty, env_3) = lookupTypeInEnv(cache, env_1, id)
                    (cache, ty, env_3)
                  end
                end
              end
               #=  Record constructor function
               =#
               #=  Found function
               =#
               #=  fprintln(Flags.INST_TRACE, \"LOOKUP TYPE IN FRAME ICD: \" + FGraphUtil.printGraphPathStr(env) + \" id:\" + id);
               =#
               #=  select the env if is the same as cenv as is updated!
               =#
               #=  selectUpdatedEnv(env, cenv);
               =#
          (outCache, outType, outEnv)
        end

         #= This actually only looks up the function name and find all
           corresponding types that have this function name. =#
        function lookupFunctionsInFrame(inCache::FCore.Cache, inClasses::FCore.Children, inFuncTypes::FCore.Children, inEnv::FCore.Graph, inFuncName::SCode.Ident, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Type}}
              local outFuncTypes::List{DAE.Type}
              local outCache::FCore.Cache

              local r::FCore.MMRef
              local data::FNode.Data
              local ty::DAE.Type

              try
                r = FCore.RefTree.get(inFuncTypes, inFuncName)
                @match FCore.N(data = FCore.FT(outFuncTypes)) = FNode.fromRef(r)
                outCache = inCache
              catch
                r = FCore.RefTree.get(inClasses, inFuncName)
                @match FCore.N(data = data) = FNode.fromRef(r)
                (outCache, outFuncTypes) = begin
                     #=  Try to look up the function among the function types first.
                     =#
                     #=  If not found, try to look the function up in the environment instead.
                     =#
                    local cl::SCode.Element
                    local tps::List{DAE.Type}
                    local cache::FCore.Cache
                    local env::FCore.Graph
                     #=  MetaModelica partial functions.
                     =#
                  @matchcontinue data begin
                    _  => begin
                        @match DAE.TYPES_VAR(ty = ty) = FNode.refInstVar(r)
                        ty = begin
                          @match ty begin
                            DAE.T_FUNCTION(__)  => begin
                                ty.path = Absyn.IDENT(inFuncName)
                              ty
                            end
                          end
                        end
                      (inCache, list(ty))
                    end

                    FCore.CO(__)  => begin
                         #=  Found a component, print an error.
                         =#
                        Error.addSourceMessage(Error.LOOKUP_TYPE_FOUND_COMP, list(inFuncName), inInfo)
                      fail()
                    end

                    FCore.CL(e = cl && SCode.CLASS(restriction = SCode.R_RECORD(__)))  => begin
                         #=  A record, create a record constructor.
                         =#
                        (cache, _, ty) = buildRecordType(inCache, inEnv, cl)
                      (cache, list(ty))
                    end

                    FCore.CL(e = cl) where (SCodeUtil.isFunction(cl))  => begin
                         #=  A function, instantiate to get the type.
                         =#
                        (cache, env) = InstFunction.implicitFunctionTypeInstantiation(inCache, inEnv, InnerOuterTypes.emptyInstHierarchy, cl)
                        (cache, tps) = lookupFunctionsInEnv2(cache, env, Absyn.IDENT(inFuncName), true, inInfo)
                      (cache, tps)
                    end

                    FCore.CL(e = cl) where (SCodeUtil.classIsExternalObject(cl))  => begin
                         #=  An external object.
                         =#
                        (cache, env) = Inst.instClass(inCache, inEnv, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), cl, nil, false, InstTypes.TOP_CALL(), ConnectionGraph.EMPTY, DAE.emptySet)
                        (cache, ty) = lookupTypeInEnv(cache, env, inFuncName)
                      (cache, list(ty))
                    end
                  end
                end
              end
          (outCache, outFuncTypes)
        end

        function selectUpdatedEnv(inNewEnv::FCore.Graph, inOldEnv::FCore.Graph) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                @matchcontinue (inNewEnv, inOldEnv) begin
                  (_, _)  => begin
                      @match true = FGraphUtil.isTopScope(inNewEnv)
                    inOldEnv
                  end

                  (_, _)  => begin
                      @match true = stringEq(FGraphUtil.getGraphNameStr(inNewEnv), FGraphUtil.getGraphNameStr(inOldEnv))
                    inNewEnv
                  end

                  _  => begin
                      inOldEnv
                  end
                end
              end
               #=  return old if is top scope!
               =#
               #=  if they point to the same env, return the new one
               =#
          outEnv
        end

         #=  =#
        function buildRecordType(cache::FCore.Cache, env::FCore.Graph, icdef::SCode.Element) ::Tuple{FCore.Cache, FCore.Graph, DAE.Type}
              local ftype::DAE.Type
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local name::String
              local env_1::FCore.Graph
              local cdef::SCode.Element

              (outCache, _, cdef) = buildRecordConstructorClass(cache, env, icdef)
              name = SCodeUtil.className(cdef)
               #=  fprintln(Flags.INST_TRACE\", \"LOOKUP BUILD RECORD TY ICD: \" + FGraphUtil.printGraphPathStr(env) + \".\" + name);
               =#
              (outCache, outEnv, _) = InstFunction.implicitFunctionTypeInstantiation(outCache, env, InnerOuterTypes.emptyInstHierarchy, cdef)
              (outCache, ftype, _) = lookupTypeInEnv(outCache, outEnv, name)
          (outCache, outEnv, ftype)
        end

         #=
          Creates the record constructor class, i.e. a function, from the record
          class given as argument. =#
        function buildRecordConstructorClass(inCache::FCore.Cache, inEnv::FCore.Graph, inClass::SCode.Element) ::Tuple{FCore.Cache, FCore.Graph, SCode.Element}
              local outClass::SCode.Element
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outClass) = begin
                  local funcelts::List{SCode.Element}
                  local elts::List{SCode.Element}
                  local reselt::SCode.Element
                  local cl::SCode.Element
                  local id::String
                  local info::SourceInfo
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @matchcontinue (inCache, inEnv, inClass) begin
                  (cache, env, cl && SCode.CLASS(name = id, info = info))  => begin
                      (cache, env, funcelts, _) = buildRecordConstructorClass2(cache, env, cl, DAE.NOMOD())
                      reselt = buildRecordConstructorResultElt(funcelts, id, env, info)
                      cl = SCode.CLASS(id, SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_FUNCTION(SCode.FR_RECORD_CONSTRUCTOR()), SCode.PARTS(_cons(reselt, funcelts), nil, nil, nil, nil, nil, nil, NONE()), SCode.noComment, info)
                    (cache, env, cl)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("buildRecordConstructorClass failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outEnv, outClass)
        end

        function buildRecordConstructorClass2(inCache::FCore.Cache, inEnv::FCore.Graph, cl::SCode.Element, mods::DAE.Mod) ::Tuple{FCore.Cache, FCore.Graph, List{SCode.Element}, List{SCode.Element}}
              local elts::List{SCode.Element}
              local funcelts::List{SCode.Element}
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, funcelts, elts) = begin
                  local cdefelts::List{SCode.Element}
                  local classExtendsElts::List{SCode.Element}
                  local extendsElts::List{SCode.Element}
                  local compElts::List{SCode.Element}
                  local eltsMods::List{Tuple{SCode.Element, DAE.Mod}}
                  local name::String
                  local fpath::Absyn.Path
                  local info::SourceInfo
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env1::FCore.Graph
                   #=  a class with parts
                   =#
                @matchcontinue (inCache, inEnv, cl, mods) begin
                  (cache, env, SCode.CLASS(name = name, info = info), _)  => begin
                      (cache, env, _, elts, _, _, _, _, _) = InstExtends.instDerivedClasses(cache, env, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), cl, true, info)
                      env = FGraphUtil.openScope(env, SCode.NOT_ENCAPSULATED(), name, SOME(FCore.CLASS_SCOPE()))
                      fpath = FGraphUtil.getGraphName(env)
                      (cdefelts, classExtendsElts, extendsElts, compElts) = InstUtil.splitElts(elts)
                      (cache, env, _, _, eltsMods, _, _, _, _) = InstExtends.instExtendsAndClassExtendsList(cache, env, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), extendsElts, classExtendsElts, elts, ClassInf.RECORD(fpath), name, true, false)
                      eltsMods = listAppend(eltsMods, InstUtil.addNomod(compElts))
                      (cache, env1, _) = InstUtil.addClassdefsToEnv(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), cdefelts, false, NONE())
                      (cache, env1, _) = InstUtil.addComponentsToEnv(cache, env1, InnerOuterTypes.emptyInstHierarchy, mods, Prefix.NOPRE(), ClassInf.RECORD(fpath), eltsMods, true)
                      (cache, env1, funcelts) = buildRecordConstructorElts(cache, env1, eltsMods, mods)
                    (cache, env1, funcelts, elts)
                  end

                  _  => begin
                        Debug.traceln("buildRecordConstructorClass2 failed, cl:" + SCodeDump.unparseElementStr(cl, SCodeDump.defaultOptions) + "\\n")
                      fail()
                  end
                end
              end
               #=  print(\"Record Elements: \" +
               =#
               #=    stringDelimitList(
               =#
               #=      List.map(
               =#
               #=        List.map(
               =#
               #=          eltsMods,
               =#
               #=          Util.tuple21),
               =#
               #=        SCodeDump.printElementStr), \"\\n\"));
               =#
               #=  fail
               =#
               #= /* TODO: short class defs */ =#
          (outCache, outEnv, funcelts, elts)
        end

         #= @author: adrpo
         if the first modifier is empty (NOMOD) use the second one! =#
        function selectModifier(inModID::DAE.Mod, inModNoID::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                @matchcontinue (inModID, inModNoID) begin
                  (DAE.NOMOD(__), _)  => begin
                    inModNoID
                  end

                  _  => begin
                      inModID
                  end
                end
              end
          outMod
        end

         #= Helper function to build_record_constructor_class. Creates the elements
          of the function class.

          TODO: This function should be replaced by a proper instantiation using instClassIn instead, followed by a
          traversal of the DAE.Var changing direction to input.
          Reason for not doing that now: records can contain arrays with unknown dimensions. =#
        function buildRecordConstructorElts(inCache::FCore.Cache, inEnv::FCore.Graph, inSCodeElementLst::List{<:Tuple{<:SCode.Element, DAE.Mod}}, mods::DAE.Mod) ::Tuple{FCore.Cache, FCore.Graph, List{SCode.Element}}
              local outSCodeElementLst::List{SCode.Element}
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outSCodeElementLst) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local rest::List{Tuple{SCode.Element, DAE.Mod}}
                  local res::List{SCode.Element}
                  local comp::SCode.Element
                  local id::String
                  local ct::SCode.ConnectorType
                  local repl::SCode.Replaceable
                  local vis::SCode.Visibility
                  local f::SCode.Final
                  local redecl::SCode.Redeclare
                  local io::Absyn.InnerOuter
                  local d::List{Absyn.Subscript}
                  local prl::SCode.Parallelism
                  local var::SCode.Variability
                  local isf::Absyn.IsField
                  local dir::Absyn.Direction
                  local tp::Absyn.TypeSpec
                  local comment::SCode.Comment
                  local cond::Option{Absyn.Exp}
                  local mod::SCode.Mod
                  local umod::SCode.Mod
                  local mod_1::DAE.Mod
                  local compMod::DAE.Mod
                  local fullMod::DAE.Mod
                  local selectedMod::DAE.Mod
                  local cmod::DAE.Mod
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inSCodeElementLst, mods) begin
                  (cache, env,  nil(), _)  => begin
                    (cache, env, nil)
                  end

                  (cache, env, (SCode.COMPONENT(id, SCode.PREFIXES(_, redecl, f && SCode.FINAL(__), io, repl), SCode.ATTR(d, ct, prl, var, _, isf), tp, mod, comment, cond, info), cmod) <| rest, _)  => begin
                      (cache, mod_1) = Mod.elabMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), mod, true, Mod.COMPONENT(id), info)
                      mod_1 = Mod.myMerge(mods, mod_1)
                      compMod = Mod.lookupCompModification(mod_1, id)
                      fullMod = mod_1
                      selectedMod = selectModifier(compMod, fullMod)
                      (cache, cmod) = Mod.updateMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), cmod, true, info)
                      selectedMod = Mod.myMerge(cmod, selectedMod)
                      umod = Mod.unelabMod(selectedMod)
                      (cache, env, res) = buildRecordConstructorElts(cache, env, rest, mods)
                      dir = Absyn.BIDIR()
                      vis = SCode.PROTECTED()
                    (cache, env, _cons(SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, f, io, repl), SCode.ATTR(d, ct, prl, var, dir, isf), tp, umod, comment, cond, info), res))
                  end

                  (cache, env, (SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, _, io, repl), SCode.ATTR(d, ct, prl, SCode.CONST(__), _, isf), tp, mod && SCode.NOMOD(__), comment, cond, info), cmod) <| rest, _)  => begin
                      (cache, mod_1) = Mod.elabMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), mod, true, Mod.COMPONENT(id), info)
                      mod_1 = Mod.myMerge(mods, mod_1)
                      compMod = Mod.lookupCompModification(mod_1, id)
                      fullMod = mod_1
                      selectedMod = selectModifier(compMod, fullMod)
                      (cache, cmod) = Mod.updateMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), cmod, true, info)
                      selectedMod = Mod.myMerge(cmod, selectedMod)
                      umod = Mod.unelabMod(selectedMod)
                      (cache, env, res) = buildRecordConstructorElts(cache, env, rest, mods)
                      var = SCode.VAR()
                      dir = Absyn.INPUT()
                      vis = SCode.PUBLIC()
                      f = SCode.NOT_FINAL()
                    (cache, env, _cons(SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, f, io, repl), SCode.ATTR(d, ct, prl, var, dir, isf), tp, umod, comment, cond, info), res))
                  end

                  (cache, env, (SCode.COMPONENT(id, SCode.PREFIXES(_, redecl, f, io, repl), SCode.ATTR(d, ct, prl, var && SCode.CONST(__), _, isf), tp, mod, comment, cond, info), cmod) <| rest, _)  => begin
                      (cache, mod_1) = Mod.elabMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), mod, true, Mod.COMPONENT(id), info)
                      mod_1 = Mod.myMerge(mods, mod_1)
                      compMod = Mod.lookupCompModification(mod_1, id)
                      fullMod = mod_1
                      selectedMod = selectModifier(compMod, fullMod)
                      (cache, cmod) = Mod.updateMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), cmod, true, info)
                      selectedMod = Mod.myMerge(cmod, selectedMod)
                      umod = Mod.unelabMod(selectedMod)
                      (cache, env, res) = buildRecordConstructorElts(cache, env, rest, mods)
                      dir = Absyn.BIDIR()
                      vis = SCode.PROTECTED()
                    (cache, env, _cons(SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, f, io, repl), SCode.ATTR(d, ct, prl, var, dir, isf), tp, umod, comment, cond, info), res))
                  end

                  (cache, env, (SCode.COMPONENT(id, SCode.PREFIXES(_, redecl, _, io, repl), SCode.ATTR(d, ct, prl, _, _, isf), tp, mod, comment, cond, info), cmod) <| rest, _)  => begin
                      (cache, mod_1) = Mod.elabMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), mod, true, Mod.COMPONENT(id), info)
                      mod_1 = Mod.myMerge(mods, mod_1)
                      compMod = Mod.lookupCompModification(mod_1, id)
                      fullMod = mod_1
                      selectedMod = selectModifier(compMod, fullMod)
                      (cache, cmod) = Mod.updateMod(cache, env, InnerOuterTypes.emptyInstHierarchy, Prefix.NOPRE(), cmod, true, info)
                      selectedMod = Mod.myMerge(cmod, selectedMod)
                      umod = Mod.unelabMod(selectedMod)
                      (cache, env, res) = buildRecordConstructorElts(cache, env, rest, mods)
                      var = SCode.VAR()
                      vis = SCode.PUBLIC()
                      f = SCode.NOT_FINAL()
                      dir = Absyn.INPUT()
                    (cache, env, _cons(SCode.COMPONENT(id, SCode.PREFIXES(vis, redecl, f, io, repl), SCode.ATTR(d, ct, prl, var, dir, isf), tp, umod, comment, cond, info), res))
                  end

                  (_, _, (comp, cmod) <| _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Lookup.buildRecordConstructorElts failed " + SCodeDump.unparseElementStr(comp, SCodeDump.defaultOptions) + " with mod: " + Mod.printModStr(cmod) + " and: " + Mod.printModStr(mods))
                    fail()
                  end
                end
              end
               #=  final becomes protected, Modelica Spec 3.2, Section 12.6, Record Constructor Functions, page 140
               =#
               #=  adrpo: this was wrong, you won't find any id modification there!!!
               =#
               #=  bjozac: This was right, you will find id modification unless modifers does not belong to component!
               =#
               #=  adrpo 2009-11-23 -> solved by selecting the full modifier if the component modifier is empty!
               =#
               #=  if the first one is empty use the other one.
               =#
               #=  - Prefixes (constant, parameter, final, discrete, input, output, ...) of the remaining record components are removed.
               =#
               #=  adrpo: 2010-11-09 : TODO! FIXME! why is this?? keep the variability!
               =#
               #=  mahge: 2013-01-15 : direction should be set to bidir.
               =#
               #=  var = SCode.VAR();
               =#
               #=  constants become protected, Modelica Spec 3.2, Section 12.6, Record Constructor Functions, page 140
               =#
               #=  mahge: 2013-01-15 : only if they have bindings. otherwise they are still modifiable.
               =#
               #=  adrpo: this was wrong, you won't find any id modification there!!!
               =#
               #=  bjozac: This was right, you will find id modification unless modifers does not belong to component!
               =#
               #=  adrpo 2009-11-23 -> solved by selecting the full modifier if the component modifier is empty!
               =#
               #=  if the first one is empty use the other one.
               =#
               #=  - Prefixes (constant, parameter, final, discrete, input, output, ...) of the remaining record components are removed.
               =#
               #=  adrpo: 2010-11-09 : TODO! FIXME! why is this?? keep the variability!
               =#
               #=  adrpo: this was wrong, you won't find any id modification there!!!
               =#
               #=  bjozac: This was right, you will find id modification unless modifers does not belong to component!
               =#
               #=  adrpo 2009-11-23 -> solved by selecting the full modifier if the component modifier is empty!
               =#
               #=  if the first one is empty use the other one.
               =#
               #=  - Prefixes (constant, parameter, final, discrete, input, output, ...) of the remaining record components are removed.
               =#
               #=  adrpo: 2010-11-09 : TODO! FIXME! why is this?? keep the variability!
               =#
               #=  mahge: 2013-01-15 : direction should be set to bidir.
               =#
               #=  var = SCode.VAR();
               =#
               #=  all others, add input see Modelica Spec 3.2, Section 12.6, Record Constructor Functions, page 140
               =#
               #=  adrpo: this was wrong, you won't find any id modification there!!!
               =#
               #=  bjozac: This was right, you will find id modification unless modifers does not belong to component!
               =#
               #=  adrpo 2009-11-23 -> solved by selecting the full modifier if the component modifier is empty!
               =#
               #=  if the first one is empty use the other one.
               =#
               #=  - Prefixes (constant, parameter, final, discrete, input, output, ...) of the remaining record components are removed.
               =#
               #=  adrpo: 2010-11-09 : TODO! FIXME! why is this?? keep the variability!
               =#
          (outCache, outEnv, outSCodeElementLst)
        end

         #= This function builds the result element of a
          record constructor function, i.e. the returned variable =#
        function buildRecordConstructorResultElt(elts::List{<:SCode.Element}, id::SCode.Ident, env::FCore.Graph, info::SourceInfo) ::SCode.Element
              local outElement::SCode.Element

               #= print(\" creating element of type: \" + id + \"\\n\");
               =#
               #= print(\" with generated mods:\" + SCodeUtil.printSubs1Str(submodlst) + \"\\n\");
               =#
               #= print(\" creating element of type: \" + id + \"\\n\");
               =#
               #= print(\" with generated mods:\" + SCodeUtil.printSubs1Str(submodlst) + \"\\n\");
               =#
              outElement = SCode.COMPONENT("result", SCode.defaultPrefixes, SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.OUTPUT(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(id), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), info)
          outElement
        end

         #= Helper function to lookupClass2. Searches the environment for the class.
          It first checks the current scope, and then base classes. The specification
          says that we first search elements in the current scope (+ the ones inherited
          from base classes) =#
        function lookupClassInEnv(inCache::FCore.Cache, inEnv::FCore.Graph, id::String, inPrevFrames::FCore.Scope, inState::MutableType #= {<:Bool} =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local c::SCode.Element
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local fs::FCore.Graph
                  local i_env::FCore.Graph
                  local prevFrames::FCore.Scope
                  local frame::FCore.Node
                  local r::FCore.MMRef
                  local rs::FCore.Scope
                  local sid::String
                  local scope::String
                  local cache::FCore.Cache
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, id, inPrevFrames, inState, inInfo) begin
                  (cache, env && FCore.G(scope = r <| _), _, prevFrames, _, _)  => begin
                      frame = FNode.fromRef(r)
                      (cache, c, env_1, prevFrames) = lookupClassInFrame(cache, frame, env, id, prevFrames, inState, inInfo)
                      Mutable.update(inState, true)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, env && FCore.G(scope = r <| _), _, prevFrames, _, _)  => begin
                      @match false = FNode.isRefTop(r)
                      frame = FNode.fromRef(r)
                      sid = FNode.refName(r)
                      @match true = FNode.isEncapsulated(frame)
                      @match true = stringEq(id, sid) #= Special case if looking up the class that -is- encapsulated. That must be allowed. =#
                      (env, _) = FGraphUtil.stripLastScopeRef(env)
                      (cache, c, env, prevFrames) = lookupClassInEnv(cache, env, id, _cons(r, prevFrames), inState, inInfo)
                      Mutable.update(inState, true)
                    (cache, c, env, prevFrames)
                  end

                  (cache, env && FCore.G(scope = r <| _), _, _, _, SOME(info))  => begin
                      @match false = FNode.isRefTop(r)
                      frame = FNode.fromRef(r)
                      @match true = FNode.isEncapsulated(frame)
                      i_env = FGraphUtil.topScope(env)
                      @shouldFail (_, _, _, _) = lookupClassInEnv(cache, i_env, id, nil, inState, NONE())
                      scope = FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.LOOKUP_ERROR, list(id, scope), info)
                    fail()
                  end

                  (cache, env && FCore.G(scope = r <| _), _, prevFrames, _, _)  => begin
                      frame = FNode.fromRef(r)
                      @match true = FNode.isEncapsulated(frame)
                      i_env = FGraphUtil.topScope(env)
                      (cache, c, env_1, prevFrames) = lookupClassInEnv(cache, i_env, id, nil, inState, inInfo)
                      Mutable.update(inState, true)
                    (cache, c, env_1, prevFrames)
                  end

                  (cache, env && FCore.G(scope = r <| _), _, prevFrames, _, _)  => begin
                      @match false = FNode.isRefTop(r)
                      frame = FNode.fromRef(r)
                      @match false = FNode.isEncapsulated(frame)
                      @match false = Mutable.access(inState)
                      (env, _) = FGraphUtil.stripLastScopeRef(env)
                      (cache, c, env_1, prevFrames) = lookupClassInEnv(cache, env, id, _cons(r, prevFrames), inState, inInfo)
                      Mutable.update(inState, true)
                    (cache, c, env_1, prevFrames)
                  end
                end
              end
               #=  lookup stops at encapsulated classes except for builtin
               =#
               #=  scope, if not found in builtin scope, error
               =#
               #=  lookup stops at encapsulated classes, except for builtin scope
               =#
               #=  if not found and not encapsulated, and no ident has been previously found, look in next enclosing scope
               =#
          (outCache, outClass, outEnv, outPrevFrames)
        end

         #= Search for a class within one frame. =#
        function lookupClassInFrame(inCache::FCore.Cache, inFrame::FCore.Node, inEnv::FCore.Graph, inIdent::SCode.Ident, inPrevFrames::FCore.Scope, inState::MutableType #= {<:Bool} =#, inInfo::Option{<:SourceInfo}) ::Tuple{FCore.Cache, SCode.Element, FCore.Graph, FCore.Scope}
              local outPrevFrames::FCore.Scope
              local outEnv::FCore.Graph
              local outClass::SCode.Element
              local outCache::FCore.Cache

              (outCache, outClass, outEnv, outPrevFrames) = begin
                  local c::SCode.Element
                  local totenv::FCore.Graph
                  local env_1::FCore.Graph
                  local prevFrames::FCore.Scope
                  local r::FCore.MMRef
                  local sid::Option{String}
                  local ht::FCore.Children
                  local name::String
                  local qimports::List{Absyn.Import}
                  local uqimports::List{Absyn.Import}
                  local cache::FCore.Cache
                  local unique::Bool
                   #=  Check this scope for class
                   =#
                @matchcontinue (inCache, inFrame, inEnv, inIdent, inPrevFrames, inState) begin
                  (cache, FCore.N(children = ht), totenv, name, prevFrames, _)  => begin
                      r = FCore.RefTree.get(ht, name)
                      @match FCore.N(data = FCore.CL(e = c)) = FNode.fromRef(r)
                    (cache, c, totenv, prevFrames)
                  end

                  (cache, _, totenv, name, _, _)  => begin
                      (qimports, uqimports) = FNode.imports(inFrame)
                      _ = begin
                        @matchcontinue (qimports, uqimports) begin
                          (_ <| _, _)  => begin
                              (cache, c, env_1, prevFrames) = lookupQualifiedImportedClassInFrame(cache, qimports, totenv, name, inState, inInfo)
                            ()
                          end

                          (_, _ <| _)  => begin
                              (cache, c, env_1, prevFrames, unique) = lookupUnqualifiedImportedClassInFrame(cache, uqimports, totenv, name, inInfo)
                              Mutable.update(inState, true)
                              reportSeveralNamesError(unique, name)
                            ()
                          end
                        end
                      end
                    (cache, c, env_1, prevFrames)
                  end
                end
              end
               #=  Search in imports
               =#
               #=  Search among the qualified imports, e.g. import A.B; or import D=A.B;
               =#
               #=  Search among the unqualified imports, e.g. import A.B.*;
               =#
          (outCache, outClass, outEnv, outPrevFrames)
        end

         #= given a boolean, report error message of importing several names
        if boolean flag is false and fail. If flag is true succeed and do nothing. =#
        function reportSeveralNamesError(unique::Bool, name::String)
              _ = begin
                @match (unique, name) begin
                  (true, _)  => begin
                    ()
                  end

                  (false, _)  => begin
                      Error.addMessage(Error.IMPORT_SEVERAL_NAMES, list(name))
                    ()
                  end
                end
              end
        end

         #= Helper function to lookupVarF and lookupIdent. =#
        function lookupVar2(inBinTree::FCore.Children, inIdent::SCode.Ident, inGraph::FCore.Graph) ::Tuple{DAE.Var, SCode.Element, DAE.Mod, FCore.Status, FCore.Graph}
              local outEnv::FCore.Graph
              local instStatus::FCore.Status
              local outMod::DAE.Mod
              local outElement::SCode.Element
              local outVar::DAE.Var

              local r::FCore.MMRef
              local s::FCore.Scope
              local n::FCore.Node
              local name::String

              r = FCore.RefTree.get(inBinTree, inIdent)
              outVar = FNode.refInstVar(r)
              s = FNode.refRefTargetScope(r)
              n = FNode.fromRef(r)
              if ! FNode.isComponent(n) && Flags.isSet(Flags.LOOKUP)
                @match false = Config.acceptMetaModelicaGrammar()
                @match FCore.N(data = FCore.CL(e = SCode.CLASS(name = name))) = n
                name = inIdent + " = " + FGraphUtil.printGraphPathStr(inGraph) + "." + name
                Debug.traceln("- Lookup.lookupVar2 failed because we found a class instead of a variable: " + name)
                fail()
              end
               #=  MetaModelica function references generate too much failtrace...
               =#
              @match FCore.N(data = FCore.CO(outElement, outMod, _, instStatus)) = n
              outEnv = FGraphUtil.setScope(inGraph, s)
          (outVar, outElement, outMod, instStatus, outEnv)
        end

         #= This function checks a list of subscripts agains type, and removes
          dimensions from the type according to the subscripting. =#
        function checkSubscripts(inType::DAE.Type, inExpSubscriptLst::List{<:DAE.Subscript}) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::DAE.Type
                  local t_1::DAE.Type
                  local dim::DAE.Dimension
                  local sub::DAE.Subscript
                  local ys::List{DAE.Subscript}
                  local s::List{DAE.Subscript}
                  local sz::ModelicaInteger
                  local ind::ModelicaInteger
                  local dim_int::ModelicaInteger
                  local step::ModelicaInteger
                  local se::List{DAE.Exp}
                  local e::DAE.Exp
                   #=  empty case
                   =#
                @matchcontinue (inType, inExpSubscriptLst) begin
                  (t,  nil())  => begin
                    t
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.WHOLEDIM(__) <| ys)  => begin
                      t_1 = checkSubscripts(t, ys)
                    DAE.T_ARRAY(t_1, list(dim))
                  end

                  (DAE.T_ARRAY(dims = _ <|  nil(), ty = t), DAE.SLICE(exp = e && DAE.RANGE(__)) <| ys)  => begin
                      t_1 = checkSubscripts(t, ys)
                      dim_int = Expression.rangeSize(e)
                    DAE.T_ARRAY(t_1, list(DAE.DIM_INTEGER(dim_int)))
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.SLICE(exp = DAE.ARRAY(array = se)) <| ys)  => begin
                      _ = Expression.dimensionSize(dim)
                      t_1 = checkSubscripts(t, ys)
                      dim_int = listLength(se) #= FIXME: Check range IMPLEMENTED 2007-05-18 BZ =#
                    DAE.T_ARRAY(t_1, list(DAE.DIM_INTEGER(dim_int)))
                  end

                  (DAE.T_ARRAY(dims = _ <|  nil(), ty = t), DAE.SLICE(exp = e) <| ys)  => begin
                      @match DAE.T_ARRAY(dims = list(dim)) = Expression.typeof(e)
                      t_1 = checkSubscripts(t, ys)
                    DAE.T_ARRAY(t_1, list(dim))
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.INDEX(exp = DAE.ICONST(integer = ind)) <| ys)  => begin
                      sz = Expression.dimensionSize(dim)
                      if ! ind > 0
                        fail()
                      end
                      if ! ind <= sz
                        fail()
                      end
                      t_1 = checkSubscripts(t, ys)
                    t_1
                  end

                  (DAE.T_ARRAY(dims = dim <|  nil(), ty = t), DAE.INDEX(__) <| ys)  => begin
                      @match true = Expression.dimensionKnown(dim)
                      t_1 = checkSubscripts(t, ys)
                    t_1
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil(), ty = t), DAE.INDEX(__) <| ys)  => begin
                      t_1 = checkSubscripts(t, ys)
                    t_1
                  end

                  (DAE.T_ARRAY(dims = DAE.DIM_EXP(__) <|  nil(), ty = t), DAE.INDEX(__) <| ys)  => begin
                      t_1 = checkSubscripts(t, ys)
                    t_1
                  end

                  (DAE.T_ARRAY(ty = t), DAE.WHOLEDIM(__) <| ys)  => begin
                      t_1 = checkSubscripts(t, ys)
                    t_1
                  end

                  (DAE.T_SUBTYPE_BASIC(complexType = t), ys)  => begin
                    checkSubscripts(t, ys)
                  end

                  (t && DAE.T_UNKNOWN(__), _)  => begin
                    t
                  end

                  (DAE.T_METAARRAY(__), DAE.INDEX(__) <|  nil())  => begin
                    inType.ty
                  end

                  (DAE.T_METAARRAY(__), _ <|  nil())  => begin
                    inType
                  end

                  (t, s)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Lookup.checkSubscripts failed (tp: ")
                      Debug.trace(Types.printTypeStr(t))
                      Debug.trace(" subs:")
                      Debug.trace(stringDelimitList(ListUtil.map(s, ExpressionDump.printSubscriptStr), ","))
                      Debug.trace(")\\n")
                    fail()
                  end
                end
              end
               #=  HJ: Subscripts needn't be constant. No range-checking can be done
               =#
          outType
        end

         #= This function looks in a frame to find a declared variable.  If
          the name being looked up is qualified, the first part of the name
          is looked up, and lookupVar2 is used to for further lookup in
          the result of that lookup.
          2007-05-29 If we can construct a expression, we do after expanding the
          subscript with dimensions to fill the Cref. =#
        function lookupVarF(inCache::FCore.Cache, inBinTree::FCore.Children, inComponentRef::DAE.ComponentRef, inEnv::FCore.Graph) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, String}
              local name::String
              local outComponentEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData
              local constOfForIteratorRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local outBinding::DAE.Binding
              local outType::DAE.Type
              local outAttributes::DAE.Attributes
              local outCache::FCore.Cache

              (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outComponentEnv, name) = begin
                  local id::String
                  local id2::String
                  local ct::DAE.ConnectorType
                  local prl::SCode.Parallelism
                  local vt::SCode.Variability
                  local vt2::SCode.Variability
                  local di::Absyn.Direction
                  local ty::DAE.Type
                  local ty_1::DAE.Type
                  local idTp::DAE.Type
                  local ty2_2::DAE.Type
                  local tyParent::DAE.Type
                  local tyChild::DAE.Type
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local bind::DAE.Binding
                  local binding::DAE.Binding
                  local parentBinding::DAE.Binding
                  local ht::FCore.Children
                  local ss::List{DAE.Subscript}
                  local componentEnv::FCore.Graph
                  local ids::DAE.ComponentRef
                  local cache::FCore.Cache
                  local io::Absyn.InnerOuter
                  local texp::Option{DAE.Exp}
                  local xCref::DAE.ComponentRef
                  local tCref::DAE.ComponentRef
                  local cref_::DAE.ComponentRef
                  local ltCref::List{DAE.ComponentRef}
                  local splicedExp::DAE.Exp
                  local eType::DAE.Type
                  local tty::DAE.Type
                  local cnstForRange::Option{DAE.Const}
                  local vis::SCode.Visibility
                  local attr::DAE.Attributes
                  local fields::List{DAE.Var}
                  local oSplicedExp::Option{DAE.Exp}
                  local p::Absyn.Path
                   #=  Simple identifier
                   =#
                @match (inCache, inBinTree, inComponentRef, inEnv) begin
                  (_, _, DAE.CREF_IDENT(ident = id, subscriptLst = ss), _)  => begin
                      (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outComponentEnv, name) = lookupVarFIdent(inCache, inBinTree, id, ss, inEnv)
                    (outCache, outAttributes, outType, outBinding, constOfForIteratorRange, splicedExpData, outComponentEnv, name)
                  end

                  (cache, ht, DAE.CREF_QUAL(ident = id, subscriptLst = ss, componentRef = ids), _)  => begin
                       #=  Qualified variables looked up through component environment with or without spliced exp
                       =#
                      @match (DAE.TYPES_VAR(_, DAE.ATTR(variability = vt2), tyParent, parentBinding, _), _, _, _, componentEnv) = lookupVar2(ht, id, inEnv)
                       #=  leave just the last scope from component env as it SHOULD BE ONLY THERE, i.e. don't go on searching the parents!
                       =#
                       #=  componentEnv = FGraphUtil.setScope(componentEnv, List.create(FGraphUtil.lastScopeRef(componentEnv)));
                       =#
                      (attr, ty, binding, cnstForRange, componentEnv, name) = begin
                        @match tyParent begin
                          DAE.T_METAARRAY(__)  => begin
                              @match true = listLength(Types.getDimensions(tyParent)) == listLength(ss)
                              (cache, attr, ty, binding, cnstForRange, name) = lookupVarFMetaModelica(cache, componentEnv, ids, Types.metaArrayElementType(tyParent))
                              splicedExpData = InstTypes.SPLICEDEXPDATA(NONE(), ty)
                            (attr, ty, binding, cnstForRange, componentEnv, name)
                          end

                          _ where (Types.isBoxedType(tyParent) && ! Types.isUnknownType(tyParent))  => begin
                              @match nil = ss
                              (cache, attr, ty, binding, cnstForRange, name) = lookupVarFMetaModelica(cache, componentEnv, ids, tyParent)
                              splicedExpData = InstTypes.SPLICEDEXPDATA(NONE(), ty)
                            (attr, ty, binding, cnstForRange, componentEnv, name)
                          end

                          _  => begin
                                @match (cache, DAE.ATTR(ct, prl, vt, di, io, vis), tyChild, binding, cnstForRange, InstTypes.SPLICEDEXPDATA(texp, idTp), _, componentEnv, name) = lookupVar(cache, componentEnv, ids)
                                ltCref = elabComponentRecursive(texp)
                                ty = tyChild
                                 #=  In case it's an unspliced expression
                                 =#
                                oSplicedExp = begin
                                  @match ltCref begin
                                    tCref <| _  => begin
                                         #=  with a spliced exp
                                         =#
                                        ty1 = checkSubscripts(tyParent, ss)
                                        ty = sliceDimensionType(ty1, tyChild)
                                        ty2_2 = Types.simplifyType(tyParent)
                                        ss = addArrayDimensions(ty2_2, ss)
                                        xCref = CrefForHashTable.makeCrefQual(id, ty2_2, ss, tCref)
                                        eType = Types.simplifyType(ty)
                                        splicedExp = Expression.makeCrefExp(xCref, eType)
                                      SOME(splicedExp)
                                    end

                                     nil()  => begin
                                      NONE()
                                    end
                                  end
                                end
                                 #=  without spliced Expression
                                 =#
                                vt = SCodeUtil.variabilityOr(vt, vt2)
                                binding = lookupBinding(inComponentRef, tyParent, ty, parentBinding, binding)
                                splicedExpData = InstTypes.SPLICEDEXPDATA(oSplicedExp, idTp)
                              (DAE.ATTR(ct, prl, vt, di, io, vis), ty, binding, cnstForRange, componentEnv, name)
                          end
                        end
                      end
                    (cache, attr, ty, binding, cnstForRange, splicedExpData, componentEnv, name)
                  end
                end
              end
          (outCache, outAttributes, outType, outBinding, constOfForIteratorRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData, outComponentEnv, name)
        end

         #= This function looks in a frame to find a declared variable.  If
          the name being looked up is qualified, the first part of the name
          is looked up, and lookupVar2 is used to for further lookup in
          the result of that lookup.
          2007-05-29 If we can construct a expression, we do after expanding the
          subscript with dimensions to fill the Cref. =#
        function lookupVarFIdent(cache::FCore.Cache, ht::FCore.Children, ident::String, ss::List{<:DAE.Subscript}, inEnv::FCore.Graph) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, InstTypes.SplicedExpData, FCore.Graph, String}
              local name::String
              local componentEnv::FCore.Graph
              local splicedExpData::InstTypes.SplicedExpData
              local cnstForRange::Option{DAE.Const} #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#
              local bind::DAE.Binding
              local ty_1::DAE.Type
              local attr::DAE.Attributes


              local tty::DAE.Type
              local ty::DAE.Type
              local ss_1::List{DAE.Subscript}

              @match (DAE.TYPES_VAR(name, attr, ty, bind, cnstForRange), _, _, _, componentEnv) = lookupVar2(ht, ident, inEnv)
              ty_1 = checkSubscripts(ty, ss)
              tty = Types.simplifyType(ty)
              ss_1 = addArrayDimensions(tty, ss)
              splicedExpData = InstTypes.SPLICEDEXPDATA(SOME(Expression.makeCrefExp(CrefForHashTable.makeCrefIdent(ident, tty, ss_1), tty)), ty)
          (cache, attr, ty_1, bind, cnstForRange #= SOME(constant-ness) of the range if this is a for iterator, NONE() if this is not a for iterator =#, splicedExpData, componentEnv, name)
        end

        function lookupVarFMetaModelica(inCache::FCore.Cache, inEnv::FCore.Graph, cr::DAE.ComponentRef, inType::DAE.Type) ::Tuple{FCore.Cache, DAE.Attributes, DAE.Type, DAE.Binding, Option{DAE.Const}, String}
              local name::String
              local cnstForRange::Option{DAE.Const}
              local binding::DAE.Binding
              local ty::DAE.Type
              local attr::DAE.Attributes
              local cache::FCore.Cache = inCache

              (attr, ty, binding, cnstForRange, name) = begin
                  local fields::List{DAE.Var}
                  local p::Absyn.Path
                  local tt::DAE.Type
                @match cr begin
                  DAE.CREF_IDENT(__)  => begin
                      fields = Types.getMetaRecordFields(inType)
                      @match DAE.TYPES_VAR(name, attr, ty, binding, cnstForRange) = listGet(fields, Types.findVarIndex(cr.ident, fields) + 1)
                      for s in cr.subscriptLst
                        ty = begin
                          @match ty begin
                            DAE.T_METAARRAY(__)  => begin
                              ty.ty
                            end
                          end
                        end
                      end
                      ty = Types.getMetaRecordIfSingleton(ty)
                    (attr, ty, binding, cnstForRange, name)
                  end

                  DAE.CREF_QUAL(__)  => begin
                      fields = Types.getMetaRecordFields(inType)
                      @match DAE.TYPES_VAR(name, attr, ty, binding, cnstForRange) = listGet(fields, Types.findVarIndex(cr.ident, fields) + 1)
                      for s in cr.subscriptLst
                        ty = begin
                          @match ty begin
                            DAE.T_METAARRAY(__)  => begin
                              ty.ty
                            end
                          end
                        end
                      end
                      ty = Types.getMetaRecordIfSingleton(ty)
                      (cache, attr, ty, binding, cnstForRange, name) = lookupVarFMetaModelica(cache, inEnv, cr.componentRef, ty)
                    (attr, ty, binding, cnstForRange, name)
                  end
                end
              end
          (cache, attr, ty, binding, cnstForRange, name)
        end

         #= @author: adrpo
         this function uses the binding of the parent
         if the parent is an array of records =#
        function lookupBinding(inCref::DAE.ComponentRef, inParentType::DAE.Type, inChildType::DAE.Type, inParentBinding::DAE.Binding, inChildBinding::DAE.Binding) ::DAE.Binding
              local outBinding::DAE.Binding

              outBinding = begin
                  local tyElement::DAE.Type
                  local b::DAE.Binding
                  local e::DAE.Exp
                  local ov::Option{Values.Value}
                  local v::Values.Value
                  local c::DAE.Const
                  local s::DAE.BindingSource
                  local ss::List{DAE.Subscript}
                  local rest::DAE.ComponentRef
                  local id::String
                  local cId::String
                  local exps::List{DAE.Exp}
                  local comp::List{String}
                @matchcontinue (inCref, inParentType, inChildType, inParentBinding, inChildBinding) begin
                  (DAE.CREF_QUAL(_, _, ss, DAE.CREF_IDENT(cId, _,  nil())), _, _, DAE.EQBOUND(e, _, c, s), _)  => begin
                      @match true = Types.isArray(inParentType)
                      tyElement = Types.arrayElementType(inParentType)
                      @match true = Types.isRecord(tyElement)
                      @match DAE.RECORD(_, exps, comp, _) = Expression.subscriptExp(e, ss)
                      e = listGet(exps, ListUtil.position(cId, comp))
                      b = DAE.EQBOUND(e, NONE(), c, s)
                    b
                  end

                  (DAE.CREF_QUAL(_, _, ss, DAE.CREF_IDENT(cId, _,  nil())), _, _, DAE.VALBOUND(v, s), _)  => begin
                      @match true = Types.isArray(inParentType)
                      tyElement = Types.arrayElementType(inParentType)
                      @match true = Types.isRecord(tyElement)
                      e = ValuesUtil.valueExp(v)
                      @match DAE.RECORD(_, exps, comp, _) = Expression.subscriptExp(e, ss)
                      e = listGet(exps, ListUtil.position(cId, comp))
                      b = DAE.EQBOUND(e, NONE(), DAE.C_CONST(), s)
                    b
                  end

                  _  => begin
                      inChildBinding
                  end
                end
              end
               #=  print(\"CREF EB: \" + CrefForHashTable.printComponentRefStr(inCref) + \"\\nTyParent: \" + Types.printTypeStr(inParentType) + \"\\nParent:\\n\" + Types.printBindingStr(inParentBinding) + \"\\nChild:\\n\" + Types.printBindingStr(inChildBinding) + \"\\n\");
               =#
               #=  print(\"CREF EB RESULT: \" + CrefForHashTable.printComponentRefStr(inCref) + \"\\nBinding:\\n\" + Types.printBindingStr(b) + \"\\n\");
               =#
               #= /*
                  case (DAE.CREF_QUAL(id, _, ss, DAE.CREF_IDENT(cId, _, {})), _, _, DAE.EQBOUND(e, ov, c, s), _)
                    equation
                      true = Types.isArray(inParentType);
                      tyElement = Types.arrayElementType(inParentType);
                      true = Types.isRecord(tyElement);
                       e = Expression.makeCrefExp(inCref, Expression.typeof(e));
                       b = DAE.EQBOUND(e, NONE(), c, s);
                    then
                      inChildBinding;*/ =#
               #=  print(\"CREF VB: \" + CrefForHashTable.printComponentRefStr(inCref) + \"\\nTyParent: \" + Types.printTypeStr(inParentType) + \"\\nParent:\\n\" + Types.printBindingStr(inParentBinding) + \"\\nChild:\\n\" + Types.printBindingStr(inChildBinding) + \"\\n\");
               =#
               #=  print(\"CREF VB RESULT: \" + CrefForHashTable.printComponentRefStr(inCref) + \"\\nBinding:\\n\" + Types.printBindingStr(b) + \"\\n\");
               =#
               #= /*
                  case (DAE.CREF_QUAL(id, _, ss, DAE.CREF_IDENT(cId, _, {})), _, _, DAE.VALBOUND(v, s), _)
                    equation
                      true = Types.isArray(inParentType);
                      tyElement = Types.arrayElementType(inParentType);
                      true = Types.isRecord(tyElement);
                      e = Expression.makeCrefExp(inCref, inChildType);
                      b = DAE.EQBOUND(e, NONE(), DAE.C_CONST(), s);
                    then
                      inChildBinding;*/ =#
          outBinding
        end

         #=
        Helper function for lookupvarF, to return an ComponentRef if there is one. =#
        function elabComponentRecursive(oCref::Option{<:DAE.Exp}) ::List{DAE.ComponentRef}
              local lref::List{DAE.ComponentRef}

              lref = begin
                  local exp::Option{DAE.Exp}
                  local ecpr::DAE.ComponentRef
                   #=  expression is an unqualified component reference
                   =#
                @match oCref begin
                  SOME(DAE.CREF(ecpr && DAE.CREF_IDENT(_, _, _), _))  => begin
                    _cons(ecpr, nil)
                  end

                  SOME(DAE.CREF(ecpr && DAE.CREF_QUAL(_, _, _, _), _))  => begin
                    _cons(ecpr, nil)
                  end

                  _  => begin
                      nil
                  end
                end
              end
               #=  expression is an qualified component reference
               =#
          lref
        end

         #= This is the function where we add arrays representing the dimension of the type.
        In type {array 2[array 3 ]] Will generate 2 arrays. {1,2} and {1,2,3} =#
        function addArrayDimensions(tySub::DAE.Type, ss::List{<:DAE.Subscript}) ::List{DAE.Subscript}
              local outType::List{DAE.Subscript}

              outType = begin
                  local subs::List{DAE.Subscript}
                  local dims::DAE.Dimensions
                @matchcontinue (tySub, ss) begin
                  (_, _)  => begin
                      @match true = Types.isArray(tySub)
                      dims = Types.getDimensions(tySub)
                      subs = ListUtil.map(dims, makeDimensionSubscript)
                      subs = expandWholeDimSubScript(ss, subs)
                    subs
                  end

                  _  => begin
                      ss
                  end
                end
              end
               #=  non array, return
               =#
          outType
        end

         #= Creates a slice with all indices of the dimension. =#
        function makeDimensionSubscript(inDim::DAE.Dimension) ::DAE.Subscript
              local outSub::DAE.Subscript

              outSub = begin
                  local sz::ModelicaInteger
                  local expl::List{DAE.Exp}
                  local enum_name::Absyn.Path
                  local l::List{String}
                   #=  Special case when addressing array[0].
                   =#
                @match inDim begin
                  DAE.DIM_INTEGER(integer = 0)  => begin
                    DAE.SLICE(DAE.ARRAY(DAE.T_INTEGER_DEFAULT, true, list(DAE.ICONST(0))))
                  end

                  DAE.DIM_INTEGER(__)  => begin
                    DAE.SLICE(DAE.RANGE(DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(inDim.integer))), DAE.ICONST(1), NONE(), DAE.ICONST(inDim.integer)))
                  end

                  DAE.DIM_BOOLEAN(__)  => begin
                      expl = list(DAE.BCONST(false), DAE.BCONST(true))
                    DAE.SLICE(DAE.ARRAY(DAE.T_BOOL_DEFAULT, true, expl))
                  end

                  DAE.DIM_ENUM(enumTypeName = enum_name, literals = l)  => begin
                      expl = makeEnumLiteralIndices(enum_name, l, 1)
                    DAE.SLICE(DAE.ARRAY(DAE.T_ENUMERATION(NONE(), enum_name, l, nil, nil), true, expl))
                  end
                end
              end
               #=  Array with integer dimension.
               =#
               #=  Array with boolean dimension.
               =#
               #=  Array with enumeration dimension.
               =#
          outSub
        end

         #= Creates a list of enumeration literal expressions from an enumeration. =#
        function makeEnumLiteralIndices(enumTypeName::Absyn.Path, enumLiterals::List{<:String}, enumIndex::ModelicaInteger) ::List{DAE.Exp}
              local enumIndices::List{DAE.Exp}

              enumIndices = begin
                  local l::String
                  local ls::List{String}
                  local e::DAE.Exp
                  local expl::List{DAE.Exp}
                  local enum_type_name::Absyn.Path
                @match (enumTypeName, enumLiterals, enumIndex) begin
                  (_,  nil(), _)  => begin
                    nil
                  end

                  (_, l <| ls, _)  => begin
                      enum_type_name = AbsynUtil.joinPaths(enumTypeName, Absyn.IDENT(l))
                      e = DAE.ENUM_LITERAL(enum_type_name, enumIndex)
                      expl = makeEnumLiteralIndices(enumTypeName, ls, enumIndex + 1)
                    _cons(e, expl)
                  end
                end
              end
          enumIndices
        end

         #=  Function expandWholeDimSubScript
        This function replaces Wholedim(if possible) with the expanded dimension.
        If there exist a subscript, the subscript is used instead of the expanded dimension.
         =#
        function expandWholeDimSubScript(inSubs::List{<:DAE.Subscript}, inSlice::List{<:DAE.Subscript}) ::List{DAE.Subscript}
              local outSubs::List{DAE.Subscript}

              outSubs = begin
                  local sub1::DAE.Subscript
                  local sub2::DAE.Subscript
                  local subs1::List{DAE.Subscript}
                  local subs2::List{DAE.Subscript}
                   #=  If a for-iterator is used as subscript we get a cref subscript in inSubs,
                   =#
                   #=  but nothing in inSlice because it only contains integers (see
                   =#
                   #=  addArrayDimensions above). This case makes sure that for-iterators are
                   =#
                   #=  not lost here.
                   =#
                @matchcontinue (inSubs, inSlice) begin
                  (sub1 && DAE.INDEX(exp = DAE.CREF(__)) <| subs1, subs2)  => begin
                      subs2 = expandWholeDimSubScript(subs1, subs2)
                    _cons(sub1, subs2)
                  end

                  (_,  nil())  => begin
                    nil
                  end

                  ( nil(), subs2)  => begin
                    subs2
                  end

                  (DAE.WHOLEDIM(__) <| subs1, sub2 <| subs2)  => begin
                      subs2 = expandWholeDimSubScript(subs1, subs2)
                    _cons(sub2, subs2)
                  end

                  (sub1 <| subs1, _ <| subs2)  => begin
                      subs2 = expandWholeDimSubScript(subs1, subs2)
                    _cons(sub1, subs2)
                  end
                end
              end
          outSubs
        end

         #= Lifts an type to spcified dimension by type2
         =#
        function sliceDimensionType(inTypeD::DAE.Type, inTypeL::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local t::DAE.Type
                  local tOrg::DAE.Type
                  local dimensions::List{ModelicaInteger}
                  local dim2::DAE.Dimensions
                @match (inTypeD, inTypeL) begin
                  (t, tOrg)  => begin
                      dimensions = Types.getDimensionSizes(t)
                      dim2 = ListUtil.map(dimensions, Expression.intDimension)
                      dim2 = listReverse(dim2)
                      t = ListUtil.foldr(dim2, Types.liftArray, tOrg)
                    t
                  end
                end
              end
          outType
        end

         #= common function when looking up the type of a metarecord =#
        function buildMetaRecordType(inCache::FCore.Cache, inEnv::FCore.Graph, cdef::SCode.Element) ::Tuple{FCore.Cache, FCore.Graph, DAE.Type}
              local ftype::DAE.Type
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local id::String
              local env_1::FCore.Graph
              local env::FCore.Graph
              local utPath::Absyn.Path
              local path::Absyn.Path
              local index::ModelicaInteger
              local varlst::List{DAE.Var}
              local els::List{SCode.Element}
              local singleton::Bool
              local cache::FCore.Cache
              local typeVarsType::List{DAE.Type}
              local typeVars::List{String}

              @match SCode.CLASS(name = id, restriction = SCode.R_METARECORD(name = utPath, index = index, singleton = singleton, typeVars = typeVars), classDef = SCode.PARTS(elementLst = els)) = cdef
              env = FGraphUtil.openScope(inEnv, SCode.NOT_ENCAPSULATED(), id, SOME(FCore.CLASS_SCOPE()))
               #=  print(\"buildMetaRecordType \" + id + \" in scope \" + FGraphUtil.printGraphPathStr(env) + \"\\n\");
               =#
              (cache, utPath) = Inst.makeFullyQualified(inCache, env, utPath)
              path = AbsynUtil.joinPaths(utPath, Absyn.IDENT(id))
              (outCache, outEnv, _, _, _, _, _, varlst, _, _) = Inst.instElementList(cache, env, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), ClassInf.META_RECORD(Absyn.IDENT("")), ListUtil.map1(els, Util.makeTuple, DAE.NOMOD()), nil, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet, true)
              varlst = Types.boxVarLst(varlst)
               #=  for v in varlst loop print(Types.unparseType(v.ty)+\"\\n\"); end for;
               =#
              typeVarsType = list(DAE.T_METAPOLYMORPHIC(tv) for tv in typeVars)
              ftype = DAE.T_METARECORD(path, utPath, typeVarsType, index, varlst, singleton)
               #=  print(\"buildMetaRecordType \" + id + \" in scope \" + FGraphUtil.printGraphPathStr(env) + \" OK \" + Types.unparseType(ftype) +\"\\n\");
               =#
          (outCache, outEnv, ftype)
        end

         #= Looks up a cref and returns SOME(true) if it references an iterator,
           SOME(false) if it references an element in the current scope, and NONE() if
           the name couldn't be found in the current scope at all. =#
        function isIterator(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::DAE.ComponentRef) ::Tuple{Option{Bool}, FCore.Cache}
              local outCache::FCore.Cache
              local outIsIterator::Option{Bool}

              (outIsIterator, outCache) = begin
                  local id::String
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ht::FCore.Children
                  local res::Option{Bool}
                  local ic::Option{DAE.Const}
                  local ref::FCore.MMRef
                  local b::Bool
                   #=  Look in the current scope.
                   =#
                @matchcontinue (inCache, inEnv, inCref) begin
                  (cache, FCore.G(scope = ref <| _), _)  => begin
                      ht = FNode.children(FNode.fromRef(ref))
                       #=  Only look up the first part of the cref, we're only interested in if
                       =#
                       #=  it exists and if it's an iterator or not.
                       =#
                      id = CrefForHashTable.crefFirstIdent(inCref)
                      @match (DAE.TYPES_VAR(constOfForIteratorRange = ic), _, _, _, _) = lookupVar2(ht, id, inEnv)
                      b = isSome(ic)
                    (SOME(b), cache)
                  end

                  (cache, FCore.G(scope = ref <| _), _)  => begin
                       #=  If not found, look in the next scope only if the current scope is implicit.
                       =#
                      @match true = frameIsImplAddedScope(FNode.fromRef(ref))
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (res, cache) = isIterator(cache, env, inCref)
                    (res, cache)
                  end

                  _  => begin
                      (NONE(), inCache)
                  end
                end
              end
          (outIsIterator, outCache)
        end

        function isFunctionCallViaComponent(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path) ::Bool
              local yes::Bool

              yes = begin
                  local name::Absyn.Ident
                   #=  see if the first path ident is a component
                   =#
                   #=  we might have a component reference, i.e. world.gravityAcceleration
                   =#
                @matchcontinue (inCache, inEnv, inPath) begin
                  (_, _, Absyn.QUALIFIED(name, _))  => begin
                      ErrorExt.setCheckpoint("functionViaComponentRef10")
                      (_, _, _, _, _, _, _, _, _) = lookupVarIdent(inCache, inEnv, name, nil)
                      ErrorExt.rollBack("functionViaComponentRef10")
                    true
                  end

                  (_, _, Absyn.QUALIFIED(_, _))  => begin
                      ErrorExt.rollBack("functionViaComponentRef10")
                    fail()
                  end

                  _  => begin
                      false
                  end
                end
              end
          yes
        end

         #= Prefixes a spliced exp that contains a cref with another cref. =#
        function prefixSplicedExp(inCref::DAE.ComponentRef, inSplicedExp::InstTypes.SplicedExpData) ::InstTypes.SplicedExpData
              local outSplicedExp::InstTypes.SplicedExpData

              outSplicedExp = begin
                  local ety::DAE.Type
                  local ty::DAE.Type
                  local cref::DAE.ComponentRef
                @match inSplicedExp begin
                  InstTypes.SPLICEDEXPDATA(SOME(DAE.CREF(cref, ety)), ty)  => begin
                      cref = CrefForHashTable.joinCrefs(inCref, cref)
                    InstTypes.SPLICEDEXPDATA(SOME(DAE.CREF(cref, ety)), ty)
                  end

                  _  => begin
                      inSplicedExp
                  end
                end
              end
          outSplicedExp
        end

        function isArrayType(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path) ::Tuple{FCore.Cache, Bool}
              local outIsArray::Bool
              local outCache::FCore.Cache

              local el::SCode.Element
              local p::Absyn.Path
              local env::FCore.Graph

              try
                (outCache, el, env) = lookupClass(inCache, inEnv, inPath)
                outIsArray = begin
                  @match el begin
                    SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(arrayDim = SOME(_))))  => begin
                      true
                    end

                    SCode.CLASS(classDef = SCode.DERIVED(attributes = SCode.ATTR(arrayDims = _ <| _)))  => begin
                      true
                    end

                    SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = p)))  => begin
                        (outCache, outIsArray) = isArrayType(outCache, env, p)
                      outIsArray
                    end

                    _  => begin
                        false
                    end
                  end
                end
              catch
                outIsArray = false
              end
          (outCache, outIsArray)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  module InstFunction


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

        import Connect

        import ConnectionGraph

        import DAE

        import FCore

        import InnerOuter

        import InstTypes

        import Mod

        import Prefix

        import SCode

        import UnitAbsyn

        import Lookup

        import Inst

        import InstUtil

        import UnitAbsynBuilder

        import ElementSource

        import ListUtil

        import Types

        import Flags

        import FGraph

        import FNode

        import Debug

        import SCodeDump
        import SCodeUtil

        import Util

        import Config

        import DAEUtil

        import PrefixUtil

        import Error

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

        InstDims = List

         #= instantiate an external object.
         This is done by instantiating the destructor and constructor
         functions and create a DAE element containing these two. =#
        function instantiateExternalObject(inCache::FCore.Cache, inEnv::FCore.Graph #= environment =#, inIH::InnerOuter.InstHierarchy, els::List{<:SCode.Element} #= elements =#, inMod::DAE.Mod, impl::Bool, comment::SCode.Comment, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, ClassInf.State}
              local ciState::ClassInf.State
              local dae::DAE.DAElist #= resulting dae =#
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, dae, ciState) = begin
                  local destr::SCode.Element
                  local constr::SCode.Element
                  local env1::FCore.Graph
                  local cache::FCore.Cache
                  local className::Ident
                  local classNameFQ::Absyn.Path
                  local functp::DAE.Type
                  local fs::FCore.Graph
                  local fs1::FCore.Graph
                  local env::FCore.Graph
                  local r::FCore.Ref
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                   #=  Explicit instantiation, generate constructor and destructor and the function type.
                   =#
                @matchcontinue (inCache, inEnv, inIH, els, inMod, impl, comment, info) begin
                  (cache, env, ih, _, _, false, _, _)  => begin
                      className = FNode.refName(FGraph.lastScopeRef(env))
                      checkExternalObjectMod(inMod, className)
                      destr = SCodeUtil.getExternalObjectDestructor(els)
                      constr = SCodeUtil.getExternalObjectConstructor(els)
                      env = FGraph.mkClassNode(env, destr, Prefix.NOPRE(), inMod)
                      env = FGraph.mkClassNode(env, constr, Prefix.NOPRE(), inMod)
                      (cache, ih) = instantiateExternalObjectDestructor(cache, env, ih, destr)
                      (cache, ih, functp) = instantiateExternalObjectConstructor(cache, env, ih, constr)
                      @match SOME(classNameFQ) = FGraph.getScopePath(env)
                      (env, r) = FGraph.stripLastScopeRef(env)
                      env = FGraph.mkTypeNode(env, className, functp)
                      env = FGraph.pushScopeRef(env, r)
                      source = ElementSource.addElementSourcePartOfOpt(DAE.emptyElementSource, FGraph.getScopePath(env))
                      source = ElementSource.addCommentToSource(source, SOME(comment))
                      source = ElementSource.addElementSourceFileInfo(source, info)
                    (cache, env, ih, DAE.DAE(list(DAE.EXTOBJECTCLASS(classNameFQ, source))), ClassInf.EXTERNAL_OBJ(classNameFQ))
                  end

                  (cache, _, ih, _, _, true, _, _)  => begin
                      @match SOME(classNameFQ) = FGraph.getScopePath(inEnv)
                    (cache, inEnv, ih, DAE.emptyDae, ClassInf.EXTERNAL_OBJ(classNameFQ))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstFunction.instantiateExternalObject failed.\\n")
                      fail()
                  end
                end
              end
               #=  The external object classname is in top frame of environment.
               =#
               #=  Fully qualified classname
               =#
               #=  Extend the frame with the type, one frame up at the same place as the class.
               =#
               #=  set the  of this element
               =#
               #=  Implicit, do not instantiate constructor and destructor.
               =#
               #=  Fully qualified classname
               =#
               #=  failed
               =#
          (outCache, outEnv, outIH, dae #= resulting dae =#, ciState)
        end

         #= Checks that an external object instance does not have any modifiers. This is
           done because an external object may only have two elements, a constructor and
           a destructor, and there's no point in modifying these. =#
        function checkExternalObjectMod(inMod::DAE.Mod, inClassName::String)
              _ = begin
                  local id::DAE.Ident
                  local mod::DAE.Mod
                  local info::SourceInfo
                @match (inMod, inClassName) begin
                  (DAE.NOMOD(__), _)  => begin
                    ()
                  end

                  (DAE.MOD(subModLst =  nil()), _)  => begin
                    ()
                  end

                  (DAE.MOD(subModLst = DAE.NAMEMOD(ident = id, mod = mod) <| _), _)  => begin
                      info = Mod.getModInfo(mod)
                      Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(id, inClassName), info)
                    fail()
                  end
                end
              end
               #=  The modifier contains a list of submods. Print an error for the first one
               =#
               #=  to make it look like a normal modifier error.
               =#
        end

         #= instantiates the destructor function of an external object =#
        function instantiateExternalObjectDestructor(inCache::FCore.Cache, env::FCore.Graph, inIH::InnerOuter.InstHierarchy, cl::SCode.Element) ::Tuple{FCore.Cache, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outCache::FCore.Cache

              (outCache, outIH) = begin
                  local cache::FCore.Cache
                  local env1::FCore.Graph
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, env, inIH, cl) begin
                  (cache, _, ih, _)  => begin
                      (cache, _, ih) = implicitFunctionInstantiation(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), cl, nil)
                    (cache, ih)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstFunction.instantiateExternalObjectDestructor failed.\\n")
                      fail()
                  end
                end
              end
          (outCache, outIH)
        end

         #= instantiates the constructor function of an external object =#
        function instantiateExternalObjectConstructor(inCache::FCore.Cache, env::FCore.Graph, inIH::InnerOuter.InstHierarchy, cl::SCode.Element) ::Tuple{FCore.Cache, InnerOuter.InstHierarchy, DAE.Type}
              local outType::DAE.Type
              local outIH::InnerOuter.InstHierarchy
              local outCache::FCore.Cache

              (outCache, outIH, outType) = begin
                  local cache::FCore.Cache
                  local env1::FCore.Graph
                  local ty::DAE.Type
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, env, inIH, cl) begin
                  (cache, _, ih, _)  => begin
                      (cache, env1, ih) = implicitFunctionInstantiation(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), cl, nil)
                      (cache, ty, _) = Lookup.lookupType(cache, env1, Absyn.IDENT("constructor"), NONE())
                    (cache, ih, ty)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstFunction.instantiateExternalObjectConstructor failed.\\n")
                      fail()
                  end
                end
              end
          (outCache, outIH, outType)
        end

         #= This function instantiates a function, which is performed *implicitly*
          since the variables of a function should not be instantiated as for an
          ordinary class. =#
        function implicitFunctionInstantiation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inClass::SCode.Element, inInstDims::List{<:List{<:DAE.Dimension}}) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH) = begin
                  local ty1::DAE.Type
                  local env::FCore.Graph
                  local cenv::FCore.Graph
                  local fpath::Absyn.Path
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local c::SCode.Element
                  local n::String
                  local inst_dims::InstDims
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local funs::List{DAE.Function}
                  local fun::DAE.Function
                  local r::SCode.Restriction
                  local pPrefix::SCode.Partial
                @match (inCache, inEnv, inIH, inMod, inPrefix, inClass, inInstDims) begin
                  (cache, env, ih, mod, pre, c && SCode.CLASS(name = n, restriction = SCode.R_RECORD(_), partialPrefix = pPrefix), inst_dims)  => begin
                      (cache, c, cenv) = Lookup.lookupRecordConstructorClass(cache, env, Absyn.IDENT(n))
                      @match (cache, env, ih, list(DAE.FUNCTION(fpath, _, ty1, _, _, _, _, source, _))) = implicitFunctionInstantiation2(cache, cenv, ih, mod, pre, c, inst_dims, true)
                      fun = DAE.RECORD_CONSTRUCTOR(fpath, ty1, source)
                      cache = InstUtil.addFunctionsToDAE(cache, list(fun), pPrefix)
                    (cache, env, ih)
                  end

                  (cache, env, ih, mod, pre, c && SCode.CLASS(restriction = r, partialPrefix = pPrefix), inst_dims)  => begin
                      @shouldFail @match SCode.R_RECORD(_) = r
                      (cache, env, ih, funs) = implicitFunctionInstantiation2(cache, env, ih, mod, pre, c, inst_dims, false)
                      cache = InstUtil.addFunctionsToDAE(cache, funs, pPrefix)
                    (cache, env, ih)
                  end

                  (_, env, _, _, _, SCode.CLASS(name = n), _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.implicitFunctionInstantiation failed " + n)
                      Debug.traceln("  Scope: " + FGraph.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #=  fpath = AbsynUtil.makeFullyQualified(fpath);
               =#
               #=  handle failure
               =#
          (outCache, outEnv, outIH)
        end

         #= This function instantiates a function, which is performed *implicitly*
          since the variables of a function should not be instantiated as for an
          ordinary class. =#
        function implicitFunctionInstantiation2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inClass::SCode.Element, inInstDims::List{<:List{<:DAE.Dimension}}, instFunctionTypeOnly::Bool #= if true, do no additional checking of the function =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, List{DAE.Function}}
              local funcs::List{DAE.Function}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, funcs) = begin
                  local ty::DAE.Type
                  local ty1::DAE.Type
                  local st::ClassInf.State
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local tempenv::FCore.Graph
                  local cenv::FCore.Graph
                  local fpath::Absyn.Path
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local c::SCode.Element
                  local n::String
                  local inst_dims::InstDims
                  local vis::SCode.Visibility
                  local partialPrefix::SCode.Partial
                  local encapsulatedPrefix::SCode.Encapsulated
                  local scExtdecl::SCode.ExternalDecl
                  local extdecl::DAE.ExternalDecl
                  local restr::SCode.Restriction
                  local parts::SCode.ClassDef
                  local els::List{SCode.Element}
                  local funcnames::List{Absyn.Path}
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local daeElts::List{DAE.Element}
                  local resfns::List{DAE.Function}
                  local derFuncs::List{DAE.FunctionDefinition}
                  local info::SourceInfo
                  local inlineType::DAE.InlineType
                  local cd::SCode.ClassDef
                  local partialPrefixBool::Bool
                  local isImpure::Bool
                  local cmt::SCode.Comment
                  local funcRest::SCode.FunctionRestriction
                  local cs::InstTypes.CallingScope
                  local visibility::SCode.Visibility
                   #=  normal functions
                   =#
                @matchcontinue (inCache, inEnv, inIH, inMod, inPrefix, inClass, inInstDims, instFunctionTypeOnly) begin
                  (cache, env, ih, mod, pre, SCode.CLASS(classDef = cd, prefixes = SCode.PREFIXES(visibility = visibility), partialPrefix = partialPrefix, name = n, restriction = SCode.R_FUNCTION(funcRest), info = info), inst_dims, _)  => begin
                      @match false = SCodeUtil.isExternalFunctionRestriction(funcRest)
                      isImpure = SCodeUtil.isImpureFunctionRestriction(funcRest)
                      c = if Config.acceptMetaModelicaGrammar()
                            inClass
                          else
                            SCodeUtil.setClassPartialPrefix(SCode.NOT_PARTIAL(), inClass)
                          end
                      cs = if instFunctionTypeOnly
                            InstTypes.TYPE_CALL()
                          else
                            InstTypes.INNER_CALL()
                          end
                      @match (cache, cenv, ih, _, DAE.DAE(daeElts), _, ty, _, _, _) = Inst.instClass(cache, env, ih, UnitAbsynBuilder.emptyInstStore(), mod, pre, c, inst_dims, true, cs, ConnectionGraph.EMPTY, Connect.emptySet)
                      ListUtil.map2_0(daeElts, InstUtil.checkFunctionElement, false, info)
                      env_1 = env
                      (cache, fpath) = Inst.makeFullyQualifiedIdent(cache, env_1, n)
                      cmt = InstUtil.extractComment(daeElts)
                      derFuncs = InstUtil.getDeriveAnnotation(cd, cmt, fpath, cache, cenv, ih, pre, info)
                      cache = instantiateDerivativeFuncs(cache, env, ih, derFuncs, fpath, info)
                      ty1 = InstUtil.setFullyQualifiedTypename(ty, fpath)
                      checkExtObjOutput(ty1, info)
                      env_1 = FGraph.mkTypeNode(env_1, n, ty1)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre)
                      inlineType = InstUtil.commentIsInlineFunc(cmt)
                      partialPrefixBool = SCodeUtil.partialBool(partialPrefix)
                      daeElts = InstUtil.optimizeFunctionCheckForLocals(fpath, daeElts, NONE(), nil, nil, nil)
                      InstUtil.checkFunctionDefUse(daeElts, info)
                      if false && Config.acceptMetaModelicaGrammar() && ! instFunctionTypeOnly
                        InstUtil.checkFunctionInputUsed(daeElts, NONE(), AbsynUtil.pathString(fpath))
                      end
                    (cache, env_1, ih, list(DAE.FUNCTION(fpath, _cons(DAE.FUNCTION_DEF(list(e for e in daeElts if ! DAEUtil.isComment(e))), derFuncs), ty1, visibility, partialPrefixBool, isImpure, inlineType, source, SOME(cmt))))
                  end

                  (cache, env, ih, mod, pre, c && SCode.CLASS(partialPrefix = partialPrefix, prefixes = SCode.PREFIXES(visibility = visibility), name = n, restriction = restr && SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(isImpure)), classDef = cd && parts && SCode.PARTS(externalDecl = SOME(scExtdecl)), info = info, encapsulatedPrefix = encapsulatedPrefix), inst_dims, _)  => begin
                      @match (cache, cenv, ih, _, DAE.DAE(daeElts), _, ty, _, _, _) = Inst.instClass(cache, env, ih, UnitAbsynBuilder.emptyInstStore(), mod, pre, c, inst_dims, true, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, Connect.emptySet)
                      ListUtil.map2_0(daeElts, InstUtil.checkFunctionElement, true, info)
                      (cache, fpath) = Inst.makeFullyQualifiedIdent(cache, env, n)
                      cmt = InstUtil.extractComment(daeElts)
                      derFuncs = InstUtil.getDeriveAnnotation(cd, cmt, fpath, cache, env, ih, pre, info)
                      cache = instantiateDerivativeFuncs(cache, env, ih, derFuncs, fpath, info)
                      ty1 = InstUtil.setFullyQualifiedTypename(ty, fpath)
                      checkExtObjOutput(ty1, info)
                      env_1 = FGraph.mkTypeNode(cenv, n, ty1)
                      vis = SCode.PUBLIC()
                      (cache, tempenv, ih, _, _, _, _, _, _, _, _, _) = Inst.instClassdef(cache, env_1, ih, UnitAbsyn.noStore, mod, pre, ClassInf.FUNCTION(fpath, isImpure), n, parts, restr, vis, partialPrefix, encapsulatedPrefix, inst_dims, true, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, Connect.emptySet, NONE(), cmt, info) #= how to get this? impl =#
                      (cache, ih, extdecl) = instExtDecl(cache, tempenv, ih, n, scExtdecl, daeElts, ty1, true, pre, info) #= impl =#
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre)
                      partialPrefixBool = SCodeUtil.partialBool(partialPrefix)
                      InstUtil.checkExternalFunction(daeElts, extdecl, AbsynUtil.pathString(fpath))
                    (cache, env_1, ih, list(DAE.FUNCTION(fpath, _cons(DAE.FUNCTION_EXT(daeElts, extdecl), derFuncs), ty1, visibility, partialPrefixBool, isImpure, DAE.NO_INLINE(), source, SOME(cmt))))
                  end

                  (cache, env, ih, _, pre, SCode.CLASS(name = n, prefixes = SCode.PREFIXES(visibility = visibility), restriction = SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(isImpure)), classDef = SCode.OVERLOAD(pathLst = funcnames), cmt = cmt), _, _)  => begin
                      (cache, env, ih, resfns) = instOverloadedFunctions(cache, env, ih, pre, funcnames, inClass.info) #= Overloaded functions =#
                      (cache, fpath) = Inst.makeFullyQualifiedIdent(cache, env, n)
                      resfns = _cons(DAE.FUNCTION(fpath, list(DAE.FUNCTION_DEF(nil)), DAE.T_UNKNOWN_DEFAULT, visibility, true, isImpure, DAE.NO_INLINE(), DAE.emptyElementSource, SOME(cmt)), resfns)
                    (cache, env, ih, resfns)
                  end

                  (_, env, _, _, _, SCode.CLASS(name = n), _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.implicitFunctionInstantiation2 failed " + n)
                      Debug.traceln("  Scope: " + FGraph.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #=  External functions should also have their type in env, but no dae.
               =#
               #= env_11 = FGraph.mkClassNode(cenv,pre,mod,c);
               =#
               #=  Only created to be able to get FQ path.
               =#
               #=  (ty1,_) = Types.traverseType(ty1, -1, Types.makeExpDimensionsUnknown);
               =#
               #=  set the source of this element
               =#
               #=  Instantiate overloaded functions
               =#
               #=  handle failure
               =#
          (outCache, outEnv, outIH, funcs)
        end

         #= instantiates all functions found in derivative annotations so they are also added to the
        dae and can be generated code for in case they are required =#
        function instantiateDerivativeFuncs(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuter.InstHierarchy, funcs::List{<:DAE.FunctionDefinition}, path::Absyn.Path #= the function name itself, must be added to derivative functions mapping to be able to search upwards =#, info::SourceInfo) ::FCore.Cache
              local outCache::FCore.Cache

               #=  print(\"instantiate deriative functions for \"+AbsynUtil.pathString(path)+\"\\n\");
               =#
              outCache = instantiateDerivativeFuncs2(cache, env, ih, DAEUtil.getDerivativePaths(funcs), path, info)
               #=  print(\"instantiated derivative functions for \"+AbsynUtil.pathString(path)+\"\\n\");
               =#
          outCache
        end

         #= help function =#
        function instantiateDerivativeFuncs2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPaths::List{<:Absyn.Path}, path::Absyn.Path #= the function name itself, must be added to derivative functions mapping to be able to search upwards =#, info::SourceInfo) ::FCore.Cache
              local outCache::FCore.Cache

              outCache = begin
                  local funcs::List{DAE.Function}
                  local p::Absyn.Path
                  local cache::FCore.Cache
                  local cenv::FCore.Graph
                  local env::FCore.Graph
                  local ih::InstanceHierarchy
                  local cdef::SCode.Element
                  local paths::List{Absyn.Path}
                  local fun::String
                  local scope::String
                @matchcontinue (inCache, inEnv, inIH, inPaths, path, info) begin
                  (cache, _, _,  nil(), _, _)  => begin
                    cache
                  end

                  (cache, env, ih, p <| paths, _, _)  => begin
                      (cache, cdef, cenv) = Lookup.lookupClass(cache, env, p, SOME(info))
                      (cache, p) = Inst.makeFullyQualified(cache, cenv, p)
                      _ = begin
                        @matchcontinue () begin
                          ()  => begin
                              FCore.checkCachedInstFuncGuard(cache, p)
                            ()
                          end

                          _  => begin
                                cache = FCore.addCachedInstFuncGuard(cache, p)
                                (cache, _, ih, funcs) = implicitFunctionInstantiation2(cache, cenv, ih, DAE.NOMOD(), Prefix.NOPRE(), cdef, nil, false)
                                funcs = InstUtil.addNameToDerivativeMapping(funcs, path)
                                cache = FCore.addDaeFunction(cache, funcs)
                              ()
                          end
                        end
                      end
                    instantiateDerivativeFuncs2(cache, env, ih, paths, path, info)
                  end

                  _  => begin
                        @match _cons(p, _) = inPaths
                        fun = AbsynUtil.pathString(p)
                        scope = FGraph.printGraphPathStr(inEnv)
                        Error.addSourceMessage(Error.LOOKUP_FUNCTION_ERROR, list(fun, scope), info)
                      fail()
                  end
                end
              end
               #=  Skipped recursive calls (by looking in cache)
               =#
               #=  add to cache before instantiating, to break recursion for recursive definitions.
               =#
          outCache
        end

         #= author: PA
          When looking up a function type it is sufficient to only instantiate the input and output arguments of the function.
          The implicitFunctionInstantiation function will instantiate the function body, resulting in a DAE for the body.
          This function does not do that. Therefore this function is the only solution available for recursive functions,
          where the function body contain a call to the function itself.

          Extended 2007-06-29, BZ
          Now this function also handles Derived function. =#
        function implicitFunctionTypeInstantiation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inClass::SCode.Element) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH) = begin
                  local stripped_class::SCode.Element
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local id::String
                  local cn2::String
                  local p::SCode.Partial
                  local e::SCode.Encapsulated
                  local r::SCode.Restriction
                  local extDecl::Option{SCode.ExternalDecl}
                  local elts::List{SCode.Element}
                  local stripped_elts::List{SCode.Element}
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local annotationLst::List{SCode.Annotation}
                  local info::SourceInfo
                  local dae::DAE.DAElist
                  local funs::List{DAE.Function}
                  local cn::Absyn.Path
                  local fpath::Absyn.Path
                  local ad::Option{List{Absyn.Subscript}}
                  local mod1::SCode.Mod
                  local mod2::DAE.Mod
                  local cenv::FCore.Graph
                  local c::SCode.Element
                  local ty1::DAE.Type
                  local ty::DAE.Type
                  local prefixes::SCode.Prefixes
                  local cmt::SCode.Comment
                  local paths::List{Absyn.Path}
                   #=  For external functions, include everything essential
                   =#
                @matchcontinue (inCache, inEnv, inIH, inClass) begin
                  (cache, env, ih, SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(_)), classDef = SCode.PARTS(__)))  => begin
                      (cache, env_1, ih, funs) = implicitFunctionInstantiation2(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), inClass, nil, true)
                      cache = FCore.addDaeExtFunction(cache, funs)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, SCode.CLASS(name = id, prefixes = prefixes, encapsulatedPrefix = e, partialPrefix = p, restriction = r, classDef = SCode.PARTS(elementLst = elts, externalDecl = extDecl), cmt = cmt, info = info))  => begin
                      elts = ListUtil.select(elts, isElementImportantForFunction)
                      stripped_class = SCode.CLASS(id, prefixes, e, p, r, SCode.PARTS(elts, nil, nil, nil, nil, nil, nil, extDecl), cmt, info)
                      (cache, env_1, ih, _) = implicitFunctionInstantiation2(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), stripped_class, nil, true)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, SCode.CLASS(name = id, classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn), modifications = mod1), info = info))  => begin
                      @match (cache, (@match SCode.CLASS() = c), cenv) = Lookup.lookupClass(cache, env, cn)
                      (cache, mod2) = Mod.elabMod(cache, env, ih, Prefix.NOPRE(), mod1, false, Mod.DERIVED(cn), info)
                      (cache, _, ih, _, _, _, ty, _, _, _) = Inst.instClass(cache, cenv, ih, UnitAbsynBuilder.emptyInstStore(), mod2, Prefix.NOPRE(), c, nil, true, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, Connect.emptySet)
                      env_1 = env
                      (cache, fpath) = Inst.makeFullyQualifiedIdent(cache, env_1, id)
                      ty1 = InstUtil.setFullyQualifiedTypename(ty, fpath)
                      env_1 = FGraph.mkTypeNode(env_1, id, ty1)
                    (cache, env_1, ih)
                  end

                  (cache, env, ih, SCode.CLASS(classDef = SCode.OVERLOAD(__)))  => begin
                      (cache, env, ih, _) = implicitFunctionInstantiation2(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), inClass, nil, true)
                    (cache, env, ih)
                  end

                  (_, _, _, SCode.CLASS(name = id))  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.implicitFunctionTypeInstantiation failed " + id + "\\nenv: " + FGraph.getGraphNameStr(inEnv) + "\\nelelement: " + SCodeDump.unparseElementStr(inClass, SCodeDump.defaultOptions))
                    fail()
                  end
                end
              end
               #=  stripped_class = SCode.CLASS(id,prefixes,e,p,r,SCode.PARTS(elts,{},{},{},{},{},{},extDecl),cmt,info);
               =#
               #=  Only external functions are valid without an algorithm section...
               =#
               #=  The function type can be determined without the body. Annotations, restrictions and external decls need
               =#
               #=  to be preserved though (e.g parallel external functions have restrictions parallel_function not external function)
               =#
               #=  Maybe we need one more restriction type for those.
               =#
               #=  Only external functions are valid without an algorithm section...
               =#
               #=  cache = FCore.addDaeExtFunction(cache, funs);
               =#
               #=  Short class definitions.
               =#
               #=  Makes MultiBody gravityacceleration hacks shit itself
               =#
               #=  why would you want to do this: FGraph.mkClassNode(env,c); ?????
               =#
               #=  (cache,env_1,ih,_) = implicitFunctionInstantiation2(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), inClass, {}, true);
               =#
          (outCache, outEnv, outIH)
        end

         #= This function instantiates the functions in the overload list of a
          overloading function definition and register the function types using
          the overloaded name. It also creates dae elements for the functions. =#
        function instOverloadedFunctions(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, pre::Prefix.PrefixType, inAbsynPathLst::List{<:Absyn.Path}, inInfo::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, List{DAE.Function}}
              local outFns::List{DAE.Function}
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outFns) = begin
                  local env::FCore.Graph
                  local cenv::FCore.Graph
                  local c::SCode.Element
                  local id::String
                  local encflag::SCode.Encapsulated
                  local fn::Absyn.Path
                  local fns::List{Absyn.Path}
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local partialPrefix::SCode.Partial
                  local resfns1::List{DAE.Function}
                  local resfns2::List{DAE.Function}
                  local rest::SCode.Restriction
                @matchcontinue (inCache, inEnv, inIH, pre, inAbsynPathLst) begin
                  (cache, _, ih, _,  nil())  => begin
                    (cache, inEnv, ih, nil)
                  end

                  (cache, env, ih, _, fn <| fns)  => begin
                      @match (cache, (@match SCode.CLASS(restriction = rest) = c), cenv) = Lookup.lookupClass(cache, env, fn, SOME(inInfo))
                      @match true = SCodeUtil.isFunctionRestriction(rest)
                      (cache, env, ih, resfns1) = implicitFunctionInstantiation2(inCache, cenv, inIH, DAE.NOMOD(), pre, c, nil, false)
                      (cache, env, ih, resfns2) = instOverloadedFunctions(cache, env, ih, pre, fns, inInfo)
                    (cache, env, ih, listAppend(resfns1, resfns2))
                  end

                  (_, _, _, _, fn <| _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.instOverloaded_functions failed " + AbsynUtil.pathString(fn))
                    fail()
                  end
                end
              end
               #=  Instantiate each function, add its FQ name to the type, needed when deoverloading
               =#
               #=  print(\"instOvl: \" + AbsynUtil.pathString(fn) + \"\\n\");
               =#
               #=  failure
               =#
          (outCache, outEnv, outIH, outFns)
        end

         #= author: LS
          This function handles the external declaration. If there is an explicit
          call of the external function, the component references are looked up and
          inserted in the argument list, otherwise the input and output parameters
          are inserted in the argument list with their order. The return type is
          determined according to the specification; if there is a explicit call
          and a lhs, which must be an output parameter, the type of the function is
          that type. If no explicit call and only one output parameter exists, then
          this will be the return type of the function, otherwise the return type
          will be void. =#
        function instExtDecl(cache::FCore.Cache, env::FCore.Graph, iH::InnerOuter.InstHierarchy, name::String, inScExtDecl::SCode.ExternalDecl, inElements::List{<:DAE.Element}, funcType::DAE.Type, impl::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, InnerOuter.InstHierarchy, DAE.ExternalDecl}
              local daeextdecl::DAE.ExternalDecl



              local fname::String
              local lang::String
              local fargs::List{DAE.ExtArg}
              local rettype::DAE.ExtArg
              local ann::Option{SCode.Annotation}
              local extdecl::SCode.ExternalDecl = inScExtDecl

              ann = InstUtil.instExtGetAnnotation(extdecl)
              lang = InstUtil.instExtGetLang(extdecl)
              fname = InstUtil.instExtGetFname(extdecl, name)
              if ! InstUtil.isExtExplicitCall(extdecl)
                (fargs, rettype) = instExtMakeDefaultExternalCall(inElements, funcType, lang, info)
              else
                (cache, fargs) = InstUtil.instExtGetFargs(cache, env, extdecl, impl, pre, info)
                (cache, rettype) = InstUtil.instExtGetRettype(cache, env, extdecl, impl, pre, info)
              end
              daeextdecl = DAE.EXTERNALDECL(fname, fargs, rettype, lang, ann)
          (cache, iH, daeextdecl)
        end

         #=  This function generates a default explicit function call,
          when it is omitted. If only one output variable exists,
          the implicit call is equivalent to:
               external \\\"C\\\" output_var=func(input_var1, input_var2,...)
          with the input_vars in their declaration order. If several output
          variables exists, the implicit call is equivalent to:
              external \\\"C\\\" func(var1, var2, ...)
          where each var can be input or output. =#
        function instExtMakeDefaultExternalCall(elements::List{<:DAE.Element}, funcType::DAE.Type, lang::String, info::SourceInfo) ::Tuple{List{DAE.ExtArg}, DAE.ExtArg}
              local rettype::DAE.ExtArg
              local fargs::List{DAE.ExtArg}

              local ty::DAE.Type
              local singleOutput::Bool
              local cr::DAE.ComponentRef
              local e::DAE.Element

              fargs = nil
              if lang == "builtin"
                rettype = DAE.NOEXTARG()
                return (fargs, rettype)
              end
              (rettype, singleOutput) = begin
                @match funcType begin
                  DAE.T_FUNCTION(funcResultType = DAE.T_ARRAY(__))  => begin
                      if lang != "builtin"
                        Error.addSourceMessage(Error.EXT_FN_SINGLE_RETURN_ARRAY, list(lang), info)
                      end
                    (DAE.NOEXTARG(), false)
                  end

                  DAE.T_FUNCTION(funcResultType = DAE.T_TUPLE(__))  => begin
                    (DAE.NOEXTARG(), false)
                  end

                  DAE.T_FUNCTION(funcResultType = DAE.T_NORETCALL(__))  => begin
                    (DAE.NOEXTARG(), false)
                  end

                  DAE.T_FUNCTION(funcResultType = ty)  => begin
                    (DAE.EXTARG(DAEUtil.varCref(ListUtil.find(elements, DAEUtil.isOutputVar)), Absyn.OUTPUT(), ty), true)
                  end

                  _  => begin
                        Error.addInternalError("instExtMakeDefaultExternalCall failed for " + Types.unparseType(funcType), info)
                      fail()
                  end
                end
              end
              for elt in elements
                fargs = begin
                  @match elt begin
                    DAE.VAR(direction = DAE.OUTPUT(__)) where (! singleOutput)  => begin
                      addExtVarToCall(elt.componentRef, Absyn.OUTPUT(), elt.dims, fargs)
                    end

                    DAE.VAR(direction = DAE.INPUT(__))  => begin
                      addExtVarToCall(elt.componentRef, Absyn.INPUT(), elt.dims, fargs)
                    end

                    DAE.VAR(direction = DAE.BIDIR(__))  => begin
                      addExtVarToCall(elt.componentRef, Absyn.OUTPUT(), elt.dims, fargs)
                    end

                    _  => begin
                        fargs
                    end
                  end
                end
              end
              fargs = listReverse(fargs)
          (fargs, rettype)
        end

        function addExtVarToCall(cr::DAE.ComponentRef, dir::Absyn.Direction, dims::DAE.Dimensions, fargs::List{<:DAE.ExtArg}) ::List{DAE.ExtArg}


              fargs = _cons(DAE.EXTARG(cr, dir, ComponentReference.crefTypeFull(cr)), fargs)
              for dim in 1:listLength(dims)
                fargs = _cons(DAE.EXTARGSIZE(cr, ComponentReference.crefTypeFull(cr), DAE.ICONST(dim)), fargs)
              end
          fargs
        end

        function getRecordConstructorFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inPath::Absyn.Path) ::Tuple{FCore.Cache, DAE.Function}
              local outFunc::DAE.Function
              local outCache::FCore.Cache

              (outCache, outFunc) = begin
                  local path::Absyn.Path
                  local recordCl::SCode.Element
                  local recordEnv::FCore.Graph
                  local func::DAE.Function
                  local cache::FCore.Cache
                  local recType::DAE.Type
                  local fixedTy::DAE.Type
                  local funcTy::DAE.Type
                  local vars::List{DAE.Var}
                  local inputs::List{DAE.Var}
                  local locals::List{DAE.Var}
                  local fargs::List{DAE.FuncArg}
                  local eqCo::DAE.EqualityConstraint
                  local name::String
                  local newName::String
                @matchcontinue (inCache, inEnv, inPath) begin
                  (_, _, _)  => begin
                      path = AbsynUtil.makeFullyQualified(inPath)
                      func = FCore.getCachedInstFunc(inCache, path)
                    (inCache, func)
                  end

                  (_, _, _)  => begin
                      (_, recordCl, recordEnv) = Lookup.lookupClass(inCache, inEnv, inPath)
                      @match true = SCodeUtil.isRecord(recordCl)
                      name = SCodeUtil.getElementName(recordCl)
                      newName = FGraph.getInstanceOriginalName(recordEnv, name)
                      recordCl = SCodeUtil.setClassName(newName, recordCl)
                      (cache, _, _, _, _, _, recType, _, _, _) = Inst.instClass(inCache, recordEnv, InnerOuter.emptyInstHierarchy, UnitAbsynBuilder.emptyInstStore(), DAE.NOMOD(), Prefix.NOPRE(), recordCl, nil, true, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, Connect.emptySet)
                      @match DAE.T_COMPLEX(ClassInf.RECORD(path), vars, eqCo) = recType
                      vars = Types.filterRecordComponents(vars, SCodeUtil.elementInfo(recordCl))
                      (inputs, locals) = ListUtil.extractOnTrue(vars, Types.isModifiableTypesVar)
                      inputs = ListUtil.map(inputs, Types.setVarDefaultInput)
                      locals = ListUtil.map(locals, Types.setVarProtected)
                      vars = listAppend(inputs, locals)
                      path = AbsynUtil.makeFullyQualified(path)
                      fixedTy = DAE.T_COMPLEX(ClassInf.RECORD(path), vars, eqCo)
                      fargs = Types.makeFargsList(inputs)
                      funcTy = DAE.T_FUNCTION(fargs, fixedTy, DAE.FUNCTION_ATTRIBUTES_DEFAULT, path)
                      func = DAE.RECORD_CONSTRUCTOR(path, funcTy, DAE.emptyElementSource)
                      cache = InstUtil.addFunctionsToDAE(cache, list(func), SCode.NOT_PARTIAL())
                      path = AbsynUtil.pathSetLastIdent(path, AbsynUtil.makeIdentPathFromString(name))
                      fixedTy = DAE.T_COMPLEX(ClassInf.RECORD(path), vars, eqCo)
                      fargs = Types.makeFargsList(inputs)
                      funcTy = DAE.T_FUNCTION(fargs, fixedTy, DAE.FUNCTION_ATTRIBUTES_DEFAULT, path)
                      func = DAE.RECORD_CONSTRUCTOR(path, funcTy, DAE.emptyElementSource)
                      cache = InstUtil.addFunctionsToDAE(cache, list(func), SCode.NOT_PARTIAL())
                    (cache, func)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("InstFunction.getRecordConstructorFunction failed for " + AbsynUtil.pathString(inPath))
                      fail()
                  end
                end
              end
               #=  add the instance record constructor too!
               =#
          (outCache, outFunc)
        end

         #= Add record constructor whenever we instantiate a variable. Needed so we can cast to this constructor freely. =#
        function addRecordConstructorFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inType::DAE.Type, inInfo::SourceInfo) ::FCore.Cache
              local outCache::FCore.Cache

              outCache = begin
                  local vars::List{DAE.Var}
                  local inputs::List{DAE.Var}
                  local locals::List{DAE.Var}
                  local ty::DAE.Type
                  local recType::DAE.Type
                  local fixedTy::DAE.Type
                  local funcTy::DAE.Type
                  local eqCo::DAE.EqualityConstraint
                  local cache::FCore.Cache
                  local path::Absyn.Path
                  local recordCl::SCode.Element
                  local recordEnv::FCore.Graph
                  local func::DAE.Function
                  local fargs::List{DAE.FuncArg}
                   #=  try to instantiate class
                   =#
                @matchcontinue (inCache, inEnv, inType, inInfo) begin
                  (cache, _, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(path)), _)  => begin
                      path = AbsynUtil.makeFullyQualified(path)
                      (cache, _) = getRecordConstructorFunction(cache, inEnv, path)
                    cache
                  end

                  (cache, _, DAE.T_COMPLEX(ClassInf.RECORD(path), vars, eqCo), _)  => begin
                      path = AbsynUtil.makeFullyQualified(path)
                      vars = Types.filterRecordComponents(vars, inInfo)
                      (inputs, locals) = ListUtil.extractOnTrue(vars, Types.isModifiableTypesVar)
                      inputs = ListUtil.map(inputs, Types.setVarDefaultInput)
                      locals = ListUtil.map(locals, Types.setVarProtected)
                      vars = listAppend(inputs, locals)
                      fixedTy = DAE.T_COMPLEX(ClassInf.RECORD(path), vars, eqCo)
                      fargs = Types.makeFargsList(inputs)
                      funcTy = DAE.T_FUNCTION(fargs, fixedTy, DAE.FUNCTION_ATTRIBUTES_DEFAULT, path)
                      func = DAE.RECORD_CONSTRUCTOR(path, funcTy, DAE.emptyElementSource)
                      cache = InstUtil.addFunctionsToDAE(cache, list(func), SCode.NOT_PARTIAL())
                    cache
                  end

                  _  => begin
                      inCache
                  end
                end
              end
               #=  if previous stuff didn't work, try to use the ty directly
               =#
          outCache
        end

        function isElementImportantForFunction(elt::SCode.Element) ::Bool
              local b::Bool

              b = begin
                @match elt begin
                  SCode.COMPONENT(prefixes = SCode.PREFIXES(visibility = SCode.PROTECTED(__)), attributes = SCode.ATTR(direction = Absyn.BIDIR(__), variability = SCode.VAR(__)))  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          b
        end

        function checkExtObjOutput(inType::DAE.Type, info::SourceInfo)
              _ = begin
                  local path::Absyn.Path
                  local ty::DAE.Type
                @match (inType, info) begin
                  (DAE.T_FUNCTION(funcResultType = ty, path = path), _)  => begin
                      @match (_, (_, _, true)) = Types.traverseType(ty, (path, info, true), checkExtObjOutputWork)
                    ()
                  end
                end
              end
        end

        function checkExtObjOutputWork(ty::DAE.Type, inTpl::Tuple{<:Absyn.Path, SourceInfo, Bool}) ::Tuple{DAE.Type, Tuple{Absyn.Path, SourceInfo, Bool}}
              local outTpl::Tuple{Absyn.Path, SourceInfo, Bool}
              local oty::DAE.Type = ty

              outTpl = begin
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local info::SourceInfo
                  local str1::String
                  local str2::String
                  local b::Bool
                @match (ty, inTpl) begin
                  (DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(path1)), (path2, info, true))  => begin
                      path1 = AbsynUtil.joinPaths(path1, Absyn.IDENT("constructor"))
                      str1 = AbsynUtil.pathStringNoQual(path2)
                      str2 = AbsynUtil.pathStringNoQual(path1)
                      b = AbsynUtil.pathEqual(path1, path2)
                      Error.assertionOrAddSourceMessage(b, Error.FUNCTION_RETURN_EXT_OBJ, list(str1, str2), info)
                      outTpl = if b
                            inTpl
                          else
                            (path2, info, false)
                          end
                    outTpl
                  end

                  _  => begin
                      inTpl
                  end
                end
              end
          (oty, outTpl)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

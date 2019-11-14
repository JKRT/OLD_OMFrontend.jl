  module InstVar


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

        # import Connect

        import ConnectionGraph

        import DAE

        import FCore

        import FGraphUtil

        import InnerOuterTypes

        import InnerOuter

        import InstTypes

        import Mod

        import Prefix

        import SCode

        import UnitAbsyn

        import Config

        import ConnectUtil

        import Debug

        import Dump

        import DAEUtil

        import ElementSource

        import Inst

        import InstBinding

        import InstDAE

        import InstFunction

        import InstSection

        import InstUtil

        import Util
        import SCodeUtil

        import Types

        import PrefixUtil

        import ListUtil

        import ComponentReference

        import NFInstUtil

        import UnitAbsynBuilder

        import Flags

        import Expression

        import ExpressionDump

        import Error

        import ErrorExt

        import Lookup

        import SCodeDump

        import BaseHashSet

        import HashSet

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuterTypes.InstHierarchy  #= an instance hierarchy =#

        InstDims = List

         #= this function will look if a variable is inner/outer and depending on that will:
          - lookup for inner in the instanance hieararchy if we have ONLY outer
          - instantiate normally via instVar_dispatch otherwise
          - report an error if we have modifications on outer

        BTH: Added cases that handles 'outer' and 'inner outer' variables differently if they
        are declared wihin an instance of a synchronous SMNode Machine state: basically, instead of
        substituting 'outer' variables through their 'inner' counterparts the 'outer' variable is
        declared with a modification equation that sets the 'outer' variable equal to the 'inner'
        variable. Hence, the information in which instance an 'outer' variable was declared is
        preserved in the flattened code. This information is necessary to handle state machines in
        the backend. The current implementation doesn't handle cases in which the
        'inner' is not (yet) set.
           =#
        function instVar(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inIdent::String, inClass::SCode.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inDimensionLst::DAE.Dimensions, inIntegerLst::List{<:DAE.Subscript}, inInstDims::List{Any #=<:List{<:DAE.Dimension}=#}, inImpl::Bool, inComment::SCode.Comment, info::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, componentDefinitionParentEnv::FCore.Graph) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local io::Absyn.InnerOuter

              if begin
                @match inIdent begin
                  "Integer"  => begin
                    true
                  end

                  "Real"  => begin
                    true
                  end

                  "Boolean"  => begin
                    true
                  end

                  "String"  => begin
                    true
                  end

                  "time"  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
                Error.addSourceMessage(Error.RESERVED_IDENTIFIER, list(inIdent), info)
                fail()
              end
              io = SCodeUtil.prefixesInnerOuter(inPrefixes)
              (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph) = begin
                  local dims::DAE.Dimensions
                  local compenv::FCore.Graph
                  local env::FCore.Graph
                  local innerCompEnv::FCore.Graph
                  local outerCompEnv::FCore.Graph
                  local dae::DAE.DAElist
                  local outerDAE::DAE.DAElist
                  local innerDAE::DAE.DAElist
                  local csets::DAE.Sets
                  local csetsInner::DAE.Sets
                  local csetsOuter::DAE.Sets
                  local ty::DAE.Type
                  local ci_state::ClassInf.SMNode
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local innerPrefix::Prefix.PrefixType
                  local n::String
                  local s1::String
                  local s2::String
                  local s3::String
                  local s::String
                  local cl::SCode.Element
                  local attr::SCode.Attributes
                  local idxs::List{DAE.Subscript}
                  local inst_dims::InstDims
                  local impl::Bool
                  local comment::SCode.Comment
                  local cache::FCore.Cache
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local cref::DAE.ComponentRef
                  local crefOuter::DAE.ComponentRef
                  local crefInner::DAE.ComponentRef
                  local crefExp::DAE.Exp
                  local outers::List{DAE.ComponentRef}
                  local nInner::String
                  local typeName::String
                  local fullName::String
                  local typePath::Absyn.Path
                  local innerScope::String
                  local ioInner::Absyn.InnerOuter
                  local instResult::Option{InnerOuter.InstResult}
                  local pf::SCode.Prefixes
                  local store::UnitAbsyn.InstStore
                  local topInstance::InnerOuter.TopInstance
                  local sm::HashSet.HashSetType
                  local aexp::Absyn.Exp
                   #=  is ONLY inner
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inState, inMod, inPrefix, inIdent, inClass, inAttributes, inPrefixes, inDimensionLst, inIntegerLst, inInstDims, inImpl, inComment, info, inGraph, inSets, componentDefinitionParentEnv) begin
                  (cache, env, ih, store, ci_state, mod, pre, n, cl && SCode.CLASS(name = typeName), attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyInner(io)
                      (cache, innerCompEnv, ih, store, dae, csets, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                      (cache, cref) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      fullName = ComponentReference.printComponentRefStr(cref)
                      (cache, typePath) = Inst.makeFullyQualifiedIdent(cache, env, typeName)
                      outerCompEnv = InnerOuter.switchInnerToOuterInGraph(innerCompEnv, cref)
                      outerDAE = DAE.emptyDae
                      innerScope = FGraphUtil.printGraphPathStr(componentDefinitionParentEnv)
                      ih = InnerOuter.updateInstHierarchy(ih, pre, io, InnerOuter.INST_INNER(pre, n, io, fullName, typePath, innerScope, SOME(InnerOuter.INST_RESULT(cache, outerCompEnv, store, outerDAE, csets, ty, graph)), nil, NONE()))
                    (cache, innerCompEnv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyOuter(io)
                      @match false = Mod.modEqual(mod, DAE.NOMOD())
                      (cache, cref) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      s1 = ComponentReference.printComponentRefStr(cref)
                      s2 = Mod.prettyPrintMod(mod, 0)
                      s = s1 + " " + s2
                      Error.addSourceMessage(Error.OUTER_MODIFICATION, list(s), info)
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instVar(cache, env, ih, store, ci_state, DAE.NOMOD(), pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets, componentDefinitionParentEnv)
                    (cache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr && SCode.ATTR(direction = Absyn.OUTPUT(__)), pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyOuter(io)
                      @match true = Mod.modEqual(mod, DAE.NOMOD())
                      @match InnerOuter.INST_INNER(_, _, _, _, _, _, SOME(InnerOuter.INST_RESULT(cache, compenv, store, _, _, ty, graph)), _, _) = InnerOuter.lookupInnerVar(cache, env, ih, pre, n, io)
                      topInstance = listHead(ih)
                      @match InnerOuter.TOP_INSTANCE(sm = sm) = topInstance
                      @match true = BaseHashSet.currentSize(sm) > 0
                      cref = PrefixUtil.prefixToCref(inPrefix)
                      @match true = BaseHashSet.has(cref, sm)
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                    (inCache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, _, mod, pre, n, _, _, _, _, _, _, _, _, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyOuter(io)
                      @match true = Mod.modEqual(mod, DAE.NOMOD())
                      @match InnerOuter.INST_INNER(innerPrefix, nInner, ioInner, fullName, typePath, innerScope, (@match SOME(InnerOuter.INST_RESULT(cache, compenv, store, outerDAE, _, ty, graph)) = instResult), outers, _) = InnerOuter.lookupInnerVar(cache, env, ih, pre, n, io)
                      (cache, crefOuter) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      (cache, crefInner) = PrefixUtil.prefixCref(cache, env, ih, innerPrefix, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      ih = InnerOuter.addOuterPrefixToIH(ih, crefOuter, crefInner)
                      outers = ListUtil.unionElt(crefOuter, outers)
                      ih = InnerOuter.updateInstHierarchy(ih, innerPrefix, ioInner, InnerOuter.INST_INNER(innerPrefix, nInner, ioInner, fullName, typePath, innerScope, instResult, outers, NONE()))
                      outerDAE = DAE.emptyDae
                    (inCache, compenv, ih, store, outerDAE, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyOuter(io)
                      @match true = Mod.modEqual(mod, DAE.NOMOD())
                      @match InnerOuter.INST_INNER(_, _, _, _, typePath, _, NONE(), _, _) = InnerOuter.lookupInnerVar(cache, env, ih, pre, n, io)
                      (cache, crefOuter) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      typeName = SCodeUtil.className(cl)
                      (cache, typePath) = Inst.makeFullyQualifiedIdent(cache, env, typeName)
                      if ! (impl && listMember(pre, list(Prefix.NOPRE()))) && ! Config.getGraphicsExpMode()
                        s1 = ComponentReference.printComponentRefStr(crefOuter)
                        s2 = Dump.unparseInnerouterStr(io)
                        s3 = InnerOuter.getExistingInnerDeclarations(ih, componentDefinitionParentEnv)
                        s1 = AbsynUtil.pathString(typePath) + " " + s1
                        Error.addSourceMessage(Error.MISSING_INNER_PREFIX, list(s1, s2, s3), info)
                      end
                      (cache, compenv, ih, store, dae, _, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isOnlyOuter(io)
                      @match true = Mod.modEqual(mod, DAE.NOMOD())
                      @shouldFail _ = InnerOuter.lookupInnerVar(cache, env, ih, pre, n, io)
                      (cache, crefOuter) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      typeName = SCodeUtil.className(cl)
                      (cache, typePath) = Inst.makeFullyQualifiedIdent(cache, env, typeName)
                      if ! (impl && listMember(pre, list(Prefix.NOPRE()))) && ! Config.getGraphicsExpMode()
                        s1 = ComponentReference.printComponentRefStr(crefOuter)
                        s2 = Dump.unparseInnerouterStr(io)
                        s3 = InnerOuter.getExistingInnerDeclarations(ih, componentDefinitionParentEnv)
                        s1 = AbsynUtil.pathString(typePath) + " " + s1
                        Error.addSourceMessage(Error.MISSING_INNER_PREFIX, list(s1, s2, s3), info)
                      end
                      (cache, compenv, ih, store, dae, _, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl && SCode.CLASS(name = typeName), attr && SCode.ATTR(direction = Absyn.OUTPUT(__)), pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isInnerOuter(io)
                      topInstance = listHead(ih)
                      @match InnerOuter.TOP_INSTANCE(sm = sm) = topInstance
                      @match true = BaseHashSet.currentSize(sm) > 0
                      cref = PrefixUtil.prefixToCref(inPrefix)
                      @match true = BaseHashSet.has(cref, sm)
                      (cache, innerCompEnv, ih, store, dae, csetsInner, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                      (cache, cref) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      fullName = ComponentReference.printComponentRefStr(cref)
                      (cache, typePath) = Inst.makeFullyQualifiedIdent(cache, env, typeName)
                      outerCompEnv = InnerOuter.switchInnerToOuterInGraph(innerCompEnv, cref)
                      innerDAE = dae
                      innerScope = FGraphUtil.printGraphPathStr(componentDefinitionParentEnv)
                      ih = InnerOuter.updateInstHierarchy(ih, pre, io, InnerOuter.INST_INNER(pre, n, io, fullName, typePath, innerScope, SOME(InnerOuter.INST_RESULT(cache, outerCompEnv, store, innerDAE, csetsInner, ty, graph)), nil, NONE()))
                      (cache, compenv, ih, store, dae, _, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, DAE.NOMOD(), pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, dae, csetsInner, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl && SCode.CLASS(name = typeName), attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isInnerOuter(io)
                      (cache, innerCompEnv, ih, store, dae, csetsInner, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                      (cache, cref) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      fullName = ComponentReference.printComponentRefStr(cref)
                      (cache, typePath) = Inst.makeFullyQualifiedIdent(cache, env, typeName)
                      outerCompEnv = InnerOuter.switchInnerToOuterInGraph(innerCompEnv, cref)
                      innerDAE = dae
                      innerScope = FGraphUtil.printGraphPathStr(componentDefinitionParentEnv)
                      ih = InnerOuter.updateInstHierarchy(ih, pre, io, InnerOuter.INST_INNER(pre, n, io, fullName, typePath, innerScope, SOME(InnerOuter.INST_RESULT(cache, outerCompEnv, store, innerDAE, csetsInner, ty, graph)), nil, NONE()))
                      pf = SCodeUtil.prefixesSetInnerOuter(pf, Absyn.OUTER())
                      (cache, compenv, ih, store, dae, _, ty, graph) = instVar(cache, env, ih, store, ci_state, DAE.NOMOD(), pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets, componentDefinitionParentEnv)
                      outerDAE = dae
                      dae = DAEUtil.joinDaes(outerDAE, innerDAE)
                    (cache, compenv, ih, store, dae, csetsInner, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, _, graph, csets, _)  => begin
                      @match true = AbsynUtil.isNotInnerOuter(io)
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instVar_dispatch(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, _, _, mod, pre, n, cl, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      (cache, cref) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, DAE.T_UNKNOWN_DEFAULT, nil))
                      Debug.traceln("- InstVar.instVar failed while instatiating variable: " + ComponentReference.printComponentRefStr(cref) + " " + Mod.prettyPrintMod(mod, 0) + "\\nin scope: " + FGraphUtil.printGraphPathStr(env) + " class:\\n" + SCodeDump.unparseElementStr(cl))
                    fail()
                  end
                end
              end
               #=  call it normally
               =#
               #=  is inner outer output and is inside an instance of a SMNode Machine state!
               =#
               #=  both inner and outer
               =#
               #=  the inner outer must be in an instance that is part of a SMNode Machine
               =#
               #=  add it to the instance hierarchy
               =#
               #=  also all the components in the environment should be updated to be outer!
               =#
               #=  switch components from inner to outer in the component env.
               =#
               #=  keep the dae we get from the instantiation of the inner
               =#
               #=  add inner to the instance hierarchy
               =#
               #=  now call it normally
               =#
               #=  is inner outer!
               =#
               #=  both inner and outer
               =#
               #=  fprintln(Flags.INNER_OUTER, \"- InstVar.instVar inner outer: \" + PrefixUtil.printPrefixStr(pre) + \"/\" + n + \" in env: \" + FGraphUtil.printGraphPathStr(env));
               =#
               #=  add it to the instance hierarchy
               =#
               #=  also all the components in the environment should be updated to be outer!
               =#
               #=  switch components from inner to outer in the component env.
               =#
               #=  keep the dae we get from the instantiation of the inner
               =#
               #=  add inner to the instance hierarchy
               =#
               #=  now instantiate it as an outer with no modifications
               =#
               #=  keep the dae we get from the instantiation of the outer
               =#
               #=  join the dae's (even thou' the outer is empty)
               =#
               #=  is NO INNER NOR OUTER or it failed before!
               =#
               #=  no inner no outer
               =#
               #=  fprintln(Flags.INNER_OUTER, \"- InstVar.instVar NO inner NO outer: \" + PrefixUtil.printPrefixStr(pre) + \"/\" + n + \" in env: \" + FGraphUtil.printGraphPathStr(env));
               =#
               #=  failtrace
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

         #= A component element in a class may consist of several subcomponents
          or array elements.  This function is used to instantiate a
          component, instantiating all subcomponents and array elements
          separately.
          P.A: Most of the implementation is moved to instVar2. instVar collects
          dimensions for userdefined types, such that these can be correctly
          handled by instVar2 (using instArray) =#
        function instVar_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inName::String, inClass::SCode.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inDimensions::List{<:DAE.Dimension}, inIndices::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, inComment::SCode.Comment, inInfo::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local comp_name::String
              local dims::List{DAE.Dimension}
              local cls::SCode.Element
              local type_mods::DAE.Mod
              local mod::DAE.Mod
              local attr::SCode.Attributes
              local source::DAE.ElementSource

              try
                Error.updateCurrentComponent(inPrefix, inName, inInfo, PrefixUtil.identAndPrefixToPath)
                (outCache, dims, cls, type_mods) = InstUtil.getUsertypeDimensions(inCache, inEnv, inIH, inPrefix, inClass, inInstDims, inImpl)
                if listEmpty(dims)
                  dims = inDimensions
                  cls = inClass
                  mod = inMod
                  attr = inAttributes
                else
                  type_mods = liftUserTypeMod(type_mods, inDimensions)
                  dims = listAppend(inDimensions, dims)
                  mod = Mod.myMerge(inMod, type_mods)
                  attr = InstUtil.propagateClassPrefix(inAttributes, inPrefix)
                end
                (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph) = instVar2(outCache, inEnv, inIH, inStore, inState, mod, inPrefix, inName, cls, attr, inPrefixes, dims, inIndices, inInstDims, inImpl, inComment, inInfo, inGraph, inSets)
                source = ElementSource.createElementSource(inInfo, FGraphUtil.getScopePath(inEnv), inPrefix)
                (outCache, outDae) = addArrayVarEquation(outCache, inEnv, outIH, inState, outDae, outType, mod, NFInstUtil.toConst(SCodeUtil.attrVariability(attr)), inPrefix, inName, source)
                outCache = InstFunction.addRecordConstructorFunction(outCache, inEnv, Types.arrayElementType(outType), SCodeUtil.elementInfo(inClass))
                Error.clearCurrentComponent()
              catch
                Error.clearCurrentComponent()
                fail()
              end
               #=  No dimensions from userdefined type.
               =#
               #=  Userdefined array type, e.g. type Point = Real[3].
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

         #= This function adds dimensions to a modifier. This is a bit of a hack to make
           modifiers on user-defined types behave as expected, e.g.:

             type T = Real[3](start = {1, 2, 3});
             T x[2];  Modifier from T must be lifted to become [2, 3].
           =#
        function liftUserTypeMod(inMod::DAE.Mod, inDims::List{<:DAE.Dimension}) ::DAE.Mod
              local outMod::DAE.Mod = inMod

              if listEmpty(inDims)
                return outMod
              end
              outMod = begin
                @matchcontinue outMod begin
                  DAE.MOD(__)  => begin
                       #=  Only lift modifiers without 'each'.
                       =#
                      if ! SCodeUtil.eachBool(outMod.eachPrefix)
                        outMod.binding = liftUserTypeEqMod(outMod.binding, inDims)
                        outMod.subModLst = list(liftUserTypeSubMod(s, inDims) for s in outMod.subModLst)
                      end
                    outMod
                  end

                  _  => begin
                      outMod
                  end
                end
              end
          outMod
        end

        function liftUserTypeSubMod(inSubMod::DAE.SubMod, inDims::List{<:DAE.Dimension}) ::DAE.SubMod
              local outSubMod::DAE.SubMod = inSubMod

              outSubMod = begin
                @match outSubMod begin
                  DAE.NAMEMOD(__)  => begin
                      outSubMod.mod = liftUserTypeMod(outSubMod.mod, inDims)
                    outSubMod
                  end
                end
              end
          outSubMod
        end

        function liftUserTypeEqMod(inEqMod::Option{<:DAE.EqMod}, inDims::List{<:DAE.Dimension}) ::Option{DAE.EqMod}
              local outEqMod::Option{DAE.EqMod}

              local eq::DAE.EqMod
              local ty::DAE.Type

              if isNone(inEqMod)
                outEqMod = inEqMod
                return outEqMod
              end
              @match SOME(eq) = inEqMod
              eq = begin
                @match eq begin
                  DAE.TYPED(__)  => begin
                      eq.modifierAsExp = Expression.liftExpList(eq.modifierAsExp, inDims)
                      eq.modifierAsValue = Util.applyOption1(eq.modifierAsValue, ValuesUtil.liftValueList, inDims)
                      ty = Types.getPropType(eq.properties)
                      eq.properties = Types.setPropType(eq.properties, Types.liftArrayListDims(ty, inDims))
                    eq
                  end

                  _  => begin
                      eq
                  end
                end
              end
              outEqMod = SOME(eq)
          outEqMod
        end

        function addArrayVarEquation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inState::ClassInf.SMNode, inDae::DAE.DAElist, inType::DAE.Type, mod::DAE.Mod, constVar::DAE.Const, pre::Prefix.PrefixType, n::String, source::DAE.ElementSource) ::Tuple{FCore.Cache, DAE.DAElist}
              local outDae::DAE.DAElist
              local outCache::FCore.Cache

              (outCache, outDae) = begin
                  local cache::FCore.Cache
                  local dae::List{DAE.Element}
                  local exp::DAE.Exp
                  local eq::DAE.Element
                  local dims::DAE.Dimensions
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                   #=  Don't add array equations if +scalarizeBindings is set.
                   =#
                @matchcontinue (inDae, constVar) begin
                  (_, _)  => begin
                      @match true = Config.scalarizeBindings()
                    (inCache, inDae)
                  end

                  (DAE.DAE_LIST(dae), DAE.C_VAR(__))  => begin
                      @match false = ClassInf.isFunctionOrRecord(inState)
                      ty = Types.simplifyType(inType)
                      @match false = Types.isExternalObject(Types.arrayElementType(ty))
                      @match false = Types.isComplexType(Types.arrayElementType(ty))
                      @match (dims && _ <| _) = Types.getDimensions(ty)
                      @match SOME(exp) = InstBinding.makeVariableBinding(ty, mod, constVar, pre, n)
                      cr = ComponentReference.makeCrefIdent(n, ty, nil)
                      (cache, cr) = PrefixUtil.prefixCref(inCache, inEnv, inIH, pre, cr)
                      eq = DAE.ARRAY_EQUATION(dims, DAE.CREF(cr, ty), exp, source)
                    (cache, DAE.DAE_LIST(_cons(eq, dae)))
                  end

                  _  => begin
                      (inCache, inDae)
                  end
                end
              end
               #=  print(\"Creating array equation for \" + PrefixUtil.printPrefixStr(pre) + \".\" + n + \" of constVar \" + DAEUtil.constStr(constVar) + \" in classinf \" + ClassInf.printStateStr(inState) + \"\\n\");
               =#
          (outCache, outDae)
        end

         #= Helper function to instVar, does the main work. =#
        function instVar2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inName::String, inClass::SCode.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inDimensions::DAE.Dimensions, inSubscripts::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, inComment::SCode.Comment, inInfo::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph) = begin
                  local inst_dims::InstDims
                  local inst_dims_1::InstDims
                  local dims_1::List{DAE.Dimension}
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local p::DAE.Properties
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local compenv::FCore.Graph
                  local csets::DAE.Sets
                  local ty::DAE.Type
                  local ty_1::DAE.Type
                  local arrty::DAE.Type
                  local st::ClassInf.SMNode
                  local ci_state::ClassInf.SMNode
                  local cr::DAE.ComponentRef
                  local ty_2::DAE.Type
                  local dae1::DAE.DAElist
                  local dae::DAE.DAElist
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local n::String
                  local cl::SCode.Element
                  local attr::SCode.Attributes
                  local dims::DAE.Dimensions
                  local idxs::List{DAE.Subscript}
                  local impl::Bool
                  local comment::SCode.Comment
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local dime::DAE.Subscript
                  local dim::DAE.Dimension
                  local dim2::DAE.Dimension
                  local cache::FCore.Cache
                  local vis::SCode.Visibility
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local n2::String
                  local deduced_dim::ModelicaInteger
                  local dime2::DAE.Subscript
                  local pf::SCode.Prefixes
                  local fin::SCode.Final
                  local info::SourceInfo
                  local io::Absyn.InnerOuter
                  local store::UnitAbsyn.InstStore
                  local subMods::List{DAE.SubMod}
                  local path::Absyn.Path
                  local vars::List{DAE.Var}
                   #=  Rules for instantation of function variables (e.g. input and output
                   =#
                   #=  Function variables with modifiers (outputs or local/protected variables)
                   =#
                   #=  For Functions we cannot always find dimensional sizes. e.g.
                   =#
                   #=  input Real x[:]; component environement The class is instantiated
                   =#
                   #=  with the calculated modification, and an extended prefix.
                   =#
                   #=
                   =#
                   #=  mahge: Function variables with subMod modifications. This can happen for records with inline constructions (and maybe other stuff too???)
                   =#
                   #=  now only for records.
                   =#
                   #=  e.g.
                   =#
                   #=  function out
                   =#
                   #=    output R1 r(v1=3,v2=3);   <= Here
                   =#
                   #=  protected
                   =#
                   #=    R1 r2(v1=1, v1=2);      <= Here
                   =#
                   #=  end out;
                   =#
                   #=  see testsuit/mofiles/RecordBindings.mo.
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inState, inMod, inPrefix, inName, inClass, inAttributes, inPrefixes, inDimensions, inSubscripts, inInstDims, inImpl, inComment, inInfo, inGraph, inSets) begin
                  (cache, env, ih, store, ci_state, mod && DAE.MOD(binding = NONE()), pre, n, cl && SCode.CLASS(restriction = SCode.R_RECORD(_)), attr, pf, dims, _, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match true = ClassInf.isFunction(ci_state)
                      InstUtil.checkFunctionVar(n, attr, pf, info)
                      (cache, env_1, ih, store, _, csets, ty, _, _, graph) = Inst.instClass(cache, env, ih, store, DAE.NOMOD(), pre, cl, inst_dims, impl, InstTypes.INNER_CALL(), graph, csets)
                      ty_1 = InstUtil.makeArrayType(dims, ty)
                      InstUtil.checkFunctionVarType(ty_1, ci_state, n, info)
                      (cache, dae_var_attr) = InstBinding.instDaeVariableAttributes(cache, env, mod, ty, nil)
                      ty_2 = Types.simplifyType(ty_1)
                      (cache, cr) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, ty_2, nil))
                      @match (cache, DAE.EQBOUND(e, _, _, _)) = InstBinding.makeBinding(cache, env, attr, mod, ty_2, pre, n, info)
                      source = ElementSource.createElementSource(info, FGraphUtil.getScopePath(env), pre)
                      @match SCode.PREFIXES(visibility = vis, finalPrefix = fin, innerOuter = io) = pf
                      dae = InstDAE.daeDeclare(cache, env, env_1, cr, ci_state, ty, attr, vis, SOME(e), list(dims), NONE(), dae_var_attr, SOME(comment), io, fin, source, true)
                      store = UnitAbsynBuilder.instAddStore(store, ty, cr)
                    (cache, env_1, ih, store, dae, csets, ty_1, graph)
                  end

                  (cache, env, ih, store, ci_state, mod && DAE.MOD(binding = SOME(_)), pre, n, cl, attr, pf, dims, _, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match true = ClassInf.isFunction(ci_state)
                      InstUtil.checkFunctionVar(n, attr, pf, info)
                      @match SOME(DAE.TYPED(e, _, p, _)) = Mod.modEquation(mod)
                      (cache, env_1, ih, store, _, csets, ty, _, _, graph) = Inst.instClass(cache, env, ih, store, DAE.NOMOD(), pre, cl, inst_dims, impl, InstTypes.INNER_CALL(), graph, csets)
                      ty_1 = InstUtil.makeArrayType(dims, ty)
                      InstUtil.checkFunctionVarType(ty_1, ci_state, n, info)
                      (cache, dae_var_attr) = InstBinding.instDaeVariableAttributes(cache, env, mod, ty, nil)
                      (e_1, _) = Types.matchProp(e, p, DAE.PROP(ty_1, DAE.C_VAR()), true)
                      ty_2 = Types.simplifyType(ty_1)
                      (cache, cr) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, ty_2, nil))
                      source = ElementSource.createElementSource(info, FGraphUtil.getScopePath(env), pre)
                      @match SCode.PREFIXES(visibility = vis, finalPrefix = fin, innerOuter = io) = pf
                      dae = InstDAE.daeDeclare(cache, env, env_1, cr, ci_state, ty, attr, vis, SOME(e_1), list(dims), NONE(), dae_var_attr, SOME(comment), io, fin, source, true)
                      store = UnitAbsynBuilder.instAddStore(store, ty, cr)
                    (cache, env_1, ih, store, dae, csets, ty_1, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl && SCode.CLASS(__), attr, pf, dims, _, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match true = ClassInf.isFunction(ci_state)
                      InstUtil.checkFunctionVar(n, attr, pf, info)
                      (cache, env_1, ih, store, _, csets, ty, _, _, _) = Inst.instClass(cache, env, ih, store, mod, pre, cl, inst_dims, impl, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, csets)
                      arrty = InstUtil.makeArrayType(dims, ty)
                      InstUtil.checkFunctionVarType(arrty, ci_state, n, info)
                      (cache, cr) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, arrty, nil))
                      (cache, dae_var_attr) = InstBinding.instDaeVariableAttributes(cache, env, mod, ty, nil)
                      source = ElementSource.createElementSource(info, FGraphUtil.getScopePath(env), pre)
                      @match SCode.PREFIXES(visibility = vis, finalPrefix = fin, innerOuter = io) = pf
                      dae = InstDAE.daeDeclare(cache, env, env_1, cr, ci_state, ty, attr, vis, NONE(), list(dims), NONE(), dae_var_attr, SOME(comment), io, fin, source, true)
                      store = UnitAbsynBuilder.instAddStore(store, ty, cr)
                    (cache, env_1, ih, store, dae, csets, arrty, graph)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _,  nil(), _, _, _, _, _, _, _)  => begin
                      @match false = ClassInf.isFunction(inState)
                      (cache, env, ih, store, dae, csets, ty, graph) = instScalar(inCache, inEnv, inIH, inStore, inState, inMod, inPrefix, inName, inClass, inAttributes, inPrefixes, inSubscripts, inInstDims, inImpl, SOME(inComment), inInfo, inGraph, inSets)
                    (cache, env, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod && DAE.MOD(binding = SOME(DAE.TYPED(__))), pre, n, cl, attr, pf, dim && DAE.DIM_UNKNOWN(__) <| dims, idxs, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match true = Config.splitArrays()
                      @match false = ClassInf.isFunction(ci_state)
                      dim2 = InstUtil.instWholeDimFromMod(dim, mod, n, info)
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, list(dim2))
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instArray(cache, env, ih, store, ci_state, mod, pre, n, (cl, attr), pf, 1, dim2, dims, idxs, inst_dims_1, impl, comment, info, graph, csets)
                      ty_1 = InstUtil.liftNonBasicTypes(ty, dim2)
                    (cache, compenv, ih, store, dae, csets, ty_1, graph)
                  end

                  (cache, env, ih, store, ci_state, mod && DAE.MOD(binding = SOME(DAE.TYPED(__))), pre, n, cl, attr, pf, dim && DAE.DIM_UNKNOWN(__) <| dims, idxs, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match false = Config.splitArrays()
                      @match false = ClassInf.isFunction(ci_state)
                      dim2 = InstUtil.instWholeDimFromMod(dim, mod, n, info)
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, list(dim2))
                      dime2 = Expression.dimensionSubscript(dim2)
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, _cons(dime2, idxs), inst_dims_1, impl, comment, info, graph, csets)
                      ty_1 = InstUtil.liftNonBasicTypes(ty, dim2)
                    (cache, compenv, ih, store, dae, csets, ty_1, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dim <| dims, idxs, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match true = Config.splitArrays()
                      @match false = ClassInf.isFunction(ci_state)
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, list(dim))
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instArray(cache, env, ih, store, ci_state, mod, pre, n, (cl, attr), pf, 1, dim, dims, idxs, inst_dims_1, impl, comment, info, graph, csets)
                      ty_1 = InstUtil.liftNonBasicTypes(ty, dim)
                    (cache, compenv, ih, store, dae, csets, ty_1, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dim <| dims, idxs, inst_dims, impl, comment, info, graph, csets)  => begin
                      @match false = Config.splitArrays()
                      @match false = ClassInf.isFunction(ci_state)
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, list(dim))
                      dime = Expression.dimensionSubscript(dim)
                      (cache, compenv, ih, store, dae, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, _cons(dime, idxs), inst_dims_1, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, dae, csets, ty, graph)
                  end

                  (_, _, _, _, _, DAE.NOMOD(__), _, n, _, _, _, DAE.DIM_UNKNOWN(__) <| _, _, _, _, _, info, _, _)  => begin
                      Error.addSourceMessage(Error.FAILURE_TO_DEDUCE_DIMS_NO_MOD, list(String(listLength(inSubscripts) + 1), n), info)
                    fail()
                  end

                  (_, env, _, _, _, mod, pre, n, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- InstVar.instVar2 failed: " + PrefixUtil.printPrefixStr(pre) + "." + n + "(" + Mod.prettyPrintMod(mod, 0) + ")\\n  Scope: " + FGraphUtil.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #= Instantiate type of the component, skip dae/not flattening (but extract functions)
               =#
               #=  adrpo: do not send in the modifications as it will fail if the modification is an ARRAY.
               =#
               #=         anyhow the modifications are handled below.
               =#
               #=         input Integer sequence[3](min = {1,1,1}, max = {3,3,3}) = {1,2,3};  this will fail if we send in the mod.
               =#
               #=         see testsuite/mofiles/Sequence.mo
               =#
               #= /* mod */ =#
               #= Make it an array type since we are not flattening
               =#
               #= Generate variable with default binding
               =#
               #= We should get a call exp from here
               =#
               #= /*source*/ =#
               #=  set the source of this element
               =#
               #=  mahge: function variables with eqMod modifications.
               =#
               #=  FIXHERE: They might have subMods too (variable attributes). see testsuite/mofiles/Sequence.mo
               =#
               #= get the equation modification
               =#
               #= Instantiate type of the component, skip dae/not flattening (but extract functions)
               =#
               #=  adrpo: do not send in the modifications as it will fail if the modification is an ARRAY.
               =#
               #=         anyhow the modifications are handled below.
               =#
               #=         input Integer sequence[3](min = {1,1,1}, max = {3,3,3}) = {1,2,3};  this will fail if we send in the mod.
               =#
               #=         see testsuite/mofiles/Sequence.mo
               =#
               #= /* mod */ =#
               #= Make it an array type since we are not flattening
               =#
               #=  Check binding type matches variable type
               =#
               #= Generate variable with default binding
               =#
               #=  set the source of this element
               =#
               #=  Function variables without binding
               =#
               #= Instantiate type of the component, skip dae/not flattening
               =#
               #=  set the source of this element
               =#
               #=  Scalar variables.
               =#
               #=  print(\"InstVar.instVar2: Scalar variables case: inClass: \" + SCodeDump.unparseElementStr(inClass) + \"\\n\");
               =#
               #=  Array variables with unknown dimensions, e.g. Real x[:] = [some expression that can be used to determine dimension].
               =#
               #=  Try to deduce the dimension from the modifier.
               =#
               #=  Do not lift types extending basic type, they are already array types.
               =#
               #=  Array variables with unknown dimensions, non-expanding case
               =#
               #=  Try to deduce the dimension from the modifier.
               =#
               #= /*TODO : mahge: remove this*/ =#
               #= /*
                      dime = InstUtil.instWholeDimFromMod(dim, mod, n, info);
                      dime2 = InstUtil.makeNonExpSubscript(dime);
                      dim2 = Expression.subscriptDimension(dime);
                      inst_dims_1 = List.appendLastList(inst_dims, {dime2});
                      */ =#
               #=  Do not lift types extending basic type, they are already array types.
               =#
               #=  Array variables , e.g. Real x[3]
               =#
               #=  dim = InstUtil.evalEnumAndBoolDim(dim);
               =#
               #=  Do not lift types extending basic type, they are already array types.
               =#
               #=  Array variables , non-expanding case
               =#
               #= /*TODO : mahge: remove this*/ =#
               #= /*
                      dime = InstUtil.instDimExpNonSplit(dim, impl);
                      inst_dims_1 = List.appendLastList(inst_dims, {dime});
                      */ =#
               #=  Type lifting is done in the \"scalar\" case
               =#
               #= ty_1 = InstUtil.liftNonBasicTypes(ty,dim);  Do not lift types extending basic type, they are already array types.
               =#
               #=  Array variable with unknown dimensions, but no binding
               =#
               #=  failtrace
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

         #= Instantiates a scalar variable. =#
        function instScalar(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inName::String, inClass::SCode.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inSubscripts::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, inComment::Option{<:SCode.Comment}, inInfo::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph) = begin
                  local cls_name::String
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local ih::InstanceHierarchy
                  local store::UnitAbsyn.InstStore
                  local csets::DAE.Sets
                  local res::SCode.Restriction
                  local vt::SCode.Variability
                  local idxs::List{DAE.Subscript}
                  local pre::Prefix.PrefixType
                  local ci_state::ClassInf.SMNode
                  local graph::ConnectionGraph.ConnectionGraphType
                  local dae::DAE.DAElist
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local ty::DAE.Type
                  local ident_ty::DAE.Type
                  local cr::DAE.ComponentRef
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local opt_binding::Option{DAE.Exp}
                  local source::DAE.ElementSource
                  local attr::SCode.Attributes
                  local vis::SCode.Visibility
                  local fin::SCode.Final
                  local io::Absyn.InnerOuter
                  local start::DAE.StartValue
                  local opt_attr::Option{SCode.Attributes}
                  local mod::DAE.Mod
                  local predims::List{DAE.Dimension}
                @matchcontinue (inCache, inEnv, inIH, inStore, inState, inMod, inPrefix, inName, inClass, inAttributes, inPrefixes, inSubscripts, inInstDims, inImpl, inComment, inInfo, inGraph, inSets) begin
                  (cache, env, ih, store, _, mod, _, _, SCode.CLASS(name = cls_name, restriction = res), SCode.ATTR(variability = vt), SCode.PREFIXES(visibility = vis, finalPrefix = fin, innerOuter = io), idxs, _, _, _, _, _, _)  => begin
                      idxs = listReverse(idxs)
                      ci_state = ClassInf.start(res, Absyn.IDENT(cls_name))
                      predims = ListUtil.lastListOrEmpty(inInstDims)
                      pre = PrefixUtil.prefixAdd(inName, predims, idxs, inPrefix, vt, ci_state, inInfo)
                      (cache, env_1, ih, store, dae1, csets, ty, _, opt_attr, graph) = Inst.instClass(cache, env, ih, store, inMod, pre, inClass, inInstDims, inImpl, InstTypes.INNER_CALL(), inGraph, inSets)
                      (cache, dae_var_attr) = InstBinding.instDaeVariableAttributes(cache, env_1, inMod, ty, nil)
                      attr = InstUtil.propagateAbSCDirection(vt, inAttributes, opt_attr, inInfo)
                      attr = SCodeUtil.removeAttributeDimensions(attr)
                      ident_ty = InstUtil.makeCrefBaseType(ty, inInstDims)
                      cr = ComponentReference.makeCrefIdent(inName, ident_ty, idxs)
                      (cache, cr) = PrefixUtil.prefixCref(cache, env, ih, inPrefix, cr)
                      InstUtil.checkModificationOnOuter(cache, env_1, ih, inPrefix, inName, cr, inMod, vt, io, inImpl, inInfo)
                      source = ElementSource.createElementSource(inInfo, FGraphUtil.getScopePath(env_1), inPrefix)
                      mod = if ! listEmpty(inSubscripts) && ! SCodeUtil.isParameterOrConst(vt) && ! ClassInf.isFunctionOrRecord(inState) && ! Types.isComplexType(Types.arrayElementType(ty)) && ! Types.isExternalObject(Types.arrayElementType(ty)) && ! Config.scalarizeBindings()
                            DAE.NOMOD()
                          else
                            inMod
                          end
                      opt_binding = InstBinding.makeVariableBinding(ty, mod, NFInstUtil.toConst(vt), inPrefix, inName)
                      start = InstBinding.instStartBindingExp(inMod, ty, vt)
                      if ! Flags.getConfigBool(Flags.USE_LOCAL_DIRECTION)
                        attr = stripVarAttrDirection(cr, ih, inState, inPrefix, attr)
                      end
                      dae1 = InstUtil.propagateAttributes(dae1, attr, inPrefixes, inInfo)
                      dae2 = InstDAE.daeDeclare(cache, env, env_1, cr, inState, ty, attr, vis, opt_binding, inInstDims, start, dae_var_attr, inComment, io, fin, source, false)
                      store = UnitAbsynBuilder.instAddStore(store, ty, cr)
                      dae = instScalar2(cr, ty, vt, inMod, dae2, dae1, source, inImpl)
                    (cache, env_1, ih, store, dae, csets, ty, graph)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Inst.instScalar failed on " + inName + " in scope " + PrefixUtil.printPrefixStr(inPrefix) + " env: " + FGraphUtil.printGraphPathStr(inEnv) + "\\n")
                      fail()
                  end
                end
              end
               #=  Propagate prefixes to any elements inside this components if it's a
               =#
               #=  structured component.
               =#
               #=  Add the component to the DAE.
               =#
               #=  The remaining work is done in instScalar2.
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

         #= This function strips the input/output prefixes from components which are not
           top-level or inside a top-level connector or part of a state machine component. =#
        function stripVarAttrDirection(inCref::DAE.ComponentRef, ih::InstanceHierarchy, inState::ClassInf.SMNode, inPrefix::Prefix.PrefixType, inAttributes::SCode.Attributes) ::SCode.Attributes
              local outAttributes::SCode.Attributes

              outAttributes = begin
                  local cref::DAE.ComponentRef
                  local topInstance::InnerOuter.TopInstance
                  local sm::HashSet.HashSetType
                   #=  Component without input/output.
                   =#
                @matchcontinue (inCref, inState, inAttributes) begin
                  (_, _, SCode.ATTR(direction = Absyn.BIDIR(__)))  => begin
                    inAttributes
                  end

                  (DAE.CREF_IDENT(__), _, _)  => begin
                    inAttributes
                  end

                  (_, ClassInf.CONNECTOR(__), _) where (ConnectUtil.faceEqual(ConnectUtil.componentFaceType(inCref), DAE.OUTSIDE()))  => begin
                    inAttributes
                  end

                  (_, _, _)  => begin
                      topInstance = listHead(ih)
                      @match InnerOuter.TOP_INSTANCE(sm = sm) = topInstance
                      @match true = BaseHashSet.currentSize(sm) > 0
                      cref = PrefixUtil.prefixToCref(inPrefix)
                      @match true = BaseHashSet.has(cref, sm)
                    inAttributes
                  end

                  _  => begin
                      SCodeUtil.setAttributesDirection(inAttributes, Absyn.BIDIR())
                  end
                end
              end
               #=  Non-qualified identifier = top-level component.
               =#
               #=  Outside connector
               =#
               #=  Component with input/output that is part of a state machine
               =#
               #=  Everything else, strip the input/output prefix.
               =#
          outAttributes
        end

         #= Helper function to instScalar. Some operations needed when instantiating a
          scalar depends on what kind of variable it is, i.e. constant, parameter or
          variable. This function does these operations to keep instScalar simple. =#
        function instScalar2(inCref::DAE.ComponentRef, inType::DAE.Type, inVariability::SCode.Variability, inMod::DAE.Mod, inDae::DAE.DAElist, inClassDae::DAE.DAElist, inSource::DAE.ElementSource, inImpl::Bool) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local dae::DAE.DAElist
                  local cls_dae::DAE.DAElist
                   #=  Constant with binding.
                   =#
                @match (inCref, inType, inVariability, inMod, inDae, inClassDae, inSource, inImpl) begin
                  (_, _, SCode.CONST(__), DAE.MOD(binding = SOME(DAE.TYPED(__))), _, _, _, _)  => begin
                      dae = DAEUtil.joinDaes(inClassDae, inDae)
                    dae
                  end

                  (_, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)), _, DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = DAE.CREF(_, _)))), _, _, _, _)  => begin
                      dae = InstBinding.instModEquation(inCref, inType, inMod, inSource, inImpl)
                      dae = InstUtil.moveBindings(dae, inClassDae)
                      dae = DAEUtil.joinDaes(dae, inDae)
                    dae
                  end

                  (_, DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)), _, DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = DAE.CAST(exp = DAE.CREF(_, _))))), _, _, _, _)  => begin
                      dae = InstBinding.instModEquation(inCref, inType, inMod, inSource, inImpl)
                      dae = InstUtil.moveBindings(dae, inClassDae)
                      dae = DAEUtil.joinDaes(dae, inDae)
                    dae
                  end

                  (_, _, SCode.PARAM(__), DAE.MOD(binding = SOME(DAE.TYPED(__))), _, _, _, _)  => begin
                      dae = InstBinding.instModEquation(inCref, inType, inMod, inSource, inImpl)
                      dae = InstUtil.propagateBinding(inClassDae, dae)
                      dae = DAEUtil.joinDaes(dae, inDae)
                    dae
                  end

                  _  => begin
                        dae = if Types.isComplexType(inType)
                              InstBinding.instModEquation(inCref, inType, inMod, inSource, inImpl)
                            else
                              DAE.emptyDae
                            end
                        cls_dae = stripRecordDefaultBindingsFromDAE(inClassDae, inType, dae)
                        dae = DAEUtil.joinDaes(dae, inDae)
                        dae = DAEUtil.joinDaes(cls_dae, dae)
                      dae
                  end
                end
              end
               #=  mahge
               =#
               #=  Records with Bindings to other records like =>
               =#
               #=  model M
               =#
               #=    R r1 = R(1);
               =#
               #=    R r1 = r2;   <= here
               =#
               #=  end M;
               =#
               #=  The dae that will be recived from instClass in instScalar will give the default record bindings for the record r1
               =#
               #=  which is wrong. Fixing it there would need a LOT of changes.
               =#
               #=  So instead we fix it here by moving the equation generated from eqMod modification for each element back to the
               =#
               #=  declaration of the element. Then removing the equation. This is done in the function moveBindings.
               =#
               #=  SEE testsuit/records/RecordBindingsOrdered.mo and RecordBindingsOrderedSimple.mo
               =#
               #= move bindings from dae to inClassDae and use the resulting dae
               =#
               #= move bindings from dae to inClassDae and use the resulting dae
               =#
               #=  Parameter with binding.
               =#
               #=  The equations generated by InstBinding.instModEquation are used only to modify
               =#
               #=  the bindings of parameters. No extra equations are added. -- alleb
               =#
               #=  All other scalars.
               =#
          outDae
        end

         #= This function removes bindings from record members for which a binding
           equation has already been generated. This is done because the record members
           otherwise get a binding from the default argument of the record too. =#
        function stripRecordDefaultBindingsFromDAE(inClassDAE::DAE.DAElist, inType::DAE.Type, inEqDAE::DAE.DAElist) ::DAE.DAElist
              local outClassDAE::DAE.DAElist

              outClassDAE = begin
                  local els::List{DAE.Element}
                  local eqs::List{DAE.Element}
                   #=  Check if the component is of record type, and if any equations have been
                   =#
                   #=  generated for the component's binding.
                   =#
                @match (inClassDAE, inType, inEqDAE) begin
                  (DAE.DAE_LIST(elementLst = els), DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__)), DAE.DAE_LIST(elementLst = eqs && _ <| _))  => begin
                      (els, _) = ListUtil.mapFold(els, stripRecordDefaultBindingsFromElement, eqs)
                    DAE.DAE_LIST(els)
                  end

                  _  => begin
                      inClassDAE
                  end
                end
              end
               #=  This assumes that the equations are ordered the same as the variables.
               =#
          outClassDAE
        end

        function stripRecordDefaultBindingsFromElement(inVar::DAE.Element, inEqs::List{<:DAE.Element}) ::Tuple{DAE.Element, List{DAE.Element}}
              local outEqs::List{DAE.Element}
              local outVar::DAE.Element

              (outVar, outEqs) = begin
                  local var_cr::DAE.ComponentRef
                  local eq_cr::DAE.ComponentRef
                  local rest_eqs::List{DAE.Element}
                @match (inVar, inEqs) begin
                  (DAE.VAR(componentRef = var_cr), DAE.EQUATION(exp = DAE.CREF(componentRef = eq_cr)) <| rest_eqs) where (ComponentReference.crefEqual(var_cr, eq_cr))  => begin
                    (DAEUtil.setElementVarBinding(inVar, NONE()), rest_eqs)
                  end

                  (DAE.VAR(componentRef = var_cr), DAE.COMPLEX_EQUATION(lhs = DAE.CREF(componentRef = eq_cr)) <| _) where (ComponentReference.crefPrefixOf(eq_cr, var_cr))  => begin
                    (DAEUtil.setElementVarBinding(inVar, NONE()), inEqs)
                  end

                  _  => begin
                      (inVar, inEqs)
                  end
                end
              end
               #=  The first equation assigns the variable. Remove the variable's
               =#
               #=  binding and discard the equation.
               =#
          (outVar, outEqs)
        end

        function checkDimensionGreaterThanZero(inDim::DAE.Dimension, inPrefix::Prefix.PrefixType, inIdent::String, info::SourceInfo)
              _ = begin
                  local dim_str::String
                  local cr_str::String
                  local cr::DAE.ComponentRef
                @match inDim begin
                  DAE.DIM_INTEGER(__)  => begin
                      if inDim.integer < 0
                        dim_str = ExpressionDump.dimensionString(inDim)
                        cr = DAE.CREF_IDENT(inIdent, DAE.T_REAL_DEFAULT, nil)
                        cr_str = ComponentReference.printComponentRefStr(PrefixUtil.prefixCrefNoContext(inPrefix, cr))
                        Error.addSourceMessageAndFail(Error.NEGATIVE_DIMENSION_INDEX, list(dim_str, cr_str), info)
                      end
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= This function checks that the dimension of a modifier is the same as the
           modified components dimension. Only the first dimension is checked, since
           this function is meant to be called in instArray which is called recursively
           for a component's dimensions. =#
        function checkArrayModDimSize(mod::DAE.Mod, inDimension::DAE.Dimension, inPrefix::Prefix.PrefixType, inIdent::String, inInfo::SourceInfo)
              _ = begin
                @match mod begin
                  DAE.MOD(eachPrefix = SCode.NOT_EACH(__))  => begin
                       #=  Only check modifiers which are not marked with 'each'.
                       =#
                      ListUtil.map4_0(mod.subModLst, checkArraySubModDimSize, inDimension, inPrefix, inIdent, inInfo)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkArraySubModDimSize(inSubMod::DAE.SubMod, inDimension::DAE.Dimension, inPrefix::Prefix.PrefixType, inIdent::String, inInfo::SourceInfo)
              _ = begin
                  local name::String
                  local eqmod::Option{DAE.EqMod}
                   #=  Don't check quantity, because Dymola doesn't and as a result the MSL
                   =#
                   #=  contains some type errors.
                   =#
                @match inSubMod begin
                  DAE.NAMEMOD(ident = "quantity")  => begin
                    ()
                  end

                  DAE.NAMEMOD(ident = name, mod = DAE.MOD(eachPrefix = SCode.NOT_EACH(__), binding = eqmod))  => begin
                      name = inIdent + "." + name
                      @match true = checkArrayModBindingDimSize(eqmod, inDimension, inPrefix, name, inInfo)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

        function checkArrayModBindingDimSize(inBinding::Option{<:DAE.EqMod}, inDimension::DAE.Dimension, inPrefix::Prefix.PrefixType, inIdent::String, inInfo::SourceInfo) ::Bool
              local outIsCorrect::Bool

              outIsCorrect = begin
                  local exp::DAE.Exp
                  local ty::DAE.Type
                  local ty_dim::DAE.Dimension
                  local dim_size1::ModelicaInteger
                  local dim_size2::ModelicaInteger
                  local exp_str::String
                  local exp_ty_str::String
                  local dims_str::String
                  local ty_dims::DAE.Dimensions
                  local info::SourceInfo
                @matchcontinue inBinding begin
                  SOME(DAE.TYPED(modifierAsExp = exp, properties = DAE.PROP(type_ = ty), info = info))  => begin
                      ty_dim = Types.getDimensionNth(ty, 1)
                      dim_size1 = Expression.dimensionSize(inDimension)
                      dim_size2 = Expression.dimensionSize(ty_dim)
                      @match true = dim_size1 != dim_size2
                      exp_str = ExpressionDump.printExpStr(exp)
                      exp_ty_str = Types.unparseType(ty)
                      @match _cons(_, ty_dims) = Types.getDimensions(ty)
                      dims_str = ExpressionDump.dimensionsString(_cons(inDimension, ty_dims))
                      Error.addMultiSourceMessage(Error.ARRAY_DIMENSION_MISMATCH, list(exp_str, exp_ty_str, dims_str), _cons(info, _cons(inInfo, nil)))
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
               #=  If the dimensions are not equal, print an error message.
               =#
               #=  We don't know the complete expected type, so lets assume that the
               =#
               #=  rest of the expression's type is correct (will be caught later anyway).
               =#
          outIsCorrect
        end

         #= When an array is instantiated by instVar, this function is used
          to go through all the array elements and instantiate each array
          element separately. =#
        function instArray(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inIdent::String, inElement::Tuple{<:SCode.Element, SCode.Attributes}, inPrefixes::SCode.Prefixes, inInteger::ModelicaInteger, inDimension::DAE.Dimension, inDimensionLst::DAE.Dimensions, inIntegerLst::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inBoolean::Bool, inComment::SCode.Comment, info::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              checkDimensionGreaterThanZero(inDimension, inPrefix, inIdent, info)
              checkArrayModDimSize(inMod, inDimension, inPrefix, inIdent, info)
              (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph) = begin
                  local e::DAE.Exp
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local p::DAE.Properties
                  local cache::FCore.Cache
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local env::FCore.Graph
                  local compenv::FCore.Graph
                  local csets::DAE.Sets
                  local ty::DAE.Type
                  local st::ClassInf.SMNode
                  local ci_state::ClassInf.SMNode
                  local cr::DAE.ComponentRef
                  local ty_1::DAE.Type
                  local mod::DAE.Mod
                  local mod_1::DAE.Mod
                  local mod_2::DAE.Mod
                  local pre::Prefix.PrefixType
                  local n::String
                  local str1::String
                  local str2::String
                  local str3::String
                  local str4::String
                  local cl::SCode.Element
                  local attr::SCode.Attributes
                  local i::ModelicaInteger
                  local stop::ModelicaInteger
                  local i_1::ModelicaInteger
                  local dim::DAE.Dimension
                  local dims::DAE.Dimensions
                  local idxs::List{DAE.Subscript}
                  local inst_dims::InstDims
                  local impl::Bool
                  local comment::SCode.Comment
                  local dae::DAE.DAElist
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local daeLst::DAE.DAElist
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local s::DAE.Subscript
                  local clBase::SCode.Element
                  local path::Absyn.Path
                  local absynAttr::SCode.Attributes
                  local scodeMod::SCode.Mod
                  local mod2::DAE.Mod
                  local mod3::DAE.Mod
                  local enum_lit::Absyn.Path
                  local pf::SCode.Prefixes
                  local store::UnitAbsyn.InstStore
                   #=  component environment If is a function var.
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inState, inMod, inPrefix, inIdent, inElement, inPrefixes, inInteger, inDimension, inDimensionLst, inIntegerLst, inInstDims, inBoolean, inComment, info, inGraph, inSets) begin
                  (cache, env, ih, store, ClassInf.FUNCTION(__), mod, pre, n, (cl, _), _, _, dim, _, _, inst_dims, _, _, _, graph, csets)  => begin
                      @match true = Expression.dimensionUnknownOrExp(dim)
                      @match SOME(DAE.TYPED(modifierAsExp = e, properties = p)) = Mod.modEquation(mod)
                      (cache, env_1, ih, store, _, _, ty, _, _, graph) = Inst.instClass(cache, env, ih, store, mod, pre, cl, inst_dims, true, InstTypes.INNER_CALL(), graph, csets) #= Which has an expression binding =#
                      ty_1 = Types.simplifyType(ty)
                      (cache, cr) = PrefixUtil.prefixCref(cache, env, ih, pre, ComponentReference.makeCrefIdent(n, ty_1, nil)) #= check their types =#
                      (rhs, _) = Types.matchProp(e, p, DAE.PROP(ty, DAE.C_VAR()), true)
                      source = ElementSource.createElementSource(info, FGraphUtil.getScopePath(env), pre)
                      lhs = Expression.makeCrefExp(cr, ty_1)
                      dae = InstSection.makeDaeEquation(lhs, rhs, source, SCode.NON_INITIAL())
                    (cache, env_1, ih, store, dae, inSets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, (cl, attr), pf, i, _, dims, idxs, inst_dims, impl, comment, _, graph, csets)  => begin
                      @match false = Expression.dimensionKnown(inDimension)
                      e = DAE.ICONST(i)
                      s = DAE.INDEX(e)
                      mod = Mod.lookupIdxModification(mod, e)
                      (cache, compenv, ih, store, daeLst, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, _cons(s, idxs), inst_dims, impl, comment, info, graph, csets)
                    (cache, compenv, ih, store, daeLst, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, _, pre, n, (cl, attr), pf, _, DAE.DIM_INTEGER(0), dims, idxs, inst_dims, impl, comment, _, graph, csets)  => begin
                      ErrorExt.setCheckpoint("instArray Real[0]")
                      e = DAE.ICONST(0)
                      s = DAE.INDEX(e)
                      mod = Mod.filterRedeclares(inMod)
                      mod = Mod.lookupIdxModification(mod, e)
                      (cache, compenv, ih, store, _, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, dims, _cons(s, idxs), inst_dims, impl, comment, info, graph, csets)
                      ErrorExt.rollBack("instArray Real[0]")
                    (cache, compenv, ih, store, DAE.emptyDae, csets, ty, graph)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _, DAE.DIM_INTEGER(0), _, _, _, _, _, _, _, _)  => begin
                      ErrorExt.delCheckpoint("instArray Real[0]")
                    fail()
                  end

                  (cache, env, ih, store, ci_state, _, _, _, (_, _), _, _, DAE.DIM_INTEGER(integer = stop), _, _, _, _, _, _, graph, csets)  => begin
                      (cache, env, ih, store, dae, csets, ty, graph) = instArrayDimInteger(cache, env, ih, store, ci_state, inMod, inPrefix, inIdent, inElement, inPrefixes, stop, inDimensionLst, inIntegerLst, inInstDims, inBoolean, inComment, info, graph, csets)
                    (cache, env, ih, store, dae, csets, ty, graph)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, (cl, attr), pf, _, DAE.DIM_ENUM(__), dims, idxs, inst_dims, impl, comment, _, graph, csets)  => begin
                    instArrayDimEnum(cache, env, ih, store, ci_state, mod, pre, n, cl, attr, pf, inDimension, dims, idxs, inst_dims, impl, comment, info, graph, csets)
                  end

                  (cache, env, ih, store, ci_state, mod, pre, n, (cl, attr), pf, _, DAE.DIM_BOOLEAN(__), dims, idxs, inst_dims, impl, comment, _, graph, csets)  => begin
                      mod_1 = Mod.lookupIdxModification(mod, DAE.BCONST(false))
                      mod_2 = Mod.lookupIdxModification(mod, DAE.BCONST(true))
                      (cache, env_1, ih, store, dae1, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod_1, pre, n, cl, attr, pf, dims, _cons(DAE.INDEX(DAE.BCONST(false)), idxs), inst_dims, impl, comment, info, graph, csets)
                      (cache, _, ih, store, dae2, csets, ty, graph) = instVar2(cache, env, ih, store, ci_state, mod_2, pre, n, cl, attr, pf, dims, _cons(DAE.INDEX(DAE.BCONST(true)), idxs), inst_dims, impl, comment, info, graph, csets)
                      daeLst = DAEUtil.joinDaes(dae1, dae2)
                    (cache, env_1, ih, store, daeLst, csets, ty, graph)
                  end

                  (_, _, _, _, ci_state, mod, pre, n, (_, _), _, i, _, _, idxs, _, _, _, _, _, _)  => begin
                      @shouldFail _ = Mod.lookupIdxModification(mod, DAE.ICONST(i))
                      str1 = PrefixUtil.printPrefixStrIgnoreNoPre(PrefixUtil.prefixAdd(n, nil, nil, pre, SCode.VAR(), ci_state, info))
                      str2 = "[" + stringDelimitList(ListUtil.map(idxs, ExpressionDump.printSubscriptStr), ", ") + "]"
                      str3 = Mod.prettyPrintMod(mod, 1)
                      str4 = PrefixUtil.printPrefixStrIgnoreNoPre(pre) + "(" + n + str2 + "=" + str3 + ")"
                      str2 = str1 + str2
                      Error.addSourceMessage(Error.MODIFICATION_INDEX_NOT_FOUND, list(str1, str4, str2, str3), info)
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Inst.instArray failed: " + inIdent)
                      fail()
                  end
                end
              end
               #=  set the source of this element
               =#
               #=  dae = DAEUtil.joinDaes(dae,DAEUtil.extractFunctions(dae1));
               =#
               #=  Special case when instantiating Real[0]. We need to know the type
               =#
               #=  Normal modifiers doesn't really matter since the empty array will be
               =#
               #=  removed anyway, and causes issues since you can't look up an element
               =#
               #=  in an empty array. But redeclares are still needed to get the correct
               =#
               #=  types, so we filter out only the redeclares.
               =#
               #=  Keep the errors if we somehow fail
               =#
               #=  Handle DIM_INTEGER, where the dimension is >0
               =#
               #=  Instantiate an array whose dimension is determined by an enumeration.
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

         #= When an array is instantiated by instVar, this function is used to go through all the array elements and instantiate each array element separately.
        Special case for DIM_INTEGER: tail-recursive implementation since the number of dimensions may grow arbitrarily large. =#
        function instArrayDimInteger(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inName::String, inElement::Tuple{<:SCode.Element, SCode.Attributes}, inPrefixes::SCode.Prefixes, inDimensionSize::ModelicaInteger, inRestDimensions::DAE.Dimensions, inSubscripts::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, inComment::SCode.Comment, inInfo::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outType::DAE.Type = DAE.T_UNKNOWN_DEFAULT
              local outSets::DAE.Sets = inSets
              local outDae::DAE.DAElist = DAE.emptyDae
              local outStore::UnitAbsyn.InstStore = inStore
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local c::SCode.Element
              local cls::SCode.Element
              local mod::DAE.Mod
              local imod::DAE.Mod
              local cls_path::Absyn.Path
              local smod::SCode.Mod
              local attr::SCode.Attributes
              local e::DAE.Exp
              local s::DAE.Subscript
              local inst_dims::List{List{DAE.Dimension}}
              local dae::DAE.DAElist

              (cls, mod, attr, inst_dims) = begin
                @match inElement begin
                  (c && SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(cls_path, SOME(_)), modifications = smod)), attr)  => begin
                       #=  adrpo: if a class is derived WITH AN ARRAY DIMENSION we should instVar2
                       =#
                       #=  the derived from type not the actual type!!!
                       =#
                      (_, cls, _) = Lookup.lookupClass(outCache, outEnv, cls_path, SOME(c.info))
                       #= /* adrpo: TODO: myMerge also the attributes, i.e.:
                                 type A = input discrete flow Integer[3];
                                 A x; <-- input discrete flow IS NOT propagated even if it should. FIXME!
                               */ =#
                       #= SOME(attr3) = SCodeUtil.mergeAttributes(attr,SOME(absynAttr));
                       =#
                      smod = InstUtil.chainRedeclares(inMod, smod)
                      (_, mod) = Mod.elabMod(outCache, outEnv, outIH, inPrefix, smod, inImpl, Mod.DERIVED(cls_path), inInfo)
                      mod = Mod.myMerge(inMod, mod)
                    (cls, mod, attr, nil)
                  end

                  (cls, attr)  => begin
                    (cls, inMod, attr, inInstDims)
                  end
                end
              end
              for i in inDimensionSize:(-1):1
                e = DAE.ICONST(i)
                imod = Mod.lookupIdxModification(mod, e)
                s = DAE.INDEX(e)
                (outCache, outEnv, outIH, outStore, dae, outSets, outType, outGraph) = instVar2(outCache, inEnv, outIH, outStore, inState, imod, inPrefix, inName, cls, attr, inPrefixes, inRestDimensions, _cons(s, inSubscripts), inst_dims, inImpl, inComment, inInfo, outGraph, outSets)
                outDae = DAEUtil.joinDaes(dae, outDae)
              end
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

        function instArrayDimEnum(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inState::ClassInf.SMNode, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inName::String, inClass::SCode.Element, inAttributes::SCode.Attributes, inPrefixes::SCode.Prefixes, inDimension::DAE.Dimension, inRestDimensions::DAE.Dimensions, inSubscripts::List{<:DAE.Subscript}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, inComment::SCode.Comment, inInfo::SourceInfo, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outType::DAE.Type = DAE.T_UNKNOWN_DEFAULT
              local outSets::DAE.Sets = inSets
              local outDae::DAE.DAElist = DAE.emptyDae
              local outStore::UnitAbsyn.InstStore = inStore
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local enum_path::Absyn.Path
              local enum_lit_path::Absyn.Path
              local literals::List{String}
              local i::ModelicaInteger = 1
              local e::DAE.Exp
              local mod::DAE.Mod
              local dae::DAE.DAElist

              @match DAE.DIM_ENUM(enumTypeName = enum_path, literals = literals) = inDimension
              for lit in literals
                enum_lit_path = AbsynUtil.joinPaths(enum_path, Absyn.IDENT(lit))
                e = DAE.ENUM_LITERAL(enum_lit_path, i)
                mod = Mod.lookupIdxModification(inMod, e)
                i = i + 1
                (outCache, outEnv, outIH, outStore, dae, outSets, outType, outGraph) = instVar2(outCache, inEnv, outIH, outStore, inState, mod, inPrefix, inName, inClass, inAttributes, inPrefixes, inRestDimensions, _cons(DAE.INDEX(e), inSubscripts), inInstDims, inImpl, inComment, inInfo, outGraph, outSets)
                outDae = DAEUtil.joinDaes(outDae, dae)
              end
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outGraph)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

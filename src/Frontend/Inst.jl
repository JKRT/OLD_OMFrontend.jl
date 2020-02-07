  module Inst


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    Type_a = Any

    BasicTypeAttrTyper = Function

    InstFunc = Function

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

        import AbsynUtil

        import ClassInf

        # import Connect

        import ConnectionGraph

        import DAE

        import FCore

        import FCoreUtil

        import InnerOuterTypes

        import InnerOuter

        import InstTypes

        import Mod

        import Prefix

        import SCode

        import UnitAbsyn
         #=  **
         =#
         #=  These type aliases are introduced to make the code a little more readable.
         =#
         #=  **
         =#

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuterTypes.InstHierarchy  #= an instance hierarchy =#

        InstDims = InstTypes.InstDims



         #=  protected imports
         =#

        import AbsynToSCode
        import BaseHashTable
        import Builtin
        import Ceval
        import ConnectUtil
        import ComponentReference
        import Config
        import DAEUtil
        import Debug
        import Dump
        import ElementSource
        import Error
        import ErrorExt
        import ExecStat
        import Expression
        import ExpressionDump
        import Flags
        import FGraph
        import FGraphUtil
        import FGraphBuildEnv
        import FNode
        import GC
        import Global
        import HashTable
        import HashTable5
        import InstHashTable
        import InstMeta
        import InstSection
        import InstBinding
        import InstVar
        import InstFunction
        import InstUtil
        import InstExtends
        import ListUtil
        import Lookup
        import Mutable
        # import OperatorOverloading
        import PrefixUtil
        import SCodeUtil
        import SCodeInstUtil
        import StringUtil
        import Static
        import Types
        import UnitParserExt
        import Util
        import Values
        import ValuesUtil
        import System
        import SCodeDump
        import UnitAbsynBuilder
        import InstStateMachineUtil
        # import NFUnitCheck
        import DAEDump

        MutableType = Mutable.MutableType

         #=  BTH
         =#

         #=  instantiate a class.
         if this function fails with stack overflow, it will be caught in the caller =#
        function instantiateClass_dispatch(inCache::FCore.Cache, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path, doSCodeDep::Bool #= Do SCode dependency (if the debug flag is also enabled) =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDAElist::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDAElist) = begin
                  local path::Absyn.Path
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local dae1::DAE.DAElist
                  local dae::DAE.DAElist
                  local dae2::DAE.DAElist
                  local cdecls::List{SCode.Element}
                  local name2::String
                  local n::String
                  local pathstr::String
                  local name::String
                  local cdef::SCode.Element
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local graph::ConnectionGraph.ConnectionGraphType
                  local source::DAE.ElementSource #= the origin of the element =#
                  local daeElts::List{DAE.Element}
                  local cmt::Option{SCode.Comment}
                   #=  top level class
                   =#
                @match (inCache, inIH, inProgram, inPath) begin
                  (cache, ih, cdecls && _ <| _, path && Absyn.IDENT(__))  => begin
                      cache = FCoreUtil.setCacheClassName(cache, path)
                      if doSCodeDep
                        cdecls = InstUtil.scodeFlatten(cdecls, inPath)
                        ExecStat.execStat("FrontEnd - scodeFlatten")
                      end
                      println("Inst.instantiateClass_dispatch 1")
                      (cache, env) = Builtin.initialGraph(cache)
                      println("Inst.instantiateClass_dispatch 2")
                      env = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      println("Inst.instantiateClass_dispatch 3")
                      source = ElementSource.addElementSourcePartOfOpt(DAE.emptyElementSource, FGraphUtil.getScopePath(env))
                      if Flags.isSet(Flags.GC_PROF)
                        print(GC.profStatsStr(GC.getProfStats(), head = "GC stats after pre-frontend work (building graphs):") + "\\n")
                      end
                      ExecStat.execStat("FrontEnd - mkProgramGraph")
                      println("Inst.instantiateClass_dispatch 4")
                      (cache, env, ih, dae2) = instClassInProgram(cache, env, ih, cdecls, path, source)
                      println("Inst.instantiateClass_dispatch 5")
                      InstHashTable.release()
                    (cache, env, ih, dae2)
                  end

                  (cache, ih, cdecls && _ <| _, path && Absyn.QUALIFIED(__))  => begin
                      cache = FCoreUtil.setCacheClassName(cache, path)
                      if doSCodeDep
                        cdecls = InstUtil.scodeFlatten(cdecls, inPath)
                        ExecStat.execStat("FrontEnd - scodeFlatten")
                      end
                      pathstr = AbsynUtil.pathString(path)
                      (cache, env) = Builtin.initialGraph(cache)
                      env = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      @match (cache, cdef && SCode.CLASS(name = n), env) = Lookup.lookupClass(cache, env, path, SOME(AbsynUtil.dummyInfo))
                      if Flags.isSet(Flags.GC_PROF)
                        print(GC.profStatsStr(GC.getProfStats(), head = "GC stats after pre-frontend work (building graphs):") + "\\n")
                      end
                      ExecStat.execStat("FrontEnd - mkProgramGraph")
                      (cache, env, ih, _, dae, _, _, _, _, _) = instClass(cache, env, ih, UnitAbsynBuilder.emptyInstStore(), DAE.NOMOD(), makeTopComponentPrefix(env, n), cdef, nil, false, InstTypes.TOP_CALL(), ConnectionGraph.EMPTY, DAE.emptySet) #= impl =#
                      dae = InstUtil.reEvaluateInitialIfEqns(cache, env, dae, true)
                      source = ElementSource.addElementSourcePartOfOpt(DAE.emptyElementSource, FGraphUtil.getScopePath(env))
                      daeElts = DAEUtil.daeElements(dae)
                      cmt = SCodeUtil.getElementComment(cdef)
                      dae = DAE.DAE_LIST(list(DAE.COMP(pathstr, daeElts, source, cmt)))
                      InstHashTable.release()
                    (cache, env, ih, dae)
                  end
                end
              end
          (outCache, outEnv, outIH, outDAElist)
        end

         #= To enable interactive instantiation, an arbitrary class in the program
          needs to be possible to instantiate. This function performs the same
          action as instProgram, but given a specific class to instantiate.

           First, all the class definitions are added to the environment without
          modifications, and then the specified class is instantiated in the
          function instClassInProgram =#
        function instantiateClass(inCache::FCore.Cache, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path, doSCodeDep::Bool = true #= Do SCode dependency (if the debug flag is also enabled) =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDAElist::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              println("Inst.instantiateClass 1")

              (outCache, outEnv, outIH, outDAElist) = instantiateClass_dispatch(inCache, inIH, inProgram, inPath, doSCodeDep)

              println("Inst.instantiateClass 2")

              (outCache, outEnv, outIH, outDAElist)
        end

         #= Author: BZ, 2009-07
         This is a function for instantiating partial 'top' classes.
         It does so by converting the partial class into a non partial class.
         Currently used by: MathCore.modelEquations, CevalScript.checkModel =#
        function instantiatePartialClass(inCache::FCore.Cache, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDAElist::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDAElist) = begin
                  local cr::Absyn.Path
                  local path::Absyn.Path
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local dae1::DAE.DAElist
                  local dae::DAE.DAElist
                  local cdecls::List{SCode.Element}
                  local name2::String
                  local n::String
                  local pathstr::String
                  local name::String
                  local cname_str::String
                  local cdef::SCode.Element
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local daeElts::List{DAE.Element}
                  local funcs::DAE.FunctionTree
                  local cmt::Option{SCode.Comment}
                @matchcontinue (inCache, inIH, inProgram, inPath) begin
                  (_, _,  nil(), _)  => begin
                      Error.addMessage(Error.NO_CLASSES_LOADED, nil)
                    fail()
                  end

                  (cache, ih, cdecls && _ <| _, path && Absyn.IDENT(__))  => begin
                      (cache, env) = Builtin.initialGraph(cache)
                      env_1 = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      cdecls = ListUtil.map1(cdecls, SCodeUtil.classSetPartial, SCode.NOT_PARTIAL())
                      source = ElementSource.addElementSourcePartOfOpt(DAE.emptyElementSource, FGraphUtil.getScopePath(env))
                      (cache, env_2, ih, dae) = instClassInProgram(cache, env_1, ih, cdecls, path, source)
                    (cache, env_2, ih, dae)
                  end

                  (cache, ih, cdecls && _ <| _, path && Absyn.QUALIFIED(__))  => begin
                      (cache, env) = Builtin.initialGraph(cache)
                      env_1 = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      @match (cache, cdef, env_2) = Lookup.lookupClass(cache, env_1, path, SOME(AbsynUtil.dummyInfo))
                      @match SCode.CLASS(name = n) = cdef
                      cdef = SCodeUtil.classSetPartial(cdef, SCode.NOT_PARTIAL())
                      (cache, env_2, ih, _, dae, _, _, _, _, _) = instClass(cache, env_2, ih, UnitAbsynBuilder.emptyInstStore(), DAE.NOMOD(), makeTopComponentPrefix(env_2, n), cdef, nil, false, InstTypes.TOP_CALL(), ConnectionGraph.EMPTY, DAE.emptySet) #= impl =#
                      pathstr = AbsynUtil.pathString(path)
                      source = ElementSource.addElementSourcePartOfOpt(DAE.emptyElementSource, FGraphUtil.getScopePath(env))
                      daeElts = DAEUtil.daeElements(dae)
                      cmt = SCodeUtil.getElementComment(cdef)
                      dae = DAE.DAE_LIST(list(DAE.COMP(pathstr, daeElts, source, cmt)))
                    (cache, env_2, ih, dae)
                  end

                  (_, _, _, path) where (! Config.getGraphicsExpMode())  => begin
                      cname_str = AbsynUtil.pathString(path)
                      Error.addMessage(Error.ERROR_FLATTENING, list(cname_str))
                    fail()
                  end
                end
              end
               #= /* top level class */ =#
               #= /* class in package */ =#
               #=  set the source of this element
               =#
               #= /* error instantiating */ =#
               #= print(\" Error flattening partial, errors: \" + ErrorExt.printMessagesStr() + \"\\n\");
               =#
          (outCache, outEnv, outIH, outDAElist)
        end

        function makeTopComponentPrefix(inGraph::FGraphUtil.Graph, inName::Absyn.Ident) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              local p::Absyn.Path

               #= p := FGraphUtil.joinScopePath(inGraph, Absyn.IDENT(inName));
               =#
               #= outPrefix := Prefix.PREFIX(Prefix.PRE(\"$i\", {}, {}, Prefix.NOCOMPPRE(), ClassInf.MODEL(p)), Prefix.CLASSPRE(SCode.VAR()));
               =#
              outPrefix = Prefix.NOPRE()
          outPrefix
        end

         #= Instantiates a specific top level class in a Program. =#
        function instClassInProgram(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path, inSource::DAE.ElementSource) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDae::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae) = begin
                  local name::String
                  local cls::SCode.Element
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InstanceHierarchy
                  local dae::DAE.DAElist
                  local elts::List{DAE.Element}
                  local cmt::Option{SCode.Comment}
                @matchcontinue (inCache, inEnv, inIH, inProgram, inPath, inSource) begin
                  (_, _, _,  nil(), _, _)  => begin
                    (inCache, inEnv, inIH, DAE.emptyDae)
                  end

                  (_, _, _, _, Absyn.IDENT(name = ""), _)  => begin
                    (inCache, inEnv, inIH, DAE.emptyDae)
                  end

                  (_, _, _, _, Absyn.IDENT(name = name), _)  => begin
                      cls = InstUtil.lookupTopLevelClass(name, inProgram, true)
                      (cache, env, ih, _, dae, _, _, _, _, _) = instClass(inCache, inEnv, inIH, UnitAbsynBuilder.emptyInstStore(), DAE.NOMOD(), makeTopComponentPrefix(inEnv, name), cls, nil, false, InstTypes.TOP_CALL(), ConnectionGraph.EMPTY, DAE.emptySet)
                      dae = InstUtil.reEvaluateInitialIfEqns(cache, env, dae, true)
                      elts = DAEUtil.daeElements(dae)
                      cmt = SCodeUtil.getElementComment(cls)
                      dae = DAE.DAE_LIST(list(DAE.COMP(name, elts, inSource, cmt)))
                    (cache, env, ih, dae)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("Inst.instClassInProgram failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outEnv, outIH, outDae)
        end

         #= Instantiation of a class can be either implicit or normal.
          This function is used in both cases. When implicit instantiation
          is performed, the last argument is true, otherwise it is false.

          Instantiating a class consists of the following steps:
           o Create a new frame on the environment
           o Initialize the class inference state machine
           o Instantiate all the elements and equations
           o Generate equations from the connection sets built during instantiation =#
        function instClass(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inClass::SCode.Element, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inBoolean::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, ClassInf.SMNode, Option{SCode.Attributes}, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local optDerAttr::Option{SCode.Attributes}
              local outState::ClassInf.SMNode
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local cache::FCore.Cache

              (cache, outEnv, outIH, outStore, outDae, outSets, outType, outState, optDerAttr, outGraph) = begin
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_3::FCore.Graph
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local csets::DAE.Sets
                  local n::String
                  local scopeName::String
                  local strDepth::String
                  local impl::Bool
                  local callscope_1::Bool
                  local isFn::Bool
                  local notIsPartial::Bool
                  local isPartialFn::Bool
                  local recursionDepthReached::Bool
                  local partialPrefix::SCode.Partial
                  local encflag::SCode.Encapsulated
                  local ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local dae1::DAE.DAElist
                  local dae1_1::DAE.DAElist
                  local dae::DAE.DAElist
                  local tys::List{DAE.Var}
                  local bc_ty::Option{DAE.Type}
                  local fq_class::Absyn.Path
                  local ty::DAE.Type
                  local c::SCode.Element
                  local r::SCode.Restriction
                  local inst_dims::InstDims
                  local callscope::InstTypes.CallingScope
                  local oDA::Option{SCode.Attributes}
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local equalityConstraint::DAE.EqualityConstraint
                  local info::SourceInfo
                  local store::UnitAbsyn.InstStore
                   #=  adrpo: ONLY when running checkModel we should be able to instantiate partial classes
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inMod, inPrefix, inClass, inInstDims, inBoolean, inCallingScope, inGraph, inSets) begin
                  (cache, _, _, store, _, _, SCode.CLASS(name = n, partialPrefix = SCode.PARTIAL(__), restriction = r, info = info), _, _, _, _, _)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      @match false = SCodeUtil.isFunctionRestriction(r)
                      c = SCodeUtil.setClassPartialPrefix(SCode.NOT_PARTIAL(), inClass)
                      if ! Config.getGraphicsExpMode()
                        Error.addSourceMessage(Error.INST_PARTIAL_CLASS_CHECK_MODEL_WARNING, list(n), info)
                      end
                      (cache, env, ih, store, dae, csets, ty, ci_state_1, oDA, graph) = instClass(inCache, inEnv, inIH, store, inMod, inPrefix, c, inInstDims, inBoolean, inCallingScope, inGraph, inSets)
                    (cache, env, ih, store, dae, csets, ty, ci_state_1, oDA, graph)
                  end

                  (cache, env, ih, store, mod, pre, c && SCode.CLASS(name = n, encapsulatedPrefix = encflag, restriction = r, partialPrefix = partialPrefix, info = info), inst_dims, impl, callscope, graph, _)  => begin
                      recursionDepthReached = listLength(FGraphUtil.currentScope(env)) < Global.recursionDepthLimit
                      if ! recursionDepthReached
                        scopeName = FGraphUtil.printGraphPathStr(env)
                        strDepth = intString(Global.recursionDepthLimit)
                        Error.addSourceMessage(Error.RECURSION_DEPTH_REACHED, list(strDepth, scopeName), info)
                        fail()
                      end
                      println("Inst.instClass 1: " + n)
                      isFn = SCodeUtil.isFunctionRestriction(r)
                      notIsPartial = ! SCodeUtil.partialBool(partialPrefix)
                      isPartialFn = isFn && SCodeUtil.partialBool(partialPrefix)
                      @match true = notIsPartial || isPartialFn
                      env_1 = FGraphUtil.openScope(env, encflag, n, FGraphUtil.restrictionToScopeType(r))
                      ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env_1))
                      csets = ConnectUtil.newSet(pre, inSets)
                      println("Inst.instClass 2: " + n)
                      (cache, env_3, ih, store, dae1, csets, ci_state_1, tys, bc_ty, oDA, equalityConstraint, graph) = instClassIn(cache, env_1, ih, store, mod, pre, ci_state, c, SCode.PUBLIC(), inst_dims, impl, callscope, graph, csets, NONE())
                      println("Inst.instClass 3: " + n)
                      csets = ConnectUtil.addSet(inSets, csets)
                      (cache, fq_class) = makeFullyQualifiedIdent(cache, env, n)
                      callscope_1 = InstUtil.isTopCall(callscope)
                      dae1_1 = DAEUtil.addComponentType(dae1, fq_class)
                      InstUtil.reportUnitConsistency(callscope_1, store)
                      (csets, _, graph) = InnerOuter.retrieveOuterConnections(cache, env_3, ih, pre, csets, callscope_1, graph)
                      dae = ConnectUtil.equations(callscope_1, csets, dae1_1, graph, AbsynUtil.pathString(AbsynUtil.makeNotFullyQualified(fq_class)))
                      ty = InstUtil.mktype(fq_class, ci_state_1, tys, bc_ty, equalityConstraint, c, InstUtil.extractComment(dae.elementLst))
                      dae = InstUtil.updateDeducedUnits(callscope_1, store, dae)
                      ty = InstUtil.fixInstClassType(ty, isPartialFn)
                    (cache, env_3, ih, store, dae, csets, ty, ci_state_1, oDA, graph)
                  end

                  (cache, _, _, _, _, _, SCode.CLASS(name = n, partialPrefix = SCode.PARTIAL(__), info = info), _, false, _, _, _)  => begin
                      if ! Config.getGraphicsExpMode()
                        Error.addSourceMessage(Error.INST_PARTIAL_CLASS, list(n), info)
                      end
                    fail()
                  end

                  (_, env, _, _, _, _, SCode.CLASS(name = n), _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- Inst.instClass: " + n + " in env: " + FGraphUtil.printGraphPathStr(env) + " failed\\n")
                    fail()
                  end
                end
              end
          (cache, outEnv, outIH, outStore, outDae, outSets, outType, outState, optDerAttr, outGraph)
        end

         #= author: PA
          This function instantiates a basictype class, e.g. Real, Integer, Real[2],
          etc. This function has the same functionality as instClass except that
          it will create array types when needed. (instClass never creates array
          types). This is needed because this function is used to instantiate classes
          extending from basic types. See instBasictypeBaseclass.
          NOTE: This function should only be called from instBasictypeBaseclass.
          This is new functionality in Modelica v 2.2. =#
        function instClassBasictype(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inClass::SCode.Element, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImplicit::Bool, inCallingScope::InstTypes.CallingScope, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, DAE.Type, List{DAE.Var}, ClassInf.SMNode}
              local outState::ClassInf.SMNode
              local outTypeVars::List{DAE.Var} #= attributes of builtin types =#
              local outType::DAE.Type
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outTypeVars, outState) = begin
                  local env_1::FCore.Graph
                  local env_3::FCore.Graph
                  local env::FCore.Graph
                  local ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local c_1::SCode.Element
                  local c::SCode.Element
                  local dae1::DAE.DAElist
                  local dae1_1::DAE.DAElist
                  local dae::DAE.DAElist
                  local csets::DAE.Sets
                  local tys::List{DAE.Var}
                  local bc_ty::Option{DAE.Type}
                  local fq_class::Absyn.Path
                  local encflag::SCode.Encapsulated
                  local impl::Bool
                  local ty::DAE.Type
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local n::String
                  local r::SCode.Restriction
                  local inst_dims::InstDims
                  local callscope::InstTypes.CallingScope
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local store::UnitAbsyn.InstStore
                @match (inCache, inEnv, inIH, inStore, inMod, inPrefix, inClass, inInstDims, inImplicit, inCallingScope, inSets) begin
                  (cache, env, ih, store, mod, pre, c && SCode.CLASS(name = n, encapsulatedPrefix = encflag, restriction = r), inst_dims, impl, _, _)  => begin
                      env_1 = FGraphUtil.openScope(env, encflag, n, FGraphUtil.restrictionToScopeType(r))
                      ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env_1))
                      c_1 = SCodeUtil.classSetPartial(c, SCode.NOT_PARTIAL())
                      (cache, env_3, ih, store, dae1, csets, ci_state_1, tys, bc_ty, _, _, _) = instClassIn(cache, env_1, ih, store, mod, pre, ci_state, c_1, SCode.PUBLIC(), inst_dims, impl, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, inSets, NONE())
                      (cache, fq_class) = makeFullyQualifiedIdent(cache, env_3, n)
                      dae1_1 = DAEUtil.addComponentType(dae1, fq_class)
                      dae = dae1_1
                      ty = InstUtil.mktypeWithArrays(fq_class, ci_state_1, tys, bc_ty, c, InstUtil.extractComment(dae.elementLst))
                    (cache, env_3, ih, store, dae, csets, ty, tys, ci_state_1)
                  end

                  (_, _, _, _, _, _, SCode.CLASS(__), _, _, _, _)  => begin
                    fail()
                  end
                end
              end
               #= /* impl */ =#
               #= fprintln(Flags.FAILTRACE, \"- Inst.instClassBasictype: \" + n + \" failed\");
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outType, outTypeVars #= attributes of builtin types =#, outState)
        end

         #=
          This rule instantiates the contents of a class definition, with a new
          environment already setup.
          The *implicitInstantiation* boolean indicates if the class should be
          instantiated implicit, i.e. without generating DAE.
          The last option is a even stronger indication of implicit instantiation,
          used when looking up variables in packages. This must be used because
          generation of functions in implicit instanitation (according to
          *implicitInstantiation* boolean) can cause circular dependencies
          (e.g. if a function uses a constant in its body) =#
        function instClassIn(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inClass::SCode.Element, inVisibility::SCode.Visibility, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, implicitInstantiation::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEqualityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local outType::Option{DAE.Type}
              local outVars::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outType, optDerAttr, outEqualityConstraint, outGraph) = begin
                  local bc::Option{DAE.Type}
                  local env::FCore.Graph
                  local ci_state::ClassInf.SMNode
                  local c::SCode.Element
                  local r::SCode.Restriction
                  local n::String
                  local dae::DAE.DAElist
                  local csets::DAE.Sets
                  local tys::List{DAE.Var}
                  local cache::FCore.Cache
                  local oDA::Option{SCode.Attributes}
                  local equalityConstraint::DAE.EqualityConstraint
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local s1::String
                  local s2::String
                  local store::UnitAbsyn.InstStore
                  local io::Absyn.InnerOuter
                  local info::SourceInfo
                  local encflag::SCode.Encapsulated
                   #=  if the class is no outer: regular, or inner
                   =#
                @matchcontinue inClass begin
                  SCode.CLASS(prefixes = SCode.PREFIXES(innerOuter = io))  => begin
                      @match true = boolOr(AbsynUtil.isNotInnerOuter(io), AbsynUtil.isOnlyInner(io))
                      (cache, env, ih, store, ci_state, graph, csets, dae, tys, bc, oDA, equalityConstraint) = instClassIn2(inCache, inEnv, inIH, inStore, inMod, inPrefix, inState, inClass, inVisibility, inInstDims, implicitInstantiation, inCallingScope, inGraph, inSets, instSingleCref)
                    (cache, env, ih, store, dae, csets, ci_state, tys, bc, oDA, equalityConstraint, graph)
                  end

                  SCode.CLASS(name = n, restriction = r, encapsulatedPrefix = encflag, prefixes = SCode.PREFIXES(innerOuter = io))  => begin
                      @match true = boolOr(AbsynUtil.isInnerOuter(io), AbsynUtil.isOnlyOuter(io))
                      @match FCore.CL(status = FCore.CLS_INSTANCE(n)) = FNode.refData(FGraphUtil.lastScopeRef(inEnv))
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      env = FGraphUtil.openScope(env, encflag, n, FGraphUtil.restrictionToScopeType(r))
                      ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env))
                      @match InnerOuter.INST_INNER(innerElement = SOME(c)) = InnerOuter.lookupInnerVar(inCache, env, inIH, inPrefix, n, io)
                      (cache, env, ih, store, ci_state, graph, csets, dae, tys, bc, oDA, equalityConstraint) = instClassIn2(inCache, env, inIH, inStore, inMod, inPrefix, ci_state, c, inVisibility, inInstDims, implicitInstantiation, inCallingScope, inGraph, inSets, instSingleCref)
                    (cache, env, ih, store, dae, csets, ci_state, tys, bc, oDA, equalityConstraint, graph)
                  end

                  SCode.CLASS(name = n, prefixes = SCode.PREFIXES(innerOuter = io))  => begin
                      @match true = boolOr(AbsynUtil.isInnerOuter(io), AbsynUtil.isOnlyOuter(io))
                      n = FGraphUtil.getInstanceOriginalName(inEnv, n)
                      @match InnerOuter.INST_INNER(innerElement = SOME(c)) = InnerOuter.lookupInnerVar(inCache, inEnv, inIH, inPrefix, n, io)
                      (cache, env, ih, store, ci_state, graph, csets, dae, tys, bc, oDA, equalityConstraint) = instClassIn2(inCache, inEnv, inIH, inStore, inMod, inPrefix, inState, c, inVisibility, inInstDims, implicitInstantiation, inCallingScope, inGraph, inSets, instSingleCref)
                    (cache, env, ih, store, dae, csets, ci_state, tys, bc, oDA, equalityConstraint, graph)
                  end

                  SCode.CLASS(name = n, prefixes = SCode.PREFIXES(innerOuter = io), info = info)  => begin
                      @match true = boolOr(AbsynUtil.isInnerOuter(io), AbsynUtil.isOnlyOuter(io))
                      if ! Config.getGraphicsExpMode()
                        s1 = n
                        s2 = Dump.unparseInnerouterStr(io)
                        Error.addSourceMessage(Error.MISSING_INNER_CLASS, list(s1, s2), info)
                      end
                      (cache, env, ih, store, ci_state, graph, csets, dae, tys, bc, oDA, equalityConstraint) = instClassIn2(inCache, inEnv, inIH, inStore, inMod, inPrefix, inState, inClass, inVisibility, inInstDims, implicitInstantiation, inCallingScope, inGraph, inSets, instSingleCref)
                    (cache, env, ih, store, dae, csets, ci_state, tys, bc, oDA, equalityConstraint, graph)
                  end
                end
              end
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outType, optDerAttr, outEqualityConstraint, outGraph)
        end

         #= This rule instantiates the contents of a class definition, with a new
         environment already setup.
         The *implicitInstantiation* boolean indicates if the class should be
         instantiated implicit, i.e. without generating DAE.
         The last option is a even stronger indication of implicit instantiation,
         used when looking up variables in packages. This must be used because
         generation of functions in implicit instanitation (according to
         *implicitInstantiation* boolean) can cause circular dependencies
         (e.g. if a function uses a constant in its body) =#
        function instClassIn2(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuterTypes.InstHierarchy, store::UnitAbsyn.InstStore, mod::DAE.Mod, prefix::Prefix.PrefixType, state::ClassInf.SMNode, cls::SCode.Element, visibility::SCode.Visibility, instDims::List{Any #= <:List{<:DAE.Dimension} =#}, implicitInst::Bool, callingScope::InstTypes.CallingScope, graph::ConnectionGraph.ConnectionGraphType, sets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType, DAE.Sets, DAE.DAElist, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint}
              local equalityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local ty::Option{DAE.Type}
              local vars::List{DAE.Var}
              local dae::DAE.DAElist








              local cache_path::Absyn.Path
              local inputs::InstHashTable.CachedInstItemInputs
              local outputs::InstHashTable.CachedInstItemOutputs
              local bbx::Tuple{InstDims, Bool, DAE.Mod, DAE.Sets, ClassInf.SMNode, SCode.Element, Option{DAE.ComponentRef}}
              local bby::Tuple{InstDims, Bool, DAE.Mod, DAE.Sets, ClassInf.SMNode, SCode.Element, Option{DAE.ComponentRef}}
              local m::DAE.Mod
              local pre::Prefix.PrefixType
              local csets::DAE.Sets
              local st::ClassInf.SMNode
              local e::SCode.Element
              local dims::InstDims
              local impl::Bool
              local scr::Option{DAE.ComponentRef}
              local cs::InstTypes.CallingScope
              local cached_graph::ConnectionGraph.ConnectionGraphType

               #=  Packages derived from partial packages should do partialInstClass, since it
               =#
               #=  filters out a lot of things.
               =#
              if SCodeUtil.isPackage(cls) && SCodeUtil.isPartial(cls)
                (cache, env, ih, state) = partialInstClassIn(cache, env, ih, mod, prefix, state, cls, visibility, instDims, 0)
                dae = DAE.emptyDae
                vars = nil
                ty = NONE()
                optDerAttr = NONE()
                equalityConstraint = NONE()
                return (cache, env, ih, store, state, graph, sets, dae, vars, ty, optDerAttr, equalityConstraint)
              end
              cache_path = generateCachePath(env, cls, prefix, callingScope)
               #=  See if we have it in the cache.
               =#
              if Flags.isSet(Flags.CACHE)
                try
                  @match SOME(InstHashTable.FUNC_instClassIn(inputs, outputs)) <| _ <| nil = InstHashTable.get(cache_path)
                  @match (m, pre, csets, st, e, dims, impl, scr, cs) = inputs
                  @match SCode.CLASS() = e
                  InstUtil.prefixEqualUnlessBasicType(prefix, pre, cls)
                  if valueEq(dims, instDims) && impl == implicitInst && valueEq(m, mod) && valueEq(csets, sets) && valueEq(st, state) && valueEq(e, cls) && valueEq(scr, instSingleCref) && callingScopeCacheEq(cs, callingScope)
                    (env, dae, sets, state, vars, ty, optDerAttr, equalityConstraint, cached_graph) = outputs
                    graph = ConnectionGraph.myMerge(graph, cached_graph)
                    showCacheInfo("Full Inst Hit: ", cache_path)
                    return (cache, env, ih, store, state, graph, sets, dae, vars, ty, optDerAttr, equalityConstraint)
                  end
                catch ex
                  println("no inst full cache")
                  showerror(stderr, ex, catch_backtrace())
                end
              end
               #=  Are the important inputs the same?
               =#
               #=  Not found in cache, continue.
               =#
               #=  If not found in the cache, instantiate the class and add it to the cache.
               =#
              try
                inputs = (mod, prefix, sets, state, cls, instDims, implicitInst, instSingleCref, callingScope)
                (cache, env, ih, store, dae, sets, state, vars, ty, optDerAttr, equalityConstraint, graph) = instClassIn_dispatch(cache, env, ih, store, mod, prefix, state, cls, visibility, instDims, implicitInst, callingScope, graph, sets, instSingleCref)
                outputs = (env, dae, sets, state, vars, ty, optDerAttr, equalityConstraint, graph)
                showCacheInfo("Full Inst Add: ", cache_path)
                InstHashTable.addToInstCache(cache_path, SOME(InstHashTable.FUNC_instClassIn(inputs, outputs)), NONE())
              catch ex
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- Inst.instClassIn2 failed on class: " + SCodeUtil.elementName(cls) + " in environment: " + FGraphUtil.printGraphPathStr(env))
                fail()
              end
          (cache, env, ih, store, state, graph, sets, dae, vars, ty, optDerAttr, equalityConstraint)
        end

        function callingScopeCacheEq(inCallingScope1::InstTypes.CallingScope, inCallingScope2::InstTypes.CallingScope) ::Bool
              local outIsEq::Bool

              outIsEq = begin
                @match (inCallingScope1, inCallingScope2) begin
                  (InstTypes.TYPE_CALL(__), InstTypes.TYPE_CALL(__))  => begin
                    true
                  end

                  (InstTypes.TYPE_CALL(__), _)  => begin
                    false
                  end

                  (_, InstTypes.TYPE_CALL(__))  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outIsEq
        end

         #= This rule instantiates the contents of a class definition, with a new
          environment already setup.
          The *implicitInstantiation* boolean indicates if the class should be
          instantiated implicit, i.e. without generating DAE.
          The last option is a even stronger indication of implicit instantiation,
          used when looking up variables in packages. This must be used because
          generation of functions in implicit instanitation (according to
          *implicitInstantiation* boolean) can cause circular dependencies
          (e.g. if a function uses a constant in its body) =#
        function instClassIn_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inClass::SCode.Element, inVisibility::SCode.Visibility, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, implicitInstantiation::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEqualityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local outTypesTypeOption::Option{DAE.Type}
              local outTypesVarLst::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph) = begin
                  local bc::Option{DAE.Type}
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local mods::DAE.Mod
                  local pre::Prefix.PrefixType
                  local ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local c::SCode.Element
                  local inst_dims::InstDims
                  local impl::Bool
                  local vis::SCode.Visibility
                  local implstr::String
                  local n::String
                  local csets::DAE.Sets
                  local tys::List{DAE.Var}
                  local r::SCode.Restriction
                  local d::SCode.ClassDef
                  local cache::FCore.Cache
                  local oDA::Option{SCode.Attributes}
                  local callscope::InstTypes.CallingScope
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local dae::DAE.DAElist
                  local dae1::DAE.DAElist
                  local dae1_1::DAE.DAElist
                  local info::SourceInfo
                  local typ::DAE.Type
                  local env_2::FCore.Graph
                  local env_3::FCore.Graph
                  local els::List{SCode.Element}
                  local comp::List{Tuple{SCode.Element, DAE.Mod}}
                  local names::List{String}
                  local eqConstraint::DAE.EqualityConstraint
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local fq_class::Absyn.Path
                  local tys1::List{DAE.Var}
                  local tys2::List{DAE.Var}
                  local partialPrefix::SCode.Partial
                  local encapsulatedPrefix::SCode.Encapsulated
                  local store::UnitAbsyn.InstStore
                  local b::Bool
                  local typer::BasicTypeAttrTyper
                  local comment::SCode.Comment
                   #=  Builtin type (Real, Integer, etc.).
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inMod, inPrefix, inState, inClass, inVisibility, inInstDims, implicitInstantiation, inCallingScope, inGraph, inSets, instSingleCref) begin
                  (cache, env, ih, store, mods, pre, ci_state, SCode.CLASS(name = n), _, inst_dims, _, _, graph, _, _)  => begin
                      ty = getBasicTypeType(n)
                      typer = getBasicTypeAttrTyper(n)
                      ty = liftNonExpType(ty, inst_dims, Config.splitArrays())
                      tys = instBasicTypeAttributes(cache, env, mods, ty, typer, pre)
                      ty = Types.setTypeVars(ty, tys)
                      bc = arrayBasictypeBaseclass(inst_dims, ty)
                    (cache, env, ih, store, DAE.emptyDae, inSets, ci_state, tys, bc, NONE(), NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, c && SCode.CLASS(name = n, restriction = SCode.R_ENUMERATION(__), classDef = SCode.PARTS(elementLst = els), info = info), _, inst_dims, impl, callscope, graph, _, _)  => begin
                      names = SCodeUtil.componentNames(c)
                      Types.checkEnumDuplicateLiterals(names, info)
                      tys = instBasicTypeAttributes(cache, env, mods, DAE.T_ENUMERATION_DEFAULT, getEnumAttributeType, pre)
                      ci_state_1 = ClassInf.trans(ci_state, ClassInf.NEWDEF())
                      comp = InstUtil.addNomod(els)
                      (cache, env_1, ih) = InstUtil.addComponentsToEnv(cache, env, ih, mods, pre, ci_state_1, comp, impl)
                      (cache, env_2, ih, store, _, csets, ci_state_1, tys1, graph, _) = instElementList(cache, env_1, ih, store, mods, pre, ci_state_1, comp, inst_dims, impl, callscope, graph, inSets, true)
                      (cache, fq_class) = makeFullyQualifiedIdent(cache, env_2, n)
                      eqConstraint = InstUtil.equalityConstraint(env_2, els, info)
                      ty2 = DAE.T_ENUMERATION(NONE(), fq_class, names, tys1, tys)
                      bc = arrayBasictypeBaseclass(inst_dims, ty2)
                      bc = if isSome(bc)
                            bc
                          else
                            SOME(ty2)
                          end
                      ty = InstUtil.mktype(fq_class, ci_state_1, tys1, bc, eqConstraint, c, SCode.noComment)
                      (cache, env_3) = InstUtil.updateEnumerationEnvironment(cache, env_2, ty, c, ci_state_1)
                      tys2 = listAppend(tys, tys1)
                    (cache, env_3, ih, store, DAE.emptyDae, csets, ci_state_1, tys2, bc, NONE(), NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, c && SCode.CLASS(name = n, restriction = r, classDef = d, cmt = comment, info = info, partialPrefix = partialPrefix, encapsulatedPrefix = encapsulatedPrefix), vis, inst_dims, impl, callscope, graph, _, _)  => begin
                      ErrorExt.setCheckpoint("instClassParts")
                      @match false = InstUtil.isBuiltInClass(n) #= If failed above, no need to try again =#
                      _ = begin
                        @match r begin
                          SCode.R_ENUMERATION(__)  => begin
                            fail()
                          end

                          _  => begin
                              ()
                          end
                        end
                      end
                      (cache, env_1, ih, store, dae, csets, ci_state_1, tys, bc, oDA, eqConstraint, graph) = instClassdef(cache, env, ih, store, mods, pre, ci_state, n, d, r, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, callscope, graph, inSets, instSingleCref, comment, info)
                      dae = if SCodeUtil.isFunction(c) && ! impl
                            DAE.DAE_LIST(nil)
                          else
                            dae
                          end
                      ErrorExt.delCheckpoint("instClassParts")
                    (cache, env_1, ih, store, dae, csets, ci_state_1, tys, bc, oDA, eqConstraint, graph)
                  end

                  (cache, env, ih, store, _, _, ci_state, c && SCode.CLASS(__), _, _, impl, _, graph, _, _)  => begin
                      b = Flags.getConfigBool(Flags.CHECK_MODEL) && ! impl && SCodeUtil.isFunction(c)
                      if ! b
                        ErrorExt.delCheckpoint("instClassParts")
                        fail()
                      else
                        ErrorExt.rollBack("instClassParts")
                      end
                    (cache, env, ih, store, DAE.emptyDae, inSets, ci_state, nil, NONE(), NONE(), NONE(), graph)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  clsname = SCodeUtil.className(cls);
               =#
               #=  print(\"Ignore function\" + clsname + \"\\n\");
               =#
               #=  failure
               =#
               #= print(\"instClassIn(\");print(n);print(\") failed\\n\");
               =#
               #= fprintln(Flags.FAILTRACE, \"- Inst.instClassIn failed\" + n);
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph)
        end

        function liftNonExpType(inType::DAE.Type, inInstDims::InstDims, inSplitArrays::Bool) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local dims::List{DAE.Dimension}
                @match (inType, inInstDims, inSplitArrays) begin
                  (_, dims <| _, false)  => begin
                    Types.liftArrayListDims(inType, dims)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

        function getBasicTypeType(inName::String) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match inName begin
                  "Real"  => begin
                    DAE.T_REAL_DEFAULT
                  end

                  "Integer"  => begin
                    DAE.T_INTEGER_DEFAULT
                  end

                  "String"  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  "Boolean"  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  "Clock"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    DAE.T_CLOCK_DEFAULT
                  end
                end
              end
               #=  BTH
               =#
          outType
        end

        function getBasicTypeAttrTyper(inName::String) ::BasicTypeAttrTyper
              local outTyper::BasicTypeAttrTyper

              outTyper = begin
                @match inName begin
                  "Real"  => begin
                    getRealAttributeType
                  end

                  "Integer"  => begin
                    getIntAttributeType
                  end

                  "String"  => begin
                    getStringAttributeType
                  end

                  "Boolean"  => begin
                    getBoolAttributeType
                  end

                  "Clock"  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    getClockAttributeType
                  end
                end
              end
               #=  BTH
               =#
          outTyper
        end

        function getRealAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  ("quantity", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("unit", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("displayUnit", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("min", _, _)  => begin
                    inBaseType
                  end

                  ("max", _, _)  => begin
                    inBaseType
                  end

                  ("start", _, _)  => begin
                    inBaseType
                  end

                  ("fixed", _, _)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  ("nominal", _, _)  => begin
                    inBaseType
                  end

                  ("stateSelect", _, _)  => begin
                    InstBinding.stateSelectType
                  end

                  ("uncertain", _, _)  => begin
                    InstBinding.uncertaintyType
                  end

                  ("distribution", _, _)  => begin
                    InstBinding.distributionType
                  end

                  _  => begin
                        Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(inAttrName, "Real"), inInfo)
                      fail()
                  end
                end
              end
          outType
        end

        function getIntAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  ("quantity", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("min", _, _)  => begin
                    inBaseType
                  end

                  ("max", _, _)  => begin
                    inBaseType
                  end

                  ("start", _, _)  => begin
                    inBaseType
                  end

                  ("fixed", _, _)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  ("nominal", _, _)  => begin
                    inBaseType
                  end

                  ("uncertain", _, _)  => begin
                    InstBinding.uncertaintyType
                  end

                  ("distribution", _, _)  => begin
                    InstBinding.distributionType
                  end

                  _  => begin
                        Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(inAttrName, "Integer"), inInfo)
                      fail()
                  end
                end
              end
          outType
        end

        function getStringAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  ("quantity", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("start", _, _)  => begin
                    inBaseType
                  end

                  _  => begin
                        Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(inAttrName, "String"), inInfo)
                      fail()
                  end
                end
              end
          outType
        end

        function getBoolAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  ("quantity", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("start", _, _)  => begin
                    inBaseType
                  end

                  ("fixed", _, _)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  _  => begin
                        Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(inAttrName, "Boolean"), inInfo)
                      fail()
                  end
                end
              end
          outType
        end

         #=
        Author: BTH
        This function is supposed to fail since clock variables don't have attributes.
         =#
        function getClockAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  (_, _, _)  => begin
                    fail()
                  end
                end
              end
          outType
        end

        function getEnumAttributeType(inAttrName::String, inBaseType::DAE.Type, inInfo::SourceInfo) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                @match (inAttrName, inBaseType, inInfo) begin
                  ("quantity", _, _)  => begin
                    DAE.T_STRING_DEFAULT
                  end

                  ("min", _, _)  => begin
                    inBaseType
                  end

                  ("max", _, _)  => begin
                    inBaseType
                  end

                  ("start", _, _)  => begin
                    inBaseType
                  end

                  ("fixed", _, _)  => begin
                    DAE.T_BOOL_DEFAULT
                  end

                  _  => begin
                        Error.addSourceMessage(Error.MISSING_MODIFIED_ELEMENT, list(inAttrName, "enumeration(:)"), inInfo)
                      fail()
                  end
                end
              end
          outType
        end

        function instBasicTypeAttributes(inCache::FCore.Cache, inEnv::FCore.Graph, inMod::DAE.Mod, inBaseType::DAE.Type, inTypeFunc::BasicTypeAttrTyper, inPrefix::Prefix.PrefixType) ::List{DAE.Var}
              local outVars::List{DAE.Var}

              outVars = begin
                  local submods::List{DAE.SubMod}
                @match inMod begin
                  DAE.MOD(subModLst = submods)  => begin
                    ListUtil.map4(submods, instBasicTypeAttributes2, inCache, inEnv, inBaseType, inTypeFunc)
                  end

                  DAE.NOMOD(__)  => begin
                    nil
                  end

                  DAE.REDECL(__)  => begin
                    nil
                  end
                end
              end
          outVars
        end

        function instBasicTypeAttributes2(inSubMod::DAE.SubMod, inCache::FCore.Cache, inEnv::FCore.Graph, inBaseType::DAE.Type, inTypeFunc::BasicTypeAttrTyper) ::DAE.Var
              local outVar::DAE.Var

              outVar = begin
                  local name::DAE.Ident
                  local ty::DAE.Type
                  local exp::DAE.Exp
                  local val::Option{Values.Value}
                  local p::DAE.Properties
                  local info::SourceInfo
                @match inSubMod begin
                  DAE.NAMEMOD(ident = name, mod = DAE.MOD(binding = SOME(DAE.TYPED(modifierAsExp = exp, modifierAsValue = val, properties = p)), info = info))  => begin
                      ty = getRealAttributeType(name, inBaseType, info)
                    instBuiltinAttribute(inCache, inEnv, name, val, exp, ty, p)
                  end

                  DAE.NAMEMOD(ident = name)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.instBasicTypeAttributes2 failed on " + name)
                    fail()
                  end
                end
              end
          outVar
        end

         #= Help function to e.g. instRealClass, etc. =#
        function instBuiltinAttribute(inCache::FCore.Cache, inEnv::FCore.Graph, id::String, optVal::Option{<:Values.Value}, bind::DAE.Exp, inExpectedTp::DAE.Type, bindProp::DAE.Properties) ::DAE.Var
              local var::DAE.Var

              var = begin
                  local v::Values.Value
                  local t_1::DAE.Type
                  local bindTp::DAE.Type
                  local bind1::DAE.Exp
                  local vbind::DAE.Exp
                  local c::DAE.Const
                  local d::DAE.Dimension
                  local s::String
                  local s1::String
                  local s2::String
                  local expectedTp::DAE.Type
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @matchcontinue (inCache, inEnv, id, optVal, bind, inExpectedTp, bindProp) begin
                  (_, _, _, SOME(v), _, expectedTp, DAE.PROP(bindTp, c))  => begin
                      @match false = valueEq(c, DAE.C_VAR())
                      (bind1, t_1) = Types.matchType(bind, bindTp, expectedTp, true)
                      (vbind, _) = Types.matchType(ValuesUtil.valueExp(v), bindTp, expectedTp, true)
                      v = ValuesUtil.expValue(vbind)
                    DAE.TYPES_VAR(id, DAE.dummyAttrParam, t_1, DAE.EQBOUND(bind1, SOME(v), DAE.C_PARAM(), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (_, _, _, SOME(v), _, expectedTp, DAE.PROP(bindTp && DAE.T_ARRAY(dims = d <|  nil()), c))  => begin
                      @match false = valueEq(c, DAE.C_VAR())
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      expectedTp = Types.liftArray(expectedTp, d)
                      (bind1, t_1) = Types.matchType(bind, bindTp, expectedTp, true)
                      (vbind, _) = Types.matchType(ValuesUtil.valueExp(v), bindTp, expectedTp, true)
                      v = ValuesUtil.expValue(vbind)
                    DAE.TYPES_VAR(id, DAE.dummyAttrParam, t_1, DAE.EQBOUND(bind1, SOME(v), DAE.C_PARAM(), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (cache, env, _, _, _, expectedTp, DAE.PROP(bindTp, c))  => begin
                      @match false = valueEq(c, DAE.C_VAR())
                      (bind1, t_1) = Types.matchType(bind, bindTp, expectedTp, true)
                      (cache, v) = Ceval.ceval(cache, env, bind1, false, Absyn.NO_MSG(), 0)
                    DAE.TYPES_VAR(id, DAE.dummyAttrParam, t_1, DAE.EQBOUND(bind1, SOME(v), DAE.C_PARAM(), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (cache, env, _, _, _, expectedTp, DAE.PROP(bindTp && DAE.T_ARRAY(dims = d <|  nil()), c))  => begin
                      @match false = valueEq(c, DAE.C_VAR())
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      expectedTp = Types.liftArray(expectedTp, d)
                      (bind1, t_1) = Types.matchType(bind, bindTp, expectedTp, true)
                      (cache, v) = Ceval.ceval(cache, env, bind1, false, Absyn.NO_MSG(), 0)
                    DAE.TYPES_VAR(id, DAE.dummyAttrParam, t_1, DAE.EQBOUND(bind1, SOME(v), DAE.C_PARAM(), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (_, _, _, _, _, expectedTp, DAE.PROP(bindTp, c))  => begin
                      if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                        @match true = valueEq(c, DAE.C_VAR())
                      else
                        @match false = valueEq(c, DAE.C_VAR())
                      end
                      (bind1, t_1) = Types.matchType(bind, bindTp, expectedTp, true)
                    DAE.TYPES_VAR(id, DAE.dummyAttrParam, t_1, DAE.EQBOUND(bind1, NONE(), DAE.C_PARAM(), DAE.BINDING_FROM_DEFAULT_VALUE()), NONE())
                  end

                  (_, _, _, _, _, _, DAE.PROP(_, c))  => begin
                      @match true = valueEq(c, DAE.C_VAR())
                      s = ExpressionDump.printExpStr(bind)
                      Error.addMessage(Error.HIGHER_VARIABILITY_BINDING, list(id, "PARAM", s, "VAR"))
                    fail()
                  end

                  (_, _, _, _, _, expectedTp, DAE.PROP(bindTp, _))  => begin
                      @shouldFail (_, _) = Types.matchType(bind, bindTp, expectedTp, true)
                      s1 = "builtin attribute " + id + " of type " + Types.unparseType(bindTp)
                      s2 = Types.unparseType(expectedTp)
                      Error.addMessage(Error.TYPE_ERROR, list(s1, s2))
                    fail()
                  end

                  (_, _, _, SOME(v), _, expectedTp, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("instBuiltinAttribute failed for: " + id + " value binding: " + ValuesUtil.printValStr(v) + " binding: " + ExpressionDump.printExpStr(bind) + " expected type: " + Types.printTypeStr(expectedTp) + " type props: " + Types.printPropStr(bindProp))
                    fail()
                  end

                  (_, _, _, _, _, expectedTp, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("instBuiltinAttribute failed for: " + id + " value binding: NONE()" + " binding: " + ExpressionDump.printExpStr(bind) + " expected type: " + Types.printTypeStr(expectedTp) + " type props: " + Types.printPropStr(bindProp))
                    fail()
                  end
                end
              end
          var
        end

         #= author: PA =#
        function arrayBasictypeBaseclass(inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inType::DAE.Type) ::Option{DAE.Type}
              local outOptType::Option{DAE.Type}

              outOptType = begin
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                @match (inInstDims, inType) begin
                  ( nil(), _)  => begin
                    NONE()
                  end

                  _  => begin
                        dims = ListUtil.last(inInstDims)
                        ty = Expression.liftArrayLeftList(inType, dims)
                      SOME(ty)
                  end
                end
              end
          outOptType
        end

         #= This function is used when instantiating classes in lookup of other classes.
          The only work performed by this function is to instantiate local classes and
          inherited classes. =#
        function partialInstClassIn(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuterTypes.InstHierarchy, mod::DAE.Mod, prefix::Prefix.PrefixType, state::ClassInf.SMNode, cls::SCode.Element, visibility::SCode.Visibility, instDims::List{Any #= <:List{<:DAE.Dimension} =#}, numIter::ModelicaInteger) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, ClassInf.SMNode, List{DAE.Var}}
              local vars::List{DAE.Var}





              local cache_path::Absyn.Path
              local inputs::InstHashTable.CachedPartialInstItemInputs
              local outputs::InstHashTable.CachedPartialInstItemOutputs
              local bbx::Tuple{InstDims, DAE.Mod, ClassInf.SMNode, SCode.Element}
              local bby::Tuple{InstDims, DAE.Mod, ClassInf.SMNode, SCode.Element}
              local m::DAE.Mod
              local pre::Prefix.PrefixType
              local st::ClassInf.SMNode
              local e::SCode.Element
              local dims::InstDims
              local partial_inst::Bool

              cache_path = generateCachePath(env, cls, prefix, InstTypes.INNER_CALL())
               #=  See if we have it in the cache.
               =#
              if Flags.isSet(Flags.CACHE)
                try
                  @match _ <| SOME(InstHashTable.FUNC_partialInstClassIn(inputs, outputs)) <| nil = InstHashTable.get(cache_path)
                  @match (m, pre, st, e, dims) = inputs
                  @match SCode.CLASS() = e
                  InstUtil.prefixEqualUnlessBasicType(pre, prefix, cls)
                  if valueEq(dims, instDims) && valueEq(m, mod) && valueEq(st, state) && valueEq(e, cls)
                    (env, state, vars) = outputs
                    showCacheInfo("Partial Inst Hit: ", cache_path)
                    return (cache, env, ih, state, vars)
                  end
                catch ex
                  println("no inst partial cache: ")
                  showerror(stderr, ex, catch_backtrace())
                end
              end
               #=  Are the important inputs the same?
               =#
               #=  Not in cache, continue.
               =#
               #=  Check that we don't have an instantiation loop.
               =#
              if numIter >= Global.recursionDepthLimit
                Error.addSourceMessage(Error.RECURSION_DEPTH_REACHED, list(String(Global.recursionDepthLimit), FGraphUtil.printGraphPathStr(env)), SCodeUtil.elementInfo(cls))
                fail()
              end
               #=  Instantiate the class and add it to the cache.
               =#
              try
                partial_inst = System.getPartialInstantiation()
                System.setPartialInstantiation(true)
                inputs = (mod, prefix, state, cls, instDims)
                (cache, env, ih, state, vars) = partialInstClassIn_dispatch(cache, env, ih, mod, prefix, state, cls, visibility, instDims, partial_inst, numIter + 1)
                outputs = (env, state, vars)
                showCacheInfo("Partial Inst Add: ", cache_path)
                InstHashTable.addToInstCache(cache_path, NONE(), SOME(InstHashTable.FUNC_partialInstClassIn(inputs, outputs)))
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- Inst.partialInstClassIn failed on class: " + SCodeUtil.elementName(cls) + " in environment: " + FGraphUtil.printGraphPathStr(env))
                fail()
              end
          (cache, env, ih, state, vars)
        end

         #= This function is used when instantiating classes in lookup of other classes.
          The only work performed by this function is to instantiate local classes and
          inherited classes. =#
        function partialInstClassIn_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inClass::SCode.Element, inVisibility::SCode.Visibility, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, partialInst::Bool, numIter::ModelicaInteger) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, ClassInf.SMNode, List{DAE.Var}}
              local outVars::List{DAE.Var} = nil
              local outState::ClassInf.SMNode = inState
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local success::Bool

              success = begin
                @matchcontinue inClass begin
                  SCode.CLASS(name = "Real")  => begin
                    true
                  end

                  SCode.CLASS(name = "Integer")  => begin
                    true
                  end

                  SCode.CLASS(name = "String")  => begin
                    true
                  end

                  SCode.CLASS(name = "Boolean")  => begin
                    true
                  end

                  SCode.CLASS(name = "Clock") where (Flags.getConfigEnum(Flags.LANGUAGE_STANDARD) == 33)  => begin
                    true
                  end

                  SCode.CLASS(__)  => begin
                      (outCache, outEnv, outIH, outState, outVars) = partialInstClassdef(inCache, inEnv, inIH, inMod, inPrefix, inState, inClass, inClass.classDef, inVisibility, inInstDims, numIter)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  BTH
               =#
              System.setPartialInstantiation(partialInst)
              if ! success
                fail()
              end
          (outCache, outEnv, outIH, outState, outVars)
        end

         #=
          There are two kinds of class definitions, either explicit
          definitions SCode.PARTS() or
          derived definitions SCode.DERIVED() or
          extended derived definitions SCode.CLASS_EXTENDS().

          When instantiating an explicit definition, the elements are first
          instantiated, using instElementList, and then the equations
          and finally the algorithms are instantiated using instEquation
          and instAlgorithm, respectively. The resulting lists of equations
          are concatenated to produce the result.
          The last two arguments are the same as for instClassIn:
          implicit instantiation and implicit package/function instantiation. =#
        function instClassdef(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, store::UnitAbsyn.InstStore, inMod2::DAE.Mod, inPrefix3::Prefix.PrefixType, inState5::ClassInf.SMNode, className::String, inClassDef6::SCode.ClassDef, inRestriction7::SCode.Restriction, inVisibility::SCode.Visibility, inPartialPrefix::SCode.Partial, inEncapsulatedPrefix::SCode.Encapsulated, inInstDims9::List{Any #= <:List{<:DAE.Dimension} =#}, inBoolean10::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}, comment::SCode.Comment, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEqualityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local outTypesTypeOption::Option{DAE.Type}
              local outTypesVarLst::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph) = instClassdef2(inCache, inEnv, inIH, store, inMod2, inPrefix3, inState5, className, inClassDef6, inRestriction7, inVisibility, inPartialPrefix, inEncapsulatedPrefix, inInstDims9, inBoolean10, inCallingScope, inGraph, inSets, instSingleCref, comment, info, Mutable.create(false))
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph)
        end

         #=
        This function will try to instantiate the
        class definition as a it would extend a basic
        type =#
        function instClassdefBasicType(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod2::DAE.Mod, inPrefix3::Prefix.PrefixType, inState5::ClassInf.SMNode, className::String, inClassDef6::SCode.ClassDef, inRestriction7::SCode.Restriction, inVisibility::SCode.Visibility, inInstDims9::List{Any #= <:List{<:DAE.Dimension} =#}, inBoolean10::Bool, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}, info::SourceInfo, stopInst::MutableType #= {<:Bool} =# #= prevent instantiation of classes adding components to primary types =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEqualityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local outTypesTypeOption::Option{DAE.Type}
              local outTypesVarLst::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph) = begin
                  local cdefelts::List{SCode.Element}
                  local compelts::List{SCode.Element}
                  local extendselts::List{SCode.Element}
                  local els::List{SCode.Element}
                  local env1::FCore.Graph
                  local env2::FCore.Graph
                  local env3::FCore.Graph
                  local env::FCore.Graph
                  local cdefelts_1::List{Tuple{SCode.Element, DAE.Mod}}
                  local cdefelts_2::List{Tuple{SCode.Element, DAE.Mod}}
                  local csets::DAE.Sets
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local dae::DAE.DAElist
                  local ci_state1::ClassInf.SMNode
                  local ci_state::ClassInf.SMNode
                  local tys::List{DAE.Var}
                  local bc::Option{DAE.Type}
                  local mods::DAE.Mod
                  local pre::Prefix.PrefixType
                  local re::SCode.Restriction
                  local impl::Bool
                  local vis::SCode.Visibility
                  local inst_dims::InstDims
                  local cache::FCore.Cache
                  local eqConstraint::DAE.EqualityConstraint
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local store::UnitAbsyn.InstStore
                   #=  This rule describes how to instantiate a class definition
                   =#
                   #=  that extends a basic type. (No equations or algorithms allowed)
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inMod2, inPrefix3, inState5, className, inClassDef6, inRestriction7, inVisibility, inInstDims9, inBoolean10, inGraph, inSets, instSingleCref, info, stopInst) begin
                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.PARTS(elementLst = els, normalEquationLst =  nil(), initialEquationLst =  nil(), normalAlgorithmLst =  nil(), initialAlgorithmLst =  nil()), _, _, inst_dims, impl, graph, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("instClassdefBasicType1")
                      @match (cdefelts, nil, extendselts && _ <| _, compelts) = InstUtil.splitElts(els) #= components should be empty, checked in instBasictypeBaseclass type below =#
                      (cache, env1, ih) = InstUtil.addClassdefsToEnv(cache, env, ih, pre, cdefelts, impl, SOME(mods)) #= 1. CLASS & IMPORT nodes and COMPONENT nodes(add to env) =#
                      cdefelts_1 = InstUtil.addNomod(cdefelts) #= instantiate CDEFS so redeclares are carried out =#
                      env2 = env1
                      cdefelts_2 = cdefelts_1
                      (cache, env3, ih, store, dae1, csets, _, tys, graph, _) = instElementList(cache, env2, ih, store, mods, pre, ci_state, cdefelts_2, inst_dims, impl, InstTypes.INNER_CALL(), graph, inSets, true)
                      mods = Mod.removeFirstSubsRedecl(mods)
                      ErrorExt.rollBack("instClassdefBasicType1")
                      (cache, ih, store, dae2, bc, tys) = instBasictypeBaseclass(cache, env3, ih, store, extendselts, compelts, mods, inst_dims, className, info, stopInst)
                      eqConstraint = InstUtil.equalityConstraint(env3, els, info)
                      dae = DAEUtil.joinDaes(dae1, dae2)
                    (cache, env3, ih, store, dae, csets, ci_state, tys, bc, NONE(), eqConstraint, graph)
                  end

                  (_, _, _, _, _, _, _, _, SCode.PARTS(normalEquationLst =  nil(), initialEquationLst =  nil(), normalAlgorithmLst =  nil(), initialAlgorithmLst =  nil()), _, _, _, _, _, _, _, _, _)  => begin
                      @match true = ErrorExt.isTopCheckpoint("instClassdefBasicType1")
                      ErrorExt.rollBack("instClassdefBasicType1")
                    fail()
                  end
                end
              end
               #=  set this to get rid of the error messages that might happen and WE FAIL BEFORE we actually call instBasictypeBaseclass
               =#
               #=  we should have just ONE extends, but it might have more like one class containing just annotations
               =#
               #= /*{one}*/ =#
               #=  adrpo: TODO! DO SOME CHECKS HERE!
               =#
               #=  1. a type extending basic types cannot have components, and only a function definition (equalityConstraint!)
               =#
               #=  {} = compelts;  no components!
               =#
               #=  adrpo: VERY decisive check!
               =#
               #=         only CONNECTOR and TYPE can be extended by basic types!
               =#
               #=  true = listMember(re, {SCode.R_TYPE, SCode.R_CONNECTOR(false), SCode.R_CONNECTOR(true)});
               =#
               #=  InstUtil.checkExtendsForTypeRestiction(cache, env, ih, re, extendselts);
               =#
               #= (cache, cdefelts_2) = removeConditionalComponents(cache, env2, cdefelts_2, pre);
               =#
               #=  rollback before going into instBasictypeBaseclass
               =#
               #=  oh, the horror of backtracking! we need this to make sure that this case failed BEFORE or AFTER it went into instBasictypeBaseclass
               =#
               #=  Search for equalityConstraint
               =#
               #=  VERY COMPLICATED CHECKPOINT! TODO! try to simplify it, maybe by sending Prefix.TYPE and checking in instVar!
               =#
               #=  did the previous
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, outTypesTypeOption, optDerAttr, outEqualityConstraint, outGraph)
        end

         #=
          There are two kinds of class definitions, either explicit
          definitions SCode.PARTS() or
          derived definitions SCode.DERIVED() or
          extended derived definitions SCode.CLASS_EXTENDS().

          When instantiating an explicit definition, the elements are first
          instantiated, using instElementList, and then the equations
          and finally the algorithms are instantiated using instEquation
          and instAlgorithm, respectively. The resulting lists of equations
          are concatenated to produce the result.
          The last two arguments are the same as for instClassIn:
          implicit instantiation and implicit package/function instantiation. =#
        function instClassdef2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod2::DAE.Mod, inPrefix3::Prefix.PrefixType, inState5::ClassInf.SMNode, className::String, inClassDef6::SCode.ClassDef, inRestriction7::SCode.Restriction, inVisibility::SCode.Visibility, inPartialPrefix::SCode.Partial, inEncapsulatedPrefix::SCode.Encapsulated, inInstDims9::List{Any #= <:List{<:DAE.Dimension} =#}, inBoolean10::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, instSingleCref::Option{<:DAE.ComponentRef}, comment::SCode.Comment, info::SourceInfo, stopInst::MutableType #= {<:Bool} =# #= prevent instantiation of classes adding components to primary types =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, Option{DAE.Type}, Option{SCode.Attributes}, DAE.EqualityConstraint, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEqualityConstraint::DAE.EqualityConstraint
              local optDerAttr::Option{SCode.Attributes}
              local oty::Option{DAE.Type}
              local outTypesVarLst::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, oty, optDerAttr, outEqualityConstraint, outGraph) = begin
                  local cdefelts::List{SCode.Element}
                  local compelts::List{SCode.Element}
                  local extendselts::List{SCode.Element}
                  local els::List{SCode.Element}
                  local extendsclasselts::List{SCode.Element}
                  local compelts_2_elem::List{SCode.Element}
                  local env1::FCore.Graph
                  local env2::FCore.Graph
                  local env3::FCore.Graph
                  local env::FCore.Graph
                  local env5::FCore.Graph
                  local cenv::FCore.Graph
                  local cenv_2::FCore.Graph
                  local env_2::FCore.Graph
                  local parentEnv::FCore.Graph
                  local parentClassEnv::FCore.Graph
                  local cdefelts_1::List{Tuple{SCode.Element, DAE.Mod}}
                  local extcomps::List{Tuple{SCode.Element, DAE.Mod}}
                  local compelts_1::List{Tuple{SCode.Element, DAE.Mod}}
                  local compelts_2::List{Tuple{SCode.Element, DAE.Mod}}
                  local comp_cond::List{Tuple{SCode.Element, DAE.Mod}}
                  local derivedClassesWithConstantMods::List{Tuple{SCode.Element, DAE.Mod}}
                  local csets::DAE.Sets
                  local csets1::DAE.Sets
                  local csets2::DAE.Sets
                  local csets3::DAE.Sets
                  local csets4::DAE.Sets
                  local csets5::DAE.Sets
                  local csets_1::DAE.Sets
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local dae3::DAE.DAElist
                  local dae4::DAE.DAElist
                  local dae5::DAE.DAElist
                  local dae6::DAE.DAElist
                  local dae7::DAE.DAElist
                  local dae8::DAE.DAElist
                  local dae::DAE.DAElist
                  local ci_state1::ClassInf.SMNode
                  local ci_state::ClassInf.SMNode
                  local ci_state2::ClassInf.SMNode
                  local ci_state3::ClassInf.SMNode
                  local ci_state4::ClassInf.SMNode
                  local ci_state5::ClassInf.SMNode
                  local ci_state6::ClassInf.SMNode
                  local ci_state7::ClassInf.SMNode
                  local new_ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local vars::List{DAE.Var}
                  local bc::Option{DAE.Type}
                  local mods::DAE.Mod
                  local emods::DAE.Mod
                  local mod_1::DAE.Mod
                  local mods_1::DAE.Mod
                  local checkMods::DAE.Mod
                  local pre::Prefix.PrefixType
                  local eqs::List{SCode.Equation}
                  local initeqs::List{SCode.Equation}
                  local eqs2::List{SCode.Equation}
                  local initeqs2::List{SCode.Equation}
                  local eqs_1::List{SCode.Equation}
                  local initeqs_1::List{SCode.Equation}
                  local alg::List{SCode.AlgorithmSection}
                  local initalg::List{SCode.AlgorithmSection}
                  local alg2::List{SCode.AlgorithmSection}
                  local initalg2::List{SCode.AlgorithmSection}
                  local alg_1::List{SCode.AlgorithmSection}
                  local initalg_1::List{SCode.AlgorithmSection}
                  local constrs::List{SCode.ConstraintSection}
                  local clsattrs::List{Absyn.NamedArg}
                  local re::SCode.Restriction
                  local r::SCode.Restriction
                  local impl::Bool
                  local valid_connector::Bool
                  local vis::SCode.Visibility
                  local enc2::SCode.Encapsulated
                  local partialPrefix::SCode.Partial
                  local encapsulatedPrefix::SCode.Encapsulated
                  local inst_dims::InstDims
                  local inst_dims_1::InstDims
                  local inst_dims2::List{DAE.Subscript}
                  local cn2::String
                  local cns::String
                  local scope_str::String
                  local s::String
                  local str::String
                  local c::SCode.Element
                  local classDef::SCode.ClassDef
                  local classDefParent::SCode.ClassDef
                  local eq::Option{DAE.EqMod}
                  local dims::DAE.Dimensions
                  local cn::Absyn.Path
                  local fq_class::Absyn.Path
                  local ad::Option{List{Absyn.Subscript}}
                  local mod::SCode.Mod
                  local cache::FCore.Cache
                  local oDA::Option{SCode.Attributes}
                  local comments::List{SCode.Comment}
                  local eqConstraint::DAE.EqualityConstraint
                  local callscope::InstTypes.CallingScope
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local fdae::DAE.DAElist
                  local unrollForLoops::Bool
                  local zero_dims::Bool
                  local info2::SourceInfo
                  local tSpecs::List{Absyn.TypeSpec}
                  local tys::List{DAE.Type}
                  local DA::SCode.Attributes
                  local ty::DAE.Type
                  local tSpec::Absyn.TypeSpec
                  local cmt::Option{SCode.Comment}
                  local store::UnitAbsyn.InstStore
                  local ed::Option{SCode.ExternalDecl}
                  local elementSource::DAE.ElementSource
                  local adno::List{Absyn.Subscript}
                  local smCompCrefs::List{DAE.ComponentRef} #= state machine components crefs =#
                  local smInitialCrefs::List{DAE.ComponentRef} #= state machine crefs of initial states =#
                  local lastRef::FCore.MMRef
                  local smCompToFlatSM::InstStateMachineUtil.SMNodeToFlatSMGroupTable
                   #= List<tuple<Absyn.ComponentRef,DAE.ComponentRef>> fieldDomLst;
                   =#
                  local domainFieldsLst::InstUtil.DomainFieldsLst
                  local typeVars::List{String}
                   #=       list<tuple<String,Integer>> domainNLst;
                   =#
                   #= /* uncomment for debugging
                      case (cache,env,ih,store,mods,pre,csets,ci_state,className,inClassDef6,
                            re,vis,_,_,inst_dims,impl,_,graph,instSingleCref,info,stopInst)
                        equation
                           fprintln(Flags.INST_TRACE, \"ICD BEGIN: \" + FGraphUtil.printGraphPathStr(env) + \" cn:\" + className + \" mods: \" + Mod.printModStr(mods));
                        then
                          fail();*/ =#
                   #=  This rule describes how to instantiate a class definition
                   =#
                   #=  that extends a basic type. (No equations or algorithms allowed)
                   =#
                @matchcontinue (inCache, inEnv, inIH, inStore, inMod2, inPrefix3, inState5, className, inClassDef6, inRestriction7, inVisibility, inPartialPrefix, inEncapsulatedPrefix, inInstDims9, inBoolean10, inCallingScope, inGraph, inSets, instSingleCref, comment, info, stopInst) begin
                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.PARTS(elementLst = els, normalEquationLst =  nil(), initialEquationLst =  nil(), normalAlgorithmLst =  nil(), initialAlgorithmLst =  nil()), re, vis, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match false = valueEq(SCode.R_MODEL(), re)
                      @match false = valueEq(SCode.R_PACKAGE(), re)
                      @match false = SCodeUtil.isFunctionRestriction(re)
                      @match false = valueEq(SCode.R_RECORD(true), re)
                      @match false = valueEq(SCode.R_RECORD(false), re)
                      @match (cdefelts, extendsclasselts, extendselts && _ <| _, nil) = InstUtil.splitElts(els)
                      extendselts = SCodeInstUtil.addRedeclareAsElementsToExtends(extendselts, ListUtil.select(els, SCodeUtil.isRedeclareElement))
                      (cache, env1, ih) = InstUtil.addClassdefsToEnv(cache, env, ih, pre, cdefelts, impl, SOME(mods))
                      @match (cache, _, _, _, extcomps, nil, nil, nil, nil, _) = InstExtends.instExtendsAndClassExtendsList(cache, env1, ih, mods, pre, extendselts, extendsclasselts, els, ci_state, className, impl, false)
                      compelts_2_elem = ListUtil.map(extcomps, Util.tuple21)
                      @match (_, _, _, nil) = InstUtil.splitElts(compelts_2_elem)
                      (cache, env, ih, store, fdae, csets, ci_state, vars, bc, oDA, eqConstraint, graph) = instClassdefBasicType(cache, env, ih, store, mods, pre, ci_state, className, inClassDef6, re, vis, inst_dims, impl, graph, inSets, instSingleCref, info, stopInst)
                    (cache, env, ih, store, fdae, csets, ci_state, vars, bc, oDA, eqConstraint, graph)
                  end

                  (cache, env, ih, store, mods, _, ci_state, _, SCode.PARTS(elementLst = els), _, _, _, _, _, impl, _, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match true = SCodeUtil.isExternalObject(els)
                      (cache, env, ih, dae, ci_state) = InstFunction.instantiateExternalObject(cache, env, ih, els, mods, impl, comment, info)
                    (cache, env, ih, store, dae, inSets, ci_state, nil, NONE(), NONE(), NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.PARTS(elementLst = els, normalEquationLst = eqs, initialEquationLst = initeqs, normalAlgorithmLst = alg, initialAlgorithmLst = initalg, constraintLst = constrs, clsattrs = clsattrs, externalDecl = ed), re, _, _, _, inst_dims, impl, callscope, graph, csets, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match false = SCodeUtil.isExternalObject(els)
                      if Flags.getConfigBool(Flags.UNIT_CHECKING)
                        UnitParserExt.checkpoint()
                      end
                      ci_state1 = ClassInf.trans(ci_state, ClassInf.NEWDEF())
                      els = InstUtil.extractConstantPlusDeps(els, instSingleCref, nil, className)
                      (cdefelts, extendsclasselts, extendselts, compelts) = InstUtil.splitElts(els)
                      extendselts = SCodeInstUtil.addRedeclareAsElementsToExtends(extendselts, ListUtil.select(els, SCodeUtil.isRedeclareElement))
                      (cache, env1, ih) = InstUtil.addClassdefsToEnv(cache, env, ih, pre, cdefelts, impl, SOME(mods), FGraphUtil.isEmptyScope(env))
                      (cache, env2, ih, emods, extcomps, eqs2, initeqs2, alg2, initalg2, comments) = InstExtends.instExtendsAndClassExtendsList(cache, env1, ih, mods, pre, extendselts, extendsclasselts, els, ci_state, className, impl, false) #= 2. EXTENDS Nodes inst_extends_list only flatten inhteritance structure. It does not perform component instantiations. =#
                      compelts_1 = InstUtil.addNomod(compelts) #= Problem. Modifiers on inherited components are unelabed, loosing their
                                        type information. This will not work, since the modifier type
                                        can not always be found.
                               For instance.
                                model B extends B2; end B; model B2 Integer ni=1; end B2;
                                model test
                                  Integer n=2;
                                  B b(ni=n);
                                end test;

                               The modifier (n=n) will be untypes when B is instantiated
                               and the variable n can not be found, since the component b
                               is instantiated in env of B.

                               Solution:
                                Redesign instExtendsList to return (SCode.Element, Mod) list and
                                convert other component elements to the same format, such that
                                instElement can handle the new format uniformely. =#
                      cdefelts_1 = InstUtil.addNomod(cdefelts)
                      compelts_1 = listAppend(listAppend(extcomps, compelts_1), cdefelts_1)
                      eqs_1 = joinExtEquations(eqs, eqs2, callscope)
                      initeqs_1 = joinExtEquations(initeqs, initeqs2, callscope)
                      alg_1 = joinExtAlgorithms(alg, alg2, callscope)
                      initalg_1 = joinExtAlgorithms(initalg, initalg2, callscope)
                      (compelts_1, eqs_1, initeqs_1, alg_1, initalg_1) = InstUtil.extractConstantPlusDepsTpl(compelts_1, instSingleCref, nil, className, eqs_1, initeqs_1, alg_1, initalg_1)
                      if intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
                        compelts_1 = InstUtil.addGhostCells(compelts_1, eqs_1)
                      end
                      checkMods = Mod.myMerge(mods, emods, className)
                      mods = checkMods
                      (cache, env3, ih) = InstUtil.addComponentsToEnv(cache, env2, ih, mods, pre, ci_state, compelts_1, impl)
                      compelts_2_elem = ListUtil.map(compelts_1, Util.tuple21)
                      InstUtil.matchModificationToComponents(compelts_2_elem, checkMods, FGraphUtil.printGraphPathStr(env3))
                      (comp_cond, compelts_1) = ListUtil.splitOnTrue(compelts_1, InstUtil.componentHasCondition)
                      compelts_2 = listAppend(compelts_1, comp_cond)
                      (smCompCrefs, smInitialCrefs) = InstStateMachineUtil.getSMStatesInContext(eqs_1, pre)
                      ih = ListUtil.fold(smCompCrefs, InnerOuter.updateSMHierarchy, ih)
                      (cache, env5, ih, store, dae1, csets, ci_state2, vars, graph, domainFieldsLst) = instElementList(cache, env3, ih, store, mods, pre, ci_state1, compelts_2, inst_dims, impl, callscope, graph, csets, true)
                      zero_dims = InstUtil.instDimsHasZeroDims(inst_dims)
                      elementSource = ElementSource.createElementSource(info, FGraphUtil.getScopePath(env3), pre)
                      csets1 = ConnectUtil.addConnectorVariablesFromDAE(zero_dims, ci_state1, pre, vars, info, elementSource, csets)
                      (cache, eqs_1) = InstUtil.reorderConnectEquationsExpandable(cache, env5, eqs_1)
                      if intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
                        eqs_1 = ListUtil.fold1(eqs_1, InstUtil.discretizePDE, domainFieldsLst, nil)
                      end
                      (cache, env5, ih, dae2, csets2, ci_state3, graph) = instList(cache, env5, ih, pre, csets1, ci_state2, InstSection.instEquation, eqs_1, impl, InstTypes.alwaysUnroll, graph)
                      DAEUtil.verifyEquationsDAE(dae2)
                      if intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
                        initeqs_1 = ListUtil.fold1(initeqs_1, InstUtil.discretizePDE, domainFieldsLst, nil)
                      end
                      (cache, env5, ih, dae3, csets3, ci_state4, graph) = instList(cache, env5, ih, pre, csets2, ci_state3, InstSection.instInitialEquation, initeqs_1, impl, InstTypes.alwaysUnroll, graph)
                      unrollForLoops = if SCodeUtil.isFunctionRestriction(re)
                            InstTypes.neverUnroll
                          else
                            InstTypes.alwaysUnroll
                          end
                      (cache, env5, ih, dae4, csets4, ci_state5, graph) = instList(cache, env5, ih, pre, csets3, ci_state4, InstSection.instAlgorithm, alg_1, impl, unrollForLoops, graph)
                      (cache, env5, ih, dae5, csets5, ci_state6, graph) = instList(cache, env5, ih, pre, csets4, ci_state5, InstSection.instInitialAlgorithm, initalg_1, impl, unrollForLoops, graph)
                      (cache, env5, dae6) = instClassAttributes(cache, env5, pre, clsattrs, impl, info)
                      (cache, env5, dae7, _) = instConstraints(cache, env5, pre, ci_state6, constrs, impl)
                      dae8 = instFunctionAnnotations(_cons(comment, comments), ci_state6)
                      smCompToFlatSM = InstStateMachineUtil.createSMNodeToFlatSMGroupTable(dae2)
                      (dae1, dae2) = InstStateMachineUtil.wrapSMCompsInFlatSMs(ih, dae1, dae2, smCompToFlatSM, smInitialCrefs)
                      dae = DAEUtil.joinDaeLst(list(dae1, dae2, dae3, dae4, dae5, dae6, dae7, dae8))
                      csets5 = InnerOuter.changeInnerOuterInOuterConnect(csets5)
                      (cache, env5, store) = InstUtil.handleUnitChecking(cache, env5, store, pre, dae1, list(dae2, dae3, dae4, dae5), className)
                      if Flags.getConfigBool(Flags.UNIT_CHECKING)
                        UnitParserExt.rollback()
                      end
                      eqConstraint = InstUtil.equalityConstraint(env5, els, info)
                      ci_state6 = if isSome(ed)
                            ClassInf.assertTrans(ci_state6, ClassInf.FOUND_EXT_DECL(), info)
                          else
                            ci_state6
                          end
                      (cache, oty) = InstMeta.fixUniontype(cache, env5, ci_state6, inClassDef6)
                      _ = begin
                        @match oty begin
                          SOME(ty && DAE.T_METAUNIONTYPE(typeVars = _ <| _))  => begin
                               #=  Search for equalityConstraint
                               =#
                              Error.addSourceMessage(Error.UNIONTYPE_MISSING_TYPEVARS, list(Types.unparseType(ty)), info)
                            fail()
                          end

                          _  => begin
                              ()
                          end
                        end
                      end
                    (cache, env5, ih, store, dae, csets5, ci_state6, vars, oty, NONE(), eqConstraint, graph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn, arrayDim = ad), modifications = mod, attributes = DA), re, vis, _, _, inst_dims, impl, callscope, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match (cache, c, cenv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      @match SCode.CLASS(name = cn2, encapsulatedPrefix = enc2, restriction = r) = c
                      @match SCode.R_ENUMERATION() = r
                      env3 = FGraphUtil.openScope(cenv, enc2, cn2, SOME(FCore.CLASS_SCOPE()))
                      ci_state2 = ClassInf.start(r, FGraphUtil.getGraphName(env3))
                      new_ci_state = ClassInf.start(r, FGraphUtil.getGraphName(env3))
                      (cache, cenv_2, _, _, _, _, _, _, _, _, _, _) = instClassIn(cache, env3, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), ci_state2, c, SCode.PUBLIC(), nil, false, callscope, ConnectionGraph.EMPTY, DAE.emptySet, NONE())
                      (cache, mod_1) = Mod.elabMod(cache, cenv_2, ih, pre, mod, impl, Mod.DERIVED(cn), info)
                      mods_1 = Mod.myMerge(mods, mod_1, className)
                      eq = Mod.modEquation(mods_1) #= instantiate array dimensions =#
                      (cache, dims) = InstUtil.elabArraydimOpt(cache, cenv_2, Absyn.CREF_IDENT("", nil), cn, ad, eq, impl, true, pre, info, inst_dims) #= owncref not valid here =#
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, dims)
                      (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph) = instClassIn(cache, cenv_2, ih, store, mods_1, pre, new_ci_state, c, vis, inst_dims_1, impl, callscope, graph, inSets, instSingleCref) #= instantiate class in opened scope. =#
                      ClassInf.assertValid(ci_state_1, re, info) #= Check for restriction violations =#
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn, arrayDim = ad), modifications = mod, attributes = DA), re, vis, _, _, inst_dims, impl, callscope, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match (cache, c, cenv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      @match SCode.CLASS(name = cn2, encapsulatedPrefix = enc2, restriction = r) = c
                      @match true = InstUtil.checkDerivedRestriction(re, r, cn2)
                      valid_connector = ConnectUtil.checkShortConnectorDef(ci_state, DA, info)
                      Mutable.update(stopInst, ! valid_connector)
                      @match true = valid_connector
                      cenv_2 = FGraphUtil.openScope(cenv, enc2, cn2, FGraphUtil.classInfToScopeType(ci_state))
                      new_ci_state = ClassInf.start(r, FGraphUtil.getGraphName(cenv_2))
                      mod = InstUtil.chainRedeclares(mods, mod)
                      (parentEnv, _) = FGraphUtil.stripLastScopeRef(env)
                      (cache, mod_1) = Mod.elabMod(cache, parentEnv, ih, pre, mod, impl, Mod.DERIVED(cn), info)
                      mods_1 = Mod.myMerge(mods, mod_1, className)
                      eq = Mod.modEquation(mods_1) #= instantiate array dimensions =#
                      (cache, dims) = InstUtil.elabArraydimOpt(cache, parentEnv, Absyn.CREF_IDENT("", nil), cn, ad, eq, impl, true, pre, info, inst_dims) #= owncref not valid here =#
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, dims)
                      _ = AbsynUtil.getArrayDimOptAsList(ad)
                      (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph) = instClassIn(cache, cenv_2, ih, store, mods_1, pre, new_ci_state, c, vis, inst_dims_1, impl, callscope, graph, inSets, instSingleCref) #= instantiate class in opened scope.  =#
                      ClassInf.assertValid(ci_state_1, re, info) #= Check for restriction violations =#
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn, arrayDim = ad), modifications = mod, attributes = DA), re, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, callscope, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match false = valueEq(re, SCode.R_TYPE())
                      @match false = valueEq(re, SCode.R_ENUMERATION())
                      @match false = valueEq(re, SCode.R_PREDEFINED_ENUMERATION())
                      @match false = SCodeUtil.isConnector(re)
                      @match true = boolOr(valueEq(ad, NONE()), valueEq(ad, SOME(nil)))
                      @match (cache, SCode.CLASS(name = cn2, restriction = r, classDef = classDefParent), parentClassEnv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      @match false = InstUtil.checkDerivedRestriction(re, r, cn2)
                      if begin
                        @match r begin
                          SCode.Restriction.R_PACKAGE(__)  => begin
                            false
                          end

                          _  => begin
                              if SCodeUtil.restrictionEqual(r, re)
                                    Mod.isInvariantMod(mod) && Mod.isInvariantDAEMod(mods)
                                  else
                                    false
                                  end
                          end
                        end
                      end
                        mod = InstUtil.chainRedeclares(mods, mod)
                        (parentEnv, _) = FGraphUtil.stripLastScopeRef(env)
                        (cache, mod_1) = Mod.elabMod(cache, parentEnv, ih, pre, mod, false, Mod.DERIVED(cn), info)
                        mods_1 = Mod.myMerge(mods, mod_1, className)
                        (cache, env, ih, store, dae, csets, ci_state, vars, bc, oDA, eqConstraint, graph) = instClassdef2(cache, parentClassEnv, ih, store, mods_1, pre, ci_state, className, classDefParent, re, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, callscope, graph, inSets, instSingleCref, comment, info, stopInst)
                        oDA = SCodeUtil.mergeAttributes(DA, oDA)
                      else
                        mod = InstUtil.chainRedeclares(mods, mod)
                        (parentEnv, _) = FGraphUtil.stripLastScopeRef(env)
                        (cache, mod_1) = Mod.elabMod(cache, parentEnv, ih, pre, mod, false, Mod.DERIVED(cn), info)
                        mods_1 = Mod.myMerge(mods, mod_1, className)
                        (cache, env, ih, store, dae, csets, ci_state, vars, bc, oDA, eqConstraint, graph) = instClassdef2(cache, env, ih, store, mods_1, pre, ci_state, className, SCode.PARTS(list(SCode.EXTENDS(cn, vis, SCode.NOMOD(), NONE(), info)), nil, nil, nil, nil, nil, nil, NONE()), re, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, callscope, graph, inSets, instSingleCref, comment, info, stopInst)
                        oDA = SCodeUtil.mergeAttributes(DA, oDA)
                      end
                    (cache, env, ih, store, dae, csets, ci_state, vars, bc, oDA, eqConstraint, graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.DERIVED(typeSpec = Absyn.TPATH(path = cn, arrayDim = ad), modifications = mod, attributes = DA), re, vis, _, _, inst_dims, impl, callscope, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match (cache, c, cenv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      @match SCode.CLASS(name = cn2, encapsulatedPrefix = enc2, restriction = r) = c
                      @match false = InstUtil.checkDerivedRestriction(re, r, cn2)
                      cenv_2 = FGraphUtil.openScope(cenv, enc2, className, FGraphUtil.classInfToScopeType(ci_state))
                      new_ci_state = ClassInf.start(r, FGraphUtil.getGraphName(cenv_2))
                      c = SCodeUtil.setClassName(className, c)
                      mod = InstUtil.chainRedeclares(mods, mod)
                      (parentEnv, _) = FGraphUtil.stripLastScopeRef(env)
                      (cache, mod_1) = Mod.elabMod(cache, parentEnv, ih, pre, mod, impl, Mod.DERIVED(cn), info)
                      mods_1 = Mod.myMerge(mods, mod_1, className)
                      eq = Mod.modEquation(mods_1) #= instantiate array dimensions =#
                      (cache, dims) = InstUtil.elabArraydimOpt(cache, parentEnv, Absyn.CREF_IDENT("", nil), cn, ad, eq, impl, true, pre, info, inst_dims) #= owncref not valid here =#
                      inst_dims_1 = ListUtil.appendLastList(inst_dims, dims)
                      (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph) = instClassIn(cache, cenv_2, ih, store, mods_1, pre, new_ci_state, c, vis, inst_dims_1, impl, callscope, graph, inSets, instSingleCref) #= instantiate class in opened scope.  =#
                      ClassInf.assertValid(ci_state_1, re, info) #= Check for restriction violations =#
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env_2, ih, store, dae, csets_1, ci_state_1, vars, bc, oDA, eqConstraint, graph)
                  end

                  (_, _, _, _, mods, _, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(__), modifications = mod), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      Error.addSourceMessage(Error.META_COMPLEX_TYPE_MOD, nil, info)
                    fail()
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT("list"), tSpec <|  nil(), NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      (cache, _, ih, tys, csets, oDA) = instClassDefHelper(cache, env, ih, list(tSpec), pre, inst_dims, impl, nil, inSets, info)
                      ty = listHead(tys)
                      ty = Types.boxIfUnboxedType(ty)
                      bc = SOME(DAE.T_METALIST(ty))
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env, ih, store, DAE.emptyDae, csets, ClassInf.META_LIST(Absyn.IDENT("")), nil, bc, oDA, NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT("Option"), tSpec <|  nil(), NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      @match (cache, _, ih, list(ty), csets, oDA) = instClassDefHelper(cache, env, ih, list(tSpec), pre, inst_dims, impl, nil, inSets, info)
                      ty = Types.boxIfUnboxedType(ty)
                      bc = SOME(DAE.T_METAOPTION(ty))
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env, ih, store, DAE.emptyDae, csets, ClassInf.META_OPTION(Absyn.IDENT("")), nil, bc, oDA, NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT("tuple"), tSpecs, NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      (cache, _, ih, tys, csets, oDA) = instClassDefHelper(cache, env, ih, tSpecs, pre, inst_dims, impl, nil, inSets, info)
                      tys = ListUtil.map(tys, Types.boxIfUnboxedType)
                      bc = SOME(DAE.T_METATUPLE(tys))
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env, ih, store, DAE.emptyDae, csets, ClassInf.META_TUPLE(Absyn.IDENT("")), nil, bc, oDA, NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT("array"), tSpec <|  nil(), NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      @match (cache, _, ih, list(ty), csets, oDA) = instClassDefHelper(cache, env, ih, list(tSpec), pre, inst_dims, impl, nil, inSets, info)
                      ty = Types.boxIfUnboxedType(ty)
                      bc = SOME(DAE.T_METAARRAY(ty))
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env, ih, store, DAE.emptyDae, csets, ClassInf.META_ARRAY(Absyn.IDENT(className)), nil, bc, oDA, NONE(), graph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT("polymorphic"), Absyn.TPATH(Absyn.IDENT("Any"), NONE()) <|  nil(), NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      (cache, _, ih, _, csets, oDA) = instClassDefHelper(cache, env, ih, nil, pre, inst_dims, impl, nil, inSets, info)
                      bc = SOME(DAE.T_METAPOLYMORPHIC(className))
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                    (cache, env, ih, store, DAE.emptyDae, csets, ClassInf.META_POLYMORPHIC(Absyn.IDENT(className)), nil, bc, oDA, NONE(), graph)
                  end

                  (_, _, _, _, mods, _, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(path = Absyn.IDENT("polymorphic")), modifications = mod), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      Error.addSourceMessage(Error.META_POLYMORPHIC, list(className), info)
                    fail()
                  end

                  (cache, env, ih, store, mods, pre, ci_state, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(Absyn.IDENT(str), tSpecs, NONE()), modifications = mod, attributes = DA), re, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      str = Util.assoc(str, list(("List", "list"), ("Tuple", "tuple"), ("Array", "array")))
                      (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, oty, optDerAttr, outEqualityConstraint, outGraph) = instClassdef2(cache, env, ih, store, mods, pre, ci_state, className, SCode.DERIVED(Absyn.TCOMPLEX(Absyn.IDENT(str), tSpecs, NONE()), mod, DA), re, vis, partialPrefix, encapsulatedPrefix, inst_dims, impl, inCallingScope, graph, inSets, instSingleCref, comment, info, stopInst)
                    (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, oty, optDerAttr, outEqualityConstraint, outGraph)
                  end

                  (cache, env, ih, store, mods, pre, _, _, SCode.DERIVED(typeSpec = Absyn.TCOMPLEX(cn, tSpecs, NONE()), modifications = mod, attributes = DA), _, _, _, _, inst_dims, impl, _, graph, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = Mutable.access(stopInst)
                      @match true = Mod.emptyModOrEquality(mods) && SCodeUtil.emptyModOrEquality(mod)
                      @match false = listMember(AbsynUtil.pathString(cn), list("tuple", "Tuple", "array", "Array", "Option", "list", "List"))
                      @match (cache, SCode.CLASS(name = cn2, restriction = SCode.R_UNIONTYPE(typeVars = typeVars), classDef = classDef), cenv) = Lookup.lookupClass(cache, env, cn, SOME(info))
                      (cache, fq_class) = makeFullyQualifiedIdent(cache, cenv, cn2)
                      new_ci_state = ClassInf.META_UNIONTYPE(fq_class, typeVars)
                      @match (cache, SOME(ty)) = InstMeta.fixUniontype(cache, env, new_ci_state, classDef)
                      @match DAE.T_METAUNIONTYPE() = ty
                      (cache, _, ih, tys, csets, oDA) = instClassDefHelper(cache, env, ih, tSpecs, pre, inst_dims, impl, nil, inSets, info)
                      tys = list(Types.boxIfUnboxedType(t) for t in tys)
                      if ! listLength(tys) == listLength(typeVars)
                        Error.addSourceMessage(Error.UNIONTYPE_WRONG_NUM_TYPEVARS, list(AbsynUtil.pathString(fq_class), String(listLength(typeVars)), String(listLength(tys))), info)
                        fail()
                      end
                      ty = Types.setTypeVariables(ty, tys)
                      oDA = SCodeUtil.mergeAttributes(DA, oDA)
                      bc = SOME(ty)
                    (cache, env, ih, store, DAE.emptyDae, csets, new_ci_state, nil, bc, oDA, NONE(), graph)
                  end

                  (_, _, _, _, _, _, _, _, SCode.DERIVED(typeSpec = tSpec && Absyn.TCOMPLEX(arrayDim = SOME(_))), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      cns = Dump.unparseTypeSpec(tSpec)
                      Error.addSourceMessage(Error.META_INVALID_COMPLEX_TYPE, list(cns), info)
                    fail()
                  end

                  (_, _, _, _, _, _, _, _, SCode.DERIVED(typeSpec = tSpec && Absyn.TCOMPLEX(path = cn, typeSpecs = tSpecs)), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match false = listMember((AbsynUtil.pathString(cn), listLength(tSpecs) == 1), list(("tuple", false), ("array", true), ("Option", true), ("list", true)))
                      cns = Dump.unparseTypeSpec(tSpec)
                      Error.addSourceMessage(Error.META_INVALID_COMPLEX_TYPE, list(cns), info)
                    fail()
                  end

                  (cache, env, _, _, _, _, _, _, SCode.DERIVED(Absyn.TPATH(path = cn)), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match false = Mutable.access(stopInst)
                      @shouldFail (_, _, _) = Lookup.lookupClass(cache, env, cn)
                      cns = AbsynUtil.pathString(cn)
                      scope_str = FGraphUtil.printGraphPathStr(env)
                      Error.addSourceMessage(Error.LOOKUP_ERROR, list(cns, scope_str), info)
                    fail()
                  end

                  (cache, env, _, _, _, _, _, _, SCode.DERIVED(Absyn.TPATH(path = cn)), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      @shouldFail (_, _, _) = Lookup.lookupClass(cache, env, cn)
                      Debug.trace("- Inst.instClassdef DERIVED( ")
                      Debug.trace(AbsynUtil.pathString(cn))
                      Debug.trace(") lookup failed\\n ENV:")
                      Debug.trace(FGraphUtil.printGraphStr(env))
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Inst.instClassdef failed")
                        s = FGraphUtil.printGraphPathStr(inEnv)
                        Debug.traceln("  class :" + s)
                      fail()
                  end
                end
              end
               #= /* ----------------------- */ =#
               #= /* If the class is derived from a class that can not be found in the environment, this rule prints an error message. */ =#
               #=  Debug.traceln(\"  Env :\" + FGraphUtil.printGraphStr(env));
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outTypesVarLst, oty, optDerAttr, outEqualityConstraint, outGraph)
        end

        function joinExtEquations(inEq::List{<:SCode.Equation}, inExtEq::List{<:SCode.Equation}, inCallingScope::InstTypes.CallingScope) ::List{SCode.Equation}
              local outEq::List{SCode.Equation}

              outEq = begin
                @match (inEq, inExtEq, inCallingScope) begin
                  (_, _, InstTypes.TYPE_CALL(__))  => begin
                    nil
                  end

                  _  => begin
                      listAppend(inEq, inExtEq)
                  end
                end
              end
          outEq
        end

        function joinExtAlgorithms(inAlg::List{<:SCode.AlgorithmSection}, inExtAlg::List{<:SCode.AlgorithmSection}, inCallingScope::InstTypes.CallingScope) ::List{SCode.AlgorithmSection}
              local outAlg::List{SCode.AlgorithmSection}

              outAlg = begin
                @match inCallingScope begin
                  InstTypes.TYPE_CALL(__)  => begin
                    nil
                  end

                  _  => begin
                      listAppend(inAlg, inExtAlg)
                  end
                end
              end
          outAlg
        end

         #= Function: instClassDefHelper
         MetaModelica extension. KS TODO: Document this function!!!! =#
        function instClassDefHelper(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inSpecs::List{<:Absyn.TypeSpec}, inPre::Prefix.PrefixType, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImpl::Bool, accTypes::List{<:DAE.Type}, inSets::DAE.Sets, inInfo::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, List{DAE.Type}, DAE.Sets, Option{SCode.Attributes}}
              local outAttr::Option{SCode.Attributes}
              local outSets::DAE.Sets
              local outType::List{DAE.Type}
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outType, outSets, outAttr) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local cenv::FCore.Graph
                  local pre::Prefix.PrefixType
                  local dims::InstDims
                  local impl::Bool
                  local localAccTypes::List{DAE.Type}
                  local restTypeSpecs::List{Absyn.TypeSpec}
                  local csets::DAE.Sets
                  local cn::Absyn.Path
                  local ty::DAE.Type
                  local p::Absyn.Path
                  local c::SCode.Element
                  local id::Absyn.Ident
                  local tSpec::Absyn.TypeSpec
                  local oDA::Option{SCode.Attributes}
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, inEnv, inIH, inSpecs, inPre, inInstDims, inImpl, accTypes, inSets) begin
                  (cache, env, ih,  nil(), _, _, _, localAccTypes, _)  => begin
                    (cache, env, ih, listReverse(localAccTypes), inSets, NONE())
                  end

                  (cache, env, ih, Absyn.TPATH(cn, _) <| restTypeSpecs, pre, dims, impl, localAccTypes, _)  => begin
                      @match (cache, c && SCode.CLASS(), cenv) = Lookup.lookupClass(cache, env, cn, SOME(inInfo))
                      @match false = SCodeUtil.isFunction(c)
                      (cache, cenv, ih, _, _, csets, ty, _, oDA, _) = instClass(cache, cenv, ih, UnitAbsyn.noStore, DAE.NOMOD(), pre, c, dims, impl, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, inSets)
                      localAccTypes = _cons(ty, localAccTypes)
                      (cache, env, ih, localAccTypes, csets, _) = instClassDefHelper(cache, env, ih, restTypeSpecs, pre, dims, impl, localAccTypes, csets, inInfo)
                    (cache, env, ih, localAccTypes, csets, oDA)
                  end

                  (cache, env, ih, Absyn.TPATH(cn, _) <| restTypeSpecs, pre, dims, impl, localAccTypes, _)  => begin
                      (cache, ty, _) = Lookup.lookupType(cache, env, cn, NONE()) #= For functions, etc =#
                      localAccTypes = _cons(ty, localAccTypes)
                      (cache, env, ih, localAccTypes, csets, _) = instClassDefHelper(cache, env, ih, restTypeSpecs, pre, dims, impl, localAccTypes, inSets, inInfo)
                    (cache, env, ih, localAccTypes, csets, NONE())
                  end

                  (cache, env, ih, tSpec && Absyn.TCOMPLEX(p, _, _) <| restTypeSpecs, pre, dims, impl, localAccTypes, _)  => begin
                      id = AbsynUtil.pathString(p)
                      c = SCode.CLASS(id, SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.DERIVED(tSpec, SCode.NOMOD(), SCode.ATTR(nil, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD())), SCode.noComment, AbsynUtil.dummyInfo)
                      (cache, _, ih, _, _, csets, ty, _, oDA, _) = instClass(cache, env, ih, UnitAbsyn.noStore, DAE.NOMOD(), pre, c, dims, impl, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, inSets)
                      localAccTypes = _cons(ty, localAccTypes)
                      (cache, env, ih, localAccTypes, csets, _) = instClassDefHelper(cache, env, ih, restTypeSpecs, pre, dims, impl, localAccTypes, csets, inInfo)
                    (cache, env, ih, localAccTypes, csets, oDA)
                  end
                end
              end
          (outCache, outEnv, outIH, outType, outSets, outAttr)
        end

         #= This function finds the type of classes that extends a basic type.
          For instance,
          connector RealSignal
            extends SignalType;
            replaceable type SignalType = Real;
          end RealSignal;
          Such classes can not have any other components,
          and can only inherit one basic type. =#
        function instBasictypeBaseclass(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inSCodeElementLst2::List{<:SCode.Element}, inSCodeElementLst3::List{<:SCode.Element}, inMod4::DAE.Mod, inInstDims5::List{Any #= <:List{<:DAE.Dimension} =#}, className::String, info::SourceInfo, stopInst::MutableType #= {<:Bool} =# #= prevent instantiation of classes adding components to primary types =#) ::Tuple{FCore.Cache, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, Option{DAE.Type}, List{DAE.Var}}
              local outTypeVars::List{DAE.Var}
              local outTypesTypeOption::Option{DAE.Type}
              local outDae::DAE.DAElist #= contain functions =#
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outCache::FCore.Cache

              (outCache, outIH, outStore, outDae, outTypesTypeOption, outTypeVars) = begin
                  local m_1::DAE.Mod
                  local m_2::DAE.Mod
                  local mods::DAE.Mod
                  local cdef::SCode.Element
                  local cenv::FCore.Graph
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local dae::DAE.DAElist
                  local ty::DAE.Type
                  local tys::List{DAE.Var}
                  local st::ClassInf.SMNode
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local path::Absyn.Path
                  local mod::SCode.Mod
                  local inst_dims::InstDims
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local store::UnitAbsyn.InstStore
                @matchcontinue (inCache, inEnv, inIH, inStore, inSCodeElementLst2, inSCodeElementLst3, inMod4, inInstDims5, className, info, stopInst) begin
                  (cache, env, ih, store, SCode.EXTENDS(baseClassPath = path, modifications = mod) <|  nil(),  nil(), mods, inst_dims, _, _, _)  => begin
                      ErrorExt.setCheckpoint("instBasictypeBaseclass")
                      (cache, m_1) = Mod.elabModForBasicType(cache, env, ih, Prefix.NOPRE(), mod, true, Mod.DERIVED(path), info)
                      m_2 = Mod.myMerge(mods, m_1, className)
                      (cache, cdef, cenv) = Lookup.lookupClass(cache, env, path, SOME(info))
                      (cache, _, ih, store, dae, _, ty, tys, _) = instClassBasictype(cache, cenv, ih, store, m_2, Prefix.NOPRE(), cdef, inst_dims, false, InstTypes.INNER_CALL(), DAE.emptySet)
                      b1 = Types.basicType(ty)
                      b2 = Types.arrayType(ty)
                      b3 = Types.extendsBasicType(ty)
                      @match true = boolOr(b1, boolOr(b2, b3))
                      ErrorExt.rollBack("instBasictypeBaseclass")
                    (cache, ih, store, dae, SOME(ty), tys)
                  end

                  (_, _, _, _, SCode.EXTENDS(baseClassPath = path) <|  nil(),  nil(), _, _, _, _, _)  => begin
                      rollbackCheck(path) #= only rollback errors affecting basic types =#
                    fail()
                  end

                  (cache, env, ih, store, SCode.EXTENDS(__) <|  nil(), _, mods, inst_dims, _, _, _)  => begin
                      @match false = listEmpty(inSCodeElementLst3)
                      ErrorExt.setCheckpoint("instBasictypeBaseclass2") #= rolled back or deleted inside call below =#
                      instBasictypeBaseclass2(cache, env, ih, store, inSCodeElementLst2, inSCodeElementLst3, mods, inst_dims, className, info, stopInst)
                    fail()
                  end
                end
              end
               #= Debug.traceln(\"Try instbasic 1 \" + AbsynUtil.pathString(path));
               =#
               #= Debug.traceln(\"Try instbasic 2 \" + AbsynUtil.pathString(path) + \" \" + Mod.printModStr(m_2));
               =#
               #= Debug.traceln(\"Try instbasic 3 \" + AbsynUtil.pathString(path) + \" \" + Mod.printModStr(m_2));
               =#
               #= /* Inherits baseclass -and- has components */ =#
          (outCache, outIH, outStore, outDae #= contain functions =#, outTypesTypeOption, outTypeVars)
        end

         #=
        Author BZ 2009-08
        Rollsback errors on builtin classes and deletes checkpoint for other classes. =#
        function rollbackCheck(p::Absyn.Path)
              _ = begin
                  local n::String
                @matchcontinue p begin
                  _  => begin
                      n = AbsynUtil.pathString(p)
                      @match true = InstUtil.isBuiltInClass(n)
                      ErrorExt.rollBack("instBasictypeBaseclass")
                    ()
                  end

                  _  => begin
                      ErrorExt.rollBack("instBasictypeBaseclass")
                    ()
                  end
                end
              end
               #=  ErrorExt.delCheckpoint(\"instBasictypeBaseclass\");
               =#
        end

         #=
        Author: BZ, 2009-02
        Helper function for instBasictypeBaseClass
        Handles the fail case rollbacks/deleteCheckpoint of errors. =#
        function instBasictypeBaseclass2(inCache::FCore.Cache, inEnv1::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, store::UnitAbsyn.InstStore, inSCodeElementLst2::List{<:SCode.Element}, inSCodeElementLst3::List{<:SCode.Element}, inMod4::DAE.Mod, inInstDims5::List{Any #= <:List{<:DAE.Dimension} =#}, className::String, inInfo::SourceInfo, stopInst::MutableType #= {<:Bool} =# #= prevent instantiation of classes adding components to primary types =#)
              _ = begin
                  local m_1::DAE.Mod
                  local mods::DAE.Mod
                  local cdef::SCode.Element
                  local cdef_1::SCode.Element
                  local cenv::FCore.Graph
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local dae::DAE.DAElist
                  local ty::DAE.Type
                  local st::ClassInf.SMNode
                  local b1::Bool
                  local b2::Bool
                  local path::Absyn.Path
                  local mod::SCode.Mod
                  local inst_dims::InstDims
                  local classname::String
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv1, inIH, store, inSCodeElementLst2, inSCodeElementLst3, inMod4, inInstDims5, className, stopInst) begin
                  (cache, env, ih, _, SCode.EXTENDS(baseClassPath = path, modifications = mod, info = info) <|  nil(), _ <| _, _, inst_dims, _, _)  => begin
                      (cache, m_1) = Mod.elabModForBasicType(cache, env, ih, Prefix.NOPRE(), mod, true, Mod.DERIVED(path), inInfo)
                      (cache, cdef, cenv) = Lookup.lookupClass(cache, env, path, SOME(info))
                      cdef_1 = SCodeUtil.classSetPartial(cdef, SCode.NOT_PARTIAL())
                      (cache, _, ih, _, _, _, ty, _, _, _) = instClass(cache, cenv, ih, store, m_1, Prefix.NOPRE(), cdef_1, inst_dims, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet) #= impl =#
                      b1 = Types.basicType(ty)
                      b2 = Types.arrayType(ty)
                      @match true = boolOr(b1, b2)
                      classname = FGraphUtil.printGraphPathStr(env)
                      ErrorExt.rollBack("instBasictypeBaseclass2")
                      Error.addSourceMessage(Error.INHERIT_BASIC_WITH_COMPS, list(classname), inInfo)
                      Mutable.update(stopInst, true)
                    ()
                  end

                  _  => begin
                        ErrorExt.rollBack("instBasictypeBaseclass2")
                      ()
                  end
                end
              end
               #= /* Inherits baseclass -and- has components */ =#
               #=  if not error above, then do not report error at all, try another case in instClassdef.
               =#
        end

         #= This function is used by partialInstClassIn for instantiating local class
           definitions and inherited class definitions only. =#
        function partialInstClassdef(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inClass::SCode.Element #= The class this definition comes from. =#, inClassDef::SCode.ClassDef, inVisibility::SCode.Visibility, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, numIter::ModelicaInteger) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, ClassInf.SMNode, List{DAE.Var}}
              local outVars::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outState, outVars) = begin
                  local partial_prefix::SCode.Partial
                  local class_name::String
                  local scope_str::String
                  local cdef_els::List{SCode.Element}
                  local class_ext_els::List{SCode.Element}
                  local extends_els::List{SCode.Element}
                  local emods::DAE.Mod
                  local mod::DAE.Mod
                  local class_mod::SCode.Mod
                  local smod::SCode.Mod
                  local ext_comps::List{Tuple{SCode.Element, DAE.Mod}}
                  local const_els::List{Tuple{SCode.Element, DAE.Mod}}
                  local class_path::Absyn.Path
                  local class_dims::Option{List{Absyn.Subscript}}
                  local cls::SCode.Element
                  local cdef::SCode.ClassDef
                  local cenv::FCore.Graph
                  local parent_env::FCore.Graph
                  local der_re::SCode.Restriction
                  local parent_re::SCode.Restriction
                  local enc::SCode.Encapsulated
                  local info::SourceInfo
                  local eq::Option{DAE.EqMod}
                  local dims::List{DAE.Dimension} = nil
                  local has_dims::Bool
                  local is_basic_type::Bool
                  local inst_dims::InstDims
                  local scope_ty::Option{FCore.ScopeType}
                @match inClassDef begin
                  SCode.PARTS(__)  => begin
                      partial_prefix = SCodeUtil.getClassPartialPrefix(inClass)
                      partial_prefix = InstUtil.isPartial(partial_prefix, inMod)
                      class_name = SCodeUtil.elementName(inClass)
                      outState = ClassInf.trans(inState, ClassInf.NEWDEF())
                      (cdef_els, class_ext_els, extends_els) = InstUtil.splitElts(inClassDef.elementLst)
                      extends_els = SCodeInstUtil.addRedeclareAsElementsToExtends(extends_els, ListUtil.select(inClassDef.elementLst, SCodeUtil.isRedeclareElement))
                       #=  Classes and imports are added to env.
                       =#
                      (outCache, outEnv, outIH) = InstUtil.addClassdefsToEnv(inCache, inEnv, inIH, inPrefix, cdef_els, true, SOME(inMod), FGraphUtil.isEmptyScope(inEnv))
                       #=  Inherited elements are added to env.
                       =#
                      (outCache, outEnv, outIH, emods, ext_comps) = InstExtends.instExtendsAndClassExtendsList(outCache, outEnv, outIH, inMod, inPrefix, extends_els, class_ext_els, inClassDef.elementLst, inState, class_name, true, true)
                       #=  If we partially instantiate a partial package, we filter out
                       =#
                       #=  constants (maybe we should also filter out functions) /sjoelund
                       =#
                      const_els = listAppend(ext_comps, InstUtil.addNomod(InstUtil.constantEls(inClassDef.elementLst)))
                       #=  Since partial instantiation is done in lookup, we need to add
                       =#
                       #=  inherited classes here.  Otherwise when looking up e.g. A.B where A
                       =#
                       #=  inherits the definition of B, and without having a base class context
                       =#
                       #=  (since we do not have any element to find it in), the class must be
                       =#
                       #=  added to the environment here.
                       =#
                      mod = Mod.myMerge(inMod, emods, class_name)
                      (cdef_els, ext_comps) = InstUtil.classdefElts2(ext_comps, partial_prefix)
                      (outCache, outEnv, outIH) = InstUtil.addClassdefsToEnv(outCache, outEnv, outIH, inPrefix, cdef_els, true, SOME(mod))
                       #=  Add inherited classes to env.
                       =#
                      (outCache, outEnv, outIH) = InstUtil.addComponentsToEnv(outCache, outEnv, outIH, mod, inPrefix, inState, const_els, false)
                       #=  Instantiate constants.
                       =#
                      (outCache, outEnv, outIH, _, _, _, outState, outVars, _, _) = instElementList(outCache, outEnv, outIH, UnitAbsyn.noStore, mod, inPrefix, outState, const_els, inInstDims, true, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet, false)
                    (outCache, outEnv, outIH, outState, outVars)
                  end

                  SCode.DERIVED(typeSpec = Absyn.TPATH(path = class_path, arrayDim = class_dims), modifications = class_mod)  => begin
                      info = SCodeUtil.elementInfo(inClass)
                      has_dims = ! (isNone(class_dims) || valueEq(class_dims, SOME(nil)))
                      try
                        @match (outCache, cls && SCode.CLASS(), cenv) = Lookup.lookupClass(inCache, inEnv, class_path, SOME(info))
                      catch
                        class_name = AbsynUtil.pathString(class_path)
                        scope_str = FGraphUtil.printGraphPathStr(inEnv)
                        Error.addSourceMessageAndFail(Error.LOOKUP_ERROR, list(class_name, scope_str), info)
                      end
                      @match SCode.CLASS(name = class_name, encapsulatedPrefix = enc, restriction = der_re) = cls
                      parent_re = SCodeUtil.getClassRestriction(inClass)
                      is_basic_type = InstUtil.checkDerivedRestriction(parent_re, der_re, class_name)
                      smod = InstUtil.chainRedeclares(inMod, class_mod)
                       #=  The mod is elaborated in the parent of this class.
                       =#
                      parent_env = FGraphUtil.stripLastScopeRef(inEnv)
                      (outCache, mod) = Mod.elabMod(outCache, parent_env, inIH, inPrefix, smod, false, Mod.DERIVED(class_path), info)
                      mod = Mod.myMerge(inMod, mod, class_name)
                      if has_dims && ! is_basic_type
                        cls = SCodeUtil.setClassName(class_name, cls)
                        eq = Mod.modEquation(mod)
                        (outCache, dims) = InstUtil.elabArraydimOpt(outCache, parent_env, Absyn.CREF_IDENT("", nil), class_path, class_dims, eq, false, true, inPrefix, info, inInstDims)
                        inst_dims = ListUtil.appendLastList(inInstDims, dims)
                      else
                        inst_dims = inInstDims
                      end
                      if is_basic_type || has_dims
                        scope_ty = if is_basic_type
                              FGraphUtil.restrictionToScopeType(der_re)
                            else
                              FGraphUtil.classInfToScopeType(inState)
                            end
                        cenv = FGraphUtil.openScope(cenv, enc, class_name, scope_ty)
                        outState = ClassInf.start(der_re, FGraphUtil.getGraphName(cenv))
                        (outCache, outEnv, outIH, outState, outVars) = partialInstClassIn(outCache, cenv, inIH, mod, inPrefix, outState, cls, inVisibility, inst_dims, numIter)
                      else
                        cdef = SCode.PARTS(list(SCode.EXTENDS(class_path, inVisibility, SCode.NOMOD(), NONE(), info)), nil, nil, nil, nil, nil, nil, NONE())
                        (outCache, outEnv, outIH, outState, outVars) = partialInstClassdef(outCache, inEnv, inIH, mod, inPrefix, inState, inClass, cdef, inVisibility, inInstDims, numIter)
                      end
                      if SCodeUtil.isPartial(cls)
                        outEnv = FGraphUtil.makeScopePartial(inEnv)
                      end
                    (outCache, outEnv, outIH, outState, outVars)
                  end
                end
              end
          (outCache, outEnv, outIH, outState, outVars)
        end

         #= Instantiates a list of elements. =#
        function instElementList(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImplInst::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, inStopOnError::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, ConnectionGraph.ConnectionGraphType, InstUtil.DomainFieldsLst}
              local domainFieldsListOut::InstUtil.DomainFieldsLst = nil
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outVars::List{DAE.Var}
              local outState::ClassInf.SMNode = inState
              local outSets::DAE.Sets = inSets
              local outDae::DAE.DAElist
              local outStore::UnitAbsyn.InstStore = inStore
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local el::List{Tuple{SCode.Element, DAE.Mod}}
              local cache::FCore.Cache
              local vars::List{DAE.Var}
              local dae::List{DAE.Element}
              local varsl::List{List{DAE.Var}} = nil
              local dael::List{List{DAE.Element}} = nil
              local fieldDomOpt::InstUtil.DomainFieldOpt
              local element_order::List{ModelicaInteger}
              local el_arr::Array{Tuple{SCode.Element, DAE.Mod}}
              local var_arr::Array{List{DAE.Var}}
              local dae_arr::Array{List{DAE.Element}}
              local length::ModelicaInteger

              cache = InstUtil.pushStructuralParameters(inCache)
               #=  Sort elements based on their dependencies.
               =#
              el = inElements # InstUtil.sortElementList(inElements, inEnv, FGraphUtil.inFunctionScope(inEnv))
               #=  adrpo: MAKE SURE inner objects ARE FIRST in the list for instantiation!
               =#
              el = InstUtil.sortInnerFirstTplLstElementMod(el)
               #=  For non-functions, don't reorder the elements.
               =#
              if ! ClassInf.isFunction(inState)
                element_order = getSortedElementOrdering(inElements, el)
                el_arr = listArray(inElements)
                length = listLength(el)
                var_arr = arrayCreate(length, nil)
                dae_arr = arrayCreate(length, nil)
                for idx in element_order
                  (cache, outEnv, outIH, outStore, dae, outSets, outState, vars, outGraph, fieldDomOpt) = instElement2(cache, outEnv, outIH, outStore, inMod, inPrefix, outState, el_arr[idx], inInstDims, inImplInst, inCallingScope, outGraph, outSets, inStopOnError)
                  arrayUpdate(var_arr, length - idx + 1, vars)
                  arrayUpdate(dae_arr, length - idx + 1, dae)
                  if intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
                    domainFieldsListOut = InstUtil.optAppendField(domainFieldsListOut, fieldDomOpt)
                  end
                end
                outVars = nil
                for lst in var_arr
                  outVars = listAppend(lst, outVars)
                end
                aaa = nil
                for lst in dae_arr
                  aaa = listAppend(lst, aaa)
                end
                outDae = DAE.DAE_LIST(aaa)
                GC.free(var_arr)
                GC.free(dae_arr)
              else
                for e in el
                  (cache, outEnv, outIH, outStore, dae, outSets, outState, vars, outGraph, fieldDomOpt) = instElement2(cache, outEnv, outIH, outStore, inMod, inPrefix, outState, e, inInstDims, inImplInst, inCallingScope, outGraph, outSets, inStopOnError)
                  varsl = _cons(vars, varsl)
                  dael = _cons(dae, dael)
                end
                outVars = ListUtil.flattenReverse(varsl)
                outDae = DAE.DAE_LIST(ListUtil.flattenReverse(dael))
              end
               #=  Figure out the ordering of the sorted elements, see getSortedElementOrdering.
               =#
               #=  Create arrays so that we can instantiate the elements in the sorted order,
               =#
               #=  while keeping the result in the same order as the elements are declared in.
               =#
               #=  Instantiate the elements.
               =#
               #=  Store the elements in reverse order to make the list flattening simpler
               =#
               #=  For functions, use the sorted elements instead, otherwise things break.
               =#
              outCache = InstUtil.popStructuralParameters(cache, inPrefix)
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outGraph, domainFieldsListOut)
        end

         #= Takes a list of unsorted elements and a list of sorted elements, and returns
           a list of the sorted elements indices in the unsorted list. E.g.:
            getSortedElementOrdering({a, b, c}, {b, c, a}) => {2, 3, 1} =#
        function getSortedElementOrdering(inElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inSortedElements::List{<:Tuple{<:SCode.Element, DAE.Mod}}) ::List{ModelicaInteger}
              local outIndices::List{ModelicaInteger} = nil

              local index_map::List{Tuple{SCode.Element, ModelicaInteger}} = nil
              local sorted_el::List{SCode.Element}
              local i::ModelicaInteger = 1

               #=  Pair each unsorted element with its index in the list.
               =#
              for e in inElements
                index_map = _cons((Util.tuple21(e), i), index_map)
                i = i + 1
              end
              index_map = listReverse(index_map)
               #=  Loop through the sorted elements.
               =#
              sorted_el = list(Util.tuple21(e) for e in inSortedElements)
              for e in sorted_el
                @match (index_map, SOME((_, i))) = ListUtil.deleteMemberOnTrue(e, index_map, getSortedElementOrdering_comp)
                outIndices = _cons(i, outIndices)
              end
               #=  Remove the element from the index map, and add its index to the list of
               =#
               #=  indices. Elements are usually not reordered much, so most of the time the
               =#
               #=  sought after element should be first in the list.
               =#
              outIndices = listReverse(outIndices)
          outIndices
        end

        function getSortedElementOrdering_comp(inElement1::SCode.Element, inElement2::Tuple{<:SCode.Element, ModelicaInteger}) ::Bool
              local outEqual::Bool = SCodeUtil.elementNameEqual(inElement1, Util.tuple21(inElement2))
          outEqual
        end

        function instElement2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inElement::Tuple{<:SCode.Element, DAE.Mod}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImplicit::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets, inStopOnError::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, List{DAE.Element}, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, ConnectionGraph.ConnectionGraphType, InstUtil.DomainFieldOpt}
              local outFieldDomOpt::InstUtil.DomainFieldOpt = NONE()
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outVars::List{DAE.Var} = nil
              local outState::ClassInf.SMNode = inState
              local outSets::DAE.Sets = inSets
              local outDae::List{DAE.Element} = nil
              local outStore::UnitAbsyn.InstStore = inStore
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local elt::Tuple{SCode.Element, DAE.Mod}
              local elts::List{Tuple{SCode.Element, DAE.Mod}}
              local is_deleted::Bool
              local zzz::DAE.DAElist

               #=  Check if the component has a conditional expression that evaluates to false.
               =#
              (is_deleted, outEnv, outCache) = isDeletedComponent(inElement, inPrefix, inStopOnError, inEnv, inCache)
               #=  Skip the component if it was deleted by a conditional expression.
               =#
              if is_deleted
                return (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outGraph, outFieldDomOpt)
              end
              try
                ErrorExt.setCheckpoint("instElement2")
                @match (outCache, outEnv, outIH, elts) = updateCompeltsMods(inCache, outEnv, outIH, inPrefix, list(inElement), outState, inImplicit)
                elt = listHead(elts)
                @match (outCache, outEnv, outIH, outStore, zzz, outSets, outState, outVars, outGraph, outFieldDomOpt) = instElement(outCache, outEnv, outIH, outStore, inMod, inPrefix, outState, elt, inInstDims, inImplicit, inCallingScope, outGraph, inSets)
                @match DAE.DAE_LIST(outDae) = zzz
                Error.clearCurrentComponent()
                ErrorExt.delCheckpoint("instElement2")
              catch
                if inStopOnError
                  ErrorExt.delCheckpoint("instElement2")
                  fail()
                else
                  ErrorExt.rollBack("instElement2")
                  outCache = inCache
                  outEnv = inEnv
                  outIH = inIH
                  return (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outGraph, outFieldDomOpt)
                end
              end
               #=  Try to instantiate the element.
               =#
               #=  Instantiation failed, fail or skip the element depending on inStopOnError.
               =#
          (outCache, outEnv, outIH, outStore, outDae, outSets, outState, outVars, outGraph, outFieldDomOpt)
        end

         #= Checks if an element has a conditional expression that evaluates to false,
           and adds it to the set of deleted components if it does. Otherwise the
           function does nothing. =#
        function isDeletedComponent(element::Tuple{<:SCode.Element, DAE.Mod}, prefix::Prefix.PrefixType, stopOnError::Bool, env::FCore.Graph, cache::FCore.Cache) ::Tuple{Bool, FCore.Graph, FCore.Cache}


              local isDeleted::Bool

              local el::SCode.Element
              local el_name::String
              local info::SourceInfo
              local cond_val_opt::Option{Bool}
              local cond_val::Bool
              local var::DAE.Var

               #=  If the element has a conditional expression, try to evaluate it.
               =#
              if InstUtil.componentHasCondition(element)
                (el, _) = element
                (el_name, info) = InstUtil.extractCurrentName(el)
                if SCodeUtil.isElementRedeclare(el)
                  Error.addSourceMessage(Error.REDECLARE_CONDITION, list(el_name), info)
                  fail()
                end
                (cond_val_opt, cache) = InstUtil.instElementCondExp(cache, env, el, prefix, info)
                if isNone(cond_val_opt)
                  if stopOnError
                    fail()
                  else
                    isDeleted = false
                    return (isDeleted, env, cache)
                  end
                end
                @match SOME(cond_val) = cond_val_opt
                isDeleted = ! cond_val
                if isDeleted == true
                  var = DAE.TYPES_VAR(el_name, DAE.dummyAttrVar, DAE.T_UNKNOWN_DEFAULT, DAE.UNBOUND(), NONE())
                  env = FGraphUtil.updateComp(env, var, FCore.VAR_DELETED(), FGraphUtil.emptyGraph)
                end
              else
                isDeleted = false
              end
               #=  An element redeclare may not have a condition.
               =#
               #=  If a conditional expression was present but couldn't be instantiatied, stop.
               =#
               #=  We should stop instantiation completely, fail.
               =#
               #=  We should continue instantiation, pretend that it was deleted.
               =#
               #=  If we succeeded, check if the condition is true or false.
               =#
               #=  The component was deleted, update its status in the environment so we can
               =#
               #=  look it up when instantiating connections.
               =#
          (isDeleted, env, cache)
        end

         #=
          This monster function instantiates an element of a class definition.  An
          element is either a class definition, a variable, or an import clause. =#
        function instElement(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inUnitStore::UnitAbsyn.InstStore, inMod::DAE.Mod, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inElement::Tuple{<:SCode.Element, DAE.Mod}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inImplicit::Bool, inCallingScope::InstTypes.CallingScope, inGraph::ConnectionGraph.ConnectionGraphType, inSets::DAE.Sets) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, DAE.DAElist, DAE.Sets, ClassInf.SMNode, List{DAE.Var}, ConnectionGraph.ConnectionGraphType, InstUtil.DomainFieldOpt}
              local outFieldDomOpt::InstUtil.DomainFieldOpt = NONE()
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outVars::List{DAE.Var}
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outUnitStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outUnitStore, outDae, outSets, outState, outVars, outGraph) = begin
                  local own_cref::Absyn.ComponentRef
                  local dir::Absyn.Direction
                  local info::SourceInfo
                  local io::Absyn.InnerOuter
                  local t::Absyn.Path
                  local type_name::Absyn.Path
                  local ts::Absyn.TypeSpec
                  local already_declared::Bool
                  local impl::Bool
                  local is_function_input::Bool
                  local callscope::InstTypes.CallingScope
                  local ci_state::ClassInf.SMNode
                  local graph::ConnectionGraph.ConnectionGraphType
                  local graph_new::ConnectionGraph.ConnectionGraphType
                  local csets::DAE.Sets
                  local dae_attr::DAE.Attributes
                  local binding::DAE.Binding
                  local cref::DAE.ComponentRef
                  local vn::DAE.ComponentRef
                  local cref2::DAE.ComponentRef
                  local dae::DAE.DAElist
                  local mod::DAE.Mod
                  local mods::DAE.Mod
                  local class_mod::DAE.Mod
                  local mm::DAE.Mod
                  local cmod::DAE.Mod
                  local mod_1::DAE.Mod
                  local var_class_mod::DAE.Mod
                  local m_1::DAE.Mod
                  local cls_mod::DAE.Mod
                  local ty::DAE.Type
                  local new_var::DAE.Var
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local env2::FCore.Graph
                  local cenv::FCore.Graph
                  local comp_env::FCore.Graph
                  local ih::InstanceHierarchy
                  local inst_dims::InstDims
                  local crefs::List{Absyn.ComponentRef}
                  local crefs1::List{Absyn.ComponentRef}
                  local crefs2::List{Absyn.ComponentRef}
                  local crefs3::List{Absyn.ComponentRef}
                  local ad::List{Absyn.Subscript}
                  local dims::DAE.Dimensions
                  local vars::List{DAE.Var}
                  local cond::Option{Absyn.Exp}
                  local eq::Option{DAE.EqMod}
                  local comment::SCode.Comment
                  local pre::Prefix.PrefixType
                  local attr::SCode.Attributes
                  local cls::SCode.Element
                  local comp::SCode.Element
                  local comp2::SCode.Element
                  local el::SCode.Element
                  local final_prefix::SCode.Final
                  local ct::SCode.ConnectorType
                  local m::SCode.Mod
                  local oldmod::SCode.Mod
                  local prefixes::SCode.Prefixes
                  local vt::SCode.Variability
                  local vis::SCode.Visibility
                  local name::String
                  local id::String
                  local ns::String
                  local s::String
                  local scope_str::String
                  local store::UnitAbsyn.InstStore
                  local node::FCore.Node
                  local topInstance::InnerOuter.TopInstance
                   #=  BTH
                   =#
                  local sm::HashSet.HashSetType
                   #=  BTH
                   =#
                  local isInSM::Bool
                   #=  BTH
                   =#
                  local elems::List{DAE.Element}
                   #=  BTH
                   =#
                  local domainCROpt::Option{DAE.ComponentRef}
                   #=  Imports are simply added to the current frame, so that the lookup rule can find them.
                   =#
                   #=  Import have already been added to the environment so there is nothing more to do here.
                   =#
                @matchcontinue (inCache, inEnv, inIH, inUnitStore, inMod, inPrefix, inState, inElement, inInstDims, inImplicit, inCallingScope, inGraph, inSets) begin
                  (_, _, _, _, _, _, _, (SCode.IMPORT(__), _), _, _, _, _, _)  => begin
                    (inCache, inEnv, inIH, inUnitStore, DAE.emptyDae, inSets, inState, nil, inGraph)
                  end

                  (_, _, _, _, _, _, _, (cls && SCode.CLASS(__), cmod), _, _, _, _, _)  => begin
                      if ! Mod.isEmptyMod(cmod)
                        env = FGraphUtil.updateClass(inEnv, cls, inPrefix, cmod, FCore.CLS_UNTYPED(), inEnv)
                      else
                        env = inEnv
                      end
                    (inCache, env, inIH, inUnitStore, DAE.emptyDae, inSets, inState, nil, inGraph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, (el && SCode.COMPONENT(name = name, typeSpec = Absyn.TPATH(__)), cmod), inst_dims, impl, _, graph, csets)  => begin
                      @match SCode.COMPONENT(
                               name = name, prefixes = prefixes, attributes = attr, typeSpec = ts,
                               modifications = m, comment = comment, condition = cond, info = info) = el
                      @match Absyn.TPATH(path = t) = ts
                      @match SCode.ATTR(arrayDims = ad) = attr
                      @match SCode.PREFIXES(finalPrefix = final_prefix, innerOuter = io) = prefixes
                      @match true = if Config.acceptParModelicaGrammar()
                            InstUtil.checkParallelismWRTEnv(env, name, attr, info)
                          else
                            true
                          end
                      m = SCodeUtil.mergeModifiers(m, SCodeUtil.getConstrainedByModifiers(prefixes))
                      if SCodeUtil.finalBool(final_prefix)
                        m = InstUtil.traverseModAddFinal(m)
                      end
                      comp = if referenceEq(el.modifications, m)
                            el
                          else
                            SCode.COMPONENT(name, prefixes, attr, ts, m, comment, cond, info)
                          end
                      oldmod = m
                      already_declared = InstUtil.checkMultiplyDeclared(cache, env, mods, pre, ci_state, (comp, cmod), inst_dims, impl)
                      m = InstUtil.chainRedeclares(mods, m)
                      m = SCodeInstUtil.expandEnumerationMod(m)
                      m = InstUtil.traverseModAddDims(cache, env, pre, m, inst_dims)
                      comp = if referenceEq(oldmod, m)
                            comp
                          else
                            SCode.COMPONENT(name, prefixes, attr, ts, m, comment, cond, info)
                          end
                      ci_state = ClassInf.trans(ci_state, ClassInf.FOUND_COMPONENT(name))
                      cref = ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil)
                      (cache, _) = PrefixUtil.prefixCref(cache, env, ih, pre, cref)
                      class_mod = Mod.lookupModificationP(mods, t)
                      mm = Mod.lookupCompModification(mods, name)
                      own_cref = Absyn.CREF_IDENT(name, nil)
                      crefs1 = InstUtil.getCrefFromMod(m)
                      crefs2 = InstUtil.getCrefFromDim(ad)
                      crefs3 = InstUtil.getCrefFromCond(cond)
                      crefs = ListUtil.unionList(listAppend(listAppend(crefs1, crefs2), crefs3))
                      (cache, env, ih, store, crefs) = removeSelfReferenceAndUpdate(cache, env, ih, store, crefs, own_cref, t, ci_state, attr, prefixes, impl, inst_dims, pre, mods, m, info)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env, ih, pre, mods, crefs, ci_state, impl)
                      (cache, class_mod) = Mod.updateMod(cache, env2, ih, pre, class_mod, impl, info)
                      (cache, mm) = Mod.updateMod(cache, env2, ih, pre, mm, impl, info)
                      (var_class_mod, class_mod) = modifyInstantiateClass(class_mod, t)
                      (cache, m_1) = Mod.elabMod(cache, env2, ih, pre, m, impl, Mod.COMPONENT(name), info)
                      mod = Mod.myMerge(mm, class_mod, name)
                      mod = Mod.myMerge(mod, m_1, name, ! ClassInf.isRecord(ci_state))
                      mod = Mod.myMerge(cmod, mod, name)
                      mod = Mod.myMerge(mod, var_class_mod, name)
                      @match (cache, env2, ih, SCode.COMPONENT(name, prefixes, attr, Absyn.TPATH(t, _), _, comment, _, _), mod_1) = redeclareType(cache, env2, ih, mod, comp, pre, ci_state, impl, DAE.NOMOD())
                      @match SCode.PREFIXES(innerOuter = io) = prefixes
                      @match SCode.ATTR(arrayDims = ad, direction = dir) = attr
                      (cache, cls, cenv) = Lookup.lookupClass(cache, env2, t, SOME(info))
                      cls_mod = Mod.getClassModifier(cenv, SCodeUtil.className(cls))
                      if ! Mod.isEmptyMod(cls_mod)
                        if ! listEmpty(ad)
                          cls_mod = Mod.addEachIfNeeded(cls_mod, list(DAE.DIM_INTEGER(1)))
                        end
                        mod_1 = Mod.myMerge(mod_1, cls_mod, name)
                      end
                      attr = SCodeUtil.mergeAttributesFromClass(attr, cls)
                      inst_dims = ListUtil.appendElt(nil, inst_dims)
                      (cache, mod) = Mod.updateMod(cache, env2, ih, pre, mod, impl, info)
                      (cache, mod_1) = Mod.updateMod(cache, env2, ih, pre, mod_1, impl, info)
                      (mod, mod_1) = InstUtil.selectModifiers(mod, mod_1, t)
                      eq = Mod.modEquation(mod)
                      is_function_input = InstUtil.isFunctionInput(ci_state, dir)
                      (cache, dims) = InstUtil.elabArraydim(cache, env2, own_cref, t, ad, eq, impl, true, is_function_input, pre, info, inst_dims)
                      if intEq(Flags.getConfigEnum(Flags.GRAMMAR), Flags.PDEMODELICA)
                        (dims, mod_1, outFieldDomOpt) = InstUtil.elabField(inCache, inEnv, name, attr, dims, mod_1, info)
                      end
                      (cenv, cls, ih) = FGraph.createVersionScope(env2, name, pre, mod_1, cenv, cls, ih)
                      (cache, cref2) = PrefixUtil.prefixCref(cache, cenv, ih, pre, cref)
                      if ! listEmpty(ih)
                        topInstance = listHead(ih)
                        @match InnerOuter.TOP_INSTANCE(sm = sm) = topInstance
                        if BaseHashSet.has(cref2, sm)
                          isInSM = true
                        else
                          isInSM = false
                        end
                      else
                        isInSM = false
                      end
                      (cache, comp_env, ih, store, dae, csets, ty, graph_new) = InstVar.instVar(cache, cenv, ih, store, ci_state, mod_1, pre, name, cls, attr, prefixes, dims, nil, inst_dims, impl, comment, info, graph, csets, env2)
                      if isInSM
                        @match DAE.DAE_LIST(elementLst = elems) = dae
                        dae = DAE.DAE_LIST(list(DAE.SM_COMP(cref2, elems)))
                      end
                      (cache, binding) = InstBinding.makeBinding(cache, env2, attr, mod, ty, pre, name, info)
                      dae_attr = DAEUtil.translateSCodeAttrToDAEAttr(attr, prefixes)
                      (ty, _) = Types.traverseType(ty, 1, Types.setIsFunctionPointer)
                      new_var = DAE.TYPES_VAR(name, dae_attr, ty, binding, NONE())
                      env = FGraphUtil.updateComp(env2, new_var, FCore.VAR_DAE(), comp_env)
                      vars = if already_declared
                            nil
                          else
                            list(new_var)
                          end
                      dae = if already_declared
                            DAE.emptyDae
                          else
                            dae
                          end
                      (_, ih, graph) = InnerOuter.handleInnerOuterEquations(io, DAE.emptyDae, ih, graph_new, graph)
                    (cache, env, ih, store, dae, csets, ci_state, vars, graph)
                  end

                  (cache, env, ih, store, mods, pre, ci_state, (comp && SCode.COMPONENT(name, prefixes && SCode.PREFIXES(finalPrefix = final_prefix, innerOuter = io), attr && SCode.ATTR(arrayDims = ad, connectorType = ct), ts && Absyn.TCOMPLEX(path = type_name), m, comment, cond, info), cmod), inst_dims, impl, _, graph, csets)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      if SCodeUtil.finalBool(final_prefix)
                        m = InstUtil.traverseModAddFinal(m)
                        comp = SCode.COMPONENT(name, prefixes, attr, ts, m, comment, cond, info)
                      end
                      already_declared = InstUtil.checkMultiplyDeclared(cache, env, mods, pre, ci_state, (comp, cmod), inst_dims, impl)
                      cref = ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil)
                      (cache, _) = PrefixUtil.prefixCref(cache, env, ih, pre, cref)
                      own_cref = Absyn.CREF_IDENT(name, nil)
                      (cache, m_1) = Mod.elabMod(cache, env, ih, pre, m, impl, Mod.COMPONENT(name), info)
                      id = AbsynUtil.pathString(type_name)
                      cls = SCode.CLASS(id, SCode.defaultPrefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_TYPE(), SCode.DERIVED(ts, SCode.NOMOD(), SCode.ATTR(ad, ct, SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD())), SCode.noComment, info)
                      (cache, dims) = InstUtil.elabArraydim(cache, env, own_cref, Absyn.IDENT("Integer"), ad, NONE(), impl, true, false, pre, info, inst_dims)
                      (cache, comp_env, ih, store, dae, csets, ty, graph_new) = InstVar.instVar(cache, env, ih, store, ci_state, m_1, pre, name, cls, attr, prefixes, dims, nil, inst_dims, impl, comment, info, graph, csets, env)
                      (cache, binding) = InstBinding.makeBinding(cache, env, attr, m_1, ty, pre, name, info)
                      dae_attr = DAEUtil.translateSCodeAttrToDAEAttr(attr, prefixes)
                      (ty, _) = Types.traverseType(ty, 1, Types.setIsFunctionPointer)
                      new_var = DAE.TYPES_VAR(name, dae_attr, ty, binding, NONE())
                      env = FGraphUtil.updateComp(env, new_var, FCore.VAR_DAE(), comp_env)
                      vars = if already_declared
                            nil
                          else
                            list(new_var)
                          end
                      dae = if already_declared
                            DAE.emptyDae
                          else
                            dae
                          end
                      (_, ih, graph) = InnerOuter.handleInnerOuterEquations(io, DAE.emptyDae, ih, graph_new, graph)
                    (cache, env, ih, store, dae, csets, ci_state, vars, graph)
                  end

                  (cache, env, _, _, _, pre, ci_state, (SCode.COMPONENT(name = name, attributes = SCode.ATTR(variability = vt), typeSpec = Absyn.TPATH(t, _), info = info), _), _, _, _, _, _)  => begin
                      @shouldFail (_, _, _) = Lookup.lookupClass(cache, env, t)
                      s = AbsynUtil.pathString(t)
                      scope_str = FGraphUtil.printGraphPathStr(env)
                      pre = PrefixUtil.prefixAdd(name, nil, nil, pre, vt, ci_state, info)
                      ns = PrefixUtil.printPrefixStrIgnoreNoPre(pre)
                      Error.addSourceMessage(Error.LOOKUP_ERROR_COMPNAME, list(s, scope_str, ns), info)
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("Lookup class failed:" + AbsynUtil.pathString(t))
                    fail()
                  end

                  (_, env, _, _, _, _, _, (comp, _), _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.instElement failed: " + SCodeDump.unparseElementStr(comp, SCodeDump.defaultOptions))
                      Debug.traceln("  Scope: " + FGraphUtil.printGraphPathStr(env))
                    fail()
                  end
                end
              end
               #=  Fails if multiple decls not identical
               =#
               #=  The types in the environment does not have correct Binding.
               =#
               #=  We must update those variables that is found in m into a new environment.
               =#
               #=  In case we want to EQBOUND a complex type, e.g. when declaring constants. /sjoelund 2009-10-30
               =#
               #= ---------
               =#
               #=  We build up a class structure for the complex type
               =#
               #=  The variable declaration and the (optional) equation modification are inspected for array dimensions.
               =#
               #=  Gather all the dimensions
               =#
               #=  (Absyn.IDENT(\"Integer\") is used as a dummy)
               =#
               #=  Instantiate the component
               =#
               #=  print(\"instElement -> component: \" + n + \" ty: \" + Types.printTypeStr(ty) + \"\\n\");
               =#
               #=  The environment is extended (updated) with the new variable binding.
               =#
               #=  true in update_frame means the variable is now instantiated.
               =#
               #=  type info present Now we can also put the binding into the dae.
               =#
               #=  If the type is one of the simple, predifined types a simple variable
               =#
               #=  declaration is added to the DAE.
               =#
               #= ------------------------------
               =#
               #=  If the class lookup in the previous rule fails, this rule catches the error
               =#
               #=  and prints an error message about the unknown class.
               =#
               #=  Failure => ({},env,csets,ci_state,{})
               =#
               #=  good for GDB debugging to re-run the instElement again
               =#
               #=  (cache, env, ih, store, dae, csets, ci_state, vars, graph) = instElement(inCache, inEnv, inIH, inUnitStore, inMod, inPrefix, inState, inElement, inInstDims, inImplicit, inCallingScope, inGraph, inSets);
               =#
          (outCache, outEnv, outIH, outUnitStore, outDae, outSets, outState, outVars, outGraph, outFieldDomOpt)
        end

         #= never fail and *NEVER* display any error messages as this function
         prints non-true error messages and even so instElementList dependency
         analysis might work fine and still instantiate. =#
        function updateCompeltsMods(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inComponents::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inState::ClassInf.SMNode, inBoolean::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, List{Tuple{SCode.Element, DAE.Mod}}}
              local outComponents::List{Tuple{SCode.Element, DAE.Mod}}
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outComponents) = begin
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inComponents, inState, inBoolean) begin
                  (_, _, _, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("updateCompeltsMods")
                      (outCache, outEnv, outIH, outComponents) = updateCompeltsMods_dispatch(inCache, inEnv, inIH, inPrefix, inComponents, inState, inBoolean)
                      ErrorExt.rollBack("updateCompeltsMods") #= roll back any errors =#
                    (outCache, outEnv, outIH, outComponents)
                  end

                  _  => begin
                        ErrorExt.rollBack("updateCompeltsMods") #= roll back any errors =#
                      (inCache, inEnv, inIH, inComponents)
                  end
                end
              end
               #= /*
                  case (_,_,_,_,_,_,_)
                    equation
                      true = Config.acceptMetaModelicaGrammar();
                    then
                      (inCache,inEnv,inIH,inComponents);*/ =#
          (outCache, outEnv, outIH, outComponents)
        end

         #= author: PA
          This function updates component modifiers to typed modifiers.
          Typed modifiers are needed  to myMerge modifiers and to be able to
          fully instantiate a component. =#
        function updateCompeltsMods_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inComponents::List{<:Tuple{<:SCode.Element, DAE.Mod}}, inState::ClassInf.SMNode, inBoolean::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, List{Tuple{SCode.Element, DAE.Mod}}}
              local outComponents::List{Tuple{SCode.Element, DAE.Mod}}
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outComponents) = begin
                  local env::FCore.Graph
                  local env2::FCore.Graph
                  local env3::FCore.Graph
                  local pre::Prefix.PrefixType
                  local umod::SCode.Mod
                  local crefs::List{Absyn.ComponentRef}
                  local crefs_1::List{Absyn.ComponentRef}
                  local cref::Absyn.ComponentRef
                  local cmod_1::DAE.Mod
                  local cmod::DAE.Mod
                  local cmod2::DAE.Mod
                  local redMod::DAE.Mod
                  local ltmod::List{DAE.Mod}
                  local res::List{Tuple{SCode.Element, DAE.Mod}}
                  local xs::List{Tuple{SCode.Element, DAE.Mod}}
                  local elMod::Tuple{SCode.Element, DAE.Mod}
                  local comp::SCode.Element
                  local redComp::SCode.Element
                  local ci_state::ClassInf.SMNode
                  local impl::Bool
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local name::String
                  local info::SourceInfo
                  local fprefix::SCode.Final
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inComponents, inState, inBoolean) begin
                  (cache, env, ih, _,  nil(), _, _)  => begin
                    (cache, env, ih, nil)
                  end

                  (cache, env, ih, pre, (elMod && (_, DAE.NOMOD(__))) <| xs, ci_state, impl)  => begin
                    (cache, env, ih, res) = updateCompeltsMods_dispatch(cache, env, ih, pre, xs, ci_state, impl)
                    (cache, env, ih, _cons(elMod, res))
                  end

                  (cache, env, ih, pre, (comp, cmod && DAE.REDECL(element = redComp)) <| xs, ci_state, impl)  => begin
                      info = SCodeUtil.elementInfo(redComp)
                      umod = Mod.unelabMod(cmod)
                      crefs = InstUtil.getCrefFromMod(umod)
                      crefs_1 = InstUtil.getCrefFromCompDim(comp) #= get crefs from dimension arguments =#
                      crefs = ListUtil.unionOnTrue(crefs, crefs_1, AbsynUtil.crefEqual)
                      name = SCodeUtil.elementName(comp)
                      cref = Absyn.CREF_IDENT(name, nil)
                      ltmod = ListUtil.map1(crefs, InstUtil.getModsForDep, xs)
                      cmod2 = ListUtil.fold2r(_cons(cmod, ltmod), Mod.myMerge, name, true, DAE.NOMOD())
                      @match SCode.PREFIXES(finalPrefix = fprefix) = SCodeUtil.elementPrefixes(comp)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env, ih, pre, cmod2, crefs, ci_state, impl)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env2, ih, pre, DAE.MOD(fprefix, SCode.NOT_EACH(), list(DAE.NAMEMOD(name, cmod)), NONE(), info), list(cref), ci_state, impl)
                      (cache, cmod_1) = Mod.updateMod(cache, env2, ih, pre, cmod, impl, info)
                      (cache, env3, ih, res) = updateCompeltsMods_dispatch(cache, env2, ih, pre, xs, ci_state, impl)
                    (cache, env3, ih, _cons((comp, cmod_1), res))
                  end

                  (cache, env, ih, pre, (comp, cmod && DAE.MOD(__)) <| xs, ci_state, impl)  => begin
                      @match false = Mod.isUntypedMod(cmod)
                      name = SCodeUtil.elementName(comp)
                      cref = Absyn.CREF_IDENT(name, nil)
                      @match SCode.PREFIXES(finalPrefix = fprefix) = SCodeUtil.elementPrefixes(comp)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env, ih, pre, DAE.MOD(fprefix, SCode.NOT_EACH(), list(DAE.NAMEMOD(name, cmod)), NONE(), cmod.info), list(cref), ci_state, impl)
                      (cache, env3, ih, res) = updateCompeltsMods_dispatch(cache, env2, ih, pre, xs, ci_state, impl)
                    (cache, env3, ih, _cons((comp, cmod), res))
                  end

                  (cache, env, ih, pre, (comp, cmod && DAE.MOD(__)) <| xs, ci_state, impl)  => begin
                      info = SCodeUtil.elementInfo(comp)
                      umod = Mod.unelabMod(cmod)
                      crefs = InstUtil.getCrefFromMod(umod)
                      crefs_1 = InstUtil.getCrefFromCompDim(comp)
                      crefs = ListUtil.unionOnTrue(crefs, crefs_1, AbsynUtil.crefEqual)
                      name = SCodeUtil.elementName(comp)
                      cref = Absyn.CREF_IDENT(name, nil)
                      ltmod = ListUtil.map1(crefs, InstUtil.getModsForDep, xs)
                      cmod2 = ListUtil.fold2r(ltmod, Mod.myMerge, name, true, DAE.NOMOD())
                      @match SCode.PREFIXES(finalPrefix = fprefix) = SCodeUtil.elementPrefixes(comp)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env, ih, pre, cmod2, crefs, ci_state, impl)
                      (cache, env2, ih) = updateComponentsInEnv(cache, env2, ih, pre, DAE.MOD(fprefix, SCode.NOT_EACH(), list(DAE.NAMEMOD(name, cmod)), NONE(), cmod.info), list(cref), ci_state, impl)
                      (cache, cmod_1) = Mod.updateMod(cache, env2, ih, pre, cmod, impl, info)
                      (cache, env3, ih, res) = updateCompeltsMods_dispatch(cache, env2, ih, pre, xs, ci_state, impl)
                    (cache, env3, ih, _cons((comp, cmod_1), res))
                  end
                end
              end
               #=  Instantiate the element if there is no mod
               =#
               #= /*
                      name = SCodeUtil.elementName(comp);
                      cref = Absyn.CREF_IDENT(name,{});
                      (cache,env,ih) = updateComponentsInEnv(cache, env, ih, pre, DAE.NOMOD(), {cref}, ci_state, impl);
                      */ =#
               #=  Special case for components being redeclared, we might instantiate partial classes when instantiating var(-> instVar2->instClass) to update component in env.
               =#
               #= print(\"(\"+intString(listLength(ltmod))+\")UpdateCompeltsMods_(\" + stringDelimitList(List.map(crefs,AbsynUtil.printComponentRefStr),\",\") + \") subs: \" + stringDelimitList(List.map(crefs,Absyn.printComponentRefStr),\",\")+ \"\\n\");
               =#
               #= print(\"REDECL     acquired mods: \" + Mod.printModStr(cmod2) + \"\\n\");
               =#
               #=  If the modifier has already been updated, just update the environment with it.
               =#
               #= print(\"(\"+intString(listLength(ltmod))+\")UpdateCompeltsMods_(\" + stringDelimitList(List.map(crefs,AbsynUtil.printComponentRefStr),\",\") + \") subs: \" + stringDelimitList(List.map(crefs,Absyn.printComponentRefStr),\",\")+ \"\\n\");
               =#
               #= print(\"     acquired mods: \" + Mod.printModStr(cmod2) + \"\\n\");
               =#
          (outCache, outEnv, outIH, outComponents)
        end

         #= This function takes a DAE.Mod and an SCode.Element and if the modification
           contains a redeclare of that element, the type is changed and an updated
           element is returned. =#
        function redeclareType(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inMod::DAE.Mod, inElement::SCode.Element, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inImpl::Bool, inCmod::DAE.Mod) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, SCode.Element, DAE.Mod}
              local outMod::DAE.Mod = DAE.NOMOD()
              local outElement::SCode.Element = inElement
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local redecl_el::SCode.Element
              local mod::SCode.Mod
              local redecl_mod::DAE.Mod
              local m::DAE.Mod
              local old_m::DAE.Mod
              local redecl_name::String
              local name::String
              local found::Bool
              local repl::SCode.Replaceable
              local cc::Option{SCode.ConstrainClass}
              local cc_comps::List{SCode.Element}
              local crefs::List{Absyn.ComponentRef}

              if ! Mod.isRedeclareMod(inMod)
                outMod = Mod.myMerge(inMod, inCmod)
                return (outCache, outEnv, outIH, outElement, outMod)
              end
              @match DAE.REDECL(element = redecl_el, mod = redecl_mod) = inMod
              redecl_name = SCodeUtil.elementName(redecl_el)
              (outElement, outMod) = begin
                @matchcontinue (redecl_el, inElement) begin
                  (SCode.COMPONENT(__), SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = repl)))  => begin
                       #=  Redeclaration of component.
                       =#
                      @match true = redecl_name == inElement.name
                      mod = InstUtil.chainRedeclares(inMod, redecl_el.modifications)
                      crefs = InstUtil.getCrefFromMod(mod)
                      (outCache, outEnv, outIH) = updateComponentsInEnv(inCache, inEnv, inIH, inPrefix, DAE.NOMOD(), crefs, inState, inImpl)
                      (outCache, m) = Mod.elabMod(outCache, outEnv, outIH, inPrefix, mod, inImpl, Mod.COMPONENT(redecl_name), redecl_el.info)
                      (outCache, old_m) = Mod.elabMod(outCache, outEnv, outIH, inPrefix, inElement.modifications, inImpl, Mod.COMPONENT(inElement.name), inElement.info)
                      m = begin
                        @match repl begin
                          SCode.REPLACEABLE(cc = cc && SOME(_))  => begin
                               #=  Constraining type on the component:
                               =#
                               #=  Extract components belonging to constraining class.
                               =#
                              cc_comps = InstUtil.extractConstrainingComps(cc, inEnv, inPrefix)
                               #=  Keep previous constraining class mods.
                               =#
                              redecl_mod = InstUtil.keepConstrainingTypeModifersOnly(redecl_mod, cc_comps)
                              old_m = InstUtil.keepConstrainingTypeModifersOnly(old_m, cc_comps)
                              m = Mod.myMerge(m, redecl_mod, redecl_name)
                              m = Mod.myMerge(m, old_m, redecl_name)
                              m = Mod.myMerge(m, inCmod, redecl_name)
                            m
                          end

                          _  => begin
                                 #=  No constraining type on comp, throw away modifiers prior to redeclaration:
                                 =#
                                m = Mod.myMerge(redecl_mod, m, redecl_name)
                                m = Mod.myMerge(m, old_m, redecl_name)
                                m = Mod.myMerge(inCmod, m, redecl_name)
                              m
                          end
                        end
                      end
                      (outCache, outElement) = propagateRedeclCompAttr(outCache, outEnv, inElement, redecl_el)
                      outElement = SCodeUtil.setComponentMod(outElement, mod)
                    (outElement, m)
                  end

                  (SCode.CLASS(__), SCode.CLASS(__))  => begin
                       #=  Redeclaration of class.
                       =#
                      @match true = redecl_name == inElement.name
                      (outCache, outEnv, outIH) = updateComponentsInEnv(inCache, inEnv, inIH, inPrefix, inMod, list(Absyn.CREF_IDENT(inElement.name, nil)), inState, inImpl)
                    (inElement, redecl_mod)
                  end

                  (SCode.CLASS(__), SCode.COMPONENT(__))  => begin
                       #=  Local redeclaration of class type path is an id.
                       =#
                      name = AbsynUtil.typeSpecPathString(inElement.typeSpec)
                      @match true = redecl_name == name
                      (outCache, outEnv, outIH) = updateComponentsInEnv(inCache, inEnv, inIH, inPrefix, inMod, list(Absyn.CREF_IDENT(name, nil)), inState, inImpl)
                    (inElement, redecl_mod)
                  end

                  (SCode.CLASS(__), SCode.COMPONENT(__))  => begin
                       #=  Local redeclaration of class, type is qualified.
                       =#
                      name = AbsynUtil.pathFirstIdent(AbsynUtil.typeSpecPath(inElement.typeSpec))
                      @match true = redecl_name == name
                      (outCache, outEnv, outIH) = updateComponentsInEnv(inCache, inEnv, inIH, inPrefix, inMod, list(Absyn.CREF_IDENT(name, nil)), inState, inImpl)
                    (inElement, redecl_mod)
                  end

                  _  => begin
                      (inElement, DAE.NOMOD())
                  end
                end
              end
          (outCache, outEnv, outIH, outElement, outMod)
        end

         #= Helper function to redeclareType, propagates attributes from the old
           component to the new according to the rules for redeclare. =#
        function propagateRedeclCompAttr(inCache::FCore.Cache, inEnv::FCore.Graph, inOldComponent::SCode.Element, inNewComponent::SCode.Element) ::Tuple{FCore.Cache, SCode.Element}
              local outComponent::SCode.Element
              local outCache::FCore.Cache = inCache

              local is_array::Bool = false

               #=  If the old component has array dimensions but the new one doesn't, then we
               =#
               #=  need to check if the new component's type is an array type. If it is we
               =#
               #=  shouldn't propagate the dimensions from the old component. I.e. we should
               =#
               #=  treat: type Real3 = Real[3]; comp(redeclare Real3 x);
               =#
               #=  in the same way as: comp(redeclare Real x[3]).
               =#
              if SCodeUtil.isArrayComponent(inOldComponent) && ! SCodeUtil.isArrayComponent(inNewComponent)
                (outCache, is_array) = Lookup.isArrayType(outCache, inEnv, AbsynUtil.typeSpecPath(SCodeUtil.getComponentTypeSpec(inNewComponent)))
              end
              outComponent = SCodeUtil.propagateAttributesVar(inOldComponent, inNewComponent, is_array)
          (outCache, outComponent)
        end

         #= author: PA
          This function is the second pass of component instantiation, when a
          component can be instantiated fully and the type of the component can be
          determined. The type is added/updated to the environment such that other
          components can use it when they are instantiated. =#
        function updateComponentsInEnv(cache::FCore.Cache, env::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, pre::Prefix.PrefixType, mod::DAE.Mod, crefs::List{<:Absyn.ComponentRef}, ci_state::ClassInf.SMNode, impl::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy}
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = env
              local outCache::FCore.Cache = cache

              ErrorExt.setCheckpoint("updateComponentsInEnv__")
               #=  do NOT fail and do not display any errors from this function as it tries
               =#
               #=  to type and evaluate dependent things but not with enough information
               =#
              try
                (outCache, outEnv, outIH) = updateComponentsInEnv2(cache, env, inIH, pre, mod, crefs, ci_state, impl)
              catch
              end
              ErrorExt.rollBack("updateComponentsInEnv__") #= roll back any errors =#
          (outCache, outEnv, outIH)
        end

         #= Routine to lazily create the hashtable as it usually unused =#
        function getUpdatedCompsHashTable(optHT::Option{<:HashTable5.HashTable}) ::HashTable5.HashTable
              local ht::HashTable5.HashTable

              ht = begin
                @match optHT begin
                  SOME(ht)  => begin
                    ht
                  end

                  _  => begin
                      HashTable5.emptyHashTableSized(BaseHashTable.lowBucketSize)
                  end
                end
              end
          ht
        end

         #= Helper function to updateComponentsInEnv. Does the work for one variable. =#
        function updateComponentInEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, pre::Prefix.PrefixType, mod::DAE.Mod, cref::Absyn.ComponentRef, inCIState::ClassInf.SMNode, impl::Bool, inUpdatedComps::Option{<:HashTable5.HashTable}, currentCref::Option{<:Absyn.ComponentRef} #= The cref that caused this call to updateComponentInEnv. =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, Option{HashTable5.HashTable}}
              local outUpdatedComps::Option{HashTable5.HashTable}
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outUpdatedComps) = begin
                  local n::String
                  local id::String
                  local nn::String
                  local name::String
                  local id2::String
                  local ct::SCode.ConnectorType
                  local io::Absyn.InnerOuter
                  local attr::SCode.Attributes
                  local ad::List{Absyn.Subscript}
                  local prl1::SCode.Parallelism
                  local var1::SCode.Variability
                  local dir::Absyn.Direction
                  local t::Absyn.Path
                  local tsNew::Absyn.TypeSpec
                  local m::SCode.Mod
                  local comment::SCode.Comment
                  local cmod::DAE.Mod
                  local mods::DAE.Mod
                  local rmod::DAE.Mod
                  local cl::SCode.Element
                  local compNew::SCode.Element
                  local cenv::FCore.Graph
                  local env2::FCore.Graph
                  local env_1::FCore.Graph
                  local crefs::List{Absyn.ComponentRef}
                  local crefs2::List{Absyn.ComponentRef}
                  local crefs3::List{Absyn.ComponentRef}
                  local crefs_1::List{Absyn.ComponentRef}
                  local crefs_2::List{Absyn.ComponentRef}
                  local cond::Option{Absyn.Exp}
                  local tyVar::DAE.Var
                  local is::FCore.Status
                  local info::SourceInfo
                  local ih::InstanceHierarchy
                  local pf::SCode.Prefixes
                  local dae_attr::DAE.Attributes
                  local visibility::SCode.Visibility #= protected/public =#
                  local ty::DAE.Type #= type =#
                  local binding::DAE.Binding #= equation modification =#
                  local cnstOpt::Option{DAE.Const} #= the constant-ness of the range if this is a for iterator, NONE() if is NOT a for iterator =#
                  local smod::SCode.Mod
                  local daeMod::DAE.Mod
                  local prefixes::SCode.Prefixes
                  local attributes::SCode.Attributes
                  local compenv::FCore.Graph
                  local env::FCore.Graph
                  local idENV::FCore.Graph
                  local instStatus::FCore.Status
                  local cache::FCore.Cache
                  local updatedComps::HashTable5.HashTable
                  local ci_state::ClassInf.SMNode
                   #=  if there are no modifications, return the same!
                   =#
                   #= case (cache,env,ih,pre,DAE.NOMOD(),cref,ci_state,csets,impl,_)
                   =#
                   #=   then
                   =#
                   #=     (cache,env,ih,csets,updatedComps);
                   =#
                   #=  if we have a redeclare for a component
                   =#
                   #= /*case (cache,env,ih,_,
                          DAE.MOD(binding = NONE(),
                                  subModLst = {
                                    DAE.NAMEMOD(ident=n,
                                    mod = rmod as DAE.REDECL(_, _, {(SCode.COMPONENT(name = name),_)}))}),_,_,_,_,_)
                        equation
                          id = AbsynUtil.crefFirstIdent(cref);
                          true = stringEq(id, name);
                          true = stringEq(id, n);
                          (outCache,outEnv,outIH,outUpdatedComps) = updateComponentInEnv(inCache,inEnv,inIH,pre,rmod,cref,inCIState,impl,inUpdatedComps,currentCref);
                        then
                          (outCache,outEnv,outIH,outUpdatedComps);*/ =#
                   #=  if we have a redeclare for a component
                   =#
                @matchcontinue (inCache, inEnv, inIH, pre, mod, cref, inCIState, impl, inUpdatedComps, currentCref) begin
                  (cache, env, ih, _, DAE.REDECL(element = SCode.COMPONENT(name = name, prefixes = prefixes && SCode.PREFIXES(visibility = visibility), attributes = attributes, modifications = smod, info = info)), _, _, _, _, _)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      @match true = stringEq(id, name)
                      @match false = valueEq(smod, SCode.NOMOD())
                      @match (cache, DAE.TYPES_VAR(_, _, _, _, _), _, _, _, _) = Lookup.lookupIdentLocal(cache, env, name)
                      (cache, daeMod) = Mod.elabMod(cache, env, ih, pre, smod, impl, Mod.COMPONENT(name), info)
                      mods = daeMod
                      attr = attributes
                      m = smod
                      cmod = DAE.NOMOD()
                      pf = prefixes
                      io = SCodeUtil.prefixesInnerOuter(pf)
                      @match SCode.ATTR(ad, ct, prl1, var1, dir) = attr
                      @match (cache, _, SCode.COMPONENT(n, _, _, Absyn.TPATH(t, _), _, _, cond, info), _, _, idENV) = Lookup.lookupIdent(cache, env, id)
                      ci_state = InstUtil.updateClassInfState(cache, idENV, env, inCIState)
                      (cache, cl, cenv) = Lookup.lookupClass(cache, env, t)
                      updatedComps = getUpdatedCompsHashTable(inUpdatedComps)
                      (mods, cmod, m) = InstUtil.noModForUpdatedComponents(var1, updatedComps, cref, mods, cmod, m)
                      crefs = InstUtil.getCrefFromMod(m)
                      crefs2 = InstUtil.getCrefFromDim(ad)
                      crefs3 = InstUtil.getCrefFromCond(cond)
                      crefs_1 = listAppend(crefs, listAppend(crefs2, crefs3))
                      crefs_2 = InstUtil.removeCrefFromCrefs(crefs_1, cref)
                      updatedComps = BaseHashTable.add((cref, 0), updatedComps)
                      @match (cache, env2, ih, SOME(updatedComps)) = updateComponentsInEnv2(cache, env, ih, pre, DAE.NOMOD(), crefs_2, ci_state, impl, SOME(updatedComps), SOME(cref))
                      (cache, env_1, ih, updatedComps) = updateComponentInEnv2(cache, env2, cenv, ih, pre, t, n, ad, cl, attr, pf, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, visibility), info, m, cmod, mods, cref, ci_state, impl, updatedComps)
                    (cache, env_1, ih, SOME(updatedComps))
                  end

                  (cache, env, ih, _, DAE.REDECL(element = SCode.CLASS(name = name)), _, _, _, _, _)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      @match true = stringEq(name, id)
                      (cl, _) = Lookup.lookupClassLocal(env, name)
                      env = FGraphUtil.updateClass(env, SCodeUtil.mergeWithOriginal(mod.element, cl), pre, mod, FCore.CLS_UNTYPED(), env)
                      updatedComps = getUpdatedCompsHashTable(inUpdatedComps)
                      updatedComps = BaseHashTable.add((cref, 0), updatedComps)
                    (cache, env, ih, SOME(updatedComps))
                  end

                  (cache, env, ih, _, _, _, _, _, _, _)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      (cache, _, _, _, is, _) = Lookup.lookupIdent(cache, env, id)
                      @match true = FCore.isTyped(is) #= If InstStatus is typed, return =#
                    (cache, env, ih, inUpdatedComps)
                  end

                  (cache, env, ih, _, mods, _, _, _, _, _)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      @match (cache, _, SCode.COMPONENT(n, pf, attr, Absyn.TPATH(t, _), m, _, cond, info), cmod, _, idENV) = Lookup.lookupIdent(cache, env, id)
                      @match SCode.PREFIXES(innerOuter = io, visibility = visibility) = pf
                      @match SCode.ATTR(ad, ct, prl1, var1, dir) = attr
                      ci_state = InstUtil.updateClassInfState(cache, idENV, env, inCIState)
                      (cache, cl, cenv) = Lookup.lookupClass(cache, env, t)
                      updatedComps = getUpdatedCompsHashTable(inUpdatedComps)
                      (mods, cmod, m) = InstUtil.noModForUpdatedComponents(var1, updatedComps, cref, mods, cmod, m)
                      crefs = ListUtil.flatten(
                                 listAppend(
                                   listAppend(InstUtil.getCrefFromMod(m),
                                     listAppend(InstUtil.getCrefFromDim(ad),
                                       listAppend(InstUtil.getCrefFromCond(cond),
                                                  Mod.getUntypedCrefs(cmod))))))
                      crefs_2 = InstUtil.removeCrefFromCrefs(crefs, cref)
                      crefs_2 = InstUtil.removeOptCrefFromCrefs(crefs_2, currentCref)
                      updatedComps = BaseHashTable.add((cref, 0), updatedComps)
                      @match (cache, env2, ih, SOME(updatedComps)) = updateComponentsInEnv2(cache, env, ih, pre, mods, crefs_2, ci_state, impl, SOME(updatedComps), SOME(cref))
                      (cache, env_1, ih, updatedComps) = updateComponentInEnv2(cache, env2, cenv, ih, pre, t, n, ad, cl, attr, pf, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, visibility), info, m, cmod, mods, cref, ci_state, impl, updatedComps)
                    (cache, env_1, ih, SOME(updatedComps))
                  end

                  (cache, env, ih, _, _, _, _, _, _, _)  => begin
                    (cache, env, ih, inUpdatedComps)
                  end

                  (_, env, _, _, _, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.updateComponentInEnv failed, cref = " + Dump.printComponentRefStr(cref))
                      Debug.traceln(" mods: " + Mod.printModStr(mod))
                      Debug.traceln(" scope: " + FGraphUtil.printGraphPathStr(env))
                      Debug.traceln(" prefix: " + PrefixUtil.printPrefixStr(pre))
                    fail()
                  end

                  _  => begin
                      (inCache, inEnv, inIH, inUpdatedComps)
                  end
                end
              end
               #=  redeclare with modfication!!
               =#
               #=  get Var
               =#
               #=  types are the same, this means only the binding/visibility, etc was updated!
               =#
               #= true = valueEq(tsOld, tsNew);
               =#
               #=  update frame in env!
               =#
               #=  fprintln(Flags.INST_TRACE, \"updateComponentInEnv: found a redeclaration that only changes bindings and prefixes: NEW:\\n\" + SCodeDump.unparseElementStr(compNew) + \" in env:\" + FGraphUtil.printGraphPathStr(env));
               =#
               #=  update the mod then give it to
               =#
               #=  take the mods and attributes from the new comp!
               =#
               #= Debug.traceln(\"update comp \" + n + \" with mods:\" + Mod.printModStr(mods) + \" m:\" + SCodeDump.printModStr(m) + \" cm:\" + Mod.printModStr(cmod));
               =#
               #= Debug.traceln(\"got class \" + SCodeDump.printClassStr(cl));
               =#
               #= print(\"updateComponentInEnv: NEW ENV:\\n\" + FGraphUtil.printGraphStr(env_1) + \"\\n\");
               =#
               #=  redeclare class!
               =#
               #=  fetch the original class!
               =#
               #=  Variable with NONE() element is already instantiated.
               =#
               #=  the default case
               =#
               #= Debug.traceln(\"update comp \" + n + \" with mods:\" + Mod.printModStr(mods) + \" m:\" + SCodeDump.printModStr(m) + \" cm:\" + Mod.printModStr(cmod));
               =#
               #= Debug.traceln(\"got class \" + SCodeDump.printClassStr(cl));
               =#
               #=  Also remove the cref that caused this updateComponentInEnv call, to avoid
               =#
               #=  infinite loops.
               =#
               #=  If first part of ident is a class, e.g StateSelect.None, nothing to update
               =#
               #=  report an error!
               =#
               #= print(\"Env:\\n\" + FGraphUtil.printGraphStr(env) + \"\\n\");
               =#
          (outCache, outEnv, outIH, outUpdatedComps)
        end

         #=  Helper function, checks if the component was already instantiated.
          If it was, don't do it again. =#
        function updateComponentInEnv2(inCache::FCore.Cache, inEnv::FCore.Graph, cenv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, pre::Prefix.PrefixType, path::Absyn.Path, name::String, ad::List{<:Absyn.Subscript}, cl::SCode.Element, attr::SCode.Attributes, inPrefixes::SCode.Prefixes, dattr::DAE.Attributes, info::SourceInfo, m::SCode.Mod, cmod::DAE.Mod, mod::DAE.Mod, cref::Absyn.ComponentRef, ci_state::ClassInf.SMNode, impl::Bool, inUpdatedComps::HashTable5.HashTable) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, HashTable5.HashTable}
              local outUpdatedComps::HashTable5.HashTable
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              try
                ErrorExt.setCheckpoint("Inst.updateComponentInEnv2")
                (outCache, outEnv, outIH, outUpdatedComps) = updateComponentInEnv2_dispatch(inCache, inEnv, cenv, inIH, pre, path, name, ad, cl, attr, inPrefixes, dattr, info, m, cmod, mod, cref, ci_state, impl, inUpdatedComps)
                ErrorExt.delCheckpoint("Inst.updateComponentInEnv2")
              catch
                ErrorExt.rollBack("Inst.updateComponentInEnv2")
                fail()
              end
          (outCache, outEnv, outIH, outUpdatedComps)
        end

        function updateComponentInEnv2_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inClsEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inPath::Absyn.Path, inName::String, inSubscripts::List{<:Absyn.Subscript}, inClass::SCode.Element, inAttr::SCode.Attributes, inPrefixes::SCode.Prefixes, inDAttr::DAE.Attributes, inInfo::SourceInfo, inSMod::SCode.Mod, inClsMod::DAE.Mod, inMod::DAE.Mod, inCref::Absyn.ComponentRef, inState::ClassInf.SMNode, inImpl::Bool, inUpdatedComps::HashTable5.HashTable) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, HashTable5.HashTable}
              local outUpdatedComps::HashTable5.HashTable = inUpdatedComps
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local smod::SCode.Mod
              local mod::DAE.Mod
              local mod1::DAE.Mod
              local mod2::DAE.Mod
              local class_mod::DAE.Mod
              local comp_mod::DAE.Mod
              local eq::Option{DAE.EqMod}
              local own_cref::Absyn.ComponentRef
              local dims::List{DAE.Dimension}
              local cls_env::FCore.Graph
              local comp_env::FCore.Graph
              local cls::SCode.Element
              local ty::DAE.Type
              local binding::DAE.Binding
              local var::DAE.Var

              try
                @match 1 = BaseHashTable.get(inCref, inUpdatedComps)
              catch
                smod = SCodeUtil.mergeModifiers(inSMod, SCodeUtil.getConstrainedByModifiers(inPrefixes))
                (outCache, mod1) = updateComponentInEnv3(outCache, outEnv, outIH, smod, inImpl, Mod.COMPONENT(inName), inInfo)
                class_mod = Mod.lookupModificationP(inMod, inPath)
                mod2 = Mod.myMerge(class_mod, mod1, inName)
                mod2 = Mod.myMerge(inClsMod, mod2, inName)
                (outCache, mod2) = Mod.updateMod(outCache, outEnv, outIH, Prefix.NOPRE(), mod2, inImpl, inInfo)
                mod = if InstUtil.redeclareBasicType(inClsMod)
                      mod1
                    else
                      mod2
                    end
                eq = Mod.modEquation(mod)
                own_cref = Absyn.CREF_IDENT(inName, nil)
                (outCache, dims) = InstUtil.elabArraydim(outCache, outEnv, own_cref, inPath, inSubscripts, eq, inImpl, true, false, inPrefix, inInfo, nil)
                (cls_env, cls, outIH) = FGraph.createVersionScope(outEnv, inName, inPrefix, mod, inClsEnv, inClass, outIH)
                (outCache, comp_env, outIH, _, _, _, ty) = InstVar.instVar(outCache, cls_env, outIH, UnitAbsyn.noStore, inState, mod, inPrefix, inName, cls, inAttr, inPrefixes, dims, nil, nil, inImpl, SCode.noComment, inInfo, ConnectionGraph.EMPTY, DAE.emptySet, outEnv)
                (outCache, binding) = InstBinding.makeBinding(outCache, outEnv, inAttr, mod, ty, inPrefix, inName, inInfo)
                var = DAE.TYPES_VAR(inName, inDAttr, ty, binding, NONE())
                outEnv = FGraphUtil.updateComp(outEnv, var, FCore.VAR_TYPED(), comp_env)
                outUpdatedComps = BaseHashTable.add((inCref, 1), outUpdatedComps)
              end
               #= comp_mod := Mod.lookupCompModification(inMod, inName);
               =#
               #= mod2 := Mod.myMerge(class_mod, comp_mod, inName);
               =#
               #=  Instantiate the component.
               =#
               #=  The environment is extended with the new variable binding.
               =#
          (outCache, outEnv, outIH, outUpdatedComps)
        end

        function updateComponentInEnv3(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inMod::SCode.Mod, inImpl::Bool, inModScope::Mod.ModScope, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Mod}
              local outMod::DAE.Mod
              local outCache::FCore.Cache

              (outCache, outMod) = begin
                  local mod::DAE.Mod
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inIH, inMod, inImpl, inModScope, inInfo) begin
                  (_, _, _, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("updateComponentInEnv3")
                      (cache, mod) = Mod.elabMod(inCache, inEnv, inIH, Prefix.NOPRE(), inMod, inImpl, inModScope, inInfo) #= Prefix does not matter, since we only update types
                               in env, and does not make any dae elements, etc.. =#
                      ErrorExt.rollBack("updateComponentInEnv3") #= Rollback all error since we are only interested in type, not value at
                               this point. Errors that occur in elabMod which does not fail the
                               function will be accepted. =#
                    (cache, mod)
                  end

                  _  => begin
                        ErrorExt.rollBack("updateComponentInEnv3")
                      fail()
                  end
                end
              end
               #= /*/ did not work, elab it untyped!
                  case (cache, _, _, _, _, _)
                    equation
                      ErrorExt.rollBack(\"updateComponentInEnv3\");
                      ErrorExt.setCheckpoint(\"updateComponentInEnv3\");
                      mod = Mod.elabUntypedMod(inMod, inEnv, Prefix.NOPRE());
                      ErrorExt.rollBack(\"updateComponentInEnv3\")
                      \"Rollback all error since we are only interested in type, not value at
                       this point. Errors that occur in elabMod which does not fail the
                       function will be accepted.\";
                    then
                      (cache, mod);*/ =#
          (outCache, outMod)
        end

         #= This function takes a SCode.Program and builds an environment. =#
        function makeEnvFromProgram(prog::SCode.Program) ::Tuple{FCore.Cache, FCore.Graph}
              local env_1::FCore.Graph
              local outCache::FCore.Cache

              local env::FCore.Graph
              local cache::FCore.Cache

               #=  prog := scodeFlatten(prog, path);
               =#
              (cache, env) = Builtin.initialGraph(FCoreUtil.emptyCache())
              env_1 = FGraphBuildEnv.mkProgramGraph(prog, FCore.USERDEFINED(), env)
              outCache = cache
          (outCache, env_1)
        end

         #= author: PA
          Transforms a class name to its fully qualified name by investigating the environment.
          For instance, the model Resistor in Modelica.Electrical.Analog.Basic will given the
          correct environment have the fully qualified name: Modelica.Electrical.Analog.Basic.Resistor =#
        function makeFullyQualified(cache::FCore.Cache, inEnv::FCore.Graph, path::Absyn.Path) ::Tuple{FCore.Cache, Absyn.Path}



              (cache, path) = begin
                @match path begin
                  Absyn.IDENT(__)  => begin
                       #=  Special cases: assert and reinit can not be handled by builtin.mo, since they do not have return type
                       =#
                      (cache, path) = makeFullyQualifiedIdent(cache, inEnv, path.name, path)
                    (cache, path)
                  end

                  Absyn.FULLYQUALIFIED(__)  => begin
                    (cache, path)
                  end

                  Absyn.QUALIFIED(__)  => begin
                       #=  do NOT fully quallify again a fully qualified path!
                       =#
                       #=  To make a class fully qualified, the class path is looked up in the environment.
                       =#
                       #=  The FQ path consist of the simple class name appended to the environment path of the looked up class.
                       =#
                      (cache, path) = makeFullyQualifiedFromQual(cache, inEnv, path)
                    (cache, path)
                  end
                end
              end
          (cache, path)
        end

        function makeFullyQualifiedFromQual(cache::FCore.Cache, inEnv::FCore.Graph, path::Absyn.Path) ::Tuple{FCore.Cache, Absyn.Path}



              (cache, path) = begin
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local path_2::Absyn.Path
                  local path3::Absyn.Path
                  local s::String
                  local cl::SCode.Element
                  local crPath::DAE.ComponentRef
                  local fs::FCore.Graph
                  local name::Absyn.Ident
                  local ename::Absyn.Ident
                  local r::FCore.MMRef
                @matchcontinue path begin
                  _  => begin
                      @match (cache, SCode.CLASS(name = name), env_1) = Lookup.lookupClass(cache, inEnv, path)
                      path_2 = makeFullyQualified2(env_1, name)
                    (cache, AbsynUtil.makeFullyQualified(path_2))
                  end

                  _  => begin
                      crPath = ComponentReference.pathToCref(path)
                      (cache, _, _, _, _, _, env, _, name) = Lookup.lookupVarInternal(cache, inEnv, crPath, InstTypes.SEARCH_ALSO_BUILTIN())
                      path3 = makeFullyQualified2(env, name)
                    (cache, AbsynUtil.makeFullyQualified(path3))
                  end

                  _  => begin
                      crPath = ComponentReference.pathToCref(path)
                      (cache, env, _, _, _, _, _, _, name) = Lookup.lookupVarInPackages(cache, inEnv, crPath, nil, Mutable.create(false))
                      path3 = makeFullyQualified2(env, name)
                    (cache, AbsynUtil.makeFullyQualified(path3))
                  end

                  _  => begin
                      (cache, path)
                  end
                end
              end
          (cache, path)
        end

         #= author: PA
          Transforms a class name to its fully qualified name by investigating the environment.
          For instance, the model Resistor in Modelica.Electrical.Analog.Basic will given the
          correct environment have the fully qualified name: Modelica.Electrical.Analog.Basic.Resistor =#
        function makeFullyQualifiedIdent(inCache::FCore.Cache, inEnv::FCore.Graph, ident::String, inPath::Absyn.Path = Absyn.IDENT("")) ::Tuple{FCore.Cache, Absyn.Path}
              local outPath::Absyn.Path
              local outCache::FCore.Cache

              local isKnownBuiltin::Bool

              (outPath, isKnownBuiltin) = makeFullyQualifiedIdentCheckBuiltin(ident)
              if isKnownBuiltin
                outCache = inCache
                return (outCache, outPath)
              end
              (outCache, outPath) = begin
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local path::Absyn.Path
                  local path_2::Absyn.Path
                  local path3::Absyn.Path
                  local s::String
                  local cache::FCore.Cache
                  local cl::SCode.Element
                  local crPath::DAE.ComponentRef
                  local fs::FCore.Graph
                  local name::Absyn.Ident
                  local ename::Absyn.Ident
                  local r::FCore.MMRef
                   #=  To make a class fully qualified, the class path is looked up in the environment.
                   =#
                   #=  The FQ path consist of the simple class name appended to the environment path of the looked up class.
                   =#
                @matchcontinue (inCache, inEnv, ident) begin
                  (cache, env, _)  => begin
                      @match (cache, SCode.CLASS(name = name), env_1) = Lookup.lookupClassIdent(cache, env, ident)
                      path_2 = makeFullyQualified2(env_1, name)
                    (cache, AbsynUtil.makeFullyQualified(path_2))
                  end

                  (cache, env, s)  => begin
                      r = FGraphUtil.lastScopeRef(env)
                      @match false = FNode.isRefTop(r)
                      name = FNode.refName(r)
                      @match true = name == s
                      @match SOME(path_2) = FGraphUtil.getScopePath(env)
                    (cache, AbsynUtil.makeFullyQualified(path_2))
                  end

                  (cache, env, s)  => begin
                      (cache, _, env_1) = Lookup.lookupTypeIdent(cache, env, s, NONE())
                      path_2 = makeFullyQualified2(env_1, s, inPath)
                    (cache, AbsynUtil.makeFullyQualified(path_2))
                  end

                  (cache, env, _)  => begin
                      (cache, _, _, _, _, _, env, _, name) = Lookup.lookupVarInternalIdent(cache, env, ident, nil, InstTypes.SEARCH_ALSO_BUILTIN())
                      path3 = makeFullyQualified2(env, name)
                    (cache, AbsynUtil.makeFullyQualified(path3))
                  end

                  (cache, env, _)  => begin
                      (cache, env, _, _, _, _, _, _, name) = Lookup.lookupVarInPackagesIdent(cache, env, ident, nil, nil, Mutable.create(false))
                      path3 = makeFullyQualified2(env, name)
                    (cache, AbsynUtil.makeFullyQualified(path3))
                  end

                  _  => begin
                      (inCache, begin
                        @match inPath begin
                          Absyn.IDENT("")  => begin
                            Absyn.IDENT(ident)
                          end

                          _  => begin
                              inPath
                          end
                        end
                      end)
                  end
                end
              end
               #=  Needed to make external objects fully-qualified
               =#
               #=  A type can exist without a class (i.e. builtin functions)
               =#
               #=  A package constant, first try to look it up local (top frame)
               =#
               #=  TODO! FIXME! what do we do here??!!
               =#
               #=  If it fails, leave name unchanged.
               =#
          (outCache, outPath)
        end

        function makeFullyQualifiedIdentCheckBuiltin(ident::String) ::Tuple{Absyn.Path, Bool}
              local isKnownBuiltin::Bool = true
              local path::Absyn.Path

              path = begin
                @match ident begin
                  "Boolean"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("Boolean"))
                  end

                  "Integer"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("Integer"))
                  end

                  "Real"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("Real"))
                  end

                  "String"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("String"))
                  end

                  "EnumType"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("EnumType"))
                  end

                  "assert"  => begin
                    Absyn.IDENT("assert")
                  end

                  "reinit"  => begin
                    Absyn.IDENT("reinit")
                  end

                  "smooth"  => begin
                    Absyn.IDENT("smooth")
                  end

                  "list"  => begin
                       #=  Builtin functions are handled after lookup of class (in case it is shadowed)
                       =#
                       #=  Other functions that can not be represented in env due to e.g. applicable to any record
                       =#
                       #=  MetaModelica extensions
                       =#
                      isKnownBuiltin = Config.acceptMetaModelicaGrammar()
                    Absyn.IDENT("list")
                  end

                  "Option"  => begin
                      isKnownBuiltin = Config.acceptMetaModelicaGrammar()
                    Absyn.IDENT("Option")
                  end

                  "tuple"  => begin
                      isKnownBuiltin = Config.acceptMetaModelicaGrammar()
                    Absyn.IDENT("tuple")
                  end

                  "polymorphic"  => begin
                      isKnownBuiltin = Config.acceptMetaModelicaGrammar()
                    Absyn.IDENT("polymorphic")
                  end

                  "array"  => begin
                      isKnownBuiltin = Config.acceptMetaModelicaGrammar()
                    Absyn.IDENT("array")
                  end

                  _  => begin
                        isKnownBuiltin = false
                      Absyn.IDENT("")
                  end
                end
              end
          (path, isKnownBuiltin)
        end

         #= This is a utility used to do instantiation of list
          of things, collecting the result in another list. =#
        function instList(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, instFunc::InstFunc, inTypeALst::List{<:Type_a}, inBoolean::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = begin
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local csets::DAE.Sets
                  local csets_1::DAE.Sets
                  local csets_2::DAE.Sets
                  local ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local ci_state_2::ClassInf.SMNode
                  local impl::Bool
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local dae::DAE.DAElist
                  local e::Type_a
                  local es::List{Type_a}
                  local cache::FCore.Cache
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                @match (inCache, inEnv, inIH, inPrefix, inSets, inState, instFunc, inTypeALst, inBoolean, unrollForLoops, inGraph) begin
                  (cache, env, ih, _, csets, ci_state, _,  nil(), _, _, graph)  => begin
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, _, e <| es, impl, _, graph)  => begin
                      # @show instFunc
                      # @show e
                      (cache, env_1, ih, dae1, csets_1, ci_state_1, graph) = instFunc(cache, env, ih, pre, csets, ci_state, e, impl, unrollForLoops, graph)
                      # @show es
                      (cache, env_2, ih, dae2, csets_2, ci_state_2, graph) = instList(cache, env_1, ih, pre, csets_1, ci_state_1, instFunc, es, impl, unrollForLoops, graph)
                      dae = DAEUtil.joinDaes(dae1, dae2)
                    (cache, env_2, ih, dae, csets_2, ci_state_2, graph)
                  end
                end
              end
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

        function instConstraints(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inConstraints::List{<:SCode.ConstraintSection}, inImpl::Bool) ::Tuple{FCore.Cache, FCore.Graph, DAE.DAElist, ClassInf.SMNode}
              local outState::ClassInf.SMNode
              local outDae::DAE.DAElist
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outDae, outState) = begin
                  local env1::FCore.Graph
                  local env2::FCore.Graph
                  local constraints_1::DAE.DAElist
                  local constraints_2::DAE.DAElist
                  local ci_state::ClassInf.SMNode
                  local rest::List{SCode.ConstraintSection}
                  local constr::SCode.ConstraintSection
                  local cache::FCore.Cache
                  local dae::DAE.DAElist
                @match (inCache, inEnv, inPrefix, inState, inConstraints, inImpl) begin
                  (_, _, _, _,  nil(), _)  => begin
                    (inCache, inEnv, DAE.emptyDae, inState)
                  end

                  (_, _, _, _, constr <| rest, _)  => begin
                      (cache, env1, constraints_1, ci_state) = InstSection.instConstraint(inCache, inEnv, inPrefix, inState, constr, inImpl)
                      (cache, env2, constraints_2, ci_state) = instConstraints(cache, env1, inPrefix, ci_state, rest, inImpl)
                      dae = DAEUtil.joinDaes(constraints_1, constraints_2)
                    (cache, env2, dae, ci_state)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Inst.instConstraints failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outEnv, outDae, outState)
        end

        function instClassAttributes(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inAttrs::List{<:Absyn.NamedArg}, inBoolean::Bool, inInfo::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, DAE.DAElist}
              local outDae::DAE.DAElist
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outDae) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local clsAttrs::DAE.DAElist
                  local dae::DAE.DAElist
                @match (inCache, inEnv, inPrefix, inAttrs, inBoolean, inInfo) begin
                  (cache, env, _,  nil(), _, _)  => begin
                    (cache, env, DAE.emptyDae)
                  end

                  (_, _, _, _, _, _)  => begin
                      clsAttrs = DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(NONE(), NONE(), NONE(), NONE()))))
                      (cache, env, dae) = instClassAttributes2(inCache, inEnv, inPrefix, inAttrs, inBoolean, inInfo, clsAttrs)
                    (cache, env, dae)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Inst.instClassAttributes failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outEnv, outDae)
        end

        function instClassAttributes2(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inAttrs::List{<:Absyn.NamedArg}, inBoolean::Bool, inInfo::SourceInfo, inClsAttrs::DAE.DAElist) ::Tuple{FCore.Cache, FCore.Graph, DAE.DAElist}
              local outDae::DAE.DAElist
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outDae) = begin
                  local env::FCore.Graph
                  local env_2::FCore.Graph
                  local pre::Prefix.PrefixType
                  local impl::Bool
                  local na::Absyn.NamedArg
                  local rest::List{Absyn.NamedArg}
                  local cache::FCore.Cache
                  local attrName::Absyn.Ident
                  local attrExp::Absyn.Exp
                  local outExp::DAE.Exp
                  local outProps::DAE.Properties
                  local clsAttrs::DAE.DAElist
                @match (inCache, inEnv, inPrefix, inAttrs, inBoolean, inInfo, inClsAttrs) begin
                  (cache, env, _,  nil(), _, _, clsAttrs)  => begin
                    (cache, env, clsAttrs)
                  end

                  (cache, env, pre, na <| rest, impl, _, clsAttrs)  => begin
                      @match Absyn.NAMEDARG(attrName, attrExp) = na
                      (cache, outExp, _) = Static.elabExp(cache, env, attrExp, impl, false, pre, inInfo)
                      clsAttrs = insertClassAttribute(clsAttrs, attrName, outExp)
                      (cache, env_2, clsAttrs) = instClassAttributes2(cache, env, pre, rest, impl, inInfo, clsAttrs)
                    (cache, env_2, clsAttrs)
                  end

                  _  => begin
                        Error.addMessage(Error.OPTIMICA_ERROR, list("Class Attributes allowed only for Optimization classes."))
                      fail()
                  end
                end
              end
               #= /*vectorize*/ =#
          (outCache, outEnv, outDae)
        end

        function insertClassAttribute(inAttrs::DAE.DAElist, attrName::Absyn.Ident, inAttrExp::DAE.Exp) ::DAE.DAElist
              local outAttrs::DAE.DAElist

              outAttrs = begin
                  local objectiveE::Option{DAE.Exp}
                  local startTimeE::Option{DAE.Exp}
                  local finalTimeE::Option{DAE.Exp}
                  local objectiveIntegrandE::Option{DAE.Exp}
                  local attrs::DAE.DAElist
                @match (inAttrs, attrName, inAttrExp) begin
                  (attrs, "objective", _)  => begin
                      @match DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(_, objectiveIntegrandE, startTimeE, finalTimeE)))) = attrs
                      attrs = DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(SOME(inAttrExp), objectiveIntegrandE, startTimeE, finalTimeE))))
                    attrs
                  end

                  (attrs, "objectiveIntegrand", _)  => begin
                      @match DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, _, startTimeE, finalTimeE)))) = attrs
                      attrs = DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, SOME(inAttrExp), startTimeE, finalTimeE))))
                    attrs
                  end

                  (attrs, "startTime", _)  => begin
                      @match DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, objectiveIntegrandE, _, finalTimeE)))) = attrs
                      attrs = DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, objectiveIntegrandE, SOME(inAttrExp), finalTimeE))))
                    attrs
                  end

                  (attrs, "finalTime", _)  => begin
                      @match DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, objectiveIntegrandE, startTimeE, _)))) = attrs
                      attrs = DAE.DAE_LIST(list(DAE.CLASS_ATTRIBUTES(DAE.OPTIMIZATION_ATTRS(objectiveE, objectiveIntegrandE, startTimeE, SOME(inAttrExp)))))
                    attrs
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Inst.insertClassAttribute failed\\n")
                      fail()
                  end
                end
              end
          outAttrs
        end

         #=
        Author BZ 2008-06,
        Instantiate a class, but _allways_ as inner class. This due to that we do not want flow equations equal to zero.
        Called from Interactive.mo, boschsection.
         =#
        function instantiateBoschClass(inCache::FCore.Cache, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDAElist::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDAElist) = begin
                  local cr::Absyn.Path
                  local path::Absyn.Path
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local dae1::DAE.DAElist
                  local dae::DAE.DAElist
                  local cdecls::List{SCode.Element}
                  local name2::String
                  local n::String
                  local pathstr::String
                  local name::String
                  local cname_str::String
                  local cdef::SCode.Element
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, inIH, inProgram, inPath) begin
                  (_, _,  nil(), _)  => begin
                      Error.addMessage(Error.NO_CLASSES_LOADED, nil)
                    fail()
                  end

                  (cache, ih, cdecls && _ <| _, path && Absyn.IDENT(__))  => begin
                      (cache, env) = Builtin.initialGraph(cache)
                      env_1 = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      (cache, env_2, ih, dae) = instBoschClassInProgram(cache, env_1, ih, cdecls, path)
                    (cache, env_2, ih, dae)
                  end

                  (cache, ih, cdecls && _ <| _, path && Absyn.QUALIFIED(__))  => begin
                      (cache, env) = Builtin.initialGraph(cache)
                      env_1 = FGraphBuildEnv.mkProgramGraph(cdecls, FCore.USERDEFINED(), env)
                      @match (cache, cdef && SCode.CLASS(), env_2) = Lookup.lookupClass(cache, env_1, path, SOME(AbsynUtil.dummyInfo))
                      (cache, env_2, ih, _, dae, _, _, _, _, _) = instClass(cache, env_2, ih, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), cdef, nil, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet) #= impl =#
                      _ = AbsynUtil.pathString(path)
                    (cache, env_2, ih, dae)
                  end

                  (_, _, _, path)  => begin
                      cname_str = AbsynUtil.pathString(path)
                      Error.addMessage(Error.ERROR_FLATTENING, list(cname_str))
                    fail()
                  end
                end
              end
               #= /* top level class */ =#
               #= /* class in package */ =#
               #= /* error instantiating */ =#
          (outCache, outEnv, outIH, outDAElist)
        end

         #= Helper function for instantiateBoschClass =#
        function instBoschClassInProgram(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inProgram::SCode.Program, inPath::SCode.Path) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, DAE.DAElist}
              local outDae::DAE.DAElist
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae) = begin
                  local dae::DAE.DAElist
                  local env_1::FCore.Graph
                  local env::FCore.Graph
                  local c::SCode.Element
                  local name1::String
                  local name2::String
                  local cs::List{SCode.Element}
                  local path::Absyn.Path
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, inEnv, inIH, inProgram, inPath) begin
                  (cache, env, ih, c && SCode.CLASS(name = name1) <| _, Absyn.IDENT(name = name2))  => begin
                      @match true = stringEq(name1, name2)
                      (cache, env_1, ih, _, dae, _, _, _, _, _) = instClass(cache, env, ih, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), c, nil, false, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet) #= impl =#
                    (cache, env_1, ih, dae)
                  end

                  (cache, env, ih, SCode.CLASS(name = name1) <| cs, path && Absyn.IDENT(name = name2))  => begin
                      @match false = stringEq(name1, name2)
                      (cache, env, ih, dae) = instBoschClassInProgram(cache, env, ih, cs, path)
                    (cache, env, ih, dae)
                  end

                  (cache, env, ih,  nil(), _)  => begin
                    (cache, env, ih, DAE.emptyDae)
                  end
                end
              end
          (outCache, outEnv, outIH, outDae)
        end

         #=  Here we check a modifier and a path,
         if we have a redeclaration of the class
         pointed by the path, we add this to a
         special reclaration modifier.
         Function returning 2 modifiers:
         - one (first output) to represent the redeclaration of
                              'current' class (class-name equal to path)
         - two (second output) to represent any other modifier. =#
        function modifyInstantiateClass(inMod::DAE.Mod, path::Absyn.Path) ::Tuple{DAE.Mod, DAE.Mod}
              local omod2::DAE.Mod
              local omod1::DAE.Mod

              (omod1, omod2) = begin
                  local id::String
                @match inMod begin
                  DAE.REDECL(element = SCode.CLASS(name = id))  => begin
                    if id == AbsynUtil.pathString(path)
                          (inMod, DAE.NOMOD())
                        else
                          (DAE.NOMOD(), inMod)
                        end
                  end

                  _  => begin
                      (DAE.NOMOD(), inMod)
                  end
                end
              end
          (omod1, omod2)
        end

         #=  BZ 2007-07-03
         This function checks if there is a reference to itself.
         If it is, it removes the reference.
         But also instantiate the declared type, if any.
         If it fails (declarations of array dimensions using
         the size of itself) it will just remove the element. =#
        function removeSelfReferenceAndUpdate(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inStore::UnitAbsyn.InstStore, inRefs::List{<:Absyn.ComponentRef}, inRef::Absyn.ComponentRef, inPath::Absyn.Path, inState::ClassInf.SMNode, iattr::SCode.Attributes, inPrefixes::SCode.Prefixes, impl::Bool, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, pre::Prefix.PrefixType, mods::DAE.Mod, scodeMod::SCode.Mod, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, UnitAbsyn.InstStore, List{Absyn.ComponentRef}}
              local o1::List{Absyn.ComponentRef}
              local outStore::UnitAbsyn.InstStore
              local outIH::InnerOuterTypes.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outStore, o1) = begin
                  local sty::Absyn.Path
                  local c1::Absyn.ComponentRef
                  local cl1::List{Absyn.ComponentRef}
                  local cl2::List{Absyn.ComponentRef}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local compenv::FCore.Graph
                  local cenv::FCore.Graph
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local ad::List{Absyn.Subscript}
                  local prl1::SCode.Parallelism
                  local var1::SCode.Variability
                  local dir::Absyn.Direction
                  local n::Ident
                  local c::SCode.Element
                  local ty::DAE.Type
                  local state::ClassInf.SMNode
                  local vis::SCode.Visibility
                  local ct::SCode.ConnectorType
                  local attr::SCode.Attributes
                  local dims::DAE.Dimensions
                  local inst_dims::InstDims
                  local new_var::DAE.Var
                  local ih::InstanceHierarchy
                  local io::Absyn.InnerOuter
                  local store::UnitAbsyn.InstStore
                  local m::DAE.Mod
                  local smod::SCode.Mod
                @matchcontinue (inCache, inEnv, inIH, inStore, inRefs, inRef, inPath, inState, iattr, inPrefixes, impl, inInstDims, pre, mods, scodeMod, info) begin
                  (cache, env, ih, store, cl1, c1, _, _, _, _, _, _, _, _, _, _)  => begin
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                      i1 = listLength(cl2)
                      i2 = listLength(cl1)
                      @match true = i1 == i2
                    (cache, env, ih, store, cl2)
                  end

                  (cache, env, ih, store, cl1, c1 && Absyn.CREF_IDENT(name = n), sty, state, attr && SCode.ATTR(arrayDims = ad, connectorType = ct, parallelism = prl1, variability = var1, direction = dir), _, _, inst_dims, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("Inst.removeSelfReferenceAndUpdate")
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                      (cache, c, cenv) = Lookup.lookupClass(cache, env, sty, SOME(info))
                      (cache, dims) = InstUtil.elabArraydim(cache, cenv, c1, sty, ad, NONE(), impl, true, false, pre, info, inst_dims)
                      smod = SCodeInstUtil.removeSelfReferenceFromMod(scodeMod, c1)
                      (cache, m) = Mod.elabMod(cache, env, ih, pre, smod, impl, Mod.COMPONENT(n), info)
                      (cenv, c, ih) = FGraph.createVersionScope(env, n, pre, m, cenv, c, ih)
                      (cache, compenv, ih, store, _, _, ty, _) = InstVar.instVar(cache, cenv, ih, store, state, m, pre, n, c, attr, inPrefixes, dims, nil, inst_dims, true, SCode.noComment, info, ConnectionGraph.EMPTY, DAE.emptySet, env)
                      io = SCodeUtil.prefixesInnerOuter(inPrefixes)
                      vis = SCodeUtil.prefixesVisibility(inPrefixes)
                      new_var = DAE.TYPES_VAR(n, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, vis), ty, DAE.UNBOUND(), NONE())
                      env = FGraphUtil.updateComp(env, new_var, FCore.VAR_TYPED(), compenv)
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    (cache, env, ih, store, cl2)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    fail()
                  end

                  (cache, env, ih, store, cl1, c1 && Absyn.CREF_IDENT(name = n), sty, state, attr && SCode.ATTR(arrayDims = ad, connectorType = ct, parallelism = prl1, variability = var1, direction = dir), _, _, inst_dims, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("Inst.removeSelfReferenceAndUpdate")
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                      (cache, c, cenv) = Lookup.lookupClass(cache, env, sty, SOME(info))
                      (cache, dims) = InstUtil.elabArraydim(cache, cenv, c1, sty, ad, NONE(), impl, true, false, pre, info, inst_dims)
                      smod = SCodeInstUtil.removeNonConstantBindingsKeepRedeclares(scodeMod, false)
                      (cache, m) = Mod.elabMod(cache, env, ih, pre, smod, impl, Mod.COMPONENT(n), info)
                      (cenv, c, ih) = FGraph.createVersionScope(env, n, pre, m, cenv, c, ih)
                      (cache, compenv, ih, store, _, _, ty, _) = InstVar.instVar(cache, cenv, ih, store, state, m, pre, n, c, attr, inPrefixes, dims, nil, inst_dims, true, SCode.noComment, info, ConnectionGraph.EMPTY, DAE.emptySet, env)
                      io = SCodeUtil.prefixesInnerOuter(inPrefixes)
                      vis = SCodeUtil.prefixesVisibility(inPrefixes)
                      new_var = DAE.TYPES_VAR(n, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, vis), ty, DAE.UNBOUND(), NONE())
                      env = FGraphUtil.updateComp(env, new_var, FCore.VAR_TYPED(), compenv)
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    (cache, env, ih, store, cl2)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    fail()
                  end

                  (cache, env, ih, store, cl1, c1 && Absyn.CREF_IDENT(name = n), sty, state, attr && SCode.ATTR(arrayDims = ad, connectorType = ct, parallelism = prl1, variability = var1, direction = dir), _, _, inst_dims, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("Inst.removeSelfReferenceAndUpdate")
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                      (cache, c, cenv) = Lookup.lookupClass(cache, env, sty, SOME(info))
                      (cache, dims) = InstUtil.elabArraydim(cache, cenv, c1, sty, ad, NONE(), impl, true, false, pre, info, inst_dims)
                      smod = SCodeInstUtil.removeNonConstantBindingsKeepRedeclares(scodeMod, true)
                      (cache, m) = Mod.elabMod(cache, env, ih, pre, smod, impl, Mod.COMPONENT(n), info)
                      (cenv, c, ih) = FGraph.createVersionScope(env, n, pre, m, cenv, c, ih)
                      (cache, compenv, ih, store, _, _, ty, _) = InstVar.instVar(cache, cenv, ih, store, state, m, pre, n, c, attr, inPrefixes, dims, nil, inst_dims, true, SCode.noComment, info, ConnectionGraph.EMPTY, DAE.emptySet, env)
                      io = SCodeUtil.prefixesInnerOuter(inPrefixes)
                      vis = SCodeUtil.prefixesVisibility(inPrefixes)
                      new_var = DAE.TYPES_VAR(n, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, vis), ty, DAE.UNBOUND(), NONE())
                      env = FGraphUtil.updateComp(env, new_var, FCore.VAR_TYPED(), compenv)
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    (cache, env, ih, store, cl2)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    fail()
                  end

                  (cache, env, ih, store, cl1, c1 && Absyn.CREF_IDENT(name = n), sty, state, attr && SCode.ATTR(arrayDims = ad, connectorType = ct, parallelism = prl1, variability = var1, direction = dir), _, _, inst_dims, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("Inst.removeSelfReferenceAndUpdate")
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                      (cache, c, cenv) = Lookup.lookupClass(cache, env, sty, SOME(info))
                      (cache, dims) = InstUtil.elabArraydim(cache, cenv, c1, sty, ad, NONE(), impl, true, false, pre, info, inst_dims)
                      m = DAE.NOMOD()
                      (cenv, c, ih) = FGraph.createVersionScope(env, n, pre, m, cenv, c, ih)
                      (cache, compenv, ih, store, _, _, ty, _) = InstVar.instVar(cache, cenv, ih, store, state, m, pre, n, c, attr, inPrefixes, dims, nil, inst_dims, true, SCode.noComment, info, ConnectionGraph.EMPTY, DAE.emptySet, env)
                      io = SCodeUtil.prefixesInnerOuter(inPrefixes)
                      vis = SCodeUtil.prefixesVisibility(inPrefixes)
                      new_var = DAE.TYPES_VAR(n, DAE.ATTR(DAEUtil.toConnectorTypeNoState(ct), prl1, var1, dir, io, vis), ty, DAE.UNBOUND(), NONE())
                      env = FGraphUtil.updateComp(env, new_var, FCore.VAR_TYPED(), compenv)
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    (cache, env, ih, store, cl2)
                  end

                  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      ErrorExt.rollBack("Inst.removeSelfReferenceAndUpdate")
                    fail()
                  end

                  (cache, env, ih, store, cl1, c1, _, _, _, _, _, _, _, _, _, _)  => begin
                      cl2 = InstUtil.removeCrefFromCrefs(cl1, c1)
                    (cache, env, ih, store, cl2)
                  end
                end
              end
          (outCache, outEnv, outIH, outStore, o1)
        end

         #= author: PA
          Help function to updateComponentsInEnv. =#
        function updateComponentsInEnv2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, pre::Prefix.PrefixType, mod::DAE.Mod, crefs::List{<:Absyn.ComponentRef}, ci_state::ClassInf.SMNode, impl::Bool, inUpdatedComps::Option{<:HashTable5.HashTable} = NONE(), currentCref::Option{<:Absyn.ComponentRef} = NONE()) ::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, Option{HashTable5.HashTable}}
              local outUpdatedComps::Option{HashTable5.HashTable} = inUpdatedComps
              local outIH::InnerOuterTypes.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              local name::String
              local binding::DAE.Binding

              for cr in crefs
                try
                  @match Absyn.CREF_IDENT(name = name, subscripts = nil) = cr
                  @match (_, DAE.TYPES_VAR(binding = binding), _, _, _, _) = Lookup.lookupIdentLocal(outCache, outEnv, name)
                  @match true = DAEUtil.isBound(binding)
                catch
                  (outCache, outEnv, outIH, outUpdatedComps) = updateComponentInEnv(outCache, outEnv, outIH, pre, mod, cr, ci_state, impl, outUpdatedComps, currentCref)
                end
              end
          (outCache, outEnv, outIH, outUpdatedComps)
        end

         #= help function to makeFullyQualified =#
        function makeFullyQualified2(env::FCore.Graph, name::String, cachedPath::Absyn.Path = Absyn.IDENT("")) ::Absyn.Path
              local path::Absyn.Path

              local scope::Absyn.Path
              local oscope::Option{Absyn.Path}

              oscope = FGraphUtil.getScopePath(env)
              if isNone(oscope)
                path = makeFullyQualified2Builtin(name, cachedPath)
              else
                @match SOME(scope) = oscope
                path = AbsynUtil.joinPaths(scope, begin
                  @match cachedPath begin
                    Absyn.IDENT("")  => begin
                      Absyn.IDENT(name)
                    end

                    _  => begin
                        cachedPath
                    end
                  end
                end)
              end
          path
        end

         #= Lookup table to avoid memory allocation of common built-in function calls =#
        function makeFullyQualified2Builtin(ident::String, cachedPath::Absyn.Path) ::Absyn.Path
              local path::Absyn.Path

               #=  TODO: Have annotation asserting that this is a switch-statement
               =#
              path = begin
                @match ident begin
                  "abs"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("abs"))
                  end

                  "acos"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("acos"))
                  end

                  "activeState"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("activeState"))
                  end

                  "actualStream"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("actualStream"))
                  end

                  "asin"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("asin"))
                  end

                  "atan"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("atan"))
                  end

                  "atan2"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("atan2"))
                  end

                  "backSample"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("backSample"))
                  end

                  "cardinality"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("cardinality"))
                  end

                  "cat"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("cat"))
                  end

                  "ceil"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("ceil"))
                  end

                  "change"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("change"))
                  end

                  "classDirectory"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("classDirectory"))
                  end

                  "constrain"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("constrain"))
                  end

                  "cos"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("cos"))
                  end

                  "cosh"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("cosh"))
                  end

                  "cross"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("cross"))
                  end

                  "delay"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("delay"))
                  end

                  "der"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("der"))
                  end

                  "diagonal"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("diagonal"))
                  end

                  "div"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("div"))
                  end

                  "edge"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("edge"))
                  end

                  "exp"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("exp"))
                  end

                  "fill"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("fill"))
                  end

                  "firstTick"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("firstTick"))
                  end

                  "floor"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("floor"))
                  end

                  "getInstanceName"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("getInstanceName"))
                  end

                  "hold"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("hold"))
                  end

                  "homotopy"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("homotopy"))
                  end

                  "identity"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("identity"))
                  end

                  "inStream"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("inStream"))
                  end

                  "initial"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("initial"))
                  end

                  "initialState"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("initialState"))
                  end

                  "integer"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("integer"))
                  end

                  "interval"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("interval"))
                  end

                  "intAbs"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("intAbs"))
                  end

                  "linspace"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("linspace"))
                  end

                  "log"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("log"))
                  end

                  "log10"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("log10"))
                  end

                  "matrix"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("matrix"))
                  end

                  "max"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("max"))
                  end

                  "min"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("min"))
                  end

                  "mod"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("mod"))
                  end

                  "ndims"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("ndims"))
                  end

                  "noClock"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("noClock"))
                  end

                  "noEvent"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("noEvent"))
                  end

                  "ones"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("ones"))
                  end

                  "outerProduct"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("outerProduct"))
                  end

                  "pre"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("pre"))
                  end

                  "previous"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("previous"))
                  end

                  "print"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("print"))
                  end

                  "product"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("product"))
                  end

                  "realAbs"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("realAbs"))
                  end

                  "rem"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("rem"))
                  end

                  "rooted"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("rooted"))
                  end

                  "sample"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("sample"))
                  end

                  "scalar"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("scalar"))
                  end

                  "semilinear"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("semilinear"))
                  end

                  "shiftSample"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("shiftSample"))
                  end

                  "sign"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("sign"))
                  end

                  "sin"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("sin"))
                  end

                  "sinh"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("sinh"))
                  end

                  "size"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("size"))
                  end

                  "skew"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("skew"))
                  end

                  "smooth"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("smooth"))
                  end

                  "spatialDistribution"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("spatialDistribution"))
                  end

                  "sqrt"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("sqrt"))
                  end

                  "subSample"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("subSample"))
                  end

                  "symmetric"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("symmetric"))
                  end

                  "tan"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("tan"))
                  end

                  "tanh"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("tanh"))
                  end

                  "terminal"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("terminal"))
                  end

                  "ticksInState"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("ticksInState"))
                  end

                  "timeInState"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("timeInState"))
                  end

                  "transition"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("transition"))
                  end

                  "transpose"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("transpose"))
                  end

                  "vector"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("vector"))
                  end

                  "zeros"  => begin
                    Absyn.FULLYQUALIFIED(Absyn.IDENT("zeros"))
                  end

                  _  => begin
                      begin
                        @match cachedPath begin
                          Absyn.IDENT("")  => begin
                            Absyn.IDENT(ident)
                          end

                          _  => begin
                              cachedPath
                          end
                        end
                      end
                  end
                end
              end
          path
        end

        function getCachedInstance(cache::FCore.Cache, env::FCore.Graph, name::String, ref::FCore.MMRef) ::Tuple{FCore.Cache, FCore.Graph}



              local cache_path::Absyn.Path
              local cls::SCode.Element
              local prefix::Prefix.PrefixType
              local prefix2::Prefix.PrefixType
              local env2::FCore.Graph
              local enc::SCode.Encapsulated
              local res::SCode.Restriction
              local inputs::InstHashTable.CachedInstItemInputs

              @match true = Flags.isSet(Flags.CACHE)
              @match FCore.CL(cls && SCode.CLASS(encapsulatedPrefix = enc, restriction = res), prefix) = FNode.refData(ref)
              env2 = FGraphUtil.openScope(env, enc, name, FGraphUtil.restrictionToScopeType(res))
              try
                cache_path = generateCachePath(env2, cls, prefix, InstTypes.INNER_CALL())
                @match SOME(InstHashTable.FUNC_instClassIn(inputs, (env, _, _, _, _, _, _, _, _))) <| _ <| nil = InstHashTable.get(cache_path)
                (_, prefix2, _, _, _, _, _, _, _) = inputs
                @match true = PrefixUtil.isPrefix(prefix) && PrefixUtil.isPrefix(prefix2)
              catch ex
                println("no inst cache: ")
                showerror(stderr, ex, catch_backtrace())
                env = FGraphUtil.pushScopeRef(env, ref)
              end
          (cache, env)
        end

        function generateCachePath(env::FCore.Graph, cls::SCode.Element, prefix::Prefix.PrefixType, callScope::InstTypes.CallingScope) ::Absyn.Path
              local cachePath::Absyn.Path

              local name::String

              name = StringUtil.stringAppend9(InstTypes.callingScopeStr(callScope), "", SCodeDump.restrString(SCodeUtil.getClassRestriction(cls)), "", generatePrefixStr(prefix), "")
              cachePath = AbsynUtil.joinPaths(Absyn.IDENT(name), FGraphUtil.getGraphName(env))
          cachePath
        end

        function generatePrefixStr(inPrefix::Prefix.PrefixType) ::String
              local str::String

              try
                str = AbsynUtil.pathString(PrefixUtil.prefixToPath(inPrefix), "", usefq = false, reverse = true)
              catch
                str = ""
              end
          str
        end

        function showCacheInfo(inMsg::String, inPath::Absyn.Path)
              if Flags.isSet(Flags.SHOW_INST_CACHE_INFO)
                print(inMsg + AbsynUtil.pathString(inPath) + "\\n")
              end
        end

         #= myMerges the function's comments from inherited classes =#
        function instFunctionAnnotations(comments::List{<:SCode.Comment}, state::ClassInf.SMNode) ::DAE.DAElist
              local dae::DAE.DAElist = DAE.emptyDae

              local comment::Option{String} = NONE()
              local mod::SCode.Mod = SCode.NOMOD()
              local mod2::SCode.Mod

              if ! ClassInf.isFunction(state)
                return dae
              end
              for cmt in comments
                if isNone(comment)
                  comment = cmt.comment
                end
                mod = begin
                  @match cmt begin
                    SCode.COMMENT(annotation_ = SOME(SCode.ANNOTATION(modification = mod2)))  => begin
                      SCodeUtil.mergeModifiers(mod2, mod)
                    end

                    _  => begin
                        mod
                    end
                  end
                end
              end
              dae = begin
                @match mod begin
                  SCode.NOMOD(__)  => begin
                    if isNone(comment)
                          dae
                        else
                          DAE.DAE_LIST(list(DAE.COMMENT(SCode.COMMENT(NONE(), comment))))
                        end
                  end

                  _  => begin
                      DAE.DAE_LIST(list(DAE.COMMENT(SCode.COMMENT(SOME(SCode.ANNOTATION(mod)), comment))))
                  end
                end
              end
          dae
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

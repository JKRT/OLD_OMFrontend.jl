  module InstExtends 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    getIdentFn = Function

    FixAFn = Function

    FixAFn = Function

    FixAFn = Function

    FixAFn = Function
    FixBFn = Function

    FixAFn = Function
    FixBFn = Function

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

        import DAE

        import FCore

        import InnerOuter

        import SCode

        import Prefix
         #=  protected imports
         =#

        import AvlSetString

        import Debug

        import Dump

        import Error

        import Flags

        import FGraph

        import Inst

        import InstUtil

        import ListUtil

        import Lookup

        import Mod

        import Util

        import SCodeDump
        import SCodeInstUtil
        import SCodeUtil

        import ErrorExt

        import AbsynToSCode

        import Global
         #= protected import System;
         =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

         #= This function flattens out the inheritance structure of a class. It takes an
           SCode.Element list and flattens out the extends nodes of that list. The
           result is a list of components and lists of equations and algorithms. =#
        function instExtendsList(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.Prefix, inLocalElements::List{<:SCode.Element}, inElementsFromExtendsScope::List{<:SCode.Element}, inState::ClassInf.State, inClassName::String #= The class whose elements are getting instantiated =#, inImpl::Bool, inPartialInst::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Mod, List{Tuple{SCode.Element, DAE.Mod, Bool}}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}, List{SCode.Comment}} 
              local outComments::List{SCode.Comment} = nil
              local outInitialAlgs::List{SCode.AlgorithmSection} = nil
              local outNormalAlgs::List{SCode.AlgorithmSection} = nil
              local outInitialEqs::List{SCode.Equation} = nil
              local outNormalEqs::List{SCode.Equation} = nil
              local outElements::List{Tuple{SCode.Element, DAE.Mod, Bool}} = nil
              local outMod::DAE.Mod = inMod
              local outIH::InnerOuter.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              for el in listReverse(inLocalElements)
                _ = begin
                    local cn::String
                    local bc_str::String
                    local scope_str::String
                    local base_first_id::String
                    local emod::SCode.Mod
                    local eq_name::Bool
                    local ocls::Option{SCode.Element}
                    local cls::SCode.Element
                    local cenv::FCore.Graph
                    local encf::SCode.Encapsulated
                    local r::SCode.Restriction
                    local els1::List{SCode.Element}
                    local rest_els::List{SCode.Element}
                    local import_els::List{SCode.Element}
                    local cdef_els::List{SCode.Element}
                    local clsext_els::List{SCode.Element}
                    local els2::List{Tuple{SCode.Element, DAE.Mod, Bool}}
                    local eq1::List{SCode.Equation}
                    local ieq1::List{SCode.Equation}
                    local eq2::List{SCode.Equation}
                    local ieq2::List{SCode.Equation}
                    local alg1::List{SCode.AlgorithmSection}
                    local ialg1::List{SCode.AlgorithmSection}
                    local alg2::List{SCode.AlgorithmSection}
                    local ialg2::List{SCode.AlgorithmSection}
                    local comments1::List{SCode.Comment}
                    local comments2::List{SCode.Comment}
                    local cmt::SCode.Comment
                    local mod::DAE.Mod
                    local tree::AvlSetString.Tree
                    local cacheArr::Array{FCore.Cache}
                    local htHasEntries::Bool
                     #=  Instantiate a basic type base class.
                     =#
                  @matchcontinue el begin
                    SCode.EXTENDS(__)  => begin
                        @match Absyn.IDENT(cn) = AbsynUtil.makeNotFullyQualified(el.baseClassPath)
                        @match true = InstUtil.isBuiltInClass(cn)
                      ()
                    end
                    
                    SCode.EXTENDS(__)  => begin
                         #=  Instantiate a base class.
                         =#
                        emod = InstUtil.chainRedeclares(outMod, el.modifications)
                         #=  Check if the extends is referencing the class we're instantiating.
                         =#
                        base_first_id = AbsynUtil.pathFirstIdent(el.baseClassPath)
                        eq_name = stringEq(inClassName, base_first_id) && AbsynUtil.pathEqual(ClassInf.getStateName(inState), AbsynUtil.joinPaths(FGraph.getGraphName(outEnv), AbsynUtil.makeIdentPathFromString(base_first_id)))
                         #=  Look up the base class.
                         =#
                        (outCache, ocls, cenv) = lookupBaseClass(el.baseClassPath, eq_name, inClassName, outEnv, outCache)
                        if isSome(ocls)
                          @match SOME(cls) = ocls
                          @match SCode.CLASS(name = cn, encapsulatedPrefix = encf, cmt = cmt) = cls
                        else
                          if Flags.getConfigBool(Flags.PERMISSIVE)
                            bc_str = AbsynUtil.pathString(el.baseClassPath)
                            scope_str = FGraph.printGraphPathStr(inEnv)
                            Error.addSourceMessage(Error.LOOKUP_BASECLASS_ERROR, list(bc_str, scope_str), el.info)
                          end
                          fail()
                        end
                         #=  Base class could not be found, print an error unless --permissive
                         =#
                         #=  is used.
                         =#
                        (outCache, cenv, outIH, els1, eq1, ieq1, alg1, ialg1, mod, comments1) = instDerivedClasses(outCache, cenv, outIH, outMod, inPrefix, cls, inImpl, el.info)
                        els1 = updateElementListVisibility(els1, el.visibility)
                         #=  Build a set with the constant elements from the extends scope.
                         =#
                        tree = AvlSetString.new()
                        tree = getLocalIdentList(InstUtil.constantAndParameterEls(inElementsFromExtendsScope), tree, getLocalIdentElement)
                        tree = getLocalIdentList(InstUtil.constantAndParameterEls(els1), tree, getLocalIdentElement)
                         #=  Fully qualify modifiers in extends in the extends environment.
                         =#
                        cacheArr = arrayCreate(1, outCache)
                        emod = fixModifications(cacheArr, inEnv, emod, tree)
                        cenv = FGraph.openScope(cenv, encf, cn, FGraph.classInfToScopeType(inState))
                         #=  Add classdefs and imports to env, so e.g. imports from baseclasses can be found.
                         =#
                        (import_els, cdef_els, clsext_els, rest_els) = InstUtil.splitEltsNoComponents(els1)
                        (outCache, cenv, outIH) = InstUtil.addClassdefsToEnv(outCache, cenv, outIH, inPrefix, import_els, inImpl, NONE())
                        (outCache, cenv, outIH) = InstUtil.addClassdefsToEnv(outCache, cenv, outIH, inPrefix, cdef_els, inImpl, SOME(mod))
                        rest_els = SCodeInstUtil.addRedeclareAsElementsToExtends(rest_els, list(e for e in rest_els if SCodeUtil.isRedeclareElement(e)))
                        outMod = Mod.elabUntypedMod(emod, Mod.EXTENDS(el.baseClassPath))
                        outMod = Mod.merge(mod, outMod, "", false)
                        (outCache, _, outIH, _, els2, eq2, ieq2, alg2, ialg2, comments2) = instExtendsAndClassExtendsList2(outCache, cenv, outIH, outMod, inPrefix, rest_els, clsext_els, els1, inState, inClassName, inImpl, inPartialInst)
                        tree = AvlSetString.new()
                        tree = getLocalIdentList(els2, tree, getLocalIdentElementTpl)
                        tree = getLocalIdentList(cdef_els, tree, getLocalIdentElement)
                        tree = getLocalIdentList(import_els, tree, getLocalIdentElement)
                        htHasEntries = ! AvlSetString.isEmpty(tree)
                        arrayUpdate(cacheArr, 1, outCache)
                        if htHasEntries
                          els2 = fixList(cacheArr, cenv, els2, tree, fixLocalIdent)
                        end
                         #=  Update components with new merged modifiers.
                         =#
                         #= (els2, outMod) := updateComponentsAndClassdefs(els2, outMod, inEnv);
                         =#
                        outElements = listAppend(els2, outElements)
                        outNormalEqs = ListUtil.unionAppendListOnTrue(listReverse(eq2), outNormalEqs, valueEq)
                        outInitialEqs = ListUtil.unionAppendListOnTrue(listReverse(ieq2), outInitialEqs, valueEq)
                        outNormalAlgs = ListUtil.unionAppendListOnTrue(listReverse(alg2), outNormalAlgs, valueEq)
                        outInitialAlgs = ListUtil.unionAppendListOnTrue(listReverse(ialg2), outInitialAlgs, valueEq)
                        outComments = listAppend(comments1, listAppend(comments2, _cons(cmt, outComments)))
                        if ! inPartialInst
                          if htHasEntries
                            eq1 = fixList(cacheArr, cenv, eq1, tree, fixEquation)
                            ieq1 = fixList(cacheArr, cenv, ieq1, tree, fixEquation)
                            alg1 = fixList(cacheArr, cenv, alg1, tree, fixAlgorithm)
                            ialg1 = fixList(cacheArr, cenv, ialg1, tree, fixAlgorithm)
                          end
                          outNormalEqs = ListUtil.unionAppendListOnTrue(listReverse(eq1), outNormalEqs, valueEq)
                          outInitialEqs = ListUtil.unionAppendListOnTrue(listReverse(ieq1), outInitialEqs, valueEq)
                          outNormalAlgs = ListUtil.unionAppendListOnTrue(listReverse(alg1), outNormalAlgs, valueEq)
                          outInitialAlgs = ListUtil.unionAppendListOnTrue(listReverse(ialg1), outInitialAlgs, valueEq)
                        end
                        outCache = arrayGet(cacheArr, 1)
                      ()
                    end
                    
                    SCode.EXTENDS(__) where (Flags.getConfigBool(Flags.PERMISSIVE))  => begin
                      ()
                    end
                    
                    SCode.COMPONENT(__)  => begin
                         #=  Skip any extends we couldn't handle if --permissive is given.
                         =#
                         #=  Keep only constants if partial inst, otherwise keep all components.
                         =#
                        if SCodeUtil.isConstant(SCodeUtil.attrVariability(el.attributes)) || ! inPartialInst
                          outElements = _cons((el, DAE.NOMOD(), false), outElements)
                        end
                      ()
                    end
                    
                    SCode.CLASS(__)  => begin
                        outElements = _cons((el, DAE.NOMOD(), false), outElements)
                        outComments = list(el.cmt)
                      ()
                    end
                    
                    SCode.IMPORT(__)  => begin
                        outElements = _cons((el, DAE.NOMOD(), false), outElements)
                      ()
                    end
                    
                    _  => begin
                          @match true = Flags.isSet(Flags.FAILTRACE)
                          Debug.traceln("- Inst.instExtendsList failed on:\\n\\t" + "className: " + inClassName + "\\n\\t" + "env:       " + FGraph.printGraphPathStr(outEnv) + "\\n\\t" + "mods:      " + Mod.printModStr(outMod) + "\\n\\t" + "elem:      " + SCodeDump.unparseElementStr(el))
                        fail()
                    end
                  end
                end
              end
               #=  Instantiation failed.
               =#
              (outElements, outMod) = updateComponentsAndClassdefs(outElements, outMod, inEnv)
          (outCache, outEnv, outIH, outMod, outElements, outNormalEqs, outInitialEqs, outNormalAlgs, outInitialAlgs, outComments)
        end

         #= Looks up a base class used in an extends clause. =#
        function lookupBaseClass(inPath::Absyn.Path, inSelfReference::Bool, inClassName::String, inEnv::FCore.Graph, inCache::FCore.Cache) ::Tuple{FCore.Cache, Option{SCode.Element}, FCore.Graph} 
              local outEnv::FCore.Graph
              local outElement::Option{SCode.Element}
              local outCache::FCore.Cache

              (outCache, outElement, outEnv) = begin
                  local name::String
                  local elem::SCode.Element
                  local env::FCore.Graph
                  local cache::FCore.Cache
                  local path::Absyn.Path
                   #=  We have a simple identifier with a self reference, i.e. a class which
                   =#
                   #=  extends a base class with the same name. The only legal situation in this
                   =#
                   #=  case is when extending a local class with the same name, e.g.:
                   =#
                   #= 
                   =#
                   #=    class A
                   =#
                   #=      extends A;
                   =#
                   #=      class A end A;
                   =#
                   #=    end A;
                   =#
                @match (inPath, inSelfReference) begin
                  (Absyn.IDENT(name), true)  => begin
                      (elem, env) = Lookup.lookupClassLocal(inEnv, name)
                    (inCache, SOME(elem), env)
                  end
                  
                  (_, _)  => begin
                      path = AbsynUtil.removePartialPrefix(Absyn.IDENT(inClassName), inPath)
                      (cache, elem, env) = Lookup.lookupClass(inCache, inEnv, path)
                    (cache, SOME(elem), env)
                  end
                  
                  _  => begin
                      (inCache, NONE(), inEnv)
                  end
                end
              end
               #=  Only look the name up locally, otherwise we might get an infinite
               =#
               #=  loop if the class extends itself.
               =#
               #=  Otherwise, remove the first identifier if it's the same as the class name
               =#
               #=  and look it up as normal.
               =#
          (outCache, outElement, outEnv)
        end

        function updateElementListVisibility(inElements::List{<:SCode.Element}, inVisibility::SCode.Visibility) ::List{SCode.Element} 
              local outElements::List{SCode.Element}

              outElements = begin
                @match inVisibility begin
                  SCode.PUBLIC(__)  => begin
                    inElements
                  end
                  
                  _  => begin
                      list(SCodeUtil.makeElementProtected(e) for e in inElements)
                  end
                end
              end
          outElements
        end

         #= 
          This function flattens out the inheritance structure of a class.
          It takes an SCode.Element list and flattens out the extends nodes and
          class extends nodes of that list. The result is a list of components and
          lists of equations and algorithms. =#
        function instExtendsAndClassExtendsList(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.Prefix, inExtendsElementLst::List{<:SCode.Element}, inClassExtendsElementLst::List{<:SCode.Element}, inElementsFromExtendsScope::List{<:SCode.Element}, inState::ClassInf.State, inClassName::String, inImpl::Bool, isPartialInst::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Mod, List{Tuple{SCode.Element, DAE.Mod}}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}, List{SCode.Comment}} 
              local outComments::List{SCode.Comment}
              local outInitialAlgs::List{SCode.AlgorithmSection}
              local outNormalAlgs::List{SCode.AlgorithmSection}
              local outInitialEqs::List{SCode.Equation}
              local outNormalEqs::List{SCode.Equation}
              local outElements::List{Tuple{SCode.Element, DAE.Mod}}
              local outMod::DAE.Mod
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local elts::List{Tuple{SCode.Element, DAE.Mod, Bool}}
              local cdefelts::List{SCode.Element}
              local tmpelts::List{SCode.Element}
              local extendselts::List{SCode.Element}

              extendselts = ListUtil.map(inExtendsElementLst, SCodeInstUtil.expandEnumerationClass)
               #= fprintln(Flags.DEBUG,\"instExtendsAndClassExtendsList: \" + inClassName);
               =#
              (outCache, outEnv, outIH, outMod, elts, outNormalEqs, outInitialEqs, outNormalAlgs, outInitialAlgs, outComments) = instExtendsAndClassExtendsList2(inCache, inEnv, inIH, inMod, inPrefix, extendselts, inClassExtendsElementLst, inElementsFromExtendsScope, inState, inClassName, inImpl, isPartialInst)
               #=  Filter out the last boolean in the tuple
               =#
              outElements = ListUtil.map(elts, Util.tuple312)
               #=  Create a list of the class definitions, since these can't be properly added in the recursive call
               =#
              tmpelts = ListUtil.map(outElements, Util.tuple21)
              (_, cdefelts, _, _) = InstUtil.splitEltsNoComponents(tmpelts)
               #=  Add the class definitions to the environment
               =#
              (outCache, outEnv, outIH) = InstUtil.addClassdefsToEnv(outCache, outEnv, outIH, inPrefix, cdefelts, inImpl, SOME(outMod))
               #= fprintln(Flags.DEBUG,\"instExtendsAndClassExtendsList: \" + inClassName + \" done\");
               =#
          (outCache, outEnv, outIH, outMod, outElements, outNormalEqs, outInitialEqs, outNormalAlgs, outInitialAlgs, outComments)
        end

         #= 
          This function flattens out the inheritance structure of a class.
          It takes an SCode.Element list and flattens out the extends nodes and
          class extends nodes of that list. The result is a list of components and
          lists of equations and algorithms. =#
        function instExtendsAndClassExtendsList2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.Prefix, inExtendsElementLst::List{<:SCode.Element}, inClassExtendsElementLst::List{<:SCode.Element}, inElementsFromExtendsScope::List{<:SCode.Element}, inState::ClassInf.State, inClassName::String, inImpl::Bool, isPartialInst::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Mod, List{Tuple{SCode.Element, DAE.Mod, Bool}}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}, List{SCode.Comment}} 
              local comments::List{SCode.Comment}
              local outInitialAlgs::List{SCode.AlgorithmSection}
              local outNormalAlgs::List{SCode.AlgorithmSection}
              local outInitialEqs::List{SCode.Equation}
              local outNormalEqs::List{SCode.Equation}
              local outElements::List{Tuple{SCode.Element, DAE.Mod, Bool}}
              local outMod::DAE.Mod
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outMod, outElements, outNormalEqs, outInitialEqs, outNormalAlgs, outInitialAlgs, comments) = instExtendsList(inCache, inEnv, inIH, inMod, inPrefix, inExtendsElementLst, inElementsFromExtendsScope, inState, inClassName, inImpl, isPartialInst)
              (outMod, outElements) = instClassExtendsList(inEnv, outMod, inClassExtendsElementLst, outElements)
          (outCache, outEnv, outIH, outMod, outElements, outNormalEqs, outInitialEqs, outNormalAlgs, outInitialAlgs, comments)
        end

         #= Instantiate element nodes of type SCode.CLASS_EXTENDS. This is done by walking
        the extended classes and performing the modifications in-place. The old class
        will no longer be accessible. =#
        function instClassExtendsList(inEnv::FCore.Graph, inMod::DAE.Mod, inClassExtendsList::List{<:SCode.Element}, inElements::List{<:Tuple{<:SCode.Element, DAE.Mod, Bool}}) ::Tuple{DAE.Mod, List{Tuple{SCode.Element, DAE.Mod, Bool}}} 
              local outElements::List{Tuple{SCode.Element, DAE.Mod, Bool}}
              local outMod::DAE.Mod

              (outMod, outElements) = begin
                  local first::SCode.Element
                  local rest::List{SCode.Element}
                  local name::String
                  local els::List{SCode.Element}
                  local compelts::List{Tuple{SCode.Element, DAE.Mod, Bool}}
                  local emod::DAE.Mod
                  local names::List{String}
                @matchcontinue (inMod, inClassExtendsList, inElements) begin
                  (emod,  nil(), compelts)  => begin
                    (emod, compelts)
                  end
                  
                  (emod, first && SCode.CLASS(name = name) <| rest, compelts)  => begin
                      (emod, compelts) = instClassExtendsList2(inEnv, emod, name, first, compelts)
                      (emod, compelts) = instClassExtendsList(inEnv, emod, rest, compelts)
                    (emod, compelts)
                  end
                  
                  (_, SCode.CLASS(name = name) <| _, compelts)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.instClassExtendsList failed " + name)
                      Debug.traceln("  Candidate classes: ")
                      els = ListUtil.map(compelts, Util.tuple31)
                      names = ListUtil.map(els, SCodeUtil.elementName)
                      Debug.traceln(stringDelimitList(names, ","))
                    fail()
                  end
                end
              end
          (outMod, outElements)
        end

        function buildClassExtendsName(inEnvPath::String, inClassName::String) ::String 
              local outClassName::String

              outClassName = "parent." + inClassName + ".env." + inEnvPath
          outClassName
        end

        function instClassExtendsList2(inEnv::FCore.Graph, inMod::DAE.Mod, inName::String, inClassExtendsElt::SCode.Element, inElements::List{<:Tuple{<:SCode.Element, DAE.Mod, Bool}}) ::Tuple{DAE.Mod, List{Tuple{SCode.Element, DAE.Mod, Bool}}} 
              local outElements::List{Tuple{SCode.Element, DAE.Mod, Bool}}
              local outMod::DAE.Mod

              (outMod, outElements) = begin
                  local elt::SCode.Element
                  local compelt::SCode.Element
                  local classExtendsElt::SCode.Element
                  local cl::SCode.Element
                  local classDef::SCode.ClassDef
                  local classExtendsCdef::SCode.ClassDef
                  local partialPrefix1::SCode.Partial
                  local partialPrefix2::SCode.Partial
                  local encapsulatedPrefix1::SCode.Encapsulated
                  local encapsulatedPrefix2::SCode.Encapsulated
                  local restriction1::SCode.Restriction
                  local restriction2::SCode.Restriction
                  local prefixes1::SCode.Prefixes
                  local prefixes2::SCode.Prefixes
                  local vis2::SCode.Visibility
                  local name1::String
                  local name2::String
                  local env_path::String
                  local externalDecl1::Option{SCode.ExternalDecl}
                  local externalDecl2::Option{SCode.ExternalDecl}
                  local annotationLst1::List{SCode.Annotation}
                  local annotationLst2::List{SCode.Annotation}
                  local comment1::SCode.Comment
                  local comment2::SCode.Comment
                  local ann1::Option{SCode.Annotation}
                  local ann2::Option{SCode.Annotation}
                  local els1::List{SCode.Element}
                  local els2::List{SCode.Element}
                  local nEqn1::List{SCode.Equation}
                  local nEqn2::List{SCode.Equation}
                  local inEqn1::List{SCode.Equation}
                  local inEqn2::List{SCode.Equation}
                  local nAlg1::List{SCode.AlgorithmSection}
                  local nAlg2::List{SCode.AlgorithmSection}
                  local inAlg1::List{SCode.AlgorithmSection}
                  local inAlg2::List{SCode.AlgorithmSection}
                  local inCons1::List{SCode.ConstraintSection}
                  local inCons2::List{SCode.ConstraintSection}
                  local clats::List{Absyn.NamedArg}
                  local rest::List{Tuple{SCode.Element, DAE.Mod, Bool}}
                  local first::Tuple{SCode.Element, DAE.Mod, Bool}
                  local mods::SCode.Mod
                  local derivedMod::SCode.Mod
                  local mod1::DAE.Mod
                  local emod::DAE.Mod
                  local info1::SourceInfo
                  local info2::SourceInfo
                  local b::Bool
                  local attrs::SCode.Attributes
                  local derivedTySpec::Absyn.TypeSpec
                   #=  found the base class with parts
                   =#
                @matchcontinue (inMod, inName, inClassExtendsElt, inElements) begin
                  (emod, name1, classExtendsElt, (cl && SCode.CLASS(name = name2, classDef = SCode.PARTS(__)), mod1, b) <| rest)  => begin
                      @match true = name1 == name2
                      env_path = AbsynUtil.pathString(FGraph.getGraphName(inEnv))
                      name2 = buildClassExtendsName(env_path, name2)
                      @match SCode.CLASS(_, prefixes2, encapsulatedPrefix2, partialPrefix2, restriction2, SCode.PARTS(els2, nEqn2, inEqn2, nAlg2, inAlg2, inCons2, clats, externalDecl2), comment2, info2) = cl
                      @match SCode.CLASS(_, prefixes1, encapsulatedPrefix1, partialPrefix1, restriction1, classExtendsCdef, comment1, info1) = classExtendsElt
                      @match SCode.CLASS_EXTENDS(mods, SCode.PARTS(els1, nEqn1, inEqn1, nAlg1, inAlg1, inCons1, _, externalDecl1)) = classExtendsCdef
                      classDef = SCode.PARTS(els2, nEqn2, inEqn2, nAlg2, inAlg2, inCons2, clats, externalDecl2)
                      compelt = SCode.CLASS(name2, prefixes2, encapsulatedPrefix2, partialPrefix2, restriction2, classDef, comment2, info2)
                      vis2 = SCodeUtil.prefixesVisibility(prefixes2)
                      elt = SCode.EXTENDS(Absyn.IDENT(name2), vis2, mods, NONE(), info1)
                      classDef = SCode.PARTS(_cons(elt, els1), nEqn1, inEqn1, nAlg1, inAlg1, inCons1, clats, externalDecl1)
                      elt = SCode.CLASS(name1, prefixes1, encapsulatedPrefix1, partialPrefix1, restriction1, classDef, comment1, info1)
                      emod = Mod.renameTopLevelNamedSubMod(emod, name1, name2)
                    (emod, _cons((compelt, mod1, b), _cons((elt, DAE.NOMOD(), true), rest)))
                  end
                  
                  (emod, name1, classExtendsElt, (cl && SCode.CLASS(name = name2, classDef = SCode.DERIVED(__)), mod1, b) <| rest)  => begin
                      @match true = name1 == name2
                      env_path = AbsynUtil.pathString(FGraph.getGraphName(inEnv))
                      name2 = buildClassExtendsName(env_path, name2)
                      @match SCode.CLASS(_, prefixes2, encapsulatedPrefix2, partialPrefix2, restriction2, SCode.DERIVED(derivedTySpec, derivedMod, attrs), comment2, info2) = cl
                      @match SCode.CLASS(_, prefixes1, encapsulatedPrefix1, partialPrefix1, restriction1, classExtendsCdef, comment1, info1) = classExtendsElt
                      @match SCode.CLASS_EXTENDS(mods, SCode.PARTS(els1, nEqn1, inEqn1, nAlg1, inAlg1, inCons1, _, externalDecl1)) = classExtendsCdef
                      classDef = SCode.DERIVED(derivedTySpec, derivedMod, attrs)
                      compelt = SCode.CLASS(name2, prefixes2, encapsulatedPrefix2, partialPrefix2, restriction2, classDef, comment2, info2)
                      vis2 = SCodeUtil.prefixesVisibility(prefixes2)
                      elt = SCode.EXTENDS(Absyn.IDENT(name2), vis2, mods, NONE(), info1)
                      classDef = SCode.PARTS(_cons(elt, els1), nEqn1, inEqn1, nAlg1, inAlg1, inCons1, nil, externalDecl1)
                      elt = SCode.CLASS(name1, prefixes1, encapsulatedPrefix1, partialPrefix1, restriction1, classDef, comment1, info1)
                      emod = Mod.renameTopLevelNamedSubMod(emod, name1, name2)
                    (emod, _cons((compelt, mod1, b), _cons((elt, DAE.NOMOD(), true), rest)))
                  end
                  
                  (emod, name1, classExtendsElt, first <| rest)  => begin
                      (emod, rest) = instClassExtendsList2(inEnv, emod, name1, classExtendsElt, rest)
                    (emod, _cons(first, rest))
                  end
                  
                  (_, _, _,  nil())  => begin
                      Debug.traceln("TODO: Make a proper Error message here - Inst.instClassExtendsList2 couldn't find the class to extend")
                    fail()
                  end
                end
              end
               #=  Compare the name before pattern-matching to speed this up
               =#
               #= Debug.traceln(\"class extends: \" + SCodeDump.unparseElementStr(compelt) + \"  \" + SCodeDump.unparseElementStr(elt));
               =#
               #=  found the base class which is derived
               =#
               #=  Compare the name before pattern-matching to speed this up
               =#
               #= Debug.traceln(\"class extends: \" + SCodeDump.unparseElementStr(compelt) + \"  \" + SCodeDump.unparseElementStr(elt));
               =#
               #=  not this one, switch to next one
               =#
               #=  bah, we did not find it
               =#
          (outMod, outElements)
        end

         #= author: PA
          This function takes a class definition and returns the
          elements and equations and algorithms of the class.
          If the class is derived, the class is looked up and the
          derived class parts are fetched. =#
        function instDerivedClasses(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.Prefix, inClass::SCode.Element, inBoolean::Bool, inInfo::SourceInfo #= File information of the extends element =#) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, List{SCode.Element}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}, DAE.Mod, List{SCode.Comment}} 
              local outComments::List{SCode.Comment}
              local outMod::DAE.Mod
              local outSCodeAlgorithmLst6::List{SCode.AlgorithmSection}
              local outSCodeAlgorithmLst5::List{SCode.AlgorithmSection}
              local outSCodeEquationLst4::List{SCode.Equation}
              local outSCodeEquationLst3::List{SCode.Equation}
              local outSCodeElementLst2::List{SCode.Element}
              local outIH::InnerOuter.InstHierarchy
              local outEnv1::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv1, outIH, outSCodeElementLst2, outSCodeEquationLst3, outSCodeEquationLst4, outSCodeAlgorithmLst5, outSCodeAlgorithmLst6, outMod, outComments) = instDerivedClassesWork(inCache, inEnv, inIH, inMod, inPrefix, inClass, inBoolean, inInfo, false, 0)
          (outCache, outEnv1, outIH, outSCodeElementLst2, outSCodeEquationLst3, outSCodeEquationLst4, outSCodeAlgorithmLst5, outSCodeAlgorithmLst6, outMod, outComments)
        end

         #= author: PA
          This function takes a class definition and returns the
          elements and equations and algorithms of the class.
          If the class is derived, the class is looked up and the
          derived class parts are fetched. =#
        function instDerivedClassesWork(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inMod::DAE.Mod, inPrefix::Prefix.Prefix, inClass::SCode.Element, inBoolean::Bool, inInfo::SourceInfo #= File information of the extends element =#, overflow::Bool, numIter::ModelicaInteger) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, List{SCode.Element}, List{SCode.Equation}, List{SCode.Equation}, List{SCode.AlgorithmSection}, List{SCode.AlgorithmSection}, DAE.Mod, List{SCode.Comment}} 
              local outComments::List{SCode.Comment}
              local outMod::DAE.Mod
              local outSCodeAlgorithmLst6::List{SCode.AlgorithmSection}
              local outSCodeAlgorithmLst5::List{SCode.AlgorithmSection}
              local outSCodeEquationLst4::List{SCode.Equation}
              local outSCodeEquationLst3::List{SCode.Equation}
              local outSCodeElementLst2::List{SCode.Element}
              local outIH::InnerOuter.InstHierarchy
              local outEnv1::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv1, outIH, outSCodeElementLst2, outSCodeEquationLst3, outSCodeEquationLst4, outSCodeAlgorithmLst5, outSCodeAlgorithmLst6, outMod, outComments) = begin
                  local elt::List{SCode.Element}
                  local env::FCore.Graph
                  local cenv::FCore.Graph
                  local mod::DAE.Mod
                  local daeDMOD::DAE.Mod
                  local eq::List{SCode.Equation}
                  local ieq::List{SCode.Equation}
                  local alg::List{SCode.AlgorithmSection}
                  local ialg::List{SCode.AlgorithmSection}
                  local c::SCode.Element
                  local tp::Absyn.Path
                  local dmod::SCode.Mod
                  local impl::Bool
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local cmt::SCode.Comment
                  local enumLst::List{SCode.Enum}
                  local n::String
                  local name::String
                  local str1::String
                  local str2::String
                  local strDepth::String
                  local cn::String
                  local extdecl::Option{SCode.ExternalDecl}
                  local pre::Prefix.Prefix
                  local info::SourceInfo
                  local prefixes::SCode.Prefixes
                   #=  from basic types return nothing
                   =#
                @matchcontinue (inCache, inEnv, inIH, inMod, inPrefix, inClass, inBoolean, inInfo, overflow) begin
                  (cache, env, ih, _, _, SCode.CLASS(name = name), _, _, _)  => begin
                      @match true = InstUtil.isBuiltInClass(name)
                    (cache, env, ih, nil, nil, nil, nil, nil, inMod, nil)
                  end
                  
                  (cache, env, ih, _, _, SCode.CLASS(name = name, classDef = SCode.PARTS(elementLst = elt, normalEquationLst = eq, initialEquationLst = ieq, normalAlgorithmLst = alg, initialAlgorithmLst = ialg, externalDecl = extdecl)), _, info, _)  => begin
                      Error.assertionOrAddSourceMessage(Util.isNone(extdecl), Error.EXTENDS_EXTERNAL, list(name), info)
                    (cache, env, ih, elt, eq, ieq, alg, ialg, inMod, list(inClass.cmt))
                  end
                  
                  (cache, env, ih, mod, pre, SCode.CLASS(info = info, classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(tp, _), modifications = dmod)), impl, _, false)  => begin
                      (cache, c, cenv) = Lookup.lookupClass(cache, env, tp, SOME(info))
                      dmod = InstUtil.chainRedeclares(mod, dmod)
                      (cache, daeDMOD) = Mod.elabMod(cache, env, ih, pre, dmod, impl, Mod.DERIVED(tp), info)
                      mod = Mod.merge(mod, daeDMOD)
                      (cache, env, ih, elt, eq, ieq, alg, ialg, mod, outComments) = instDerivedClassesWork(cache, cenv, ih, mod, pre, c, impl, info, numIter >= Global.recursionDepthLimit, numIter + 1) #= Mod.lookup_modification_p(mod, c) => innermod & We have to merge and apply modifications as well! =#
                    (cache, env, ih, elt, eq, ieq, alg, ialg, mod, _cons(inClass.cmt, outComments))
                  end
                  
                  (cache, env, ih, mod, pre, SCode.CLASS(name = n, prefixes = prefixes, classDef = SCode.ENUMERATION(enumLst), cmt = cmt, info = info), impl, _, false)  => begin
                      c = SCodeInstUtil.expandEnumeration(n, enumLst, prefixes, cmt, info)
                      (cache, env, ih, elt, eq, ieq, alg, ialg, mod, outComments) = instDerivedClassesWork(cache, env, ih, mod, pre, c, impl, info, numIter >= Global.recursionDepthLimit, numIter + 1)
                    (cache, env, ih, elt, eq, ieq, alg, ialg, mod, outComments)
                  end
                  
                  (_, _, _, _, _, _, _, _, true)  => begin
                      str1 = SCodeDump.unparseElementStr(inClass, SCodeDump.defaultOptions)
                      str2 = FGraph.printGraphPathStr(inEnv)
                      Error.addSourceMessage(Error.RECURSION_DEPTH_DERIVED, list(str1, str2), inInfo)
                    fail()
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Inst.instDerivedClasses failed\\n")
                      fail()
                  end
                end
              end
               #= /* elt_1 = noImportElements(elt); */ =#
               #=  fprintln(Flags.INST_TRACE, \"DERIVED: \" + FGraph.printGraphPathStr(env) + \" el: \" + SCodeDump.unparseElementStr(inClass) + \" mods: \" + Mod.printModStr(mod));
               =#
               #=  false = AbsynUtil.pathEqual(FGraph.getGraphName(env),FGraph.getGraphName(cenv)) and SCodeUtil.elementEqual(c,inClass);
               =#
               #=  modifiers should be evaluated in the current scope for derived!
               =#
               #= daeDMOD = Mod.elabUntypedMod(dmod, Mod.DERIVED(tp));
               =#
               #=  print(\"DER: \" + SCodeDump.unparseElementStr(inClass, SCodeDump.defaultOptions) + \"\\n\");
               =#
               #=  print(\"instDerivedClassesWork recursion depth... \" + str1 + \" \" + str2 + \"\\n\");
               =#
          (outCache, outEnv1, outIH, outSCodeElementLst2, outSCodeEquationLst3, outSCodeEquationLst4, outSCodeAlgorithmLst5, outSCodeAlgorithmLst6, outMod, outComments)
        end

         #= Returns all elements except imports, i.e. filter out import elements. =#
        function noImportElements(inElements::List{<:SCode.Element}) ::List{SCode.Element} 
              local outElements::List{SCode.Element}

              outElements = list(e for e in inElements if ! SCodeUtil.elementIsImport(e))
          outElements
        end

         #= This function takes a list of components and a Mod and returns a list of
          components  with the modifiers updated.  The function is used when flattening
          the inheritance structure, resulting in a list of components to insert into
          the class definition. For instance
          model A
            extends B(modifiers)
          end A;
          will result in a list of components
          from B for which modifiers should be applied to. =#
        function updateComponentsAndClassdefs(inComponents::List{<:Tuple{<:SCode.Element, DAE.Mod, Bool}}, inMod::DAE.Mod, inEnv::FCore.Graph) ::Tuple{List{Tuple{SCode.Element, DAE.Mod, Bool}}, DAE.Mod} 
              local outRestMod::DAE.Mod
              local outComponents::List{Tuple{SCode.Element, DAE.Mod, Bool}}

              (outComponents, outRestMod) = ListUtil.map1Fold(inComponents, updateComponentsAndClassdefs2, inEnv, inMod)
          (outComponents, outRestMod)
        end

        function updateComponentsAndClassdefs2(inComponent::Tuple{<:SCode.Element, DAE.Mod, Bool}, inEnv::FCore.Graph, inMod::DAE.Mod) ::Tuple{Tuple{SCode.Element, DAE.Mod, Bool}, DAE.Mod} 
              local outRestMod::DAE.Mod
              local outComponent::Tuple{SCode.Element, DAE.Mod, Bool}

              local el::SCode.Element
              local mod::DAE.Mod
              local b::Bool

              (el, mod, b) = inComponent
              (outComponent, outRestMod) = begin
                  local comp::SCode.Element
                  local cmod::DAE.Mod
                  local mod_rest::DAE.Mod
                @matchcontinue el begin
                  SCode.COMPONENT(__)  => begin
                      cmod = Mod.lookupCompModificationFromEqu(inMod, el.name)
                      cmod = Mod.merge(cmod, mod, el.name, false)
                      mod_rest = inMod
                    ((el, cmod, b), mod_rest)
                  end
                  
                  SCode.EXTENDS(__)  => begin
                    (inComponent, inMod)
                  end
                  
                  SCode.IMPORT(__)  => begin
                    ((el, DAE.NOMOD(), b), inMod)
                  end
                  
                  SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_)))  => begin
                      @match DAE.REDECL(element = comp, mod = cmod) = Mod.lookupCompModification(inMod, el.name)
                      mod_rest = inMod
                      cmod = Mod.merge(cmod, mod, el.name, false)
                      comp = SCodeUtil.mergeWithOriginal(comp, el)
                    ((comp, cmod, b), mod_rest)
                  end
                  
                  SCode.CLASS(__)  => begin
                      cmod = Mod.lookupCompModification(inMod, el.name)
                      outComponent = if valueEq(cmod, DAE.NOMOD())
                            inComponent
                          else
                            (el, cmod, b)
                          end
                    (outComponent, inMod)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- InstExtends.updateComponentsAndClassdefs2 failed on:\\n" + "env = " + FGraph.printGraphPathStr(inEnv) + "\\nmod = " + Mod.printModStr(inMod) + "\\ncmod = " + Mod.printModStr(mod) + "\\nbool = " + boolString(b) + "\\n" + SCodeDump.unparseElementStr(el))
                      fail()
                  end
                end
              end
               #=  Debug.traceln(\" comp: \" + id + \" \" + Mod.printModStr(mod));
               =#
               #=  take ONLY the modification from the equation if is typed
               =#
               #=  cmod2 = Mod.getModifs(inMod, id, m);
               =#
               #=  Debug.traceln(\"\\tSpecific mods on comp: \" +  Mod.printModStr(cmod2));
               =#
               #= mod_rest = Mod.removeMod(inMod, id);
               =#
               #= mod_rest = Mod.removeMod(inMod, id);
               =#
               #=  comp2 = SCodeUtil.renameElement(comp2, id);
               =#
               #=  adrpo:
               =#
               #=   2011-01-19 we can have a modifier in the mods here,
               =#
               #=   example in Modelica.Media:
               =#
               #=    partial package SingleGasNasa
               =#
               #=      extends Interfaces.PartialPureSubstance(
               =#
               #=        ThermoStates = Choices.IndependentVariables.pT,
               =#
               #=        mediumName=data.name,
               =#
               #=        substanceNames={data.name},
               =#
               #=        singleState=false,
               =#
               #=        Temperature(min=200, max=6000, start=500, nominal=500),
               =#
               #=        SpecificEnthalpy(start=if referenceChoice==ReferenceEnthalpy.ZeroAt0K then data.H0 else
               =#
               #=          if referenceChoice==ReferenceEnthalpy.UserDefined then h_offset else 0, nominal=1.0e5),
               =#
               #=        Density(start=10, nominal=10),
               =#
               #=        AbsolutePressure(start=10e5, nominal=10e5)); <--- AbsolutePressure is a type and can have modifications!
               =#
          (outComponent, outRestMod)
        end

         #=  Analyzes the elements of a class and fetches a list of components and classdefs,
          as well as aliases from imports to paths.
         =#
        function getLocalIdentList(ielts::List{<:Type_A}, tree::AvlSetString.Tree, getIdent::getIdentFn) ::AvlSetString.Tree 


              for elt in ielts
                tree = getIdent(elt, tree)
              end
          tree
        end

         #=  Analyzes the elements of a class and fetches a list of components and classdefs,
          as well as aliases from imports to paths.
         =#
        function getLocalIdentElementTpl(eltTpl::Tuple{<:SCode.Element, DAE.Mod, Bool}, tree::AvlSetString.Tree) ::AvlSetString.Tree 


              local elt::SCode.Element

              (elt, _, _) = eltTpl
              tree = getLocalIdentElement(elt, tree)
          tree
        end

         #=  Analyzes an element of a class and fetches a list of components and classdefs,
          as well as aliases from imports to paths. =#
        function getLocalIdentElement(elt::SCode.Element, tree::AvlSetString.Tree) ::AvlSetString.Tree 


              tree = begin
                  local id::String
                @match elt begin
                  SCode.COMPONENT(name = id)  => begin
                    AvlSetString.add(tree, id)
                  end
                  
                  SCode.CLASS(name = id)  => begin
                    AvlSetString.add(tree, id)
                  end
                  
                  _  => begin
                      tree
                  end
                end
              end
          tree
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment. =#
        function fixLocalIdent(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, elt::Tuple{<:SCode.Element, DAE.Mod, Bool}, tree::AvlSetString.Tree) ::Tuple{SCode.Element, DAE.Mod, Bool} 


              local elt1::SCode.Element
              local elt2::SCode.Element
              local mod::DAE.Mod
              local b::Bool

              (elt1, mod, b) = elt
              elt2 = fixElement(inCache, inEnv, elt1, tree)
              if ! referenceEq(elt1, elt2) || ! b
                elt = (elt2, mod, true)
              end
          elt
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixElement(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inElt::SCode.Element, tree::AvlSetString.Tree) ::SCode.Element 
              local outElts::SCode.Element

              outElts = begin
                  local name::String
                  local prefixes::SCode.Prefixes
                  local partialPrefix::SCode.Partial
                  local typeSpec1::Absyn.TypeSpec
                  local typeSpec2::Absyn.TypeSpec
                  local modifications1::SCode.Mod
                  local modifications2::SCode.Mod
                  local comment::SCode.Comment
                  local condition::Option{Absyn.Exp}
                  local info::SourceInfo
                  local classDef1::SCode.ClassDef
                  local classDef2::SCode.ClassDef
                  local restriction::SCode.Restriction
                  local optAnnotation::Option{SCode.Annotation}
                  local extendsPath1::Absyn.Path
                  local extendsPath2::Absyn.Path
                  local vis::SCode.Visibility
                  local ad::Absyn.ArrayDim
                  local ct::SCode.ConnectorType
                  local var::SCode.Variability
                  local prl::SCode.Parallelism
                  local dir::Absyn.Direction
                  local isf::Absyn.IsField
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local elt::SCode.Element
                  local elt2::SCode.Element
                  local attr::SCode.Attributes
                @matchcontinue (inEnv, inElt) begin
                  (env, elt && SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_))))  => begin
                       #= fprintln(Flags.DEBUG,\"fix comp \" + SCodeDump.unparseElementStr(elt,SCodeDump.defaultOptions));
                       =#
                       #=  lookup as it might have been redeclared!!!
                       =#
                      @match (_, _, (@match SCode.COMPONENT(name, prefixes, (@match SCode.ATTR() = attr), typeSpec1, modifications1, comment, condition, info) = elt2), _, _, env) = Lookup.lookupIdentLocal(arrayGet(inCache, 1), env, elt.name)
                      modifications2 = fixModifications(inCache, env, modifications1, tree)
                      typeSpec2 = fixTypeSpec(inCache, env, typeSpec1, tree)
                      ad = fixArrayDim(inCache, env, attr.arrayDims, tree)
                      if ! referenceEq(ad, attr.arrayDims)
                        attr.arrayDims = ad
                      end
                      if ! (referenceEq(ad, attr.arrayDims) && referenceEq(typeSpec1, typeSpec2) && referenceEq(modifications1, modifications2))
                        elt2 = SCode.COMPONENT(name, prefixes, attr, typeSpec2, modifications2, comment, condition, info)
                      end
                    elt2
                  end
                  
                  (env, elt && SCode.COMPONENT(attributes = attr))  => begin
                      modifications2 = fixModifications(inCache, env, elt.modifications, tree)
                      typeSpec2 = fixTypeSpec(inCache, env, elt.typeSpec, tree)
                      ad = fixArrayDim(inCache, env, attr.arrayDims, tree)
                      if ! referenceEq(ad, attr.arrayDims)
                        attr.arrayDims = ad
                      end
                      if ! (referenceEq(ad, attr.arrayDims) && referenceEq(elt.typeSpec, typeSpec2) && referenceEq(elt.modifications, modifications2))
                        elt = SCode.COMPONENT(elt.name, elt.prefixes, attr, typeSpec2, modifications2, elt.comment, elt.condition, elt.info)
                      end
                    elt
                  end
                  
                  (env, SCode.CLASS(name, prefixes && SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_)), SCode.ENCAPSULATED(__), partialPrefix, restriction, _, comment, info))  => begin
                      @match (SCode.CLASS(prefixes = prefixes, partialPrefix = partialPrefix, restriction = restriction, cmt = comment, info = info, classDef = classDef1), env) = Lookup.lookupClassLocal(env, name)
                      env = FGraph.openScope(env, SCode.ENCAPSULATED(), name, FGraph.restrictionToScopeType(restriction))
                      classDef2 = fixClassdef(inCache, env, classDef1, tree)
                    if referenceEq(classDef1, classDef2)
                          inElt
                        else
                          SCode.CLASS(name, prefixes, SCode.ENCAPSULATED(), partialPrefix, restriction, classDef2, comment, info)
                        end
                  end
                  
                  (env, SCode.CLASS(name, prefixes, SCode.ENCAPSULATED(__), partialPrefix, restriction, classDef1, comment, info))  => begin
                      env = FGraph.openScope(env, SCode.ENCAPSULATED(), name, FGraph.restrictionToScopeType(restriction))
                      classDef2 = fixClassdef(inCache, env, classDef1, tree)
                    if referenceEq(classDef1, classDef2)
                          inElt
                        else
                          SCode.CLASS(name, prefixes, SCode.ENCAPSULATED(), partialPrefix, restriction, classDef2, comment, info)
                        end
                  end
                  
                  (env, SCode.CLASS(name, prefixes && SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(_)), SCode.NOT_ENCAPSULATED(__), partialPrefix, restriction, _, comment, info))  => begin
                      @match (SCode.CLASS(prefixes = prefixes, partialPrefix = partialPrefix, restriction = restriction, cmt = comment, info = info, classDef = classDef1), env) = Lookup.lookupClassLocal(env, name)
                      env = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), name, FGraph.restrictionToScopeType(restriction))
                      classDef2 = fixClassdef(inCache, env, classDef1, tree)
                    if referenceEq(classDef1, classDef2)
                          inElt
                        else
                          SCode.CLASS(name, prefixes, SCode.NOT_ENCAPSULATED(), partialPrefix, restriction, classDef2, comment, info)
                        end
                  end
                  
                  (env, SCode.CLASS(name, prefixes, SCode.NOT_ENCAPSULATED(__), partialPrefix, restriction, classDef1, comment, info))  => begin
                      env = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), name, FGraph.restrictionToScopeType(restriction))
                      classDef2 = fixClassdef(inCache, env, classDef1, tree)
                    if referenceEq(classDef1, classDef2)
                          inElt
                        else
                          SCode.CLASS(name, prefixes, SCode.NOT_ENCAPSULATED(), partialPrefix, restriction, classDef2, comment, info)
                        end
                  end
                  
                  (env, SCode.EXTENDS(extendsPath1, vis, modifications1, optAnnotation, info))  => begin
                      extendsPath2 = fixPath(inCache, env, extendsPath1, tree)
                      modifications2 = fixModifications(inCache, env, modifications1, tree)
                    if referenceEq(extendsPath1, extendsPath2) && referenceEq(modifications1, modifications2)
                          inElt
                        else
                          SCode.EXTENDS(extendsPath2, vis, modifications2, optAnnotation, info)
                        end
                  end
                  
                  (_, SCode.IMPORT(__))  => begin
                    inElt
                  end
                  
                  (_, elt)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("InstExtends.fixElement failed: " + SCodeDump.unparseElementStr(elt))
                    fail()
                  end
                end
              end
               #= fprintln(Flags.DEBUG,\"fixClassdef \" + name);
               =#
               #=  lookup as it might have been redeclared!!!
               =#
               #=  failed above
               =#
               #= fprintln(Flags.DEBUG,\"fixClassdef \" + name);
               =#
               #= fprintln(Flags.DEBUG,\"fixClassdef \" + name + str);
               =#
               #=  lookup as it might have been redeclared!!!
               =#
               #=  failed above
               =#
               #= fprintln(Flags.DEBUG,\"fixClassdef \" + name + str);
               =#
               #= fprintln(Flags.DEBUG,\"fix extends \" + SCodeDump.unparseElementStr(elt,SCodeDump.defaultOptions));
               =#
          outElts
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment. =#
        function fixClassdef(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inCd::SCode.ClassDef, inTree::AvlSetString.Tree) ::SCode.ClassDef 
              local outCd::SCode.ClassDef

              local tree::AvlSetString.Tree = inTree

              outCd = begin
                  local elts::List{SCode.Element}
                  local elts_1::List{SCode.Element}
                  local ne::List{SCode.Equation}
                  local ne_1::List{SCode.Equation}
                  local ie::List{SCode.Equation}
                  local ie_1::List{SCode.Equation}
                  local na::List{SCode.AlgorithmSection}
                  local na_1::List{SCode.AlgorithmSection}
                  local ia::List{SCode.AlgorithmSection}
                  local ia_1::List{SCode.AlgorithmSection}
                  local nc::List{SCode.ConstraintSection}
                  local nc_1::List{SCode.ConstraintSection}
                  local clats::List{Absyn.NamedArg}
                  local ed::Option{SCode.ExternalDecl}
                  local ann::List{SCode.Annotation}
                  local c::Option{SCode.Comment}
                  local ts::Absyn.TypeSpec
                  local ts_1::Absyn.TypeSpec
                  local attr::SCode.Attributes
                  local mod::SCode.Mod
                  local mod_1::SCode.Mod
                  local env::FCore.Graph
                  local cd::SCode.ClassDef
                  local cd_1::SCode.ClassDef
                @matchcontinue (inEnv, inCd) begin
                  (env, SCode.PARTS(elts, ne, ie, na, ia, nc, clats, ed))  => begin
                      tree = getLocalIdentList(elts, tree, getLocalIdentElement)
                      elts_1 = fixList(cache, env, elts, tree, fixElement)
                      ne_1 = fixList(cache, env, ne, tree, fixEquation)
                      ie_1 = fixList(cache, env, ie, tree, fixEquation)
                      na_1 = fixList(cache, env, na, tree, fixAlgorithm)
                      ia_1 = fixList(cache, env, ia, tree, fixAlgorithm)
                      nc_1 = fixList(cache, env, nc, tree, fixConstraint)
                    if referenceEq(elts, elts_1) && referenceEq(ne, ne_1) && referenceEq(ie, ie_1) && referenceEq(na, na_1) && referenceEq(ia, ia_1) && referenceEq(nc, nc_1)
                          inCd
                        else
                          SCode.PARTS(elts_1, ne_1, ie_1, na_1, ia_1, nc_1, clats, ed)
                        end
                  end
                  
                  (env, SCode.CLASS_EXTENDS(mod, cd && SCode.PARTS(elts, ne, ie, na, ia, nc, clats, ed)))  => begin
                      mod_1 = fixModifications(cache, env, mod, inTree)
                      elts_1 = fixList(cache, env, elts, tree, fixElement)
                      ne_1 = fixList(cache, env, ne, tree, fixEquation)
                      ie_1 = fixList(cache, env, ie, tree, fixEquation)
                      na_1 = fixList(cache, env, na, tree, fixAlgorithm)
                      ia_1 = fixList(cache, env, ia, tree, fixAlgorithm)
                      nc_1 = fixList(cache, env, nc, tree, fixConstraint)
                      cd_1 = if referenceEq(elts, elts_1) && referenceEq(ne, ne_1) && referenceEq(ie, ie_1) && referenceEq(na, na_1) && referenceEq(ia, ia_1) && referenceEq(nc, nc_1)
                            cd
                          else
                            SCode.PARTS(elts_1, ne_1, ie_1, na_1, ia_1, nc_1, clats, ed)
                          end
                    if referenceEq(cd, cd_1) && referenceEq(mod, mod_1)
                          inCd
                        else
                          SCode.CLASS_EXTENDS(mod_1, cd_1)
                        end
                  end
                  
                  (env, SCode.DERIVED(ts, mod, attr))  => begin
                      ts_1 = fixTypeSpec(cache, env, ts, tree)
                      mod_1 = fixModifications(cache, env, mod, tree)
                    if referenceEq(ts, ts_1) && referenceEq(mod, mod_1)
                          inCd
                        else
                          SCode.DERIVED(ts_1, mod_1, attr)
                        end
                  end
                  
                  (_, cd && SCode.ENUMERATION(__))  => begin
                    cd
                  end
                  
                  (_, cd && SCode.OVERLOAD(__))  => begin
                    cd
                  end
                  
                  (_, cd && SCode.PDER(__))  => begin
                    cd
                  end
                  
                  (_, cd)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("InstExtends.fixClassDef failed: " + SCodeDump.classDefStr(cd))
                    fail()
                  end
                end
              end
          outCd
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixEquation(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inEq::SCode.Equation, tree::AvlSetString.Tree) ::SCode.Equation 
              local outEq::SCode.Equation

              outEq = begin
                  local eeq1::SCode.EEquation
                  local eeq2::SCode.EEquation
                @match inEq begin
                  SCode.EQUATION(eeq1)  => begin
                      eeq2 = fixEEquation(inCache, inEnv, eeq1, tree)
                    if referenceEq(eeq1, eeq2)
                          inEq
                        else
                          SCode.EQUATION(eeq2)
                        end
                  end
                  
                  SCode.EQUATION(eeq1)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- Inst.fixEquation failed: " + SCodeDump.equationStr(eeq1))
                    fail()
                  end
                end
              end
          outEq
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixEEquation(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inEeq::SCode.EEquation, tree::AvlSetString.Tree) ::SCode.EEquation 
              local outEeq::SCode.EEquation

              outEeq = begin
                  local id::String
                  local cref::Absyn.ComponentRef
                  local cref1::Absyn.ComponentRef
                  local cref2::Absyn.ComponentRef
                  local exp::Absyn.Exp
                  local exp1::Absyn.Exp
                  local exp2::Absyn.Exp
                  local exp3::Absyn.Exp
                  local expl::List{Absyn.Exp}
                  local eql::List{SCode.EEquation}
                  local eqll::List{List{SCode.EEquation}}
                  local whenlst::List{Tuple{Absyn.Exp, List{SCode.EEquation}}}
                  local comment::SCode.Comment
                  local optExp::Option{Absyn.Exp}
                  local info::SourceInfo
                @match inEeq begin
                  SCode.EQ_IF(expl, eqll, eql, comment, info)  => begin
                      expl = fixList(cache, inEnv, expl, tree, fixExp)
                      eqll = fixListList(cache, inEnv, eqll, tree, fixEEquation)
                      eql = fixList(cache, inEnv, eql, tree, fixEEquation)
                    SCode.EQ_IF(expl, eqll, eql, comment, info)
                  end
                  
                  SCode.EQ_EQUALS(exp1, exp2, comment, info)  => begin
                      exp1 = fixExp(cache, inEnv, exp1, tree)
                      exp2 = fixExp(cache, inEnv, exp2, tree)
                    SCode.EQ_EQUALS(exp1, exp2, comment, info)
                  end
                  
                  SCode.EQ_PDE(exp1, exp2, cref, comment, info)  => begin
                      exp1 = fixExp(cache, inEnv, exp1, tree)
                      exp2 = fixExp(cache, inEnv, exp2, tree)
                      cref = fixCref(cache, inEnv, cref, tree)
                    SCode.EQ_PDE(exp1, exp2, cref, comment, info)
                  end
                  
                  SCode.EQ_CONNECT(cref1, cref2, comment, info)  => begin
                      cref1 = fixCref(cache, inEnv, cref1, tree)
                      cref2 = fixCref(cache, inEnv, cref2, tree)
                    SCode.EQ_CONNECT(cref1, cref2, comment, info)
                  end
                  
                  SCode.EQ_FOR(id, optExp, eql, comment, info)  => begin
                      optExp = fixOption(cache, inEnv, optExp, tree, fixExp)
                      eql = fixList(cache, inEnv, eql, tree, fixEEquation)
                    SCode.EQ_FOR(id, optExp, eql, comment, info)
                  end
                  
                  SCode.EQ_WHEN(exp, eql, whenlst, comment, info)  => begin
                      exp = fixExp(cache, inEnv, exp, tree)
                      eql = fixList(cache, inEnv, eql, tree, fixEEquation)
                      whenlst = fixListTuple2(cache, inEnv, whenlst, tree, fixExp, fixListEEquation)
                    SCode.EQ_WHEN(exp, eql, whenlst, comment, info)
                  end
                  
                  SCode.EQ_ASSERT(exp1, exp2, exp3, comment, info)  => begin
                      exp1 = fixExp(cache, inEnv, exp1, tree)
                      exp2 = fixExp(cache, inEnv, exp2, tree)
                      exp3 = fixExp(cache, inEnv, exp3, tree)
                    SCode.EQ_ASSERT(exp1, exp2, exp3, comment, info)
                  end
                  
                  SCode.EQ_TERMINATE(exp, comment, info)  => begin
                      exp = fixExp(cache, inEnv, exp, tree)
                    SCode.EQ_TERMINATE(exp, comment, info)
                  end
                  
                  SCode.EQ_REINIT(exp1, exp, comment, info)  => begin
                      exp1 = fixExp(cache, inEnv, exp1, tree)
                      exp = fixExp(cache, inEnv, exp, tree)
                    SCode.EQ_REINIT(exp1, exp, comment, info)
                  end
                  
                  SCode.EQ_NORETCALL(exp, comment, info)  => begin
                      exp = fixExp(cache, inEnv, exp, tree)
                    SCode.EQ_NORETCALL(exp, comment, info)
                  end
                end
              end
          outEeq
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixListEEquation(cache::Array{<:FCore.Cache}, env::FCore.Graph, eeq::List{<:SCode.EEquation}, tree::AvlSetString.Tree) ::List{SCode.EEquation} 
              local outEeq::List{SCode.EEquation}

              outEeq = fixList(cache, env, eeq, tree, fixEEquation)
          outEeq
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixAlgorithm(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inAlg::SCode.AlgorithmSection, tree::AvlSetString.Tree) ::SCode.AlgorithmSection 
              local outAlg::SCode.AlgorithmSection

              local stmts1::List{SCode.Statement}
              local stmts2::List{SCode.Statement}

              @match SCode.ALGORITHM(stmts1) = inAlg
              stmts2 = fixList(inCache, inEnv, stmts1, tree, fixStatement)
              outAlg = if referenceEq(stmts1, stmts2)
                    inAlg
                  else
                    SCode.ALGORITHM(stmts2)
                  end
          outAlg
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixConstraint(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inConstrs::SCode.ConstraintSection, tree::AvlSetString.Tree) ::SCode.ConstraintSection 
              local outConstrs::SCode.ConstraintSection

              local exps::List{Absyn.Exp}

              @match SCode.CONSTRAINTS(exps) = inConstrs
              exps = fixList(inCache, inEnv, exps, tree, fixExp)
              outConstrs = SCode.CONSTRAINTS(exps)
          outConstrs
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixListAlgorithmItem(cache::Array{<:FCore.Cache}, env::FCore.Graph, alg::List{<:SCode.Statement}, tree::AvlSetString.Tree) ::List{SCode.Statement} 
              local outAlg::List{SCode.Statement}

              outAlg = fixList(cache, env, alg, tree, fixStatement)
          outAlg
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixStatement(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inStmt::SCode.Statement, tree::AvlSetString.Tree) ::SCode.Statement 
              local outStmt::SCode.Statement

              outStmt = begin
                  local exp::Absyn.Exp
                  local exp_1::Absyn.Exp
                  local exp1::Absyn.Exp
                  local exp2::Absyn.Exp
                  local exp1_1::Absyn.Exp
                  local exp2_1::Absyn.Exp
                  local optExp1::Option{Absyn.Exp}
                  local optExp2::Option{Absyn.Exp}
                  local iter::String
                  local elseifbranch1::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
                  local elseifbranch2::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
                  local whenlst::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
                  local truebranch1::List{SCode.Statement}
                  local truebranch2::List{SCode.Statement}
                  local elsebranch1::List{SCode.Statement}
                  local elsebranch2::List{SCode.Statement}
                  local body1::List{SCode.Statement}
                  local body2::List{SCode.Statement}
                  local comment::SCode.Comment
                  local info::SourceInfo
                  local stmt::SCode.Statement
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                @matchcontinue inStmt begin
                  SCode.ALG_ASSIGN(exp1, exp2, comment, info)  => begin
                      exp1_1 = fixExp(cache, inEnv, exp1, tree)
                      exp2_1 = fixExp(cache, inEnv, exp2, tree)
                    if referenceEq(exp1, exp1_1) && referenceEq(exp2, exp2_1)
                          inStmt
                        else
                          SCode.ALG_ASSIGN(exp1_1, exp2_1, comment, info)
                        end
                  end
                  
                  SCode.ALG_IF(exp1, truebranch1, elseifbranch1, elsebranch1, comment, info)  => begin
                      exp2 = fixExp(cache, inEnv, exp1, tree)
                      truebranch2 = fixList(cache, inEnv, truebranch1, tree, fixStatement)
                      elseifbranch2 = fixListTuple2(cache, inEnv, elseifbranch1, tree, fixExp, fixListAlgorithmItem)
                      elsebranch2 = fixList(cache, inEnv, elsebranch1, tree, fixStatement)
                    if referenceEq(exp1, exp2) && referenceEq(truebranch1, truebranch2) && referenceEq(elseifbranch1, elseifbranch2) && referenceEq(elsebranch1, elsebranch2)
                          inStmt
                        else
                          SCode.ALG_IF(exp2, truebranch2, elseifbranch2, elsebranch2, comment, info)
                        end
                  end
                  
                  SCode.ALG_FOR(iter, optExp1, body1, comment, info)  => begin
                      optExp2 = fixOption(cache, inEnv, optExp1, tree, fixExp)
                      body2 = fixList(cache, inEnv, body1, tree, fixStatement)
                    if referenceEq(optExp1, optExp2) && referenceEq(body1, body2)
                          inStmt
                        else
                          SCode.ALG_FOR(iter, optExp2, body2, comment, info)
                        end
                  end
                  
                  SCode.ALG_PARFOR(iter, optExp1, body1, comment, info)  => begin
                      optExp2 = fixOption(cache, inEnv, optExp1, tree, fixExp)
                      body2 = fixList(cache, inEnv, body1, tree, fixStatement)
                    if referenceEq(optExp1, optExp2) && referenceEq(body1, body2)
                          inStmt
                        else
                          SCode.ALG_PARFOR(iter, optExp2, body2, comment, info)
                        end
                  end
                  
                  SCode.ALG_WHILE(exp1, body1, comment, info)  => begin
                      exp2 = fixExp(cache, inEnv, exp1, tree)
                      body2 = fixList(cache, inEnv, body1, tree, fixStatement)
                    if referenceEq(exp1, exp2) && referenceEq(body1, body2)
                          inStmt
                        else
                          SCode.ALG_WHILE(exp2, body2, comment, info)
                        end
                  end
                  
                  SCode.ALG_WHEN_A(whenlst, comment, info)  => begin
                      whenlst = fixListTuple2(cache, inEnv, whenlst, tree, fixExp, fixListAlgorithmItem)
                    SCode.ALG_WHEN_A(whenlst, comment, info)
                  end
                  
                  SCode.ALG_ASSERT(exp, exp1, exp2, comment, info)  => begin
                      exp_1 = fixExp(cache, inEnv, exp, tree)
                      exp1_1 = fixExp(cache, inEnv, exp1, tree)
                      exp2_1 = fixExp(cache, inEnv, exp2, tree)
                    if referenceEq(exp, exp_1) && referenceEq(exp1, exp1_1) && referenceEq(exp2, exp2_1)
                          inStmt
                        else
                          SCode.ALG_ASSERT(exp_1, exp1_1, exp2_1, comment, info)
                        end
                  end
                  
                  SCode.ALG_TERMINATE(exp1, comment, info)  => begin
                      exp2 = fixExp(cache, inEnv, exp1, tree)
                    if referenceEq(exp1, exp2)
                          inStmt
                        else
                          SCode.ALG_TERMINATE(exp2, comment, info)
                        end
                  end
                  
                  SCode.ALG_REINIT(exp1, exp2, comment, info)  => begin
                      exp1_1 = fixExp(cache, inEnv, exp1, tree)
                      exp2_1 = fixExp(cache, inEnv, exp2, tree)
                    if referenceEq(exp1, exp1_1) && referenceEq(exp2, exp2_1)
                          inStmt
                        else
                          SCode.ALG_REINIT(exp1_1, exp2_1, comment, info)
                        end
                  end
                  
                  SCode.ALG_NORETCALL(exp1, comment, info)  => begin
                      exp2 = fixExp(cache, inEnv, exp1, tree)
                    if referenceEq(exp1, exp2)
                          inStmt
                        else
                          SCode.ALG_NORETCALL(exp2, comment, info)
                        end
                  end
                  
                  SCode.ALG_RETURN(__)  => begin
                    inStmt
                  end
                  
                  SCode.ALG_BREAK(__)  => begin
                    inStmt
                  end
                  
                  SCode.ALG_FAILURE(body1, comment, info)  => begin
                      body2 = fixList(cache, inEnv, body1, tree, fixStatement)
                    if referenceEq(body1, body2)
                          inStmt
                        else
                          SCode.ALG_FAILURE(body2, comment, info)
                        end
                  end
                  
                  SCode.ALG_TRY(truebranch1, elsebranch1, comment, info)  => begin
                      truebranch2 = fixList(cache, inEnv, truebranch1, tree, fixStatement)
                      elsebranch2 = fixList(cache, inEnv, elsebranch1, tree, fixStatement)
                    if referenceEq(truebranch1, truebranch2) && referenceEq(elsebranch1, elsebranch2)
                          inStmt
                        else
                          SCode.ALG_TRY(truebranch2, elsebranch2, comment, info)
                        end
                  end
                  
                  SCode.ALG_CONTINUE(__)  => begin
                    inStmt
                  end
                  
                  _  => begin
                        Error.addInternalError(getInstanceName() + " failed: " + Dump.unparseAlgorithmStr(SCodeUtil.statementToAlgorithmItem(inStmt)), sourceInfo())
                      fail()
                  end
                end
              end
          outStmt
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixArrayDim(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, ads::Absyn.ArrayDim, tree::AvlSetString.Tree) ::Absyn.ArrayDim 


              ads = fixList(inCache, inEnv, ads, tree, fixSubscript)
          ads
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixSubscript(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inSub::Absyn.Subscript, tree::AvlSetString.Tree) ::Absyn.Subscript 
              local outSub::Absyn.Subscript

              outSub = begin
                  local exp1::Absyn.Exp
                  local exp2::Absyn.Exp
                @match inSub begin
                  Absyn.NOSUB(__)  => begin
                    inSub
                  end
                  
                  Absyn.SUBSCRIPT(exp1)  => begin
                      exp2 = fixExp(cache, inEnv, exp1, tree)
                    if referenceEq(exp1, exp2)
                          inSub
                        else
                          Absyn.SUBSCRIPT(exp2)
                        end
                  end
                end
              end
          outSub
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixTypeSpec(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inTs::Absyn.TypeSpec, tree::AvlSetString.Tree) ::Absyn.TypeSpec 
              local outTs::Absyn.TypeSpec

              outTs = begin
                  local path1::Absyn.Path
                  local path2::Absyn.Path
                  local arrayDim1::Option{Absyn.ArrayDim}
                  local arrayDim2::Option{Absyn.ArrayDim}
                  local typeSpecs1::List{Absyn.TypeSpec}
                  local typeSpecs2::List{Absyn.TypeSpec}
                @match inTs begin
                  Absyn.TPATH(path1, arrayDim1)  => begin
                      arrayDim2 = fixOption(cache, inEnv, arrayDim1, tree, fixArrayDim)
                      path2 = fixPath(cache, inEnv, path1, tree)
                    if referenceEq(arrayDim2, arrayDim1) && referenceEq(path1, path2)
                          inTs
                        else
                          Absyn.TPATH(path2, arrayDim2)
                        end
                  end
                  
                  Absyn.TCOMPLEX(path1, typeSpecs1, arrayDim1)  => begin
                      arrayDim2 = fixOption(cache, inEnv, arrayDim1, tree, fixArrayDim)
                      path2 = fixPath(cache, inEnv, path1, tree)
                      typeSpecs2 = fixList(cache, inEnv, typeSpecs1, tree, fixTypeSpec)
                    if referenceEq(arrayDim2, arrayDim1) && referenceEq(path1, path2) && referenceEq(typeSpecs1, typeSpecs2)
                          inTs
                        else
                          Absyn.TCOMPLEX(path2, typeSpecs2, arrayDim2)
                        end
                  end
                end
              end
          outTs
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment. =#
        function fixPath(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inPath::Absyn.Path, tree::AvlSetString.Tree) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local id::String
                  local path2::Absyn.Path
                  local path::Absyn.Path
                  local cache::FCore.Cache
                @matchcontinue inPath begin
                  Absyn.FULLYQUALIFIED(__)  => begin
                    inPath
                  end
                  
                  _  => begin
                      id = AbsynUtil.pathFirstIdent(inPath)
                      @match true = AvlSetString.hasKey(tree, id)
                      path2 = FGraph.pathStripGraphScopePrefix(inPath, inEnv, false)
                    path2
                  end
                  
                  _  => begin
                      (_, _) = Lookup.lookupClassLocal(inEnv, AbsynUtil.pathFirstIdent(inPath))
                      path = FGraph.pathStripGraphScopePrefix(inPath, inEnv, false)
                    path
                  end
                  
                  _  => begin
                      (cache, path) = Inst.makeFullyQualified(arrayGet(inCache, 1), inEnv, inPath)
                      path = FGraph.pathStripGraphScopePrefix(path, inEnv, false)
                      arrayUpdate(inCache, 1, cache)
                    path
                  end
                  
                  _  => begin
                        path = FGraph.pathStripGraphScopePrefix(inPath, inEnv, false)
                      path
                  end
                end
              end
               #=  first indent is local in the inEnv, DO NOT QUALIFY!
               =#
               #= fprintln(Flags.DEBUG,\"Try makeFullyQualified \" + AbsynUtil.pathString(path));
               =#
               #= fprintln(Flags.DEBUG,\"FullyQual: \" + AbsynUtil.pathString(path));
               =#
               #=  isOutside = isPathOutsideScope(cache, inEnv, path);
               =#
               #= print(\"Try makeFullyQualified \" + AbsynUtil.pathString(path) + \"\\n\");
               =#
               #=  path = if_(isOutside, path, FGraph.pathStripGraphScopePrefix(path, inEnv, false));
               =#
               #= print(\"FullyQual: \" + AbsynUtil.pathString(path) + \"\\n\");
               =#
               #= fprintln(Flags.DEBUG, \"Path not fixed: \" + AbsynUtil.pathString(path) + \"\\n\");
               =#
          outPath
        end

        function lookupVarNoErrorMessage(inCache::FCore.Cache, inEnv::FCore.Graph, ident::String) ::Tuple{FCore.Graph, String} 
              local id::String
              local outEnv::FCore.Graph

              try
                ErrorExt.setCheckpoint("InstExtends.lookupVarNoErrorMessage")
                (_, _, _, _, _, _, outEnv, _, id) = Lookup.lookupVarIdent(inCache, inEnv, ident)
                ErrorExt.rollBack("InstExtends.lookupVarNoErrorMessage")
              catch
                ErrorExt.rollBack("InstExtends.lookupVarNoErrorMessage")
                fail()
              end
          (outEnv, id)
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment. =#
        function fixCref(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, tree::AvlSetString.Tree) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local id::String
                  local path::Absyn.Path
                  local cref_::DAE.ComponentRef
                  local env::FCore.Graph
                  local denv::FCore.Graph
                  local cref::Absyn.ComponentRef
                  local c::SCode.Element
                  local isOutside::Bool
                @matchcontinue (inEnv, inCref) begin
                  (env, Absyn.CREF_FULLYQUALIFIED(__))  => begin
                      env = FGraph.topScope(inEnv)
                    fixCref(cache, env, inCref.componentRef, tree)
                  end
                  
                  (env, cref)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      @match true = AvlSetString.hasKey(tree, id)
                      cref = FGraph.crefStripGraphScopePrefix(cref, env, false)
                      cref = if AbsynUtil.crefEqual(cref, inCref)
                            inCref
                          else
                            cref
                          end
                    cref
                  end
                  
                  (env, cref)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      (denv, id) = lookupVarNoErrorMessage(arrayGet(cache, 1), env, id)
                      denv = FGraph.openScope(denv, SCode.ENCAPSULATED(), id, NONE())
                      cref = AbsynUtil.crefReplaceFirstIdent(cref, FGraph.getGraphName(denv))
                      cref = FGraph.crefStripGraphScopePrefix(cref, env, false)
                      cref = if AbsynUtil.crefEqual(cref, inCref)
                            inCref
                          else
                            cref
                          end
                    cref
                  end
                  
                  (env, cref)  => begin
                      id = AbsynUtil.crefFirstIdent(cref)
                      (_, c, denv) = Lookup.lookupClassIdent(arrayGet(cache, 1), env, id)
                      id = SCodeUtil.getElementName(c)
                      denv = FGraph.openScope(denv, SCode.ENCAPSULATED(), id, NONE())
                      cref = AbsynUtil.crefReplaceFirstIdent(cref, FGraph.getGraphName(denv))
                      cref = FGraph.crefStripGraphScopePrefix(cref, env, false)
                      cref = if AbsynUtil.crefEqual(cref, inCref)
                            inCref
                          else
                            cref
                          end
                    cref
                  end
                  
                  _  => begin
                      inCref
                  end
                end
              end
               #=  try lookup var (constant in a package?)
               =#
               #= fprintln(Flags.DEBUG,\"Try lookupV \" + id);
               =#
               #= fprintln(Flags.DEBUG,\"Got env \" + intString(listLength(env)));
               =#
               #=  isOutside = FGraph.graphPrefixOf(denv, env);
               =#
               #=  cref = if_(isOutside, cref, FGraph.crefStripGraphScopePrefix(cref, env, false));
               =#
               #= fprintln(Flags.DEBUG, \"Cref VAR fixed: \" + AbsynUtil.printComponentRefStr(cref));
               =#
               #= print(\"Try lookupC \" + id + \"\\n\");
               =#
               #=  isOutside = FGraph.graphPrefixOf(denv, env);
               =#
               #=  id might come from named import, make sure you use the actual class name!
               =#
               #= fprintln(Flags.DEBUG,\"Got env \" + intString(listLength(env)));
               =#
               #=  cref = if_(isOutside, cref, FGraph.crefStripGraphScopePrefix(cref, env, false));
               =#
               #= print(\"Cref CLASS fixed: \" + AbsynUtil.printComponentRefStr(cref) + \"\\n\");
               =#
          outCref
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixModifications(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inMod::SCode.Mod, tree::AvlSetString.Tree) ::SCode.Mod 
              local outMod::SCode.Mod = inMod

              outMod = begin
                  local subModLst::List{SCode.SubMod}
                  local exp::Option{Absyn.Exp}
                  local e::SCode.Element
                  local cdef::SCode.ClassDef
                @matchcontinue outMod begin
                  SCode.NOMOD(__)  => begin
                    inMod
                  end
                  
                  SCode.MOD(__)  => begin
                      subModLst = fixList(inCache, inEnv, outMod.subModLst, tree, fixSubMod)
                      if ! referenceEq(outMod.subModLst, subModLst)
                        outMod.subModLst = subModLst
                      end
                      exp = fixOption(inCache, inEnv, outMod.binding, tree, fixExp)
                      if ! referenceEq(exp, outMod.binding)
                        outMod.binding = exp
                      end
                    outMod
                  end
                  
                  SCode.REDECL(element = SCode.COMPONENT(__))  => begin
                      e = fixElement(inCache, inEnv, outMod.element, tree)
                      if ! referenceEq(e, outMod.element)
                        outMod.element = e
                      end
                    outMod
                  end
                  
                  SCode.REDECL(element = e && SCode.CLASS(classDef = cdef))  => begin
                      cdef = fixClassdef(inCache, inEnv, cdef, tree)
                      if ! referenceEq(cdef, e.classDef)
                        e.classDef = cdef
                        outMod.element = e
                      end
                    outMod
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("InstExtends.fixModifications failed: " + SCodeDump.printModStr(inMod))
                      fail()
                  end
                end
              end
          outMod
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment. =#
        function fixSubMod(inCache::Array{<:FCore.Cache}, inEnv::FCore.Graph, subMod::SCode.SubMod, tree::AvlSetString.Tree) ::SCode.SubMod 


              local ident::Absyn.Ident
              local mod1::SCode.Mod
              local mod2::SCode.Mod

              @match SCode.NAMEMOD(ident, mod1) = subMod
              mod2 = fixModifications(inCache, inEnv, mod1, tree)
              if ! referenceEq(mod1, mod2)
                subMod = SCode.NAMEMOD(ident, mod2)
              end
          subMod
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixExp(cache::Array{<:FCore.Cache}, inEnv::FCore.Graph, inExp::Absyn.Exp, tree::AvlSetString.Tree) ::Absyn.Exp 
              local outExp::Absyn.Exp

              (outExp, _) = AbsynUtil.traverseExp(inExp, fixExpTraverse, (cache, inEnv, tree))
          outExp
        end

         #=  All of the fix functions do the following:
          Analyzes the SCode datastructure and replace paths with a new path (from
          local lookup or fully qualified in the environment.
         =#
        function fixExpTraverse(exp::Absyn.Exp, tpl::Tuple{<:Array{<:FCore.Cache}, FCore.Graph, AvlSetString.Tree}) ::Tuple{Absyn.Exp, Tuple{Array{FCore.Cache}, FCore.Graph, AvlSetString.Tree}} 



              local inExp::Absyn.Exp = exp

              exp = begin
                  local fargs::Absyn.FunctionArgs
                  local cref::Absyn.ComponentRef
                  local cref1::Absyn.ComponentRef
                  local path::Absyn.Path
                  local cache::Array{FCore.Cache}
                  local env::FCore.Graph
                  local tree::AvlSetString.Tree
                @match (exp, tpl) begin
                  (Absyn.CREF(cref), (cache, env, tree))  => begin
                      cref1 = fixCref(cache, env, cref, tree)
                    if referenceEq(cref, cref1)
                          exp
                        else
                          Absyn.CREF(cref1)
                        end
                  end
                  
                  (Absyn.CALL(cref, fargs), (cache, env, tree))  => begin
                      cref1 = fixCref(cache, env, cref, tree)
                    if referenceEq(cref, cref1)
                          exp
                        else
                          Absyn.CALL(cref1, fargs)
                        end
                  end
                  
                  (Absyn.PARTEVALFUNCTION(cref, fargs), (cache, env, tree))  => begin
                      cref1 = fixCref(cache, env, cref, tree)
                    if referenceEq(cref, cref1)
                          exp
                        else
                          Absyn.PARTEVALFUNCTION(cref1, fargs)
                        end
                  end
                  
                  _  => begin
                      exp
                  end
                end
              end
               #=  print(\"cref actual: \" + AbsynUtil.crefString(cref) + \" scope: \" + FGraph.printGraphPathStr(env) + \"\\n\");
               =#
               #=  print(\"cref fixed : \" + AbsynUtil.crefString(cref) + \"\\n\");
               =#
          (exp, tpl)
        end

         #=  Generic function to fix an optional element. =#
        function fixOption(inCache::Array{FCore.Cache}, inEnv::FCore.Graph, inA::Option{Type_A}, tree::AvlSetString.Tree, fixA::FixAFn)  where {Type_A}
              local outA::Option{Type_A}

              outA = begin
                  local A1::Type_A
                  local A2::Type_A
                @match inA begin
                  NONE()  => begin
                    inA
                  end
                  
                  SOME(A1)  => begin
                      A2 = fixA(inCache, inEnv, A1, tree)
                    if referenceEq(A1, A2)
                          inA
                        else
                          SOME(A2)
                        end
                  end
                end
              end
          outA
        end

         #=  Generic function to fix a list of elements. =#
        function fixList(inCache::Array{FCore.Cache}, inEnv::FCore.Graph, inA::List{Type_A}, tree::AvlSetString.Tree, fixA::FixAFn)  where {Type_A}
              local outA::List{Type_A}

              if listEmpty(inA)
                outA = inA
                return outA
              end
              outA = ListUtil.mapCheckReferenceEq(inA, (inCache, inEnv, tree) -> fixA(inCache = inCache, inEnv = inEnv, tree = tree))
          outA
        end

         #=  Generic function to fix a list of elements. =#
        function fixListList(inCache::Array{FCore.Cache}, inEnv::FCore.Graph, inA::List{List{Type_A}}, tree::AvlSetString.Tree, fixA::FixAFn)  where {Type_A}
              local outA::List{List{Type_A}} = nil

              if listEmpty(inA)
                outA = nil
                return outA
              end
              outA = ListUtil.mapCheckReferenceEq(inA, (inCache, inEnv, tree, fixA) -> fixList(inCache = inCache, inEnv = inEnv, tree = tree, fixA = fixA))
          outA
        end

         #=  Generic function to fix a list of elements. =#
        function fixListTuple2(inCache::Array{FCore.Cache}, inEnv::FCore.Graph, inRest::List{Tuple{Type_A, Type_B}}, tree::AvlSetString.Tree, fixA::FixAFn, fixB::FixBFn)  where {Type_A, Type_B}
              local outA::List{Tuple{Type_A, Type_B}}

              local a1::Type_A
              local a2::Type_A
              local b1::Type_B
              local b2::Type_B

              outA = fixList(inCache, inEnv, inRest, tree, (fixA, fixB) -> fixTuple2(fixA = fixA, fixB = fixB))
          outA
        end

         #=  Generic function to fix a list of elements. =#
        function fixTuple2(inCache::Array{FCore.Cache}, inEnv::FCore.Graph, tpl::Tuple{Type_A, Type_B}, tree::AvlSetString.Tree, fixA::FixAFn, fixB::FixBFn)  where {Type_A, Type_B}


              local a1::Type_A
              local a2::Type_A
              local b1::Type_B
              local b2::Type_B

              (a1, b1) = tpl
              a2 = fixA(inCache, inEnv, a1, tree)
              b2 = fixB(inCache, inEnv, b1, tree)
              if ! (referenceEq(a1, a2) && referenceEq(b1, b2))
                tpl = (a2, b2)
              end
          tpl
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
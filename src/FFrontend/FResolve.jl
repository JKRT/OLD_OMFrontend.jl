  module FResolve 


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
         #=  public imports
         =#

        import Absyn
        import AbsynUtil
        import FCore
        import FNode
        import FLookup

        import SCode
        import SCodeUtil
        import FGraphBuild
        import ListUtil
        import ClassInf

        Name = FCore.Name 
        Id = FCore.Id 
        Seq = FCore.Seq 
        Next = FCore.Next 
        Node = FCore.Node 
        Data = FCore.Data 
        Kind = FCore.Kind 
        Ref = FCore.MMRef 
        Refs = FCore.Refs 
        Children = FCore.Children 
        Parents = FCore.Parents 
        ImportTable = FCore.ImportTable 
        Extra = FCore.Extra 
        Visited = FCore.Visited 
        Import = FCore.Import 
        Graph = FCore.Graph 
        Msg = Option 

         #= @author: adrpo
         for all extends nodes lookup the type and add $ref nodes to the result =#
        function ext(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, ext_one, g)
                    g
                  end
                end
              end
               #=  apply on all extends nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function ext_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local rn::Ref
                  local rc::Ref
                  local p::Absyn.Path
                  local e::SCode.Element
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found extends that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefExtends(r)
                      @match false = FNode.isRefDerived(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefExtends(r)
                      @match false = FNode.isRefDerived(r)
                      @match FCore.EX(e = e) = FNode.refData(r)
                      p = SCodeUtil.getBaseClassPath(e)
                      _ = SCodeUtil.elementInfo(e)
                      (g, rr) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefExtends(r)
                      @match false = FNode.isRefDerived(r)
                      @match FCore.EX(e = e) = FNode.refData(r)
                      p = SCodeUtil.getBaseClassPath(e)
                      _ = SCodeUtil.elementInfo(e)
                      @shouldFail (_, _) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.ext_one: baseclass: " + AbsynUtil.pathString(p) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found extends
               =#
               #=  not found ref
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all derived nodes lookup the type and add $ref nodes to the result =#
        function derived(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, derived_one, g)
                    g
                  end
                end
              end
               #=  apply on all derived nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function derived_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local p::Absyn.Path
                  local d::SCode.ClassDef
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found derived that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefDerived(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefDerived(r)
                      @match FCore.CL(e = SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(p, _)))) = FNode.refData(r)
                      (g, rr) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefDerived(r)
                      @match FCore.CL(e = SCode.CLASS(classDef = SCode.DERIVED(typeSpec = Absyn.TPATH(p, _)))) = FNode.refData(r)
                      @shouldFail (_, _) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.derived_one: baseclass: " + AbsynUtil.pathString(p) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found derived
               =#
               #=  not found ref
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all component nodes lookup the type and add $ref nodes to the result =#
        function ty(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, ty_one, g)
                    g
                  end
                end
              end
               #=  apply to all component nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function ty_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local p::Absyn.Path
                  local e::SCode.Element
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found component that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefComponent(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefComponent(r)
                      @match FCore.CO(e = e) = FNode.refData(r)
                      @match Absyn.TPATH(p, _) = SCodeUtil.getComponentTypeSpec(e)
                      (g, rr) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefComponent(r)
                      @match FCore.CO(e = e) = FNode.refData(r)
                      @match Absyn.TPATH(p, _) = SCodeUtil.getComponentTypeSpec(e)
                      @shouldFail (_, _) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.ty_one: component type path: " + AbsynUtil.pathString(p) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found component
               =#
               #=  print(\"Resolving ty: \" + AbsynUtil.pathString(p) + \" -> \" + FNode.toStr(FNode.fromRef(rr)) + \"\\n\");
               =#
               #=  not found ref
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all constrained class nodes lookup the type and add $ref nodes to the result =#
        function cc(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, cc_one, g)
                    g
                  end
                end
              end
               #=  apply on all constraintby nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function cc_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local p::Absyn.Path
                  local e::SCode.Element
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found constraint class that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefConstrainClass(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefConstrainClass(r)
                      @match FCore.CC(SCode.CONSTRAINCLASS(constrainingClass = p)) = FNode.refData(r)
                      (g, rr) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefConstrainClass(r)
                      @match FCore.CC(SCode.CONSTRAINCLASS(constrainingClass = p)) = FNode.refData(r)
                      @shouldFail (_, _) = FLookup.name(g, r, p, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.cc_one: constrained class: " + AbsynUtil.pathString(p) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found constraint class
               =#
               #=  not found ref
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all class extends nodes lookup the base class and add $ref nodes to the result =#
        function clsext(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, clsext_one, g)
                    g
                  end
                end
              end
               #=  apply on all class extends nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function clsext_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local p::Ref
                  local e::SCode.Element
                  local n::Node
                  local i::SourceInfo
                  local id::Name
                  local g::Graph
                   #=  found class extends that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefClassExtends(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefClassExtends(r)
                      @match FCore.CL(e = SCode.CLASS(name = id)) = FNode.refData(r)
                      @match _cons(p, _) = FNode.parents(FNode.fromRef(r))
                      (g, rr) = FLookup.ext(g, p, id, FLookup.ignoreParentsAndImports, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefClassExtends(r)
                      @match FCore.CL(e = SCode.CLASS(name = id)) = FNode.refData(r)
                      @match _cons(p, _) = FNode.parents(FNode.fromRef(r))
                      @shouldFail (_, _) = FLookup.ext(g, p, id, FLookup.ignoreParentsAndImports, FLookup.dummyLookupOption)
                      print("FResolve.clsext_one: class extends: " + id + " scope: " + FNode.toPathStr(FNode.fromRef(r)) + " not found in extends of: " + FNode.toPathStr(FNode.fromRef(p)) + ":\\n")
                      print("\\t" + stringDelimitList(ListUtil.map(ListUtil.map(FNode.extendsRefs(p), FNode.fromRef), FNode.toPathStr), "\\n\\t") + "\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found class extends
               =#
               #=  get the parent where the extends are!
               =#
               #=  search ONLY in extends!
               =#
               #=  not found ref
               =#
               #=  get the parent where the extends are!
               =#
               #=  search ONLY in extends!
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all crefs lookup the cref node and add $ref nodes to the result =#
        function cr(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, cr_one, g)
                    g
                  end
                end
              end
               #=  apply on all component reference nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function cr_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local cr::Absyn.ComponentRef
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found cref that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefCref(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefCref(r)
                      @match FCore.CR(r = cr) = FNode.refData(r)
                      (g, rr) = FLookup.cr(g, r, cr, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefCref(r)
                      @match FCore.CR(r = cr) = FNode.refData(r)
                      @shouldFail (_, _) = FLookup.cr(g, r, cr, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.cr_one: component reference: " + AbsynUtil.crefString(cr) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found cref
               =#
               #=  SOME(AbsynUtil.dummyInfo));
               =#
               #=  not found ref
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all mods lookup the modifier node and add $ref nodes to the result =#
        function mod(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, mod_one, g)
                    g
                  end
                end
              end
               #=  apply on all modifier nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function mod_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local cr::Absyn.ComponentRef
                  local n::Node
                  local i::SourceInfo
                  local g::Graph
                   #=  found mod that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefMod(r) && ! FNode.isRefModHolder(r) && ! ClassInf.isBasicTypeComponentName(FNode.refName(r))
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefMod(r) && ! FNode.isRefModHolder(r) && ! ClassInf.isBasicTypeComponentName(FNode.refName(r))
                      cr = AbsynUtil.pathToCref(AbsynUtil.stringListPath(FNode.namesUpToParentName(r, FNode.modNodeName)))
                      (g, rr) = FLookup.cr(g, FNode.getModifierTarget(r), cr, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefMod(r) && ! FNode.isRefModHolder(r) && ! ClassInf.isBasicTypeComponentName(FNode.refName(r))
                      cr = AbsynUtil.pathToCref(AbsynUtil.stringListPath(FNode.namesUpToParentName(r, FNode.modNodeName)))
                      @shouldFail (_, _) = FLookup.cr(g, FNode.getModifierTarget(r), cr, FLookup.ignoreNothing, FLookup.dummyLookupOption)
                      print("FResolve.mod_one: modifier: " + AbsynUtil.crefString(cr) + " not found in: " + FNode.toPathStr(FNode.fromRef(r)) + "!\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found mod
               =#
               #=  SOME(AbsynUtil.dummyInfo));
               =#
               #=  not found mod
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

         #= @author: adrpo
         for all redeclare as element lookup the base class and add $ref nodes to the result =#
        function elred(inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local refs::Refs
                  local g::Graph
                @match (inRef, ig) begin
                  (_, g)  => begin
                      g = FNode.apply1(inRef, elred_one, g)
                    g
                  end
                end
              end
               #=  apply on all class extends nodes
               =#
          og
        end

         #= @author: adrpo
         helper =#
        function elred_one(name::Name, inRef::Ref, ig::Graph) ::Graph 
              local og::Graph

              og = begin
                  local r::Ref
                  local rr::Ref
                  local p::Ref
                  local e::SCode.Element
                  local n::Node
                  local i::SourceInfo
                  local id::Name
                  local g::Graph
                   #=  found redeclare as element that has a ref node
                   =#
                @matchcontinue (inRef, ig) begin
                  (r, g)  => begin
                      @match true = FNode.isRefRedeclare(r)
                      @match true = FNode.isRefClass(r) && ! FNode.isRefClassExtends(r) || FNode.isRefComponent(r)
                      @match true = FNode.isRefRefResolved(r)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefRedeclare(r)
                      @match true = FNode.isRefClass(r) && ! FNode.isRefClassExtends(r) || FNode.isRefComponent(r)
                      id = SCodeUtil.elementName(FNode.getElement(FNode.fromRef(r)))
                      @match _cons(p, _) = FNode.parents(FNode.fromRef(r))
                      (g, rr) = FLookup.ext(g, p, id, FLookup.ignoreParentsAndImports, FLookup.dummyLookupOption)
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, list(rr), r, g)
                    g
                  end
                  
                  (r, g)  => begin
                      @match true = FNode.isRefRedeclare(r)
                      @match true = FNode.isRefClass(r) && ! FNode.isRefClassExtends(r) || FNode.isRefComponent(r)
                      id = SCodeUtil.elementName(FNode.getElement(FNode.fromRef(r)))
                      @match _cons(p, _) = FNode.parents(FNode.fromRef(r))
                      @shouldFail (_, _) = FLookup.ext(g, p, id, FLookup.ignoreParentsAndImports, FLookup.dummyLookupOption)
                      print("FResolve.elred_one: redeclare as element: " + id + " scope: " + FNode.toPathStr(FNode.fromRef(r)) + " not found in extends of: " + FNode.toPathStr(FNode.fromRef(p)) + ":\\n")
                      print("\\t" + stringDelimitList(ListUtil.map(ListUtil.map(FNode.extendsRefs(p), FNode.fromRef), FNode.toPathStr), "\\n\\t") + "\\n")
                      g = FGraphBuild.mkRefNode(FNode.refNodeName, nil, r, g)
                    g
                  end
                  
                  _  => begin
                      ig
                  end
                end
              end
               #=  it does have a reference child already!
               =#
               #=  found redeclare as element
               =#
               #=  get the parent where the extends are!
               =#
               #=  search ONLY in extends!
               =#
               #=  not found ref
               =#
               #=  get the parent where the extends are!
               =#
               #=  search ONLY in extends!
               =#
               #=  put it in the graph as unresolved ref
               =#
          og
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
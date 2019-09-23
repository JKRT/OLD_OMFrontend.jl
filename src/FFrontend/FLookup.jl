  module FLookup 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Options 

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
        import FCore
        import FNode

        import ListUtil
        import FGraph
        import FGraphBuild

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
        Graph = FCore.Graph 
        Extra = FCore.Extra 
        Visited = FCore.Visited 
        Import = FCore.Import 
        Msg = Option 
         const dummyLookupOption = NONE()::Option
         #=  SOME(AbsynUtil.dummyInfo);
         =#

         @Uniontype Options begin
              @Record OPTIONS begin

                       ignoreImports::Bool
                       ignoreExtends::Bool
                       ignoreParents::Bool
              end
         end

         const ignoreNothing = OPTIONS(false, false, false)::Options

         const ignoreParents = OPTIONS(false, false, true)::Options

         const ignoreParentsAndImports = OPTIONS(true, false, true)::Options

         const ignoreAll = OPTIONS(true, true, true)::Options

         #= @author: adrpo
         search for id =#
        function id(inGraph::Graph, inRef::Ref, inName::Name, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local p::Parents
                  local g::Graph
                   #=  implicit scope which has for iterators
                   =#
                @matchcontinue (inGraph, inRef, inName, inOptions, inMsg) begin
                  (g, _, _, _, _)  => begin
                      r = FNode.child(inRef, FNode.forNodeName)
                      r = FNode.child(r, inName)
                    (g, r)
                  end
                  
                  (g, _, _, OPTIONS(_, _, false), _)  => begin
                      @match true = FNode.isRefImplicitScope(inRef)
                      p = FNode.parents(FNode.fromRef(inRef))
                      r = FNode.original(p)
                      (g, r) = id(g, r, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, _, _)  => begin
                      @match false = FNode.isRefImplicitScope(inRef)
                      r = FNode.child(inRef, inName)
                    (g, r)
                  end
                  
                  (g, _, _, OPTIONS(false, _, _), _)  => begin
                      @match false = FNode.isRefImplicitScope(inRef)
                      (g, r) = imp(g, inRef, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, OPTIONS(_, false, _), _)  => begin
                      @match false = FNode.isRefImplicitScope(inRef)
                      (g, r) = ext(g, inRef, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, OPTIONS(_, _, false), _)  => begin
                      @match false = FNode.isRefImplicitScope(inRef)
                      @match true = FNode.isEncapsulated(FNode.fromRef(inRef))
                      r = FNode.top(inRef)
                      (g, r) = id(g, r, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, OPTIONS(_, _, false), _)  => begin
                      @match false = FNode.isRefImplicitScope(inRef)
                      @match false = FNode.isEncapsulated(FNode.fromRef(inRef))
                      @match true = FNode.hasParents(FNode.fromRef(inRef))
                      p = FNode.parents(FNode.fromRef(inRef))
                      r = FNode.original(p)
                      (g, r) = search(g, list(r), inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (_, _, _, OPTIONS(_, _, false), _)  => begin
                      @match false = FNode.hasParents(FNode.fromRef(inRef))
                    fail()
                  end
                  
                  (_, _, _, _, SOME(_))  => begin
                      print("FLookup.id failed for: " + inName + " in: " + FNode.toPathStr(FNode.fromRef(inRef)) + "\\n")
                    fail()
                  end
                end
              end
               #= /*/ self?
                  case (g, _, _, _, _)
                    equation
                      true = FNode.isRefImplicitScope(inRef);
                      true = stringEq(FNode.name(FNode.fromRef(inRef)), inName);
                      r = FNode.child(inRef, inName);
                      false = FNode.isRefImplicitScope(r);
                    then
                      (g, r);*/ =#
               #=  implicit scope? move upwards if allowed
               =#
               #=  get the original parent
               =#
               #=  local?
               =#
               #=  lookup in imports
               =#
               #=  lookup in extends
               =#
               #=  encapsulated
               =#
               #=  search parent
               =#
               #=  get the original parent
               =#
               #=  top node reached
               =#
               #=  failure
               =#
          (outGraph, outRef)
        end

         #= @author: adrpo
         search for id in list =#
        function search(inGraph::Graph, inRefs::Refs, inName::Name, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local rest::Refs
                  local g::Graph
                   #=  not found
                   =#
                @matchcontinue (inGraph, inRefs, inName, inOptions, inMsg) begin
                  (_,  nil(), _, _, _)  => begin
                    fail()
                  end
                  
                  (g, r <| _, _, _, _)  => begin
                      (g, r) = id(g, r, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _ <| rest, _, _, _)  => begin
                      (g, r) = search(g, rest, inName, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (_, _, _, _, SOME(_))  => begin
                      print("FLookup.search failed for: " + inName + " in: " + FNode.toPathStr(FNode.fromRef(listHead(inRefs))) + "\\n")
                    fail()
                  end
                end
              end
               #=  found
               =#
               #=  search rest
               =#
               #=  failure
               =#
          (outGraph, outRef)
        end

         #= @author: adrpo
         search for a name =#
        function name(inGraph::Graph, inRef::Ref, inPath::Absyn.Path, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local i::Name
                  local rest::Absyn.Path
                  local s::String
                  local g::Graph
                   #=  simple name
                   =#
                @matchcontinue (inGraph, inRef, inPath, inOptions, inMsg) begin
                  (g, _, Absyn.IDENT(i), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, Absyn.QUALIFIED(i, rest), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                      (g, r) = name(g, r, rest, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, Absyn.QUALIFIED(i, rest), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                      @shouldFail (_, _) = name(g, r, rest, inOptions, inMsg)
                      s = "missing: " + AbsynUtil.pathString(rest) + " in scope: " + FNode.toPathStr(FNode.fromRef(r))
                      (g, r) = FGraphBuild.mkAssertNode(AbsynUtil.pathFirstIdent(rest), s, r, g)
                    (g, r)
                  end
                  
                  (g, _, Absyn.FULLYQUALIFIED(rest), _, _)  => begin
                      r = FNode.top(inRef)
                      (g, r) = name(g, r, rest, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (_, _, _, _, SOME(_))  => begin
                      print("FLookup.name failed for: " + AbsynUtil.pathString(inPath) + " in: " + FNode.toPathStr(FNode.fromRef(inRef)) + "\\n")
                    fail()
                  end
                end
              end
               #=  qualified name, could find the rest
               =#
               #=  qualified name, could not find the rest, stop!
               =#
               #=  add an assersion node that it should
               =#
               #=  be a name in here and return that
               =#
               #=  make the assert node have the name of the missing path part
               =#
               #=  fully qual name
               =#
          (outGraph, outRef)
        end

         #= @author: adrpo
         search for id in extends =#
        function ext(inGraph::Graph, inRef::Ref, inName::Name, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local refs::Refs
                  local p::Parents
                  local g::Graph
                   #=  for class extends search inside the base class first
                   =#
                @matchcontinue (inGraph, inRef, inName, inOptions, inMsg) begin
                  (g, _, _, _, _)  => begin
                      @match true = FNode.isClassExtends(FNode.fromRef(inRef))
                      r = FNode.child(inRef, FNode.refNodeName)
                      r = FNode.target(FNode.fromRef(r))
                      (g, r) = id(g, r, inName, ignoreParents, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, _, _)  => begin
                      @match true = FNode.isClassExtends(FNode.fromRef(inRef))
                      r = FNode.original(FNode.parents(FNode.fromRef(inRef)))
                      (g, r) = id(g, r, inName, ignoreNothing, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, _, _)  => begin
                      refs = FNode.extendsRefs(inRef)
                      @match false = listEmpty(refs)
                      refs = ListUtil.mapMap(refs, FNode.fromRef, FNode.target)
                      (g, r) = search(g, refs, inName, ignoreParentsAndImports, inMsg)
                    (g, r)
                  end
                end
              end
               #=  get its ref node
               =#
               #=  get the target from ref
               =#
               #=  print(\"Searching for: \" + inName + \" in class extends target:\\n\\t\" + FNode.toPathStr(FNode.fromRef(r)) + \"\\n\");
               =#
               #=  search in type target
               =#
               #=  print(\"Found it in: \" + FNode.toPathStr(FNode.fromRef(r)) + \"\\n\");
               =#
               #=  for class extends: if not found in base class search in the parents of this node
               =#
               #=  get the original parent
               =#
               #=  print(\"Found it in: \" + FNode.toPathStr(FNode.fromRef(r)) + \"\\n\");
               =#
               #=  get all extends of the node and search in them
               =#
               #=  print(\"Searching for: \" + inName + \" in extends targets:\\n\\t\" + stringDelimitList(List.mapMap(refs, FNode.fromRef, FNode.toPathStr), \"\\n\\t\") + \"\\n\");
               =#
          (outGraph, outRef)
        end

         #= @author: adrpo
         search for id in imports =#
        function imp(inGraph::Graph, inRef::Ref, inName::Name, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local p::Parents
                  local qi::List{Import}
                  local uqi::List{Import}
                  local g::Graph
                   #=  lookup in qual
                   =#
                @matchcontinue (inGraph, inRef, inName, inOptions, inMsg) begin
                  (g, _, _, _, _)  => begin
                      @match true = FNode.hasImports(FNode.fromRef(inRef))
                      (qi, _) = FNode.imports(FNode.fromRef(inRef))
                      (g, r) = imp_qual(g, inRef, inName, qi, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, _, _)  => begin
                      @match true = FNode.hasImports(FNode.fromRef(inRef))
                      (_, uqi) = FNode.imports(FNode.fromRef(inRef))
                      (g, r) = imp_unqual(g, inRef, inName, uqi, inOptions, inMsg)
                    (g, r)
                  end
                end
              end
               #=  lookup in un-qual
               =#
          (outGraph, outRef)
        end

         #= Looks up a name through the qualified imports in a scope. =#
        function imp_qual(inGraph::Graph, inRef::Ref, inName::Name, inImports::List{<:Import}, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local name::Name
                  local path::Absyn.Path
                  local rest_imps::List{Import}
                  local r::Ref
                  local g::Graph
                   #=  No match, search the rest of the list of imports.
                   =#
                @matchcontinue (inGraph, inRef, inName, inImports, inOptions, inMsg) begin
                  (g, _, _, Absyn.NAMED_IMPORT(name = name) <| rest_imps, _, _)  => begin
                      @match false = stringEqual(inName, name)
                      (g, r) = imp_qual(g, inRef, inName, rest_imps, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, Absyn.NAMED_IMPORT(name = name, path = path) <| _, _, _)  => begin
                      @match true = stringEqual(inName, name)
                      (g, r) = fq(g, path, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (_, _, _, Absyn.NAMED_IMPORT(name = name) <| _, _, _)  => begin
                      @match true = stringEqual(inName, name)
                    fail()
                  end
                end
              end
               #=  Match, look up the fully qualified import path.
               =#
               #=  Partial match, return failure
               =#
               #=  TODO! maybe add an assertion node!
               =#
          (outGraph, outRef)
        end

         #= Looks up a name through the qualified imports in a scope. If it finds the
          name it returns the item, path, and environment for the name, otherwise it
          fails. =#
        function imp_unqual(inGraph::Graph, inRef::Ref, inName::Name, inImports::List{<:Import}, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local path::Absyn.Path
                  local path2::Absyn.Path
                  local rest_imps::List{Import}
                  local r::Ref
                  local g::Graph
                   #=  For each unqualified import we have to look up the package the import
                   =#
                   #=  points to, and then look among the public member of the package for the
                   =#
                   #=  name we are looking for.
                   =#
                @matchcontinue (inGraph, inRef, inName, inImports, inOptions, inMsg) begin
                  (g, _, _, Absyn.UNQUAL_IMPORT(path = path) <| _, _, _)  => begin
                      (g, r) = fq(g, path, inOptions, inMsg)
                      (g, r) = id(g, r, inName, ignoreParents, inMsg)
                    (g, r)
                  end
                  
                  (g, _, _, _ <| rest_imps, _, _)  => begin
                      (g, r) = imp_unqual(g, inRef, inName, rest_imps, inOptions, inMsg)
                    (g, r)
                  end
                end
              end
               #=  Look up the import path.
               =#
               #=  Look up the name among the public member of the found package.
               =#
               #=  No match, continue with the rest of the imports.
               =#
          (outGraph, outRef)
        end

         #= Looks up a fully qualified path in ref =#
        function fq(inGraph::Graph, inName::Absyn.Path, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = name(inGraph, FGraph.top(inGraph), inName, inOptions, inMsg)
          (outGraph, outRef)
        end

         #= @author: adrpo
         search for a component reference =#
        function cr(inGraph::Graph, inRef::Ref, inCref::Absyn.ComponentRef, inOptions::Options, inMsg::Msg #= Message flag, SOME() outputs lookup error messages =#) ::Tuple{Graph, Ref} 
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local r::Ref
                  local i::Name
                  local rest::Absyn.ComponentRef
                  local ss::List{Absyn.Subscript}
                  local g::Graph
                  local s::String
                   #=  simple name
                   =#
                @matchcontinue (inGraph, inRef, inCref, inOptions, inMsg) begin
                  (g, _, Absyn.CREF_IDENT(i, _), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (g, _, Absyn.CREF_QUAL(i, _, rest), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                      @match true = FNode.isRefComponent(r)
                      r = FNode.child(r, FNode.refNodeName)
                      r = FNode.target(FNode.fromRef(r))
                      (g, r) = cr(g, r, rest, ignoreParents, inMsg)
                    (g, r)
                  end
                  
                  (g, _, Absyn.CREF_QUAL(i, _, rest), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                      @match true = FNode.isRefClass(r)
                      (g, r) = cr(g, r, rest, ignoreParents, inMsg)
                    (g, r)
                  end
                  
                  (g, _, Absyn.CREF_QUAL(i, _, rest), _, _)  => begin
                      (g, r) = id(g, inRef, i, inOptions, inMsg)
                      @match true = FNode.isRefClass(r) || FNode.isRefComponent(r)
                      s = "missing: " + AbsynUtil.crefString(rest) + " in scope: " + FNode.toPathStr(FNode.fromRef(r))
                      (g, r) = FGraphBuild.mkAssertNode(AbsynUtil.crefFirstIdent(rest), s, r, g)
                    (g, r)
                  end
                  
                  (g, _, Absyn.CREF_FULLYQUALIFIED(rest), _, _)  => begin
                      r = FGraph.top(g)
                      (g, r) = cr(g, r, rest, inOptions, inMsg)
                    (g, r)
                  end
                  
                  (_, _, _, _, SOME(_))  => begin
                      print("FLookup.cr failed for: " + AbsynUtil.crefString(inCref) + " in: " + FNode.toPathStr(FNode.fromRef(inRef)) + "\\n")
                    fail()
                  end
                end
              end
               #=  qualified name, first is component
               =#
               #=  inRef is a component, lookup in type
               =#
               #=  get the ref
               =#
               #=  get the target from ref
               =#
               #=  search in type target
               =#
               #=  qualified name
               =#
               #=  inRef is a class
               =#
               #=  qualified name
               =#
               #=  inRef is a class
               =#
               #=  add an assersion node that it should
               =#
               #=  be a name in here and return that
               =#
               #=  make the assert node have the name of the missing cref part
               =#
               #=  fully qual name
               =#
          (outGraph, outRef)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
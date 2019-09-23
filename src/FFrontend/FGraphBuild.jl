  module FGraphBuild


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

        import SCode

        import FCore

        import FNode

        import FGraph

        import DAE

        import Prefix

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
        Scope = FCore.Scope

        import ListUtil
        import AbsynToSCode
        import SCodeDump
        import SCodeUtil
        import SCodeInstUtil
        import Util
        import FMod

         #= builds nodes out of classes =#
        function mkProgramGraph(inProgram::SCode.Program, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              local topRef::Ref

              topRef = FGraph.top(inGraph)
              outGraph = ListUtil.fold2(inProgram, mkClassGraph, topRef, inKind, inGraph)
          outGraph
        end

         #= Extends the graph with a class. =#
        function mkClassGraph(inClass::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local name::String
                  local g::Graph
                  local cdef::SCode.ClassDef
                  local info::SourceInfo
                   #=  class (we don't care here if is replaceable or not we can get that from the class)
                   =#
                @match (inClass, inParentRef, inKind, inGraph) begin
                  (SCode.CLASS(__), _, _, g)  => begin
                      g = mkClassNode(inClass, inParentRef, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

        function mkClassNode(inClass::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local cdef::SCode.ClassDef
                  local cls::SCode.Element
                  local name::String
                  local g::Graph
                  local info::SourceInfo
                  local n::Node
                  local nr::Ref
                @match (inClass, inParentRef, inKind, inGraph) begin
                  (_, _, _, g)  => begin
                      cls = SCodeInstUtil.expandEnumerationClass(inClass)
                      @match SCode.CLASS(name = name, classDef = cdef) = cls
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.CL(cls, Prefix.NOPRE(), DAE.NOMOD(), inKind, FCore.VAR_UNTYPED()))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = mkConstrainClass(cls, nr, inKind, g)
                      g = mkClassChildren(name, cdef, nr, inKind, g)
                    g
                  end
                end
              end
               #=  add constrained by node
               =#
          outGraph
        end

        function mkConstrainClass(inElement::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                  local cc::SCode.ConstrainClass
                  local m::SCode.Mod
                  local p::Absyn.Path
                @matchcontinue (inElement, inParentRef, inKind, inGraph) begin
                  (SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(SOME(cc && SCode.CONSTRAINCLASS(constrainingClass = p, modifier = m))))), _, _, g)  => begin
                      (g, n) = FGraph.node(g, FNode.ccNodeName, list(inParentRef), FCore.CC(cc))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.ccNodeName, nr)
                      g = mkModNode(FNode.modNodeName, m, FCore.MS_CONSTRAINEDBY(p), nr, inKind, g)
                    g
                  end

                  (SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(SOME(cc && SCode.CONSTRAINCLASS(constrainingClass = p, modifier = m))))), _, _, g)  => begin
                      (g, n) = FGraph.node(g, FNode.ccNodeName, list(inParentRef), FCore.CC(cc))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.ccNodeName, nr)
                      g = mkModNode(FNode.modNodeName, m, FCore.MS_CONSTRAINEDBY(p), nr, inKind, g)
                    g
                  end

                  _  => begin
                      inGraph
                  end
                end
              end
               #=  no cc found in element!
               =#
          outGraph
        end

        function mkModNode(inName::Name #= a name for this mod so we can call it from sub-mods =#, inMod::SCode.Mod, inModScope::FCore.ModScope, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local name::Name
                  local g::Graph
                  local n::Node
                  local nr::Ref
                  local e::SCode.Element
                  local sm::List{SCode.SubMod}
                  local b::Option{Absyn.Exp}
                  local p::Absyn.Path
                   #=  no mods
                   =#
                @matchcontinue (inName, inMod, inModScope, inParentRef, inKind, inGraph) begin
                  (_, SCode.NOMOD(__), _, _, _, g)  => begin
                    g
                  end

                  (_, SCode.MOD(subModLst =  nil(), binding = NONE()), _, _, _, g)  => begin
                    g
                  end

                  (name, SCode.MOD(subModLst =  nil(), binding = b && SOME(_)), _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.MO(inMod))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = mkBindingNode(b, nr, inKind, g)
                    g
                  end

                  (name, SCode.MOD(subModLst = sm, binding = b), _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.MO(inMod))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      sm = FMod.compactSubMods(sm, inModScope)
                      g = mkSubMods(sm, inModScope, nr, inKind, g)
                      g = mkBindingNode(b, nr, inKind, g)
                    g
                  end

                  (name, SCode.REDECL(element = e), _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.MO(inMod))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = mkElementNode(e, nr, inKind, g)
                    g
                  end

                  (name, _, _, _, _, g)  => begin
                      print("FGraphBuild.mkModNode failed with: " + name + " mod: " + SCodeDump.printModStr(inMod, SCodeDump.defaultOptions) + "\\n")
                    g
                  end
                end
              end
               #=  no binding no sub-mods
               =#
               #=  just a binding
               =#
               #=  yeha, some mods for sure and a possible binding
               =#
               #=  compact the sub modifiers so no duplicates occur (that would overwrite subnodes)
               =#
               #=  ouch, a redeclare :)
               =#
               #=  something bad happened!
               =#
          outGraph
        end

        function mkSubMods(inSubMod::List{<:SCode.SubMod}, inModScope::FCore.ModScope, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local rest::List{SCode.SubMod}
                  local s::SCode.SubMod
                  local id::Name
                  local m::SCode.Mod
                  local g::Graph
                   #=  no more, we're done!
                   =#
                @match (inSubMod, inModScope, inParentRef, inKind, inGraph) begin
                  ( nil(), _, _, _, g)  => begin
                    g
                  end

                  (SCode.NAMEMOD(id, m) <| rest, _, _, _, g)  => begin
                      g = mkModNode(id, m, inModScope, inParentRef, inKind, g)
                      g = mkSubMods(rest, inModScope, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  some sub-mods!
               =#
          outGraph
        end

        function mkBindingNode(inBinding::Option{<:Absyn.Exp}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local m::SCode.Mod
                  local e::Absyn.Exp
                  local g::Graph
                   #=  no binding
                   =#
                @match (inBinding, inParentRef, inKind, inGraph) begin
                  (NONE(), _, _, g)  => begin
                    g
                  end

                  (SOME(e), _, _, g)  => begin
                      g = mkExpressionNode(FNode.bndNodeName, e, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  some binding
               =#
          outGraph
        end

         #= Extends the graph with a class's components. =#
        function mkClassChildren(name::String, inClassDef::SCode.ClassDef, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local el::List{SCode.Element}
                  local g::Graph
                  local c::SCode.Element
                  local cdef::SCode.ClassDef
                  local n::Node
                  local nr::Ref
                  local ts::Absyn.TypeSpec
                  local p::Absyn.Path
                  local m::SCode.Mod
                  local ad::Absyn.ArrayDim
                  local eqs::List{SCode.Equation}
                  local ieqs::List{SCode.Equation}
                  local als::List{SCode.AlgorithmSection}
                  local ials::List{SCode.AlgorithmSection}
                  local constraintLst::List{SCode.ConstraintSection}
                  local clsattrs::List{Absyn.NamedArg}
                  local externalDecl::Option{SCode.ExternalDecl}
                  local pathlst::List{Absyn.Path}
                @matchcontinue (inClassDef, inParentRef, inKind, inGraph) begin
                  (SCode.PARTS(elementLst = el, normalEquationLst = eqs, initialEquationLst = ieqs, normalAlgorithmLst = als, initialAlgorithmLst = ials, constraintLst = constraintLst, clsattrs = clsattrs, externalDecl = externalDecl), _, _, g)  => begin
                      g = ListUtil.fold2(el, mkElementNode, inParentRef, inKind, g)
                      g = mkEqNode(FNode.eqNodeName, eqs, inParentRef, inKind, g)
                      g = mkEqNode(FNode.ieqNodeName, ieqs, inParentRef, inKind, g)
                      g = mkAlNode(FNode.alNodeName, als, inParentRef, inKind, g)
                      g = mkAlNode(FNode.ialNodeName, ials, inParentRef, inKind, g)
                      g = mkOptNode(FNode.optNodeName, constraintLst, clsattrs, inParentRef, inKind, g)
                      g = mkExternalNode(FNode.edNodeName, externalDecl, inParentRef, inKind, g)
                    g
                  end

                  (SCode.CLASS_EXTENDS(composition = cdef, modifications = m), _, _, g)  => begin
                      g = mkClassChildren(name, cdef, inParentRef, inKind, g)
                      g = mkModNode(FNode.modNodeName, m, FCore.MS_CLASS_EXTENDS(name), inParentRef, inKind, g)
                    g
                  end

                  (SCode.DERIVED(typeSpec = ts, modifications = m), _, _, g)  => begin
                      p = AbsynUtil.typeSpecPath(ts)
                      nr = inParentRef
                      g = mkModNode(FNode.modNodeName, m, FCore.MS_DERIVED(p), nr, inKind, g)
                      ad = AbsynUtil.typeSpecDimensions(ts)
                      g = mkDimsNode(FNode.tydimsNodeName, SOME(ad), nr, inKind, g)
                    g
                  end

                  (SCode.OVERLOAD(_), _, _, g)  => begin
                    g
                  end

                  (SCode.PDER(_, _), _, _, g)  => begin
                    g
                  end

                  _  => begin
                      inGraph
                  end
                end
              end
          outGraph
        end

         #= Extends the graph with an element. =#
        function mkElementNode(inElement::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local name::SCode.Ident
                  local p::Absyn.Path
                  local n::Node
                  local ts::Absyn.TypeSpec
                  local nr::Ref
                  local m::SCode.Mod
                   #=  component
                   =#
                @match (inElement, inParentRef, inKind, inGraph) begin
                  (SCode.COMPONENT(__), _, _, g)  => begin
                      g = mkCompNode(inElement, inParentRef, inKind, g)
                    g
                  end

                  (SCode.CLASS(__), _, _, g)  => begin
                      g = mkClassNode(inElement, inParentRef, inKind, g)
                    g
                  end

                  (SCode.EXTENDS(baseClassPath = p, modifications = m), _, _, g)  => begin
                      name = FNode.mkExtendsName(p)
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.EX(inElement, DAE.NOMOD()))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = mkModNode(FNode.modNodeName, m, FCore.MS_EXTENDS(p), nr, inKind, g)
                    g
                  end

                  (SCode.IMPORT(__), _, _, g)  => begin
                      g = mkImportNode(inElement, inParentRef, inKind, g)
                    g
                  end

                  (SCode.DEFINEUNIT(__), _, _, g)  => begin
                      g = mkUnitsNode(inElement, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  class
               =#
               #=  the extends is saved as a child with the extends name
               =#
          outGraph
        end

         #= @author: adrpo
         create FNode.duNodeName if it doesn't
         exist and add the given element to it =#
        function mkUnitsNode(inElement::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local r::Ref
                  local du::List{SCode.Element}
                   #=  if is there add the unit to it
                   =#
                @matchcontinue (inElement, inParentRef, inKind, inGraph) begin
                  (_, _, _, g)  => begin
                      r = FNode.child(inParentRef, FNode.duNodeName)
                      FNode.addDefinedUnitToRef(r, inElement)
                    g
                  end

                  (_, _, _, g)  => begin
                      (g, n) = FGraph.node(g, FNode.duNodeName, list(inParentRef), FCore.DU(list(inElement)))
                      r = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.duNodeName, r)
                    g
                  end
                end
              end
               #=  if not there create it
               =#
          outGraph
        end

         #= @author: adrpo
         create FNode.imNodeName if it doesn't
         exist and add the given element to it =#
        function mkImportNode(inElement::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local r::Ref
                  local du::List{SCode.Element}
                   #=  if is there add the unit to it
                   =#
                @matchcontinue (inElement, inParentRef, inKind, inGraph) begin
                  (_, _, _, g)  => begin
                      r = FNode.child(inParentRef, FNode.imNodeName)
                      FNode.addImportToRef(r, inElement)
                    g
                  end

                  (_, _, _, g)  => begin
                      (g, n) = FGraph.node(g, FNode.imNodeName, list(inParentRef), FCore.IM(FCore.emptyImportTable))
                      r = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.imNodeName, r)
                      FNode.addImportToRef(r, inElement)
                    g
                  end
                end
              end
               #=  if not there create it
               =#
          outGraph
        end

        function mkDimsNode(inName::Name #= name to use for the array dims node: $dims (FNode.dimsNodeName) or $tydims (FNode.tydimsNodeName) =#, inArrayDims::Option{<:Absyn.ArrayDim}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local m::SCode.Mod
                  local a::Absyn.ArrayDim
                  local g::Graph
                @match (inName, inArrayDims, inParentRef, inKind, inGraph) begin
                  (_, NONE(), _, _, g)  => begin
                    g
                  end

                  (_, SOME( nil()), _, _, g)  => begin
                    g
                  end

                  (_, SOME(a && _ <| _), _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.DIMS(inName, a))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                      g = mkDimsNode_helper(0, a, nr, inKind, g)
                    g
                  end
                end
              end
               #=  some array dims
               =#
          outGraph
        end

        function mkDimsNode_helper(inStartWith::ModelicaInteger, inArrayDims::Absyn.ArrayDim, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local name::Name
                  local rest::Absyn.ArrayDim
                  local s::Absyn.Subscript
                  local i::ModelicaInteger
                  local e::Absyn.Exp
                  local g::Graph
                   #=  we're done
                   =#
                @match (inStartWith, inArrayDims, inParentRef, inKind, inGraph) begin
                  (_,  nil(), _, _, g)  => begin
                    g
                  end

                  (i, Absyn.NOSUB(__) <| rest, _, _, g)  => begin
                      name = intString(i)
                      g = mkExpressionNode(name, Absyn.END(), inParentRef, inKind, g)
                      g = mkDimsNode_helper(i + 1, rest, inParentRef, inKind, g)
                    g
                  end

                  (i, Absyn.SUBSCRIPT(e) <| rest, _, _, g)  => begin
                      name = intString(i)
                      g = mkExpressionNode(name, e, inParentRef, inKind, g)
                      g = mkDimsNode_helper(i + 1, rest, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  nosub, saved as Absyn.END
               =#
               #=  subscript, saved as exp
               =#
          outGraph
        end

         #= Extends the graph with a component =#
        function mkCompNode(inComp::SCode.Element, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              local name::String
              local g::Graph
              local n::Node
              local nr::Ref
              local m::SCode.Mod
              local cnd::Option{Absyn.Exp}
              local ad::Absyn.ArrayDim
              local ts::Absyn.TypeSpec
              local tad::Absyn.ArrayDim
              local nd::Data
              local i::DAE.Var

              @match SCode.COMPONENT(name = name, attributes = SCode.ATTR(arrayDims = ad), typeSpec = ts, modifications = m, condition = cnd) = inComp
              (nd, i) = FNode.element2Data(inComp, inKind)
              (g, n) = FGraph.node(inGraph, name, list(inParentRef), nd)
              nr = FNode.toRef(n)
              FNode.addChildRef(inParentRef, name, nr)
               #=  add instance node
               =#
              g = mkInstNode(i, nr, g)
               #=  add ref node
               =#
              g = mkRefNode(FNode.refNodeName, nil, nr, g)
               #=  add type dimensions if exists
               =#
              tad = AbsynUtil.typeSpecDimensions(ts)
              g = mkDimsNode(FNode.tydimsNodeName, SOME(tad), nr, inKind, g)
               #=  add component dimensions if exists
               =#
              g = mkDimsNode(FNode.dimsNodeName, SOME(ad), nr, inKind, g)
               #=  add condition if exists
               =#
              g = mkConditionNode(cnd, nr, inKind, g)
               #=  add constrained by node
               =#
              g = mkConstrainClass(inComp, nr, inKind, g)
               #=  add modifier
               =#
              g = mkModNode(FNode.modNodeName, m, FCore.MS_COMPONENT(name), nr, inKind, g)
              outGraph = g
          outGraph
        end

         #= Extends the graph with an inst node =#
        function mkInstNode(inVar::DAE.Var, inParentRef::Ref, inGraph::Graph) ::Graph
              local outGraph::Graph

              local nr::Ref
              local n::Node
              local g::Graph

              (g, n) = FGraph.node(inGraph, FNode.itNodeName, list(inParentRef), FCore.IT(inVar))
              nr = FNode.toRef(n)
              FNode.addChildRef(inParentRef, FNode.itNodeName, nr)
              outGraph = g
          outGraph
        end

        function mkConditionNode(inCondition::Option{<:Absyn.Exp}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local e::Absyn.Exp
                  local g::Graph
                   #=  no binding
                   =#
                @match (inCondition, inParentRef, inKind, inGraph) begin
                  (NONE(), _, _, g)  => begin
                    g
                  end

                  (SOME(e), _, _, g)  => begin
                      g = mkExpressionNode(FNode.cndNodeName, e, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  some condition
               =#
          outGraph
        end

        function mkExpressionNode(inName::Name, inExp::Absyn.Exp, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local e::Absyn.Exp
                  local crefs::List{Absyn.ComponentRef}
                  local g::Graph
                @match (inName, inExp, inParentRef, inKind, inGraph) begin
                  (_, e, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.EXP(inName, e))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                      g = analyseExp(e, nr, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

        function mkCrefsNodes(inCrefs::List{<:Absyn.ComponentRef}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local name::Name
                  local rest::List{Absyn.ComponentRef}
                  local s::Absyn.Subscript
                  local i::ModelicaInteger
                  local e::Absyn.Exp
                  local g::Graph
                  local cr::Absyn.ComponentRef
                   #=  we're done
                   =#
                @match (inCrefs, inParentRef, inKind, inGraph) begin
                  ( nil(), _, _, g)  => begin
                    g
                  end

                  (cr <| rest, _, _, g)  => begin
                      g = mkCrefNode(cr, inParentRef, inKind, g)
                      g = mkCrefsNodes(rest, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  cref::rest
               =#
          outGraph
        end

        function mkCrefNode(inCref::Absyn.ComponentRef, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local e::Absyn.Exp
                  local g::Graph
                  local name::Name
                @match (inCref, inParentRef, inKind, inGraph) begin
                  (_, _, _, g)  => begin
                      name = AbsynUtil.printComponentRefStr(inCref)
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.CR(inCref))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = mkDimsNode(FNode.subsNodeName, ListUtil.mkOption(AbsynUtil.getSubsFromCref(inCref, true, true)), nr, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

        function mkTypeNode(inTypes::List{<:DAE.Type} #= the types to add =#, inParentRef::Ref, inName::Name #= name to search for =#, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local tys::List{DAE.Type}
                  local nr::Ref
                  local pr::Ref
                  local name::Option{Name}
                  local parents::FNode.Parents
                  local children::Children
                  local n::Node
                  local g::Graph
                   #=  type node present, update
                   =#
                @matchcontinue (inTypes, inParentRef, inName, inGraph) begin
                  (_, _, _, _)  => begin
                      pr = FNode.child(inParentRef, FNode.tyNodeName)
                      nr = FNode.child(pr, inName)
                      FNode.addTypesToRef(nr, inTypes)
                    inGraph
                  end

                  (_, _, _, g)  => begin
                      @shouldFail _ = FNode.child(inParentRef, FNode.tyNodeName)
                      (g, n) = FGraph.node(g, FNode.tyNodeName, list(inParentRef), FCore.ND(NONE()))
                      pr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.tyNodeName, pr)
                      (g, n) = FGraph.node(g, inName, list(pr), FCore.FT(inTypes))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(pr, inName, nr)
                    g
                  end

                  (_, _, _, g)  => begin
                      pr = FNode.child(inParentRef, FNode.tyNodeName)
                      @shouldFail _ = FNode.child(pr, inName)
                      (g, n) = FGraph.node(g, inName, list(pr), FCore.FT(inTypes))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(pr, inName, nr)
                    g
                  end

                  _  => begin
                        pr = FGraph.top(inGraph)
                        print("FGraphBuild.mkTypeNode: Error making type node: " + inName + " in parent: " + FNode.name(FNode.fromRef(pr)) + "\\n")
                      inGraph
                  end
                end
              end
               #=  search in the parent node for a child with name FNode.tyNodeName
               =#
               #=  search for the given name in FNode.tyNodeName
               =#
               #=  type node not present, add
               =#
               #=  search in the parent node for a child with name FNode.tyNodeName
               =#
               #=  add it
               =#
               #=  type node present, but inName not present in it
               =#
               #=  search in the parent node for a child with name FNode.tyNodeName
               =#
               #=  add it
               =#
          outGraph
        end

         #= equation node =#
        function mkEqNode(inName::Name, inEqs::List{<:SCode.Equation}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                @match (inName, inEqs, inParentRef, inKind, inGraph) begin
                  (_,  nil(), _, _, g)  => begin
                    g
                  end

                  (_, _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.EQ(inName, inEqs))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                      g = ListUtil.fold2(inEqs, analyseEquation, nr, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= algorithm node =#
        function mkAlNode(inName::Name, inAlgs::List{<:SCode.AlgorithmSection}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                @match (inName, inAlgs, inParentRef, inKind, inGraph) begin
                  (_,  nil(), _, _, g)  => begin
                    g
                  end

                  (_, _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.AL(inName, inAlgs))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                      g = ListUtil.fold2(inAlgs, analyseAlgorithm, nr, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= optimization node =#
        function mkOptNode(inName::Name, inConstraintLst::List{<:SCode.ConstraintSection}, inClsAttrs::List{<:Absyn.NamedArg}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                @match (inName, inConstraintLst, inClsAttrs, inParentRef, inKind, inGraph) begin
                  (_,  nil(),  nil(), _, _, g)  => begin
                    g
                  end

                  (_, _, _, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.OT(inConstraintLst, inClsAttrs))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                    g
                  end
                end
              end
          outGraph
        end

         #= optimization node =#
        function mkExternalNode(inName::Name, inExternalDeclOpt::Option{<:SCode.ExternalDecl}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                  local ed::SCode.ExternalDecl
                  local ocr::Option{Absyn.ComponentRef}
                  local oae::Option{Absyn.Exp}
                  local exps::List{Absyn.Exp}
                @match (inName, inExternalDeclOpt, inParentRef, inKind, inGraph) begin
                  (_, NONE(), _, _, g)  => begin
                    g
                  end

                  (_, SOME(ed && SCode.EXTERNALDECL(output_ = ocr, args = exps)), _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.ED(ed))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, nr)
                      oae = Util.applyOption(ocr, AbsynUtil.crefExp)
                      g = mkCrefsFromExps(ListUtil.consOption(oae, exps), nr, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

        function mkCrefsFromExps(inExps::List{<:Absyn.Exp}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local e::Absyn.Exp
                  local rest::List{Absyn.Exp}
                  local crefs::List{Absyn.ComponentRef}
                  local g::Graph
                @match (inExps, inParentRef, inKind, inGraph) begin
                  ( nil(), _, _, g)  => begin
                    g
                  end

                  (e <| rest, _, _, g)  => begin
                      crefs = AbsynUtil.getCrefFromExp(e, true, true)
                      g = mkCrefsNodes(crefs, inParentRef, inKind, g)
                      g = mkCrefsFromExps(rest, inParentRef, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= Recursively analyses an expression. =#
        function analyseExp(inExp::Absyn.Exp, inRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              (_, (_, _, outGraph)) = AbsynUtil.traverseExpBidir(inExp, analyseExpTraverserEnter, analyseExpTraverserExit, (inRef, inKind, inGraph))
          outGraph
        end

         #= Recursively analyses an optional expression. =#
        function analyseOptExp(inExp::Option{<:Absyn.Exp}, inRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local exp::Absyn.Exp
                  local g::Graph
                @match (inExp, inRef, inKind, inGraph) begin
                  (NONE(), _, _, g)  => begin
                    g
                  end

                  (SOME(exp), _, _, g)  => begin
                      g = analyseExp(exp, inRef, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= Traversal enter function for use in analyseExp. =#
        function analyseExpTraverserEnter(inExp::Absyn.Exp, inTuple::Tuple{<:Ref, Kind, Graph}) ::Tuple{Absyn.Exp, Tuple{Ref, Kind, Graph}}
              local outTuple::Tuple{Ref, Kind, Graph}
              local exp::Absyn.Exp

              local ref::Ref
              local k::Kind
              local g::Graph

              (ref, k, g) = inTuple
              g = analyseExp2(inExp, ref, k, g)
              exp = inExp
              outTuple = (ref, k, g)
          (exp, outTuple)
        end

         #= Helper function to analyseExp, does the actual work. =#
        function analyseExp2(inExp::Absyn.Exp, inRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local cref::Absyn.ComponentRef
                  local args::Absyn.FunctionArgs
                  local iters::Absyn.ForIterators
                  local ref::Ref
                  local g::Graph
                @match (inExp, inRef, inKind, inGraph) begin
                  (Absyn.CREF(componentRef = cref), _, _, g)  => begin
                      g = analyseCref(cref, inRef, inKind, g)
                    g
                  end

                  (Absyn.CALL(functionArgs = Absyn.FOR_ITER_FARG(iterators = iters)), _, _, g)  => begin
                      g = addIterators(iters, inRef, inKind, g)
                    g
                  end

                  (Absyn.CALL(function_ = cref), _, _, g)  => begin
                      g = analyseCref(cref, inRef, inKind, g)
                    g
                  end

                  (Absyn.PARTEVALFUNCTION(function_ = cref), _, _, g)  => begin
                      g = analyseCref(cref, inRef, inKind, g)
                    g
                  end

                  (Absyn.MATCHEXP(__), _, _, g)  => begin
                      g = addMatchScope(inExp, inRef, inKind, g)
                    g
                  end

                  _  => begin
                      inGraph
                  end
                end
              end
          outGraph
        end

         #= Analyses a component reference. =#
        function analyseCref(inCref::Absyn.ComponentRef, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local path::Absyn.Path
                  local ref::Ref
                  local g::Graph
                @matchcontinue (inCref, inParentRef, inKind, inGraph) begin
                  (Absyn.WILD(__), _, _, g)  => begin
                    g
                  end

                  (_, _, _, g)  => begin
                      g = mkCrefNode(inCref, inParentRef, inKind, g)
                    g
                  end
                end
              end
          outGraph
        end

         #= Traversal exit function for use in analyseExp. =#
        function analyseExpTraverserExit(inExp::Absyn.Exp, inTuple::Tuple{<:Ref, Kind, Graph}) ::Tuple{Absyn.Exp, Tuple{Ref, Kind, Graph}}
              local outTuple::Tuple{Ref, Kind, Graph}
              local outExp::Absyn.Exp

               #=  nothing to do here!
               =#
              outExp = inExp
              outTuple = inTuple
          (outExp, outTuple)
        end

         #= Analyses an equation. =#
        function analyseEquation(inEquation::SCode.Equation, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              local equ::SCode.EEquation

              @match SCode.EQUATION(equ) = inEquation
              (_, (_, (_, _, outGraph))) = SCodeUtil.traverseEEquations(equ, (analyseEEquationTraverser, (inParentRef, inKind, inGraph)))
          outGraph
        end

         #= Traversal function for use in analyseEquation. =#
        function analyseEEquationTraverser(inTuple::Tuple{<:SCode.EEquation, Tuple{<:Ref, Kind, Graph}}) ::Tuple{SCode.EEquation, Tuple{Ref, Kind, Graph}}
              local outTuple::Tuple{SCode.EEquation, Tuple{Ref, Kind, Graph}}

              outTuple = begin
                  local equ::SCode.EEquation
                  local equf::SCode.EEquation
                  local equr::SCode.EEquation
                  local iter_name::SCode.Ident
                  local ref::Ref
                  local info::SourceInfo
                  local cref1::Absyn.ComponentRef
                  local g::Graph
                  local k::Kind
                @match inTuple begin
                  (equf && SCode.EQ_FOR(index = iter_name), (ref, k, g))  => begin
                      g = addIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), ref, k, g)
                      (equ, (_, _, g)) = SCodeUtil.traverseEEquationExps(equf, traverseExp, (ref, k, g))
                    (equ, (ref, k, g))
                  end

                  (equr && SCode.EQ_REINIT(cref = Absyn.CREF(componentRef = cref1)), (ref, k, g))  => begin
                      g = analyseCref(cref1, ref, k, g)
                      (equ, (_, _, g)) = SCodeUtil.traverseEEquationExps(equr, traverseExp, (ref, k, g))
                    (equ, (ref, k, g))
                  end

                  (equ, (ref, k, g))  => begin
                      _ = SCodeUtil.getEEquationInfo(equ)
                      (equ, (_, _, g)) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (ref, k, g))
                    (equ, (ref, k, g))
                  end
                end
              end
          outTuple
        end

         #= Traversal function used by analyseEEquationTraverser and
          analyseStatementTraverser. =#
        function traverseExp(inExp::Absyn.Exp, inTuple::Tuple{<:Ref, Kind, Graph}) ::Tuple{Absyn.Exp, Tuple{Ref, Kind, Graph}}
              local outTuple::Tuple{Ref, Kind, Graph}
              local outExp::Absyn.Exp

              (outExp, outTuple) = AbsynUtil.traverseExpBidir(inExp, analyseExpTraverserEnter, analyseExpTraverserExit, inTuple)
          (outExp, outTuple)
        end

         #= Analyses an algorithm. =#
        function analyseAlgorithm(inAlgorithm::SCode.AlgorithmSection, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              local stmts::List{SCode.Statement}

              @match SCode.ALGORITHM(stmts) = inAlgorithm
              outGraph = ListUtil.fold2(stmts, analyseStatement, inParentRef, inKind, inGraph)
          outGraph
        end

         #= Analyses a statement in an algorithm. =#
        function analyseStatement(inStatement::SCode.Statement, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              (_, (_, (_, _, outGraph))) = SCodeUtil.traverseStatements(inStatement, (analyseStatementTraverser, (inParentRef, inKind, inGraph)))
          outGraph
        end

         #= Traversal function used by analyseStatement. =#
        function analyseStatementTraverser(inTuple::Tuple{<:SCode.Statement, Tuple{<:Ref, Kind, Graph}}) ::Tuple{SCode.Statement, Tuple{Ref, Kind, Graph}}
              local outTuple::Tuple{SCode.Statement, Tuple{Ref, Kind, Graph}}

              outTuple = begin
                  local ref::Ref
                  local stmt::SCode.Statement
                  local info::SourceInfo
                  local parforBody::List{SCode.Statement}
                  local iter_name::String
                  local g::Graph
                  local k::Kind
                @match inTuple begin
                  (stmt && SCode.ALG_FOR(index = iter_name), (ref, k, g))  => begin
                      g = addIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), ref, k, g)
                      (_, (_, _, g)) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (ref, k, g))
                    (stmt, (ref, k, g))
                  end

                  (stmt && SCode.ALG_PARFOR(index = iter_name), (ref, k, g))  => begin
                      g = addIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), ref, k, g)
                      (_, (_, _, g)) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (ref, k, g))
                    (stmt, (ref, k, g))
                  end

                  (stmt, (ref, k, g))  => begin
                      _ = SCodeUtil.getStatementInfo(stmt)
                      (_, (_, _, g)) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (ref, k, g))
                    (stmt, (ref, k, g))
                  end
                end
              end
          outTuple
        end

         #= adds iterators nodes =#
        function addIterators(inIterators::Absyn.ForIterators, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local g::Graph
                  local n::Node
                  local nr::Ref
                  local i::Absyn.ForIterators
                   #=  FNode.forNodeName already present!
                   =#
                @matchcontinue (inIterators, inParentRef, inKind, inGraph) begin
                  (_, _, _, g)  => begin
                      nr = FNode.child(inParentRef, FNode.forNodeName)
                      FNode.addIteratorsToRef(nr, inIterators)
                      g = addIterators_helper(inIterators, nr, inKind, g)
                    g
                  end

                  (_, _, _, g)  => begin
                      (g, n) = FGraph.node(g, FNode.forNodeName, list(inParentRef), FCore.FS(inIterators))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, FNode.forNodeName, nr)
                      g = addIterators_helper(inIterators, nr, inKind, g)
                    g
                  end
                end
              end
               #=  FNode.forNodeName not present, add it
               =#
          outGraph
        end

        function addIterators_helper(inIterators::Absyn.ForIterators, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local name::Name
                  local rest::List{Absyn.ForIterator}
                  local i::Absyn.ForIterator
                  local e::Absyn.Exp
                  local g::Graph
                  local cr::Absyn.ComponentRef
                   #=  we're done
                   =#
                @match (inIterators, inParentRef, inKind, inGraph) begin
                  ( nil(), _, _, g)  => begin
                    g
                  end

                  (i && Absyn.ITERATOR(name = name) <| rest, _, _, g)  => begin
                      (g, n) = FGraph.node(g, name, list(inParentRef), FCore.FI(i))
                      nr = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, name, nr)
                      g = addIterators_helper(rest, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  iterator::rest
               =#
          outGraph
        end

         #= Extends the node with a match-expression, i.e. opens a new scope and
         adds the local declarations in the match to it. =#
        function addMatchScope(inMatchExp::Absyn.Exp, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              local n::Node
              local nr::Ref
              local local_decls::List{Absyn.ElementItem}
              local g::Graph

              (g, n) = FGraph.node(inGraph, FNode.matchNodeName, list(inParentRef), FCore.MS(inMatchExp))
              nr = FNode.toRef(n)
              FNode.addChildRef(inParentRef, FNode.matchNodeName, nr)
              @match Absyn.MATCHEXP(localDecls = local_decls) = inMatchExp
              outGraph = addMatchScope_helper(local_decls, nr, inKind, g)
          outGraph
        end

        function addMatchScope_helper(inElements::List{<:Absyn.ElementItem}, inParentRef::Ref, inKind::Kind, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local nr::Ref
                  local name::Name
                  local element::Absyn.Element
                  local rest::List{Absyn.ElementItem}
                  local i::Absyn.ForIterator
                  local e::Absyn.Exp
                  local g::Graph
                  local cr::Absyn.ComponentRef
                  local el::List{SCode.Element}
                   #=  we're done
                   =#
                @match (inElements, inParentRef, inKind, inGraph) begin
                  ( nil(), _, _, g)  => begin
                    g
                  end

                  (Absyn.ELEMENTITEM(element = element) <| rest, _, _, g)  => begin
                      el = AbsynToSCode.translateElement(element, SCode.PROTECTED())
                      g = ListUtil.fold2(el, mkElementNode, inParentRef, inKind, g)
                      g = addMatchScope_helper(rest, inParentRef, inKind, g)
                    g
                  end

                  (_ <| rest, _, _, g)  => begin
                      g = addMatchScope_helper(rest, inParentRef, inKind, g)
                    g
                  end
                end
              end
               #=  el::rest
               =#
               #=  Translate the element item to a SCode element.
               =#
               #=  el::rest
               =#
          outGraph
        end

        function mkRefNode(inName::Name, inTargetScope::Scope, inParentRef::Ref, inGraph::Graph) ::Graph
              local outGraph::Graph

              outGraph = begin
                  local n::Node
                  local rn::Ref
                  local rc::Ref
                  local g::Graph
                @match (inName, inTargetScope, inParentRef, inGraph) begin
                  (_, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.REF(inTargetScope))
                      rn = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, rn)
                    g
                  end
                end
              end
               #=  make a ref
               =#
               #=  add the ref node
               =#
          outGraph
        end

        function mkAssertNode(inName::Name, inMessage::String, inParentRef::Ref, inGraph::Graph) ::Tuple{Graph, Ref}
              local outRef::Ref
              local outGraph::Graph

              (outGraph, outRef) = begin
                  local n::Node
                  local rn::Ref
                  local rc::Ref
                  local g::Graph
                @match (inName, inMessage, inParentRef, inGraph) begin
                  (_, _, _, g)  => begin
                      (g, n) = FGraph.node(g, inName, list(inParentRef), FCore.ASSERT(inMessage))
                      rn = FNode.toRef(n)
                      FNode.addChildRef(inParentRef, inName, rn)
                    (g, rn)
                  end
                end
              end
               #=  make a ref
               =#
               #=  add the ref node
               =#
          (outGraph, outRef)
        end

         #= /*
        public function mkCloneNode
        \"@author: adrpo
         clone the target ref
         ignore basic types\"
          input Name inName;
          input Ref inTargetRef;
          input Ref inParentRef;
          input Graph inGraph;
          output Graph outGraph;
          output Ref outCloneRef;
        algorithm
          (outGraph, outCloneRef) := matchcontinue(inName, inTargetRef, inParentRef, inGraph)
            local
              Node n;
              Ref rn, rc;
              Graph g;
              Children kids;

             not in section (eq or alg), modifiers or dimensions/subscripts
            case (_, _, _, g)
              equation
                false = FNode.isRefIn(inParentRef, FNode.isRefSection);
                false = FNode.isRefIn(inParentRef, FNode.isRefMod);
                false = FNode.isRefIn(inParentRef, FNode.isRefDims);
                false = FNode.isRefIn(inParentRef, FNode.isRefDerived);
                false = FNode.isRefIn(inParentRef, FNode.isRefFunction);
                true = not FNode.isRefBasicType(inTargetRef) and
                       not FNode.isRefBuiltin(inTargetRef) and
                       not FNode.isRefComponent(inTargetRef) and
                       not FNode.isRefConstrainClass(inTargetRef) and
                       not FNode.isRefFunction(inTargetRef);

                print(\"Cloning: \" + FNode.toPathStr(FNode.fromRef(inTargetRef)) + \"/\" + FNode.toStr(FNode.fromRef(inTargetRef)) + \"\\n\\t\" +
                      \"Scope: \" + FNode.toPathStr(FNode.fromRef(inParentRef)) + \"/\" + FNode.toStr(FNode.fromRef(inParentRef)) + \"\\n\");
                (g, n) = FGraph.node(g, inName, {inParentRef}, FCore.CLONE(inTargetRef));
                 make a ref
                rn = FNode.toRef(n);
                 add the ref node
                FNode.addChildRef(inParentRef, inName, rn);
                 clone ref target node children
                (g, kids) = FNode.cloneTree(FNode.children(FNode.fromRef(inTargetRef)), rn, g);
                rn = FNode.updateRef(rn, FNode.setChildren(n, kids));
              then
                (g, rn);

            else (inGraph, inTargetRef);

          end matchcontinue;
        end mkCloneNode;
        */ =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

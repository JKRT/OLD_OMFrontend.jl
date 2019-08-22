  module FMod 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

         #= /*
         * This file is part of OpenModelica.
         *
         * Copyright (c) 1998-CurrentYear, Linköping University,
         * Department of Computer and Information Science,
         * SE-58183 Linköping, Sweden.
         *
         * All rights reserved.
         *
         * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3
         * AND THIS OSMC PUBLIC LICENSE (OSMC-PL).
         * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
         * ACCEPTANCE OF THE OSMC PUBLIC LICENSE.
         *
         * The OpenModelica software and the Open Source Modelica
         * Consortium (OSMC) Public License (OSMC-PL) are obtained
         * from Linköping University, either from the above address,
         * from the URLs: http:www.ida.liu.se/projects/OpenModelica or
         * http:www.openmodelica.org, and in the OpenModelica distribution.
         * GNU version 3 is obtained from: http:www.gnu.org/copyleft/gpl.html.
         *
         * This program is distributed WITHOUT ANY WARRANTY; without
         * even the implied warranty of  MERCHANTABILITY or FITNESS
         * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
         * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
         * OF OSMC-PL.
         *
         * See the full OSMC Public License conditions for more details.
         *
         */ =#
         #=  public imports
         =#

        import Absyn
        import AbsynUtil
        import SCode
        import FCore
         #=  protected imports
         =#

        import ListUtil
        import Error
        import SCodeUtil

        Name = FCore.Name 
        Id = FCore.Id 
        Seq = FCore.Seq 
        Next = FCore.Next 
        Node = FCore.Node 
        Data = FCore.Data 
        Kind = FCore.Kind 
        Ref = FCore.Ref 
        Refs = FCore.Refs 
        Children = FCore.Children 
        Parents = FCore.Parents 
        Scope = FCore.Scope 
        ImportTable = FCore.ImportTable 
        Graph = FCore.Graph 
        Extra = FCore.Extra 
        Visited = FCore.Visited 
        Import = FCore.Import 
        AvlTree = FCore.CAvlTree 
        AvlKey = FCore.CAvlKey 
        AvlValue = FCore.CAvlValue 
        AvlTreeValue = FCore.CAvlTreeValue 
        ModScope = FCore.ModScope 

         #= @author: adrpo
         merge 2 modifiers, one outer one inner =#
        function merge(inParentRef::Ref, inOuterModRef::Ref, inInnerModRef::Ref, inGraph::Graph) ::Tuple{Graph, Ref} 
              local outMergedModRef::Ref
              local outGraph::Graph

              (outGraph, outMergedModRef) = begin
                  local r::Ref
                  local g::Graph
                @match (inParentRef, inOuterModRef, inInnerModRef, inGraph) begin
                  (r, _, _, g)  => begin
                    (g, r)
                  end
                end
              end
          (outGraph, outMergedModRef)
        end

         #= @author: adrpo
         apply the modifier to the given target =#
        function apply(inTargetRef::Ref, inModRef::Ref, inGraph::Graph) ::Tuple{Graph, Ref} 
              local outNodeRef::Ref
              local outGraph::Graph

              (outGraph, outNodeRef) = begin
                  local r::Ref
                  local g::Graph
                @match (inTargetRef, inModRef, inGraph) begin
                  (r, _, g)  => begin
                    (g, r)
                  end
                end
              end
          (outGraph, outNodeRef)
        end

         #= This function merges the submodifiers in a modifier so that each submodifier
            only occurs once. Ex:

            compactMod({x.start = 2.0, y = 4.0, x(min = 1.0, max = 3.0)}) =>
              {x(start = 2.0, min = 1.0, max = 3.0), y = 4.0}

           =#
        function compactSubMods(inSubMods::List{<:SCode.SubMod}, inModScope::ModScope) ::List{SCode.SubMod} 
              local outSubMods::List{SCode.SubMod}

              local submods::List{SCode.SubMod}

              submods = ListUtil.fold2(inSubMods, compactSubMod, inModScope, nil, nil)
              outSubMods = listReverse(submods)
          outSubMods
        end

         #= Helper function to compactSubMods. Tries to merge the given modifier with an
           existing modifier in the accumulation list. If a matching modifier is not
           found in the list it's added instead. =#
        function compactSubMod(inSubMod::SCode.SubMod, inModScope::ModScope, inName::List{<:String}, inAccumMods::List{<:SCode.SubMod}) ::List{SCode.SubMod} 
              local outSubMods::List{SCode.SubMod}

              local name::String
              local submods::List{SCode.SubMod}
              local found::Bool

              @match SCode.NAMEMOD(name, _) = inSubMod
              (submods, found) = ListUtil.findMap3(inAccumMods, compactSubMod2, inSubMod, inModScope, inName)
              outSubMods = ListUtil.consOnTrue(! found, inSubMod, submods)
          outSubMods
        end

         #= Helper function to compactSubMod. Merges the given modifier with the existing
            modifier if they have the same name, otherwise does nothing. =#
        function compactSubMod2(inExistingMod::SCode.SubMod, inNewMod::SCode.SubMod, inModScope::ModScope, inName::List{<:String}) ::Tuple{SCode.SubMod, Bool} 
              local outFound::Bool
              local outMod::SCode.SubMod

              (outMod, outFound) = begin
                  local name1::String
                  local name2::String
                  local submod::SCode.SubMod
                @matchcontinue (inExistingMod, inNewMod, inModScope, inName) begin
                  (SCode.NAMEMOD(ident = name1), SCode.NAMEMOD(ident = name2), _, _)  => begin
                      @match false = stringEqual(name1, name2)
                    (inExistingMod, false)
                  end
                  
                  (SCode.NAMEMOD(ident = name1), _, _, _)  => begin
                      submod = mergeSubModsInSameScope(inExistingMod, inNewMod, _cons(name1, inName), inModScope)
                    (submod, true)
                  end
                end
              end
          (outMod, outFound)
        end

         #= Merges two submodifiers in the same scope, i.e. they have the same priority.
           It's thus an error if the modifiers modify the same element. =#
        function mergeSubModsInSameScope(inMod1::SCode.SubMod, inMod2::SCode.SubMod, inElementName::List{<:String}, inModScope::ModScope) ::SCode.SubMod 
              local outMod::SCode.SubMod

              outMod = begin
                  local id::String
                  local scope::String
                  local name::String
                  local fp::SCode.Final
                  local ep::SCode.Each
                  local submods1::List{SCode.SubMod}
                  local submods2::List{SCode.SubMod}
                  local binding::Option{Absyn.Exp}
                  local info1::SourceInfo
                  local info2::SourceInfo
                  local mod1::SCode.Mod
                  local mod2::SCode.Mod
                   #=  The second modifier has no binding, use the binding from the first.
                   =#
                @match (inMod1, inMod2, inElementName, inModScope) begin
                  (SCode.NAMEMOD(id, SCode.MOD(fp, ep, submods1, binding, info1)), SCode.NAMEMOD(mod = SCode.MOD(subModLst = submods2, binding = NONE())), _, _)  => begin
                      submods1 = ListUtil.fold2(submods1, compactSubMod, inModScope, inElementName, submods2)
                    SCode.NAMEMOD(id, SCode.MOD(fp, ep, submods1, binding, info1))
                  end
                  
                  (SCode.NAMEMOD(mod = SCode.MOD(subModLst = submods1, binding = NONE())), SCode.NAMEMOD(id, SCode.MOD(fp, ep, submods2, binding, info2)), _, _)  => begin
                      submods1 = ListUtil.fold2(submods1, compactSubMod, inModScope, inElementName, submods2)
                    SCode.NAMEMOD(id, SCode.MOD(fp, ep, submods1, binding, info2))
                  end
                  
                  (SCode.NAMEMOD(mod = mod1), SCode.NAMEMOD(mod = mod2), _, _)  => begin
                      info1 = SCodeUtil.getModifierInfo(mod1)
                      info2 = SCodeUtil.getModifierInfo(mod2)
                      scope = printModScope(inModScope)
                      name = stringDelimitList(listReverse(inElementName), ".")
                      Error.addMultiSourceMessage(Error.DUPLICATE_MODIFICATIONS, list(name, scope), list(info2, info1))
                    fail()
                  end
                end
              end
               #=  The first modifier has no binding, use the binding from the second.
               =#
               #=  The first modifier has no binding, use the binding from the second.
               =#
          outMod
        end

        function printModScope(inModScope::ModScope) ::String 
              local outString::String

              outString = begin
                  local name::String
                  local path::Absyn.Path
                @match inModScope begin
                  FCore.MS_COMPONENT(name = name)  => begin
                    "component " + name
                  end
                  
                  FCore.MS_EXTENDS(path = path)  => begin
                    "extends " + AbsynUtil.pathString(path)
                  end
                  
                  FCore.MS_DERIVED(path = path)  => begin
                    "inherited class " + AbsynUtil.pathString(path)
                  end
                  
                  FCore.MS_CLASS_EXTENDS(name = name)  => begin
                    "class extends class " + name
                  end
                  
                  FCore.MS_CONSTRAINEDBY(path = path)  => begin
                    "constrainedby class " + AbsynUtil.pathString(path)
                  end
                end
              end
          outString
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
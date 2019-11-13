  module SCodeInstUtil 


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

        import ListUtil
        import SCodeDump
        import SCodeUtil

         #= @author: adrpo
         keeps the constant binding and if not returns none =#
        function constantBindingOrNone(inBinding::Option{<:Absyn.Exp}) ::Option{Absyn.Exp} 
              local outBinding::Option{Absyn.Exp}

              outBinding = begin
                  local e::Absyn.Exp
                   #=  keep it
                   =#
                @match inBinding begin
                  SOME(e)  => begin
                    if listEmpty(AbsynUtil.getCrefFromExp(e, true, true))
                          inBinding
                        else
                          NONE()
                        end
                  end
                  
                  _  => begin
                      NONE()
                  end
                end
              end
               #=  else
               =#
          outBinding
        end

         #= @author: adrpo
         keeps the redeclares and removes all non-constant bindings!
         if onlyRedeclare is true then bindings are removed completely! =#
        function removeNonConstantBindingsKeepRedeclares(inMod::SCode.Mod, onlyRedeclares::Bool) ::SCode.Mod 
              local outMod::SCode.Mod

              outMod = begin
                  local sl::List{SCode.SubMod}
                  local fp::SCode.Final
                  local ep::SCode.Each
                  local i::SourceInfo
                  local binding::Option{Absyn.Exp}
                @match (inMod, onlyRedeclares) begin
                  (SCode.MOD(fp, ep, sl, binding, i), _)  => begin
                      binding = if onlyRedeclares
                            NONE()
                          else
                            constantBindingOrNone(binding)
                          end
                      sl = removeNonConstantBindingsKeepRedeclaresFromSubMod(sl, onlyRedeclares)
                    SCode.MOD(fp, ep, sl, binding, i)
                  end
                  
                  (SCode.REDECL(__), _)  => begin
                    inMod
                  end
                  
                  _  => begin
                      inMod
                  end
                end
              end
          outMod
        end

         #= @author: adrpo
         removes the non-constant bindings in submods and keeps the redeclares =#
        function removeNonConstantBindingsKeepRedeclaresFromSubMod(inSl::List{<:SCode.SubMod}, onlyRedeclares::Bool) ::List{SCode.SubMod} 
              local outSl::List{SCode.SubMod}

              outSl = begin
                  local n::String
                  local sl::List{SCode.SubMod}
                  local rest::List{SCode.SubMod}
                  local m::SCode.Mod
                  local ssl::List{SCode.Subscript}
                @match (inSl, onlyRedeclares) begin
                  ( nil(), _)  => begin
                    nil
                  end
                  
                  (SCode.NAMEMOD(n, m) <| rest, _)  => begin
                      m = removeNonConstantBindingsKeepRedeclares(m, onlyRedeclares)
                      sl = removeNonConstantBindingsKeepRedeclaresFromSubMod(rest, onlyRedeclares)
                    _cons(SCode.NAMEMOD(n, m), sl)
                  end
                end
              end
          outSl
        end

         #= add the redeclare-as-element elements to extends =#
        function addRedeclareAsElementsToExtends(inElements::List{<:SCode.Element}, redeclareElements::List{<:SCode.Element}) ::List{SCode.Element} 
              local outExtendsElements::List{SCode.Element}

              outExtendsElements = begin
                  local el::SCode.Element
                  local redecls::List{SCode.Element}
                  local rest::List{SCode.Element}
                  local out::List{SCode.Element}
                  local baseClassPath::Absyn.Path
                  local visibility::SCode.Visibility
                  local mod::SCode.Mod
                  local ann::Option{SCode.Annotation} #= the extends annotation =#
                  local info::SourceInfo
                  local redeclareMod::SCode.Mod
                  local submods::List{SCode.SubMod}
                   #=  empty, return the same
                   =#
                @match (inElements, redeclareElements) begin
                  (_,  nil())  => begin
                    inElements
                  end
                  
                  ( nil(), _)  => begin
                    nil
                  end
                  
                  (SCode.EXTENDS(baseClassPath, visibility, mod, ann, info) <| rest, redecls)  => begin
                      submods = makeElementsIntoSubMods(SCode.NOT_FINAL(), SCode.NOT_EACH(), redecls)
                      redeclareMod = SCode.MOD(SCode.NOT_FINAL(), SCode.NOT_EACH(), submods, NONE(), info)
                      mod = SCodeUtil.myMergeSCodeMods(redeclareMod, mod)
                      out = addRedeclareAsElementsToExtends(rest, redecls)
                    _cons(SCode.EXTENDS(baseClassPath, visibility, mod, ann, info), out)
                  end
                  
                  (el <| rest, redecls)  => begin
                      out = addRedeclareAsElementsToExtends(rest, redecls)
                    _cons(el, out)
                  end
                end
              end
               #=  empty elements
               =#
               #=  we got some
               =#
               #=  ignore non-extends
               =#
          outExtendsElements
        end

         #= transform elements into submods with named mods =#
        function makeElementsIntoSubMods(inFinal::SCode.Final, inEach::SCode.Each, inElements::List{<:SCode.Element}) ::List{SCode.SubMod} 
              local outSubMods::List{SCode.SubMod}

              outSubMods = begin
                  local el::SCode.Element
                  local rest::List{SCode.Element}
                  local f::SCode.Final
                  local e::SCode.Each
                  local n::SCode.Ident
                  local newSubMods::List{SCode.SubMod}
                   #=  empty
                   =#
                @match (inFinal, inEach, inElements) begin
                  (_, _,  nil())  => begin
                    nil
                  end
                  
                  (f, e, el && SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__)) <| rest)  => begin
                      print("- AbsynToSCode.makeElementsIntoSubMods ignoring class-extends redeclare-as-element: " + SCodeDump.unparseElementStr(el, SCodeDump.defaultOptions) + "\\n")
                      newSubMods = makeElementsIntoSubMods(f, e, rest)
                    newSubMods
                  end
                  
                  (f, e, el && SCode.COMPONENT(name = n) <| rest)  => begin
                      newSubMods = makeElementsIntoSubMods(f, e, rest)
                    _cons(SCode.NAMEMOD(n, SCode.REDECL(f, e, el)), newSubMods)
                  end
                  
                  (f, e, el && SCode.CLASS(name = n) <| rest)  => begin
                      newSubMods = makeElementsIntoSubMods(f, e, rest)
                    _cons(SCode.NAMEMOD(n, SCode.REDECL(f, e, el)), newSubMods)
                  end
                  
                  (f, e, el <| rest)  => begin
                      print("- AbsynToSCode.makeElementsIntoSubMods ignoring redeclare-as-element redeclaration: " + SCodeDump.unparseElementStr(el, SCodeDump.defaultOptions) + "\\n")
                      newSubMods = makeElementsIntoSubMods(f, e, rest)
                    newSubMods
                  end
                end
              end
               #=  class extends, error!
               =#
               #=  print an error here
               =#
               #=  recurse
               =#
               #=  component
               =#
               #=  recurse
               =#
               #=  class
               =#
               #=  recurse
               =#
               #=  rest
               =#
               #=  print an error here
               =#
               #=  recurse
               =#
          outSubMods
        end

         #= @author: adrpo
         remove the binding that contains a cref =#
        function removeReferenceInBinding(inBinding::Option{<:Absyn.Exp}, inCref::Absyn.ComponentRef) ::Option{Absyn.Exp} 
              local outBinding::Option{Absyn.Exp}

              outBinding = begin
                  local e::Absyn.Exp
                  local crlst1::List{Absyn.ComponentRef}
                  local crlst2::List{Absyn.ComponentRef}
                   #=  if cref is not present keep the binding!
                   =#
                @match inBinding begin
                  SOME(e)  => begin
                      crlst1 = AbsynUtil.getCrefFromExp(e, true, true)
                      crlst2 = AbsynUtil.removeCrefFromCrefs(crlst1, inCref)
                    if intEq(listLength(crlst1), listLength(crlst2))
                          inBinding
                        else
                          NONE()
                        end
                  end
                  
                  _  => begin
                      NONE()
                  end
                end
              end
               #=  else
               =#
          outBinding
        end

         #= @author: adrpo
         remove the self reference from mod! =#
        function removeSelfReferenceFromMod(inMod::SCode.Mod, inCref::Absyn.ComponentRef) ::SCode.Mod 
              local outMod::SCode.Mod

              outMod = begin
                  local sl::List{SCode.SubMod}
                  local fp::SCode.Final
                  local ep::SCode.Each
                  local i::SourceInfo
                  local binding::Option{Absyn.Exp}
                @match (inMod, inCref) begin
                  (SCode.MOD(fp, ep, sl, binding, i), _)  => begin
                      binding = removeReferenceInBinding(binding, inCref)
                      sl = removeSelfReferenceFromSubMod(sl, inCref)
                    SCode.MOD(fp, ep, sl, binding, i)
                  end
                  
                  (SCode.REDECL(__), _)  => begin
                    inMod
                  end
                  
                  _  => begin
                      inMod
                  end
                end
              end
          outMod
        end

         #= @author: adrpo
         removes the self references from a submod =#
        function removeSelfReferenceFromSubMod(inSl::List{<:SCode.SubMod}, inCref::Absyn.ComponentRef) ::List{SCode.SubMod} 
              local outSl::List{SCode.SubMod}

              outSl = begin
                  local n::String
                  local sl::List{SCode.SubMod}
                  local rest::List{SCode.SubMod}
                  local m::SCode.Mod
                  local ssl::List{SCode.Subscript}
                @match (inSl, inCref) begin
                  ( nil(), _)  => begin
                    nil
                  end
                  
                  (SCode.NAMEMOD(n, m) <| rest, _)  => begin
                      m = removeSelfReferenceFromMod(m, inCref)
                      sl = removeSelfReferenceFromSubMod(rest, inCref)
                    _cons(SCode.NAMEMOD(n, m), sl)
                  end
                end
              end
          outSl
        end

        function expandEnumerationSubMod(inSubMod::SCode.SubMod, inChanged::Bool) ::Tuple{SCode.SubMod, Bool} 
              local outChanged::Bool
              local outSubMod::SCode.SubMod

              (outSubMod, outChanged) = begin
                  local mod::SCode.Mod
                  local mod1::SCode.Mod
                  local ident::SCode.Ident
                @match inSubMod begin
                  SCode.NAMEMOD(ident = ident, mod = mod)  => begin
                      mod1 = expandEnumerationMod(mod)
                    if referenceEq(mod, mod1)
                          (inSubMod, inChanged)
                        else
                          (SCode.NAMEMOD(ident, mod1), true)
                        end
                  end
                  
                  _  => begin
                      (inSubMod, inChanged)
                  end
                end
              end
          (outSubMod, outChanged)
        end

        function expandEnumerationMod(inMod::SCode.Mod) ::SCode.Mod 
              local outMod::SCode.Mod

              local f::SCode.Final
              local e::SCode.Each
              local el::SCode.Element
              local el1::SCode.Element
              local submod::List{SCode.SubMod}
              local binding::Option{Absyn.Exp}
              local info::SourceInfo
              local changed::Bool

              outMod = begin
                @match inMod begin
                  SCode.REDECL(f, e, el)  => begin
                      el1 = expandEnumerationClass(el)
                    if referenceEq(el, el1)
                          inMod
                        else
                          SCode.REDECL(f, e, el1)
                        end
                  end
                  
                  SCode.MOD(f, e, submod, binding, info)  => begin
                      (submod, changed) = ListUtil.mapFold(submod, expandEnumerationSubMod, false)
                    if changed
                          SCode.MOD(f, e, submod, binding, info)
                        else
                          inMod
                        end
                  end
                  
                  _  => begin
                      inMod
                  end
                end
              end
          outMod
        end

         #= @author: PA, adrpo
         this function expands the enumeration from a list into a class with components
         if the class is not an enumeration is kept as it is =#
        function expandEnumerationClass(inElement::SCode.Element) ::SCode.Element 
              local outElement::SCode.Element

              outElement = begin
                  local n::SCode.Ident
                  local l::List{SCode.Enum}
                  local cmt::SCode.Comment
                  local info::SourceInfo
                  local c::SCode.Element
                  local prefixes::SCode.Prefixes
                  local m::SCode.Mod
                  local m1::SCode.Mod
                  local p::Absyn.Path
                  local v::SCode.Visibility
                  local ann::Option{SCode.Annotation}
                @match inElement begin
                  SCode.CLASS(name = n, restriction = SCode.R_TYPE(__), prefixes = prefixes, classDef = SCode.ENUMERATION(enumLst = l), cmt = cmt, info = info)  => begin
                      c = expandEnumeration(n, l, prefixes, cmt, info)
                    c
                  end
                  
                  SCode.EXTENDS(baseClassPath = p, visibility = v, modifications = m, ann = ann, info = info)  => begin
                      m1 = expandEnumerationMod(m)
                    if referenceEq(m, m1)
                          inElement
                        else
                          SCode.EXTENDS(p, v, m1, ann, info)
                        end
                  end
                  
                  _  => begin
                      inElement
                  end
                end
              end
          outElement
        end

         #= author: PA
          This function takes an Ident and list of strings, and returns an enumeration class. =#
        function expandEnumeration(n::SCode.Ident, l::List{<:SCode.Enum}, prefixes::SCode.Prefixes, cmt::SCode.Comment, info::SourceInfo) ::SCode.Element 
              local outClass::SCode.Element

              outClass = SCode.CLASS(n, prefixes, SCode.NOT_ENCAPSULATED(), SCode.NOT_PARTIAL(), SCode.R_ENUMERATION(), makeEnumParts(l, info), cmt, info)
          outClass
        end

        function makeEnumParts(inEnumLst::List{<:SCode.Enum}, info::SourceInfo) ::SCode.ClassDef 
              local classDef::SCode.ClassDef

              classDef = SCode.PARTS(makeEnumComponents(inEnumLst, info), nil, nil, nil, nil, nil, nil, NONE())
          classDef
        end

         #= Translates a list of Enums to a list of elements of type EnumType. =#
        function makeEnumComponents(inEnumLst::List{<:SCode.Enum}, info::SourceInfo) ::List{SCode.Element} 
              local outSCodeElementLst::List{SCode.Element}

              outSCodeElementLst = list(SCodeUtil.makeEnumType(e, info) for e in inEnumLst)
          outSCodeElementLst
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
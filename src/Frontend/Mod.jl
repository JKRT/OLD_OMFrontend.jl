  module Mod


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    import Setfield

    @UniontypeDecl ModScope
    @UniontypeDecl FullMod

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

        import DAE

        import FCore

        import FNode

        import FGraphUtil

        import Prefix

        import SCode

        import InnerOuterTypes

        import CrefForHashTable
        println("MOD:1 before instancehierarchy")
        const InstanceHierarchy = InnerOuterTypes.InstHierarchy  #= an instance hierarchy =#
        println("MOD:2 after instancehierarchy")
        import Ceval

        import ClassInf

        import Config

        import Dump

        import Debug

        import Error

        import Expression

        import ExpressionDump

        import ExpressionSimplify

        import Flags

        #TODO: Fixme
        #import Inst

        #TODO: Fixme
        #import InstUtil

        import ListUtil

        import PrefixUtil

        import Print
        import SCodeInstUtil
        import SCodeUtil

        import Static

        import Types

        import Util

        import Values

        import ValuesUtil

        import System

        import SCodeDump

        import Lookup

          #= Used to know where a modifier came from, for error reporting. =#
         @Uniontype ModScope begin
              @Record COMPONENT begin

                       name::String
              end

              @Record EXTENDS begin

                       path::Absyn.Path
              end

              @Record DERIVED begin

                       path::Absyn.Path
              end
         end

          #= used for error reporting =#
         @Uniontype FullMod begin
              @Record MOD begin

                       cref::DAE.ComponentRef
                       mod::DAE.Mod
              end

              @Record SUB_MOD begin

                       cref::DAE.ComponentRef
                       subMod::DAE.SubMod
              end
         end

        SubMod = DAE.SubMod

        EqMod = DAE.EqMod

         #=
          This function elaborates on the expressions in a modification and
          turns them into global expressions.  This is done because the
          expressions in modifications must be elaborated on in the context
          they are provided in, and not the context they are used in. =#
        function elabMod(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inMod::SCode.Mod, inBoolean::Bool, inModScope::ModScope, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Mod}
              local outMod::DAE.Mod
              local outCache::FCore.Cache

              local mod::SCode.Mod

              mod = SCodeInstUtil.expandEnumerationMod(inMod)
              (outCache, outMod) = begin
                  local impl::Bool
                  local finalPrefix::SCode.Final
                  local subs_1::List{DAE.SubMod}
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local m::SCode.Mod
                  local each_::SCode.Each
                  local subs::List{SCode.SubMod}
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local prop::DAE.Properties
                  local e_val::Option{Values.Value}
                  local e::Absyn.Exp
                  local elem::SCode.Element
                  local dm::DAE.Mod
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local info::SourceInfo
                  local str::String
                   #=  no modifications
                   =#
                @match (inCache, inEnv, inIH, inPrefix, mod, inBoolean, inModScope, inInfo) begin
                  (cache, _, _, _, SCode.NOMOD(__), _, _, _)  => begin
                    (cache, DAE.NOMOD())
                  end

                  (cache, env, ih, pre, SCode.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = NONE(), info = info), impl, _, _)  => begin
                      (cache, subs_1) = elabSubmods(cache, env, ih, pre, subs, impl, inModScope, info)
                    (cache, DAE.MOD(finalPrefix, each_, subs_1, NONE(), info))
                  end

                  (cache, env, ih, pre, SCode.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(e), info = info), impl, _, _)  => begin
                      (cache, subs_1) = elabSubmods(cache, env, ih, pre, subs, impl, inModScope, info)
                      (cache, e_1, prop) = Static.elabExp(cache, env, e, impl, Config.splitArrays(), pre, info)
                      (e_1, prop) = Expression.tupleHead(e_1, prop)
                      (cache, e_1, prop) = Ceval.cevalIfConstant(cache, env, e_1, prop, impl, info)
                      (e_val, cache) = elabModValue(cache, env, e_1, prop, impl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, env, ih, e_1, pre) #= Bug: will cause elaboration of parameters without value to fail,
                               But this can be ok, since a modifier is present, giving it a value from outer modifications.. =#
                    (cache, DAE.MOD(finalPrefix, each_, subs_1, SOME(DAE.TYPED(e_2, e_val, prop, e, info)), info))
                  end

                  (cache, env, ih, pre, SCode.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(e), info = info), impl, _, _)  => begin
                      (cache, subs_1) = elabSubmods(cache, env, ih, pre, subs, impl, inModScope, info)
                    (cache, DAE.MOD(finalPrefix, each_, subs_1, SOME(DAE.UNTYPED(e)), info))
                  end

                  (cache, env, ih, pre, SCode.REDECL(finalPrefix = finalPrefix, eachPrefix = each_, element = elem), impl, _, info)  => begin
                      (elem, dm) = elabModRedeclareElement(cache, env, ih, pre, finalPrefix, elem, impl, inModScope, info)
                    (cache, DAE.REDECL(finalPrefix, each_, elem, dm))
                  end
                end
              end
          (outCache, outMod)
        end

         #= Is the modification one that does not depend on the scope it is evaluated in? =#
        function isInvariantMod(mod::SCode.Mod) ::Bool
              local b::Bool = false

              local e::Absyn.Exp
              local mods::SCode.Mod

              b = begin
                @match mod begin
                  SCode.NOMOD(__)  => begin
                    true
                  end

                  SCode.MOD(binding = NONE())  => begin
                      b = begin
                        @match mod.binding begin
                          SOME(e)  => begin
                              (_, b) = AbsynUtil.traverseExp(e, AbsynUtil.isInvariantExpNoTraverse, true)
                            b
                          end

                          _  => begin
                              true
                          end
                        end
                      end
                      if ! b
                        return b
                      end
                      for sm in mod.subModLst
                        if ! isInvariantMod(sm.mod)
                          b = false
                          return b
                        end
                      end
                    true
                  end

                  SCode.Mod.REDECL(element = SCode.Element.COMPONENT(modifications = mods, typeSpec = Absyn.TypeSpec.TPATH(path = Absyn.Path.FULLYQUALIFIED(__), arrayDim = NONE())))  => begin
                    isInvariantMod(mods)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  operator record ComplexCurrent = Complex(redeclare Modelica.SIunits.Current re, redeclare Modelica.SIunits.Current im)
               =#
               #=  Redeclarations, etc
               =#
          b
        end

         #= Is the modification one that does not depend on the scope it is evaluated in? =#
        function isInvariantDAEMod(mod::DAE.Mod) ::Bool
              local b::Bool

              local e::DAE.Exp
              local exp::Absyn.Exp
              local mods::SCode.Mod

              b = begin
                @match mod begin
                  DAE.NOMOD(__)  => begin
                    true
                  end

                  DAE.MOD(binding = NONE())  => begin
                      b = begin
                        @match mod.binding begin
                          SOME(DAE.TYPED(modifierAsExp = e))  => begin
                              (_, b) = Expression.traverseExpBottomUp(e, Expression.isInvariantExpNoTraverse, true)
                            b
                          end

                          SOME(DAE.UNTYPED(exp))  => begin
                              (_, b) = AbsynUtil.traverseExp(exp, AbsynUtil.isInvariantExpNoTraverse, true)
                            b
                          end

                          _  => begin
                              true
                          end
                        end
                      end
                      if ! b
                        return b
                      end
                      for sm in mod.subModLst
                        if ! isInvariantDAEMod(sm.mod)
                          b = false
                          return b
                        end
                      end
                    true
                  end

                  DAE.Mod.REDECL(element = SCode.Element.COMPONENT(modifications = mods, typeSpec = Absyn.TypeSpec.TPATH(path = Absyn.Path.FULLYQUALIFIED(__), arrayDim = NONE())))  => begin
                    isInvariantMod(mods)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  operator record ComplexCurrent = Complex(redeclare Modelica.SIunits.Current re, redeclare Modelica.SIunits.Current im)
               =#
               #=  Redeclarations, etc
               =#
          b
        end

         #=
          Same as elabMod, but if a named Mod is not part of a basic type, fail instead. =#
        function elabModForBasicType(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inMod::SCode.Mod, inBoolean::Bool, inModScope::ModScope, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Mod}
              local outMod::DAE.Mod
              local outCache::FCore.Cache

              checkIfModsAreBasicTypeMods(inMod)
              (outCache, outMod) = elabMod(inCache, inEnv, inIH, inPrefix, inMod, inBoolean, inModScope, info)
          (outCache, outMod)
        end

         #=
          Verifies that a list of submods only have named modifications that could be
          used for basic types. =#
        function checkIfModsAreBasicTypeMods(mod::SCode.Mod)
              _ = begin
                  local subs::List{SCode.SubMod}
                @match mod begin
                  SCode.NOMOD(__)  => begin
                    ()
                  end

                  SCode.MOD(subModLst = subs)  => begin
                      checkIfSubmodsAreBasicTypeMods(subs)
                    ()
                  end
                end
              end
        end

         #=
          Verifies that a list of submods only have named modifications that could be
          used for basic types. =#
        function checkIfSubmodsAreBasicTypeMods(inSubs::List{<:SCode.SubMod})
              _ = begin
                  local mod::SCode.Mod
                  local ident::String
                  local subs::List{SCode.SubMod}
                @match inSubs begin
                   nil()  => begin
                    ()
                  end

                  SCode.NAMEMOD(ident = ident) <| subs  => begin
                      @match true = ClassInf.isBasicTypeComponentName(ident)
                      checkIfSubmodsAreBasicTypeMods(subs)
                    ()
                  end
                end
              end
        end

        function elabModRedeclareElement(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, finalPrefix::SCode.Final, inElt::SCode.Element, impl::Bool, inModScope::ModScope, info::SourceInfo) ::Tuple{SCode.Element, DAE.Mod}
              local outMod::DAE.Mod
              local outElement::SCode.Element

              (outElement, outMod) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local f::SCode.Final
                  local fi::SCode.Final
                  local repl::SCode.Replaceable
                  local p::SCode.Partial
                  local enc::SCode.Encapsulated
                  local vis::SCode.Visibility
                  local redecl::SCode.Redeclare
                  local io::Absyn.InnerOuter
                  local cn::SCode.Ident
                  local compname::SCode.Ident
                  local bcn::SCode.Ident
                  local restr::SCode.Restriction
                  local tp::Absyn.TypeSpec
                  local tp1::Absyn.TypeSpec
                  local emod::DAE.Mod
                  local attr::SCode.Attributes
                  local mod::SCode.Mod
                  local modOriginal::SCode.Mod
                  local cond::Option{Absyn.Exp}
                  local i::SourceInfo
                  local ih::InstanceHierarchy
                  local attr1::SCode.Attributes
                  local cmt::SCode.Comment
                  local comment::SCode.Comment
                  local element::SCode.Element
                  local c::SCode.Element
                  local prefixes::SCode.Prefixes
                   #= /*/ search for target class locally and if it is a derived with no modifications, use it
                       replaceable package Medium = Modelica.Media.Air.MoistAir constrainedby Modelica.Media.Interfaces.PartialMedium;
                       modifier: redeclare Medium = Medium
                      case SCode.CLASS(cn, prefixes as SCode.PREFIXES(vis,redecl,fi,io,repl), enc, p, restr, SCode.DERIVED(Absyn.TPATH(Absyn.IDENT(bcn), NONE()),mod,attr1), cmt, i)
                        equation
                          true = stringEq(cn, bcn);
                          (c, _) = Lookup.lookupClassLocal(inEnv, bcn);
                          tp = SCodeUtil.getDerivedTypeSpec(c);
                          c = SCodeUtil.mergeWithOriginal(SCode.CLASS(cn,SCode.PREFIXES(vis,redecl,fi,io,repl),enc,p,restr,SCode.DERIVED(tp,mod,attr1),cmt,i), c);
                          SCode.CLASS(cn,SCode.PREFIXES(vis,redecl,fi,io,repl),enc,p,restr,SCode.DERIVED(tp,mod,attr1),cmt,i) = c;
                          (cache, emod) = elabMod(inCache, inEnv, inIH, inPrefix, mod, impl, inModScope, info);
                          (cache, tp1) = elabModQualifyTypespec(cache, inEnv, inIH, inPrefix, impl, info, cn, tp);
                           unelab mod so we get constant evaluation of parameters
                          mod = unelabMod(emod);
                        then
                          (SCode.CLASS(cn,SCode.PREFIXES(vis,redecl,fi,io,repl),enc,p,restr,SCode.DERIVED(tp1,mod,attr1),cmt,i), emod);*/ =#
                   #=  Only derived classdefinitions supported in redeclares for now.
                   =#
                   #=  TODO: What is allowed according to spec? adrpo: 2011-06-28: is not decided yet,
                   =#
                   #=        but i think only derived even if in the Modelica.Media we have redeclare-as-element
                   =#
                   #=        replacing entire functions with PARTS and everything, so i added the case below
                   =#
                @matchcontinue inElt begin
                  SCode.CLASS(cn, prefixes && SCode.PREFIXES(vis, redecl, fi, io, repl), enc, p, restr, SCode.DERIVED(tp, mod, attr1), cmt, i)  => begin
                      mod = SCodeUtil.mergeModifiers(mod, SCodeUtil.getConstrainedByModifiers(prefixes))
                      (cache, emod) = elabMod(inCache, inEnv, inIH, inPrefix, mod, impl, inModScope, info)
                      (_, tp1) = elabModQualifyTypespec(cache, inEnv, inIH, inPrefix, impl, info, cn, tp)
                      mod = unelabMod(emod)
                    (SCode.CLASS(cn, SCode.PREFIXES(vis, redecl, fi, io, repl), enc, p, restr, SCode.DERIVED(tp1, mod, attr1), cmt, i), emod)
                  end

                  SCode.CLASS(restriction = SCode.R_ENUMERATION(__))  => begin
                    (inElt, DAE.NOMOD())
                  end

                  SCode.CLASS(classDef = SCode.ENUMERATION(__))  => begin
                    (inElt, DAE.NOMOD())
                  end

                  SCode.COMPONENT(compname, prefixes && SCode.PREFIXES(vis, redecl, fi, io, repl), attr, tp, mod, cmt, cond, i)  => begin
                      mod = SCodeUtil.mergeModifiers(mod, SCodeUtil.getConstrainedByModifiers(prefixes))
                      (cache, emod) = elabMod(inCache, inEnv, inIH, inPrefix, mod, impl, inModScope, info)
                      (_, tp1) = elabModQualifyTypespec(cache, inEnv, inIH, inPrefix, impl, info, compname, tp)
                      mod = unelabMod(emod)
                    (SCode.COMPONENT(compname, SCode.PREFIXES(vis, redecl, fi, io, repl), attr, tp1, mod, cmt, cond, i), emod)
                  end

                  element  => begin
                      print("Unhandled element redeclare (we keep it as it is!): " + SCodeDump.unparseElementStr(element, SCodeDump.defaultOptions) + "\\n")
                    (element, DAE.NOMOD())
                  end
                end
              end
               #=  myMerge modifers from the component to the modifers from the constrained by
               =#
               #=  unelab mod so we get constant evaluation of parameters
               =#
               #=  replaceable type E=enumeration(e1,...,en), E=enumeration(:)
               =#
               #=  redeclare of component declaration
               =#
               #=  myMerge modifers from the component to the modifers from the constrained by
               =#
               #=  unelab mod so we get constant evaluation of parameters
               =#
               #=  redeclare failure?
               =#
          (outElement, outMod)
        end

         #= Help function to elabModRedeclareElements.
         This function makes sure that type specifiers, i.e. class names, in redeclarations are looked up in the correct environment.
         This is achieved by making them fully qualified. =#
        function elabModQualifyTypespec(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, impl::Bool, info::SourceInfo, name::Absyn.Ident, tp::Absyn.TypeSpec) ::Tuple{FCore.Cache, Absyn.TypeSpec}
              local outTp::Absyn.TypeSpec
              local outCache::FCore.Cache

              (outCache, outTp) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local dims::Absyn.ArrayDim
                  local p::Absyn.Path
                  local p1::Absyn.Path
                  local cref::Absyn.ComponentRef
                  local edims::DAE.Dimensions
                  local ih::InnerOuterTypes.InstHierarchy
                  local pre::Prefix.PrefixType
                   #=  no array dimensions
                   =#
                @match (inCache, inEnv, inIH, inPrefix, impl, info, name, tp) begin
                  (cache, env, _, _, _, _, _, Absyn.TPATH(p, NONE()))  => begin
                     #TODO. Solve Circ dep between Inst and Mod
                      #(cache, p1) = Inst.makeFullyQualified(cache, env, p)
                    (cache, Absyn.TPATH(p1, NONE()))
                  end

                  (cache, env, ih, pre, _, _, _, Absyn.TPATH(p, SOME(dims)))  => begin
                    cref = Absyn.CREF_IDENT(name, nil)
                      #TODO solve circular dependency between InstUtil and Mod
                      #(cache, edims) = InstUtil.elabArraydim(cache, env, cref, p, dims, NONE(), impl, true, false, pre, info, nil)
                      (cache, edims) = PrefixUtil.prefixDimensions(cache, env, ih, pre, edims)
                      dims = ListUtil.map(edims, Expression.unelabDimension)
                      #TODO. Solve Circ dep between Inst and Mod
                      #(cache, p1) = Inst.makeFullyQualified(cache, env, p)
                    (cache, Absyn.TPATH(p1, SOME(dims)))
                  end
                end
              end
               #=  some array dimensions, elaborate them!
               =#
          (outCache, outTp)
        end

         #= Helper function to elabMod. Tries to constant evaluate a modifier expression. =#
        function elabModValue(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inProp::DAE.Properties, inImpl::Bool, inInfo::SourceInfo) ::Tuple{Option{Values.Value}, FCore.Cache}
              local outCache::FCore.Cache = inCache
              local outValue::Option{Values.Value} = NONE()

              local err_count::ModelicaInteger
              local msg::Absyn.Msg
              local c::DAE.Const
              local v::Values.Value

              c = Types.propAllConst(inProp)
               #=  If the expression is a parameter or constant expression:
               =#
              if ! Types.constIsVariable(c)
                msg = AbsynUtil.optMsg(Types.constIsConst(c) && ! inImpl, inInfo)
                err_count = Error.getNumErrorMessages()
                try
                  (_, v) = Ceval.ceval(inCache, inEnv, inExp, false, msg, 0)
                  if ValuesUtil.isRecord(v)
                    v = ValuesUtil.typeConvertRecord(v, Expression.typeOf(inExp))
                  end
                  outValue = SOME(v)
                catch
                  if err_count != Error.getNumErrorMessages() && ! Expression.containsAnyCall(inExp)
                    fail()
                  end
                end
              end
               #=  Show error messages from ceval only if the expression is constant.
               =#
               #=  Fail if ceval gave an error. Except if the expression contains a
               =#
               #=  function call, because we don't handle function parameter modifiers
               =#
               #=  correctly which causes issues with CevalFunction.
               =#
          (outValue, outCache)
        end

         #= Transforms Mod back to SCode.Mod, loosing type information. =#
        function unelabMod(inMod::DAE.Mod) ::SCode.Mod
              local outMod::SCode.Mod

              outMod = begin
                  local subs_1::List{SCode.SubMod}
                  local m::DAE.Mod
                  local mod::DAE.Mod
                  local finalPrefix::SCode.Final
                  local each_::SCode.Each
                  local subs::List{DAE.SubMod}
                  local e::Absyn.Exp
                  local e_1::Absyn.Exp
                  local absynExp::Absyn.Exp
                  local p::DAE.Properties
                  local elem::SCode.Element
                  local dexp::DAE.Exp
                  local str::String
                  local info::SourceInfo
                  local v::Values.Value
                @matchcontinue inMod begin
                  DAE.NOMOD(__)  => begin
                    SCode.NOMOD()
                  end

                  DAE.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = NONE(), info = info)  => begin
                      subs_1 = unelabSubmods(subs)
                    SCode.MOD(finalPrefix, each_, subs_1, NONE(), info)
                  end

                  DAE.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(DAE.UNTYPED(e)), info = info)  => begin
                      subs_1 = unelabSubmods(subs)
                    SCode.MOD(finalPrefix, each_, subs_1, SOME(e), info)
                  end

                  DAE.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(DAE.TYPED(modifierAsValue = SOME(v))), info = info)  => begin
                      subs_1 = unelabSubmods(subs)
                      e_1 = Expression.unelabExp(ValuesUtil.valueExp(v))
                    SCode.MOD(finalPrefix, each_, subs_1, SOME(e_1), info)
                  end

                  DAE.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(DAE.TYPED(_, _, _, absynExp)), info = info)  => begin
                      subs_1 = unelabSubmods(subs)
                      e_1 = absynExp
                    SCode.MOD(finalPrefix, each_, subs_1, SOME(e_1), info)
                  end

                  DAE.REDECL(finalPrefix = finalPrefix, eachPrefix = each_, element = elem)  => begin
                    SCode.REDECL(finalPrefix, each_, elem)
                  end

                  mod  => begin
                      str = "Mod.elabUntypedMod failed: " + printModStr(mod) + "\\n"
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #=  use the constant first!
               =#
               #= es = ExpressionDump.printExpStr(e);
               =#
               #=  default typechecking non-delayed
               =#
               #= /* / use the expression second
                  case ((DAE.MOD(finalPrefix = finalPrefix,eachPrefix = each_,subModLst = subs,
                                      binding = SOME(DAE.TYPED(modifierAsExp = dexp, info = info)))))
                    equation
                      es = ExpressionDump.printExpStr(e);
                      subs_1 = unelabSubmods(subs);
                      e_1 = Expression.unelabExp(dexp);
                    then
                      SCode.MOD(finalPrefix,each_,subs_1,SOME((e_1,false)),info);  default typechecking non-delayed */ =#
               #= es = ExpressionDump.printExpStr(e);
               =#
               #= Expression.unelabExp(e);
               =#
          outMod
        end

         #= Helper function to unelabMod. =#
        function unelabSubmods(inTypesSubModLst::List{<:DAE.SubMod}) ::List{SCode.SubMod}
              local outSCodeSubModLst::List{SCode.SubMod}

              outSCodeSubModLst = list(begin
                  local m_1::SCode.Mod
                  local i::String
                  local m::DAE.Mod
                @match x begin
                  DAE.NAMEMOD(ident = i, mod = m)  => begin
                      m_1 = unelabMod(m)
                    SCode.NAMEMOD(i, m_1)
                  end
                end
              end for x in inTypesSubModLst)
          outSCodeSubModLst
        end

        function unelabSubscript(inIntegerLst::List{<:ModelicaInteger}) ::List{SCode.Subscript}
              local outSCodeSubscriptLst::List{SCode.Subscript}

              outSCodeSubscriptLst = list(Absyn.SUBSCRIPT(Absyn.INTEGER(i)) for i in inIntegerLst)
          outSCodeSubscriptLst
        end

         #= This function updates an untyped modification to a typed one, by looking
          up the type of the modifier in the environment and update it. =#
        function updateMod(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inMod::DAE.Mod, inBoolean::Bool, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Mod}
              local outMod::DAE.Mod
              local outCache::FCore.Cache

              (outCache, outMod) = begin
                  local impl::Bool
                  local f::SCode.Final
                  local m::DAE.Mod
                  local subs_1::List{DAE.SubMod}
                  local subs::List{DAE.SubMod}
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local prop::DAE.Properties
                  local p::DAE.Properties
                  local e_val::Option{Values.Value}
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local each_::SCode.Each
                  local e::Absyn.Exp
                  local eOpt::Option{Absyn.Exp}
                  local cache::FCore.Cache
                  local ih::InstanceHierarchy
                  local str::String
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inMod, inBoolean, inInfo) begin
                  (cache, _, _, _, DAE.NOMOD(__), _, _)  => begin
                    (cache, DAE.NOMOD())
                  end

                  (cache, _, _, _, m && DAE.REDECL(__), _, _)  => begin
                    (cache, m)
                  end

                  (cache, env, ih, pre, DAE.MOD(finalPrefix = f, eachPrefix = each_, subModLst = subs, binding = SOME(DAE.UNTYPED(e)), info = info), impl, _)  => begin
                      (cache, subs_1) = updateSubmods(cache, env, ih, pre, subs, impl, info)
                      (cache, e_1, prop) = Static.elabExp(cache, env, e, impl, true, pre, info)
                      (cache, e_1, prop) = Ceval.cevalIfConstant(cache, env, e_1, prop, impl, info)
                      (e_val, cache) = elabModValue(cache, env, e_1, prop, impl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, env, ih, e_1, pre)
                      if Flags.isSet(Flags.UPDMOD)
                        Debug.trace("Updated mod: ")
                        Debug.traceln(printModStr(DAE.MOD(f, each_, subs_1, SOME(DAE.TYPED(e_2, NONE(), prop, e, info)), info)))
                      end
                    (cache, DAE.MOD(f, each_, subs_1, SOME(DAE.TYPED(e_2, e_val, prop, e, info)), info))
                  end

                  (cache, env, ih, pre, DAE.MOD(finalPrefix = f, eachPrefix = each_, subModLst = subs, binding = SOME(DAE.TYPED(e_1, e_val, p, e)), info = info), impl, _)  => begin
                      (cache, subs_1) = updateSubmods(cache, env, ih, pre, subs, impl, info)
                    (cache, DAE.MOD(f, each_, subs_1, SOME(DAE.TYPED(e_1, e_val, p, e, info)), info))
                  end

                  (cache, env, ih, pre, DAE.MOD(finalPrefix = f, eachPrefix = each_, subModLst = subs, binding = NONE(), info = info), impl, _)  => begin
                      (cache, subs_1) = updateSubmods(cache, env, ih, pre, subs, impl, info)
                    (cache, DAE.MOD(f, each_, subs_1, NONE(), info))
                  end

                  (_, _, _, _, m, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      str = printModStr(m)
                      Debug.traceln("- Mod.updateMod failed mod: " + str)
                    fail()
                  end
                end
              end
          (outCache, outMod)
        end

         #=  =#
        function updateSubmods(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inTypesSubModLst::List{<:DAE.SubMod}, inBoolean::Bool, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.SubMod}}
              local outTypesSubModLst::List{DAE.SubMod} = nil
              local outCache::FCore.Cache = inCache
              local m_1::DAE.Mod
              local m::DAE.Mod
              local modif::DAE.SubMod
              local i::String

              for x in inTypesSubModLst
                modif = @match x begin
                  DAE.NAMEMOD(ident = i, mod = m)  => begin
                      (outCache, m_1) = updateMod(outCache, inEnv, inIH, inPrefix, m, inBoolean, info)
                    DAE.NAMEMOD(i, m_1)
                  end
                end
                outTypesSubModLst = _cons(modif, outTypesSubModLst)
              end
              outTypesSubModLst = listReverse(outTypesSubModLst)
          (outCache, outTypesSubModLst)
        end

         #= This function is used to convert SCode.Mod into Mod, without
          adding correct type information. Instead, a undefined type will be
          given to the modification. This is used when modifications of e.g.
          elements in base classes used. For instance,
          model test extends A(x=y); end test;  both x and y are defined in A
          The modifier x=y must be myMerged with outer modifiers, thus it needs
          to be converted to Mod.
          Notice that the correct type information must be updated later on. =#
        function elabUntypedMod(inMod::SCode.Mod, inModScope::ModScope) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local subs_1::List{DAE.SubMod}
                  local m::SCode.Mod
                  local mod::SCode.Mod
                  local finalPrefix::SCode.Final
                  local each_::SCode.Each
                  local subs::List{SCode.SubMod}
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local e::Absyn.Exp
                  local elem::SCode.Element
                  local s::String
                  local info::SourceInfo
                @matchcontinue inMod begin
                  SCode.NOMOD(__)  => begin
                    DAE.NOMOD()
                  end

                  SCode.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = NONE(), info = info)  => begin
                      subs_1 = elabUntypedSubmods(subs, inModScope)
                    DAE.MOD(finalPrefix, each_, subs_1, NONE(), info)
                  end

                  SCode.MOD(finalPrefix = finalPrefix, eachPrefix = each_, subModLst = subs, binding = SOME(e), info = info)  => begin
                      subs_1 = elabUntypedSubmods(subs, inModScope)
                    DAE.MOD(finalPrefix, each_, subs_1, SOME(DAE.UNTYPED(e)), info)
                  end

                  SCode.REDECL(finalPrefix = finalPrefix, eachPrefix = each_, element = elem)  => begin
                    DAE.REDECL(finalPrefix, each_, elem, DAE.NOMOD())
                  end

                  _  => begin
                        print("- elab_untyped_mod ")
                        s = SCodeDump.printModStr(inMod, SCodeDump.defaultOptions)
                        print(s)
                        print(" failed\\n")
                      fail()
                  end
                end
              end
          outMod
        end

         #= This function helps elabMod by recursively elaborating on a list of submodifications. =#
        function elabSubmods(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inSCodeSubModLst::List{<:SCode.SubMod}, inBoolean::Bool, inModScope::ModScope, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.SubMod}}
              local outTypesSubModLst::List{DAE.SubMod}
              local outCache::FCore.Cache

              local submods::List{SCode.SubMod}

              submods = compactSubMods(inSCodeSubModLst, inModScope)
              (outCache, outTypesSubModLst) = elabSubmods2(inCache, inEnv, inIH, inPrefix, submods, inBoolean, info, nil)
          (outCache, outTypesSubModLst)
        end

         #= This function elaborates a list of submodifications. =#
        function elabSubmods2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inSubMods::List{<:SCode.SubMod}, inImpl::Bool, inInfo::SourceInfo, inAccumMods::List{<:DAE.SubMod}) ::Tuple{FCore.Cache, List{DAE.SubMod}}
              local outSubMods::List{DAE.SubMod}
              local outCache::FCore.Cache

              (outCache, outSubMods) = begin
                  local cache::FCore.Cache
                  local smod::SCode.SubMod
                  local rest_smods::List{SCode.SubMod}
                  local dmod::DAE.SubMod
                  local accum_mods::List{DAE.SubMod}
                @match (inCache, inEnv, inIH, inPrefix, inSubMods, inImpl, inInfo, inAccumMods) begin
                  (cache, _, _, _, smod <| rest_smods, _, _, _)  => begin
                      (cache, dmod) = elabSubmod(cache, inEnv, inIH, inPrefix, smod, inImpl, inInfo)
                      (cache, accum_mods) = elabSubmods2(cache, inEnv, inIH, inPrefix, rest_smods, inImpl, inInfo, _cons(dmod, inAccumMods))
                    (cache, accum_mods)
                  end

                  _  => begin
                      (inCache, listReverse(inAccumMods))
                  end
                end
              end
          (outCache, outSubMods)
        end

         #= This function myMerges the submodifiers in a modifier so that each submodifier
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

         #= Helper function to compactSubMods. Tries to myMerge the given modifier with an
           existing modifier in the accumulation list. If a matching modifier is not
           found in the list it's added instead. =#
        function compactSubMod(inSubMod::SCode.SubMod, inModScope::ModScope, inName::List{<:String}, inAccumMods::List{<:SCode.SubMod}) ::List{SCode.SubMod}
              local outSubMods::List{SCode.SubMod}

              local submods::List{SCode.SubMod}
              local found::Bool

              (submods, found) = ListUtil.findMap3(inAccumMods, compactSubMod2, inSubMod, inModScope, inName)
              outSubMods = ListUtil.consOnTrue(! found, inSubMod, submods)
          outSubMods
        end

         #= Helper function to compactSubMod. myMerges the given modifier with the existing
            modifier if they have the same name, otherwise does nothing. =#
        function compactSubMod2(inExistingMod::SCode.SubMod, inNewMod::SCode.SubMod, inModScope::ModScope, inName::List{<:String}) ::Tuple{SCode.SubMod, Bool}
              local outFound::Bool
              local outMod::SCode.SubMod

              (outMod, outFound) = begin
                  local name1::String
                  local name2::String
                  local submod::SCode.SubMod
                @match (inExistingMod, inNewMod, inModScope, inName) begin
                  (SCode.NAMEMOD(ident = name1), SCode.NAMEMOD(ident = name2), _, _) where (! stringEqual(name1, name2))  => begin
                    (inExistingMod, false)
                  end

                  (SCode.NAMEMOD(ident = name1), _, _, _)  => begin
                      submod = myMergeSubModsInSameScope(inExistingMod, inNewMod, _cons(name1, inName), inModScope)
                    (submod, true)
                  end
                end
              end
          (outMod, outFound)
        end

         #= myMerges two submodifiers in the same scope, i.e. they have the same priority.
           It's thus an error if the modifiers modify the same element. =#
        function myMergeSubModsInSameScope(inMod1::SCode.SubMod, inMod2::SCode.SubMod, inElementName::List{<:String}, inModScope::ModScope) ::SCode.SubMod
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
               #=  Both modifiers have bindings, print error.
               =#
          outMod
        end

        function printModScope(inModScope::ModScope) ::String
              local outString::String

              outString = begin
                  local name::String
                  local path::Absyn.Path
                @match inModScope begin
                  COMPONENT(name = name)  => begin
                    System.gettext("component ") + name
                  end

                  EXTENDS(path = path)  => begin
                    System.gettext("extends ") + AbsynUtil.pathString(path)
                  end

                  DERIVED(path = path)  => begin
                    System.gettext("inherited class ") + AbsynUtil.pathString(path)
                  end
                end
              end
          outString
        end

         #= This function elaborates on a submodification, turning an
           SCode.SubMod into a DAE.SubMod. =#
        function elabSubmod(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPrefix::Prefix.PrefixType, inSubMod::SCode.SubMod, inBoolean::Bool, info::SourceInfo) ::Tuple{FCore.Cache, DAE.SubMod}
              local outSubMod::DAE.SubMod
              local outCache::FCore.Cache

              local smod::SCode.Mod
              local dmod::DAE.Mod
              local i::String

              @match SCode.NAMEMOD(ident = i, mod = smod) = inSubMod
              (outCache, dmod) = elabMod(inCache, inEnv, inIH, inPrefix, smod, inBoolean, COMPONENT(i), info)
              outSubMod = DAE.NAMEMOD(i, dmod)
          (outCache, outSubMod)
        end

        function elabUntypedSubmods(inSubMods::List{<:SCode.SubMod}, inModScope::ModScope) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod}

              local submods::List{SCode.SubMod}

              submods = compactSubMods(inSubMods, inModScope)
              outSubMods = listAppend(elabUntypedSubmod(m) for m in listReverse(submods))
          outSubMods
        end

         #=
          This function elaborates on a submodification, turning an
          `SCode.SubMod\\' into one or more `DAE.SubMod\\'s, wihtout type information.
         =#
        function elabUntypedSubmod(inSubMod::SCode.SubMod) ::List{DAE.SubMod}
              local outTypesSubModLst::List{DAE.SubMod}

              outTypesSubModLst = begin
                  local m_1::DAE.Mod
                  local i::String
                  local m::SCode.Mod
                @match inSubMod begin
                  SCode.NAMEMOD(ident = i, mod = m)  => begin
                      m_1 = elabUntypedMod(m, COMPONENT(""))
                    list(DAE.NAMEMOD(i, m_1))
                  end
                end
              end
          outTypesSubModLst
        end

         #=  - Lookup
         =#

         #= This function extracts a modification from inside another
          modification, using a name to look up submodifications. =#
        function lookupModificationP(inMod::DAE.Mod, inPath::Absyn.Path) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local mod::DAE.Mod
                  local m::DAE.Mod
                  local mod_1::DAE.Mod
                  local n::String
                  local p::Absyn.Path
                @matchcontinue (inMod, inPath) begin
                  (m, Absyn.IDENT(name = n))  => begin
                      mod = lookupCompModification(m, n)
                    mod
                  end

                  (m, Absyn.FULLYQUALIFIED(p))  => begin
                    lookupModificationP(m, p)
                  end

                  (m, Absyn.QUALIFIED(name = n, path = p))  => begin
                      mod = lookupCompModification(m, n)
                      mod_1 = lookupModificationP(mod, p)
                    mod_1
                  end

                  _  => begin
                        Print.printBuf("- Mod.lookupModificationP failed\\n")
                      fail()
                  end
                end
              end
          outMod
        end

         #= This function is used to look up an identifier in a modification. =#
        function lookupCompModification(inMod::DAE.Mod, inIdent::Absyn.Ident) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local mod::DAE.Mod
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local subs::List{DAE.SubMod}
                  local n::String
                  local eqMod::Option{DAE.EqMod}
                  local e::SCode.Each
                  local f::SCode.Final
                  local info::SourceInfo
                @match (inMod, inIdent) begin
                  (DAE.MOD(finalPrefix = f, eachPrefix = e, subModLst = subs, binding = eqMod, info = info), n)  => begin
                      mod1 = lookupCompModification2(subs, n)
                      mod2 = lookupComplexCompModification(eqMod, n, f, e, info)
                    checkDuplicateModifications(mod1, mod2, n)
                  end

                  _  => begin
                      DAE.NOMOD()
                  end
                end
              end
          outMod
        end

         #= return the modifications from mod
         which is named inName or which
         is named name if name is inside
         inSMod(xxx = name) =#
        function getModifs(inMods::DAE.Mod, inName::SCode.Ident, inSMod::SCode.Mod) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local m::DAE.Mod
                @matchcontinue (inMods, inName, inSMod) begin
                  (_, _, _)  => begin
                      m = lookupCompModification(inMods, inName)
                      m = myMergeModifiers(inMods, m, inSMod)
                    m
                  end

                  _  => begin
                        m = myMergeModifiers(inMods, DAE.NOMOD(), inSMod)
                      m
                  end
                end
              end
          outMod
        end

        function myMergeModifiers(inMods::DAE.Mod, inMod::DAE.Mod, inSMod::SCode.Mod) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local m::DAE.Mod
                  local sl::List{SCode.SubMod}
                  local f::SCode.Final
                  local e::SCode.Each
                @matchcontinue (inMods, inMod, inSMod) begin
                  (_, _, SCode.MOD(f, e, sl, _, _))  => begin
                      m = myMergeSubMods(inMods, inMod, f, e, sl)
                    m
                  end

                  _  => begin
                      inMod
                  end
                end
              end
          outMod
        end

        function myMergeSubMods(inMods::DAE.Mod, inMod::DAE.Mod, f::SCode.Final, e::SCode.Each, inSMods::List{<:SCode.SubMod}) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local m::DAE.Mod
                  local id::SCode.Ident
                  local n::SCode.Ident
                  local rest::List{SCode.SubMod}
                  local info::SourceInfo
                @matchcontinue inSMods begin
                   nil()  => begin
                    inMod
                  end

                  SCode.NAMEMOD(n, SCode.MOD(binding = SOME(Absyn.CREF(Absyn.CREF_IDENT(id, _))), info = info)) <| rest  => begin
                      m = lookupCompModification(inMods, id)
                      m = DAE.MOD(f, e, list(DAE.NAMEMOD(n, m)), NONE(), info)
                      m = myMerge(inMod, m)
                      m = myMergeSubMods(inMods, m, f, e, rest)
                    m
                  end

                  _ <| rest  => begin
                      m = myMergeSubMods(inMods, inMod, f, e, rest)
                    m
                  end
                end
              end
          outMod
        end

         #= This function is used to look up an identifier in a modification. =#
        function lookupCompModificationFromEqu(inMod::DAE.Mod, inIdent::Absyn.Ident) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local mod::DAE.Mod
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local subs::List{DAE.SubMod}
                  local n::String
                  local eqMod::Option{DAE.EqMod}
                  local e::SCode.Each
                  local f::SCode.Final
                  local info::SourceInfo
                @match (inMod, inIdent) begin
                  (DAE.NOMOD(__), _)  => begin
                    DAE.NOMOD()
                  end

                  (DAE.REDECL(__), _)  => begin
                    DAE.NOMOD()
                  end

                  (DAE.MOD(finalPrefix = f, eachPrefix = e, subModLst = subs, binding = eqMod, info = info), n)  => begin
                      mod1 = lookupCompModification2(subs, n)
                      mod2 = lookupComplexCompModification(eqMod, n, f, e, info)
                      mod = selectEqMod(mod1, mod2, n)
                    mod
                  end
                end
              end
          outMod
        end

         #= @adrpo:
          This function selects the eqmod modifier if is not DAE.NOMOD! AND IS TYPED!
          Otherwise check for duplicates =#
        function selectEqMod(subMod::DAE.Mod, eqMod::DAE.Mod, n::String) ::DAE.Mod
              local mod::DAE.Mod

              mod = begin
                @match (subMod, eqMod, n) begin
                  (_, DAE.NOMOD(__), _)  => begin
                    subMod
                  end

                  (_, DAE.MOD(binding = SOME(DAE.TYPED(__))), _)  => begin
                    eqMod
                  end

                  _  => begin
                        mod = checkDuplicateModifications(subMod, eqMod, n)
                      mod
                  end
                end
              end
               #=  eqmod is nomod!
               =#
          mod
        end

         #= Looks up a component modification from a complex constructor (e.g. record
           constructor) by name. =#
        function lookupComplexCompModification(inEqMod::Option{<:DAE.EqMod}, inName::Absyn.Ident, inFinal::SCode.Final, inEach::SCode.Each, inInfo::SourceInfo) ::DAE.Mod
              local outMod::DAE.Mod = DAE.NOMOD()

              local values::List{Values.Value}
              local names::List{String}
              local v::Values.Value
              local name::String
              local e::DAE.Exp
              local ae::Absyn.Exp
              local ty::DAE.Type
              local eq_mod::DAE.EqMod
              local info::SourceInfo

              try
                @match SOME(DAE.TYPED(modifierAsValue = SOME(Values.RECORD(orderd = values, comp = names, index = -1)), info = info)) = inEqMod
                for name in names
                  @match _cons(v, values) = values
                  if name == inName
                    e = ValuesUtil.valueExp(v)
                    ae = Expression.unelabExp(e)
                    ty = Types.complicateType(Expression.typeOf(e))
                    eq_mod = DAE.TYPED(e, SOME(v), DAE.PROP(ty, DAE.C_CONST()), ae, info)
                    outMod = DAE.MOD(inFinal, inEach, nil, SOME(eq_mod), inInfo)
                    break
                  end
                end
              catch
              end
          outMod
        end

         #= Checks if two modifiers are present, and in that case
        print error of duplicate modifications, if not, the one modification having a value is returned =#
        function checkDuplicateModifications(mod1::DAE.Mod, mod2::DAE.Mod, n::String) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local submods::List{DAE.SubMod}
                @match (mod1, mod2) begin
                  (DAE.NOMOD(__), _)  => begin
                    mod2
                  end

                  (_, DAE.NOMOD(__))  => begin
                    mod1
                  end

                  (DAE.REDECL(__), DAE.MOD(__))  => begin
                    myMergeRedeclareWithBinding(mod1, mod2)
                  end

                  (DAE.MOD(__), DAE.REDECL(__))  => begin
                    myMergeRedeclareWithBinding(mod2, mod1)
                  end

                  (DAE.MOD(binding = NONE()), DAE.MOD(__))  => begin
                      submods = checkDuplicateModifications2(mod1.subModLst, mod2.subModLst, n)
                    DAE.MOD(mod2.finalPrefix, mod2.eachPrefix, submods, mod2.binding, mod2.info)
                  end

                  (DAE.MOD(__), DAE.MOD(binding = NONE()))  => begin
                      submods = checkDuplicateModifications2(mod1.subModLst, mod2.subModLst, n)
                    DAE.MOD(mod1.finalPrefix, mod1.eachPrefix, submods, mod1.binding, mod1.info)
                  end

                  (DAE.MOD(__), DAE.MOD(__))  => begin
                      Error.addMultiSourceMessage(Error.DUPLICATE_MODIFICATIONS, list(n, ""), list(getModInfo(mod1), getModInfo(mod2)))
                    mod2
                  end
                end
              end
          outMod
        end

        function checkDuplicateModifications2(inSubMods1::List{<:DAE.SubMod}, inSubMods2::List{<:DAE.SubMod}, inName::String) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod}

              local submods::List{DAE.SubMod} = inSubMods2
              local osubmod::Option{DAE.SubMod}
              local submod::DAE.SubMod
              local info1::SourceInfo
              local info2::SourceInfo

              for s in inSubMods1
                (submods, osubmod) = ListUtil.deleteMemberOnTrue(subModName(s), submods, isSubModNamed)
                if isSome(osubmod)
                  @match SOME(submod) = osubmod
                  info1 = subModInfo(s)
                  info2 = subModInfo(submod)
                  Error.addMultiSourceMessage(Error.MULTIPLE_MODIFIER, list(inName), list(info1, info2))
                end
              end
              outSubMods = listAppend(inSubMods1, inSubMods2)
          outSubMods
        end

         #= myMerges two modifiers where the first is a redeclare and the second a binding
           modifier. This is to handle the case where an extended record redeclares a
           component, and then the component gets a binding when the record type is used.

           E.g. record ER = R(redeclare SomeType x);
                ER er = ER(1.0);
           =#
        function myMergeRedeclareWithBinding(inRedeclare::DAE.Mod, inBinding::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod = inRedeclare

              outMod = begin
                @match (outMod, inBinding) begin
                  (DAE.REDECL(__), DAE.MOD(subModLst =  nil(), binding = SOME(_)))  => begin
                      Setfield.@set outMod.mod = myMerge(inBinding, outMod.mod)
                    outMod
                  end
                end
              end
          outMod
        end

        function modEqualNoPrefix(mod1::DAE.Mod, mod2::DAE.Mod) ::Tuple{DAE.Mod, Bool}
              local equal::Bool
              local outMod::DAE.Mod

              (outMod, equal) = begin
                @match (mod1, mod2) begin
                  (DAE.MOD(__), DAE.MOD(__))  => begin
                      @match true = subModsEqual(mod1.subModLst, mod2.subModLst)
                      @match true = eqModEqual(mod1.binding, mod2.binding)
                    (mod2, true)
                  end

                  (DAE.REDECL(__), DAE.REDECL(__))  => begin
                      @match true = SCodeUtil.elementEqual(mod1.element, mod2.element)
                    (mod2, true)
                  end

                  (DAE.NOMOD(__), DAE.NOMOD(__))  => begin
                    (DAE.NOMOD(), true)
                  end

                  _  => begin
                      (mod2, false)
                  end
                end
              end
               #=  two exactly the same mod, return just one! (used when it is REDECL or a submod is REDECL)
               =#
               #=  adrpo: do not fail, return false!
               =#
          (outMod, equal)
        end

        function lookupNamedSubMod(inSubMods::List{<:DAE.SubMod}, inIdent::Absyn.Ident) ::DAE.SubMod
              local outSubMod::DAE.SubMod

              outSubMod = ListUtil.getMemberOnTrue(inIdent, inSubMods, isSubModNamed)
          outSubMod
        end

        function isSubModNamed(inIdent::Absyn.Ident, inSubMod::DAE.SubMod) ::Bool
              local outIsNamed::Bool

              local ident::String

              @match DAE.NAMEMOD(ident = ident) = inSubMod
              outIsNamed = stringEq(inIdent, ident)
          outIsNamed
        end

         #= @author: adrpo
         Prints sub-mods in a string with format (sub1, sub2, sub3) =#
        function printSubsStr(inSubMods::List{<:DAE.SubMod}, addParan::Bool) ::String
              local s::String

              s = stringDelimitList(ListUtil.map(inSubMods, prettyPrintSubmod), ", ")
              s = (if addParan
                    "("
                  else
                    ""
                  end) + s + (if addParan
                    ")"
                  else
                    ""
                  end)
          s
        end

        function lookupCompModification2(inSubModLst::List{<:DAE.SubMod}, inIdent::Absyn.Ident) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local mmods::List{DAE.SubMod}
                  local mod::DAE.Mod
                @matchcontinue (inSubModLst, inIdent) begin
                  ( nil(), _)  => begin
                    DAE.NOMOD()
                  end

                  (_, _)  => begin
                      @match DAE.NAMEMOD(mod = mod) = lookupNamedSubMod(inSubModLst, inIdent)
                    mod
                  end

                  _  => begin
                      DAE.NOMOD()
                  end
                end
              end
          outMod
        end

         #= This function extracts modifications to an array element, using a subscript
           expression to index the modification. =#
        function lookupIdxModification(inMod::DAE.Mod, inIndex::DAE.Exp) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local subs::List{DAE.SubMod}
                  local eq::Option{DAE.EqMod}
                @matchcontinue inMod begin
                  DAE.NOMOD(__)  => begin
                    DAE.NOMOD()
                  end

                  DAE.REDECL(__)  => begin
                    DAE.NOMOD()
                  end

                  DAE.MOD(__)  => begin
                      (mod1, subs) = lookupIdxModification2(inMod.subModLst, inIndex)
                      mod2 = DAE.MOD(inMod.finalPrefix, inMod.eachPrefix, subs, NONE(), inMod.info)
                      mod2 = myMerge(mod2, mod1)
                      eq = indexEqmod(inMod.binding, list(inIndex), inMod.info)
                      mod1 = DAE.MOD(SCode.NOT_FINAL(), inMod.eachPrefix, nil, eq, inMod.info)
                      mod2 = myMerge(mod2, mod1)
                    mod2
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Mod.lookupIdxModification(")
                        Debug.trace(printModStr(inMod))
                        Debug.traceln(", " + ExpressionDump.printExpStr(inIndex) + ") failed")
                      fail()
                  end
                end
              end
          outMod
        end

         #= This function does part of the job for lookupIdxModification. =#
        function lookupIdxModification2(inSubMods::List{<:DAE.SubMod}, inIndex::DAE.Exp) ::Tuple{DAE.Mod, List{DAE.SubMod}}
              local outSubMods::List{DAE.SubMod} = nil
              local outMod::DAE.Mod = DAE.NOMOD()

              local mod::DAE.Mod
              local name::String

              for submod in inSubMods
                @match DAE.NAMEMOD(name, mod) = submod
                mod = lookupIdxModification3(mod, inIndex)
                if ! isNoMod(mod)
                  outSubMods = _cons(DAE.NAMEMOD(name, mod), outSubMods)
                end
              end
               #=  isEmptyMod should be used instead, but the Modification13 test case
               =#
               #=  breaks if empty submods are filtered out...
               =#
              outSubMods = listReverse(outSubMods)
          (outMod, outSubMods)
        end

         #= Helper function to lookupIdxModification2.
           When lookup up the index of a named mod, e.g. y = {1, 2, 3}, it should
           subscript the expression {1, 2, 3} to the corresponding index. =#
        function lookupIdxModification3(inMod::DAE.Mod, inIndex::DAE.Exp) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local subs::List{DAE.SubMod}
                  local eq::Option{DAE.EqMod}
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    DAE.NOMOD()
                  end

                  DAE.REDECL(__)  => begin
                    inMod
                  end

                  DAE.MOD(eachPrefix = SCode.NOT_EACH(__))  => begin
                      (_, subs) = lookupIdxModification2(inMod.subModLst, inIndex)
                      eq = indexEqmod(inMod.binding, list(inIndex), inMod.info)
                    DAE.MOD(inMod.finalPrefix, inMod.eachPrefix, subs, eq, inMod.info)
                  end

                  DAE.MOD(eachPrefix = SCode.EACH(__))  => begin
                    inMod
                  end
                end
              end
          outMod
        end

         #= If there is an equation modification, this function can subscript it using
           the provided indexing expressions. This is used when a modification equates
           an array variable with an array expression. This expression will be expanded
           to produce one equation expression per array component. =#
        function indexEqmod(inBinding::Option{<:DAE.EqMod}, inIndices::List{<:DAE.Exp}, inInfo::SourceInfo) ::Option{DAE.EqMod}
              local outBinding::Option{DAE.EqMod} = inBinding

              local exp::DAE.Exp
              local oval::Option{Values.Value}
              local val::Values.Value
              local ty::DAE.Type
              local c::DAE.Const
              local aexp::Absyn.Exp
              local eq::DAE.EqMod
              local info::SourceInfo

              if isNone(inBinding) || listEmpty(inIndices)
                return outBinding
              end
              @match SOME(eq) = inBinding
              outBinding = begin
                @matchcontinue eq begin
                  DAE.TYPED(modifierAsValue = SOME(Values.ARRAY(valueLst =  nil())))  => begin
                    NONE()
                  end

                  DAE.TYPED(exp, oval, DAE.PROP(ty, c), aexp, info)  => begin
                       #=  Subscripting empty array gives no value. This is needed in e.g. fill(1.0, 0, 2).
                       =#
                       #=  A normal typed binding.
                       =#
                       #=  Subscript the expression with the indices.
                       =#
                      for i in inIndices
                        if ! Types.isArray(ty)
                          Error.addSourceMessage(Error.MODIFIER_NON_ARRAY_TYPE_WARNING, list(ExpressionDump.printExpStr(exp)), inInfo)
                          return outBinding
                        end
                        ty = Types.unliftArray(ty)
                        (exp, _) = ExpressionSimplify.simplify1(Expression.makeASUB(exp, list(i)))
                      end
                       #=  Check that we're not trying to apply a non-array modifier to an
                       =#
                       #=  array, which isn't really allowed but working anyway. Some
                       =#
                       #=  standard Modelica libraries are missing the 'each' keyword
                       =#
                       #=  though (e.g. the DoublePendulum example), and therefore relying
                       =#
                       #=  on this behaviour, so just print a warning here.
                       =#
                       #=  If the modifier has a value, retrieve the indexed elements.
                       =#
                      if isSome(oval)
                        @match SOME(val) = oval
                        for i in inIndices
                          val = ValuesUtil.nthArrayelt(val, Expression.expArrayIndex(i))
                        end
                        oval = SOME(val)
                      end
                    SOME(DAE.TYPED(exp, oval, DAE.PROP(ty, c), aexp, info))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- Mod.indexEqmod failed for mod:\\n " + Types.unparseEqMod(eq) + "\\n indices: " + ExpressionDump.printExpListStr(inIndices))
                      fail()
                  end
                end
              end
          outBinding
        end

         #= myMerges two modifiers, where the outer modifiers overrides the inner one. =#
        function myMerge(inModOuter::DAE.Mod #= The outer mod which should override the inner mod. =#, inModInner::DAE.Mod #= The inner mod. =#, inElementName::String = "", inCheckFinal::Bool = true) ::DAE.Mod
              local outMod::DAE.Mod

              local mod_str::String

              if isEmptyMod(inModOuter)
                outMod = inModInner
              elseif isEmptyMod(inModInner)
                outMod = inModOuter
              elseif inCheckFinal && isFinalMod(inModInner) && ! myMerge_isEqual(inModOuter, inModInner) && ! isRedeclareMod(inModOuter)
                mod_str = unparseModStr(inModOuter)
                Error.addMultiSourceMessage(Error.FINAL_COMPONENT_OVERRIDE, list(inElementName, mod_str), list(getModInfo(inModInner), getModInfo(inModOuter)))
                fail()
              else
                outMod = domyMerge(inModOuter, inModInner, inCheckFinal)
              end
          outMod
        end

        function myMerge_isEqual(inMod1::DAE.Mod, inMod2::DAE.Mod) ::Bool
              local outIsEqual::Bool

              local info1::SourceInfo
              local info2::SourceInfo

              if referenceEq(inMod1, inMod2)
                outIsEqual = true
              else
                info1 = getModInfo(inMod1)
                info2 = getModInfo(inMod2)
                outIsEqual = ! (Util.sourceInfoIsEmpty(info1) || Util.sourceInfoIsEmpty(info2)) && Util.sourceInfoIsEqual(info1, info2)
              end
          outIsEqual
        end

         #= Returns whether a modifier is declared final or not. =#
        function isFinalMod(inMod1::DAE.Mod) ::Bool
              local outMod::Bool

              outMod = begin
                @match inMod1 begin
                  DAE.MOD(finalPrefix = SCode.FINAL(__))  => begin
                    true
                  end

                  DAE.REDECL(element = SCode.COMPONENT(prefixes = SCode.PREFIXES(finalPrefix = SCode.FINAL(__))))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outMod
        end

         #= myMerges two DAE.Mod into one. The first argument is the outer modification
           that should take precedence over the inner modification. =#
        function domyMerge(inModOuter::DAE.Mod #= The outer mod which should overwrite the inner mod. =#, inModInner::DAE.Mod #= The inner mod. =#, inCheckFinal::Bool) ::DAE.Mod
              local outMod::DAE.Mod = inModOuter

              outMod = begin
                  local el1::SCode.Element
                  local el2::SCode.Element
                  local smod1::SCode.Mod
                  local smod2::SCode.Mod
                  local smod::SCode.Mod
                  local emod1::DAE.Mod
                  local emod2::DAE.Mod
                  local emod::DAE.Mod
                  local dmod1::DAE.Mod
                  local dmod2::DAE.Mod
                  local dmod::DAE.Mod
                  local res::SCode.Restriction
                  local info::SourceInfo
                  local eqmod::DAE.EqMod
                  local vals::List{Values.Value}
                  local val::Values.Value
                  local names::List{String}
                  local name::String
                  local submods::List{DAE.SubMod}
                  local submod::DAE.SubMod
                   #=  Redeclaration of component with no constraining class on the inner modifier.
                   =#
                @match (outMod, inModInner) begin
                  (DAE.REDECL(element = SCode.COMPONENT(__)), DAE.REDECL(element = SCode.COMPONENT(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(cc = NONE())))))  => begin
                    inModOuter
                  end

                  (DAE.REDECL(element = el1 && SCode.COMPONENT(__), mod = emod1), DAE.REDECL(element = el2 && SCode.COMPONENT(__), mod = emod2))  => begin
                       #=  Redeclaration of component with constraining class on the inner modifier.
                       =#
                      smod1 = SCodeUtil.getConstrainedByModifiers(el1.prefixes)
                      smod1 = SCodeUtil.mergeModifiers(el1.modifications, smod1)
                      dmod1 = elabUntypedMod(smod1, COMPONENT(el1.name))
                      smod2 = SCodeUtil.getConstrainedByModifiers(el2.prefixes)
                      smod2 = SCodeUtil.mergeModifiers(el2.modifications, smod2)
                      dmod2 = elabUntypedMod(smod2, COMPONENT(el2.name))
                      dmod = myMerge(dmod1, dmod2, el1.name, inCheckFinal)
                      emod = myMerge(emod1, emod2, el1.name, inCheckFinal)
                       #=  If we have a constraining class we don't need the mod.
                       =#
                      Setfield.@set el1.modifications = unelabMod(dmod)
                      Setfield.@set el1.prefixes = SCodeUtil.propagatePrefixes(el2.prefixes, el1.prefixes)
                      Setfield.@set el1.attributes = SCodeUtil.propagateAttributes(el2.attributes, el1.attributes)
                      Setfield.@set outMod.element = el1
                      Setfield.@set outMod.mod = emod
                    outMod
                  end

                  (DAE.REDECL(element = SCode.CLASS(__)), DAE.REDECL(element = SCode.CLASS(prefixes = SCode.PREFIXES(replaceablePrefix = SCode.REPLACEABLE(cc = NONE())))))  => begin
                    inModOuter
                  end

                  (DAE.REDECL(element = el1 && SCode.CLASS(__), mod = emod1), DAE.REDECL(element = el2 && SCode.CLASS(__), mod = emod2))  => begin
                       #=  Redeclaration of class with no constraining class on the inner modifier.
                       =#
                       #=  Redeclaration of class with constraining class on the inner modifier.
                       =#
                      smod1 = SCodeUtil.getConstrainedByModifiers(el1.prefixes)
                      dmod1 = elabUntypedMod(smod1, COMPONENT(el1.name))
                      emod1 = myMerge(emod1, dmod1, el1.name, inCheckFinal)
                      smod2 = SCodeUtil.getConstrainedByModifiers(el2.prefixes)
                      dmod2 = elabUntypedMod(smod2, COMPONENT(el2.name))
                      emod2 = myMerge(emod2, dmod2, el1.name, inCheckFinal)
                      emod = myMerge(emod1, emod2, el1.name, inCheckFinal)
                      Setfield.@set el1.prefixes = SCodeUtil.propagatePrefixes(el2.prefixes, el2.prefixes)
                      (res, info) = SCodeUtil.checkSameRestriction(el1.restriction, el2.restriction, el1.info, el2.info)
                      Setfield.@set el1.restriction = res
                      Setfield.@set el1.info = info
                      Setfield.@set outMod.element = el1
                      Setfield.@set outMod.mod = emod
                    outMod
                  end

                  (DAE.REDECL(element = el1, mod = emod), DAE.MOD(__))  => begin
                      emod = myMerge(emod, inModInner, "", inCheckFinal)
                      Setfield.@set outMod.element = el1
                      Setfield.@set outMod.mod = emod
                    outMod
                  end

                  (DAE.MOD(__), DAE.REDECL(element = el2, mod = emod))  => begin
                      emod = myMerge(inModOuter, emod, "", inCheckFinal)
                    DAE.REDECL(inModInner.finalPrefix, inModInner.eachPrefix, el2, emod)
                  end

                  (DAE.MOD(binding = SOME(eqmod && DAE.TYPED(modifierAsValue = SOME(val && Values.RECORD(__)))), subModLst =  nil()), DAE.MOD(binding = NONE(), subModLst = submods && _ <| _))  => begin
                       #=  The outer modifier has a record binding, while the inner consists of submodifiers.
                       =#
                      names = val.comp
                      vals = nil
                      for v in val.orderd
                        @match _cons(name, names) = names
                        if ValuesUtil.isEmpty(v)
                          try
                            @match (submods, SOME(submod)) = ListUtil.deleteMemberOnTrue(name, submods, isSubModNamed)
                            v = subModValue(submod)
                          catch
                          end
                        end
                        vals = _cons(v, vals)
                      end
                       #=  If the record component doesn't have a binding, use the value
                       =#
                       #=  from the submodifier instead.
                       =#
                      Setfield.@set val.orderd = listReverse(vals)
                      Setfield.@set eqmod.modifierAsValue = SOME(val)
                      Setfield.@set outMod.binding = SOME(eqmod)
                       #=  Remove all submodifier bindings, they have been myMerged into the
                       =#
                       #=  record binding.
                       =#
                      Setfield.@set outMod.subModLst = stripSubModBindings(inModInner.subModLst)
                    outMod
                  end

                  (DAE.MOD(binding = NONE(), subModLst = submods && _ <| _), DAE.MOD(binding = SOME(eqmod && DAE.TYPED(modifierAsValue = SOME(val && Values.RECORD(__)))), subModLst =  nil()))  => begin
                       #=  The outer modifier consists of submodifiers, while the inner has a record binding.
                       =#
                      names = val.comp
                      vals = nil
                      for v in val.orderd
                        @match _cons(name, names) = names
                        try
                          @match (submods, SOME(submod)) = ListUtil.deleteMemberOnTrue(name, submods, isSubModNamed)
                          v = subModValue(submod)
                        catch
                        end
                        vals = _cons(v, vals)
                      end
                       #=  For each component in the record, check if we have a submodifier
                       =#
                       #=  for it. In that case, use the value from the submodifier instead.
                       =#
                      Setfield.@set val.orderd = listReverse(vals)
                      Setfield.@set eqmod.modifierAsValue = SOME(val)
                      Setfield.@set outMod.binding = SOME(eqmod)
                       #=  Remove all submodifier bindings, they have been myMerged into the
                       =#
                       #=  record binding.
                       =#
                      Setfield.@set outMod.subModLst = stripSubModBindings(outMod.subModLst)
                    outMod
                  end

                  (DAE.MOD(__), DAE.MOD(__))  => begin
                      Setfield.@set outMod.subModLst = myMergeSubs(outMod.subModLst, inModInner.subModLst, inCheckFinal)
                      Setfield.@set outMod.binding = myMergeEq(outMod.binding, inModInner.binding)
                    outMod
                  end
                end
              end
          outMod
        end

        function myMergeSubs(inSubMods1::List{<:DAE.SubMod}, inSubMods2::List{<:DAE.SubMod}, inCheckFinal::Bool) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod} = nil

              local submods2::List{DAE.SubMod}
              local name::String
              local m1::DAE.Mod
              local m2::DAE.Mod
              local osm2::Option{DAE.SubMod}
              local sm2::DAE.SubMod

              if listEmpty(inSubMods1)
                outSubMods = inSubMods2
              elseif listEmpty(inSubMods2)
                outSubMods = inSubMods1
              else
                submods2 = inSubMods2
                for sm1 in inSubMods1
                  (submods2, osm2) = ListUtil.deleteMemberOnTrue(subModName(sm1), submods2, subModIsNamed)
                  if isSome(osm2)
                    @match SOME(sm2) = osm2
                    @match DAE.NAMEMOD(ident = name, mod = m1) = sm1
                    @match DAE.NAMEMOD(mod = m2) = sm2
                    m1 = myMerge(m1, m2, name, inCheckFinal)
                    sm1 = DAE.NAMEMOD(name, m1)
                  end
                  outSubMods = _cons(sm1, outSubMods)
                end
                outSubMods = ListUtil.append_reverse(outSubMods, submods2)
              end
          outSubMods
        end

         #= The outer modification, given in the first argument, takes precedence over
           the inner modifications. =#
        function myMergeEq(inOuterEq::Option{<:DAE.EqMod}, inInnerEq::Option{<:DAE.EqMod}) ::Option{DAE.EqMod}
              local outEqMod::Option{DAE.EqMod} = if isSome(inOuterEq)
                    inOuterEq
                  else
                    inInnerEq
                  end
          outEqMod
        end

         #= This function simply extracts the equation part of a modification. =#
        function modEquation(inMod::DAE.Mod) ::Option{DAE.EqMod}
              local outEqMod::Option{DAE.EqMod}

              outEqMod = begin
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    NONE()
                  end

                  DAE.REDECL(__)  => begin
                    NONE()
                  end

                  DAE.MOD(__)  => begin
                    inMod.binding
                  end
                end
              end
          outEqMod
        end

         #=
        same as modEqual with the difference that we allow:
         outer(input arg1: mod1) - modifier to be a subset of
         inner(input arg2: mod2) - modifier,
         IF the subset is cotained in mod2 and those subset matches are equal
         or if outer(expr=NONE()) with inner(expr=(SOME)) =#
        function modSubsetOrEqualOrNonOverlap(mod1::DAE.Mod, mod2::DAE.Mod) ::Bool
              local equal::Bool

              equal = begin
                  local f1::SCode.Final
                  local f2::SCode.Final
                  local each1::SCode.Each
                  local each2::SCode.Each
                  local submods1::List{DAE.SubMod}
                  local submods2::List{DAE.SubMod}
                  local eqmod1::Option{DAE.EqMod}
                  local eqmod2::Option{DAE.EqMod}
                   #=  adrpo: handle non-overlap: final parameter Real eAxis_ia[3](each final unit=\"1\") = {1,2,3};
                   =#
                   #=         mod1 = final each unit=\"1\" mod2 = final = {1,2,3}
                   =#
                   #=         otherwise we get an error as: Error: Variable eAxis_ia: trying to override final variable ...
                   =#
                @matchcontinue (mod1, mod2) begin
                  (DAE.MOD(f1, _, _, NONE(), _), DAE.MOD(f2, SCode.NOT_EACH(__),  nil(), SOME(_), _))  => begin
                      @match true = SCodeUtil.finalEqual(f1, f2)
                    true
                  end

                  (DAE.MOD(binding = eqmod1), DAE.MOD(_, SCode.NOT_EACH(__),  nil(), eqmod2, _))  => begin
                      @match true = eqModSubsetOrEqual(eqmod1, eqmod2)
                    true
                  end

                  (DAE.MOD(f1, each1, submods1, eqmod1, _), DAE.MOD(f2, each2, submods2, eqmod2, _))  => begin
                      @match true = SCodeUtil.finalEqual(f1, f2)
                      @match true = SCodeUtil.eachEqual(each1, each2)
                      @match true = subModsEqual(submods1, submods2)
                      @match true = eqModSubsetOrEqual(eqmod1, eqmod2)
                    true
                  end

                  (DAE.REDECL(f1, each1), DAE.REDECL(f2, each2))  => begin
                      @match true = SCodeUtil.finalEqual(f1, f2)
                      @match true = SCodeUtil.eachEqual(each1, each2)
                      @match true = SCodeUtil.elementEqual(mod1.element, mod2.element)
                    true
                  end

                  (DAE.NOMOD(__), DAE.NOMOD(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  handle subset equal
               =#
               #=  two exactly the same mod, return just one! (used when it is REDECL or a submod is REDECL)
               =#
          equal
        end

         #=
        Returns true if two EqMods are equal or outer(input arg1) is NONE =#
        function eqModSubsetOrEqual(eqMod1::Option{<:DAE.EqMod}, eqMod2::Option{<:DAE.EqMod}) ::Bool
              local equal::Bool

              equal = begin
                  local aexp1::Absyn.Exp
                  local aexp2::Absyn.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local teq::DAE.EqMod
                   #=  no mods
                   =#
                @matchcontinue (eqMod1, eqMod2) begin
                  (NONE(), NONE())  => begin
                    true
                  end

                  (NONE(), SOME(_))  => begin
                    true
                  end

                  (SOME(DAE.TYPED(__)), SOME(DAE.TYPED(__)))  => begin
                      @match true = eqModEqual(eqMod1, eqMod2)
                    true
                  end

                  (SOME(DAE.TYPED(modifierAsAbsynExp = aexp1)), SOME(DAE.UNTYPED(exp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  (SOME(DAE.UNTYPED(exp = aexp1)), SOME(DAE.TYPED(modifierAsAbsynExp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  (SOME(DAE.UNTYPED(exp = aexp1)), SOME(DAE.UNTYPED(exp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  none vs. some (subset) mods
               =#
               #=  typed mods
               =#
               #=  typed vs. untyped mods
               =#
               #=  untyped vs. typed
               =#
               #=  untyped mods
               =#
               #=  anything else gives false
               =#
          equal
        end

         #=
        Returns true if two submod lists are equal. Or all of the elements in subModLst1 have equalities in subModLst2.
        if subModLst2 then contain more elements is not a mather. =#
        function subModsSubsetOrEqual(subModLst1::List{<:DAE.SubMod}, subModLst2::List{<:DAE.SubMod}) ::Bool
              local equal::Bool

              equal = begin
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local indx1::List{ModelicaInteger}
                  local indx2::List{ModelicaInteger}
                  local blst1::List{Bool}
                  local rest1::List{DAE.SubMod}
                  local rest2::List{DAE.SubMod}
                @matchcontinue (subModLst1, subModLst2) begin
                  ( nil(),  nil())  => begin
                    true
                  end

                  (DAE.NAMEMOD(id1, mod1) <| rest1, DAE.NAMEMOD(id2, mod2) <| rest2)  => begin
                      @match true = stringEq(id1, id2)
                      @match true = modEqual(mod1, mod2)
                      @match true = subModsEqual(rest1, rest2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  otherwise false
               =#
          equal
        end

         #=
        Compares two DAE.Mod, returns true if equal =#
        function modEqual(mod1::DAE.Mod, mod2::DAE.Mod) ::Bool
              local equal::Bool

              equal = begin
                @match (mod1, mod2) begin
                  (DAE.MOD(__), DAE.MOD(__))  => begin
                    SCodeUtil.finalEqual(mod1.finalPrefix, mod2.finalPrefix) && SCodeUtil.eachEqual(mod1.eachPrefix, mod2.eachPrefix) && ListUtil.isEqualOnTrue(mod1.subModLst, mod2.subModLst, subModEqual) && eqModEqual(mod1.binding, mod2.binding)
                  end

                  (DAE.REDECL(__), DAE.REDECL(__))  => begin
                    SCodeUtil.finalEqual(mod1.finalPrefix, mod2.finalPrefix) && SCodeUtil.eachEqual(mod1.eachPrefix, mod2.eachPrefix) && SCodeUtil.elementEqual(mod1.element, mod2.element)
                  end

                  (DAE.NOMOD(__), DAE.NOMOD(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          equal
        end

         #= Returns true if two submod lists are equal. =#
        function subModsEqual(inSubModLst1::List{<:DAE.SubMod}, inSubModLst2::List{<:DAE.SubMod}) ::Bool
              local equal::Bool

              equal = begin
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local indx1::List{ModelicaInteger}
                  local indx2::List{ModelicaInteger}
                  local subModLst1::List{DAE.SubMod}
                  local subModLst2::List{DAE.SubMod}
                @matchcontinue (inSubModLst1, inSubModLst2) begin
                  ( nil(),  nil())  => begin
                    true
                  end

                  (DAE.NAMEMOD(id1, mod1) <| subModLst1, DAE.NAMEMOD(id2, mod2) <| subModLst2)  => begin
                      @match true = stringEq(id1, id2)
                      @match true = modEqual(mod1, mod2)
                      @match true = subModsEqual(subModLst1, subModLst2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  otherwise false
               =#
          equal
        end

         #= Returns true if two submod are equal. =#
        function subModEqual(subMod1::DAE.SubMod, subMod2::DAE.SubMod) ::Bool
              local equal::Bool

              equal = begin
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                  local mod1::DAE.Mod
                  local mod2::DAE.Mod
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local indx1::List{ModelicaInteger}
                  local indx2::List{ModelicaInteger}
                  local blst1::List{Bool}
                @match (subMod1, subMod2) begin
                  (DAE.NAMEMOD(id1, mod1), DAE.NAMEMOD(id2, mod2)) where (stringEq(id1, id2) && modEqual(mod1, mod2))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  otherwise false
               =#
          equal
        end

        function valEqual(inV1::Option{<:Values.Value}, inV2::Option{<:Values.Value}, equal::Bool) ::Bool
              local bEq::Bool

              bEq = begin
                  local v1::Values.Value
                  local v2::Values.Value
                @match (inV1, inV2, equal) begin
                  (_, _, true)  => begin
                    true
                  end

                  (NONE(), NONE(), _)  => begin
                    equal
                  end

                  (SOME(v1), SOME(v2), false)  => begin
                      bEq = Expression.expEqual(ValuesUtil.valueExp(v1), ValuesUtil.valueExp(v2))
                    bEq
                  end
                end
              end
          bEq
        end

         #= Returns true if two EqMods are equal =#
        function eqModEqual(eqMod1::Option{<:DAE.EqMod}, eqMod2::Option{<:DAE.EqMod}) ::Bool
              local equal::Bool

              equal = begin
                  local aexp1::Absyn.Exp
                  local aexp2::Absyn.Exp
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local v1::Option{Values.Value}
                  local v2::Option{Values.Value}
                   #=  no equ mods
                   =#
                @matchcontinue (eqMod1, eqMod2) begin
                  (NONE(), NONE())  => begin
                    true
                  end

                  (SOME(DAE.TYPED(modifierAsExp = exp1, modifierAsValue = v1)), SOME(DAE.TYPED(modifierAsExp = exp2, modifierAsValue = v2)))  => begin
                      equal = Expression.expEqual(exp1, exp2)
                      @match true = valEqual(v1, v2, equal)
                    true
                  end

                  (SOME(DAE.TYPED(modifierAsAbsynExp = aexp1)), SOME(DAE.UNTYPED(exp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  (SOME(DAE.UNTYPED(exp = aexp1)), SOME(DAE.TYPED(modifierAsAbsynExp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  (SOME(DAE.UNTYPED(exp = aexp1)), SOME(DAE.UNTYPED(exp = aexp2)))  => begin
                      @match true = AbsynUtil.expEqual(aexp1, aexp2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  typed equmods
               =#
               #=  check the values as crefs might have been replaced!
               =#
               #=  typed vs. untyped equmods
               =#
               #=  untyped vs. typed equmods
               =#
               #=  untyped equmods
               =#
               #=  anything else will give false
               =#
          equal
        end

         #= This function prints a modification.
         It uses a few other function to do its stuff. =#
        function printModStr(inMod::DAE.Mod) ::String
              local outString::String

              outString = begin
                  local prefix::String
                  local str::String
                  local res::String
                  local s1_1::String
                  local s2::String
                  local s1::List{String}
                  local finalPrefix::SCode.Final
                  local eachPrefix::SCode.Each
                  local subs::List{DAE.SubMod}
                  local eq::Option{DAE.EqMod}
                @matchcontinue inMod begin
                  DAE.NOMOD(__)  => begin
                    "()"
                  end

                  DAE.REDECL(finalPrefix = finalPrefix, eachPrefix = eachPrefix)  => begin
                      prefix = SCodeDump.finalStr(finalPrefix) + SCodeDump.eachStr(eachPrefix)
                      str = SCodeDump.unparseElementStr(inMod.element)
                      res = stringAppendList(list("(", prefix, str, ")"))
                    res
                  end

                  DAE.MOD(finalPrefix = finalPrefix, eachPrefix = eachPrefix, subModLst = subs, binding = eq)  => begin
                      prefix = SCodeDump.finalStr(finalPrefix) + SCodeDump.eachStr(eachPrefix)
                      s1 = printSubs1Str(subs)
                      s1_1 = stringDelimitList(s1, ", ")
                      s1_1 = if ! listEmpty(subs)
                            " {" + s1_1 + "} "
                          else
                            s1_1
                          end
                      s2 = printEqmodStr(eq)
                      str = stringAppendList(list(prefix, s1_1, s2))
                    str
                  end

                  _  => begin
                        print(" failure in printModStr \\n")
                      fail()
                  end
                end
              end
          outString
        end

         #= Print a modifier on the Print buffer. =#
        function printMod(m::DAE.Mod)
              local str::String

              str = printModStr(m)
              Print.printBuf(str)
        end

         #=
        Author BZ, 2009-07
        Prints a readable format of a modifier. =#
        function prettyPrintMod(m::DAE.Mod, depth::ModelicaInteger) ::String
              local str::String

              str = begin
                  local subs::List{DAE.SubMod}
                  local fp::SCode.Final
                  local eq::DAE.EqMod
                @matchcontinue (m, depth) begin
                  (DAE.MOD(subModLst = subs, binding = NONE()), _)  => begin
                    prettyPrintSubs(subs, depth)
                  end

                  (DAE.MOD(finalPrefix = fp, binding = SOME(eq)), _)  => begin
                    (if SCodeUtil.finalBool(fp)
                          "final "
                        else
                          ""
                        end) + " = " + Types.unparseEqMod(eq)
                  end

                  (DAE.REDECL(__), _)  => begin
                    SCodeDump.unparseElementStr(m.element)
                  end

                  (DAE.NOMOD(__), _)  => begin
                    ""
                  end

                  _  => begin
                        print(" failed prettyPrintMod\\n")
                      fail()
                  end
                end
              end
          str
        end

         #=
        Author BZ
        Helper function for prettyPrintMod =#
        function prettyPrintSubs(inSubs::List{<:DAE.SubMod}, depth::ModelicaInteger) ::String
              local str::String

              str = begin
                  local s1::String
                  local s2::String
                  local id::String
                  local s::DAE.SubMod
                  local m::DAE.Mod
                  local li::List{ModelicaInteger}
                  local subs::List{DAE.SubMod}
                @match (inSubs, depth) begin
                  ( nil(), _)  => begin
                    ""
                  end

                  (DAE.NAMEMOD(id, DAE.REDECL(__)) <| _, _)  => begin
                      s2 = " redeclare(" + id + "), class or component " + id
                    s2
                  end

                  (DAE.NAMEMOD(id, m) <| _, _)  => begin
                      s2 = prettyPrintMod(m, depth + 1)
                      s2 = "(" + id + s2 + "), class or component " + id
                    s2
                  end
                end
              end
          str
        end

         #=
        Prints a readable format of a sub-modifier, used in error reporting for built-in classes =#
        function prettyPrintSubmod(inSub::DAE.SubMod) ::String
              local str::String

              str = begin
                  local s1::String
                  local s2::String
                  local id::String
                  local m::DAE.Mod
                  local li::List{ModelicaInteger}
                  local fp::SCode.Final
                  local ep::SCode.Each
                  local el::SCode.Element
                @match inSub begin
                  DAE.NAMEMOD(id, m && DAE.REDECL(__))  => begin
                      s1 = SCodeDump.unparseElementStr(m.element)
                      s2 = id + "(redeclare " + (if SCodeUtil.eachBool(m.eachPrefix)
                            "each "
                          else
                            ""
                          end) + (if SCodeUtil.finalBool(m.finalPrefix)
                            "final "
                          else
                            ""
                          end) + s1 + ")"
                    s2
                  end

                  DAE.NAMEMOD(id, m)  => begin
                      s2 = prettyPrintMod(m, 0)
                      s2 = id + s2
                    s2
                  end
                end
              end
          str
        end

         #= Helper function to printModStr =#
        function printSubs1Str(inTypesSubModLst::List{<:DAE.SubMod}) ::List{String}
              local outStringLst::List{String}

              outStringLst = begin
                  local s1::String
                  local res::List{String}
                  local x::DAE.SubMod
                  local xs::List{DAE.SubMod}
                @match inTypesSubModLst begin
                   nil()  => begin
                    nil
                  end

                  x <| xs  => begin
                      s1 = printSubStr(x)
                      res = printSubs1Str(xs)
                    _cons(s1, res)
                  end
                end
              end
          outStringLst
        end

         #= Helper function to printSubs1Str =#
        function printSubStr(inSubMod::DAE.SubMod) ::String
              local outString::String

              outString = begin
                  local mod_str::String
                  local res::String
                  local n::String
                  local str::String
                  local mod::DAE.Mod
                  local ss::List{ModelicaInteger}
                @match inSubMod begin
                  DAE.NAMEMOD(ident = n, mod = mod)  => begin
                      mod_str = printModStr(mod)
                      res = stringAppend(n + " ", mod_str)
                    res
                  end
                end
              end
          outString
        end

         #= Helper function to printModStr =#
        function printEqmodStr(inTypesEqModOption::Option{<:DAE.EqMod}) ::String
              local outString::String

              outString = begin
                  local str::String
                  local str2::String
                  local e_val_str::String
                  local res::String
                  local e::DAE.Exp
                  local e_val::Values.Value
                  local prop::DAE.Properties
                  local ae::Absyn.Exp
                @matchcontinue inTypesEqModOption begin
                  NONE()  => begin
                    ""
                  end

                  SOME(DAE.TYPED(e, SOME(e_val), prop, _))  => begin
                      str = ExpressionDump.printExpStr(e)
                      str2 = Types.printPropStr(prop)
                      e_val_str = ValuesUtil.valString(e_val)
                      res = stringAppendList(list(" = (typed)", str, " ", str2, ", value: ", e_val_str))
                    res
                  end

                  SOME(DAE.TYPED(e, NONE(), prop, _))  => begin
                      str = ExpressionDump.printExpStr(e)
                      str2 = Types.printPropStr(prop)
                      res = stringAppendList(list(" = (typed)", str, ", type:\\n", str2))
                    res
                  end

                  SOME(DAE.UNTYPED(exp = ae))  => begin
                      str = Dump.printExpStr(ae)
                      res = stringAppend(" =(untyped) ", str)
                    res
                  end

                  _  => begin
                        res = "---Mod.printEqmodStr FAILED---"
                      res
                  end
                end
              end
          outString
        end

        function renameTopLevelNamedSubMod(mod::DAE.Mod, oldIdent::String, newIdent::String) ::DAE.Mod
              local outMod::DAE.Mod = mod

              outMod = begin
                @match outMod begin
                  DAE.MOD(__)  => begin
                      Setfield.@set outMod.subModLst = list(renameNamedSubMod(s, oldIdent, newIdent) for s in outMod.subModLst)
                    outMod
                  end

                  _  => begin
                      mod
                  end
                end
              end
          outMod
        end

        function renameNamedSubMod(submod::DAE.SubMod, oldIdent::String, newIdent::String) ::DAE.SubMod
              local outMod::DAE.SubMod

              outMod = begin
                  local mod::DAE.Mod
                  local id::String
                @match (submod, oldIdent, newIdent) begin
                  (DAE.NAMEMOD(id, mod), _, _) where (stringEq(id, oldIdent))  => begin
                    DAE.NAMEMOD(newIdent, mod)
                  end

                  _  => begin
                      submod
                  end
                end
              end
          outMod
        end

        function emptyModOrEquality(mod::DAE.Mod) ::Bool
              local b::Bool

              b = begin
                @match mod begin
                  DAE.NOMOD(__)  => begin
                    true
                  end

                  DAE.MOD(subModLst =  nil())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function intStringDot(i::ModelicaInteger) ::String
              local str::String

              str = intString(i) + "."
          str
        end

        function isPrefixOf(indexSubMod::Tuple{<:String, DAE.SubMod}, idx::String) ::Bool
              local isPrefix::Bool

              isPrefix = begin
                  local i::String
                  local len1::ModelicaInteger
                  local len2::ModelicaInteger
                @matchcontinue (indexSubMod, idx) begin
                  ((i, _), _)  => begin
                      len1 = stringLength(i)
                      len2 = stringLength(idx)
                      @match true = boolOr(0 == System.strncmp(i, idx, len1), 0 == System.strncmp(idx, i, len2))
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  either one of them is a substring of the other
               =#
          isPrefix
        end

         #= @author: adrpo
          This function will create fully qualified crefs from
          modifications. See also getFullModsFromSubMods.
          Examples:
          x(start=1, stateSelect=s) => x.start, x.stateSelect
          (x.start=1, x.stateSelect=s) => x.start, x.stateSelect
          x([2] = 1, start = 2) => x[2], x.start =#
        function getFullModsFromMod(inTopCref::DAE.ComponentRef, inMod::DAE.Mod) ::List{FullMod}
              local outFullMods::List{FullMod}

              outFullMods = begin
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    nil
                  end

                  DAE.MOD(__)  => begin
                    getFullModsFromSubMods(inTopCref, inMod.subModLst)
                  end

                  DAE.REDECL(__)  => begin
                    list(getFullModFromModRedeclare(inTopCref, inMod))
                  end
                end
              end
               #=  DAE.NOMOD empty case, no more dive in
               =#
               #=  DAE.MOD
               =#
               #=  DAE.REDECL
               =#
          outFullMods
        end

         #= @author: adrpo
          This function will create fully qualified
          crefs from the redeclaration lists for redeclare mod.
          See also getFullModsFromMod, getFullModsFromSubMod
          Examples:
          x(redeclare package P = P, redeclare class C = C) => x.P, x.C =#
        function getFullModFromModRedeclare(inTopCref::DAE.ComponentRef, inRedeclare::DAE.Mod) ::FullMod
              local outFullMod::FullMod

              local el::SCode.Element
              local id::DAE.Ident
              local cref::DAE.ComponentRef

              @match DAE.REDECL(element = el) = inRedeclare
              id = SCodeUtil.elementName(el)
              cref = CrefForHashTable.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil)
              cref = CrefForHashTable.joinCrefs(inTopCref, cref)
              outFullMod = MOD(cref, inRedeclare)
          outFullMod
        end

         #= @author: adrpo
          This function will create fully qualified crefs from
          sub modifications. See also getFullModsFromMod.
          Examples:
          x(start=1, stateSelect=s) => x.start, x.stateSelect
          (x.start=1, x.stateSelect=s) => x.start, x.stateSelect
          x([2] = 1, start = 2) => x[2], x.start =#
        function getFullModsFromSubMods(inTopCref::DAE.ComponentRef, inSubMods::List{<:DAE.SubMod}) ::List{FullMod}
              local outFullMods::List{FullMod}

              outFullMods = begin
                  local fullMods1::List{FullMod}
                  local fullMods2::List{FullMod}
                  local fullMods::List{FullMod}
                  local rest::List{DAE.SubMod}
                  local subMod::DAE.SubMod
                  local id::DAE.Ident
                  local mod::DAE.Mod
                  local indexes::List{ModelicaInteger}
                  local cref::DAE.ComponentRef
                   #=  empty case
                   =#
                @match (inTopCref, inSubMods) begin
                  (_,  nil())  => begin
                    nil
                  end

                  (_, subMod && DAE.NAMEMOD(id, mod) <| rest)  => begin
                      cref = CrefForHashTable.joinCrefs(inTopCref, CrefForHashTable.makeCrefIdent(id, DAE.T_UNKNOWN_DEFAULT, nil))
                      fullMods1 = getFullModsFromMod(cref, mod)
                      fullMods2 = getFullModsFromSubMods(inTopCref, rest)
                      fullMods = listAppend(if listEmpty(fullMods1)
                            _cons(SUB_MOD(cref, subMod), fullMods1)
                          else
                            fullMods1
                          end, fullMods2)
                    fullMods
                  end
                end
              end
               #=  named modifier, only add LEAFS to the list!
               =#
               #=  add if LEAF
               =#
          outFullMods
        end

         #= @author: adrpo
          This function checks if the crefs of the given full mods are equal =#
        function fullModCrefsEqual(inFullMod1::FullMod, inFullMod2::FullMod) ::Bool
              local isEqual::Bool

              isEqual = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                @match (inFullMod1, inFullMod2) begin
                  (MOD(cr1, _), MOD(cr2, _))  => begin
                    CrefForHashTable.crefEqualNoStringCompare(cr1, cr2)
                  end

                  (SUB_MOD(cr1, _), SUB_MOD(cr2, _))  => begin
                    CrefForHashTable.crefEqualNoStringCompare(cr1, cr2)
                  end

                  (MOD(cr1, _), SUB_MOD(cr2, _))  => begin
                    CrefForHashTable.crefEqualNoStringCompare(cr1, cr2)
                  end

                  (SUB_MOD(cr1, _), MOD(cr2, _))  => begin
                    CrefForHashTable.crefEqualNoStringCompare(cr1, cr2)
                  end
                end
              end
          isEqual
        end

         #= @author: adrpo
          This function checks if the crefs of the given full mods are equal =#
        function prettyPrintFullMod(inFullMod::FullMod, inDepth::ModelicaInteger) ::String
              local outStr::String

              outStr = begin
                  local mod::DAE.Mod
                  local subMod::DAE.SubMod
                  local cr::DAE.ComponentRef
                  local str::String
                @match (inFullMod, inDepth) begin
                  (MOD(cr, mod), _)  => begin
                      str = CrefForHashTable.printComponentRefStr(cr) + ": " + prettyPrintMod(mod, inDepth)
                    str
                  end

                  (SUB_MOD(cr, subMod), _)  => begin
                      str = CrefForHashTable.printComponentRefStr(cr) + ": " + prettyPrintSubmod(subMod)
                    str
                  end
                end
              end
          outStr
        end

        function getUnelabedSubMod(inMod::SCode.Mod, inIdent::SCode.Ident) ::SCode.Mod
              local outSubMod::SCode.Mod

              local submods::List{SCode.SubMod}

              @match SCode.MOD(subModLst = submods) = inMod
              outSubMod = getUnelabedSubMod2(submods, inIdent)
          outSubMod
        end

        function getUnelabedSubMod2(inSubMods::List{<:SCode.SubMod}, inIdent::SCode.Ident) ::SCode.Mod
              local outMod::SCode.Mod

              outMod = begin
                  local id::SCode.Ident
                  local m::SCode.Mod
                  local rest_mods::List{SCode.SubMod}
                @matchcontinue (inSubMods, inIdent) begin
                  (SCode.NAMEMOD(ident = id, mod = m) <| _, _)  => begin
                      @match true = stringEqual(id, inIdent)
                    m
                  end

                  (_ <| rest_mods, _)  => begin
                    getUnelabedSubMod2(rest_mods, inIdent)
                  end
                end
              end
          outMod
        end

         #= Returns true if a modifier contains any untyped parts, otherwise false. =#
        function isUntypedMod(inMod::DAE.Mod) ::Bool
              local outIsUntyped::Bool

              outIsUntyped = begin
                  local submods::List{DAE.SubMod}
                @matchcontinue inMod begin
                  DAE.MOD(binding = SOME(DAE.UNTYPED(__)))  => begin
                    true
                  end

                  DAE.MOD(subModLst = submods)  => begin
                      _ = ListUtil.find(submods, isUntypedSubMod)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsUntyped
        end

         #= Returns true if a submodifier contains any untyped parts, otherwise false. =#
        function isUntypedSubMod(inSubMod::DAE.SubMod) ::Bool
              local outIsUntyped::Bool

              local mod::DAE.Mod

              @match DAE.NAMEMOD(mod = mod) = inSubMod
              outIsUntyped = isUntypedMod(mod)
          outIsUntyped
        end

        function getUntypedCrefs(inMod::DAE.Mod) ::List{Absyn.ComponentRef}
              local outCrefs::List{Absyn.ComponentRef}

              outCrefs = begin
                  local exp::Absyn.Exp
                  local crefs::List{Absyn.ComponentRef}
                  local submods::List{DAE.SubMod}
                @matchcontinue inMod begin
                  DAE.MOD(binding = SOME(DAE.UNTYPED(exp = exp)))  => begin
                      crefs = AbsynUtil.getCrefFromExp(exp, true, true)
                    crefs
                  end

                  DAE.MOD(subModLst = submods)  => begin
                      crefs = ListUtil.fold(submods, getUntypedCrefFromSubMod, nil)
                    crefs
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outCrefs
        end

        function getUntypedCrefFromSubMod(inSubMod::DAE.SubMod, inCrefs::List{<:Absyn.ComponentRef}) ::List{Absyn.ComponentRef}
              local outCrefs::List{Absyn.ComponentRef}

              outCrefs = begin
                  local mod::DAE.Mod
                  local crefs::List{Absyn.ComponentRef}
                @match (inSubMod, inCrefs) begin
                  (DAE.NAMEMOD(mod = mod), _)  => begin
                      crefs = getUntypedCrefs(mod)
                    listAppend(crefs, inCrefs)
                  end
                end
              end
          outCrefs
        end

         #=  moved from Types!
         =#

         #= author: PA
          Removes the sub modifiers of a modifier. =#
        function stripSubmod(inMod::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod = inMod

              outMod = begin
                @match outMod begin
                  DAE.MOD(__)  => begin
                      Setfield.@set outMod.subModLst = nil
                    outMod
                  end

                  _  => begin
                      outMod
                  end
                end
              end
          outMod
        end

         #=
        Author: BZ, 2009-08
        Removed REDECLARE() statements at first level of SubMods =#
        function removeFirstSubsRedecl(inMod::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local f::SCode.Final
                  local each_::SCode.Each
                  local subs::List{SubMod}
                  local eq::Option{EqMod}
                  local m::DAE.Mod
                  local info::SourceInfo
                @matchcontinue inMod begin
                  DAE.MOD(finalPrefix = f, eachPrefix = each_, subModLst =  nil(), binding = eq, info = info)  => begin
                    DAE.MOD(f, each_, nil, eq, info)
                  end

                  DAE.MOD(subModLst = subs, binding = NONE())  => begin
                      @match nil = removeRedecl(subs)
                    DAE.NOMOD()
                  end

                  DAE.MOD(finalPrefix = f, eachPrefix = each_, subModLst = subs, binding = eq, info = info)  => begin
                      subs = removeRedecl(subs)
                    DAE.MOD(f, each_, subs, eq, info)
                  end

                  m  => begin
                    m
                  end
                end
              end
          outMod
        end

         #=
        Author BZ
        helper function for removeFirstSubsRedecl =#
        function removeRedecl(isubs::List{<:SubMod}) ::List{SubMod}
              local osubs::List{SubMod}

              osubs = begin
                  local sm::SubMod
                  local s::String
                  local subs::List{SubMod}
                @match isubs begin
                   nil()  => begin
                    nil
                  end

                  DAE.NAMEMOD(_, DAE.REDECL(__)) <| subs  => begin
                    removeRedecl(subs)
                  end

                  sm <| subs  => begin
                      osubs = removeRedecl(subs)
                    _cons(sm, osubs)
                  end
                end
              end
          osubs
        end

         #=
        Author BZ, 2009-07
        Delete a list of named modifiers =#
        function removeModList(inMod::DAE.Mod, remStrings::List{<:String}) ::DAE.Mod
              local outMod::DAE.Mod

              local s::String

              outMod = begin
                  local rest::List{String}
                @match (inMod, remStrings) begin
                  (_,  nil())  => begin
                    inMod
                  end

                  (_, s <| _)  => begin
                    removeModList(removeMod(inMod, s), remStrings)
                  end
                end
              end
          outMod
        end

         #=
        Author: BZ, 2009-05
        Remove a modifier(/s) on a specified component. =#
        function removeMod(inMod::DAE.Mod, componentModified::String) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local f::SCode.Final
                  local e::SCode.Each
                  local subs::List{SubMod}
                  local oem::Option{EqMod}
                  local info::SourceInfo
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    DAE.NOMOD()
                  end

                  DAE.REDECL(__)  => begin
                    if SCodeUtil.elementName(inMod.element) == componentModified
                          DAE.NOMOD()
                        else
                          inMod
                        end
                  end

                  DAE.MOD(f, e, subs, oem, info)  => begin
                      subs = removeModInSubs(subs, componentModified)
                      outMod = DAE.MOD(f, e, subs, oem, info)
                    outMod
                  end
                end
              end
               #= fprint(Flags.REDECL,\"Removing redeclare mods: \" + componentModified +\" before\" + Mod.printModStr(inmod) + \"\\n\");
               =#
               #= fprint(Flags.REDECL,\"Removing redeclare mods: \" + componentModified +\" after\" + Mod.printModStr(outmod) + \"\\n\");
               =#
          outMod
        end

         #=
        Author BZ, 2009-05
        Helper function for removeMod, removes modifiers in submods;
         =#
        function removeModInSubs(inSubs::List{<:SubMod}, componentName::String) ::List{SubMod}
              local outsubs::List{SubMod}

              outsubs = begin
                  local m1::DAE.Mod
                  local subs1::List{SubMod}
                  local subs2::List{SubMod}
                  local subs::List{SubMod}
                  local s1::String
                  local sub::SubMod
                @match (inSubs, componentName) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.NAMEMOD(s1, m1) <| subs, _)  => begin
                      subs1 = if stringEq(s1, componentName)
                            nil
                          else
                            list(DAE.NAMEMOD(s1, m1))
                          end
                      subs2 = removeModInSubs(subs, componentName) #= check for multiple mod on same comp =#
                      outsubs = listAppend(subs1, subs2)
                    outsubs
                  end
                end
              end
          outsubs
        end

         #= This function adds each to the mods
         if the dimensions are not empty. =#
        function addEachIfNeeded(inMod::DAE.Mod, inDimensions::DAE.Dimensions) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local finalPrefix::SCode.Final
                  local el::SCode.Element
                  local mod::DAE.Mod
                  local eachPrefix::SCode.Each
                  local subs::List{DAE.SubMod}
                  local eq::Option{DAE.EqMod}
                  local info::SourceInfo
                @matchcontinue (inMod, inDimensions) begin
                  (_,  nil())  => begin
                    inMod
                  end

                  (DAE.NOMOD(__), _)  => begin
                    DAE.NOMOD()
                  end

                  (DAE.REDECL(finalPrefix, _, el, mod), _)  => begin
                    DAE.REDECL(finalPrefix, SCode.EACH(), el, mod)
                  end

                  (DAE.MOD(finalPrefix, SCode.EACH(__), subs, eq, info), _)  => begin
                    DAE.MOD(finalPrefix, SCode.EACH(), subs, eq, info)
                  end

                  (DAE.MOD(finalPrefix, eachPrefix, subs, eq, info), _)  => begin
                      subs = addEachToSubsIfNeeded(subs, inDimensions)
                    DAE.MOD(finalPrefix, eachPrefix, subs, eq, info)
                  end

                  _  => begin
                        print("Mod.addEachIfNeeded failed on: " + printModStr(inMod) + "\\n")
                      fail()
                  end
                end
              end
               #=  do not each the subs of already each'ed mod
               =#
          outMod
        end

         #= This function adds each to the mods
         if the dimensions are not empty. =#
        function addEachOneLevel(inMod::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod

              outMod = begin
                  local finalPrefix::SCode.Final
                  local el::SCode.Element
                  local mod::DAE.Mod
                  local eachPrefix::SCode.Each
                  local subs::List{DAE.SubMod}
                  local eq::Option{DAE.EqMod}
                  local info::SourceInfo
                @matchcontinue inMod begin
                  DAE.NOMOD(__)  => begin
                    DAE.NOMOD()
                  end

                  DAE.REDECL(finalPrefix, _, el, mod)  => begin
                    DAE.REDECL(finalPrefix, SCode.EACH(), el, mod)
                  end

                  DAE.MOD(finalPrefix, _, subs, eq, info)  => begin
                    DAE.MOD(finalPrefix, SCode.EACH(), subs, eq, info)
                  end

                  _  => begin
                        print("Mod.addEachOneLevel failed on: " + printModStr(inMod) + "\\n")
                      fail()
                  end
                end
              end
          outMod
        end

        function addEachToSubsIfNeeded(inSubMods::List{<:DAE.SubMod}, inDimensions::DAE.Dimensions) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod}

              outSubMods = begin
                  local rest::List{DAE.SubMod}
                  local m::DAE.Mod
                  local id::String
                  local idxs::List{ModelicaInteger}
                @match (inSubMods, inDimensions) begin
                  (_,  nil())  => begin
                    inSubMods
                  end

                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.NAMEMOD(id, m) <| rest, _)  => begin
                      m = addEachOneLevel(m)
                      rest = addEachToSubsIfNeeded(rest, inDimensions)
                    _cons(DAE.NAMEMOD(id, m), rest)
                  end
                end
              end
          outSubMods
        end

         #= @author: adrpo
         returns true if this is an empty modifier =#
        function isEmptyMod(inMod::DAE.Mod) ::Bool
              local isEmpty::Bool

              isEmpty = begin
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    true
                  end

                  DAE.MOD(subModLst =  nil(), binding = NONE())  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  That's a NOMOD() if I ever saw one...
               =#
          isEmpty
        end

        function isNoMod(inMod::DAE.Mod) ::Bool
              local outIsNoMod::Bool

              outIsNoMod = begin
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsNoMod
        end

        function getModInfo(inMod::DAE.Mod) ::SourceInfo
              local outInfo::SourceInfo

              outInfo = begin
                  local info::SourceInfo
                  local e::SCode.Element
                @match inMod begin
                  DAE.MOD(__)  => begin
                    inMod.info
                  end

                  DAE.REDECL(__)  => begin
                    SCodeUtil.elementInfo(inMod.element)
                  end

                  _  => begin
                      AbsynUtil.dummyInfo
                  end
                end
              end
          outInfo
        end

        function isRedeclareMod(inMod::DAE.Mod) ::Bool
              local yes::Bool

              yes = begin
                @match inMod begin
                  DAE.REDECL(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          yes
        end


         #= return the modifier present in the environment for this class or DAE.NOMOD if ther is none =#
        function getClassModifier(inEnv::FCore.Graph, inName::FCore.Name) ::DAE.Mod
              local outMod::DAE.Mod

              local n::FCore.Node
              local mod::DAE.Mod

              outMod = begin
                @matchcontinue (inEnv, inName) begin
                  (_, _)  => begin
                      n = FNode.fromRef(FNode.child(FGraphUtil.lastScopeRef(inEnv), inName))
                      if ! FNode.isInstance(FNode.fromRef(FGraphUtil.lastScopeRef(inEnv)))
                        @match FCore.N(data = FCore.CL(mod = mod)) = n
                        mod = Mod.removeMod(mod, inName)
                      else
                        mod = DAE.NOMOD()
                      end
                    mod
                  end

                  _  => begin
                      DAE.NOMOD()
                  end
                end
              end
          outMod
        end

        function subModValue(inSubMod::DAE.SubMod) ::Values.Value
              local outValue::Values.Value

              @match DAE.NAMEMOD(mod = DAE.MOD(binding = SOME(DAE.TYPED(modifierAsValue = SOME(outValue))))) = inSubMod
          outValue
        end

        function subModName(inSubMod::DAE.SubMod) ::DAE.Ident
              local outName::DAE.Ident

              @match DAE.NAMEMOD(ident = outName) = inSubMod
          outName
        end

        function subModIsNamed(inName::String, inSubMod::DAE.SubMod) ::Bool
              local outNameEq::Bool

              outNameEq = inName == subModName(inSubMod)
          outNameEq
        end

        function subModInfo(inSubMod::DAE.SubMod) ::SourceInfo
              local outInfo::SourceInfo

              local mod::DAE.Mod

              @match DAE.NAMEMOD(mod = mod) = inSubMod
              outInfo = getModInfo(mod)
          outInfo
        end

        function setEqMod(inEqMod::Option{<:DAE.EqMod}, inMod::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod = inMod

              outMod = begin
                @match outMod begin
                  DAE.MOD(__)  => begin
                      Setfield.@set outMod.binding = inEqMod
                    outMod
                  end

                  _  => begin
                      outMod
                  end
                end
              end
          outMod
        end

        function stripSubModBindings(inSubMods::List{<:DAE.SubMod}) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod} = nil

              local id::DAE.Ident
              local mod::DAE.Mod

              for submod in inSubMods
                @match DAE.NAMEMOD(id, mod) = submod
                mod = setEqMod(NONE(), mod)
                if ! isEmptyMod(mod)
                  outSubMods = _cons(DAE.NAMEMOD(id, mod), outSubMods)
                end
              end
              outSubMods = listReverse(outSubMods)
          outSubMods
        end

        function filterRedeclares(inMod::DAE.Mod) ::DAE.Mod
              local outMod::DAE.Mod = inMod

              outMod = begin
                @match outMod begin
                  DAE.MOD(__)  => begin
                      Setfield.@set outMod.subModLst = filterRedeclaresSubMods(outMod.subModLst)
                      Setfield.@set outMod.binding = NONE()
                    if listEmpty(outMod.subModLst)
                          DAE.NOMOD()
                        else
                          outMod
                        end
                  end

                  _  => begin
                      outMod
                  end
                end
              end
          outMod
        end

        function filterRedeclaresSubMods(inSubMods::List{<:DAE.SubMod}) ::List{DAE.SubMod}
              local outSubMods::List{DAE.SubMod} = nil

              local id::DAE.Ident
              local mod::DAE.Mod

              for submod in inSubMods
                @match DAE.NAMEMOD(id, mod) = submod
                mod = filterRedeclares(mod)
                if isRedeclareMod(mod)
                  outSubMods = _cons(DAE.NAMEMOD(id, mod), outSubMods)
                end
              end
              outSubMods = listReverse(outSubMods)
          outSubMods
        end

        function unparseModStr(inMod::DAE.Mod) ::String
              local outString::String

              outString = begin
                  local final_str::String
                  local each_str::String
                  local sub_str::String
                  local binding_str::String
                  local el_str::String
                @match inMod begin
                  DAE.NOMOD(__)  => begin
                    ""
                  end

                  DAE.MOD(__)  => begin
                      final_str = if SCodeUtil.finalBool(inMod.finalPrefix)
                            "final "
                          else
                            ""
                          end
                      each_str = if SCodeUtil.eachBool(inMod.eachPrefix)
                            "each "
                          else
                            ""
                          end
                      sub_str = ListUtil.toString(inMod.subModLst, unparseSubModStr, "", "(", ", ", ")", false)
                      binding_str = unparseBindingStr(inMod.binding)
                    final_str + each_str + sub_str + binding_str
                  end

                  DAE.REDECL(__)  => begin
                      final_str = if SCodeUtil.finalBool(inMod.finalPrefix)
                            "final "
                          else
                            ""
                          end
                      each_str = if SCodeUtil.eachBool(inMod.eachPrefix)
                            "each "
                          else
                            ""
                          end
                      el_str = SCodeDump.unparseElementStr(inMod.element)
                    final_str + each_str + "redeclare " + el_str
                  end
                end
              end
          outString
        end

        function unparseSubModStr(inSubMod::DAE.SubMod) ::String
              local outString::String

              outString = begin
                @match inSubMod begin
                  DAE.NAMEMOD(__)  => begin
                    inSubMod.ident + " = " + unparseModStr(inSubMod.mod)
                  end
                end
              end
          outString
        end

        function unparseBindingStr(inBinding::Option{<:DAE.EqMod}) ::String
              local outString::String

              outString = begin
                  local exp::Absyn.Exp
                @match inBinding begin
                  NONE()  => begin
                    ""
                  end

                  SOME(DAE.TYPED(modifierAsAbsynExp = exp))  => begin
                    " = " + Dump.printExpStr(exp)
                  end

                  SOME(DAE.UNTYPED(exp = exp))  => begin
                    " = " + Dump.printExpStr(exp)
                  end
                end
              end
          outString
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

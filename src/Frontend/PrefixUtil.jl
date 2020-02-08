  module PrefixUtil


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

    using Setfield
    
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

        import FCoreUtil

        import LookupUtil

        import SCode

        import Prefix

        import InnerOuterTypes

        import ClassInf

        InstanceHierarchy = InnerOuterTypes.InstHierarchy  #= an instance hierarchy =#
        import CrefForHashTable
        import Config
        import Debug
        import Error
        import Expression
        import ExpressionDump
        import Flags
        import File
        import ListUtil
        import Print
         #= import Util;
         =#
        import System
        import Types
        import MetaModelica.Dangerous

         #= Prints a Prefix to a string. Rather slow... =#
        function printComponentPrefixStr(pre::Prefix.ComponentPrefix) ::String
              local outString::String

              outString = begin
                  local str::String
                  local s::String
                  local rest_1::String
                  local s_1::String
                  local s_2::String
                  local rest::Prefix.ComponentPrefix
                  local cp::Prefix.ClassPrefix
                  local ss::List{DAE.Subscript}
                @match pre begin
                  Prefix.NOCOMPPRE(__)  => begin
                    "<Prefix.NOCOMPPRE()>"
                  end

                  Prefix.PRE(next = Prefix.NOCOMPPRE(__), subscripts =  nil())  => begin
                    pre.prefix
                  end

                  Prefix.PRE(next = Prefix.NOCOMPPRE(__))  => begin
                    pre.prefix + "[" + ExpressionDump.printSubscriptLstStr(pre.subscripts) + "]"
                  end

                  Prefix.PRE(subscripts =  nil())  => begin
                    printComponentPrefixStr(pre.next) + "." + pre.prefix
                  end

                  Prefix.PRE(__)  => begin
                    printComponentPrefixStr(pre.next) + "." + pre.prefix + "[" + ExpressionDump.printSubscriptLstStr(pre.subscripts) + "]"
                  end
                end
              end
          outString
        end

         #= Prints a Prefix to a string. =#
        function printPrefixStr(inPrefix::Prefix.PrefixType) ::String
              local outString::String

              outString = begin
                  local str::String
                  local s::String
                  local rest_1::String
                  local s_1::String
                  local s_2::String
                  local rest::Prefix.ComponentPrefix
                  local cp::Prefix.ClassPrefix
                  local ss::List{DAE.Subscript}
                @matchcontinue inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    "<Prefix.NOPRE()>"
                  end

                  Prefix.PREFIX(Prefix.NOCOMPPRE(__), _)  => begin
                    "<Prefix.PREFIX(Prefix.NOCOMPPRE())>"
                  end

                  Prefix.PREFIX(Prefix.PRE(str, _,  nil(), Prefix.NOCOMPPRE(__), _, _), _)  => begin
                    str
                  end

                  Prefix.PREFIX(Prefix.PRE(str, _, ss, Prefix.NOCOMPPRE(__), _, _), _)  => begin
                      s = stringAppend(str, "[" + stringDelimitList(ListUtil.map(ss, ExpressionDump.subscriptString), ", ") + "]")
                    s
                  end

                  Prefix.PREFIX(Prefix.PRE(str, _,  nil(), rest, _, _), cp)  => begin
                      rest_1 = printPrefixStr(Prefix.PREFIX(rest, cp))
                      s = stringAppend(rest_1, ".")
                      s_1 = stringAppend(s, str)
                    s_1
                  end

                  Prefix.PREFIX(Prefix.PRE(str, _, ss, rest, _, _), cp)  => begin
                      rest_1 = printPrefixStr(Prefix.PREFIX(rest, cp))
                      s = stringAppend(rest_1, ".")
                      s_1 = stringAppend(s, str)
                      s_2 = stringAppend(s_1, "[" + stringDelimitList(ListUtil.map(ss, ExpressionDump.subscriptString), ", ") + "]")
                    s_2
                  end
                end
              end
          outString
        end

         #= Prints a Prefix to a string. Designed to be used in Error messages to produce qualified component names =#
        function printPrefixStr2(inPrefix::Prefix.PrefixType) ::String
              local outString::String

              outString = begin
                  local p::Prefix.PrefixType
                @match inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    ""
                  end

                  Prefix.PREFIX(Prefix.NOCOMPPRE(__), _)  => begin
                    ""
                  end

                  p  => begin
                    printPrefixStr(p) + "."
                  end
                end
              end
          outString
        end

         #= Prints a Prefix to a string as a component name. Designed to be used in Error messages =#
        function printPrefixStr3(inPrefix::Prefix.PrefixType) ::String
              local outString::String

              outString = begin
                  local p::Prefix.PrefixType
                @match inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    "<NO COMPONENT>"
                  end

                  Prefix.PREFIX(Prefix.NOCOMPPRE(__), _)  => begin
                    "<NO COMPONENT>"
                  end

                  p  => begin
                    printPrefixStr(p)
                  end
                end
              end
          outString
        end

         #= Prints a Prefix to a string as a component name. Designed to be used in Error messages =#
        function printPrefixStrIgnoreNoPre(inPrefix::Prefix.PrefixType) ::String
              local outString::String

              outString = begin
                  local p::Prefix.PrefixType
                @match inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    ""
                  end

                  Prefix.PREFIX(Prefix.NOCOMPPRE(__), _)  => begin
                    ""
                  end

                  p  => begin
                    printPrefixStr(p)
                  end
                end
              end
          outString
        end

         #= Prints a prefix to the Print buffer. =#
        function printPrefix(p::Prefix.PrefixType)
              local s::String

              s = printPrefixStr(p)
              Print.printBuf(s)
        end

         #= This function is used to extend a prefix with another level.  If
          the prefix `a.b{10}.c\\' is extended with `d\\' and an empty subscript
          list, the resulting prefix is `a.b{10}.c.d\\'.  Remember that
          prefixes components are stored in the opposite order from the
          normal order used when displaying them. =#
        function prefixAdd(inIdent::String, inType::List{<:DAE.Dimension}, inIntegerLst::List{<:DAE.Subscript}, inPrefix::Prefix.PrefixType, vt::SCode.Variability, ci_state::ClassInf.SMNode, inInfo::SourceInfo) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              outPrefix = begin
                  local i::String
                  local s::List{DAE.Subscript}
                  local p::Prefix.ComponentPrefix
                @match (inIdent, inType, inIntegerLst, inPrefix, vt, ci_state) begin
                  (i, _, s, Prefix.PREFIX(p, _), _, _)  => begin
                    Prefix.PREFIX(Prefix.PRE(i, inType, s, p, ci_state, inInfo), Prefix.CLASSPRE(vt))
                  end

                  (i, _, s, Prefix.NOPRE(__), _, _)  => begin
                    Prefix.PREFIX(Prefix.PRE(i, inType, s, Prefix.NOCOMPPRE(), ci_state, inInfo), Prefix.CLASSPRE(vt))
                  end
                end
              end
          outPrefix
        end

        function prefixFirst(inPrefix::Prefix.PrefixType) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              outPrefix = begin
                  local a::String
                  local b::List{DAE.Subscript}
                  local cp::Prefix.ClassPrefix
                  local c::Prefix.ComponentPrefix
                  local ci_state::ClassInf.SMNode
                  local pdims::List{DAE.Dimension}
                  local info::SourceInfo
                @match inPrefix begin
                  Prefix.PREFIX(Prefix.PRE(prefix = a, dimensions = pdims, subscripts = b, ci_state = ci_state, info = info), cp)  => begin
                    Prefix.PREFIX(Prefix.PRE(a, pdims, b, Prefix.NOCOMPPRE(), ci_state, info), cp)
                  end
                end
              end
          outPrefix
        end

         #= Returns the first cref in the prefix. =#
        function prefixFirstCref(inPrefix::Prefix.PrefixType) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              local name::String
              local subs::List{DAE.Subscript}

              @match Prefix.PREFIX(compPre = Prefix.PRE(prefix = name, subscripts = subs)) = inPrefix
              outCref = DAE.CREF_IDENT(name, DAE.T_UNKNOWN_DEFAULT, subs)
          outCref
        end

         #= Returns the last NONPRE Prefix of a prefix =#
        function prefixLast(inPrefix::Prefix.PrefixType) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              outPrefix = begin
                  local p::Prefix.ComponentPrefix
                  local res::Prefix.PrefixType
                  local cp::Prefix.ClassPrefix
                @matchcontinue inPrefix begin
                  res && Prefix.PREFIX(Prefix.PRE(next = Prefix.NOCOMPPRE(__)), _)  => begin
                    res
                  end

                  Prefix.PREFIX(Prefix.PRE(next = p), cp)  => begin
                      res = prefixLast(Prefix.PREFIX(p, cp))
                    res
                  end
                end
              end
          outPrefix
        end

         #= @author: adrpo
         remove the last prefix from the component prefix =#
        function prefixStripLast(inPrefix::Prefix.PrefixType) ::Prefix.PrefixType
              local outPrefix::Prefix.PrefixType

              outPrefix = begin
                  local cp::Prefix.ClassPrefix
                  local compPre::Prefix.ComponentPrefix
                   #=  we can't remove what it isn't there!
                   =#
                @match inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    Prefix.NOPRE()
                  end

                  Prefix.PREFIX(compPre, cp)  => begin
                      compPre = compPreStripLast(compPre)
                    Prefix.PREFIX(compPre, cp)
                  end
                end
              end
               #=  if there isn't any next prefix, return Prefix.NOPRE!
               =#
          outPrefix
        end

         #= @author: adrpo
         remove the last prefix from the component prefix =#
        function compPreStripLast(inCompPrefix::Prefix.ComponentPrefix) ::Prefix.ComponentPrefix
              local outCompPrefix::Prefix.ComponentPrefix

              outCompPrefix = begin
                  local next::Prefix.ComponentPrefix
                   #=  nothing to remove!
                   =#
                @match inCompPrefix begin
                  Prefix.NOCOMPPRE(__)  => begin
                    Prefix.NOCOMPPRE()
                  end

                  Prefix.PRE(next = next)  => begin
                    next
                  end
                end
              end
               #=  we have something
               =#
          outCompPrefix
        end

         #= Prefix a Path variable by adding the supplied
          prefix to it and returning a new Path. =#
        function prefixPath(inPath::Absyn.Path, inPrefix::Prefix.PrefixType) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local p::Absyn.Path
                  local p_1::Absyn.Path
                  local s::String
                  local ss::Prefix.ComponentPrefix
                  local cp::Prefix.ClassPrefix
                @match (inPath, inPrefix) begin
                  (p, Prefix.NOPRE(__))  => begin
                    p
                  end

                  (p, Prefix.PREFIX(Prefix.PRE(prefix = s, next = Prefix.NOCOMPPRE(__)), _))  => begin
                      p_1 = Absyn.QUALIFIED(s, p)
                    p_1
                  end

                  (p, Prefix.PREFIX(Prefix.PRE(prefix = s, next = ss), cp))  => begin
                      p_1 = prefixPath(Absyn.QUALIFIED(s, p), Prefix.PREFIX(ss, cp))
                    p_1
                  end
                end
              end
          outPath
        end

         #= Convert a Prefix to a Path =#
        function prefixToPath(inPrefix::Prefix.PrefixType) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local ss::Prefix.ComponentPrefix
                @match inPrefix begin
                  Prefix.PREFIX(ss, _)  => begin
                    componentPrefixToPath(ss)
                  end
                end
              end
          outPath
        end

         #= Convert a Ident/Prefix to a String =#
        function identAndPrefixToPath(ident::String, inPrefix::Prefix.PrefixType) ::String
              local str::String

              str = AbsynUtil.pathString(PrefixUtil.prefixPath(Absyn.IDENT(ident), inPrefix))
          str
        end

         #= Convert a Prefix to a Path =#
        function componentPrefixToPath(pre::Prefix.ComponentPrefix) ::Absyn.Path
              local path::Absyn.Path

              path = begin
                  local s::String
                  local ss::Prefix.ComponentPrefix
                @match pre begin
                  Prefix.PRE(prefix = s, next = Prefix.NOCOMPPRE(__))  => begin
                    Absyn.IDENT(s)
                  end

                  Prefix.PRE(prefix = s, next = ss)  => begin
                    Absyn.QUALIFIED(s, componentPrefixToPath(ss))
                  end
                end
              end
          path
        end

         #= Prefix a ComponentRef variable by adding the supplied prefix to
          it and returning a new ComponentRef.
          LS: Changed to call prefixToCref which is more general now =#
        function prefixCref(cache::FCore.Cache, env::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, pre::Prefix.PrefixType, cref::DAE.ComponentRef) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local cref_1::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, cref_1) = prefixToCref2(cache, env, inIH, pre, SOME(cref))
          (outCache, cref_1)
        end

         #= Prefix a ComponentRef variable by adding the supplied prefix to
          it and returning a new ComponentRef.
          LS: Changed to call prefixToCref which is more general now =#
        function prefixCrefNoContext(inPre::Prefix.PrefixType, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              (_, outCref) = prefixToCref2(FCoreUtil.noCache(), FCore.emptyGraph, InnerOuterTypes.emptyInstHierarchy, inPre, SOME(inCref))
          outCref
        end

         #= Convert a prefix to a component reference. =#
        function prefixToCref(pre::Prefix.PrefixType) ::DAE.ComponentRef
              local cref_1::DAE.ComponentRef

              (_, cref_1) = prefixToCref2(FCoreUtil.noCache(), FCore.emptyGraph, InnerOuterTypes.emptyInstHierarchy, pre, NONE())
          cref_1
        end

         #= Convert a prefix to a component reference. Converting Prefix.NOPRE with no
          component reference is an error because a component reference cannot be
          empty =#
        function prefixToCref2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, inPrefix::Prefix.PrefixType, inExpComponentRefOption::Option{<:DAE.ComponentRef}) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outComponentRef::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outComponentRef) = begin
                  local cref::DAE.ComponentRef
                  local cref_1::DAE.ComponentRef
                  local cref_2::DAE.ComponentRef
                  local cref_::DAE.ComponentRef
                  local i::String
                  local s::List{DAE.Subscript}
                  local ds::List{DAE.Dimension}
                  local ident_ty::DAE.Type
                  local xs::Prefix.ComponentPrefix
                  local cp::Prefix.ClassPrefix
                  local ci_state::ClassInf.SMNode
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inCache, inEnv, inIH, inPrefix, inExpComponentRefOption) begin
                  (_, _, _, Prefix.NOPRE(__), NONE())  => begin
                    fail()
                  end

                  (_, _, _, Prefix.PREFIX(Prefix.NOCOMPPRE(__), _), NONE())  => begin
                    fail()
                  end

                  (cache, _, _, Prefix.NOPRE(__), SOME(cref))  => begin
                    (cache, cref)
                  end

                  (cache, _, _, Prefix.PREFIX(Prefix.NOCOMPPRE(__), _), SOME(cref))  => begin
                    (cache, cref)
                  end

                  (cache, env, _, Prefix.PREFIX(Prefix.PRE(prefix = i, dimensions = ds, subscripts = s, next = xs, ci_state = ci_state), cp), NONE())  => begin
                      ident_ty = Expression.liftArrayLeftList(DAE.T_COMPLEX(ci_state, nil, NONE()), ds)
                      cref_ = CrefForHashTable.makeCrefIdent(i, ident_ty, s)
                      (cache, cref_1) = prefixToCref2(cache, env, inIH, Prefix.PREFIX(xs, cp), SOME(cref_))
                    (cache, cref_1)
                  end

                  (cache, env, _, Prefix.PREFIX(Prefix.PRE(prefix = i, dimensions = ds, subscripts = s, next = xs, ci_state = ci_state), cp), SOME(cref))  => begin
                      (cache, cref) = prefixSubscriptsInCref(cache, env, inIH, inPrefix, cref)
                      ident_ty = Expression.liftArrayLeftList(DAE.T_COMPLEX(ci_state, nil, NONE()), ds)
                      cref_2 = CrefForHashTable.makeCrefQual(i, ident_ty, s, cref)
                      (cache, cref_1) = prefixToCref2(cache, env, inIH, Prefix.PREFIX(xs, cp), SOME(cref_2))
                    (cache, cref_1)
                  end
                end
              end
          (outCache, outComponentRef)
        end

         #= Convert a prefix to an optional component reference. =#
        function prefixToCrefOpt(pre::Prefix.PrefixType) ::Option{DAE.ComponentRef}
              local cref_1::Option{DAE.ComponentRef}

              cref_1 = prefixToCrefOpt2(pre, NONE())
          cref_1
        end

         #= Convert a prefix to a component reference. Converting Prefix.NOPRE with no
          component reference gives a NONE =#
        function prefixToCrefOpt2(inPrefix::Prefix.PrefixType, inExpComponentRefOption::Option{<:DAE.ComponentRef}) ::Option{DAE.ComponentRef}
              local outComponentRefOpt::Option{DAE.ComponentRef}

              outComponentRefOpt = begin
                  local cref_1::Option{DAE.ComponentRef}
                  local cref::DAE.ComponentRef
                  local cref_::DAE.ComponentRef
                  local i::String
                  local s::List{DAE.Subscript}
                  local xs::Prefix.ComponentPrefix
                  local cp::Prefix.ClassPrefix
                @match (inPrefix, inExpComponentRefOption) begin
                  (Prefix.NOPRE(__), NONE())  => begin
                    NONE()
                  end

                  (Prefix.NOPRE(__), SOME(cref))  => begin
                    SOME(cref)
                  end

                  (Prefix.PREFIX(Prefix.NOCOMPPRE(__), _), SOME(cref))  => begin
                    SOME(cref)
                  end

                  (Prefix.PREFIX(Prefix.PRE(prefix = i, subscripts = s, next = xs), cp), NONE())  => begin
                      cref_ = CrefForHashTable.makeCrefIdent(i, DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("")), nil, NONE()), s)
                      cref_1 = prefixToCrefOpt2(Prefix.PREFIX(xs, cp), SOME(cref_))
                    cref_1
                  end

                  (Prefix.PREFIX(Prefix.PRE(prefix = i, subscripts = s, next = xs), cp), SOME(cref))  => begin
                      cref_ = CrefForHashTable.makeCrefQual(i, DAE.T_COMPLEX(ClassInf.UNKNOWN(Absyn.IDENT("")), nil, NONE()), s, cref)
                      cref_1 = prefixToCrefOpt2(Prefix.PREFIX(xs, cp), SOME(cref_))
                    cref_1
                  end
                end
              end
          outComponentRefOpt
        end

         #= @author:adrpo
           Similar to prefixToCref but it doesn't fail for NOPRE or NOCOMPPRE,
           it will just create an empty cref in these cases =#
        function makeCrefFromPrefixNoFail(pre::Prefix.PrefixType) ::DAE.ComponentRef
              local cref::DAE.ComponentRef

              cref = begin
                  local c::DAE.ComponentRef
                @matchcontinue pre begin
                  Prefix.NOPRE(__)  => begin
                      c = CrefForHashTable.makeCrefIdent("", DAE.T_UNKNOWN_DEFAULT, nil)
                    c
                  end

                  Prefix.PREFIX(Prefix.NOCOMPPRE(__), _)  => begin
                      c = CrefForHashTable.makeCrefIdent("", DAE.T_UNKNOWN_DEFAULT, nil)
                    c
                  end

                  _  => begin
                      c = prefixToCref(pre)
                    c
                  end
                end
              end
          cref
        end

         #= help function to prefixToCrefOpt2, deals with prefixing expressions in subscripts =#
        function prefixSubscriptsInCref(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, pre::Prefix.PrefixType, inCr::DAE.ComponentRef) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outCr::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outCr) = prefixSubscriptsInCrefWork(inCache, inEnv, inIH, pre, inCr, nil)
          (outCache, outCr)
        end

         #= help function to prefixToCrefOpt2, deals with prefixing expressions in subscripts =#
        function prefixSubscriptsInCrefWork(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, pre::Prefix.PrefixType, inCr::DAE.ComponentRef, acc::List{<:DAE.ComponentRef}) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outCr::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outCr) = begin
                  local id::DAE.Ident
                  local tp::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local cr::DAE.ComponentRef
                  local crid::DAE.ComponentRef
                @match (inCache, inEnv, inIH, pre, inCr, acc) begin
                  (cache, env, _, _, DAE.CREF_IDENT(id, tp, subs), _)  => begin
                      (cache, subs) = prefixSubscripts(cache, env, inIH, pre, subs)
                      cr = CrefForHashTable.makeCrefIdent(id, tp, subs)
                    (cache, CrefForHashTable.implode_reverse(_cons(cr, acc)))
                  end

                  (cache, env, _, _, DAE.CREF_QUAL(id, tp, subs, cr), _)  => begin
                      (cache, subs) = prefixSubscripts(cache, env, inIH, pre, subs)
                      crid = CrefForHashTable.makeCrefIdent(id, tp, subs)
                      (cache, cr) = prefixSubscriptsInCrefWork(cache, env, inIH, pre, cr, _cons(crid, acc))
                    (cache, cr)
                  end

                  (cache, _, _, _, DAE.WILD(__), _)  => begin
                    (cache, DAE.WILD())
                  end
                end
              end
          (outCache, outCr)
        end

         #= help function to prefixSubscriptsInCref, adds prefix to subscripts =#
        function prefixSubscripts(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, pre::Prefix.PrefixType, inSubs::List{<:DAE.Subscript}) ::Tuple{FCore.Cache, List{DAE.Subscript}}
              local outSubs::List{DAE.Subscript}
              local outCache::FCore.Cache

              (outCache, outSubs) = begin
                  local sub::DAE.Subscript
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local subs::List{DAE.Subscript}
                @match (inCache, inEnv, inIH, pre, inSubs) begin
                  (cache, _, _, _,  nil())  => begin
                    (cache, nil)
                  end

                  (cache, env, _, _, sub <| subs)  => begin
                      (cache, sub) = prefixSubscript(cache, env, inIH, pre, sub)
                      (cache, subs) = prefixSubscripts(cache, env, inIH, pre, subs)
                    (cache, _cons(sub, subs))
                  end
                end
              end
          (outCache, outSubs)
        end

         #= help function to prefixSubscripts, adds prefix to one subscript, if it is an expression =#
        function prefixSubscript(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, pre::Prefix.PrefixType, sub::DAE.Subscript) ::Tuple{FCore.Cache, DAE.Subscript}
              local outSub::DAE.Subscript
              local outCache::FCore.Cache

              (outCache, outSub) = begin
                  local exp::DAE.Exp
                  local cache::FCore.Cache
                  local env::FCore.Graph
                @match (inCache, inEnv, inIH, pre, sub) begin
                  (cache, _, _, _, DAE.WHOLEDIM(__))  => begin
                    (cache, DAE.WHOLEDIM())
                  end

                  (cache, env, _, _, DAE.SLICE(exp))  => begin
                      (cache, exp) = prefixExpWork(cache, env, inIH, exp, pre)
                    (cache, DAE.SLICE(exp))
                  end

                  (cache, env, _, _, DAE.WHOLE_NONEXP(exp))  => begin
                      (cache, exp) = prefixExpWork(cache, env, inIH, exp, pre)
                    (cache, DAE.WHOLE_NONEXP(exp))
                  end

                  (cache, env, _, _, DAE.INDEX(exp))  => begin
                      (cache, exp) = prefixExpWork(cache, env, inIH, exp, pre)
                    (cache, DAE.INDEX(exp))
                  end
                end
              end
          (outCache, outSub)
        end

         #= Search for the prefix of the inner when the cref is
          an outer and add that instead of the given prefix!
          If the cref is an inner, prefix it normally. =#
        function prefixCrefInnerOuter(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inCref::DAE.ComponentRef, inPrefix::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.ComponentRef}
              local outCref::DAE.ComponentRef
              local outCache::FCore.Cache

              (outCache, outCref) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local io::Absyn.InnerOuter
                  local ih::InstanceHierarchy
                  local innerPrefix::Prefix.PrefixType
                  local pre::Prefix.PrefixType
                  local lastCref::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                  local newCref::DAE.ComponentRef
                  local n::String
                @match (inCache, inEnv, inIH, inCref, inPrefix) begin
                  (cache, _, ih, cref, pre)  => begin
                      newCref = prefixOuterCrefWithTheInnerPrefix(ih, cref, pre)
                    (cache, newCref)
                  end
                end
              end
          (outCache, outCref)
        end

         #= Add the supplied prefix to all component references in an expression. =#
        function prefixExp(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuterTypes.InstHierarchy, exp::DAE.Exp, pre::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.Exp}



              try
                (cache, exp) = prefixExpWork(cache, env, ih, exp, pre)
              catch
                Error.addInternalError(getInstanceName() + " failed on exp: " + ExpressionDump.printExpStr(exp) + " " + makePrefixString(pre), sourceInfo())
                fail()
              end
          (cache, exp)
        end

         #= Add the supplied prefix to all component references in an expression. =#
        function prefixExpWork(cache::FCore.Cache, env::FCore.Graph, ih::InnerOuterTypes.InstHierarchy, inExp::DAE.Exp, pre::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.Exp}
              local outExp::DAE.Exp


              (cache, outExp) = begin
                  local e::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local cref_1::DAE.Exp
                  local dim_1::DAE.Exp
                  local cref::DAE.Exp
                  local dim::DAE.Exp
                  local start_1::DAE.Exp
                  local stop_1::DAE.Exp
                  local start::DAE.Exp
                  local stop::DAE.Exp
                  local step_1::DAE.Exp
                  local step::DAE.Exp
                  local e_1::DAE.Exp
                  local exp_1::DAE.Exp
                  local exp::DAE.Exp
                  local crefExp::DAE.Exp
                  local cr::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local o::DAE.Operator
                  local es_1::List{DAE.Exp}
                  local es::List{DAE.Exp}
                  local f::Absyn.Path
                  local sc::Bool
                  local x_1::List{DAE.Exp}
                  local x::List{DAE.Exp}
                  local xs_1::List{List{DAE.Exp}}
                  local xs::List{List{DAE.Exp}}
                  local s::String
                  local expl::List{DAE.Exp}
                  local p::Prefix.PrefixType
                  local b::ModelicaInteger
                  local a::ModelicaInteger
                  local t::DAE.Type
                  local tp::DAE.Type
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local reductionInfo::DAE.ReductionInfo
                  local riters::DAE.ReductionIterators
                  local attr::DAE.CallAttributes
                  local fieldNames::List{String}
                  local clk::DAE.ClockKind
                   #=  no prefix, return the input expression
                   =#
                @match (inExp, pre) begin
                  (e, Prefix.NOPRE(__)) where (! System.getHasInnerOuterDefinitions())  => begin
                    (cache, e)
                  end

                  (e && DAE.ICONST(__), _)  => begin
                    (cache, e)
                  end

                  (e && DAE.RCONST(__), _)  => begin
                    (cache, e)
                  end

                  (e && DAE.SCONST(__), _)  => begin
                    (cache, e)
                  end

                  (e && DAE.BCONST(__), _)  => begin
                    (cache, e)
                  end

                  (e && DAE.ENUM_LITERAL(__), _)  => begin
                    (cache, e)
                  end

                  (DAE.CREF(componentRef = cr, ty = t), _)  => begin
                       #=  handle literal constants
                       =#
                       #=  adrpo: handle prefixing of inner/outer variables
                       =#
                      if System.getHasInnerOuterDefinitions() && ! listEmpty(ih)
                        try
                          cr_1 = prefixOuterCrefWithTheInnerPrefix(ih, cr, pre)
                          (cache, t) = prefixExpressionsInType(cache, env, ih, pre, t)
                          outExp = Expression.makeCrefExp(cr_1, t)
                          return (cache, outExp)
                        catch
                        end
                      end
                      if valueEq(Prefix.NOPRE(), pre)
                        crefExp = inExp
                      else
                        (cache, crefExp) = prefixExpCref(cache, env, ih, inExp, pre)
                      end
                    (cache, crefExp)
                  end

                  (DAE.CLKCONST(clk), _)  => begin
                      (cache, clk) = prefixClockKind(cache, env, ih, clk, pre)
                    (cache, DAE.CLKCONST(clk))
                  end

                  (DAE.ASUB(exp = e1, sub = expl), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, expl, pre)
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                      e2 = Expression.makeASUB(e1, es_1)
                    (cache, e2)
                  end

                  (DAE.TSUB(e1, index_, t), _)  => begin
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                      e2 = DAE.TSUB(e1, index_, t)
                    (cache, e2)
                  end

                  (DAE.BINARY(exp1 = e1, operator = o, exp2 = e2), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                      (cache, e2_1) = prefixExpWork(cache, env, ih, e2, pre)
                    (cache, DAE.BINARY(e1_1, o, e2_1))
                  end

                  (DAE.UNARY(operator = o, exp = e1), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                    (cache, DAE.UNARY(o, e1_1))
                  end

                  (DAE.LBINARY(exp1 = e1, operator = o, exp2 = e2), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                      (cache, e2_1) = prefixExpWork(cache, env, ih, e2, pre)
                    (cache, DAE.LBINARY(e1_1, o, e2_1))
                  end

                  (DAE.LUNARY(operator = o, exp = e1), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                    (cache, DAE.LUNARY(o, e1_1))
                  end

                  (DAE.RELATION(exp1 = e1, operator = o, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                      (cache, e2_1) = prefixExpWork(cache, env, ih, e2, pre)
                    (cache, DAE.RELATION(e1_1, o, e2_1, index_, isExpisASUB))
                  end

                  (DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), _)  => begin
                      (cache, e1_1) = prefixExpWork(cache, env, ih, e1, pre)
                      (cache, e2_1) = prefixExpWork(cache, env, ih, e2, pre)
                      (cache, e3_1) = prefixExpWork(cache, env, ih, e3, pre)
                    (cache, DAE.IFEXP(e1_1, e2_1, e3_1))
                  end

                  (DAE.SIZE(exp = cref, sz = SOME(dim)), _)  => begin
                      (cache, cref_1) = prefixExpWork(cache, env, ih, cref, pre)
                      (cache, dim_1) = prefixExpWork(cache, env, ih, dim, pre)
                    (cache, DAE.SIZE(cref_1, SOME(dim_1)))
                  end

                  (DAE.SIZE(exp = cref, sz = NONE()), _)  => begin
                      (cache, cref_1) = prefixExpWork(cache, env, ih, cref, pre)
                    (cache, DAE.SIZE(cref_1, NONE()))
                  end

                  (DAE.CALL(f, es, attr), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.CALL(f, es_1, attr))
                  end

                  (e && DAE.PARTEVALFUNCTION(__), _)  => begin
                       #=  clocks
                       =#
                      (cache, es_1) = prefixExpList(cache, env, ih, e.expList, pre)
                      @set e.expList = es_1
                    (cache, e)
                  end

                  (DAE.RECORD(f, es, fieldNames, t), _)  => begin
                      (cache, _) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.RECORD(f, es, fieldNames, t))
                  end

                  (DAE.ARRAY(ty = t, scalar = sc, array =  nil()), _)  => begin
                    (cache, inExp)
                  end

                  (DAE.ARRAY(ty = t, scalar = sc, array = es), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.ARRAY(t, sc, es_1))
                  end

                  (DAE.TUPLE(PR = es), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.TUPLE(es_1))
                  end

                  (DAE.MATRIX(ty = t, integer = a, matrix =  nil()), _)  => begin
                    (cache, inExp)
                  end

                  (DAE.MATRIX(ty = t, integer = a, matrix = x <| xs), _)  => begin
                      (cache, x_1) = prefixExpList(cache, env, ih, x, pre)
                      @match (cache, DAE.MATRIX(t, _, xs_1)) = prefixExpWork(cache, env, ih, DAE.MATRIX(t, a, xs), pre)
                    (cache, DAE.MATRIX(t, a, _cons(x_1, xs_1)))
                  end

                  (DAE.RANGE(ty = t, start = start, step = NONE(), stop = stop), _)  => begin
                      (cache, start_1) = prefixExpWork(cache, env, ih, start, pre)
                      (cache, stop_1) = prefixExpWork(cache, env, ih, stop, pre)
                    (cache, DAE.RANGE(t, start_1, NONE(), stop_1))
                  end

                  (DAE.RANGE(ty = t, start = start, step = SOME(step), stop = stop), _)  => begin
                      (cache, start_1) = prefixExpWork(cache, env, ih, start, pre)
                      (cache, step_1) = prefixExpWork(cache, env, ih, step, pre)
                      (cache, stop_1) = prefixExpWork(cache, env, ih, stop, pre)
                    (cache, DAE.RANGE(t, start_1, SOME(step_1), stop_1))
                  end

                  (DAE.CAST(ty = tp, exp = e), _)  => begin
                      (cache, e_1) = prefixExpWork(cache, env, ih, e, pre)
                    (cache, DAE.CAST(tp, e_1))
                  end

                  (DAE.REDUCTION(reductionInfo = reductionInfo, expr = exp, iterators = riters), _)  => begin
                      (cache, exp_1) = prefixExpWork(cache, env, ih, exp, pre)
                      (cache, riters) = prefixIterators(cache, env, ih, riters, pre)
                    (cache, DAE.REDUCTION(reductionInfo, exp_1, riters))
                  end

                  (DAE.LIST(es), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.LIST(es_1))
                  end

                  (DAE.CONS(e1, e2), _)  => begin
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                      (cache, e2) = prefixExpWork(cache, env, ih, e2, pre)
                    (cache, DAE.CONS(e1, e2))
                  end

                  (DAE.META_TUPLE(es), _)  => begin
                      (cache, es_1) = prefixExpList(cache, env, ih, es, pre)
                    (cache, DAE.META_TUPLE(es_1))
                  end

                  (DAE.META_OPTION(SOME(e1)), _)  => begin
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                    (cache, DAE.META_OPTION(SOME(e1)))
                  end

                  (DAE.META_OPTION(NONE()), _)  => begin
                    (cache, DAE.META_OPTION(NONE()))
                  end

                  (e && DAE.UNBOX(e1), _)  => begin
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                      @set e.exp = e1
                    (cache, e)
                  end

                  (e && DAE.BOX(e1), _)  => begin
                      (cache, e1) = prefixExpWork(cache, env, ih, e1, pre)
                      @set e.exp = e1
                    (cache, e)
                  end

                  (e, Prefix.NOPRE(__))  => begin
                    (cache, e)
                  end

                  (e && DAE.EMPTY(__), _)  => begin
                    (cache, e)
                  end

                  _  => begin
                         #=  MetaModelica extension. KS
                         =#
                         #=  ------------------------
                         =#
                         #=  no prefix, return the input expression
                         =#
                        Error.addInternalError(getInstanceName() + " failed on exp: " + ExpressionDump.printExpStr(inExp) + " " + makePrefixString(pre), sourceInfo())
                      fail()
                  end
                end
              end
          (cache, outExp)
        end

         #= Helper function to prefixExp for prefixing a cref expression. =#
        function prefixExpCref(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, inCref::DAE.Exp, inPrefix::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.Exp}
              local outCref::DAE.Exp
              local outCache::FCore.Cache

              local is_iter::Option{Bool}
              local cache::FCore.Cache
              local cr::DAE.ComponentRef

              @match DAE.CREF(componentRef = cr) = inCref
              (is_iter, cache) = LookupUtil.isIterator(inCache, inEnv, cr)
              (outCache, outCref) = prefixExpCref2(cache, inEnv, inIH, is_iter, inCref, inPrefix)
          (outCache, outCref)
        end

        function prefixExpCref2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstanceHierarchy, inIsIter::Option{<:Bool}, inCref::DAE.Exp, inPrefix::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.Exp}
              local outCref::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outCref) = begin
                  local cache::FCore.Cache
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local exp::DAE.Exp
                   #=  A cref found in the current scope that's not an iterator.
                   =#
                @match (inCache, inEnv, inIH, inIsIter, inCref, inPrefix) begin
                  (cache, _, _, SOME(false), DAE.CREF(componentRef = cr, ty = ty), _)  => begin
                      (cache, cr) = prefixCref(cache, inEnv, inIH, inPrefix, cr)
                      (cache, ty) = prefixExpressionsInType(cache, inEnv, inIH, inPrefix, ty)
                      exp = Expression.makeCrefExp(cr, ty)
                    (cache, exp)
                  end

                  (_, _, _, SOME(true), _, _)  => begin
                    (inCache, inCref)
                  end

                  (cache, _, _, NONE(), DAE.CREF(componentRef = cr, ty = ty), _)  => begin
                      (cache, cr) = prefixSubscriptsInCref(cache, inEnv, inIH, inPrefix, cr)
                      (cache, ty) = prefixExpressionsInType(cache, inEnv, inIH, inPrefix, ty)
                      exp = Expression.makeCrefExp(cr, ty)
                    (cache, exp)
                  end
                end
              end
               #=  An iterator, shouldn't be prefixed.
               =#
               #=  A cref not found in the current scope.
               =#
          (outCache, outCref)
        end

        function prefixIterators(inCache::FCore.Cache, inEnv::FCore.Graph, ih::InstanceHierarchy, inIters::DAE.ReductionIterators, pre::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.ReductionIterators}
              local outIters::DAE.ReductionIterators
              local outCache::FCore.Cache

              (outCache, outIters) = begin
                  local id::String
                  local exp::DAE.Exp
                  local gexp::DAE.Exp
                  local ty::DAE.Type
                  local iter::DAE.ReductionIterator
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local iters::DAE.ReductionIterators
                @match (inCache, inEnv, ih, inIters, pre) begin
                  (cache, _, _,  nil(), _)  => begin
                    (cache, nil)
                  end

                  (cache, env, _, DAE.REDUCTIONITER(id, exp, SOME(gexp), ty) <| iters, _)  => begin
                      (cache, exp) = prefixExpWork(cache, env, ih, exp, pre)
                      (cache, gexp) = prefixExpWork(cache, env, ih, gexp, pre)
                      iter = DAE.REDUCTIONITER(id, exp, SOME(gexp), ty)
                      (cache, iters) = prefixIterators(cache, env, ih, iters, pre)
                    (cache, _cons(iter, iters))
                  end

                  (cache, env, _, DAE.REDUCTIONITER(id, exp, NONE(), ty) <| iters, _)  => begin
                      (cache, exp) = prefixExpWork(cache, env, ih, exp, pre)
                      iter = DAE.REDUCTIONITER(id, exp, NONE(), ty)
                      (cache, iters) = prefixIterators(cache, env, ih, iters, pre)
                    (cache, _cons(iter, iters))
                  end
                end
              end
          (outCache, outIters)
        end

         #= This function prefixes a list of expressions using the prefixExp function. =#
        function prefixExpList(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inExpExpLst::List{<:DAE.Exp}, inPrefix::Prefix.PrefixType) ::Tuple{FCore.Cache, List{DAE.Exp}}
              local outExpExpLst::List{DAE.Exp} = nil
              local outCache::FCore.Cache = inCache

              local e_1::DAE.Exp

              for e in inExpExpLst
                (outCache, e_1) = prefixExpWork(outCache, inEnv, inIH, e, inPrefix)
                outExpExpLst = _cons(e_1, outExpExpLst)
              end
              outExpExpLst = Dangerous.listReverseInPlace(outExpExpLst)
          (outCache, outExpExpLst)
        end

         #= --------------------------------------------
         =#
         #=    PART OF THE WORKAROUND FOR VALUEBLOCKS. KS
         =#

         #= Prefix statements.
          PART OF THE WORKAROUND FOR VALUEBLOCKS =#
        function prefixStatements(cache::FCore.Cache, env::FCore.Graph, inIH::InstanceHierarchy, stmts::List{<:DAE.Statement}, p::Prefix.PrefixType) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStmts::List{DAE.Statement} = nil
              local outCache::FCore.Cache = cache

              for st in stmts
                _ = begin
                    local t::DAE.Type
                    local e::DAE.Exp
                    local e1::DAE.Exp
                    local e2::DAE.Exp
                    local e3::DAE.Exp
                    local source::DAE.ElementSource
                    local elem::DAE.Statement
                    local localAccList::List{DAE.Statement}
                    local rest::List{DAE.Statement}
                    local pre::Prefix.PrefixType
                    local ih::InstanceHierarchy
                    local elems::List{DAE.Statement}
                    local sList::List{DAE.Statement}
                    local b::List{DAE.Statement}
                    local s::String
                    local id::String
                    local eLst::List{DAE.Exp}
                    local cRef::DAE.ComponentRef
                    local bool::Bool
                    local elseBranch::DAE.Else
                    local ix::ModelicaInteger
                  @match st begin
                    DAE.STMT_ASSIGN(t, e1, e, source)  => begin
                        (outCache, e1) = prefixExpWork(outCache, env, inIH, e1, p)
                        (outCache, e) = prefixExpWork(outCache, env, inIH, e, p)
                        elem = DAE.STMT_ASSIGN(t, e1, e, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_TUPLE_ASSIGN(t, eLst, e, source)  => begin
                        (outCache, e) = prefixExpWork(outCache, env, inIH, e, p)
                        (outCache, eLst) = prefixExpList(outCache, env, inIH, eLst, p)
                        elem = DAE.STMT_TUPLE_ASSIGN(t, eLst, e, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_ASSIGN_ARR(t, e1, e, source)  => begin
                        (outCache, e1) = prefixExpWork(outCache, env, inIH, e1, p)
                        (outCache, e) = prefixExpWork(outCache, env, inIH, e, p)
                        elem = DAE.STMT_ASSIGN_ARR(t, e1, e, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_FOR(t, bool, id, ix, e, sList, source)  => begin
                        (outCache, e) = prefixExpWork(outCache, env, inIH, e, p)
                        (outCache, sList) = prefixStatements(outCache, env, inIH, sList, p)
                        elem = DAE.STMT_FOR(t, bool, id, ix, e, sList, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_IF(e1, sList, elseBranch, source)  => begin
                        (outCache, e1) = prefixExpWork(outCache, env, inIH, e1, p)
                        (outCache, sList) = prefixStatements(outCache, env, inIH, sList, p)
                        (outCache, elseBranch) = prefixElse(outCache, env, inIH, elseBranch, p)
                        elem = DAE.STMT_IF(e1, sList, elseBranch, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_WHILE(e1, sList, source)  => begin
                        (outCache, e1) = prefixExpWork(outCache, env, inIH, e1, p)
                        (outCache, sList) = prefixStatements(outCache, env, inIH, sList, p)
                        elem = DAE.STMT_WHILE(e1, sList, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_ASSERT(e1, e2, e3, source)  => begin
                        (outCache, e1) = prefixExpWork(outCache, env, inIH, e1, p)
                        (outCache, e2) = prefixExpWork(outCache, env, inIH, e2, p)
                        (outCache, e3) = prefixExpWork(outCache, env, inIH, e3, p)
                        elem = DAE.STMT_ASSERT(e1, e2, e3, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_FAILURE(b, source)  => begin
                        (outCache, b) = prefixStatements(outCache, env, inIH, b, p)
                        elem = DAE.STMT_FAILURE(b, source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_RETURN(source)  => begin
                        elem = DAE.STMT_RETURN(source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end

                    DAE.STMT_BREAK(source)  => begin
                        elem = DAE.STMT_BREAK(source)
                        outStmts = _cons(elem, outStmts)
                      ()
                    end
                  end
                end
              end
              outStmts = Dangerous.listReverseInPlace(outStmts)
          (outCache, outStmts)
        end

         #= Prefix else statements.
          PART OF THE WORKAROUND FOR VALUEBLOCKS =#
        function prefixElse(cache::FCore.Cache, env::FCore.Graph, inIH::InstanceHierarchy, elseBranch::DAE.Else, p::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.Else}
              local outElse::DAE.Else
              local outCache::FCore.Cache

              (outCache, outElse) = begin
                  local localCache::FCore.Cache
                  local localEnv::FCore.Graph
                  local pre::Prefix.PrefixType
                  local ih::InstanceHierarchy
                  local e::DAE.Exp
                  local lStmt::List{DAE.Statement}
                  local el::DAE.Else
                  local stmt::DAE.Else
                @match (cache, env, inIH, elseBranch, p) begin
                  (localCache, _, _, DAE.NOELSE(__), _)  => begin
                    (localCache, DAE.NOELSE())
                  end

                  (localCache, localEnv, ih, DAE.ELSEIF(e, lStmt, el), pre)  => begin
                      (localCache, e) = prefixExpWork(localCache, localEnv, ih, e, pre)
                      (localCache, el) = prefixElse(localCache, localEnv, ih, el, pre)
                      (localCache, lStmt) = prefixStatements(localCache, localEnv, ih, lStmt, pre)
                      stmt = DAE.ELSEIF(e, lStmt, el)
                    (localCache, stmt)
                  end

                  (localCache, localEnv, ih, DAE.ELSE(lStmt), pre)  => begin
                      (localCache, lStmt) = prefixStatements(localCache, localEnv, ih, lStmt, pre)
                      stmt = DAE.ELSE(lStmt)
                    (localCache, stmt)
                  end
                end
              end
          (outCache, outElse)
        end

         #= helper function for Mod.verifySingleMod, pretty output =#
        function makePrefixString(pre::Prefix.PrefixType) ::String
              local str::String

              str = begin
                @matchcontinue pre begin
                  Prefix.NOPRE(__)  => begin
                    "from top scope"
                  end

                  _  => begin
                      str = "from calling scope: " + printPrefixStr(pre)
                    str
                  end
                end
              end
          str
        end

        function prefixExpressionsInType(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPre::Prefix.PrefixType, inTy::DAE.Type) ::Tuple{FCore.Cache, DAE.Type}
              local outTy::DAE.Type
              local outCache::FCore.Cache

              (outCache, outTy) = begin
                @matchcontinue (inCache, inEnv, inIH, inPre, inTy) begin
                  (_, _, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                    (inCache, inTy)
                  end

                  _  => begin
                        (outTy, (outCache, _, _, _)) = Types.traverseType(inTy, (inCache, inEnv, inIH, inPre), prefixArrayDimensions)
                      (outCache, outTy)
                  end
                end
              end
               #=  don't do this for MetaModelica!
               =#
          (outCache, outTy)
        end

         #= @author: adrpo
         this function prefixes all the expressions in types to be found by the back-end or code generation! =#
        function prefixArrayDimensions(ty::DAE.Type, tpl::Tuple{<:FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, Prefix.PrefixType}) ::Tuple{DAE.Type, Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, Prefix.PrefixType}}
              local otpl::Tuple{FCore.Cache, FCore.Graph, InnerOuterTypes.InstHierarchy, Prefix.PrefixType}
              local oty::DAE.Type = ty

              (oty, otpl) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InnerOuterTypes.InstHierarchy
                  local pre::Prefix.PrefixType
                  local dims::DAE.Dimensions
                @match (oty, tpl) begin
                  (DAE.T_ARRAY(__), (cache, env, ih, pre))  => begin
                      (cache, dims) = prefixDimensions(cache, env, ih, pre, oty.dims)
                      @set oty.dims = dims
                    (oty, (cache, env, ih, pre))
                  end

                  _  => begin
                      (oty, tpl)
                  end
                end
              end
          (oty, otpl)
        end

        function prefixDimensions(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inPre::Prefix.PrefixType, inDims::DAE.Dimensions) ::Tuple{FCore.Cache, DAE.Dimensions}
              local outDims::DAE.Dimensions
              local outCache::FCore.Cache

              (outCache, outDims) = begin
                  local e::DAE.Exp
                  local rest::DAE.Dimensions
                  local new::DAE.Dimensions
                  local d::DAE.Dimension
                  local cache::FCore.Cache
                @matchcontinue (inCache, inEnv, inIH, inPre, inDims) begin
                  (_, _, _, _,  nil())  => begin
                    (inCache, nil)
                  end

                  (_, _, _, _, DAE.DIM_EXP(exp = e) <| rest)  => begin
                      (cache, e) = prefixExpWork(inCache, inEnv, inIH, e, inPre)
                      (cache, new) = prefixDimensions(cache, inEnv, inIH, inPre, rest)
                    (cache, _cons(DAE.DIM_EXP(e), new))
                  end

                  (_, _, _, _, d <| rest)  => begin
                      (cache, new) = prefixDimensions(inCache, inEnv, inIH, inPre, rest)
                    (cache, _cons(d, new))
                  end
                end
              end
          (outCache, outDims)
        end

        function isPrefix(prefix::Prefix.PrefixType) ::Bool
              local isPrefix::Bool

              isPrefix = begin
                @match prefix begin
                  Prefix.PREFIX(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isPrefix
        end

        function isNoPrefix(inPrefix::Prefix.PrefixType) ::Bool
              local outIsEmpty::Bool

              outIsEmpty = begin
                @match inPrefix begin
                  Prefix.NOPRE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsEmpty
        end

         #= Add the supplied prefix to the clock kind =#
        function prefixClockKind(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuterTypes.InstHierarchy, inClkKind::DAE.ClockKind, inPrefix::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.ClockKind}
              local outClkKind::DAE.ClockKind
              local outCache::FCore.Cache

              (outCache, outClkKind) = begin
                  local e::DAE.Exp
                  local resolution::DAE.Exp
                  local interval::DAE.Exp
                  local method::DAE.Exp
                  local clkKind::DAE.ClockKind
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InstanceHierarchy
                  local p::Prefix.PrefixType
                   #=  clock kinds
                   =#
                @match (inCache, inEnv, inIH, inClkKind, inPrefix) begin
                  (cache, _, _, DAE.INFERRED_CLOCK(__), _)  => begin
                    (cache, inClkKind)
                  end

                  (cache, env, ih, DAE.INTEGER_CLOCK(e, resolution), p)  => begin
                      (cache, e) = prefixExpWork(cache, env, ih, e, p)
                      (cache, resolution) = prefixExpWork(cache, env, ih, resolution, p)
                      clkKind = DAE.INTEGER_CLOCK(e, resolution)
                    (cache, clkKind)
                  end

                  (cache, env, ih, DAE.REAL_CLOCK(e), p)  => begin
                      (cache, e) = prefixExpWork(cache, env, ih, e, p)
                      clkKind = DAE.REAL_CLOCK(e)
                    (cache, clkKind)
                  end

                  (cache, env, ih, DAE.BOOLEAN_CLOCK(e, interval), p)  => begin
                      (cache, e) = prefixExpWork(cache, env, ih, e, p)
                      (cache, interval) = prefixExpWork(cache, env, ih, interval, p)
                      clkKind = DAE.BOOLEAN_CLOCK(e, interval)
                    (cache, clkKind)
                  end

                  (cache, env, ih, DAE.SOLVER_CLOCK(e, method), p)  => begin
                      (cache, e) = prefixExpWork(cache, env, ih, e, p)
                      (cache, method) = prefixExpWork(cache, env, ih, method, p)
                      clkKind = DAE.SOLVER_CLOCK(e, method)
                    (cache, clkKind)
                  end
                end
              end
          (outCache, outClkKind)
        end

        function getPrefixInfo(inPrefix::Prefix.PrefixType) ::SourceInfo
              local outInfo::SourceInfo

              outInfo = begin
                @match inPrefix begin
                  Prefix.PREFIX(compPre = Prefix.PRE(info = outInfo))  => begin
                    outInfo
                  end

                  _  => begin
                      AbsynUtil.dummyInfo
                  end
                end
              end
          outInfo
        end

        function prefixHashWork(inPrefix::Prefix.ComponentPrefix, hash::ModelicaInteger) ::ModelicaInteger


              hash = begin
                @match inPrefix begin
                  Prefix.PRE(__)  => begin
                    prefixHashWork(inPrefix.next, 31 * hash + stringHashDjb2(inPrefix.prefix))
                  end

                  _  => begin
                      hash
                  end
                end
              end
          hash
        end

        function componentPrefixPathEqual(pre1::Prefix.ComponentPrefix, pre2::Prefix.ComponentPrefix) ::Bool
              local eq::Bool

              eq = begin
                @match (pre1, pre2) begin
                  (Prefix.PRE(__), Prefix.PRE(__))  => begin
                    if pre1.prefix == pre2.prefix
                          componentPrefixPathEqual(pre1.next, pre2.next)
                        else
                          false
                        end
                  end

                  (Prefix.NOCOMPPRE(__), Prefix.NOCOMPPRE(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          eq
        end

        function componentPrefix(inPrefix::Prefix.PrefixType) ::Prefix.ComponentPrefix
              local outPrefix::Prefix.ComponentPrefix

              outPrefix = begin
                @match inPrefix begin
                  Prefix.PREFIX(__)  => begin
                    inPrefix.compPre
                  end

                  _  => begin
                      Prefix.NOCOMPPRE()
                  end
                end
              end
          outPrefix
        end

        #=
        function writeComponentPrefix(file::File.FILE, pre::Prefix.ComponentPrefix, escape::File.Escape = File.Escape.None)
              _ = begin
                @match pre begin
                  Prefix.PRE(next = Prefix.NOCOMPPRE(__))  => begin
                      File.writeEscape(file, pre.prefix, escape)
                      CrefForHashTable.writeSubscripts(file, pre.subscripts, escape)
                    ()
                  end

                  Prefix.PRE(__)  => begin
                      writeComponentPrefix(file, pre.next)
                       #=  Stored in reverse order...
                       =#
                      File.writeEscape(file, pre.prefix, escape)
                      CrefForHashTable.writeSubscripts(file, pre.subscripts, escape)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end
        =#

         #= Function: crefHaveSubs
          Checks whether Prefix has any subscripts, recursive  =#
        function haveSubs(pre::Prefix.ComponentPrefix) ::Bool
              local ob::Bool

              ob = begin
                @match pre begin
                  Prefix.PRE(subscripts =  nil())  => begin
                    haveSubs(pre.next)
                  end

                  Prefix.PRE(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          ob
        end

        #= @author: adrpo
         This function searches for outer crefs and prefixes them with the inner prefix =#
       function prefixOuterCrefWithTheInnerPrefix(inIH::InnerOuterTypes.InstHierarchy, inOuterComponentRef::DAE.ComponentRef, inPrefix::Prefix.PrefixType) ::DAE.ComponentRef
             local outInnerComponentRef::DAE.ComponentRef

             outInnerComponentRef = begin
                 local outerCrefPrefix::DAE.ComponentRef
                 local fullCref::DAE.ComponentRef
                 local innerCref::DAE.ComponentRef
                 local innerCrefPrefix::DAE.ComponentRef
                 local outerPrefixes::OuterPrefixes
                  #=  we have no outer references, fail so prefixing can happen in the calling function
                  =#
               @match (inIH, inOuterComponentRef, inPrefix) begin
                 ( nil(), _, _)  => begin
                   fail()
                 end

                 (InnerOuterTypes.TOP_INSTANCE(_, _, outerPrefixes && _ <| _, _) <|  nil(), _, _)  => begin
                     (_, fullCref) = prefixCref(FCoreUtil.emptyCache(), FCore.EG("empty"), emptyInstHierarchy, inPrefix, inOuterComponentRef)
                     (outerCrefPrefix, innerCrefPrefix) = searchForInnerPrefix(fullCref, inOuterComponentRef, outerPrefixes)
                     innerCref = changeOuterReferenceToInnerReference(fullCref, outerCrefPrefix, innerCrefPrefix)
                   innerCref
                 end

                 _  => begin
                     fail()
                 end
               end
             end
              #=  we have some outer references, search for our prefix + cref in them
              =#
              #=  this will fail if we don't find it so prefixing can happen in the calling function
              =#
              #=  fprintln(Flags.FAILTRACE, \"- InnerOuter.prefixOuterCrefWithTheInnerPrefix replaced cref \" + CrefForHashTable.printComponentRefStr(fullCref) + \" with cref: \" + CrefForHashTable.printComponentRefStr(innerCref));
              =#
              #=  failure
              =#
              #=  true = Flags.isSet(Flags.FAILTRACE);
              =#
              #=  Debug.traceln(\"- InnerOuter.prefixOuterCrefWithTheInnerPrefix failed to find prefix of inner for outer: prefix/cref \" + PrefixUtil.printPrefixStr(inPrefix) + \"/\" + CrefForHashTable.printComponentRefStr(inOuterComponentRef));
              =#
         outInnerComponentRef
       end

       #= @author: adrpo
        This function replaces the outer prefix with the inner prefix in the full cref =#
      function changeOuterReferenceToInnerReference(inFullCref::DAE.ComponentRef, inOuterCrefPrefix::DAE.ComponentRef, inInnerCrefPrefix::DAE.ComponentRef) ::DAE.ComponentRef
            local outInnerCref::DAE.ComponentRef

            outInnerCref = begin
                local ifull::DAE.ComponentRef
                local ocp::DAE.ComponentRef
                local icp::DAE.ComponentRef
                local ic::DAE.ComponentRef
                local eifull::List{DAE.ComponentRef}
                local eocp::List{DAE.ComponentRef}
                local eicp::List{DAE.ComponentRef}
                local epre::List{DAE.ComponentRef}
                local erest::List{DAE.ComponentRef}
                local esuffix::List{DAE.ComponentRef}
                 #=  The full cref might contain subscripts that we wish to keep, so we use
                 =#
                 #=  the inner and outer prefix to extract the relevant parts of the full cref.
                 =#
                 #=
                 =#
                 #=  E.g. if we have a full cref a.b.c.d.e.f.g, an outer prefix a.b.c.d.e and
                 =#
                 #=  an inner prefix a.d.e, then we want a, d.e and f.g, resulting in a.d.e.f.g.
                 =#
              @match (inFullCref, inOuterCrefPrefix, inInnerCrefPrefix) begin
                (ifull, ocp, icp)  => begin
                    eifull = CrefForHashTable.explode(ifull)
                    eicp = CrefForHashTable.explode(icp)
                    (eocp, esuffix) = ListUtil.split(eifull, CrefForHashTable.identifierCount(ocp))
                    (epre, erest) = ListUtil.splitEqualPrefix(eocp, eicp, CrefForHashTable.crefFirstIdentEqual)
                    (_, eicp) = ListUtil.splitEqualPrefix(eicp, epre, CrefForHashTable.crefFirstIdentEqual)
                    (erest, _) = ListUtil.splitEqualPrefix(listReverse(erest), listReverse(eicp), CrefForHashTable.crefFirstIdentEqual)
                    erest = ListUtil.append_reverse(erest, esuffix)
                    eifull = listAppend(epre, erest)
                    ic = CrefForHashTable.implode(eifull)
                  ic
                end
              end
            end
             #=  print(\"F:\" + CrefForHashTable.printComponentRefStr(ifull) + \"\\n\" + \"I:\" + CrefForHashTable.printComponentRefStr(icp) + \"\\n\" + \"O:\" + CrefForHashTable.printComponentRefStr(ocp) + \"\\n\");
             =#
             #=  Explode the crefs to lists so that they are easier to work with.
             =#
             #=  Split the full cref so that we get the part that is equal to the
             =#
             #=  outer prefix and the rest of the suffix.
             =#
             #=  Extract the common prefix of the outer and inner prefix.
             =#
             #=  remove the common prefix from the inner!
             =#
             #=  Extract the common suffix of the outer and inner prefix.
             =#
             #=  Combine the parts into a new cref.
             =#
             #=  print(\"C:\" + CrefForHashTable.printComponentRefStr(ic) + \"\\n\");
             =#
        outInnerCref
      end

      #= @author: adrpo
       search in the outer prefixes and retrieve the outer/inner crefs =#
     function searchForInnerPrefix(fullCref::DAE.ComponentRef, inOuterCref::DAE.ComponentRef, outerPrefixes::InnerOuterTypes.OuterPrefixes) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
           local innerCrefPrefix::DAE.ComponentRef
           local outerCrefPrefix::DAE.ComponentRef

           local cr::DAE.ComponentRef
           local id::DAE.ComponentRef
           local b1::Bool = false
           local b2::Bool = false

            #=  print(\"L:\" + intString(listLength(outerPrefixes)) + \"\\n\");
            =#
           for op in outerPrefixes
             @match InnerOuterTypes.OUTER(outerComponentRef = outerCrefPrefix) = op
             b1 = CrefForHashTable.crefPrefixOfIgnoreSubscripts(outerCrefPrefix, fullCref)
             if ! b1
               cr = CrefForHashTable.crefStripLastIdent(outerCrefPrefix)
               b2 = CrefForHashTable.crefLastIdent(outerCrefPrefix) == CrefForHashTable.crefFirstIdent(inOuterCref) && CrefForHashTable.crefPrefixOfIgnoreSubscripts(cr, fullCref)
             end
             if b1 || b2
               @match InnerOuterTypes.OUTER(innerComponentRef = innerCrefPrefix) = op
               return (outerCrefPrefix, innerCrefPrefix)
             end
           end
           fail()
       (outerCrefPrefix, innerCrefPrefix)
     end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

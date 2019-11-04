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

module InnerOuter


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl InstResult
    @UniontypeDecl InstInner
    @UniontypeDecl OuterPrefix
    @UniontypeDecl TopInstance
    @UniontypeDecl InstHierarchyHashTable
    @UniontypeDecl ValueArray
    const InstHierarchy = List
    const emptyInstHierarchy = nil #= an empty instance hierarchy =#::InstHierarchy


        import Absyn
        # import Connect
        import ConnectionGraph
        import DAE
        import FCore
        import FNode
        import Prefix
        import SCode
        import UnitAbsyn
        import HashSet

        import ArrayUtil

        import ComponentReference

        import ConnectUtil

        import DAEUtil

        import Debug

        import Dump

        import ElementSource

        import Error

        import ErrorExt

        import Expression

        import Flags

        import InstSection

        import ListUtil

        import Lookup

        import PrefixUtil

        import System

        import Util

        import VarTransform

        import BaseHashSet

        import FGraph

        Cache = FCore.Cache

         @Uniontype InstResult begin
              @Record INST_RESULT begin

                       outCache::Cache
                       outEnv::FCore.Graph
                       outStore::UnitAbsyn.InstStore
                       outDae::DAE.DAElist
                       outSets::DAE.Sets
                       outType::DAE.Type
                       outGraph::ConnectionGraph.ConnectionGraphType
              end
         end

         @Uniontype InstInner begin
              @Record INST_INNER begin

                       innerPrefix #= the prefix of the inner. we need it to prefix the outer variables with it! =#::Prefix.PrefixType
                       name::SCode.Ident
                       io::Absyn.InnerOuter
                       fullName #= full inner component name =#::String
                       typePath #= the type of the inner =#::Absyn.Path
                       scope #= the scope of the inner =#::String
                       instResult::Option{InstResult}
                       outers #= which outers are referencing this inner =#::List{DAE.ComponentRef}
                       innerElement #= class or component =#::Option{SCode.Element}
              end
         end

         @Uniontype OuterPrefix begin
              @Record OUTER begin

                       outerComponentRef #= the prefix of this outer + component name =#::DAE.ComponentRef
                       innerComponentRef #= the coresponding prefix for this outer + component name =#::DAE.ComponentRef
              end
         end

        OuterPrefixes = List
         const emptyOuterPrefixes = nil #= empty outer prefixes =#::OuterPrefixes

        Key = DAE.ComponentRef  #= the prefix + '.' + the component name =#
        Value = InstInner  #= the inputs of the instantiation function and the results =#

          #= a top instance is an instance of a model thar resides at top level =#
         @Uniontype TopInstance begin
              @Record TOP_INSTANCE begin

                       path #= top model path =#::Option{Absyn.Path}
                       ht #= hash table with fully qualified components =#::InstHierarchyHashTable
                       outerPrefixes #= the outer prefixes help us prefix the outer components with the correct prefix of inner component directly =#::OuterPrefixes
                       sm #= Set of synchronous SM states (fully qualified components) =#::HashSet.HashSetType
              end
         end

         #= Author: BZ, 2008-12
         Depending on the inner outer declaration we do
         different things for dae declared for a variable.
         If it is an outer variable, we remove all equations
         (will be declared again in the inner part).
         If it is InnerOuter declared, we rename all the crefs
         in this equation to unique vars, while we want to keep
         them with this prefix for the inner part of the innerouter. =#
        function handleInnerOuterEquations(io::Absyn.InnerOuter, inDae::DAE.DAElist, inIH::InstHierarchy, inGraphNew::ConnectionGraph.ConnectionGraphType, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{DAE.DAElist, InstHierarchy, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outIH::InstHierarchy
              local odae::DAE.DAElist

              (odae, outIH, outGraph) = begin
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local dae::DAE.DAElist
                  local graphNew::ConnectionGraph.ConnectionGraphType
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstHierarchy
                   #=  is an outer, remove equations
                   =#
                   #=  outer components do NOT change the connection graph!
                   =#
                @matchcontinue (io, inDae, inIH, inGraphNew, inGraph) begin
                  (Absyn.OUTER(__), dae, ih, _, graph)  => begin
                      (odae, _) = DAEUtil.splitDAEIntoVarsAndEquations(dae)
                    (odae, ih, graph)
                  end

                  (Absyn.INNER_OUTER(__), dae, ih, _, graph)  => begin
                      (dae1, dae2) = DAEUtil.splitDAEIntoVarsAndEquations(dae)
                      dae2 = DAEUtil.nameUniqueOuterVars(dae2)
                      dae = DAEUtil.joinDaes(dae1, dae2)
                    (dae, ih, graph)
                  end

                  (Absyn.INNER(__), dae, ih, graphNew, _)  => begin
                    (dae, ih, graphNew)
                  end

                  (Absyn.NOT_INNER_OUTER(__), dae, ih, graphNew, _)  => begin
                    (dae, ih, graphNew)
                  end

                  _  => begin
                        print("- InnerOuter.handleInnerOuterEquations failed!\\n")
                      fail()
                  end
                end
              end
               #=  is both an inner and an outer,
               =#
               #=  rename inner vars in the equations to unique names
               =#
               #=  innerouter component change the connection graph
               =#
               #=  rename variables in the equations and algs.
               =#
               #=  inner vars from dae1 are kept with the same name.
               =#
               #=  adrpo: TODO! FIXME: here we should do a difference of graphNew-graph
               =#
               #=                      and rename the new equations added with unique vars.
               =#
               #=  is an inner do nothing
               =#
               #=  is not an inner nor an outer
               =#
               #=  something went totally wrong!
               =#
          (odae, outIH, outGraph)
        end

         #= changes inner to outer and outer to inner where needed =#
        function changeInnerOuterInOuterConnect(sets::DAE.Sets) ::DAE.Sets


              sets.outerConnects = ListUtil.map(sets.outerConnects, changeInnerOuterInOuterConnect2)
          sets
        end

         #= @author: adrpo
          changes inner to outer and outer to inner where needed =#
        function changeInnerOuterInOuterConnect2(inOC::DAE.OuterConnect) ::DAE.OuterConnect
              local outOC::DAE.OuterConnect

              outOC = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local ncr1::DAE.ComponentRef
                  local ncr2::DAE.ComponentRef
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local f1::DAE.Face
                  local f2::DAE.Face
                  local scope::Prefix.PrefixType
                  local source::DAE.ElementSource #= the origin of the element =#
                   #=  the left hand side is an outer!
                   =#
                @matchcontinue inOC begin
                  DAE.OUTERCONNECT(scope, cr1, io1, f1, cr2, io2, f2, source)  => begin
                      @match (_, true) = innerOuterBooleans(io1)
                      ncr1 = PrefixUtil.prefixToCref(scope)
                      @match false = ComponentReference.crefFirstCrefLastCrefEqual(ncr1, cr1)
                    DAE.OUTERCONNECT(scope, cr1, Absyn.INNER(), f1, cr2, io2, f2, source)
                  end

                  DAE.OUTERCONNECT(scope, cr1, io1, f1, cr2, io2, f2, source)  => begin
                      @match (_, true) = innerOuterBooleans(io2)
                      ncr2 = PrefixUtil.prefixToCref(scope)
                      @match false = ComponentReference.crefFirstCrefLastCrefEqual(ncr2, cr2)
                    DAE.OUTERCONNECT(scope, cr1, io1, f1, cr2, Absyn.INNER(), f2, source)
                  end

                  _  => begin
                      inOC
                  end
                end
              end
               #=  fprintln(Flags.IOS, \"changeInnerOuterInOuterConnect: changing left: \" +
               =#
               #=    ComponentReference.printComponentRefStr(cr1) + \" to inner\");
               =#
               #=  the right hand side is an outer!
               =#
               #=  fprintln(Flags.IOS, \"changeInnerOuterInOuterConnect: changing right: \" +
               =#
               #=    ComponentReference.printComponentRefStr(cr2) + \" to inner\");
               =#
               #=  none of left or right hand side are outer
               =#
          outOC
        end

         #= Builds replacement rules for changing outer references
         to the inner variable =#
        function buildInnerOuterRepl(innerVars::List{<:DAE.Element}, outerVars::List{<:DAE.Element}, inRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local outRepl::VarTransform.VariableReplacements

              outRepl = begin
                  local repl::VarTransform.VariableReplacements
                  local v::DAE.Element
                  local rest::List{DAE.Element}
                @match (innerVars, outerVars, inRepl) begin
                  ( nil(), _, repl)  => begin
                    repl
                  end

                  (v <| rest, _, repl)  => begin
                      repl = buildInnerOuterReplVar(v, outerVars, repl)
                      repl = buildInnerOuterRepl(rest, outerVars, repl)
                    repl
                  end
                end
              end
          outRepl
        end

         #= Help function to buildInnerOuterRepl =#
        function buildInnerOuterReplVar(innerVar::DAE.Element, outerVars::List{<:DAE.Element}, inRepl::VarTransform.VariableReplacements) ::VarTransform.VariableReplacements
              local outRepl::VarTransform.VariableReplacements

              outRepl = begin
                  local outerCrs::List{DAE.ComponentRef}
                  local ourOuterCrs::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                  local repl::VarTransform.VariableReplacements
                @matchcontinue (innerVar, outerVars, inRepl) begin
                  (DAE.VAR(componentRef = cr, innerOuter = Absyn.INNER_OUTER(__)), _, repl)  => begin
                      outerCrs = ListUtil.map(outerVars, DAEUtil.varCref)
                      ourOuterCrs = ListUtil.select1(outerCrs, isInnerOuterMatch, cr)
                      cr = DAEUtil.nameInnerouterUniqueCref(cr)
                      repl = ListUtil.fold1r(ourOuterCrs, VarTransform.addReplacement, Expression.crefExp(cr), repl)
                    repl
                  end

                  (DAE.VAR(componentRef = cr), _, repl)  => begin
                      outerCrs = ListUtil.map(outerVars, DAEUtil.varCref)
                      ourOuterCrs = ListUtil.select1(outerCrs, isInnerOuterMatch, cr)
                      repl = ListUtil.fold1r(ourOuterCrs, VarTransform.addReplacement, Expression.crefExp(cr), repl)
                    repl
                  end
                end
              end
          outRepl
        end

         #= Returns true if an inner element matches an outer, i.e.
        the outer reference should be translated to the inner reference =#
        function isInnerOuterMatch(outerCr::DAE.ComponentRef #=  e.g. a.b.x =#, innerCr::DAE.ComponentRef #=  e.g. x =#) ::Bool
              local res::Bool

              res = begin
                  local innerCr1::DAE.ComponentRef
                  local outerCr1::DAE.ComponentRef
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                   #=  try a simple comparison first.
                   =#
                   #=  adrpo: this case is just to speed up the checking!
                   =#
                @matchcontinue (outerCr, innerCr) begin
                  (_, _)  => begin
                      @match false = ComponentReference.crefLastIdentEqual(outerCr, innerCr)
                    false
                  end

                  _  => begin
                        (outerCr1, innerCr1) = stripCommonCrefPart(outerCr, innerCr)
                        res = ComponentReference.crefContainedIn(outerCr1, innerCr1)
                      res
                  end
                end
              end
               #=  try to compare last ident first!
               =#
               #=  try the hard and expensive case.
               =#
               #=  Strip the common part of inner outer cr.
               =#
               #=  For instance, innerCr = e.f.T1, outerCr = e.f.g.h.a.b.c.d.T1 results in
               =#
               #=  innerCr1 = T1, outerCr = g.h.a.b.c.d.T1
               =#
          res
        end

         #= Help function to isInnerOuterMatch =#
        function stripCommonCrefPart(outerCr::DAE.ComponentRef, innerCr::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
              local outInnerCr::DAE.ComponentRef
              local outOuterCr::DAE.ComponentRef

              (outOuterCr, outInnerCr) = begin
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                  local subs1::List{DAE.Subscript}
                  local subs2::List{DAE.Subscript}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local cr11::DAE.ComponentRef
                  local cr22::DAE.ComponentRef
                @matchcontinue (outerCr, innerCr) begin
                  (DAE.CREF_QUAL(id1, _, _, cr1), DAE.CREF_QUAL(id2, _, _, cr2))  => begin
                      @match true = stringEq(id1, id2)
                      (cr11, cr22) = stripCommonCrefPart(cr1, cr2)
                    (cr11, cr22)
                  end

                  (cr1, cr2)  => begin
                    (cr1, cr2)
                  end
                end
              end
          (outOuterCr, outInnerCr)
        end

         #=
        Author: BZ, 2008-12
        Compares two crefs ex:
        model1.model2.connector vs model2.connector.variable
        would become: model2.connector =#
        function extractCommonPart(prefixedCref::DAE.ComponentRef, innerCref::DAE.ComponentRef) ::DAE.ComponentRef
              local cr3::DAE.ComponentRef

              cr3 = begin
                  local ty::DAE.Type
                  local ty2::DAE.Type
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local c3::DAE.ComponentRef
                @matchcontinue (prefixedCref, innerCref) begin
                  (_, _)  => begin
                      c1 = ComponentReference.crefLastCref(prefixedCref)
                      c2 = ComponentReference.crefLastCref(innerCref)
                      @match true = ComponentReference.crefEqual(c1, c2)
                      c3 = ComponentReference.crefSetLastType(innerCref, ComponentReference.crefLastType(prefixedCref))
                    c3
                  end

                  _  => begin
                        c2 = ComponentReference.crefStripLastIdent(innerCref)
                        cr3 = extractCommonPart(prefixedCref, c2)
                      cr3
                  end
                end
              end
          cr3
        end

         #= Author: BZ, 2008-09
         Helper function for instClass.
         If top scope, traverse DAE and change any uniqnamed vars back to original.
         This is a work around for innerouter declarations. =#
        function renameUniqueVarsInTopScope(isTopScope::Bool, dae::DAE.DAElist) ::DAE.DAElist
              local odae::DAE.DAElist

              odae = begin
                @matchcontinue (isTopScope, dae) begin
                  (_, _)  => begin
                      @match false = System.getHasInnerOuterDefinitions()
                    dae
                  end

                  (true, _)  => begin
                    DAEUtil.renameUniqueOuterVars(dae)
                  end

                  (false, _)  => begin
                    dae
                  end
                end
              end
               #=  adrpo: don't do anything if there are no inner/outer declarations in the model!
               =#
               #=  we are in top level scope (isTopScope=true) and we need to rename
               =#
               #=  we are NOT in top level scope (isTopScope=false) and we need to rename
               =#
          odae
        end

         #= Moves outerConnections to connection sets
         author PA:
         This function moves the connections put in outerConnects to the connection
         set, if a corresponding innner component can be found in the environment.
         If not, they are kept in the outerConnects for use higher up in the instance
         hierarchy. =#
        function retrieveOuterConnections(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inTopCall::Bool, inCGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{DAE.Sets, List{DAE.OuterConnect}, ConnectionGraph.ConnectionGraphType}
              local outCGraph::ConnectionGraph.ConnectionGraphType
              local outInnerOuterConnects::List{DAE.OuterConnect}
              local outSets::DAE.Sets

              local oc::List{DAE.OuterConnect}

              @match DAE.SETS(outerConnects = oc) = inSets
              (oc, outSets, outInnerOuterConnects, outCGraph) = retrieveOuterConnections2(inCache, inEnv, inIH, inPrefix, oc, inSets, inTopCall, inCGraph)
              outSets.outerConnects = oc
          (outSets, outInnerOuterConnects, outCGraph)
        end

         #= @author: adrpo
         This function will strip the given prefix from the component references. =#
        function removeInnerPrefixFromCref(inPrefix::Prefix.PrefixType, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local crefPrefix::DAE.ComponentRef
                  local crOuter::DAE.ComponentRef
                   #=  no prefix to strip, return the cref!
                   =#
                @matchcontinue (inPrefix, inCref) begin
                  (Prefix.NOPRE(__), _)  => begin
                    inCref
                  end

                  (_, _)  => begin
                      crefPrefix = PrefixUtil.prefixToCref(inPrefix)
                      crOuter = ComponentReference.crefStripPrefix(inCref, crefPrefix)
                    crOuter
                  end

                  _  => begin
                      inCref
                  end
                end
              end
               #=  we have a prefix, remove it from the cref
               =#
               #=  transform prefix into cref
               =#
               #=  remove the prefix from the component reference
               =#
               #=  something went wrong, print a failtrace and then
               =#
               #= true = Flags.isSet(Flags.FAILTRACE);
               =#
               #= Debug.traceln(\"- InnerOuter.removeInnerPrefixFromCref failed on prefix: \" + PrefixUtil.printPrefixStr(inPrefix) +
               =#
               #=  \" cref: \" + ComponentReference.printComponentRefStr(inCref));
               =#
          outCref
        end

         #= help function to retrieveOuterConnections =#
        function retrieveOuterConnections2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstHierarchy, inPrefix::Prefix.PrefixType, inOuterConnects::List{<:DAE.OuterConnect}, inSets::DAE.Sets, inTopCall::Bool, inCGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{List{DAE.OuterConnect}, DAE.Sets, List{DAE.OuterConnect}, ConnectionGraph.ConnectionGraphType}
              local outCGraph::ConnectionGraph.ConnectionGraphType
              local outInnerOuterConnects::List{DAE.OuterConnect}
              local outSets::DAE.Sets
              local outOuterConnects::List{DAE.OuterConnect}

              (outOuterConnects, outSets, outInnerOuterConnects, outCGraph) = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local f1::DAE.Face
                  local f2::DAE.Face
                  local oc::DAE.OuterConnect
                  local rest_oc::List{DAE.OuterConnect}
                  local ioc::List{DAE.OuterConnect}
                  local inner1::Bool
                  local inner2::Bool
                  local outer1::Bool
                  local outer2::Bool
                  local added::Bool
                  local scope::Prefix.PrefixType
                  local source::DAE.ElementSource #= the origin of the element =#
                  local info::SourceInfo
                  local sets::DAE.Sets
                  local graph::ConnectionGraph.ConnectionGraphType
                   #=  handle empty
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inOuterConnects, inSets, inTopCall, inCGraph) begin
                  (_, _, _, _,  nil(), _, _, _)  => begin
                    (inOuterConnects, inSets, nil, inCGraph)
                  end

                  (_, _, _, _, DAE.OUTERCONNECT(scope, cr1, io1, f1, cr2, io2, f2, source && DAE.SOURCE(info = info)) <| rest_oc, sets, _, graph)  => begin
                      (inner1, outer1) = lookupVarInnerOuterAttr(inCache, inEnv, inIH, cr1, cr2)
                      @match true = inner1
                      @match false = outer1
                      cr1 = removeInnerPrefixFromCref(inPrefix, cr1)
                      cr2 = removeInnerPrefixFromCref(inPrefix, cr2)
                      (sets, added) = ConnectUtil.addOuterConnectToSets(cr1, cr2, io1, io2, f1, f2, sets, info)
                      (sets, graph) = addOuterConnectIfEmpty(inCache, inEnv, inIH, inPrefix, sets, added, cr1, io1, f1, cr2, io2, f2, info, graph)
                      (rest_oc, sets, ioc, graph) = retrieveOuterConnections2(inCache, inEnv, inIH, inPrefix, rest_oc, sets, inTopCall, graph)
                      rest_oc = if outer1
                            _cons(DAE.OUTERCONNECT(scope, cr1, io1, f1, cr2, io2, f2, source), rest_oc)
                          else
                            rest_oc
                          end
                    (rest_oc, sets, ioc, graph)
                  end

                  (_, _, _, _, DAE.OUTERCONNECT(_, cr1, io1, f1, cr2, io2, f2, DAE.SOURCE(info = info)) <| rest_oc, sets, true, graph)  => begin
                      (inner1, outer1) = innerOuterBooleans(io1)
                      (inner2, outer2) = innerOuterBooleans(io2)
                      @match true = boolOr(inner1, inner2)
                      @match false = boolOr(outer1, outer2)
                      io1 = convertInnerOuterInnerToOuter(io1)
                      io2 = convertInnerOuterInnerToOuter(io2)
                      (sets, added) = ConnectUtil.addOuterConnectToSets(cr1, cr2, io1, io2, f1, f2, sets, info)
                      (sets, graph) = addOuterConnectIfEmpty(inCache, inEnv, inIH, inPrefix, sets, added, cr1, io1, f1, cr2, io2, f2, info, graph)
                      (rest_oc, sets, ioc, graph) = retrieveOuterConnections2(inCache, inEnv, inIH, inPrefix, rest_oc, sets, true, graph)
                    (rest_oc, sets, ioc, graph)
                  end

                  (_, _, _, _, oc <| rest_oc, sets, _, graph)  => begin
                      (rest_oc, sets, ioc, graph) = retrieveOuterConnections2(inCache, inEnv, inIH, inPrefix, rest_oc, sets, inTopCall, graph)
                    (_cons(oc, rest_oc), sets, ioc, graph)
                  end
                end
              end
               #=  an inner only outer connect
               =#
               #=  remove the prefixes so we can find it in the DAE
               =#
               #=  if no connection set available (added = false), create new one
               =#
               #=  if is also outer, then keep it also in the outer connects
               =#
               #=  this case is for innerouter declarations, since we do not have them in environment we need to treat them in a special way
               =#
               #=  for inner outer we set Absyn.INNER()
               =#
               #=  we need to change from inner to outer to be able to join sets in: addOuterConnectToSets
               =#
               #=  If no connection set available (added = false), create new one
               =#
               #=  just keep the outer connects the same if we don't find them in the same scope
               =#
          (outOuterConnects, outSets, outInnerOuterConnects, outCGraph)
        end

         #= Author: BZ, 2008-12
         Change from Absyn.INNER => Absyn.OUTER,
         this to be able to use normal functions
         for the innerouter declared variables/connections. =#
        function convertInnerOuterInnerToOuter(io::Absyn.InnerOuter) ::Absyn.InnerOuter
              local oio::Absyn.InnerOuter

              oio = begin
                @match io begin
                  Absyn.INNER(__)  => begin
                    Absyn.OUTER()
                  end

                  _  => begin
                      io
                  end
                end
              end
          oio
        end

         #= help function to retrieveOuterConnections2
         author PA.
         Adds a new connectionset if inner component
         found but no connection set refering to the
         inner component. In that is case the outer
         connection (from inside sub-components) forms
         a connection set of their own. =#
        function addOuterConnectIfEmpty(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstHierarchy, pre::Prefix.PrefixType, inSets::DAE.Sets, added::Bool #= if true, this function does nothing =#, cr1::DAE.ComponentRef, iio1::Absyn.InnerOuter, f1::DAE.Face, cr2::DAE.ComponentRef, iio2::Absyn.InnerOuter, f2::DAE.Face, info::SourceInfo, inCGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{DAE.Sets, ConnectionGraph.ConnectionGraphType}
              local outCGraph::ConnectionGraph.ConnectionGraphType
              local outSets::DAE.Sets

              (outSets, outCGraph) = begin
                  local vt1::SCode.Variability
                  local vt2::SCode.Variability
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local ct::DAE.ConnectorType
                  local dae::DAE.DAElist
                  local ih::InstHierarchy
                  local sets::DAE.SetTrie
                  local sc::ModelicaInteger
                  local cl::List{DAE.SetConnection}
                  local oc::List{DAE.OuterConnect}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local graph::ConnectionGraph.ConnectionGraphType
                   #=  if it was added, return the same
                   =#
                @match (inCache, inEnv, inIH, pre, inSets, added, cr1, iio1, f1, cr2, iio2, f2, info, inCGraph) begin
                  (_, _, _, _, _, true, _, _, _, _, _, _, _, _)  => begin
                    (inSets, inCGraph)
                  end

                  (cache, env, ih, _, DAE.SETS(sets, sc, cl, oc), false, _, io1, _, _, io2, _, _, graph)  => begin
                      @match (cache, DAE.ATTR(connectorType = ct, variability = vt1), t1, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr1)
                      @match (cache, DAE.ATTR(variability = vt2), t2, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr2)
                      io1 = removeOuter(io1)
                      io2 = removeOuter(io2)
                      @match (cache, env, ih, DAE.SETS(sets = sets, setCount = sc, connections = cl), _, graph) = InstSection.connectComponents(cache, env, ih, DAE.SETS(sets, sc, cl, nil), pre, cr1, f1, t1, vt1, cr2, f2, t2, vt2, ct, io1, io2, graph, info)
                    (DAE.SETS(sets, sc, cl, oc), graph)
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  if it was not added, add it (search for both components)
               =#
               #=  TODO: take care of dae, can contain asserts from connections
               =#
               #=  This can fail, for innerouter, the inner part is not declared in env so instead the call to addOuterConnectIfEmptyNoEnv will succed.
               =#
               #= print(\"Failed lookup: \" + ComponentReference.printComponentRefStr(cr1) + \"\\n\");
               =#
               #= print(\"Failed lookup: \" + ComponentReference.printComponentRefStr(cr2) + \"\\n\");
               =#
               #=  print(\"#FAILURE# in: addOuterConnectIfEmpty:__ \" + ComponentReference.printComponentRefStr(cr1) + \" \" + ComponentReference.printComponentRefStr(cr2) + \"\\n\");
               =#
          (outSets, outCGraph)
        end

         #= help function to retrieveOuterConnections2
         author BZ.
         Adds a new connectionset if inner component found but
         no connection set refering to the inner component.
         In that case the outer connection (from inside
         sub-components) forms a connection set of their own.
         2008-12: This is an extension of addOuterConnectIfEmpty,
                  with the difference that we only need to find
                  one variable in the enviroment. =#
        function addOuterConnectIfEmptyNoEnv(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InstHierarchy, inPre::Prefix.PrefixType, inSets::DAE.Sets, added::Bool #= if true, this function does nothing =#, cr1::DAE.ComponentRef, iio1::Absyn.InnerOuter, f1::DAE.Face, cr2::DAE.ComponentRef, iio2::Absyn.InnerOuter, f2::DAE.Face, info::SourceInfo) ::DAE.Sets
              local outSets::DAE.Sets

              outSets = begin
                  local vt1::SCode.Variability
                  local vt2::SCode.Variability
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local ct::DAE.ConnectorType
                  local dae::DAE.DAElist
                  local ih::InstHierarchy
                  local sets::DAE.SetTrie
                  local sc::ModelicaInteger
                  local cl::List{DAE.SetConnection}
                  local oc::List{DAE.OuterConnect}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local pre::Prefix.PrefixType
                   #=  if it was added, return the same
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPre, inSets, added, cr1, iio1, f1, cr2, iio2, f2, info) begin
                  (_, _, _, _, _, true, _, _, _, _, _, _, _)  => begin
                    inSets
                  end

                  (cache, env, ih, _, DAE.SETS(sets, sc, cl, oc), false, _, io1, _, _, io2, _, _)  => begin
                      @match (cache, DAE.ATTR(connectorType = ct, variability = vt1), t1, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr1)
                      pre = Prefix.NOPRE()
                      t2 = t1
                      vt2 = vt1
                      io1 = removeOuter(io1)
                      io2 = removeOuter(io2)
                      @match (cache, env, ih, DAE.SETS(sets = sets, setCount = sc, connections = cl), _, _) = InstSection.connectComponents(cache, env, ih, DAE.SETS(sets, sc, cl, nil), pre, cr1, f1, t1, vt1, cr2, f2, t2, vt2, ct, io1, io2, ConnectionGraph.EMPTY, info)
                    DAE.SETS(sets, sc, cl, oc)
                  end

                  (cache, env, ih, _, DAE.SETS(sets, sc, cl, oc), false, _, io1, _, _, io2, _, _)  => begin
                      pre = Prefix.NOPRE()
                      @match (cache, DAE.ATTR(connectorType = ct, variability = vt2), t2, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr2)
                      t1 = t2
                      vt1 = vt2
                      io1 = removeOuter(io1)
                      io2 = removeOuter(io2)
                      @match (cache, env, ih, DAE.SETS(sets = sets, setCount = sc, connections = cl), _, _) = InstSection.connectComponents(cache, env, ih, DAE.SETS(sets, sc, cl, nil), pre, cr1, f1, t1, vt1, cr2, f2, t2, vt2, ct, io1, io2, ConnectionGraph.EMPTY, info)
                    DAE.SETS(sets, sc, cl, oc)
                  end

                  _  => begin
                        print("failure in: addOuterConnectIfEmptyNOENV\\n")
                      fail()
                  end
                end
              end
               #=  if it was not added, add it (first component found: cr1)
               =#
               #=  TODO: take care of dae, can contain asserts from connections
               =#
               #=  if it was not added, add it (first component found: cr2)
               =#
               #=  TODO: take care of dae, can contain asserts from connections
               =#
               #=  fail
               =#
          outSets
        end

         #= Removes outer attribute, keeping inner =#
        function removeOuter(io::Absyn.InnerOuter) ::Absyn.InnerOuter
              local outIo::Absyn.InnerOuter

              outIo = begin
                @match io begin
                  Absyn.OUTER(__)  => begin
                    Absyn.NOT_INNER_OUTER()
                  end

                  Absyn.INNER(__)  => begin
                    Absyn.INNER()
                  end

                  Absyn.INNER_OUTER(__)  => begin
                    Absyn.INNER()
                  end

                  Absyn.NOT_INNER_OUTER(__)  => begin
                    Absyn.NOT_INNER_OUTER()
                  end
                end
              end
          outIo
        end

         #= searches for two variables in env and retrieves
         its inner and outer attributes in form of booleans.
         adrpo: Make sure that there are no error messages displayed! =#
        function lookupVarInnerOuterAttr(cache::FCore.Cache, env::FCore.Graph, inIH::InstHierarchy, cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Tuple{Bool, Bool}
              local isOuter::Bool
              local isInner::Bool

              (isInner, isOuter) = begin
                  local io::Absyn.InnerOuter
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local isInner1::Bool
                  local isInner2::Bool
                  local isOuter1::Bool
                  local isOuter2::Bool
                  local ih::InstHierarchy
                   #=  Search for both
                   =#
                @matchcontinue (cache, env, inIH, cr1, cr2) begin
                  (_, _, _, _, _)  => begin
                      ErrorExt.setCheckpoint("lookupVarInnerOuterAttr")
                      @match (_, DAE.ATTR(innerOuter = io1), _, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr1)
                      @match (_, DAE.ATTR(innerOuter = io2), _, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr2)
                      (isInner1, isOuter1) = innerOuterBooleans(io1)
                      (isInner2, isOuter2) = innerOuterBooleans(io2)
                      isInner = isInner1 || isInner2
                      isOuter = isOuter1 || isOuter2
                      ErrorExt.rollBack("lookupVarInnerOuterAttr")
                    (isInner, isOuter)
                  end

                  (_, _, _, _, _)  => begin
                      @match (_, DAE.ATTR(innerOuter = io), _, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr1)
                      (isInner, isOuter) = innerOuterBooleans(io)
                      ErrorExt.rollBack("lookupVarInnerOuterAttr")
                    (isInner, isOuter)
                  end

                  (_, _, _, _, _)  => begin
                      @match (_, DAE.ATTR(innerOuter = io), _, _, _, _, _, _, _) = Lookup.lookupVar(cache, env, cr2)
                      (isInner, isOuter) = innerOuterBooleans(io)
                      ErrorExt.rollBack("lookupVarInnerOuterAttr")
                    (isInner, isOuter)
                  end

                  _  => begin
                        ErrorExt.rollBack("lookupVarInnerOuterAttr")
                      fail()
                  end
                end
              end
               #=  try to find var cr1 (lookup can fail for one of them)
               =#
               #=  ..else try cr2 (lookup can fail for one of them)
               =#
               #=  failure
               =#
          (isInner, isOuter)
        end

         #= Checks that outer declarations has a
         corresponding inner declaration.
         This can only be done at the top scope =#
        function checkMissingInnerDecl(inDae::DAE.DAElist, callScope::Bool #= only done if true =#)
              local innerVars::List{DAE.Element}
              local outerVars::List{DAE.Element}
              local allVars::List{DAE.Element}
              local repl::VarTransform.VariableReplacements
              local srcs::List{DAE.ComponentRef}
              local targets::List{DAE.ComponentRef}

              _ = begin
                @matchcontinue (inDae, callScope) begin
                  (_, _)  => begin
                      @match false = System.getHasInnerOuterDefinitions()
                    ()
                  end

                  (_, true)  => begin
                      @match (DAE.DAE(innerVars), DAE.DAE(outerVars)) = DAEUtil.findAllMatchingElements(inDae, DAEUtil.isInnerVar, DAEUtil.isOuterVar)
                      checkMissingInnerDecl1(DAE.DAE(innerVars), DAE.DAE(outerVars))
                    ()
                  end

                  (_, false)  => begin
                    ()
                  end
                end
              end
               #=  adrpo, do nothing if we have no inner/outer components
               =#
               #=  if call scope is TOP level (true) do the checking
               =#
               #= print(\"DAE has :\" + intString(listLength(inDae)) + \" elements\\n\");
               =#
               #=  if call scope is NOT TOP level (false) do nothing
               =#
        end

         #= checks that the 'inner' prefix is used
         when an corresponding 'outer' variable
         found =#
        function checkMissingInnerDecl1(innerVarsDae::DAE.DAElist, outerVarsDae::DAE.DAElist)
              ListUtil.map1_0(DAEUtil.daeElements(outerVarsDae), checkMissingInnerDecl2, DAEUtil.daeElements(innerVarsDae))
        end

         #= help function to checkMissingInnerDecl =#
        function checkMissingInnerDecl2(outerVar::DAE.Element, innerVars::List{<:DAE.Element})
              _ = begin
                  local str::String
                  local str2::String
                  local cr::DAE.ComponentRef
                  local v::DAE.Element
                  local crs::List{DAE.ComponentRef}
                  local res::List{DAE.ComponentRef}
                  local io::Absyn.InnerOuter
                  local source::DAE.ElementSource
                  local info::SourceInfo
                @match (outerVar, innerVars) begin
                  (DAE.VAR(componentRef = cr, innerOuter = io, source = source), _)  => begin
                      crs = ListUtil.map(innerVars, DAEUtil.varCref)
                      res = ListUtil.select1(crs, isInnerOuterMatch, cr)
                      if listEmpty(res)
                        if ! Flags.getConfigBool(Flags.CHECK_MODEL)
                          str2 = Dump.unparseInnerouterStr(io)
                          str = ComponentReference.printComponentRefStr(cr)
                          info = ElementSource.getElementSourceFileInfo(source)
                          Error.addSourceMessage(Error.MISSING_INNER_PREFIX, list(str, str2), info)
                          fail()
                        end
                      end
                    ()
                  end
                end
              end
        end

         #= function that fails if checkModel option is not set, otherwise it succeeds.
         It should be used for the cases when normal instantiation should fail but
         a instantiation for performing checkModel call should not fail =#
        function failExceptForCheck()
              _ = begin
                @match () begin
                  ()  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                    ()
                  end

                  ()  => begin
                    fail()
                  end
                end
              end
               #= /* false = Flags.getConfigBool(Flags.CHECK_MODEL); */ =#
        end

         #= Returns inner outer information as two booleans =#
        function innerOuterBooleans(io::Absyn.InnerOuter) ::Tuple{Bool, Bool}
              local outer1::Bool
              local inner1::Bool

              (inner1, outer1) = begin
                @match io begin
                  Absyn.INNER(__)  => begin
                    (true, false)
                  end

                  Absyn.OUTER(__)  => begin
                    (false, true)
                  end

                  Absyn.INNER_OUTER(__)  => begin
                    (true, true)
                  end

                  Absyn.NOT_INNER_OUTER(__)  => begin
                    (false, false)
                  end
                end
              end
          (inner1, outer1)
        end

         #=
        Author: BZ, 2008-12
        determin the innerouter attributes for 2 connections.
        Special cases:
          if (innerouter , unspecified) -> do NOT prefix firstelement refers to outer elem
          if (innerouter , outer) -> DO prefix
          else
            use normal function( innerOuterBooleans)
         =#
        function referOuter(io1::Absyn.InnerOuter, io2::Absyn.InnerOuter) ::Tuple{Bool, Bool}
              local prefix2::Bool
              local prefix1::Bool

              (prefix1, prefix2) = begin
                  local b1::Bool
                  local b2::Bool
                @match (io1, io2) begin
                  (Absyn.INNER_OUTER(__), Absyn.NOT_INNER_OUTER(__))  => begin
                    (true, false)
                  end

                  (Absyn.INNER_OUTER(__), Absyn.OUTER(__))  => begin
                    (false, true)
                  end

                  _  => begin
                        (_, b1) = innerOuterBooleans(io1)
                        (_, b2) = innerOuterBooleans(io2)
                      (b1, b2)
                  end
                end
              end
          (prefix1, prefix2)
        end

         #= Returns true if either Absyn.InnerOuter is OUTER. =#
        function outerConnection(io1::Absyn.InnerOuter, io2::Absyn.InnerOuter) ::Bool
              local isOuter::Bool

              isOuter = begin
                @match (io1, io2) begin
                  (Absyn.OUTER(__), _)  => begin
                    true
                  end

                  (_, Absyn.OUTER(__))  => begin
                    true
                  end

                  (Absyn.INNER_OUTER(__), _)  => begin
                    true
                  end

                  (_, Absyn.INNER_OUTER(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          isOuter
        end

         #= @author: adrpo
         Given an instance hierarchy and a component name find the
         modification of the inner component with the same name =#
        function lookupInnerInIH(inTIH::TopInstance, inPrefix::Prefix.PrefixType, inComponentIdent::SCode.Ident) ::InstInner
              local outInstInner::InstInner

              outInstInner = begin
                  local name::SCode.Ident
                  local prefix::Prefix.PrefixType
                  local ht::InstHierarchyHashTable
                  local cref::DAE.ComponentRef
                  local instInner::InstInner
                  local outerPrefixes::OuterPrefixes
                   #=  no prefix, this is an error!
                   =#
                   #=  disabled as this is used in Interactive.getComponents
                   =#
                   #=  and makes mosfiles/interactive_api_attributes.mos to fail!
                   =#
                @matchcontinue (inTIH, inPrefix, inComponentIdent) begin
                  (TOP_INSTANCE(__), Prefix.PREFIX(compPre = Prefix.NOCOMPPRE(__)), _)  => begin
                    lookupInnerInIH(inTIH, Prefix.NOPRE(), inComponentIdent)
                  end

                  (TOP_INSTANCE(__), Prefix.NOPRE(__), name)  => begin
                    emptyInstInner(Prefix.NOPRE(), name)
                  end

                  (TOP_INSTANCE(_, ht, _, _), _, name)  => begin
                      prefix = PrefixUtil.prefixStripLast(inPrefix)
                      (_, cref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, prefix, ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil))
                      instInner = get(cref, ht)
                    instInner
                  end

                  (TOP_INSTANCE(_, ht, _, _), _, name)  => begin
                      prefix = PrefixUtil.prefixStripLast(inPrefix)
                      (_, cref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, prefix, ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil))
                      @shouldFail _ = get(cref, ht)
                      instInner = lookupInnerInIH(inTIH, prefix, name)
                    instInner
                  end

                  (TOP_INSTANCE(__), prefix, name)  => begin
                    emptyInstInner(prefix, name)
                  end
                end
              end
               #=  no prefix, this is an error!
               =#
               #=  disabled as this is used in Interactive.getComponents
               =#
               #=  and makes mosfiles/interactive_api_attributes.mos to fail!
               =#
               #=  fprintln(Flags.INNER_OUTER, \"Error: outer component: \" + name + \" defined at the top level!\");
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : looking for: \" + PrefixUtil.printPrefixStr(Prefix.NOPRE()) + \"/\" + name + \" REACHED TOP LEVEL!\");
               =#
               #=  TODO! add warning!
               =#
               #=  we have a prefix, remove the last cref from the prefix and search!
               =#
               #=  back one step in the instance hierarchy
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : looking for: \" + PrefixUtil.printPrefixStr(inPrefix) + \"/\" + name);
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : stripping and looking for: \" + PrefixUtil.printPrefixStr(prefix) + \"/\" + name);
               =#
               #=  put the name as the last prefix
               =#
               #=  search in instance hierarchy
               =#
               #=  isInner = AbsynUtil.isInner(io);
               =#
               #=  instInner = if_(isInner, instInner, emptyInstInner(inPrefix, name));
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : Looking up: \" +
               =#
               #=   ComponentReference.printComponentRefStr(cref) + \" FOUND with innerPrefix: \" +
               =#
               #=   PrefixUtil.printPrefixStr(innerPrefix));
               =#
               #=  we have a prefix, search recursively as there was a failure before!
               =#
               #=  back one step in the instance hierarchy
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : looking for: \" + PrefixUtil.printPrefixStr(inPrefix) + \"/\" + name);
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : stripping and looking for: \" + PrefixUtil.printPrefixStr(prefix) + \"/\" + name);
               =#
               #=  put the name as the last prefix
               =#
               #=  search in instance hierarchy we had a failure
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : Couldn't find: \" + ComponentReference.printComponentRefStr(cref) + \" going deeper\");
               =#
               #=  call recursively to back one more step!
               =#
               #=  if we fail return nothing
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.lookupInnerInIH : looking for: \" + PrefixUtil.printPrefixStr(prefix) + \"/\" + name + \" NOT FOUND!\");
               =#
               #=  dumpInstHierarchyHashTable(ht);
               =#
          outInstInner
        end

         #=
        Author BZ, 2008-11
        According to specification modifiers on outer elements is not allowed. =#
        function modificationOnOuter(cache::FCore.Cache, env::FCore.Graph, ih::InstHierarchy, prefix::Prefix.PrefixType, componentName::String, cr::DAE.ComponentRef, inMod::DAE.Mod, io::Absyn.InnerOuter, impl::Bool, inInfo::SourceInfo) ::Bool
              local modd::Bool

              modd = begin
                  local s1::String
                  local s2::String
                  local s::String
                   #=  if we don't have the same modification on inner report error!
                   =#
                @matchcontinue (cache, env, ih, prefix, componentName, cr, inMod, io, impl, inInfo) begin
                  (_, _, _, _, _, _, DAE.MOD(__), Absyn.OUTER(__), _, _)  => begin
                      s1 = ComponentReference.printComponentRefStr(cr)
                      #TODO: Fix circular dep between Mod and InnerOuter
                      #s2 = Mod.prettyPrintMod(inMod, 0)
                      s = s1 + " " + s2
                      Error.addSourceMessage(Error.OUTER_MODIFICATION, list(s), inInfo)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          modd
        end

         #= switches the inner to outer attributes of a component in the dae. =#
        function switchInnerToOuterAndPrefix(inDae::List{<:DAE.Element}, io::Absyn.InnerOuter, pre::Prefix.PrefixType) ::List{DAE.Element}
              local outDae::List{DAE.Element}

              outDae = begin
                  local lst::List{DAE.Element}
                  local r_1::List{DAE.Element}
                  local r::List{DAE.Element}
                  local lst_1::List{DAE.Element}
                  local v::DAE.Element
                  local cr::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local t::DAE.Type
                  local e::Option{DAE.Exp}
                  local id::List{DAE.Dimension}
                  local ct::DAE.ConnectorType
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local dir::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local s1::String
                  local s2::String
                  local x::DAE.Element
                  local prot::DAE.VarVisibility
                  local idName::String
                  local source::DAE.ElementSource #= the origin of the element =#
                   #=  Component that is unspecified does not change inner/outer on subcomponents
                   =#
                @matchcontinue (inDae, io, pre) begin
                  (lst, Absyn.NOT_INNER_OUTER(__), _)  => begin
                    lst
                  end

                  ( nil(), _, _)  => begin
                    nil
                  end

                  (DAE.VAR(componentRef = cr, kind = vk, direction = dir, parallelism = prl, protection = prot, ty = t, binding = e, dims = id, connectorType = ct, source = source, variableAttributesOption = dae_var_attr, comment = comment, innerOuter = Absyn.INNER(__)) <| r, _, _)  => begin
                      (_, cr) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, pre, cr)
                      r_1 = switchInnerToOuterAndPrefix(r, io, pre)
                    _cons(DAE.VAR(cr, vk, dir, prl, prot, t, e, id, ct, source, dae_var_attr, comment, io), r_1)
                  end

                  (v && DAE.VAR(__) <| r, _, _)  => begin
                      r_1 = switchInnerToOuterAndPrefix(r, io, pre)
                    _cons(v, r_1)
                  end

                  (DAE.COMP(ident = idName, dAElist = lst, source = source, comment = comment) <| r, _, _)  => begin
                      lst_1 = switchInnerToOuterAndPrefix(lst, io, pre)
                      r_1 = switchInnerToOuterAndPrefix(r, io, pre)
                    _cons(DAE.COMP(idName, lst_1, source, comment), r_1)
                  end

                  (x <| r, _, _)  => begin
                      r_1 = switchInnerToOuterAndPrefix(r, io, pre)
                    _cons(x, r_1)
                  end
                end
              end
               #=  unspecified variables are changed to inner/outer if component has such prefix.
               =#
               #=  If var already have inner/outer, keep it.
               =#
               #=  Traverse components
               =#
          outDae
        end

         #= prefixes all the outer variables in the DAE with the given prefix. =#
        function prefixOuterDaeVars(inDae::List{<:DAE.Element}, crefPrefix::Prefix.PrefixType) ::List{DAE.Element}
              local outDae::List{DAE.Element}

              outDae = begin
                  local lst::List{DAE.Element}
                  local r_1::List{DAE.Element}
                  local r::List{DAE.Element}
                  local lst_1::List{DAE.Element}
                  local v::DAE.Element
                  local cr::DAE.ComponentRef
                  local vk::DAE.VarKind
                  local t::DAE.Type
                  local e::Option{DAE.Exp}
                  local id::List{DAE.Dimension}
                  local ct::DAE.ConnectorType
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local dir::DAE.VarDirection
                  local prl::DAE.VarParallelism
                  local s1::String
                  local s2::String
                  local x::DAE.Element
                  local io::Absyn.InnerOuter
                  local prot::DAE.VarVisibility
                  local idName::String
                  local source::DAE.ElementSource #= the origin of the element =#
                @matchcontinue (inDae, crefPrefix) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.VAR(componentRef = cr, kind = vk, direction = dir, parallelism = prl, protection = prot, ty = t, binding = e, dims = id, connectorType = ct, source = source, variableAttributesOption = dae_var_attr, comment = comment, innerOuter = io) <| r, _)  => begin
                      (_, cr) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, crefPrefix, cr)
                      r_1 = prefixOuterDaeVars(r, crefPrefix)
                    _cons(DAE.VAR(cr, vk, dir, prl, prot, t, e, id, ct, source, dae_var_attr, comment, io), r_1)
                  end

                  (DAE.COMP(ident = idName, dAElist = lst, source = source, comment = comment) <| r, _)  => begin
                      lst_1 = prefixOuterDaeVars(lst, crefPrefix)
                      r_1 = prefixOuterDaeVars(r, crefPrefix)
                    _cons(DAE.COMP(idName, lst_1, source, comment), r_1)
                  end

                  (x <| r, _)  => begin
                      r_1 = prefixOuterDaeVars(r, crefPrefix)
                    _cons(x, r_1)
                  end
                end
              end
               #=  prefix variables.
               =#
               #=  Traverse components
               =#
          outDae
        end

         #=
        function switchInnerToOuterInGraph
          switches the inner to outer attributes of a component in the Env. =#
        function switchInnerToOuterInGraph(inEnv::FCore.Graph, inCr::DAE.ComponentRef) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                  local envIn::FCore.Graph
                  local envRest::FCore.Graph
                  local cr::DAE.ComponentRef
                  local r::FCore.MMRef
                  local n::FCore.Node
                   #=  handle nothingness
                   =#
                @match (inEnv, inCr) begin
                  (FCore.EG(_), _)  => begin
                    inEnv
                  end

                  (FCore.G(scope =  nil()), _)  => begin
                    inEnv
                  end

                  (_, cr)  => begin
                      r = FGraph.lastScopeRef(inEnv)
                      n = FNode.fromRef(r)
                      n = switchInnerToOuterInNode(n, cr)
                      r = FNode.updateRef(r, n)
                    inEnv
                  end
                end
              end
               #=  only need to handle top frame!
               =#
          outEnv
        end

         #=
        function switchInnerToOuterInFrame
          switches the inner to outer attributes of a component in the Frame. =#
        function switchInnerToOuterInNode(inNode::FCore.Node, inCr::DAE.ComponentRef) ::FCore.Node
              local outNode::FCore.Node = inNode

              _ = begin
                @match outNode begin
                  FCore.N(__)  => begin
                      outNode.children = FNode.RefTree.map(outNode.children, (inCr) -> switchInnerToOuterInChild(cr = inCr))
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
          outNode
        end

        function switchInnerToOuterInChild(name::FCore.Name, cr::DAE.ComponentRef, inRef::FCore.MMRef) ::FCore.MMRef
              local ref::FCore.MMRef

              local n::FCore.Node

              n = FNode.fromRef(inRef)
              n = switchInnerToOuterInChildrenValue(n, cr)
              ref = FNode.updateRef(inRef, n)
          ref
        end

         #=
        function switchInnerToOuterInChildrenValue
          switches the inner to outer attributes of a component in the RefTree. =#
        function switchInnerToOuterInChildrenValue(inNode::FCore.Node, inCr::DAE.ComponentRef) ::FCore.Node
              local outNode::FCore.Node

              outNode = begin
                  local cr::DAE.ComponentRef
                  local r::FCore.MMRef
                  local node::FCore.Node
                  local name::DAE.Ident
                  local attributes::DAE.Attributes
                  local visibility::SCode.Visibility
                  local ty::DAE.Type
                  local binding::DAE.Binding
                  local ct::DAE.ConnectorType
                  local parallelism::SCode.Parallelism #= parallelism =#
                  local variability::SCode.Variability #= variability =#
                  local direction::Absyn.Direction #= direction =#
                  local cnstForRange::Option{DAE.Const}
                   #=  inner
                   =#
                @matchcontinue (inNode, inCr) begin
                  (node, _)  => begin
                      r = FNode.childFromNode(node, FNode.itNodeName)
                      @match FCore.IT(DAE.TYPES_VAR(name, attributes, ty, binding, cnstForRange)) = FNode.refData(r)
                      @match DAE.ATTR(ct, parallelism, variability, direction, Absyn.INNER(), visibility) = attributes
                      attributes = DAE.ATTR(ct, parallelism, variability, direction, Absyn.OUTER(), visibility)
                      r = FNode.updateRef(r, FNode.setData(FNode.fromRef(r), FCore.IT(DAE.TYPES_VAR(name, attributes, ty, binding, cnstForRange))))
                    node
                  end

                  (node, _)  => begin
                      r = FNode.childFromNode(node, FNode.itNodeName)
                      @match FCore.IT(DAE.TYPES_VAR(name, attributes, ty, binding, cnstForRange)) = FNode.refData(r)
                      @match DAE.ATTR(ct, parallelism, variability, direction, Absyn.INNER_OUTER(), visibility) = attributes
                      attributes = DAE.ATTR(ct, parallelism, variability, direction, Absyn.OUTER(), visibility)
                      r = FNode.updateRef(r, FNode.setData(FNode.fromRef(r), FCore.IT(DAE.TYPES_VAR(name, attributes, ty, binding, cnstForRange))))
                    node
                  end

                  (_, _)  => begin
                    inNode
                  end
                end
              end
               #=  get the instance child
               =#
               #=  update the ref
               =#
               #=  env = switchInnerToOuterInGraph(env, inCr);
               =#
               #=  inner outer
               =#
               #=  get the instance child
               =#
               #=  update the ref
               =#
               #=  env = switchInnerToOuterInGraph(env, inCr);
               =#
               #=  leave unchanged
               =#
          outNode
        end

         #= /
         =#
         #= / instance hieararchy for inner/outer
         =#
         #= / add furher functions before this
         =#
         #= /
         =#

        function emptyInstInner(innerPrefix::Prefix.PrefixType, name::String) ::InstInner
              local outInstInner::InstInner

              outInstInner = INST_INNER(innerPrefix, name, Absyn.NOT_INNER_OUTER(), "", Absyn.IDENT(""), "", NONE(), nil, NONE())
          outInstInner
        end

         #= @author: adrpo
         This function lookups the result of instatiation of the inner
         component given an instance hierarchy a prefix and a component name. =#
        function lookupInnerVar(inCache::Cache, inEnv::FCore.Graph, inIH::InstHierarchy, inPrefix::Prefix.PrefixType, inIdent::SCode.Ident, io::Absyn.InnerOuter) ::InstInner
              local outInstInner::InstInner

              outInstInner = begin
                  local cache::Cache
                  local n::String
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local tih::TopInstance
                  local instInner::InstInner
                   #=  adrpo: if component is an outer or an inner/outer we need to
                   =#
                   #=         lookup the modification of the inner component and use it
                   =#
                   #=         when we instantiate the outer component
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inIdent, io) begin
                  (_, _, tih <| _, pre, n, _)  => begin
                      instInner = lookupInnerInIH(tih, pre, n)
                    instInner
                  end

                  (_, _, _, pre, n, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("InnerOuter.lookupInnerVar failed on component: " + PrefixUtil.printPrefixStr(pre) + "/" + n)
                    fail()
                  end
                end
              end
               #=  is component an outer or an inner/outer?
               =#
               #= true = AbsynUtil.isOuter(io);   is outer
               =#
               #= false = AbsynUtil.isInner(io);  and is not inner
               =#
               #=  search the instance hierarchy for the inner component
               =#
               #=  failure in case we look for anything else but outer!
               =#
          outInstInner
        end

         #= @author: adrpo
         This function updates the instance hierarchy by adding
         the INNER components to it with the given prefix =#
        function updateInstHierarchy(inIH::InstHierarchy, inPrefix::Prefix.PrefixType, inInnerOuter::Absyn.InnerOuter, inInstInner::InstInner) ::InstHierarchy
              local outIH::InstHierarchy

              outIH = begin
                  local tih::TopInstance
                  local restIH::InstHierarchy
                  local ih::InstHierarchy
                  local cref::DAE.ComponentRef
                  local name::SCode.Ident
                  local io::Absyn.InnerOuter
                  local ht::InstHierarchyHashTable
                  local pathOpt::Option{Absyn.Path}
                  local outerPrefixes::OuterPrefixes
                  local cref_::DAE.ComponentRef
                  local sm::HashSet.HashSetType
                   #= /* only add inner elements
                      case(ih,inPrefix,inInnerOuter,inInstInner as INST_INNER(name=name))
                        equation
                          false = AbsynUtil.isInner(inInnerOuter);
                           prefix the name!
                          (_,cref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(),{},emptyInstHierarchy,inPrefix, ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, {}));
                           print (\"InnerOuter.updateInstHierarchy jumping over non-inner: \" + ComponentReference.printComponentRefStr(cref) + \"\\n\");
                        then
                          ih;*/ =#
                   #=  no hashtable, create one!
                   =#
                @match (inIH, inPrefix, inInnerOuter, inInstInner) begin
                  ( nil(), _, _, INST_INNER(__))  => begin
                      ht = emptyInstHierarchyHashTable()
                      sm = HashSet.emptyHashSet()
                      tih = TOP_INSTANCE(NONE(), ht, emptyOuterPrefixes, sm)
                      ih = updateInstHierarchy(list(tih), inPrefix, inInnerOuter, inInstInner)
                    ih
                  end

                  (TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm) <| restIH, _, _, INST_INNER(name = name))  => begin
                      cref_ = ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil)
                      (_, cref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, inPrefix, cref_)
                      ht = add((cref, inInstInner), ht)
                    _cons(TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm), restIH)
                  end

                  (_, _, _, INST_INNER(__))  => begin
                    fail()
                  end
                end
              end
               #=  print (\"InnerOuter.updateInstHierarchy creating an empty hash table! \\n\");
               =#
               #=  add to the hierarchy
               =#
               #=  prefix the name!
               =#
               #=  add to hashtable!
               =#
               #=  fprintln(Flags.FAILTRACE, \"InnerOuter.updateInstHierarchy adding: \" + PrefixUtil.printPrefixStr(inPrefix) + \"/\" + name + \" to IH\");
               =#
               #=  failure
               =#
               #=  prefix the name!
               =#
               #= (_,cref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(),{},emptyInstHierarchy,inPrefix, ComponentReference.makeCrefIdent(\"UNKNOWN\", DAE.T_UNKNOWN_DEFAULT, {}));
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.updateInstHierarchy failure for: \" +
               =#
               #=    PrefixUtil.printPrefixStr(inPrefix) + \"/\" + name);
               =#
          outIH
        end

         #= @author: BTH
        Add SMNode Machine state to collection of SMNode Machine states in instance hierarchy. =#
        function updateSMHierarchy(smState::DAE.ComponentRef, inIH::InstHierarchy) ::InstHierarchy
              local outIH::InstHierarchy

              outIH = begin
                  local tih::TopInstance
                  local restIH::InstHierarchy
                  local ih::InstHierarchy
                  local cref::DAE.ComponentRef
                  local name::SCode.Ident
                  local ht::InstHierarchyHashTable
                  local pathOpt::Option{Absyn.Path}
                  local outerPrefixes::OuterPrefixes
                  local sm::HashSet.HashSetType
                  local sm2::HashSet.HashSetType
                   #=  no hashtable, create one!
                   =#
                @match (smState, inIH) begin
                  (_,  nil())  => begin
                      ht = emptyInstHierarchyHashTable()
                      sm = HashSet.emptyHashSet()
                      sm2 = BaseHashSet.add(smState, sm)
                      tih = TOP_INSTANCE(NONE(), ht, emptyOuterPrefixes, sm2)
                      ih = list(tih)
                    ih
                  end

                  (cref, TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm) <| restIH)  => begin
                      sm = BaseHashSet.add(cref, sm)
                    _cons(TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm), restIH)
                  end

                  (DAE.CREF_IDENT(ident = name), _)  => begin
                      @match true = Flags.isSet(Flags.INSTANCE)
                      Debug.traceln("InnerOuter.updateSMHierarchy failure for: " + name)
                    fail()
                  end
                end
              end
               #= sm = Debug.bcallret2(true, BaseHashSet.add, smState, sm, sm);
               =#
               #=  FIXME what to put for emptyOuterPrefixes
               =#
               #=  add to the hierarchy
               =#
               #=  add to hashtable!
               =#
               #=  add((cref,inInstInner), ht);
               =#
               #=  failure
               =#
          outIH
        end

        function addClassIfInner(inClass::SCode.Element, inPrefix::Prefix.PrefixType, inScope::FCore.Graph, inIH::InstHierarchy) ::InstHierarchy
              local outIH::InstHierarchy

              outIH = begin
                  local name::String
                  local scopeName::String
                  local io::Absyn.InnerOuter
                   #=  add inner or innerouter
                   =#
                @matchcontinue (inClass, inPrefix, inScope, inIH) begin
                  (SCode.CLASS(name = name, prefixes = SCode.PREFIXES(innerOuter = io)), _, _, _)  => begin
                      @match true = AbsynUtil.isInner(io)
                      scopeName = FGraph.getGraphNameStr(inScope)
                      outIH = updateInstHierarchy(inIH, inPrefix, io, INST_INNER(inPrefix, name, io, name, Absyn.IDENT(name), scopeName, NONE(), nil, SOME(inClass)))
                    outIH
                  end

                  _  => begin
                      inIH
                  end
                end
              end
               #=  add to instance hierarchy
               =#
               #=  prefix
               =#
               #=  class name
               =#
               #=  do nothing if not inner
               =#
          outIH
        end

         #= @author: adrpo
         This function remembers the outer prefix with the correct prefix of the inner =#
        function addOuterPrefixToIH(inIH::InstHierarchy, inOuterComponentRef::DAE.ComponentRef, inInnerComponentRef::DAE.ComponentRef) ::InstHierarchy
              local outIH::InstHierarchy

              outIH = begin
                  local tih::TopInstance
                  local restIH::InstHierarchy
                  local ih::InstHierarchy
                  local ht::InstHierarchyHashTable
                  local pathOpt::Option{Absyn.Path}
                  local outerPrefixes::OuterPrefixes
                  local sm::HashSet.HashSetType
                   #=  no hashtable, create one!
                   =#
                @matchcontinue (inIH, inOuterComponentRef, inInnerComponentRef) begin
                  ( nil(), _, _)  => begin
                      ht = emptyInstHierarchyHashTable()
                      sm = HashSet.emptyHashSet()
                      tih = TOP_INSTANCE(NONE(), ht, list(OUTER(ComponentReference.crefStripSubs(inOuterComponentRef), inInnerComponentRef)), sm)
                      ih = list(tih)
                    ih
                  end

                  (TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm) <| restIH, _, _)  => begin
                      outerPrefixes = ListUtil.unionElt(OUTER(ComponentReference.crefStripSubs(inOuterComponentRef), inInnerComponentRef), outerPrefixes)
                    _cons(TOP_INSTANCE(pathOpt, ht, outerPrefixes, sm), restIH)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("InnerOuter.addOuterPrefix failed to add: outer cref: " + ComponentReference.printComponentRefStr(inOuterComponentRef) + " refers to inner cref: " + ComponentReference.printComponentRefStr(inInnerComponentRef) + " to IH")
                      fail()
                  end
                end
              end
               #=  create an empty table and add the crefs to it.
               =#
               #=  add to the top instance
               =#
               #=  fprintln(Flags.INNER_OUTER, \"InnerOuter.addOuterPrefix adding: outer cref: \" +
               =#
               #=    ComponentReference.printComponentRefStr(inOuterComponentRef) + \" refers to inner cref: \" +
               =#
               #=    ComponentReference.printComponentRefStr(inInnerComponentRef) + \" to IH\");
               =#
               #=  failure
               =#
          outIH
        end

         #= @author: adrpo
          This function searches for outer crefs and prefixes them with the inner prefix =#
        function prefixOuterCrefWithTheInnerPrefix(inIH::InstHierarchy, inOuterComponentRef::DAE.ComponentRef, inPrefix::Prefix.PrefixType) ::DAE.ComponentRef
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

                  (TOP_INSTANCE(_, _, outerPrefixes && _ <| _, _) <|  nil(), _, _)  => begin
                      (_, fullCref) = PrefixUtil.prefixCref(FCoreUtil.emptyCache(), FGraph.empty(), emptyInstHierarchy, inPrefix, inOuterComponentRef)
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
               #=  fprintln(Flags.FAILTRACE, \"- InnerOuter.prefixOuterCrefWithTheInnerPrefix replaced cref \" + ComponentReference.printComponentRefStr(fullCref) + \" with cref: \" + ComponentReference.printComponentRefStr(innerCref));
               =#
               #=  failure
               =#
               #=  true = Flags.isSet(Flags.FAILTRACE);
               =#
               #=  Debug.traceln(\"- InnerOuter.prefixOuterCrefWithTheInnerPrefix failed to find prefix of inner for outer: prefix/cref \" + PrefixUtil.printPrefixStr(inPrefix) + \"/\" + ComponentReference.printComponentRefStr(inOuterComponentRef));
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
                      eifull = ComponentReference.explode(ifull)
                      eicp = ComponentReference.explode(icp)
                      (eocp, esuffix) = ListUtil.split(eifull, ComponentReference.identifierCount(ocp))
                      (epre, erest) = ListUtil.splitEqualPrefix(eocp, eicp, ComponentReference.crefFirstIdentEqual)
                      (_, eicp) = ListUtil.splitEqualPrefix(eicp, epre, ComponentReference.crefFirstIdentEqual)
                      (erest, _) = ListUtil.splitEqualPrefix(listReverse(erest), listReverse(eicp), ComponentReference.crefFirstIdentEqual)
                      erest = ListUtil.append_reverse(erest, esuffix)
                      eifull = listAppend(epre, erest)
                      ic = ComponentReference.implode(eifull)
                    ic
                  end
                end
              end
               #=  print(\"F:\" + ComponentReference.printComponentRefStr(ifull) + \"\\n\" + \"I:\" + ComponentReference.printComponentRefStr(icp) + \"\\n\" + \"O:\" + ComponentReference.printComponentRefStr(ocp) + \"\\n\");
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
               #=  print(\"C:\" + ComponentReference.printComponentRefStr(ic) + \"\\n\");
               =#
          outInnerCref
        end

         #= @author: adrpo
          search in the outer prefixes and retrieve the outer/inner crefs =#
        function searchForInnerPrefix(fullCref::DAE.ComponentRef, inOuterCref::DAE.ComponentRef, outerPrefixes::OuterPrefixes) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
              local innerCrefPrefix::DAE.ComponentRef
              local outerCrefPrefix::DAE.ComponentRef

              local cr::DAE.ComponentRef
              local id::DAE.ComponentRef
              local b1::Bool = false
              local b2::Bool = false

               #=  print(\"L:\" + intString(listLength(outerPrefixes)) + \"\\n\");
               =#
              for op in outerPrefixes
                @match OUTER(outerComponentRef = outerCrefPrefix) = op
                b1 = ComponentReference.crefPrefixOfIgnoreSubscripts(outerCrefPrefix, fullCref)
                if ! b1
                  cr = ComponentReference.crefStripLastIdent(outerCrefPrefix)
                  b2 = ComponentReference.crefLastIdent(outerCrefPrefix) == ComponentReference.crefFirstIdent(inOuterCref) && ComponentReference.crefPrefixOfIgnoreSubscripts(cr, fullCref)
                end
                if b1 || b2
                  @match OUTER(innerComponentRef = innerCrefPrefix) = op
                  return (outerCrefPrefix, innerCrefPrefix)
                end
              end
              fail()
          (outerCrefPrefix, innerCrefPrefix)
        end

        function printInnerDefStr(inInstInner::InstInner) ::String
              local outStr::String

              outStr = begin
                  local innerPrefix::Prefix.PrefixType
                  local name::SCode.Ident
                  local io::Absyn.InnerOuter
                  local instResult::Option{InstResult}
                  local fullName::String #= full inner component name =#
                  local typePath::Absyn.Path #= the type of the inner =#
                  local scope::String #= the scope of the inner =#
                  local outers::List{DAE.ComponentRef} #= which outers are referencing this inner =#
                  local str::String
                  local strOuters::String
                @match inInstInner begin
                  INST_INNER(_, _, _, fullName, typePath, scope, _, outers, _)  => begin
                      outers = ListUtil.uniqueOnTrue(outers, ComponentReference.crefEqualNoStringCompare)
                      strOuters = if listEmpty(outers)
                            ""
                          else
                            " Referenced by 'outer' components: {" + stringDelimitList(ListUtil.map(outers, ComponentReference.printComponentRefStr), ", ") + "}"
                          end
                      str = AbsynUtil.pathString(typePath) + " " + fullName + "; defined in scope: " + scope + "." + strOuters
                    str
                  end
                end
              end
          outStr
        end

         #= @author: adrpo
         This function retrieves all the existing inner declarations as a string =#
        function getExistingInnerDeclarations(inIH::InstHierarchy, inEnv::FCore.Graph) ::String
              local innerDeclarations::String

              innerDeclarations = begin
                  local tih::TopInstance
                  local restIH::InstHierarchy
                  local ht::InstHierarchyHashTable
                  local pathOpt::Option{Absyn.Path}
                  local outerPrefixes::OuterPrefixes
                  local inners::List{InstInner}
                  local str::String
                   #=  we have no inner components yet
                   =#
                @match (inIH, inEnv) begin
                  ( nil(), _)  => begin
                    "There are no 'inner' components defined in the model in any of the parent scopes of 'outer' component's scope: " + FGraph.printGraphPathStr(inEnv) + "."
                  end

                  (TOP_INSTANCE(_, ht, _, _) <| _, _)  => begin
                      inners = getInnersFromInstHierarchyHashTable(ht)
                      str = stringDelimitList(ListUtil.map(inners, printInnerDefStr), "\\n    ")
                    str
                  end
                end
              end
               #=  get the list of components
               =#
          innerDeclarations
        end

         #= @author: adrpo
          Returns all the inners defined in the hashtable. =#
        function getInnersFromInstHierarchyHashTable(t::InstHierarchyHashTable) ::List{InstInner}
              local inners::List{InstInner}

              inners = ListUtil.map(hashTableList(t), getValue)
          inners
        end

        function getValue(tpl::Tuple{<:Key, Value}) ::InstInner
              local v::InstInner

              v = begin
                @match tpl begin
                  (_, v)  => begin
                    v
                  end
                end
              end
          v
        end

         #= /
         =#
         #=  hash table implementation for InnerOuter instance hierarchy
         =#
         #= /
         =#

         #= author: PA
          Calculates a hash value for DAE.ComponentRef =#
        function hashFunc(k::Key) ::ModelicaInteger
              local res::ModelicaInteger

              res = stringHashDjb2(ComponentReference.printComponentRefStr(k))
          res
        end

        function keyEqual(key1::Key, key2::Key) ::Bool
              local res::Bool

              res = ComponentReference.crefEqualNoStringCompare(key1, key2)
          res
        end

         #=  =#
        function dumpInstHierarchyHashTable(t::InstHierarchyHashTable)
              print("InstHierarchyHashTable:\\n")
              print(stringDelimitList(ListUtil.map(hashTableList(t), dumpTuple), "\\n"))
              print("\\n")
        end

        function dumpTuple(tpl::Tuple{<:Key, Value}) ::String
              local str::String

              str = begin
                  local k::Key
                  local v::Value
                @match tpl begin
                  (k, _)  => begin
                      str = "{" + ComponentReference.crefStr(k) + " opaque InstInner for now, implement printing. " + "}\\n"
                    str
                  end
                end
              end
          str
        end

         #= /* end of InstHierarchyHashTable instance specific code */ =#
         #= /* Generic hashtable code below!! */ =#

         @Uniontype InstHierarchyHashTable begin
              @Record HASHTABLE begin

                       hashTable #=  hashtable to translate Key to array indx =#::Array{List{Tuple{Key, ModelicaInteger}}}
                       valueArr #= Array of values =#::ValueArray
                       bucketSize #= bucket size =#::ModelicaInteger
                       numberOfEntries #= number of entries in hashtable =#::ModelicaInteger
              end
         end

          #= array of values are expandable, to amortize the
          cost of adding elements in a more efficient manner =#
         @Uniontype ValueArray begin
              @Record VALUE_ARRAY begin

                       numberOfElements #= number of elements in hashtable =#::ModelicaInteger
                       valueArray #= array of values =#::Array{Option{Tuple{Key, Value}}}
              end
         end

         #= Author BZ 2008-06
         Make a stand-alone-copy of hashtable. =#
        function cloneInstHierarchyHashTable(inHash::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHash::InstHierarchyHashTable

              outHash = begin
                  local arg1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local arg1_2::Array{List{Tuple{Key, ModelicaInteger}}}
                  local arg3::ModelicaInteger
                  local arg4::ModelicaInteger
                  local arg3_2::ModelicaInteger
                  local arg4_2::ModelicaInteger
                  local arg21::ModelicaInteger
                  local arg21_2::ModelicaInteger
                  local arg22::Array{Option{Tuple{Key, Value}}}
                  local arg22_2::Array{Option{Tuple{Key, Value}}}
                @match inHash begin
                  HASHTABLE(arg1, VALUE_ARRAY(arg21, arg22), arg3, arg4)  => begin
                      arg1_2 = arrayCopy(arg1)
                      arg21_2 = arg21
                      arg22_2 = arrayCopy(arg22)
                      arg3_2 = arg3
                      arg4_2 = arg4
                    HASHTABLE(arg1_2, VALUE_ARRAY(arg21_2, arg22_2), arg3_2, arg4_2)
                  end
                end
              end
          outHash
        end

         #= author: PA
          Returns an empty InstHierarchyHashTable.
          Using the bucketsize 100 and array size 10. =#
        function emptyInstHierarchyHashTable() ::InstHierarchyHashTable
              local hashTable::InstHierarchyHashTable

              local arr::Array{List{Tuple{Key, ModelicaInteger}}}
              local lst::List{Option{Tuple{Key, Value}}}
              local emptyarr::Array{Option{Tuple{Key, Value}}}

              arr = arrayCreate(1000, nil)
              emptyarr = arrayCreate(100, NONE())
              hashTable = HASHTABLE(arr, VALUE_ARRAY(0, emptyarr), 1000, 0)
          hashTable
        end

         #= Returns true if hashtable is empty =#
        function isEmpty(hashTable::InstHierarchyHashTable) ::Bool
              local res::Bool

              res = begin
                @match hashTable begin
                  HASHTABLE(_, _, _, 0)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= author: PA
          Add a Key-Value tuple to hashtable.
          If the Key-Value tuple already exists, the function updates the Value. =#
        function add(entry::Tuple{<:Key, Value}, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local key::Key
                  local value::Value
                   #= /* Adding when not existing previously */ =#
                @matchcontinue (entry, hashTable) begin
                  (v && (key, _), HASHTABLE(hashvec, varr, bsize, _))  => begin
                      @shouldFail _ = get(key, hashTable)
                      hval = hashFunc(key)
                      indx = intMod(hval, bsize)
                      newpos = valueArrayLength(varr)
                      varr_1 = valueArrayAdd(varr, v)
                      indexes = hashvec[indx + 1]
                      hashvec_1 = arrayUpdate(hashvec, indx + 1, _cons((key, newpos), indexes))
                      n_1 = valueArrayLength(varr_1)
                    HASHTABLE(hashvec_1, varr_1, bsize, n_1)
                  end

                  (newv && (key, _), HASHTABLE(hashvec, varr, bsize, n))  => begin
                      (_, indx) = get1(key, hashTable)
                      varr_1 = valueArraySetnth(varr, indx, newv)
                    HASHTABLE(hashvec, varr_1, bsize, n)
                  end

                  _  => begin
                        print("- InnerOuter.add failed\\n")
                      fail()
                  end
                end
              end
               #=  print(\"Added NEW to IH: key:\" + ComponentReference.printComponentRefStr(key) + \" value: \" + printInnerDefStr(value) + \"\\n\");
               =#
               #= /* adding when already present => Updating value */ =#
               #= print(\"adding when present, indx =\" );print(intString(indx));print(\"\\n\");
               =#
               #=  print(\"Updated NEW to IH: key:\" + ComponentReference.printComponentRefStr(key) + \" value: \" + printInnerDefStr(value) + \"\\n\");
               =#
          outHashTable
        end

         #= author: PA
          Add a Key-Value tuple to hashtable.
          If the Key-Value tuple already exists, the function updates the Value. =#
        function addNoUpdCheck(entry::Tuple{<:Key, Value}, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local name_str::String
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local key::Key
                  local value::Value
                   #=  Adding when not existing previously
                   =#
                @matchcontinue (entry, hashTable) begin
                  (v && (key, _), HASHTABLE(hashvec, varr, bsize, _))  => begin
                      hval = hashFunc(key)
                      indx = intMod(hval, bsize)
                      newpos = valueArrayLength(varr)
                      varr_1 = valueArrayAdd(varr, v)
                      indexes = hashvec[indx + 1]
                      hashvec_1 = arrayUpdate(hashvec, indx + 1, _cons((key, newpos), indexes))
                      n_1 = valueArrayLength(varr_1)
                    HASHTABLE(hashvec_1, varr_1, bsize, n_1)
                  end

                  _  => begin
                        print("- InnerOuter.addNoUpdCheck failed\\n")
                      fail()
                  end
                end
              end
          outHashTable
        end

         #= author: PA
          delete the Value associatied with Key from the InstHierarchyHashTable.
          Note: This function does not delete from the index table, only from the ValueArray.
          This means that a lot of deletions will not make the InstHierarchyHashTable more compact, it
          will still contain a lot of incices information. =#
        function delete(key::Key, hashTable::InstHierarchyHashTable) ::InstHierarchyHashTable
              local outHashTable::InstHierarchyHashTable

              outHashTable = begin
                  local hval::ModelicaInteger
                  local indx::ModelicaInteger
                  local newpos::ModelicaInteger
                  local n::ModelicaInteger
                  local n_1::ModelicaInteger
                  local bsize::ModelicaInteger
                  local indx_1::ModelicaInteger
                  local varr_1::ValueArray
                  local varr::ValueArray
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local hashvec_1::Array{List{Tuple{Key, ModelicaInteger}}}
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local name_str::String
                  local v::Tuple{Key, Value}
                  local newv::Tuple{Key, Value}
                  local value::Value
                   #=  adding when already present => Updating value
                   =#
                @matchcontinue (key, hashTable) begin
                  (_, HASHTABLE(hashvec, varr, bsize, n))  => begin
                      (_, indx) = get1(key, hashTable)
                      varr_1 = valueArrayClearnth(varr, indx)
                    HASHTABLE(hashvec, varr_1, bsize, n)
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.delete failed\\n")
                        print("content:")
                        dumpInstHierarchyHashTable(hashTable)
                      fail()
                  end
                end
              end
          outHashTable
        end

         #= author: PA
          Returns a Value given a Key and a InstHierarchyHashTable. =#
        function get(key::Key, hashTable::InstHierarchyHashTable) ::Value
              local value::Value

              (value, _) = get1(key, hashTable)
          value
        end

         #= help function to get =#
        function get1(key::Key, hashTable::InstHierarchyHashTable) ::Tuple{Value, ModelicaInteger}
              local indx::ModelicaInteger
              local value::Value

              (value, indx) = begin
                  local hval::ModelicaInteger
                  local hashindx::ModelicaInteger
                  local bsize::ModelicaInteger
                  local n::ModelicaInteger
                  local indexes::List{Tuple{Key, ModelicaInteger}}
                  local v::Value
                  local hashvec::Array{List{Tuple{Key, ModelicaInteger}}}
                  local varr::ValueArray
                  local k::Key
                @match (key, hashTable) begin
                  (_, HASHTABLE(hashvec, varr, bsize, _))  => begin
                      hval = hashFunc(key)
                      hashindx = intMod(hval, bsize)
                      indexes = hashvec[hashindx + 1]
                      indx = get2(key, indexes)
                      (k, v) = valueArrayNth(varr, indx)
                      @match true = keyEqual(k, key)
                    (v, indx)
                  end
                end
              end
          (value, indx)
        end

         #= author: PA
          Helper function to get =#
        function get2(key::Key, keyIndices::List{<:Tuple{<:Key, ModelicaInteger}}) ::ModelicaInteger
              local index::ModelicaInteger

              index = begin
                  local key2::Key
                  local xs::List{Tuple{Key, ModelicaInteger}}
                @matchcontinue (key, keyIndices) begin
                  (_, (key2, index) <| _)  => begin
                      @match true = keyEqual(key, key2)
                    index
                  end

                  (_, _ <| xs)  => begin
                      index = get2(key, xs)
                    index
                  end
                end
              end
          index
        end

         #= return the Value entries as a list of Values =#
        function hashTableValueList(hashTable::InstHierarchyHashTable) ::List{Value}
              local valLst::List{Value}

              valLst = ListUtil.map(hashTableList(hashTable), Util.tuple22)
          valLst
        end

         #= return the Key entries as a list of Keys =#
        function hashTableKeyList(hashTable::InstHierarchyHashTable) ::List{Key}
              local valLst::List{Key}

              valLst = ListUtil.map(hashTableList(hashTable), Util.tuple21)
          valLst
        end

         #= returns the entries in the hashTable as a list of tuple<Key,Value> =#
        function hashTableList(hashTable::InstHierarchyHashTable) ::List{Tuple{Key, Value}}
              local tplLst::List{Tuple{Key, Value}}

              tplLst = begin
                  local varr::ValueArray
                @match hashTable begin
                  HASHTABLE(valueArr = varr)  => begin
                      tplLst = valueArrayList(varr)
                    tplLst
                  end
                end
              end
          tplLst
        end

         #= author: PA
          Transforms a ValueArray to a tuple<Key,Value> list =#
        function valueArrayList(valueArray::ValueArray) ::List{Tuple{Key, Value}}
              local tplLst::List{Tuple{Key, Value}}

              tplLst = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local elt::Tuple{Key, Value}
                  local lastpos::ModelicaInteger
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                  local lst::List{Tuple{Key, Value}}
                @matchcontinue valueArray begin
                  VALUE_ARRAY(numberOfElements = 0)  => begin
                    nil
                  end

                  VALUE_ARRAY(numberOfElements = 1, valueArray = arr)  => begin
                      @match SOME(elt) = arr[0 + 1]
                    list(elt)
                  end

                  VALUE_ARRAY(numberOfElements = n, valueArray = arr)  => begin
                      lastpos = n - 1
                      lst = valueArrayList2(arr, 0, lastpos)
                    lst
                  end
                end
              end
          tplLst
        end

         #= Helper function to valueArrayList =#
        function valueArrayList2(inVarOptionArray1::Array{<:Option{<:Tuple{<:Key, Value}}}, inInteger2::ModelicaInteger, inInteger3::ModelicaInteger) ::List{Tuple{Key, Value}}
              local outVarLst::List{Tuple{Key, Value}}

              outVarLst = begin
                  local v::Tuple{Key, Value}
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local pos::ModelicaInteger
                  local lastpos::ModelicaInteger
                  local pos_1::ModelicaInteger
                  local res::List{Tuple{Key, Value}}
                @matchcontinue (inVarOptionArray1, inInteger2, inInteger3) begin
                  (arr, pos, lastpos)  => begin
                      if !(pos == lastpos)
                        fail()
                      end
                      @match SOME(v) = arr[pos + 1]
                    list(v)
                  end

                  (arr, pos, lastpos)  => begin
                      pos_1 = pos + 1
                      @match SOME(v) = arr[pos + 1]
                      res = valueArrayList2(arr, pos_1, lastpos)
                    _cons(v, res)
                  end

                  (arr, pos, lastpos)  => begin
                      pos_1 = pos + 1
                      @match NONE() = arr[pos + 1]
                      res = valueArrayList2(arr, pos_1, lastpos)
                    res
                  end
                end
              end
          outVarLst
        end

         #= author: PA
          Returns the number of elements in the ValueArray =#
        function valueArrayLength(valueArray::ValueArray) ::ModelicaInteger
              local size::ModelicaInteger

              size = begin
                @match valueArray begin
                  VALUE_ARRAY(numberOfElements = size)  => begin
                    size
                  end
                end
              end
          size
        end

         #= author: PA
          Adds an entry last to the ValueArray, increasing
          array size if no space left by factor 1.4 =#
        function valueArrayAdd(valueArray::ValueArray, entry::Tuple{<:Key, Value}) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local n_1::ModelicaInteger
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                  local expandsize::ModelicaInteger
                  local expandsize_1::ModelicaInteger
                  local newsize::ModelicaInteger
                  local arr_1::Array{Option{Tuple{Key, Value}}}
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local arr_2::Array{Option{Tuple{Key, Value}}}
                  local rsize::ModelicaReal
                  local rexpandsize::ModelicaReal
                @matchcontinue (valueArray, entry) begin
                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      if !(n < arrayLength(arr))
                        fail() #= Have space to add array elt. =#
                      end #= Have space to add array elt. =#
                      n_1 = n + 1
                      arr_1 = arrayUpdate(arr, n + 1, SOME(entry))
                    VALUE_ARRAY(n_1, arr_1)
                  end

                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      size = arrayLength(arr)
                      if (n < size)
                        fail() #= Do NOT have splace to add array elt. Expand with factor 1.4 =#
                      end #= Do NOT have splace to add array elt. Expand with factor 1.4 =#
                      rsize = intReal(size)
                      rexpandsize = rsize * 0.4
                      expandsize = realInt(rexpandsize)
                      expandsize_1 = intMax(expandsize, 1)
                      arr_1 = ArrayUtil.expand(expandsize_1, arr, NONE())
                      n_1 = n + 1
                      arr_2 = arrayUpdate(arr_1, n + 1, SOME(entry))
                    VALUE_ARRAY(n_1, arr_2)
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArrayAdd failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Set the n:th variable in the ValueArray to value. =#
        function valueArraySetnth(valueArray::ValueArray, pos::ModelicaInteger, entry::Tuple{<:Key, Value}) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                @matchcontinue (valueArray, pos, entry) begin
                  (VALUE_ARRAY(_, arr), _, _)  => begin
                      if !(pos < arrayLength(arr))
                        fail()
                      end
                      arrayUpdate(arr, pos + 1, SOME(entry))
                    valueArray
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArraySetnth failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Clears the n:th variable in the ValueArray (set to NONE()). =#
        function valueArrayClearnth(valueArray::ValueArray, pos::ModelicaInteger) ::ValueArray
              local outValueArray::ValueArray

              outValueArray = begin
                  local arr::Array{Option{Tuple{Key, Value}}}
                  local n::ModelicaInteger
                  local size::ModelicaInteger
                @matchcontinue (valueArray, pos) begin
                  (VALUE_ARRAY(_, arr), _)  => begin
                      if !(pos < arrayLength(arr))
                        fail()
                      end
                      arrayUpdate(arr, pos + 1, NONE())
                    valueArray
                  end

                  _  => begin
                        print("-InstHierarchyHashTable.valueArrayClearnth failed\\n")
                      fail()
                  end
                end
              end
          outValueArray
        end

         #= author: PA
          Retrieve the n:th Vale from ValueArray, index from 0..n-1. =#
        function valueArrayNth(valueArray::ValueArray, pos::ModelicaInteger) ::Tuple{Key, Value}
              local value::Value
              local key::Key

              (key, value) = begin
                  local k::Key
                  local v::Value
                  local n::ModelicaInteger
                  local arr::Array{Option{Tuple{Key, Value}}}
                @match (valueArray, pos) begin
                  (VALUE_ARRAY(numberOfElements = n, valueArray = arr), _)  => begin
                      if !(pos < n)
                        fail()
                      end
                      @match SOME((k, v)) = arr[pos + 1]
                    (k, v)
                  end
                end
              end
          (key, value)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

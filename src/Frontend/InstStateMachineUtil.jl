  module InstStateMachineUtil 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl SMNode 
    @UniontypeDecl FlatSMGroup 
    @UniontypeDecl IncidenceTable 

         #= /*
         * This file is part of OpenModelica.
         *
         * Copyright (c) 1998-2015, Open Source Modelica Consortium (OSMC),
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
        
        import SCode

        import DAE

        import Config

        import Flags

        import ListUtil

        import ComponentReference
        
        import BaseHashTable

        import HashTable

        import HashTableSM1

        import HashTableCG

        import HashTable3

        import HashSet

        import Util

        import ArrayUtil

        import DAEUtil

        import InnerOuterTypes

        import Expression

        import Debug
        
        import Prefix

        import PrefixUtil

        import DAEDump

         @Uniontype SMNode begin
              @Record SMNODE begin

                       #= DAE.Ident ident;
                       =#
                       componentRef::DAE.ComponentRef
                       isInitial::Bool
                       edges #= relations to other modes due to in- and out-going transitions =#::HashSet.HashSetType
              end
         end

         @Uniontype FlatSMGroup begin
              @Record FLAT_SM_GROUP begin

                       initState::DAE.ComponentRef
                       states::Array{DAE.ComponentRef}
              end
         end

         @Uniontype IncidenceTable begin
              @Record INCIDENCE_TABLE begin

                       cref2index #= Map cref to corresponding index in incidence matrix =#::HashTable.HashTableType
                       incidence #= Incidence matrix showing which modes are connected by transitions =#::Array{Array{Bool}}
              end
         end

         #=  Table having crefs as keys and corresponding SMNODE as value
         =#
        SMNodeTable = HashTableSM1.HashTable 
         #=  Table mapping crefs of SMNodes to corresponding crefs of FlatSMGroup
         =#
        SMNodeToFlatSMGroupTable = HashTableCG.HashTable 
         const SMS_PRE = "smOf" #= prefix for flat SMNode Machine names =#::String

         const DEBUG_SMDUMP = false #= enable verbose stdout debug information during elaboration =#::Bool

         #= 
        Author: BTH
        Create table that associates a state instance with its governing flat state machine.
         =#
        function createSMNodeToFlatSMGroupTable(inDae::DAE.DAElist) ::SMNodeToFlatSMGroupTable 
              local smNodeToFlatSMGroup::SMNodeToFlatSMGroupTable

              local elementLst::List{DAE.Element}
              local smNodeTable::SMNodeTable
              local nStates::ModelicaInteger
              local iTable::IncidenceTable
              local transClosure::IncidenceTable
              local initialStates::List{DAE.ComponentRef}
              local flatSMGroup::List{FlatSMGroup}

              if intLt(Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), 33)
                smNodeToFlatSMGroup = HashTableCG.emptyHashTableSized(1)
                return smNodeToFlatSMGroup
              end
              @match DAE.DAE_LIST(elementLst = elementLst) = inDae
              smNodeTable = getSMNodeTable(elementLst)
              nStates = BaseHashTable.hashTableCurrentSize(smNodeTable)
              if nStates > 0
                smNodeToFlatSMGroup = HashTableCG.emptyHashTable()
                if DEBUG_SMDUMP
                  print("***** InstStateMachineUtil.createSMNodeToFlatSMGroupTable: START ***** \\n")
                end
                if DEBUG_SMDUMP
                  print("***** SMNode machine node table: ***** \\n")
                end
                if DEBUG_SMDUMP
                  BaseHashTable.dumpHashTable(smNodeTable)
                end
                if DEBUG_SMDUMP
                  print("***** Incidence Matrix: ***** \\n")
                end
                iTable = createIncidenceTable(smNodeTable, nStates)
                if DEBUG_SMDUMP
                  printIncidenceTable(iTable, nStates)
                end
                if DEBUG_SMDUMP
                  print("***** Transitive Closure: ***** \\n")
                end
                transClosure = transitiveClosure(iTable, nStates)
                if DEBUG_SMDUMP
                  printIncidenceTable(transClosure, nStates)
                end
                if DEBUG_SMDUMP
                  print("***** Initial States: ***** \\n")
                end
                initialStates = extractInitialStates(smNodeTable)
                if DEBUG_SMDUMP
                  print(stringDelimitList(ListUtil.map(initialStates, ComponentReference.printComponentRefStr), ", ") + "\\n")
                end
                if DEBUG_SMDUMP
                  print("***** Flat SMNode Machine Groups: ***** \\n")
                end
                flatSMGroup = extractFlatSMGroup(initialStates, transClosure, nStates)
                if DEBUG_SMDUMP
                  print(stringDelimitList(ListUtil.map(flatSMGroup, dumpFlatSMGroupStr), "\\n") + "\\n")
                end
                if DEBUG_SMDUMP
                  print("***** SM Node cref to SM Group cref mapping: ***** \\n")
                end
                smNodeToFlatSMGroup = ListUtil.fold(flatSMGroup, relateNodesToGroup, smNodeToFlatSMGroup)
                if DEBUG_SMDUMP
                  BaseHashTable.dumpHashTable(smNodeToFlatSMGroup)
                end
                if DEBUG_SMDUMP
                  print("***** InstStateMachineUtil.createSMNodeToFlatSMGroupTable: END ***** \\n")
                end
              else
                smNodeToFlatSMGroup = HashTableCG.emptyHashTableSized(1)
              end
          smNodeToFlatSMGroup
        end

         #= 
        Author: BTH
        Wrap state machine components into corresponding flat state machine containers.
         =#
        function wrapSMCompsInFlatSMs(inIH::InnerOuterTypes.InstHierarchy, inDae1::DAE.DAElist, inDae2::DAE.DAElist, smNodeToFlatSMGroup::SMNodeToFlatSMGroupTable, smInitialCrefs::List{<:DAE.ComponentRef} #= every smInitialCrefs corresponds to a flat state machine group =#) ::Tuple{DAE.DAElist, DAE.DAElist} 
              local outDae2::DAE.DAElist
              local outDae1::DAE.DAElist

              local elementLst1::List{DAE.Element}
              local elementLst2::List{DAE.Element}
              local smCompsLst::List{DAE.Element}
              local otherLst1::List{DAE.Element}
              local otherLst2::List{DAE.Element}
              local smTransitionsLst::List{DAE.Element}
              local flatSmLst::List{DAE.Element}
              local flatSMsAndMergingEqns::List{DAE.Element}

               #= print(\"InstStateMachineUtil.wrapSMCompsInFlatSMs: smInitialCrefs: \" + stringDelimitList(List.map(smInitialCrefs, ComponentReference.crefStr), \",\") + \"\\n\");
               =#
               #= print(\"InstStateMachineUtil.wrapSMCompsInFlatSMs: smNodeToFlatSMGroup:\\n\"); BaseHashTable.dumpHashTable(smNodeToFlatSMGroup);
               =#
              @match DAE.DAE_LIST(elementLst = elementLst1) = inDae1
               #=  extract SM_COMPs
               =#
              (smCompsLst, otherLst1) = ListUtil.extractOnTrue(elementLst1, isSMComp)
              @match DAE.DAE_LIST(elementLst = elementLst2) = inDae2
               #=  extract transition and initialState statements
               =#
              (smTransitionsLst, otherLst2) = ListUtil.extractOnTrue(elementLst2, isSMStatement2)
               #=  Create list of FLAT_SM(..). Every FLAT_SM contains the components that constitute that flat state machine
               =#
               #= flatSmLst := List.map2(smInitialCrefs, createFlatSM, smCompsLst, smNodeToFlatSMGroup);
               =#
              flatSmLst = ListUtil.map2(smInitialCrefs, createFlatSM, listAppend(smCompsLst, smTransitionsLst), smNodeToFlatSMGroup)
               #=  myMerge variable definitions in flat state machine and create elements list containing FLAT_SMs and merging equations
               =#
              flatSMsAndMergingEqns = ListUtil.fold1(flatSmLst, mergeVariableDefinitions, inIH, nil)
              outDae1 = DAE.DAE_LIST(listAppend(flatSMsAndMergingEqns, otherLst1))
              outDae2 = DAE.DAE_LIST(otherLst2)
          (outDae1, outDae2)
        end

         #= 
        Author: BTH
        Create fresh equations for merging outer output variable definitions
         =#
        function myMergeVariableDefinitions(inFlatSM::DAE.Element, inIH::InnerOuterTypes.InstHierarchy, inStartElementLst::List{<:DAE.Element}) ::List{DAE.Element} 
              local outElementLst::List{DAE.Element}

              local outerOutputCrefToSMCompCref::HashTableCG.HashTable #= Table to map outer outputs to corresponding state =#
              local outerOutputCrefToInnerCref::HashTableCG.HashTable #= Table to map outer output to corresponding inners =#
              local innerCrefToOuterOutputCrefs::HashTable3.HashTable #= Kind of \\\"inverse\\\" of  outerOutputCrefToInnerCref =#
              local hashEntries_outerOutputCrefToInnerCref::List{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
              local innerCrefToOuterOutputCrefs_der::List{Tuple{DAE.ComponentRef, List{DAE.ComponentRef}}} = nil #= Extracted part in which at least one of the output crefs appears in a der(..) =#
              local innerCrefToOuterOutputCrefs_nonDer::List{Tuple{DAE.ComponentRef, List{DAE.ComponentRef}}} = nil #= The non-der(..) rest =#
              local uniqueHashValues::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef}
              local derCrefsAcc::List{DAE.ComponentRef} = nil
              local outerOutputCrefs::List{DAE.ComponentRef}
              local derCrefsSet::HashSet.HashSetType
              local emptyTree::DAE.FunctionTree
              local dAElistNew::List{DAE.Element}
              local myMergeEqns::List{DAE.Element}
              local myMergeEqns_der::List{DAE.Element}
              local aliasEqns_der::List{DAE.Element}
              local nOfHits::ModelicaInteger
              local hasDer::Bool
               #=  FLAT_SM
               =#
              local ident::DAE.Ident
              local dAElist::List{DAE.Element} #= The states/modes within the the flat state machine =#

              @match DAE.FLAT_SM(ident = ident, dAElist = dAElist) = inFlatSM
               #=  Create table that maps outer outputs to corresponding state
               =#
              outerOutputCrefToSMCompCref = ListUtil.fold(dAElist, collectOuterOutputs, HashTableCG.emptyHashTable())
               #=  print(\"InstStateMachineUtil.myMergeVariableDefinitions OuterToSTATE:\\n\"); BaseHashTable.dumpHashTable(outerOutputCrefToSMCompCref);
               =#
               #=  Create table that maps outer outputs crefs to corresponding inner crefs
               =#
              outerOutputCrefToInnerCref = ListUtil.fold1(BaseHashTable.hashTableKeyList(outerOutputCrefToSMCompCref), matchOuterWithInner, inIH, HashTableCG.emptyHashTable())
               #=  print(\"InstStateMachineUtil.myMergeVariableDefinitions OuterToINNER:\\n\"); BaseHashTable.dumpHashTable(outerOutputCrefToInnerCref);
               =#
               #=  Create table that maps inner crefs from above to a list of corresponding outer crefs
               =#
              hashEntries_outerOutputCrefToInnerCref = BaseHashTable.hashTableList(outerOutputCrefToInnerCref)
              uniqueHashValues = ListUtil.unique(BaseHashTable.hashTableValueList(outerOutputCrefToInnerCref))
               #=  print(\"InstStateMachineUtil.myMergeVariableDefinitions uniqueHashValues: (\" + stringDelimitList(List.map(uniqueHashValues, ComponentReference.crefStr), \",\") + \")\\n\");
               =#
              innerCrefToOuterOutputCrefs = ListUtil.fold1(uniqueHashValues, collectCorrespondingKeys, hashEntries_outerOutputCrefToInnerCref, HashTable3.emptyHashTable())
               #=  print(\"InstStateMachineUtil.myMergeVariableDefinitions: innerCrefToOuterOutputCrefs:\\n\"); BaseHashTable.dumpHashTable(innerCrefToOuterOutputCrefs);
               =#
               #=  Substitute occurrences of previous(outerCref) by previous(innerCref)
               =#
              emptyTree = DAE.AvlTreePathFunction.Tree.EMPTY()
              @match (DAE.DAE_LIST(dAElist), _, _) = DAEUtil.traverseDAE(DAE.DAE_LIST(dAElist), emptyTree, traverserHelperSubsOuterByInnerExp, outerOutputCrefToInnerCref)
              if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                crefs = BaseHashTable.hashTableKeyList(outerOutputCrefToSMCompCref)
                for cref in crefs
                  nOfHits = 0
                  (_, _, (_, (_, nOfHits))) = DAEUtil.traverseDAE(DAE.DAE_LIST(dAElist), emptyTree, Expression.traverseSubexpressionsHelper, (traversingCountDer, (cref, 0)))
                  if nOfHits > 0
                    derCrefsAcc = _cons(cref, derCrefsAcc)
                  end
                end
                derCrefsSet = HashSet.emptyHashSetSized(listLength(derCrefsAcc))
                derCrefsSet = ListUtil.fold(derCrefsAcc, BaseHashSet.add, derCrefsSet)
                for hashEntry in BaseHashTable.hashTableList(innerCrefToOuterOutputCrefs)
                  (_, outerOutputCrefs) = hashEntry
                  hasDer = ListUtil.exist(outerOutputCrefs, (derCrefsSet) -> BaseHashSet.has(hashSet = derCrefsSet))
                  if hasDer
                    innerCrefToOuterOutputCrefs_der = _cons(hashEntry, innerCrefToOuterOutputCrefs_der)
                  else
                    innerCrefToOuterOutputCrefs_nonDer = _cons(hashEntry, innerCrefToOuterOutputCrefs_nonDer)
                  end
                end
                aliasEqns_der = ListUtil.flatten(ListUtil.map(innerCrefToOuterOutputCrefs_der, freshAliasEqn_der))
                myMergeEqns_der = listAppend(ListUtil.map(innerCrefToOuterOutputCrefs_der, freshMergingEqn_der), aliasEqns_der)
                myMergeEqns = listAppend(ListUtil.map(innerCrefToOuterOutputCrefs_nonDer, freshMergingEqn), myMergeEqns_der)
              else
                myMergeEqns = ListUtil.map(BaseHashTable.hashTableList(innerCrefToOuterOutputCrefs), freshMergingEqn)
              end
               #=  == HACK Let's deal with continuous-time ==
               =#
               #=  traverse dae expressions and search for der(cref) occurances
               =#
               #=  print(\"InstStateMachineUtil.myMergeVariableDefinitions derCrefsAcc:\\n\" + stringDelimitList(List.map(derCrefsAcc, ComponentReference.crefStr), \", \") + \"\\n\");
               =#
               #=  Split the mapping from inner crefs to outer output crefs in a \"continuous\" part and the rest
               =#
               #=  Create aliases between inner and outer of 'der' entries, e.g., a tuple (x -> {a.x, b.x}) will be transformed to alias equations {x = a.x, x = b.x}
               =#
               #=  Create merging equations for 'der' entries
               =#
               #=  Create merging equations for 'nonDer' entries
               =#
               #=  FIXME add support for outers that don't have \"inner outer\" or \"inner\" at closest instance level (requires to introduce a fresh intermediate variable)
               =#
               #=  add processed flat state machine and corresponding merging equations to the dae element list
               =#
               #= outElementLst := listAppend(outElementLst, {DAE.FLAT_SM(ident=ident, dAElist=listAppend(dAElist, myMergeEqns))});  put myMerge equations in FLAT_SM element
               =#
              outElementLst = listAppend(inStartElementLst, _cons(DAE.FLAT_SM(ident = ident, dAElist = dAElist), myMergeEqns))
               #=  put equations after FLAT_SM element
               =#
          outElementLst
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinition.
        Create a fresh alias equation between inners and their corresponding outer output variable defintions
         =#
        function freshAliasEqn_der(inInnerCrefToOuterOutputCrefs::Tuple{<:DAE.ComponentRef, List{<:DAE.ComponentRef}} #= tuple relating the inner cref to respective outer crefs =#) ::List{DAE.Element} 
              local outEqns::List{DAE.Element}

              local innerCref::DAE.ComponentRef
              local outerCrefs::List{DAE.ComponentRef}
              local ty::DAE.Type

              (innerCref, outerCrefs) = inInnerCrefToOuterOutputCrefs
               #=  FIXME use instead 'ty := ComponentReference.crefTypeConsiderSubs(innerCref);'?
               =#
              ty = ComponentReference.crefLastType(innerCref)
               #=  Alias equations
               =#
              outEqns = list(DAE.EQUATION(DAE.CREF(innerCref, ty), DAE.CREF(outerCref, ty), DAE.emptyElementSource) for outerCref in outerCrefs)
          outEqns
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinition.
        Create a fresh equation for merging outer output variable defintions of equations involving der(..)
         =#
        function freshMergingEqn_der(inInnerCrefToOuterOutputCrefs::Tuple{<:DAE.ComponentRef, List{<:DAE.ComponentRef}} #= tuple relating the inner cref to respective outer crefs =#) ::DAE.Element 
              local outEqn::DAE.Element

              local innerCref::DAE.ComponentRef
              local outerCrefs::List{DAE.ComponentRef}
              local outerCrefsStripped::List{DAE.ComponentRef}
              local outerCrefDers::List{DAE.ComponentRef}
              local ty::DAE.Type
              local exp::DAE.Exp

              (innerCref, outerCrefs) = inInnerCrefToOuterOutputCrefs
               #=  FIXME use instead 'ty := ComponentReference.crefTypeConsiderSubs(innerCref);'?
               =#
              ty = ComponentReference.crefLastType(innerCref)
              outerCrefsStripped = ListUtil.map(outerCrefs, ComponentReference.crefStripLastIdent)
               #=  FIXME this variables are generated in StateMachineFlatten.addStateActivationAndReset(..) which is UGLY
               =#
              outerCrefDers = ListUtil.map(outerCrefs, fn -> ComponentReference.appendStringLastIdent(inString = "_der\$"))
               #=  der(x)
               =#
              exp = DAE.CALL(Absyn.IDENT("der"), list(DAE.CREF(innerCref, ty)), DAE.callAttrBuiltinReal)
               #=  der(x) = ...
               =#
              outEqn = DAE.EQUATION(exp, mergingRhs_der(outerCrefDers, innerCref, ty), DAE.emptyElementSource)
          outEqn
        end

         #= 
        Author: BTH
        Helper function to freshMergingEqn_der.
        Create RHS expression of merging equation.
         =#
        function mergingRhs_der(inOuterCrefs::List{<:DAE.ComponentRef} #= List of the crefs of the outer variables =#, inInnerCref::DAE.ComponentRef, ty::DAE.Type #= type of inner cref (inner cref type expected to the same as outer crefs type) =#) ::DAE.Exp 
              local res::DAE.Exp

              local callAttributes::DAE.CallAttributes = DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())

              res = begin
                  local outerCref::DAE.ComponentRef
                  local crefState::DAE.ComponentRef
                  local rest::List{DAE.ComponentRef}
                  local outerCrefExp::DAE.Exp
                  local innerCrefExp::DAE.Exp
                  local crefStateExp::DAE.Exp
                  local ifExp::DAE.Exp
                  local expCond::DAE.Exp
                  local expElse::DAE.Exp
                @match inOuterCrefs begin
                  outerCref <|  nil()  => begin
                      outerCrefExp = DAE.CREF(outerCref, ty)
                      crefState = ComponentReference.crefStripLastIdent(outerCref)
                      crefStateExp = DAE.CREF(crefState, ty)
                      expCond = DAE.CALL(Absyn.IDENT("activeState"), list(crefStateExp), callAttributes)
                      expElse = DAE.RCONST(0)
                      ifExp = DAE.IFEXP(expCond, outerCrefExp, expElse)
                    ifExp
                  end
                  
                  outerCref <| rest  => begin
                      outerCrefExp = DAE.CREF(outerCref, ty)
                      crefState = ComponentReference.crefStripLastIdent(outerCref)
                      crefStateExp = DAE.CREF(crefState, ty)
                      expCond = DAE.CALL(Absyn.IDENT("activeState"), list(crefStateExp), callAttributes)
                      expElse = mergingRhs_der(rest, inInnerCref, ty)
                      ifExp = DAE.IFEXP(expCond, outerCrefExp, expElse)
                    ifExp
                  end
                end
              end
          res
        end

         #= 
        Author: BTH
        Helper function to traverse subexpressions
        Counts occurances of 'der(cref)'
         =#
        function traversingCountDer(inExp::DAE.Exp, inCref_HitCount::Tuple{<:DAE.ComponentRef, ModelicaInteger} #= tuple of x and counter for hits of der(x) =#) ::Tuple{DAE.Exp, Tuple{DAE.ComponentRef, ModelicaInteger}} 
              local outCref_HitCount::Tuple{DAE.ComponentRef, ModelicaInteger}
              local outExp::DAE.Exp

              local cref::DAE.ComponentRef
              local hitCount::ModelicaInteger

              (cref, hitCount) = inCref_HitCount
              (outExp, outCref_HitCount) = begin
                  local componentRef::DAE.ComponentRef
                  local expLst::List{DAE.Exp}
                  local attr::DAE.CallAttributes
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT("der"), expLst = DAE.CREF(componentRef = componentRef) <|  nil()) where (ComponentReference.crefEqual(componentRef, cref))  => begin
                    (inExp, (cref, hitCount + 1))
                  end
                  
                  _  => begin
                      (inExp, inCref_HitCount)
                  end
                end
              end
          (outExp, outCref_HitCount)
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinition.
        Create a fresh equation for merging outer output variable defintions
         =#
        function freshMergingEqn(inInnerCrefToOuterOutputCrefs::Tuple{<:DAE.ComponentRef, List{<:DAE.ComponentRef}} #= tuple relating the inner cref to respective outer crefs =#) ::DAE.Element 
              local outEqn::DAE.Element

              local innerCref::DAE.ComponentRef
              local outerCrefs::List{DAE.ComponentRef}
              local outerCrefsStripped::List{DAE.ComponentRef}
              local ty::DAE.Type

              (innerCref, outerCrefs) = inInnerCrefToOuterOutputCrefs
               #=  FIXME BTH use instead 'ty := ComponentReference.crefTypeConsiderSubs(innerCref);'?
               =#
              ty = ComponentReference.crefLastType(innerCref)
              outerCrefsStripped = ListUtil.map(outerCrefs, ComponentReference.crefStripLastIdent)
              outEqn = DAE.EQUATION(DAE.CREF(innerCref, ty), mergingRhs(outerCrefs, innerCref, ty), DAE.emptyElementSource)
          outEqn
        end

         #= 
        Author: BTH
        Helper function to freshMergingEqn.
        Create RHS expression of merging equation.
         =#
        function mergingRhs(inOuterCrefs::List{<:DAE.ComponentRef} #= List of the crefs of the outer variables =#, inInnerCref::DAE.ComponentRef, ty::DAE.Type #= type of inner cref (inner cref type expected to the same as outer crefs type) =#) ::DAE.Exp 
              local res::DAE.Exp

              local callAttributes::DAE.CallAttributes = DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())

              res = begin
                  local outerCref::DAE.ComponentRef
                  local crefState::DAE.ComponentRef
                  local rest::List{DAE.ComponentRef}
                  local outerCrefExp::DAE.Exp
                  local innerCrefExp::DAE.Exp
                  local crefStateExp::DAE.Exp
                  local ifExp::DAE.Exp
                  local expCond::DAE.Exp
                  local expElse::DAE.Exp
                @match inOuterCrefs begin
                  outerCref <|  nil()  => begin
                      outerCrefExp = DAE.CREF(outerCref, ty)
                      innerCrefExp = DAE.CREF(inInnerCref, ty)
                      crefState = ComponentReference.crefStripLastIdent(outerCref)
                      crefStateExp = DAE.CREF(crefState, ty)
                      expCond = DAE.CALL(Absyn.IDENT("activeState"), list(crefStateExp), callAttributes)
                      expElse = DAE.CALL(Absyn.IDENT("previous"), list(innerCrefExp), callAttributes)
                      ifExp = DAE.IFEXP(expCond, outerCrefExp, expElse)
                    ifExp
                  end
                  
                  outerCref <| rest  => begin
                      outerCrefExp = DAE.CREF(outerCref, ty)
                      crefState = ComponentReference.crefStripLastIdent(outerCref)
                      crefStateExp = DAE.CREF(crefState, ty)
                      expCond = DAE.CALL(Absyn.IDENT("activeState"), list(crefStateExp), callAttributes)
                      expElse = mergingRhs(rest, inInnerCref, ty)
                      ifExp = DAE.IFEXP(expCond, outerCrefExp, expElse)
                    ifExp
                  end
                end
              end
          res
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinitions =#
        function collectCorrespondingKeys(inInnerCref::DAE.ComponentRef, inHashEntries::List{<:Tuple{<:DAE.ComponentRef, DAE.ComponentRef}}, inInnerCrefToOuterOutputCrefs::HashTable3.HashTable) ::HashTable3.HashTable 
              local outInnerCrefToOuterOutputCrefs::HashTable3.HashTable = inInnerCrefToOuterOutputCrefs

              local outerRefs::List{DAE.ComponentRef}

              outerRefs = ListUtil.filterMap1(inHashEntries, crefEqualTuple22, inInnerCref)
              outInnerCrefToOuterOutputCrefs = BaseHashTable.addUnique((inInnerCref, outerRefs), outInnerCrefToOuterOutputCrefs)
          outInnerCrefToOuterOutputCrefs
        end

         #= 
        Helper function to collect collectCorrespondingKeys =#
        function crefEqualTuple22(inHashEntry::Tuple{<:DAE.ComponentRef, DAE.ComponentRef}, inCref::DAE.ComponentRef) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              local isEqual::Bool
              local tuple22::DAE.ComponentRef

              tuple22 = Util.tuple22(inHashEntry)
              isEqual = ComponentReference.crefEqual(tuple22, inCref)
              if ! isEqual
                fail()
              end
              outCref = Util.tuple21(inHashEntry)
          outCref
        end

         #= 
        Author: BTH
        Substitute outer variables in previous(x) by corresponding 'inner'.
        Helper function to myMergeVariableDefinitions =#
        function traverserHelperSubsOuterByInnerExp(inExp::DAE.Exp, inOuterToInner::HashTableCG.HashTable) ::Tuple{DAE.Exp, HashTableCG.HashTable} 
              local outOuterToInner::HashTableCG.HashTable
              local outExp::DAE.Exp

              (outExp, outOuterToInner) = Expression.traverseExpBottomUp(inExp, traverserHelperSubsOuterByInner, inOuterToInner)
          (outExp, outOuterToInner)
        end

         #= 
        Author: BTH
        Helper function to traverserHelperSubsOuterByInnerExp =#
        function traverserHelperSubsOuterByInner(inExp::DAE.Exp, inOuterToInner::HashTableCG.HashTable) ::Tuple{DAE.Exp, HashTableCG.HashTable} 
              local outOuterToInner::HashTableCG.HashTable
              local outExp::DAE.Exp

              (outExp, outOuterToInner) = begin
                  local componentRef::DAE.ComponentRef
                  local ty::DAE.Type
                  local attr::DAE.CallAttributes
                   #=  Substitute outer variables in previous(x) by corresponding 'inner:
                   =#
                @match inExp begin
                  DAE.CALL(Absyn.IDENT("previous"), DAE.CREF(componentRef, ty) <|  nil(), attr) where (BaseHashTable.hasKey(componentRef, inOuterToInner))  => begin
                    (DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(BaseHashTable.get(componentRef, inOuterToInner), ty)), attr), inOuterToInner)
                  end
                  
                  _  => begin
                      (inExp, inOuterToInner)
                  end
                end
              end
          (outExp, outOuterToInner)
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinitions
         =#
        function matchOuterWithInner(inOuterCref::DAE.ComponentRef, inIH::InnerOuterTypes.InstHierarchy, inOuterCrefToInnerCref::HashTableCG.HashTable) ::HashTableCG.HashTable 
              local outOuterCrefToInnerCref::HashTableCG.HashTable = inOuterCrefToInnerCref

              local crefIdent::DAE.ComponentRef
              local crefFound::DAE.ComponentRef
              local strippedCref1::DAE.ComponentRef
              local strippedCref2::DAE.ComponentRef

              crefIdent = ComponentReference.crefLastCref(inOuterCref)
               #=  inOuterCref is supposed to be \"outer\" or \"inner outer\" and we want to move one level up the instance hierachy for starting the search for the corresponding inner
               =#
              strippedCref1 = ComponentReference.crefStripLastIdent(inOuterCref)
               #=  Go up one instance level, append identifier and try again. If already at top level, try to find identifier at top level
               =#
              strippedCref2 = if ComponentReference.crefDepth(strippedCref1) >= 2
                    ComponentReference.joinCrefs(ComponentReference.crefStripLastIdent(strippedCref1), crefIdent)
                  else
                    crefIdent
                  end
               #=  now use strippedCref2 for starting the search in the instance hierarchy
               =#
              crefFound = findInner(strippedCref2, crefIdent, inIH)
              outOuterCrefToInnerCref = BaseHashTable.addUnique((inOuterCref, crefFound), outOuterCrefToInnerCref)
          outOuterCrefToInnerCref
        end

         #= 
        Author: BTH
        Helper function to matchOuterWithInner
         =#
        function findInner(inCrefTest::DAE.ComponentRef, inCrefIdent::DAE.ComponentRef, inIH::InnerOuterTypes.InstHierarchy) ::DAE.ComponentRef 
              local outCrefFound::DAE.ComponentRef

              local testCref::DAE.ComponentRef
              local strippedCref1::DAE.ComponentRef
              local strippedCref2::DAE.ComponentRef
              local ht::InnerOuter.InstHierarchyHashTable

              @match InnerOuter.TOP_INSTANCE(ht = ht) = listHead(inIH)
              try
                _ = InnerOuter.get(inCrefTest, ht)
                outCrefFound = inCrefTest
              catch
                strippedCref1 = ComponentReference.crefStripLastIdent(inCrefTest)
                strippedCref2 = if ComponentReference.crefDepth(strippedCref1) >= 2
                      ComponentReference.joinCrefs(ComponentReference.crefStripLastIdent(strippedCref1), inCrefIdent)
                    else
                      inCrefIdent
                    end
                outCrefFound = findInner(strippedCref2, inCrefIdent, inIH)
              end
               #=  Go up one instance level, append identifier and try again. If already at top level, try to find identifier at top level
               =#
          outCrefFound
        end

         #= 
        Author: BTH
        Helper function to myMergeVariableDefinitions.
         =#
        function collectOuterOutputs(inElem::DAE.Element, inOuterAcc::HashTableCG.HashTable) ::HashTableCG.HashTable 
              local outOuterAcc::HashTableCG.HashTable = inOuterAcc

              local outerOutputs::List{DAE.Element}
              local outerOutputCrefs::List{DAE.ComponentRef}
              local outerOutputCrefToSMCompCref::List{Tuple{HashTableCG.Key, HashTableCG.Value}}
               #=  SM_COMP
               =#
              local componentRef::DAE.ComponentRef
              local dAElist::List{DAE.Element} #= a component with subelements =#

              outOuterAcc = begin
                @match inElem begin
                  DAE.SM_COMP(componentRef = componentRef, dAElist = dAElist)  => begin
                      outerOutputs = ListUtil.filterOnTrue(dAElist, isOuterOutput)
                      outerOutputCrefs = ListUtil.map(outerOutputs, DAEUtil.varCref)
                      outerOutputCrefToSMCompCref = ListUtil.map(outerOutputCrefs, (componentRef) -> Util.makeTuple(inValue2 = componentRef))
                    ListUtil.fold(outerOutputCrefToSMCompCref, BaseHashTable.addUnique, outOuterAcc)
                  end
                  
                  _  => begin
                      inOuterAcc
                  end
                end
              end
          outOuterAcc
        end

         #= 
        Author: BTH
        Helper function to collectOuterOutputs.
         =#
        function isOuterOutput(inElem::DAE.Element) ::Bool 
              local outB::Bool

              outB = begin
                  local direction::DAE.VarDirection
                  local innerOuter::Absyn.InnerOuter
                @match inElem begin
                  DAE.VAR(direction = DAE.OUTPUT(__), innerOuter = Absyn.OUTER(__))  => begin
                    true
                  end
                  
                  DAE.VAR(direction = DAE.OUTPUT(__), innerOuter = Absyn.INNER_OUTER(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outB
        end

         #= 
        Author: BTH
        Helper function to wrapSMCompsInFlatSMs.
         =#
        function createFlatSM(smInitialCref::DAE.ComponentRef, smElemsLst::List{<:DAE.Element}, smNodeToFlatSMGroup::SMNodeToFlatSMGroupTable) ::DAE.Element 
              local flatSM::DAE.Element

              local smElemsInFlatSM::List{DAE.Element}

              smElemsInFlatSM = ListUtil.filter2OnTrue(smElemsLst, isInFlatSM, smInitialCref, smNodeToFlatSMGroup)
              flatSM = DAE.FLAT_SM(ComponentReference.printComponentRefStr(smInitialCref), smElemsInFlatSM)
          flatSM
        end

         #= 
        Author: BTH
        Check if SM_COMP, transition or initialState (first argument) is part of the flat state machine which corresponds to smInitialCref.
         =#
        function isInFlatSM(inElement::DAE.Element, smInitialCref::DAE.ComponentRef, smNodeToFlatSMGroup::SMNodeToFlatSMGroupTable #= Table which maps the cref of an SM_COMP to the cref of its corresponding flat state machine group =#) ::Bool 
              local outResult::Bool

              local crefCorrespondingFlatSMGroup::DAE.ComponentRef

              crefCorrespondingFlatSMGroup = begin
                  local cref1::DAE.ComponentRef
                @match inElement begin
                  DAE.SM_COMP(componentRef = cref1) where (BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup))  => begin
                    BaseHashTable.get(cref1, smNodeToFlatSMGroup)
                  end
                  
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("transition"), expLst = DAE.CREF(componentRef = cref1) <| _)) where (BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup))  => begin
                    BaseHashTable.get(cref1, smNodeToFlatSMGroup)
                  end
                  
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("initialState"), expLst = DAE.CREF(componentRef = cref1) <|  nil())) where (BaseHashTable.hasKey(cref1, smNodeToFlatSMGroup))  => begin
                    BaseHashTable.get(cref1, smNodeToFlatSMGroup)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- InstStateMachineUtil.isInFlatSM failed: Hash table lookup failed for " + DAEDump.dumpElementsStr(list(inElement)))
                        BaseHashTable.dumpHashTableStatistics(smNodeToFlatSMGroup)
                      fail()
                  end
                end
              end
               #=  Note that it suffices to check for the \"from\" state, since the \"to\" state must be in the same FlatSMGroup
               =#
              outResult = if ComponentReference.crefEqual(crefCorrespondingFlatSMGroup, smInitialCref)
                    true
                  else
                    false
                  end
          outResult
        end

         #= 
        Author: BTH
        Check if element is a SM_COMP.
         =#
        function isSMComp(inElement::DAE.Element) ::Bool 
              local outResult::Bool

              outResult = begin
                @match inElement begin
                  DAE.SM_COMP(_, _)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outResult
        end

         #= 
        Author: BTH
        Relate crefs of SMNodes with cref of the FlatSMGroup that it belongs to.
         =#
        function relateNodesToGroup(flatSMGroup::FlatSMGroup, inNodeToGroup::SMNodeToFlatSMGroupTable) ::SMNodeToFlatSMGroupTable 
              local outNodeToGroup::SMNodeToFlatSMGroupTable = inNodeToGroup

              local nodeGroup::Array{Tuple{DAE.ComponentRef, DAE.ComponentRef}}
               #=  FLAT_SM_GROUP
               =#
              local initState::DAE.ComponentRef
              local states::Array{DAE.ComponentRef}

              @match FLAT_SM_GROUP(initState, states) = flatSMGroup
              nodeGroup = ArrayUtil.map(states, (initState) -> Util.makeTuple(inValue2 = initState))
              outNodeToGroup = ArrayUtil.fold(nodeGroup, BaseHashTable.add, outNodeToGroup)
          outNodeToGroup
        end

         #= 
        Author: BTH
        For each initial state extract the (flat) state machine group that is defined by the
        transitive closure associated with that initial state. =#
        function extractFlatSMGroup(initialStates::List{<:DAE.ComponentRef}, iTable::IncidenceTable, nStates::ModelicaInteger #= Number of states =#) ::List{FlatSMGroup} 
              local flatSMGroup::List{FlatSMGroup}

              local cref2index::HashTable.HashTableType
              local incidence::Bool[nStates, nStates]
              local entries::List{Tuple{DAE.ComponentRef, ModelicaInteger}}
              local i2cref::Array{DAE.ComponentRef}
              local cref::DAE.ComponentRef
              local members::List{DAE.ComponentRef}
              local membersArr::Array{DAE.ComponentRef}
              local memberSet::HashSet.HashSetType
              local n::ModelicaInteger
              local i::ModelicaInteger
              local j::ModelicaInteger

              @match INCIDENCE_TABLE(cref2index, incidence) = iTable
              n = BaseHashTable.hashTableCurrentSize(cref2index)
               #=  sanity check:
               =#
              assert(n == nStates, "Value of nStates needs to be equal to number of modes within state table argument.")
              entries = BaseHashTable.hashTableList(cref2index)
              entries = ListUtil.sort(entries, crefIndexCmp)
               #= i2cref := arrayCreate(n, ComponentReference.makeDummyCref());
               =#
              i2cref = listArray(ListUtil.map(entries, Util.tuple21))
              flatSMGroup = nil
              for cref in initialStates
                i = BaseHashTable.get(cref, cref2index)
                members = nil
                for j in 1:n
                  if incidence[i, j]
                    members = _cons(i2cref[j], members)
                  end
                end
                memberSet = HashSet.emptyHashSetSized(listLength(members))
                memberSet = ListUtil.fold(members, BaseHashSet.add, memberSet)
                memberSet = BaseHashSet.delete(cref, memberSet)
                membersArr = listArray(_cons(cref, BaseHashSet.hashSetList(memberSet)))
                flatSMGroup = _cons(FLAT_SM_GROUP(cref, membersArr), flatSMGroup)
              end
               #=  Ensure uniquenes of entries
               =#
               #=  Ensure that initialState comes first in array
               =#
          flatSMGroup
        end

         #= 
        Author: BTH
        Dump flat state machine group to string =#
        function dumpFlatSMGroupStr(flatA::FlatSMGroup) ::String 
              local flatStr::String

              local crefs::List{DAE.ComponentRef}
              local initialStateStr::String
              local statesStr::String
              local statesStrs::List{String}
               #=  FLAT_SM_GROUP fields
               =#
              local initState::DAE.ComponentRef
              local states::Array{DAE.ComponentRef}

              @match FLAT_SM_GROUP(initState = initState, states = states) = flatA
              initialStateStr = ComponentReference.printComponentRefStr(initState)
              crefs = arrayList(states)
              statesStrs = ListUtil.map(crefs, ComponentReference.printComponentRefStr)
              statesStr = stringDelimitList(statesStrs, ", ")
              flatStr = initialStateStr + "( states(" + statesStr + "))"
          flatStr
        end

         #= 
        Author: BTH
        Return crefs of states declared as 'initialState'.  =#
        function extractInitialStates(smNodeTable::SMNodeTable) ::List{DAE.ComponentRef} 
              local initialStates::List{DAE.ComponentRef}

              local entries::List{Tuple{DAE.ComponentRef, SMNode}}
              local e::Tuple{DAE.ComponentRef, SMNode}
              local cref::DAE.ComponentRef
              local smNode::SMNode
              local isInitial::Bool

              entries = BaseHashTable.hashTableList(smNodeTable)
              initialStates = nil
              for e in entries
                (cref, smNode) = e
                @match SMNODE(isInitial = isInitial) = smNode
                if isInitial
                  initialStates = _cons(cref, initialStates)
                end
              end
          initialStates
        end

         #= 
        Author: BTH
        Compute the transitive closure over the transition relation between states.
        This allows to group states that are part of the same (flat) state machine.
        The function uses the Warshall's algorithm for that task, c.f.
        http:en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
        or the more succinct (and potentially more readable) description
        http:de.wikipedia.org/wiki/Warshall-Algorithmus
         =#
        function transitiveClosure(iTable::IncidenceTable, nStates::ModelicaInteger #= Number of states =#) ::IncidenceTable 
              local transClosure::IncidenceTable

              local cref2index::HashTable.HashTableType
              local incidence::Bool[nStates, nStates]
              local n::ModelicaInteger
              local k::ModelicaInteger
              local i::ModelicaInteger
              local j::ModelicaInteger
              local c::Bool

              @match INCIDENCE_TABLE(cref2index, incidence) = iTable
              n = BaseHashTable.hashTableCurrentSize(cref2index)
               #=  sanity check:
               =#
              assert(n == nStates, "Value of nStates needs to be equal to number of states within state table argument.")
               #=  Warshall's algorithm for computing the transitive closure
               =#
              for k in 1:n
                for i in 1:n
                  if incidence[i, k]
                    for j in 1:n
                      if incidence[k, j]
                        incidence[i, j] = true
                      end
                    end
                  end
                end
              end
              transClosure = INCIDENCE_TABLE(cref2index, incidence)
          transClosure
        end

         #= 
        Author: BTH
        Create incidence table showing which modes are connected by transitions. =#
        function createIncidenceTable(smNodes::SMNodeTable, nStates::ModelicaInteger #= Number of states =#) ::IncidenceTable 
              local iTable::IncidenceTable

              local cref2index::HashTable.HashTableType #= Map cref to corresponding index in incidence matrix =#
              local incidence::Bool[nStates, nStates] #= Incidence matrix showing which states are connected by transitions =#
              local iRow::Array{Bool}
              local n::ModelicaInteger
              local m::ModelicaInteger
              local i::ModelicaInteger
              local j::ModelicaInteger
              local k::ModelicaInteger
              local cref::DAE.ComponentRef
              local edges::HashSet.HashSetType
              local crefs1::Array{DAE.ComponentRef}
              local crefs2::Array{DAE.ComponentRef}

              crefs1 = listArray(BaseHashTable.hashTableKeyList(smNodes))
              n = arrayLength(crefs1)
              cref2index = HashTable.emptyHashTableSized(n)
              assert(n == nStates, "Value of nStates needs to be equal to number of modes within mode table argument.")
              incidence = fill(false, n, n)
              for i in 1:n
                cref2index = BaseHashTable.addNoUpdCheck((crefs1[i], i), cref2index)
              end
              for i in 1:n
                @match SMNODE(edges = edges) = BaseHashTable.get(crefs1[i], smNodes)
                crefs2 = listArray(BaseHashSet.hashSetList(edges))
                m = arrayLength(crefs2)
                for j in 1:m
                  cref = crefs2[j]
                  k = BaseHashTable.get(cref, cref2index)
                  incidence[i, k] = true
                end
              end
              iTable = INCIDENCE_TABLE(cref2index, incidence)
          iTable
        end

         #= 
        Author: BTH
        Print incidence table. =#
        function printIncidenceTable(iTable::IncidenceTable, nStates::ModelicaInteger #= Number of states =#)  
              local cref2index::HashTable.HashTableType
              local incidence::Bool[nStates, nStates]
              local entries::List{Tuple{DAE.ComponentRef, ModelicaInteger}}
              local entry::Tuple{DAE.ComponentRef, ModelicaInteger}
              local cref::DAE.ComponentRef
              local n::ModelicaInteger
              local i::ModelicaInteger
              local j::ModelicaInteger
              local padn::ModelicaInteger
              local row::Array{Bool}
              local str::String
              local pads::String
              local b::Bool

              @match INCIDENCE_TABLE(cref2index, incidence) = iTable
              entries = BaseHashTable.hashTableList(cref2index)
               #=  sanity check:
               =#
              n = listLength(entries)
              assert(n == nStates, "Value of nStates needs to be equal to number of modes within state table argument.")
              entries = ListUtil.sort(entries, crefIndexCmp)
              for entry in entries
                (cref, i) = entry
                print(ComponentReference.printComponentRefStr(cref) + ": " + intString(i) + "\\n")
              end
              pads = " "
              padn = 8
               #=  Print table header
               =#
              str = Util.stringPadRight("i", padn, pads)
              for i in 1:n
                str = str + Util.stringPadLeft(intString(i) + ",", padn, pads)
              end
              print(str + "\\n")
               #=  print incidence matrix rows
               =#
              for i in 1:n
                str = Util.stringPadRight(intString(i), padn, pads)
                for j in 1:n
                  b = incidence[i, j]
                  str = str + Util.stringPadLeft(boolString(b) + ",", padn, pads)
                end
                print(str + "\\n")
              end
        end

         #= 
        Author: BTH
        Compare the indices assigned to two crefs (helper function for sorting) =#
        function crefIndexCmp(inElement1::Tuple{<:DAE.ComponentRef, ModelicaInteger}, inElement2::Tuple{<:DAE.ComponentRef, ModelicaInteger}) ::Bool 
              local inRes::Bool

              local i1::ModelicaInteger
              local i2::ModelicaInteger

              (_, i1) = inElement1
              (_, i2) = inElement2
              inRes = i1 > i2
          inRes
        end

         #= 
        Author: BTH
        Traverse the equations, search for 'transition' and 'initialState' operators,
        extract the state arguments from them and collect them in the table. =#
        function getSMNodeTable(elementLst::List{<:DAE.Element}) ::SMNodeTable 
              local smNodeTable::SMNodeTable

              local elementLst2::List{DAE.Element}

              elementLst2 = list(e for e in elementLst if isSMStatement2(e))
              if ! listEmpty(elementLst2)
                smNodeTable = ListUtil.fold(elementLst2, extractSMStates2, HashTableSM1.emptyHashTable())
              else
                smNodeTable = HashTableSM1.emptyHashTableSized(1)
              end
          smNodeTable
        end

         #= 
        Author: BTH
        Return true if element is a state machine statement, otherwise false =#
        function isSMStatement(inElement::SCode.Equation) ::Bool 
              local outIsSMStatement::Bool

              outIsSMStatement = begin
                  local name::String
                @match inElement begin
                  SCode.EQUATION(eEquation = SCode.EQ_NORETCALL(exp = Absyn.CALL(function_ = Absyn.CREF_IDENT(name = name))))  => begin
                    (name == "transition" || name == "initialState") && Config.synchronousFeaturesAllowed()
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsSMStatement
        end

         #= 
        Author: BTH
        Return true if element is a state machine statement, otherwise false =#
        function isSMStatement2(inElement::DAE.Element) ::Bool 
              local outIsSMStatement::Bool

              outIsSMStatement = begin
                  local name::String
                @match inElement begin
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT(name)))  => begin
                    (name == "transition" || name == "initialState") && Config.synchronousFeaturesAllowed()
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsSMStatement
        end

         #= 
        Author: BTH
        Helper function to getSMNodeTable =#
        function extractSMStates2(inElement::DAE.Element, inTable::SMNodeTable) ::SMNodeTable 
              local outTable::SMNodeTable = inTable

              outTable = begin
                  local smnode1::SMNode
                  local smnode2::SMNode
                  local cref1::DAE.ComponentRef
                  local cref2::DAE.ComponentRef
                  local isInitial1::Bool
                  local isInitial2::Bool
                  local edges1::HashSet.HashSetType
                  local edges2::HashSet.HashSetType
                @match inElement begin
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("transition"), expLst = DAE.CREF(componentRef = cref1) <| DAE.CREF(componentRef = cref2) <| _))  => begin
                      smnode1 = if BaseHashTable.hasKey(cref1, outTable)
                            BaseHashTable.get(cref1, outTable)
                          else
                            SMNODE(cref1, false, HashSet.emptyHashSet())
                          end
                      @match SMNODE(_, isInitial1, edges1) = smnode1
                      edges1 = BaseHashSet.add(cref1, edges1)
                      edges1 = BaseHashSet.add(cref2, edges1)
                      smnode1 = SMNODE(cref1, isInitial1, edges1)
                      outTable = BaseHashTable.add((cref1, smnode1), outTable)
                      smnode2 = if BaseHashTable.hasKey(cref2, outTable)
                            BaseHashTable.get(cref2, outTable)
                          else
                            SMNODE(cref2, false, HashSet.emptyHashSet())
                          end
                      @match SMNODE(_, isInitial2, edges2) = smnode2
                      edges2 = BaseHashSet.add(cref1, edges2)
                      edges2 = BaseHashSet.add(cref2, edges2)
                      smnode2 = SMNODE(cref2, isInitial2, edges2)
                      outTable = BaseHashTable.add((cref2, smnode2), outTable)
                    outTable
                  end
                  
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("initialState"), expLst = DAE.CREF(componentRef = cref1) <|  nil()))  => begin
                      smnode1 = if BaseHashTable.hasKey(cref1, outTable)
                            BaseHashTable.get(cref1, outTable)
                          else
                            SMNODE(cref1, true, HashSet.emptyHashSet())
                          end
                      @match SMNODE(_, _, edges1) = smnode1
                      edges1 = BaseHashSet.add(cref1, edges1)
                      smnode1 = SMNODE(cref1, true, edges1)
                      outTable = BaseHashTable.add((cref1, smnode1), outTable)
                    outTable
                  end
                end
              end
               #= print(\"InstStateMachineUtil.extractSMStates: transition(\"+ComponentReference.crefStr(cref1)+\", \"+ComponentReference.crefStr(cref2)+\")\\n\");
               =#
               #= print(\"InstStateMachineUtil.extractSMStates: initialState(\"+ComponentReference.crefStr(cref1)+\")\\n\");
               =#
          outTable
        end

         #= 
        Author: BTH
        Return list of states defined in current context (by checking 'transtion' and 'initialState' operators) =#
        function getSMStatesInContext(eqns::List{<:SCode.Equation}, inPrefix::Prefix.PrefixType) ::Tuple{List{DAE.ComponentRef}, List{DAE.ComponentRef}} 
              local initialStates::List{DAE.ComponentRef} #= Only initial states =#
              local states::List{DAE.ComponentRef} #= Initial and non-initial states =#

              local eqns1::List{SCode.Equation}
              local statesLL::List{List{Absyn.ComponentRef}}
              local initialStatesCR::List{Absyn.ComponentRef}
              local statesCR::List{Absyn.ComponentRef}

              eqns1 = list(eq for eq in eqns if isSMStatement(eq))
               #=  Extract initial states
               =#
              initialStatesCR = ListUtil.filterMap(eqns1, extractInitialSMStates)
              initialStates = ListUtil.map(initialStatesCR, ComponentReference.toExpCref)
               #=  prefix the names
               =#
              initialStates = ListUtil.map1(initialStates, prefixCrefNoContext2, inPrefix)
               #=  01.06.2015 Strange. I get a compile error if using below instead of above AND removing prefixCrefNoContext2(..) function definitions
               =#
               #=  initialStates := List.map(initialStates, function PrefixUtil.prefixCrefNoContext(inPre=inPrefix));
               =#
               #=  Extract states (initial as well as non-initial)
               =#
              statesLL = ListUtil.map(eqns1, extractSMStates)
              statesCR = ListUtil.flatten(statesLL)
              states = ListUtil.map(statesCR, ComponentReference.toExpCref)
               #=  prefix the names
               =#
              states = ListUtil.map(states, (inPrefix) -> PrefixUtil.prefixCrefNoContext(inPre = inPrefix))
          (states #= Initial and non-initial states =#, initialStates #= Only initial states =#)
        end

         #= 
        Helper function to getSMStatesInContext.
        Swapped order of inputs of PrefixUtil.prefixCrefNoContext(..) in order to use it with map1 =#
        function prefixCrefNoContext2(inCref::DAE.ComponentRef, inPre::Prefix.PrefixType) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              outCref = PrefixUtil.prefixCrefNoContext(inPre, inCref)
          outCref
        end

         #= 
        Author: BTH
        Helper function to getSMStatesInContext.
        Return state instance componenent refs used as arguments in operator 'initialState'.
         =#
        function extractInitialSMStates(inElement::SCode.Equation) ::Absyn.ComponentRef 
              local outElement::Absyn.ComponentRef

              outElement = begin
                  local cref1::Absyn.ComponentRef
                @match inElement begin
                  SCode.EQUATION(eEquation = SCode.EQ_NORETCALL(exp = Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "initialState"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(componentRef = cref1) <|  nil()))))  => begin
                    cref1
                  end
                end
              end
          outElement
        end

         #= 
        Author: BTH
        Helper function to getSMStatesInContext.
        Return list of state instance componenent refs used as arguments in operators 'transtion' or 'initialState'.
         =#
        function extractSMStates(inElement::SCode.Equation) ::List{Absyn.ComponentRef} 
              local outElement::List{Absyn.ComponentRef}

              outElement = begin
                  local cref1::Absyn.ComponentRef
                  local cref2::Absyn.ComponentRef
                @match inElement begin
                  SCode.EQUATION(eEquation = SCode.EQ_NORETCALL(exp = Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "transition"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(componentRef = cref1) <| Absyn.CREF(componentRef = cref2) <| _ <|  nil()))))  => begin
                    list(cref1, cref2)
                  end
                  
                  SCode.EQUATION(eEquation = SCode.EQ_NORETCALL(exp = Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "initialState"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(componentRef = cref1) <|  nil()))))  => begin
                    list(cref1)
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          outElement
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  module StateMachineFlatten 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Transition 
    @UniontypeDecl FlatSmSemantics 

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

        import DAE

        import FCore

        import ListUtil

        import ComponentReference

        import ExpressionDump

        import DAEUtil

        import Util

        import DAEDump

        import Error

        import HashTableCrToExpOption

        import Flags

          #= 
         Properties of a transition =#
         @Uniontype Transition begin
              @Record TRANSITION begin

                       from::ModelicaInteger
                       to::ModelicaInteger
                       condition::DAE.Exp
                       immediate = true::Bool
                       reset = true::Bool
                       synchronize = false::Bool
                       priority = 1::ModelicaInteger
              end
         end

          #= 
         Structure that combines states of flat state machine in
         canonical order with governing semantic equations. =#
         @Uniontype FlatSmSemantics begin
              @Record FLAT_SM_SEMANTICS begin

                       ident::DAE.Ident
                       smComps #= First element is the initial state =#::Array{DAE.Element}
                       #=  Flat State machine semantics (SMS)
                       =#
                       t #= List/Array of transition data sorted in priority =#::List{Transition}
                       c #= Transition conditions sorted in priority =#::List{DAE.Exp}
                       vars #= SMS veriables =#::List{DAE.Element}
                       knowns #= SMS constants/parameters =#::List{DAE.Element}
                       eqs #= SMS equations =#::List{DAE.Element}
                       #=  Activation and Reset propagation through hierarchy
                       =#
                       pvars #= Propagation related variables =#::List{DAE.Element}
                       peqs #= Propagation equations =#::List{DAE.Element}
                       enclosingState #= Cref to enclosing state if any =#::Option{DAE.ComponentRef}
                       #=  FIXME needed?
                       =#
              end
         end

         const SMS_PRE = "smOf" #= prefix for crefs of fresh State Machine Semantics variables/knowns =#::String

         #= 
        Author: BTH
          Transform state machines to data-flow equations
         =#
        function stateMachineToDataFlow(cache::FCore.Cache, env::FCore.Graph, inDAElist::DAE.DAElist) ::DAE.DAElist 
              local outDAElist::DAE.DAElist

              local elementLst::List{DAE.Element}
              local elementLst1::List{DAE.Element}
              local flatSmLst::List{DAE.Element}
              local otherLst::List{DAE.Element}
              local elementLst2::List{DAE.Element}
              local elementLst3::List{DAE.Element}
              local t::List{Transition}
              local compElem::DAE.Element
              local nOfSubstitutions::ModelicaInteger
               #=  COMP
               =#
              local ident::DAE.Ident
              local dAElist::List{DAE.Element} #= a component with subelements, normally only used at top level. =#
              local source::DAE.ElementSource #= the origin of the component/equation/algorithm =#
              local comment::Option{SCode.Comment}

              @match DAE.DAE(elementLst = elementLst) = inDAElist
              assert(listLength(elementLst) == 1, "Internal compiler error: Handling of elementLst != 1 not supported\\n")
              @match DAE.COMP(ident, dAElist, source, comment) = listHead(elementLst)
              if ! ListUtil.exist(dAElist, isFlatSm)
                outDAElist = inDAElist
                return outDAElist
              end
              (flatSmLst, otherLst) = ListUtil.extractOnTrue(dAElist, isFlatSm)
              elementLst2 = ListUtil.fold2(flatSmLst, flatSmToDataFlow, NONE(), NONE(), nil)
               #=  HACK1 Wrap semantic state machine equations in when clauses for continuous-time state machines
               =#
              if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                elementLst2 = wrapHack(cache, elementLst2)
              end
              elementLst3 = listAppend(otherLst, elementLst2)
              outDAElist = DAE.DAE(list(DAE.COMP(ident, elementLst3, source, comment)))
               #=  print(\"StateMachineFlatten.stateMachineToDataFlow: outDAElist before global subs:\\n\" + DAEDump.dumpStr(outDAElist,FCore.getFunctionTree(cache)));
               =#
               #=  traverse dae expressions for making substitutions activeState(x) -> x.active
               =#
              (outDAElist, _, (_, nOfSubstitutions)) = DAEUtil.traverseDAE(outDAElist, FCore.getFunctionTree(cache), Expression.traverseSubexpressionsHelper, (traversingSubsActiveState, 0))
              if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                (outDAElist, _, (_, nOfSubstitutions)) = DAEUtil.traverseDAE(outDAElist, FCore.getFunctionTree(cache), Expression.traverseSubexpressionsHelper, (traversingSubsPreForPrevious, 0))
              end
               #=  HACK2 traverse dae expressions for making substitutions previous(x) -> pre(x)
               =#
               #=  FIXME not needed any more? HACK3 traverse dae expressions for making substitutions sample(x, _) -> x
               =#
               #=  (outDAElist, _, (_,nOfSubstitutions)) := DAEUtil.traverseDAE(outDAElist, FCore.getFunctionTree(cache), Expression.traverseSubexpressionsHelper, (traversingSubsXForSampleX, 0));
               =#
               #= print(\"StateMachineFlatten.stateMachineToDataFlow: outDAElist:\\n\" + DAEDump.dumpStr(outDAElist,FCore.getFunctionTree(cache)));
               =#
          outDAElist
        end

         #= 
        Author: BTH
        Helper function to traverse subexpressions
        Substitutes 'activeState(x)' by 'x.active'  =#
        function traversingSubsActiveState(inExp::DAE.Exp, inHitCount::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local outHitCount::ModelicaInteger
              local outExp::DAE.Exp

              (outExp, outHitCount) = begin
                  local componentRef::DAE.ComponentRef
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT("activeState"), expLst = DAE.CREF(componentRef = componentRef) <|  nil())  => begin
                    (DAE.CREF(ComponentReference.crefPrependIdent(componentRef, "active", nil, DAE.T_BOOL_DEFAULT), DAE.T_BOOL_DEFAULT), inHitCount + 1)
                  end
                  
                  _  => begin
                      (inExp, inHitCount)
                  end
                end
              end
          (outExp, outHitCount)
        end

         #= 
          Author: BTH
          Transform a flat state machine to data-flow equations
         =#
        function flatSmToDataFlow(inFlatSm::DAE.Element #= flat state machine that is to be transformed to data-flow equations =#, inEnclosingStateCrefOption::Option{<:DAE.ComponentRef} #= Cref of state that encloses the flat state machiene (NONE() if at top hierarchy) =#, inEnclosingFlatSmSemanticsOption::Option{<:FlatSmSemantics} #= The flat state machine semantics structure governing the enclosing state (NONE() if at top hierarchy) =#, accElems::List{<:DAE.Element}) ::List{DAE.Element} 
              local outElems::List{DAE.Element} = accElems

              local ident::DAE.Ident
              local dAElist::List{DAE.Element}
              local smCompsLst::List{DAE.Element}
              local otherLst1::List{DAE.Element}
              local transitionLst::List{DAE.Element}
              local otherLst2::List{DAE.Element}
              local otherLst3::List{DAE.Element}
              local eqnLst::List{DAE.Element}
              local otherLst4::List{DAE.Element}
              local smCompsLst2::List{DAE.Element}
              local initialStateOp::DAE.Element
              local initialStateComp::DAE.Element
              local crefInitialState::DAE.ComponentRef
              local flatSmSemanticsBasics::FlatSmSemantics
              local flatSmSemanticsWithPropagation::FlatSmSemantics
              local flatSmSemantics::FlatSmSemantics
              local transitions::List{Transition}
              local vars::List{DAE.Element} #= SMS veriables =#
              local knowns::List{DAE.Element} #= SMS constants/parameters =#
              local eqs::List{DAE.Element} #= SMS equations =#
              local pvars::List{DAE.Element} #= Propagation related variables =#
              local peqs::List{DAE.Element} #= Propagation equations =#
               #=  Option<DAE.ComponentRef> enclosingState \"Cref to enclosing state if any\";  FIXME needed?
               =#

              @match DAE.FLAT_SM(ident = ident, dAElist = dAElist) = inFlatSm
               #=  break Elements into different groups
               =#
              (smCompsLst, otherLst1) = ListUtil.extractOnTrue(dAElist, isSMComp)
              (transitionLst, otherLst2) = ListUtil.extractOnTrue(otherLst1, isTransition)
              @match (list(initialStateOp), otherLst3) = ListUtil.extractOnTrue(otherLst2, isInitialState)
              (eqnLst, otherLst4) = ListUtil.extractOnTrue(otherLst3, isEquation)
              assert(listLength(otherLst4) == 0, "Internal compiler error. Unexpected elements in flat state machine.")
              @match DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("initialState"), expLst = list(DAE.CREF(componentRef = crefInitialState)))) = initialStateOp
              @match (list(initialStateComp), smCompsLst2) = ListUtil.extract1OnTrue(smCompsLst, sMCompEqualsRef, crefInitialState)
               #=  Create basic semantic equations (MLS 17.3.4 Semantics Summary)
               =#
              flatSmSemanticsBasics = basicFlatSmSemantics(ident, _cons(initialStateComp, smCompsLst2), transitionLst)
               #=  Add activation and reset propagation related equations
               =#
              flatSmSemanticsWithPropagation = addPropagationEquations(flatSmSemanticsBasics, inEnclosingStateCrefOption, inEnclosingFlatSmSemanticsOption)
               #=  Elaborate on ticksInState() and timeInState() operators (MLS 17.1 Transitions)
               =#
              flatSmSemantics = elabXInStateOps(flatSmSemanticsWithPropagation, inEnclosingStateCrefOption)
              if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                smCompsLst = ListUtil.map(smCompsLst, elabXInStateOps_CT)
              end
               #=  Allow ticksInState() in state components (BTH not needed really needed for CT, delete this stuff?)
               =#
               #=  Extract semantic equations for flat state machine and add the elements to the DAE list
               =#
              @match FLAT_SM_SEMANTICS(vars = vars, knowns = knowns, eqs = eqs, pvars = pvars, peqs = peqs) = flatSmSemantics
              outElems = ListUtil.flatten(list(outElems, eqnLst, vars, knowns, eqs, pvars, peqs))
               #=  Extract DAE.Elements from state components (and recurse into potential FLAT_SMs in the state component)
               =#
              outElems = ListUtil.fold1(smCompsLst, smCompToDataFlow, flatSmSemantics, outElems)
          outElems
        end

         #= 
        Author: BTH
          For continuous-time state machines, support ticksInState() operators in state components
         =#
        function elabXInStateOps_CT(inSmComp::DAE.Element) ::DAE.Element 
              local outSmComp::DAE.Element

              local nOfHits::ModelicaInteger = 0
              local componentRef::DAE.ComponentRef
              local dAElist1::List{DAE.Element}
              local dAElist2::List{DAE.Element}
              local emptyTree::DAE.FunctionTree

              @match DAE.SM_COMP(componentRef, dAElist1) = inSmComp
              emptyTree = DAE.AvlTreePathFunction.Tree.EMPTY()
              @match (DAE.DAE(dAElist2), _, (_, (_, nOfHits))) = DAEUtil.traverseDAE(DAE.DAE(dAElist1), emptyTree, Expression.traverseSubexpressionsHelper, (traversingSubsTicksInState, (componentRef, 0)))
              outSmComp = DAE.SM_COMP(componentRef, dAElist2)
          outSmComp
        end

         #= 
        Author: BTH
        Helper function to elabXInStateOps_CT for traversing subexpressions
        Substitutes ticksInState() by enclosingStateComponent.$ticksInState '
         =#
        function traversingSubsTicksInState(inExp::DAE.Exp, inCref_HitCount::Tuple{<:DAE.ComponentRef, ModelicaInteger} #= tuple of cref of enclosing state component and substitution hit counter =#) ::Tuple{DAE.Exp, Tuple{DAE.ComponentRef, ModelicaInteger}} 
              local outCref_HitCount::Tuple{DAE.ComponentRef, ModelicaInteger}
              local outExp::DAE.Exp

              local cref::DAE.ComponentRef
              local hitCount::ModelicaInteger

              (cref, hitCount) = inCref_HitCount
              (outExp, outCref_HitCount) = begin
                  local ty::DAE.Type
                  local crefTicksInState::DAE.ComponentRef
                @match inExp begin
                  DAE.CALL(path = Absyn.IDENT("ticksInState"), expLst =  nil(), attr = DAE.CALL_ATTR(ty = ty))  => begin
                      crefTicksInState = ComponentReference.joinCrefs(cref, DAE.CREF_IDENT("ticksInState", ty, nil))
                    (DAE.CREF(crefTicksInState, ty), (cref, hitCount + 1))
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
          Transform ticksInState() and timeInState() operators to data-flow equations
         =#
        function elabXInStateOps(inFlatSmSemantics::FlatSmSemantics, inEnclosingStateCrefOption::Option{<:DAE.ComponentRef} #= Cref of state that encloses the flat state machiene (NONE() if at top hierarchy) =#) ::FlatSmSemantics 
              local outFlatSmSemantics::FlatSmSemantics

              local i::ModelicaInteger
              local found::Bool
              local c2::DAE.Exp
              local c3::DAE.Exp
              local c4::DAE.Exp
              local conditionNew::DAE.Exp
              local substTickExp::DAE.Exp
              local substTimeExp::DAE.Exp
              local stateRef::DAE.ComponentRef
              local t2::Transition
              local tElab::List{Transition} = nil #= Elaborated transitions =#
              local cElab::List{DAE.Exp} = nil #= Elaborated conditions =#
              local smeqsElab::List{DAE.Element} = nil #= Elaborated smeqs =#
               #=  FLAT_SM_SEMANTICS
               =#
              local ident::DAE.Ident
              local smComps::Array{DAE.Element} #= First element is the initial state =#
              local t::List{Transition} #= List/Array of transition data sorted in priority =#
              local c::List{DAE.Exp} #= Transition conditions sorted in priority =#
              local smvars::List{DAE.Element} #= SMS veriables =#
              local smknowns::List{DAE.Element} #= SMS constants/parameters =#
              local smeqs::List{DAE.Element} #= SMS equations =#
              local pvars::List{DAE.Element} = nil #= Propagation related variables =#
              local peqs::List{DAE.Element} = nil #= Propagation equations =#
              local enclosingStateOption::Option{DAE.ComponentRef} #= Cref to enclosing state if any =#
               #=  FIXME needed?
               =#
               #=  TRANSITION
               =#
              local from::ModelicaInteger
              local to::ModelicaInteger
              local condition::DAE.Exp
              local immediate::Bool
              local reset::Bool
              local synchronize::Bool
              local priority::ModelicaInteger

              @match FLAT_SM_SEMANTICS(ident, smComps, t, c, smvars, smknowns, smeqs, pvars, peqs, enclosingStateOption) = inFlatSmSemantics
               #=  We have some redundancy here (t[:].condition == c[:]) and thus need to update both
               =#
              i = 0
              for tc in ListUtil.threadTuple(t, c)
                i = i + 1
                (t2, c2) = tc
                @match TRANSITION(from, to, condition, immediate, reset, synchronize, priority) = t2
                @match DAE.SM_COMP(componentRef = stateRef) = arrayGet(smComps, from)
                substTickExp = DAE.CREF(qCref("ticksInState", DAE.T_INTEGER_DEFAULT, nil, stateRef), DAE.T_INTEGER_DEFAULT)
                (c3, (_, _, found)) = Expression.traverseExpTopDown(c2, traversingSubsXInState, ("ticksInState", substTickExp, false))
                if found && isSome(inEnclosingStateCrefOption)
                  Error.addCompilerError("Found 'ticksInState()' within a state of an hierarchical state machine.")
                  fail()
                end
                smeqsElab = if found
                      ListUtil.map5(smeqs, smeqsSubsXInState, arrayGet(smComps, 1), i, listLength(t), substTickExp, "ticksInState")
                    else
                      smeqs
                    end
                smeqs = smeqsElab
                substTimeExp = DAE.CREF(qCref("timeInState", DAE.T_REAL_DEFAULT, nil, stateRef), DAE.T_REAL_DEFAULT)
                (c4, (_, _, found)) = Expression.traverseExpTopDown(c2, traversingSubsXInState, ("timeInState", substTimeExp, false))
                if found && isSome(inEnclosingStateCrefOption)
                  Error.addCompilerError("Found 'timeInState()' within a state of an hierarchical state machine.")
                  fail()
                end
                smeqsElab = if found
                      ListUtil.map5(smeqs, smeqsSubsXInState, arrayGet(smComps, 1), i, listLength(t), substTimeExp, "timeInState")
                    else
                      smeqs
                    end
                smeqs = smeqsElab
                tElab = _cons(TRANSITION(from, to, c4, immediate, reset, synchronize, priority), tElab)
                cElab = _cons(c4, cElab)
              end
               #=  Need to access decorations attached to 'from' state
               =#
               #=  == Search whether condition contains a subexpression 'ticksInState()', if so, substitute them by 'smComps[from].$ticksInState' ==
               =#
               #=  MLS 3.3 17.1: \"can only be used in transition conditions of state machines not present in states of hierarchical state machines\" violated
               =#
               #=  if a transition was updated we also need to update the semantic equation containing that transition's logic
               =#
               #=  use updated smeqs
               =#
               #=  == Search whether condition contains a subexpression 'timeInState()', if so, substitute them by 'smComps[from].$timeInState' ==
               =#
               #=  MLS 3.3 17.1: \"can only be used in transition conditions of state machines not present in states of hierarchical state machines\" violated
               =#
               #=  if a transition was updated we also need to update the semantic equation containing that transition's logic
               =#
               #=  use updated smeqs
               =#
              outFlatSmSemantics = FLAT_SM_SEMANTICS(ident, smComps, listReverse(tElab), listReverse(cElab), smvars, smknowns, smeqsElab, pvars, peqs, enclosingStateOption)
          outFlatSmSemantics
        end

         #= 
        Author: BTH
        Helper function to elabXInStateOps.
        Replace 'xInState()' in RHS of semantic equations by 'substExp', but only within the transition
        condition specified by the remaining function arguments.
         =#
        function smeqsSubsXInState(inSmeqs::DAE.Element #= SMS equation =#, initialStateComp::DAE.Element #= Initial state component of governing flat state machine =#, i::ModelicaInteger #= Index of transition =#, nTransitions::ModelicaInteger, substExp::DAE.Exp, xInState::String #= Name of function that is to be replaced, e.g., 'timeInState', or 'tickInState' =#) ::DAE.Element 
              local outSmeqs::DAE.Element #= SMS equation =#

              local preRef::DAE.ComponentRef
              local cref::DAE.ComponentRef
              local lhsRef::DAE.ComponentRef
              local crefInitialState::DAE.ComponentRef
              local tArrayBool::DAE.Type
              local elemSource::DAE.ElementSource
              local lhsExp::DAE.Exp
              local rhsExp::DAE.Exp
              local rhsExp2::DAE.Exp
              local ty::DAE.Type

               #=  Cref to initial state of governing flat state machine
               =#
              @match DAE.SM_COMP(componentRef = crefInitialState) = initialStateComp
              preRef = ComponentReference.crefPrefixString(SMS_PRE, crefInitialState)
              tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(nTransitions)))
              cref = qCref("cImmediate", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef)
              @match DAE.EQUATION(lhsExp, rhsExp, elemSource) = inSmeqs
              @match DAE.CREF(lhsRef, ty) = lhsExp
               #=  print(\"StateMachineFlatten.smeqsSubsXInState: cref: \" + ComponentReference.printComponentRefStr(cref) + \"\\n\");
               =#
               #=  print(\"StateMachineFlatten.smeqsSubsXInState: lhsRef: \" + ComponentReference.printComponentRefStr(lhsRef) + \"\\n\");
               =#
              if ComponentReference.crefEqual(cref, lhsRef)
                (rhsExp2, _) = Expression.traverseExpTopDown(rhsExp, traversingSubsXInState, (xInState, substExp, false))
              else
                rhsExp2 = rhsExp
              end
               #=  print(\"StateMachineFlatten.smeqsSubsXInState: rhsExp: \" + ExpressionDump.printExpStr(rhsExp) + \"\\n\");
               =#
               #=  print(\"StateMachineFlatten.smeqsSubsXInState: rhsExp2: \" + ExpressionDump.printExpStr(rhsExp2) + \"\\n\");
               =#
              outSmeqs = DAE.EQUATION(lhsExp, rhsExp2, elemSource)
          outSmeqs #= SMS equation =#
        end

         #= 
        Author: BTH
        Helper function to elabXInStateOps and smeqsSubsXInState.
        Replace 'XInState()' operators (first element of inXSubstHit) by expression given in second element of inXSubstHit tuple.
         =#
        function traversingSubsXInState(inExp::DAE.Exp, inXSubstHit::Tuple{<:String, DAE.Exp, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{String, DAE.Exp, Bool}} 
              local outXSubstHit::Tuple{String, DAE.Exp, Bool}
              local cont::Bool = true
              local outExp::DAE.Exp

              (outExp, outXSubstHit) = begin
                  local subsExp::DAE.Exp
                  local hit::Bool
                  local xInState::String
                  local name::String
                @match (inExp, inXSubstHit) begin
                  (DAE.CALL(path = Absyn.IDENT(name)), (xInState, subsExp, _)) where (name == xInState)  => begin
                    (subsExp, (xInState, subsExp, true))
                  end
                  
                  _  => begin
                      (inExp, inXSubstHit)
                  end
                end
              end
          (outExp, cont, outXSubstHit)
        end

         #= 
        Author: BTH
          Transform state machine component to data-flow equations
         =#
        function smCompToDataFlow(inSMComp::DAE.Element, inEnclosingFlatSmSemantics::FlatSmSemantics #= The flat state machine semantics structure governing the state component =#, accElems::List{<:DAE.Element}) ::List{DAE.Element} 
              local outElems::List{DAE.Element} = accElems

              local varLst1::List{DAE.Element}
              local varLst2::List{DAE.Element}
              local assignedVarLst::List{DAE.Element}
              local stateVarLst::List{DAE.Element}
              local otherLst1::List{DAE.Element}
              local equationLst1::List{DAE.Element}
              local equationLst2::List{DAE.Element}
              local otherLst2::List{DAE.Element}
              local flatSmLst::List{DAE.Element}
              local otherLst3::List{DAE.Element}
              local componentRef::DAE.ComponentRef
              local stateVarCrefs::List{DAE.ComponentRef}
              local variableAttributesOptions::List{Option{DAE.VariableAttributes}}
              local startValuesOpt::List{Option{DAE.Exp}}
              local varCrefStartVal::List{Tuple{DAE.ComponentRef, Option{DAE.Exp}}}
              local dAElist::List{DAE.Element} #= a component with subelements =#
              local crToExpOpt::HashTableCrToExpOption.HashTable #= Table that maps the cref of a variable to its start value =#

              @match DAE.SM_COMP(componentRef = componentRef, dAElist = dAElist) = inSMComp
              (varLst1, otherLst1) = ListUtil.extractOnTrue(dAElist, isVar)
               #=  FIXME More general handling requires supporting all valid elements, e.g., also IF_EQUATION (also in downstream functions), but not sure what can be possibly encountered here
               =#
              (equationLst1, otherLst2) = ListUtil.extractOnTrue(otherLst1, isEquationOrWhenEquation)
               #=  FIXME More general handling might require assignment matching algorithm. Current restriction relies on that any assigned variable appears at the LHS of an assignment equation.
               =#
               #=  FIXME Maybe better to just filter out variables declared as \"inputs\" and assume that the rest are assigned variables?
               =#
               #=  Retain all variables for which there exits an assignment equation
               =#
              assignedVarLst = ListUtil.filterOnTrue(varLst1, (equationLst1, isVarAtLHS) -> ListUtil.exist1(inList = equationLst1, inFindFunc = isVarAtLHS))
               #=  Retain all variables which have \"previous(x)\" applied
               =#
              stateVarLst = ListUtil.filterOnTrue(varLst1, (equationLst1, isPreviousAppliedToVar) -> ListUtil.exist1(inList = equationLst1, inFindFunc = isPreviousAppliedToVar))
               #= print(\"StateMachineFlatten.smCompToDataFlow: stateVarLst:\\n\" + DAEDump.dumpElementsStr(stateVarLst) +\"\\n\");
               =#
              stateVarCrefs = ListUtil.map(stateVarLst, DAEUtil.varCref)
              variableAttributesOptions = ListUtil.map(stateVarLst, DAEUtil.getVariableAttributes)
              startValuesOpt = ListUtil.map(variableAttributesOptions, getStartAttrOption)
              varCrefStartVal = ListUtil.threadTuple(stateVarCrefs, startValuesOpt)
              crToExpOpt = HashTableCrToExpOption.emptyHashTableSized(listLength(varCrefStartVal) + 1)
               #=  create table that maps the cref of a variable to its start value
               =#
              crToExpOpt = ListUtil.fold(varCrefStartVal, BaseHashTable.add, crToExpOpt)
               #= print(\"StateMachineFlatten.smCompToDataFlow: crToExpOpt:\\n\"); BaseHashTable.dumpHashTable(crToExpOpt);
               =#
               #=  1. Make equations conditional so that they are only active if enclosing state is active
               =#
               #=  2. Add reset equations for discrete-time states declared in the component
               =#
              (equationLst2, varLst2) = ListUtil.fold3(equationLst1, addStateActivationAndReset, inSMComp, inEnclosingFlatSmSemantics, crToExpOpt, (nil, nil))
              (flatSmLst, otherLst3) = ListUtil.extractOnTrue(otherLst2, isFlatSm)
               #=  append non FLAT_SM elements to accumulator
               =#
              outElems = ListUtil.flatten(list(outElems, varLst1, varLst2, equationLst2, otherLst3))
               #=  recurse into FLAT_SM elements (if any)
               =#
              outElems = ListUtil.fold2(flatSmLst, flatSmToDataFlow, SOME(componentRef), SOME(inEnclosingFlatSmSemantics), outElems)
          outElems
        end

         #= 
        Author: BTH
        The real work is done in helper function addStateActivationAndReset1.
        This top-level function just handles the recursive descent if inEqn is a DAE.WHEN_EQUATION().
         =#
        function addStateActivationAndReset(inEqn::DAE.Element #= Expects DAE.EQUATION() or DAE.WHEN_EQUATION() =#, inEnclosingSMComp::DAE.Element #= The state component enclosing the equation =#, inEnclosingFlatSmSemantics::FlatSmSemantics #= The flat state machine semantics structure governing the state component =#, crToExpOpt::HashTableCrToExpOption.HashTable #= Table mapping variable declaration in the enclosing state to start values =#, accEqnsVars::Tuple{<:List{<:DAE.Element}, List{<:DAE.Element}} #= Tuple for accumulating equations and variable definitions =#) ::Tuple{List{DAE.Element}, List{DAE.Element}} 
              local outEqnsVars::Tuple{List{DAE.Element}, List{DAE.Element}}

              local equations1::List{DAE.Element}
              local vars1::List{DAE.Element}
               #=  WHEN_EQUATION
               =#
              local condition::DAE.Exp
              local equations::List{DAE.Element}
              local source::DAE.ElementSource

              outEqnsVars = begin
                @match inEqn begin
                  DAE.EQUATION(__)  => begin
                    addStateActivationAndReset1(inEqn, inEnclosingSMComp, inEnclosingFlatSmSemantics, crToExpOpt, accEqnsVars)
                  end
                  
                  DAE.WHEN_EQUATION(condition, equations, NONE(), source)  => begin
                      (equations1, vars1) = ListUtil.fold3(equations, addStateActivationAndReset, inEnclosingSMComp, inEnclosingFlatSmSemantics, crToExpOpt, (nil, nil))
                    (_cons(DAE.WHEN_EQUATION(condition, equations1, NONE(), source), Util.tuple21(accEqnsVars)), listAppend(vars1, Util.tuple22(accEqnsVars)))
                  end
                  
                  DAE.WHEN_EQUATION(elsewhen_ = SOME(_))  => begin
                      Error.addCompilerError("Encountered elsewhen part in a when clause of a clocked state machine.\\n")
                    fail()
                  end
                  
                  _  => begin
                        Error.addCompilerError("Internal compiler error: StateMachineFlatten.addStateActivationAndReset(..) called with unexpected argument.\\n")
                      fail()
                  end
                end
              end
          outEqnsVars
        end

         #= 
        Author: BTH
        The function has following purpose:
        1. Make equations conditional so that they are only active if enclosing state is active
        2. Add reset equations for discrete-time states declared in the component

        FIXME 2017-02-17: There is problem with the approach taken in this function of transforming s.th. similar to
          Real x(start=1.1);
          x = previous(x) + 1
        to something like
          x = if stateActive then x_previous + 1 else x_previous;
          x_previous = if active and (activeReset or activeResetStates[1]) then 1.1 else previous(x);
        While this gives the correct reset semantics for x, one gets a wrong result for previous(x) at the reset instant:
        'x_previous' is set to the correct result value, but during the reset instant in general there will be 'previous(x) != x_previous'!
        The transformation below replaces all occurances of 'previous(x)' within the state's equations to 'x_previous', so that the
        state machine will show the correct behavior. However, if 'x' is accessed with 'previous(x)' from outside the state, it will hold
        the wrong value. Also, when plotting 'previous(x)' will show a wrong value during reset.
        Hence, one needs another mechanism to reset 'previous(x)' correctly, but I don't see how this can be easily done by an equation
        transformation to standard clocked synchronous equations in the front-end. Probably one could add a dedicated internal marker/operator
        which is then handled specially in the back-end.
         =#
        function addStateActivationAndReset1(inEqn::DAE.Element, inEnclosingSMComp::DAE.Element #= The state component enclosing the equation =#, inEnclosingFlatSmSemantics::FlatSmSemantics #= The flat state machine semantics structure governing the state component =#, crToExpOpt::HashTableCrToExpOption.HashTable #= Table mapping variable declaration in the enclosing state to start values =#, accEqnsVars::Tuple{<:List{<:DAE.Element}, List{<:DAE.Element}} #= Tuple for accumulating equations and variable definitions =#) ::Tuple{List{DAE.Element}, List{DAE.Element}} 
              local outEqnsVars::Tuple{List{DAE.Element}, List{DAE.Element}}

              local stateVarCrefs::List{DAE.ComponentRef}
              local crefLHS::DAE.ComponentRef
              local enclosingStateRef::DAE.ComponentRef
              local substituteRef::DAE.ComponentRef
              local activeResetRef::DAE.ComponentRef
              local activeResetStatesRef::DAE.ComponentRef
              local cref2::DAE.ComponentRef
              local found::Bool
              local is::Bool
              local tyLHS::DAE.Type
              local eqn::DAE.Element
              local eqn1::DAE.Element
              local eqn2::DAE.Element
              local var2::DAE.Element
              local varDecl::DAE.Element
              local attr::DAE.CallAttributes
              local dAElist::List{DAE.Element}
              local isOuterVar::Bool
               #=  EQUATION
               =#
              local exp::DAE.Exp
              local scalar::DAE.Exp
              local scalarNew::DAE.Exp
              local source::DAE.ElementSource

              @match DAE.EQUATION(exp, scalar, source) = inEqn
              @match DAE.SM_COMP(componentRef = enclosingStateRef, dAElist = dAElist) = inEnclosingSMComp
              stateVarCrefs = BaseHashTable.hashTableKeyList(crToExpOpt)
              try
                @match DAE.CREF(componentRef = crefLHS, ty = tyLHS) = exp
                (scalarNew, (_, found)) = Expression.traverseExpTopDown(scalar, traversingSubsPreviousCrefs, (stateVarCrefs, false))
                eqn = DAE.EQUATION(exp, scalarNew, source)
                if ListUtil.exist(stateVarCrefs, (crefLHS) -> ComponentReference.crefEqual(inComponentRef1 = crefLHS))
                  eqn1 = wrapInStateActivationConditional(eqn, enclosingStateRef, true)
                  var2 = createVarWithDefaults(ComponentReference.appendStringLastIdent("_previous", crefLHS), DAE.DISCRETE(), tyLHS, nil)
                  eqn2 = createResetEquation(crefLHS, tyLHS, enclosingStateRef, inEnclosingFlatSmSemantics, crToExpOpt)
                  outEqnsVars = (_cons(eqn1, _cons(eqn2, Util.tuple21(accEqnsVars))), _cons(var2, Util.tuple22(accEqnsVars)))
                else
                  outEqnsVars = (_cons(wrapInStateActivationConditional(eqn, enclosingStateRef, false), Util.tuple21(accEqnsVars)), Util.tuple22(accEqnsVars))
                end
              catch
                try
                  if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                    @match DAE.CALL(Absyn.IDENT("der"), list(DAE.CREF(componentRef = crefLHS, ty = tyLHS)), attr) = exp
                    try
                      varDecl = ListUtil.find1(dAElist, isCrefInVar, crefLHS)
                    catch
                      Error.addCompilerError("Couldn't find variable declaration matching to cref " + ComponentReference.crefStr(crefLHS) + "\\n")
                      fail()
                    end
                    isOuterVar = DAEUtil.isOuterVar(varDecl)
                    if isOuterVar
                      cref2 = ComponentReference.appendStringLastIdent("_der", crefLHS)
                      var2 = createVarWithDefaults(cref2, DAE.VARIABLE(), tyLHS, nil)
                      eqn1 = DAE.EQUATION(DAE.CREF(cref2, tyLHS), scalar, source)
                      outEqnsVars = (_cons(eqn1, Util.tuple21(accEqnsVars)), _cons(var2, Util.tuple22(accEqnsVars)))
                    else
                      eqn1 = wrapInStateActivationConditionalCT(inEqn, enclosingStateRef)
                      eqn2 = createResetEquationCT(crefLHS, tyLHS, enclosingStateRef, inEnclosingFlatSmSemantics, crToExpOpt)
                      outEqnsVars = (_cons(eqn1, _cons(eqn2, Util.tuple21(accEqnsVars))), Util.tuple22(accEqnsVars))
                    end
                  else
                    fail()
                  end
                catch
                  if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                    Error.addCompilerError("Currently, only equations in state machines with a LHS component reference, e.g., x=.., or its derivative, e.g., der(x)=.., are supported")
                  else
                    Error.addCompilerError("Currently, only equations in state machines with a LHS component reference, e.g., x=.., are supported")
                  end
                  fail()
                end
              end
               #=  Handle case with LHS component reference
               =#
               #=  For all {x1,x2,..}, search whether the RHS of an equation 'x=exp' contains a subexpression 'previous(x)', if so, substitute them by 'x_previous'
               =#
               #=  If it is an assigning state equation, transform equation 'a.x = e' to 'a.x = if a.active then e else a.x_previous'
               =#
               #=  Transform equation 'a.x = e' to 'a.x = if a.active then e else a.x_previous'
               =#
               #=  Create fresh variable 'a.x_previous'
               =#
               #=  Create fresh reset equation: 'a.x_previous = if a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i] then x_start else previous(a.x)'
               =#
               #=  Handle case with LHS derivative (der(a.x))
               =#
               #=  BTH CT_STATE_MACHINES is experimental code
               =#
               #=  Find variable declaration that corresponds to crefLHS
               =#
               #=  Create fresh variable 'a.x_der$'
               =#
               #=  Change equation 'der(a.x) = e' to 'a.x_der$ = e'
               =#
               #=  Transform equation 'der(a.x) = e' to 'der(a.x) = if a.active then e else 0'
               =#
               #=  Create fresh reinit equation: 'when a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i]) then reinit(a.x, a.x_start) end when'
               =#
          outEqnsVars
        end

         #= 
        Author: BTH
        Return true if variable appears as LHS assignment in a scalar equation or in the body of a when equation.
         =#
        function isVarAtLHS(eqn::DAE.Element #= Expects DAE.EQUATION() or DAE.WHEN_EQUATION() =#, var::DAE.Element #= Expects DAE.VAR()) =#) ::Bool 
              local res::Bool

              local cref::DAE.ComponentRef
              local crefLHS::DAE.ComponentRef
              local tyLHS::DAE.Type
               #=  EQUATION
               =#
              local exp::DAE.Exp
              local scalar::DAE.Exp
              local scalarNew::DAE.Exp
              local source::DAE.ElementSource
               #=  WHEN_EQUATION
               =#
              local equations::List{DAE.Element}
              local elsewhen_::Option{DAE.Element}

              res = begin
                @match eqn begin
                  DAE.EQUATION(exp, scalar, source)  => begin
                      cref = DAEUtil.varCref(var)
                      try
                        @match DAE.CREF(componentRef = crefLHS, ty = tyLHS) = exp
                        res = ComponentReference.crefEqual(crefLHS, cref)
                      catch
                        res = false
                      end
                       #=  Handle case with LHS component reference
                       =#
                    res
                  end
                  
                  DAE.WHEN_EQUATION(equations = equations, elsewhen_ = NONE())  => begin
                    ListUtil.exist1(equations, isVarAtLHS, var)
                  end
                  
                  DAE.WHEN_EQUATION(elsewhen_ = SOME(_))  => begin
                      Error.addCompilerError("Encountered elsewhen part in a when clause of a clocked state machine.\\n")
                    fail()
                  end
                  
                  _  => begin
                        Error.addCompilerError("Internal compiler error: StateMachineFlatten.isVarAtLHS(..) called with unexpected argument.\\n")
                      fail()
                  end
                end
              end
          res
        end

         #= 
        Author: BTH
        Return true if variable x appears as previous(x) in the RHS of a scalar equation or in the body of a when equation.
         =#
        function isPreviousAppliedToVar(eqn::DAE.Element #= Expects DAE.EQUATION() or DAE.WHEN_EQUATION() =#, var::DAE.Element #= Expects DAE.VAR()) =#) ::Bool 
              local found::Bool = false

              local cref::DAE.ComponentRef
               #=  EQUATION
               =#
              local exp::DAE.Exp
              local scalar::DAE.Exp
              local scalarNew::DAE.Exp
              local source::DAE.ElementSource
               #=  WHEN_EQUATION
               =#
              local equations::List{DAE.Element}
              local elsewhen_::Option{DAE.Element}

              found = begin
                @match eqn begin
                  DAE.EQUATION(exp, scalar, source)  => begin
                      cref = DAEUtil.varCref(var)
                      (_, (_, found)) = Expression.traverseExpTopDown(scalar, traversingFindPreviousCref, (cref, false))
                    found
                  end
                  
                  DAE.WHEN_EQUATION(equations = equations, elsewhen_ = NONE())  => begin
                    ListUtil.exist1(equations, isPreviousAppliedToVar, var)
                  end
                  
                  DAE.WHEN_EQUATION(elsewhen_ = SOME(_))  => begin
                      Error.addCompilerError("Encountered elsewhen part in a when clause of a clocked state machine.\\n")
                    fail()
                  end
                  
                  _  => begin
                        Error.addCompilerError("Internal compiler error: StateMachineFlatten.isPreviousAppliedToVar(..) called with unexpected argument.\\n")
                      fail()
                  end
                end
              end
          found
        end

         #= 
        Author: BTH
        Given a cref 'x', find if the expression has subexpressions 'previous(x)' and indicate success.
         =#
        function traversingFindPreviousCref(inExp::DAE.Exp, inCrefHit::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outCrefHit::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool = true
              local outExp::DAE.Exp

              (outExp, outCrefHit) = begin
                  local cr::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                @match (inExp, inCrefHit) begin
                  (DAE.CALL(Absyn.IDENT("previous"), DAE.CREF(cr, _) <|  nil(), _), (cref, _)) where (ComponentReference.crefEqual(cr, cref))  => begin
                    (inExp, (cref, true))
                  end
                  
                  _  => begin
                      (inExp, inCrefHit)
                  end
                end
              end
          (outExp, cont, outCrefHit)
        end

         #= 
        Author: BTH
        Given LHS 'a.x' and its start value 'x_start', as well as its enclosing state component 'a' with index 'i' in its governing FLAT_SM 'fsm_of_a' return eqn
        'when a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i]) then reinit(a.x, a.x_start) end when'
         =#
        function createResetEquationCT(inLHSCref::DAE.ComponentRef #= LHS cref =#, inLHSty::DAE.Type #= LHS type =#, inStateCref::DAE.ComponentRef #= Component reference of state enclosing the equation =#, inEnclosingFlatSmSemantics::FlatSmSemantics #= The flat state machine semantics structure governing the state component =#, crToExpOpt::HashTableCrToExpOption.HashTable #= Table mapping variable declaration in the enclosing state to start values =#) ::DAE.Element 
              local outEqn::DAE.Element

              local activeExp::DAE.Exp
              local activeResetExp::DAE.Exp
              local activeResetStatesExp::DAE.Exp
              local orExp::DAE.Exp
              local andExp::DAE.Exp
              local startValueExp::DAE.Exp
              local preExp::DAE.Exp
              local reinitElem::DAE.Element
              local startValueOpt::Option{DAE.Exp}
              local initStateRef::DAE.ComponentRef
              local preRef::DAE.ComponentRef
              local i::ModelicaInteger
              local nStates::ModelicaInteger
              local enclosingFlatSMComps::Array{DAE.Element}
              local tArrayBool::DAE.Type
              local callAttributes::DAE.CallAttributes

              @match FLAT_SM_SEMANTICS(smComps = enclosingFlatSMComps) = inEnclosingFlatSmSemantics
              @match DAE.SM_COMP(componentRef = initStateRef) = arrayGet(enclosingFlatSMComps, 1)
               #=  initial state
               =#
               #=  prefix for state machine semantics equations of the governing flat state machine
               =#
              preRef = ComponentReference.crefPrefixString(SMS_PRE, initStateRef)
               #=  position of enclosing state in the array of states of its governing flat state machine
               =#
              i = ListUtil.position1OnTrue(arrayList(enclosingFlatSMComps), sMCompEqualsRef, inStateCref)
               #=  smOf.a.activeReset
               =#
              activeResetExp = DAE.CREF(qCref("activeReset", DAE.T_BOOL_DEFAULT, nil, preRef), DAE.T_BOOL_DEFAULT)
              nStates = arrayLength(enclosingFlatSMComps)
              tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(nStates)))
               #=  smOf.fsm_of_a.activeResetStates[i]
               =#
              activeResetStatesExp = DAE.CREF(qCref("activeResetStates", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef), DAE.T_BOOL_DEFAULT)
               #=  smOf.fsm_of_a.activeReset or smOf.fsm_of_a.activeResetStates[i]
               =#
              orExp = DAE.LBINARY(activeResetExp, DAE.OR(DAE.T_BOOL_DEFAULT), activeResetStatesExp)
               #=  a.active (reference the active indicator for this state)
               =#
              activeExp = DAE.CREF(qCref("active", DAE.T_BOOL_DEFAULT, nil, inStateCref), DAE.T_BOOL_DEFAULT)
               #=  a.active and (smOf.fsm_of_a.activeReset or smOf.fsm_of_a.activeResetStates[i])
               =#
              andExp = DAE.LBINARY(activeExp, DAE.AND(DAE.T_BOOL_DEFAULT), orExp)
               #= callAttributes := DAE.CALL_ATTR(inLHSty,false,true,false,false,DAE.NO_INLINE(),DAE.NO_TAIL());
               =#
               #=  pre(activeExp)
               =#
               #= preExp := DAE.CALL(Absyn.IDENT(\"pre\"), {activeExp}, callAttributes);
               =#
               #= andExp := DAE.LBINARY(activeExp, DAE.AND(DAE.T_BOOL_DEFAULT),  DAE.LUNARY(DAE.NOT(DAE.T_BOOL_DEFAULT), preExp));
               =#
              startValueOpt = BaseHashTable.get(inLHSCref, crToExpOpt)
              if isSome(startValueOpt)
                startValueExp = Util.getOption(startValueOpt)
              else
                startValueExp = begin
                  @match inLHSty begin
                    DAE.T_INTEGER(__)  => begin
                         #=  No start value given for the variable, default to \"0\"
                         =#
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=0.\\n")
                      DAE.ICONST(0)
                    end
                    
                    DAE.T_REAL(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=0.\\n")
                      DAE.RCONST(0)
                    end
                    
                    DAE.T_BOOL(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=false.\\n")
                      DAE.BCONST(false)
                    end
                    
                    DAE.T_STRING(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=\\\\.\\n")
                      DAE.SCONST("")
                    end
                    
                    _  => begin
                          Error.addCompilerError("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value.\\n")
                        fail()
                    end
                  end
                end
              end
               #=  reinit(a.x, a.x_start)
               =#
              reinitElem = DAE.REINIT(inLHSCref, startValueExp, DAE.emptyElementSource)
               #=  when a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i]) then reinit(a.x, a.x_start) end when;
               =#
              outEqn = DAE.WHEN_EQUATION(andExp, list(reinitElem), NONE(), DAE.emptyElementSource)
          outEqn
        end

         #= 
        Author: BTH
        Return true if element is a VAR containing the cref, otherwise false =#
        function isCrefInVar(inElement::DAE.Element, inCref::DAE.ComponentRef) ::Bool 
              local result::Bool

              result = begin
                  local cref::DAE.ComponentRef
                @match inElement begin
                  DAE.VAR(componentRef = cref) where (ComponentReference.crefEqual(cref, inCref))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Given LHS 'a.x' and its start value 'x_start', as well as its enclosing state component 'a' with index 'i' in its governing FLAT_SM 'fsm_of_a' return eqn
        'a.x_previous = if a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i] then x_start else previous(a.x)'
         =#
        function createResetEquation(inLHSCref::DAE.ComponentRef #= LHS cref =#, inLHSty::DAE.Type #= LHS type =#, inStateCref::DAE.ComponentRef #= Component reference of state enclosing the equation =#, inEnclosingFlatSmSemantics::FlatSmSemantics #= The flat state machine semantics structure governing the state component =#, crToExpOpt::HashTableCrToExpOption.HashTable #= Table mapping variable declaration in the enclosing state to start values =#) ::DAE.Element 
              local outEqn::DAE.Element

              local activeExp::DAE.Exp
              local lhsExp::DAE.Exp
              local activeResetExp::DAE.Exp
              local activeResetStatesExp::DAE.Exp
              local orExp::DAE.Exp
              local andExp::DAE.Exp
              local previousExp::DAE.Exp
              local startValueExp::DAE.Exp
              local ifExp::DAE.Exp
              local startValueOpt::Option{DAE.Exp}
              local initStateRef::DAE.ComponentRef
              local preRef::DAE.ComponentRef
              local i::ModelicaInteger
              local nStates::ModelicaInteger
              local enclosingFlatSMComps::Array{DAE.Element}
              local tArrayBool::DAE.Type
              local callAttributes::DAE.CallAttributes

              @match FLAT_SM_SEMANTICS(smComps = enclosingFlatSMComps) = inEnclosingFlatSmSemantics
              @match DAE.SM_COMP(componentRef = initStateRef) = arrayGet(enclosingFlatSMComps, 1)
               #=  initial state
               =#
               #=  prefix for state machine semantics equations of the governing flat state machine
               =#
              preRef = ComponentReference.crefPrefixString(SMS_PRE, initStateRef)
               #=  position of enclosing state in the array of states of its governing flat state machine
               =#
              i = ListUtil.position1OnTrue(arrayList(enclosingFlatSMComps), sMCompEqualsRef, inStateCref)
               #=  smOf.a.activeReset
               =#
              activeResetExp = DAE.CREF(qCref("activeReset", DAE.T_BOOL_DEFAULT, nil, preRef), DAE.T_BOOL_DEFAULT)
              nStates = arrayLength(enclosingFlatSMComps)
              tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(nStates)))
               #=  smOf.fsm_of_a.activeResetStates[i]
               =#
              activeResetStatesExp = DAE.CREF(qCref("activeResetStates", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef), DAE.T_BOOL_DEFAULT)
               #=  smOf.fsm_of_a.activeReset or smOf.fsm_of_a.activeResetStates[i]
               =#
              orExp = DAE.LBINARY(activeResetExp, DAE.OR(DAE.T_BOOL_DEFAULT), activeResetStatesExp)
               #=  a.active (reference the active indicator for this state)
               =#
              activeExp = DAE.CREF(qCref("active", DAE.T_BOOL_DEFAULT, nil, inStateCref), DAE.T_BOOL_DEFAULT)
               #=  a.active and (smOf.fsm_of_a.activeReset or smOf.fsm_of_a.activeResetStates[i])
               =#
              andExp = DAE.LBINARY(activeExp, DAE.AND(DAE.T_BOOL_DEFAULT), orExp)
              callAttributes = DAE.CALL_ATTR(inLHSty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())
               #=  previous(a.x)
               =#
              previousExp = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(inLHSCref, inLHSty)), callAttributes)
              startValueOpt = BaseHashTable.get(inLHSCref, crToExpOpt)
              if isSome(startValueOpt)
                startValueExp = Util.getOption(startValueOpt)
              else
                startValueExp = begin
                  @match inLHSty begin
                    DAE.T_INTEGER(__)  => begin
                         #=  No start value given for the variable, default to \"0\"
                         =#
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=0.\\n")
                      DAE.ICONST(0)
                    end
                    
                    DAE.T_REAL(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=0.\\n")
                      DAE.RCONST(0)
                    end
                    
                    DAE.T_BOOL(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=false.\\n")
                      DAE.BCONST(false)
                    end
                    
                    DAE.T_STRING(__)  => begin
                        Error.addCompilerWarning("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value. Defaulting to start=\\\\.\\n")
                      DAE.SCONST("")
                    end
                    
                    _  => begin
                          Error.addCompilerError("Variable " + ComponentReference.crefStr(inLHSCref) + " lacks start value.\\n")
                        fail()
                    end
                  end
                end
              end
               #=  if a.active and (smOf.fsm_of_a.activeReset or smOf.fsm_of_a.activeResetStates[i]) than x_start else previous(a.x)
               =#
              ifExp = DAE.IFEXP(andExp, startValueExp, previousExp)
               #=  a.x_previous
               =#
              lhsExp = DAE.CREF(ComponentReference.appendStringLastIdent("_previous", inLHSCref), inLHSty)
               #=  a.x_previous = if a.active and (smOf.a.activeReset or smOf.fsm_of_a.activeResetStates[i] then x_start else previous(a.x)
               =#
              outEqn = DAE.EQUATION(lhsExp, ifExp, DAE.emptyElementSource)
          outEqn
        end

         #= 
        Author: BTH
        Transform an equation 'a.x = e' to 'a.x = if a.active then e else previous(a.x)' (isResetEquation=false)
        Transform an equation 'a.x = e' to 'a.x = if a.active then e else x_previous' (isResetEquation=true)
         =#
        function wrapInStateActivationConditional(inEqn::DAE.Element, inStateCref::DAE.ComponentRef #= Component reference of state enclosing the equation =#, isResetEquation::Bool #= Reset equations =#) ::DAE.Element 
              local outEqn::DAE.Element

              local exp::DAE.Exp
              local scalar::DAE.Exp
              local scalar1::DAE.Exp
              local activeRef::DAE.Exp
              local expElse::DAE.Exp
              local ty::DAE.Type
              local callAttributes::DAE.CallAttributes
              local source::DAE.ElementSource
              local cref::DAE.ComponentRef

              @match DAE.EQUATION(exp, scalar, source) = inEqn
              try
                @match DAE.CREF(cref, ty) = exp
              catch
                Error.addCompilerError("The LHS of equations in state machines needs to be a component reference")
                fail()
              end
               #=  reference the active indicator for this state
               =#
              activeRef = DAE.CREF(qCref("active", DAE.T_BOOL_DEFAULT, nil, inStateCref), DAE.T_BOOL_DEFAULT)
              callAttributes = DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())
              if isResetEquation
                expElse = DAE.CREF(ComponentReference.appendStringLastIdent("_previous", cref), ty)
              else
                expElse = DAE.CALL(Absyn.IDENT("previous"), list(exp), callAttributes)
              end
               #=  x_previous
               =#
               #=  previous(x)
               =#
              scalar1 = DAE.IFEXP(activeRef, scalar, expElse)
               #=  state.x = if state.active then .. else expElse
               =#
              outEqn = DAE.EQUATION(exp, scalar1, source)
          outEqn
        end

         #= 
        Author: BTH
        Transform an equation 'der(a.x) = e' to 'der(a.x) = if a.active then e else 0' (isResetEquation=false)
        TODO: Implement reset equations for continuous time. Should that be done in this function or somewhere else?
        FIXME: Merge with wrapInStateActivationConditional(..)?
         =#
        function wrapInStateActivationConditionalCT(inEqn::DAE.Element, inStateCref::DAE.ComponentRef #= Component reference of state enclosing the equation =#) ::DAE.Element 
              local outEqn::DAE.Element

              local exp::DAE.Exp
              local scalar::DAE.Exp
              local scalar1::DAE.Exp
              local activeRef::DAE.Exp
              local expElse::DAE.Exp
              local ty::DAE.Type
              local callAttributes::DAE.CallAttributes
              local source::DAE.ElementSource
              local cref::DAE.ComponentRef

              @match DAE.EQUATION(exp, scalar, source) = inEqn
              try
                @match DAE.CALL(Absyn.IDENT("der"), list(DAE.CREF(componentRef = cref, ty = ty)), _) = exp
              catch
                Error.addCompilerError("The LHS of equations in state machines needs to be a component reference, e.g., x = .., or its derivative, e.g., der(x) = ..")
                fail()
              end
               #=  reference the active indicator for this state
               =#
              activeRef = DAE.CREF(qCref("active", DAE.T_BOOL_DEFAULT, nil, inStateCref), DAE.T_BOOL_DEFAULT)
              callAttributes = DAE.CALL_ATTR(ty, false, true, false, false, DAE.NO_INLINE(), DAE.NO_TAIL())
              expElse = DAE.RCONST(0)
              scalar1 = DAE.IFEXP(activeRef, scalar, expElse)
               #=  state.x = if state.active then .. else expElse
               =#
              outEqn = DAE.EQUATION(exp, scalar1, source)
          outEqn
        end

         #= 
        Author: BTH
        Given a cref 'x', find if the expression has subexpressions 'previous(x)' and replace them by 'x_previous'
        and return an indication if any substitutions took place.
         =#
        function traversingSubsPreviousCref(inExp::DAE.Exp, inCrefHit::Tuple{<:DAE.ComponentRef, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{DAE.ComponentRef, Bool}} 
              local outCrefHit::Tuple{DAE.ComponentRef, Bool}
              local cont::Bool = true
              local outExp::DAE.Exp

              (outExp, outCrefHit) = begin
                  local cr::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                  local substituteRef::DAE.ComponentRef
                  local hit::Bool
                  local attr::DAE.CallAttributes
                  local ty::DAE.Type
                @match (inExp, inCrefHit) begin
                  (DAE.CALL(Absyn.IDENT("previous"), DAE.CREF(cr, ty) <|  nil(), _), (cref, _)) where (ComponentReference.crefEqual(cr, cref))  => begin
                      print("StateMachineFlatten.traversingSubsPreviousCref: cr: " + ComponentReference.crefStr(cr) + ", cref: " + ComponentReference.crefStr(cref) + "\\n")
                      substituteRef = ComponentReference.appendStringLastIdent("_previous", cref)
                    (DAE.CREF(substituteRef, ty), (cref, true))
                  end
                  
                  _  => begin
                      (inExp, inCrefHit)
                  end
                end
              end
          (outExp, cont, outCrefHit)
        end

         #= 
        Author: BTH
        Given a list of crefs '{x1,x2,...}', find if the expression has subexpressions 'previous(x)' and replace them by 'x_previous'
        and return an indication if any substitutions took place.
         =#
        function traversingSubsPreviousCrefs(inExp::DAE.Exp, inCrefsHit::Tuple{<:List{<:DAE.ComponentRef}, Bool}) ::Tuple{DAE.Exp, Bool, Tuple{List{DAE.ComponentRef}, Bool}} 
              local outCrefsHit::Tuple{List{DAE.ComponentRef}, Bool}
              local cont::Bool = true
              local outExp::DAE.Exp

              (outExp, outCrefsHit) = begin
                  local cr::DAE.ComponentRef
                  local substituteRef::DAE.ComponentRef
                  local crefs::List{DAE.ComponentRef}
                  local hit::Bool
                  local attr::DAE.CallAttributes
                  local ty::DAE.Type
                @match (inExp, inCrefsHit) begin
                  (DAE.CALL(Absyn.IDENT("previous"), DAE.CREF(cr, ty) <|  nil(), _), (crefs, _)) where (ListUtil.exist(crefs, (cr) -> ComponentReference.crefEqual(inComponentRef1 = cr)))  => begin
                       #=  print(\"StateMachineFlatten.traversingSubsPreviousCrefs: cr: \"+ComponentReference.crefStr(cr)+\", crefs: \" + stringDelimitList(List.map(crefs, ComponentReference.crefStr), \",\")+\"\\n\");
                       =#
                      substituteRef = ComponentReference.appendStringLastIdent("_previous", cr)
                    (DAE.CREF(substituteRef, ty), (crefs, true))
                  end
                  
                  _  => begin
                      (inExp, inCrefsHit)
                  end
                end
              end
          (outExp, cont, outCrefsHit)
        end

         #= 
        Helper function to smCompToDataFlow
         =#
        function getStartAttrOption(inVarAttrOpt::Option{<:DAE.VariableAttributes}) ::Option{DAE.Exp} 
              local outExpOpt::Option{DAE.Exp}

              local start::DAE.Exp

              if isSome(inVarAttrOpt)
                start = DAEUtil.getStartAttr(inVarAttrOpt)
                outExpOpt = SOME(start)
              else
                outExpOpt = NONE()
              end
          outExpOpt
        end

         #= 
        Author: BTH
        Add activation and reset propagation related equation and variables to flat state machine
         =#
        function addPropagationEquations(inFlatSmSemantics::FlatSmSemantics, inEnclosingStateCrefOption::Option{<:DAE.ComponentRef} #= Cref of state that encloses the flat state machiene (NONE() if at top hierarchy) =#, inEnclosingFlatSmSemanticsOption::Option{<:FlatSmSemantics} #= The flat state machine semantics structure governing the enclosing state (NONE() if at top hierarchy) =#) ::FlatSmSemantics 
              local outFlatSmSemantics::FlatSmSemantics

              local preRef::DAE.ComponentRef
              local initStateRef::DAE.ComponentRef
              local initRef::DAE.ComponentRef
              local resetRef::DAE.ComponentRef
              local activeRef::DAE.ComponentRef
              local stateRef::DAE.ComponentRef
              local activePlotIndicatorRef::DAE.ComponentRef
              local initVar::DAE.Element
              local activePlotIndicatorVar::DAE.Element
              local ticksInStateVar::DAE.Element
              local timeEnteredStateVar::DAE.Element
              local timeInStateVar::DAE.Element
              local activePlotIndicatorEqn::DAE.Element
              local ticksInStateEqn::DAE.Element
              local timeEnteredStateEqn::DAE.Element
              local timeInStateEqn::DAE.Element
              local rhs::DAE.Exp
              local andExp::DAE.Exp
              local eqExp::DAE.Exp
              local activeResetStateRefExp::DAE.Exp
              local activeStateRefExp::DAE.Exp
              local activeResetRefExp::DAE.Exp
              local tArrayBool::DAE.Type
              local tArrayInteger::DAE.Type
               #=  FLAT_SM_SEMANTICS
               =#
              local ident::DAE.Ident
              local smComps::Array{DAE.Element} #= First element is the initial state =#
              local t::List{Transition} #= List/Array of transition data sorted in priority =#
              local c::List{DAE.Exp} #= Transition conditions sorted in priority =#
              local smvars::List{DAE.Element} #= SMS veriables =#
              local smknowns::List{DAE.Element} #= SMS constants/parameters =#
              local smeqs::List{DAE.Element} #= SMS equations =#
              local enclosingStateOption::Option{DAE.ComponentRef} #= Cref to enclosing state if any =#
               #=  FIXME needed?
               =#
              local pvars::List{DAE.Element} = nil #= Propagation related variables =#
              local peqs::List{DAE.Element} = nil #= Propagation equations =#
               #=  Enclosing FLAT_SM_SEMANTICS
               =#
              local enclosingStateCref::DAE.ComponentRef
              local enclosingPreRef::DAE.ComponentRef
              local enclosingActiveResetStateRef::DAE.ComponentRef
              local enclosingActiveResetRef::DAE.ComponentRef
              local enclosingActiveStateRef::DAE.ComponentRef
              local enclosingFlatSMSemantics::FlatSmSemantics
              local enclosingFlatSMComps::Array{DAE.Element} #= First element is the initial state =#
              local enclosingFlatSMInitStateRef::DAE.ComponentRef
              local posOfEnclosingSMComp::ModelicaInteger
              local nStates::ModelicaInteger

              @match FLAT_SM_SEMANTICS(ident = ident, smComps = smComps, t = t, c = c, vars = smvars, knowns = smknowns, eqs = smeqs) = inFlatSmSemantics
              @match DAE.SM_COMP(componentRef = initStateRef) = arrayGet(smComps, 1)
               #=  initial state
               =#
               #=  cref prefix for semantics equations governing flat state machine
               =#
              preRef = ComponentReference.crefPrefixString(SMS_PRE, initStateRef)
               #=  MLS 17.3.4 Semantics Summary: \"active\" and \"reset\" are *inputs* to the state machine semantics. They are defined below
               =#
              activeRef = qCref("active", DAE.T_BOOL_DEFAULT, nil, preRef)
              resetRef = qCref("reset", DAE.T_BOOL_DEFAULT, nil, preRef)
              if isNone(inEnclosingFlatSmSemanticsOption)
                initRef = qCref("init", DAE.T_BOOL_DEFAULT, nil, preRef)
                initVar = createVarWithDefaults(initRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
                initVar = setVarFixedStartValue(initVar, DAE.BCONST(true))
                pvars = _cons(initVar, pvars)
                peqs = _cons(DAE.EQUATION(DAE.CREF(initRef, DAE.T_BOOL_DEFAULT), DAE.BCONST(false), DAE.emptyElementSource), peqs)
                rhs = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(initRef, DAE.T_BOOL_DEFAULT)), DAE.callAttrBuiltinImpureBool)
                peqs = _cons(DAE.EQUATION(DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT), rhs, DAE.emptyElementSource), peqs)
                peqs = _cons(DAE.EQUATION(DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT), DAE.BCONST(true), DAE.emptyElementSource), peqs)
              else
                enclosingStateCref = Util.getOption(inEnclosingStateCrefOption)
                enclosingFlatSMSemantics = Util.getOption(inEnclosingFlatSmSemanticsOption)
                @match FLAT_SM_SEMANTICS(smComps = enclosingFlatSMComps) = enclosingFlatSMSemantics
                @match DAE.SM_COMP(componentRef = enclosingFlatSMInitStateRef) = arrayGet(enclosingFlatSMComps, 1)
                enclosingPreRef = ComponentReference.crefPrefixString(SMS_PRE, enclosingFlatSMInitStateRef)
                posOfEnclosingSMComp = ListUtil.position1OnTrue(arrayList(enclosingFlatSMComps), sMCompEqualsRef, enclosingStateCref)
                nStates = arrayLength(enclosingFlatSMComps)
                tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(nStates)))
                tArrayInteger = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, list(DAE.DIM_INTEGER(nStates)))
                enclosingActiveResetStateRef = qCref("activeResetStates", tArrayBool, list(DAE.INDEX(DAE.ICONST(posOfEnclosingSMComp))), enclosingPreRef)
                enclosingActiveResetRef = qCref("activeReset", DAE.T_BOOL_DEFAULT, nil, enclosingPreRef)
                enclosingActiveStateRef = qCref("activeState", DAE.T_INTEGER_DEFAULT, nil, enclosingPreRef)
                eqExp = DAE.RELATION(DAE.CREF(enclosingActiveStateRef, DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(posOfEnclosingSMComp), -1, NONE())
                andExp = DAE.LBINARY(DAE.CREF(enclosingActiveResetRef, DAE.T_BOOL_DEFAULT), DAE.AND(DAE.T_BOOL_DEFAULT), eqExp)
                rhs = DAE.LBINARY(DAE.CREF(enclosingActiveResetStateRef, DAE.T_BOOL_DEFAULT), DAE.OR(DAE.T_BOOL_DEFAULT), andExp)
                peqs = _cons(DAE.EQUATION(DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT), rhs, DAE.emptyElementSource), peqs)
                rhs = DAE.RELATION(DAE.CREF(enclosingActiveStateRef, DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(posOfEnclosingSMComp), -1, NONE())
                peqs = _cons(DAE.EQUATION(DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT), rhs, DAE.emptyElementSource), peqs)
              end
               #=  toplevel flat state machines need to \"self-reset\" at their first clock tick. After that reset is always false
               =#
               #=  Boolean preRef.init(start=true) = false
               =#
               #=  preRef.reset = previous(preRef.init)
               =#
               #=  input Boolean active \"true if the state machine is active\";
               =#
               #=  set to \"true\", since toplevel state machines is always active
               =#
               #=  We have an enclosing state: propagate reset handling and activation handling to refined state machine
               =#
               #=  initial state of enclosing flat state machine
               =#
               #=  cref prefix for semantics equations governing enclosing SM
               =#
               #=  Position of enclosing state in enclosing flat state machine
               =#
               #=  == Create equation for SMS_PRE.initStateRef.reset ==
               =#
               #=  SMS_PRE.enclosingFlatSMInitStateRef.activeState == posOfEnclosingSMComp
               =#
               #=  SMS_PRE.enclosingFlatSMInitStateRef.activeReset and SMS_PRE.enclosingFlatSMInitStateRef.activeState == posOfEnclosingSMComp
               =#
               #=  SMS_PRE.initStateRef.reset = SMS_PRE.enclosingFlatSMInitStateRef.activeResetStates[posOfEnclosingSMComp]
               =#
               #=    or (SMS_PRE.enclosingFlatSMInitStateRef.activeReset and SMS_PRE.enclosingFlatSMInitStateRef.activeState == posOfEnclosingSMComp)
               =#
               #=  == Create equation for SMS_PRE.initStateRef.active ==
               =#
               #=  SMS_PRE.initStateRef.active = SMS_PRE.enclosingFlatSMInitStateRef.activeState == posOfEnclosingSMComp
               =#
               #=  Decorate state with additional information
               =#
              for i in 1:arrayLength(smComps)
                @match DAE.SM_COMP(componentRef = stateRef) = arrayGet(smComps, i)
                (activePlotIndicatorVar, activePlotIndicatorEqn) = createActiveIndicator(stateRef, preRef, i)
                pvars = _cons(activePlotIndicatorVar, pvars)
                peqs = _cons(activePlotIndicatorEqn, peqs)
                @match DAE.VAR(componentRef = activePlotIndicatorRef) = activePlotIndicatorVar
                (ticksInStateVar, ticksInStateEqn) = createTicksInStateIndicator(stateRef, activePlotIndicatorRef)
                pvars = _cons(ticksInStateVar, pvars)
                peqs = _cons(ticksInStateEqn, peqs)
                (timeEnteredStateVar, timeEnteredStateEqn) = createTimeEnteredStateIndicator(stateRef, activePlotIndicatorRef)
                (timeInStateVar, timeInStateEqn) = createTimeInStateIndicator(stateRef, activePlotIndicatorRef, timeEnteredStateVar)
                pvars = _cons(timeEnteredStateVar, _cons(timeInStateVar, pvars))
                peqs = _cons(timeEnteredStateEqn, _cons(timeInStateEqn, peqs))
              end
               #=  Add indication for plotting whether a state is active or not (stateRef.active)
               =#
               #=  Add ticksInState counter (stateRef.$ticksInState = if stateRef.active then previous(stateRef.$ticksInState) + 1 else 0)
               =#
               #=  == Add timeInState Indicator (stateRef.$timeInState(start=0)) ==
               =#
               #=  Auxiliary variable holding time when state was entred (stateRef.$timeEnteredState(start=0)
               =#
               #=  stateRef.$timeEnteredState = if previous(stateRef.active) == false and stateRef.active == true then sample(time) else previous(stateRef.$timeEnteredState)
               =#
               #=  stateRef.$timeInState = if stateRef.active then sample(time) - stateRef.$timeEnteredState else 0
               =#
              outFlatSmSemantics = FLAT_SM_SEMANTICS(ident, smComps, t, c, smvars, smknowns, smeqs, pvars, peqs, inEnclosingStateCrefOption)
          outFlatSmSemantics
        end

         #= 
        Author: BTH
        Helper function to addPropagationEquations.
        Create variable that indicates the time duration since a transition was made to the currently active state =#
        function createTimeInStateIndicator(stateRef::DAE.ComponentRef #= cref of state to which timeInState variable shall be added =#, stateActiveRef::DAE.ComponentRef #= cref of active indicator corresponding to stateRef =#, timeEnteredStateVar::DAE.Element #= Auxiliary variable generated in createTimeEnteredStateIndicator(..) =#) ::Tuple{DAE.Element, DAE.Element} 
              local timeInStateEqn::DAE.Element
              local timeInStateVar::DAE.Element

              local timeInStateRef::DAE.ComponentRef
              local timeEnteredStateRef::DAE.ComponentRef
              local ty::DAE.Type
              local timeInStateExp::DAE.Exp
              local timeEnteredStateExp::DAE.Exp
              local stateActiveExp::DAE.Exp
              local expCond::DAE.Exp
              local expSampleTime::DAE.Exp
              local expThen::DAE.Exp
              local expElse::DAE.Exp

               #=  Create Variable stateRef.$timeEnteredState
               =#
              timeInStateRef = qCref("timeInState", DAE.T_REAL_DEFAULT, nil, stateRef)
              timeInStateVar = createVarWithDefaults(timeInStateRef, DAE.DISCRETE(), DAE.T_REAL_DEFAULT, nil)
              timeInStateVar = setVarFixedStartValue(timeInStateVar, DAE.RCONST(0))
              timeInStateExp = DAE.CREF(timeInStateRef, DAE.T_REAL_DEFAULT)
              @match DAE.VAR(componentRef = timeEnteredStateRef, ty = ty) = timeEnteredStateVar
              timeEnteredStateExp = DAE.CREF(timeEnteredStateRef, ty)
              stateActiveExp = Expression.crefExp(stateActiveRef)
               #=  == $timeInState = if active then sample(time) - $timeEnteredState else 0; ==
               =#
               #=  active
               =#
              expCond = Expression.crefExp(stateActiveRef)
               #=  sample(time)
               =#
              expSampleTime = DAE.CALL(Absyn.IDENT("sample"), list(DAE.CREF(DAE.CREF_IDENT("time", DAE.T_REAL_DEFAULT, nil), DAE.T_REAL_DEFAULT), DAE.CLKCONST(DAE.INFERRED_CLOCK())), DAE.callAttrBuiltinImpureReal)
               #=  sample(time) - $timeEnteredState
               =#
              expThen = DAE.BINARY(expSampleTime, DAE.SUB(DAE.T_REAL_DEFAULT), timeEnteredStateExp)
               #=  0
               =#
              expElse = DAE.RCONST(0)
               #=  $timeInState = if active then sample(time) - $timeEnteredState else 0;
               =#
              timeInStateEqn = DAE.EQUATION(timeInStateExp, DAE.IFEXP(expCond, expThen, expElse), DAE.emptyElementSource)
          (timeInStateVar, timeInStateEqn)
        end

         #= 
        Author: BTH
        Helper function to addPropagationEquations.
        Create auxiliary variable that remembers the time in which a state is entered =#
        function createTimeEnteredStateIndicator(stateRef::DAE.ComponentRef #= cref of state to which timeEnteredState variable shall be added =#, stateActiveRef::DAE.ComponentRef #= cref of active indicator corresponding to stateRef =#) ::Tuple{DAE.Element, DAE.Element} 
              local timeEnteredStateEqn::DAE.Element
              local timeEnteredStateVar::DAE.Element

              local timeEnteredStateRef::DAE.ComponentRef
              local timeEnteredStateExp::DAE.Exp
              local stateActiveExp::DAE.Exp
              local expCond::DAE.Exp
              local expThen::DAE.Exp
              local expElse::DAE.Exp

               #=  Create Variable stateRef.$timeEnteredState
               =#
              timeEnteredStateRef = qCref("timeEnteredState", DAE.T_REAL_DEFAULT, nil, stateRef)
              timeEnteredStateVar = createVarWithDefaults(timeEnteredStateRef, DAE.DISCRETE(), DAE.T_REAL_DEFAULT, nil)
              timeEnteredStateVar = setVarFixedStartValue(timeEnteredStateVar, DAE.RCONST(0))
              timeEnteredStateExp = DAE.CREF(timeEnteredStateRef, DAE.T_REAL_DEFAULT)
              stateActiveExp = Expression.crefExp(stateActiveRef)
               #=  == $timeEnteredState = if previous(active) == false and active == true then sample(time) else previous($timeEnteredState); ==
               =#
               #=  previous(active) == false and active == true
               =#
              expCond = DAE.LBINARY(DAE.RELATION(DAE.CALL(Absyn.IDENT("previous"), list(stateActiveExp), DAE.callAttrBuiltinImpureBool), DAE.EQUAL(DAE.T_BOOL_DEFAULT), DAE.BCONST(false), -1, NONE()), DAE.AND(DAE.T_BOOL_DEFAULT), DAE.RELATION(stateActiveExp, DAE.EQUAL(DAE.T_BOOL_DEFAULT), DAE.BCONST(true), -1, NONE()))
               #=  previous(active) == false
               =#
               #=  and
               =#
               #=  active == true
               =#
               #=  sample(time)
               =#
              expThen = DAE.CALL(Absyn.IDENT("sample"), list(DAE.CREF(DAE.CREF_IDENT("time", DAE.T_REAL_DEFAULT, nil), DAE.T_REAL_DEFAULT), DAE.CLKCONST(DAE.INFERRED_CLOCK())), DAE.callAttrBuiltinImpureReal)
               #=  previous($timeEnteredState)
               =#
              expElse = DAE.CALL(Absyn.IDENT("previous"), list(timeEnteredStateExp), DAE.callAttrBuiltinImpureReal)
               #=  $timeEnteredState = if previous(active) == false and active == true then sample(time) else previous($timeEnteredState);
               =#
              timeEnteredStateEqn = DAE.EQUATION(timeEnteredStateExp, DAE.IFEXP(expCond, expThen, expElse), DAE.emptyElementSource)
          (timeEnteredStateVar, timeEnteredStateEqn)
        end

         #= 
        Author: BTH
        Helper function to addPropagationEquations.
        Create variable that counts ticks within a state =#
        function createTicksInStateIndicator(stateRef::DAE.ComponentRef #= cref of state to which ticksInState counter shall be added =#, stateActiveRef::DAE.ComponentRef #= cref of active indicator corresponding to stateRef =#) ::Tuple{DAE.Element, DAE.Element} 
              local ticksInStateEqn::DAE.Element
              local ticksInStateVar::DAE.Element

              local ticksInStateRef::DAE.ComponentRef
              local ticksInStateExp::DAE.Exp
              local expCond::DAE.Exp
              local expThen::DAE.Exp
              local expElse::DAE.Exp

               #=  Create Variable stateRef.$ticksInState
               =#
              ticksInStateRef = qCref("ticksInState", DAE.T_INTEGER_DEFAULT, nil, stateRef)
              ticksInStateVar = createVarWithDefaults(ticksInStateRef, DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, nil)
              ticksInStateVar = setVarFixedStartValue(ticksInStateVar, DAE.ICONST(0))
               #=  $ticksInState = if active then previous($ticksInState) + 1 else 0;
               =#
              ticksInStateExp = DAE.CREF(ticksInStateRef, DAE.T_INTEGER_DEFAULT)
              expCond = Expression.crefExp(stateActiveRef)
               #=  previous($ticksInState) + 1
               =#
              expThen = DAE.BINARY(DAE.CALL(Absyn.IDENT("previous"), list(ticksInStateExp), DAE.callAttrBuiltinImpureInteger), DAE.ADD(DAE.T_INTEGER_DEFAULT), DAE.ICONST(1))
              expElse = DAE.ICONST(0)
              ticksInStateEqn = DAE.EQUATION(ticksInStateExp, DAE.IFEXP(expCond, expThen, expElse), DAE.emptyElementSource)
          (ticksInStateVar, ticksInStateEqn)
        end

         #= 
        Author: BTH
        Helper function to addPropagationEquations.
        Create indication (e.g., for plotting) whether a state is active or not =#
        function createActiveIndicator(stateRef::DAE.ComponentRef #= cref of state to which activation indication shall be added =#, preRef::DAE.ComponentRef #= cref of prefix where variables of governing semantic equations for stateRef are located =#, i::ModelicaInteger #= index of state within flat state machine state array =#) ::Tuple{DAE.Element, DAE.Element} 
              local eqn::DAE.Element
              local activePlotIndicatorVar::DAE.Element

              local activeRef::DAE.ComponentRef
              local activePlotIndicatorRef::DAE.ComponentRef
              local activeStateRef::DAE.ComponentRef
              local andExp::DAE.Exp
              local eqExp::DAE.Exp

               #=  Create Variable stateRef.active
               =#
               #=  FIXME Use name that cannot possible conflict with user variable (or is .active reserved for state machines?)
               =#
              activePlotIndicatorRef = qCref("active", DAE.T_BOOL_DEFAULT, nil, stateRef)
              activePlotIndicatorVar = createVarWithStartValue(activePlotIndicatorRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, DAE.BCONST(false), nil)
               #=  stateRef.active := SMS_PRE.initialState.active and (SMS_PRE.initialState.activeState==i)
               =#
              activeRef = qCref("active", DAE.T_BOOL_DEFAULT, nil, preRef)
              activeStateRef = qCref("activeState", DAE.T_INTEGER_DEFAULT, nil, preRef)
               #=  SMS_PRE.initialState.activeState==i
               =#
              eqExp = DAE.RELATION(DAE.CREF(activeStateRef, DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(i), -1, NONE())
               #=  SMS_PRE.initialState.active and (SMS_PRE.initialState.activeState==i)
               =#
              andExp = DAE.LBINARY(DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT), DAE.AND(DAE.T_BOOL_DEFAULT), eqExp)
              eqn = DAE.EQUATION(DAE.CREF(activePlotIndicatorRef, DAE.T_BOOL_DEFAULT), andExp, DAE.emptyElementSource)
          (activePlotIndicatorVar, eqn)
        end

         #= 
        Author: BTH
        Set a fixed start value to a variable
         =#
        function setVarFixedStartValue(inVar::DAE.Element, inExp::DAE.Exp) ::DAE.Element 
              local outVar::DAE.Element

              local vao::Option{DAE.VariableAttributes}

              @match DAE.VAR(variableAttributesOption = vao) = inVar
              vao = DAEUtil.setStartAttrOption(vao, SOME(inExp))
              vao = DAEUtil.setFixedAttr(vao, SOME(DAE.BCONST(true)))
              outVar = DAEUtil.setVariableAttributes(inVar, vao)
          outVar
        end

         #= 
        Author: BTH
        Helper function to flatSmToDataFlow.
        Create variables/parameters and equations for defining the state machine semantic (SMS) equations.
         =#
        function basicFlatSmSemantics(ident::DAE.Ident, q::List{<:DAE.Element} #= state components =#, inTransitions::List{<:DAE.Element}) ::FlatSmSemantics 
              local flatSmSemantics::FlatSmSemantics

              local crefInitialState::DAE.ComponentRef
              local preRef::DAE.ComponentRef
               #=  Modeling variables and parameters/constants
               =#
              local defaultIntVar::DAE.Element
              local defaultBoolVar::DAE.Element
              local vars::List{DAE.Element} #= SMS veriables =#
              local knowns::List{DAE.Element} #= SMS constants/parameters =#
              local i::ModelicaInteger
              local preRef::DAE.ComponentRef
              local cref::DAE.ComponentRef
              local nStatesRef::DAE.ComponentRef
              local activeRef::DAE.ComponentRef
              local resetRef::DAE.ComponentRef
              local selectedStateRef::DAE.ComponentRef
              local selectedResetRef::DAE.ComponentRef
              local firedRef::DAE.ComponentRef
              local activeStateRef::DAE.ComponentRef
              local activeResetRef::DAE.ComponentRef
              local nextStateRef::DAE.ComponentRef
              local nextResetRef::DAE.ComponentRef
              local stateMachineInFinalStateRef::DAE.ComponentRef
              local var::DAE.Element
              local nStatesVar::DAE.Element
              local activeVar::DAE.Element
              local resetVar::DAE.Element
              local selectedStateVar::DAE.Element
              local selectedResetVar::DAE.Element
              local firedVar::DAE.Element
              local activeStateVar::DAE.Element
              local activeResetVar::DAE.Element
              local nextStateVar::DAE.Element
              local nextResetVar::DAE.Element
              local stateMachineInFinalStateVar::DAE.Element
               #=  Modeling arrays with size nStates
               =#
              local nStates::ModelicaInteger
              local nStatesDims::DAE.InstDims
              local nStatesArrayBool::DAE.Type
              local activeResetStatesRefs::Array{DAE.ComponentRef}
              local nextResetStatesRefs::Array{DAE.ComponentRef}
              local finalStatesRefs::Array{DAE.ComponentRef}
              local activeResetStatesVars::Array{DAE.Element}
              local nextResetStatesVars::Array{DAE.Element}
              local finalStatesVars::Array{DAE.Element}
               #=  Modeling Transitions \"t\":
               =#
              local t::List{Transition}
              local nTransitions::ModelicaInteger
              local tDims::DAE.InstDims
              local tArrayInteger::DAE.Type
              local tArrayBool::DAE.Type
              local tFromRefs::Array{DAE.ComponentRef}
              local tToRefs::Array{DAE.ComponentRef}
              local tImmediateRefs::Array{DAE.ComponentRef}
              local tResetRefs::Array{DAE.ComponentRef}
              local tSynchronizeRefs::Array{DAE.ComponentRef}
              local tPriorityRefs::Array{DAE.ComponentRef}
              local tFromVars::Array{DAE.Element}
              local tToVars::Array{DAE.Element}
              local tImmediateVars::Array{DAE.Element}
              local tResetVars::Array{DAE.Element}
              local tSynchronizeVars::Array{DAE.Element}
              local tPriorityVars::Array{DAE.Element}
               #=  TRANSITION
               =#
              local from::ModelicaInteger
              local to::ModelicaInteger
              local condition::DAE.Exp
              local immediate::Bool
              local reset::Bool
              local synchronize::Bool
              local priority::ModelicaInteger
               #=  Modeling Conditions \"c\":
               =#
              local cExps::List{DAE.Exp}
              local cRefs::Array{DAE.ComponentRef}
              local cImmediateRefs::Array{DAE.ComponentRef}
              local cVars::Array{DAE.Element}
              local cImmediateVars::Array{DAE.Element}
               #=  Modeling Equations
               =#
              local eqs::List{DAE.Element} #= SMS equations =#
              local selectedStateEqn::DAE.Element
              local selectedResetEqn::DAE.Element
              local firedEqn::DAE.Element
              local activeStateEqn::DAE.Element
              local activeResetEqn::DAE.Element
              local nextStateEqn::DAE.Element
              local nextResetEqn::DAE.Element
              local exp::DAE.Exp
              local rhs::DAE.Exp
              local expCond::DAE.Exp
              local expThen::DAE.Exp
              local expElse::DAE.Exp
              local exp1::DAE.Exp
              local exp2::DAE.Exp
              local expIf::DAE.Exp
              local expLst::List{DAE.Exp}
              local bindExp::Option{DAE.Exp}

               #=  make sure that created vars won't clutter up the variable space
               =#
              @match DAE.SM_COMP(componentRef = crefInitialState) = listHead(q)
              preRef = ComponentReference.crefPrefixString(SMS_PRE, crefInitialState)
              (t, cExps) = createTandC(q, inTransitions)
               #=  print(\"StateMachineFlatten.basicFlatSmSemantics: transitions:\\n\\t\" + stringDelimitList(List.map(t, dumpTransitionStr), \"\\n\\t\") + \"\\n\");
               =#
               #=  print(\"StateMachineFlatten.basicFlatSmSemantics: conditions\\n\\t\" + stringDelimitList(List.map(cExps, ExpressionDump.printExpStr), \"\\n\\t\") + \"\\n\");
               =#
              defaultIntVar = createVarWithDefaults(ComponentReference.makeDummyCref(), DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, nil)
              defaultBoolVar = createVarWithDefaults(ComponentReference.makeDummyCref(), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              knowns = nil
              vars = nil
               #=  ***** Create new variable declarations needed for semantic equations *****
               =#
              nStates = listLength(q)
              nStatesRef = qCref("nState", DAE.T_INTEGER_DEFAULT, nil, preRef)
              nStatesVar = createVarWithDefaults(nStatesRef, DAE.PARAM(), DAE.T_INTEGER_DEFAULT, nil)
              nStatesVar = DAEUtil.setElementVarBinding(nStatesVar, SOME(DAE.ICONST(nStates)))
              knowns = _cons(nStatesVar, knowns)
               #=  parameter Transition t[:] \"Array of transition data sorted in priority\";
               =#
              nTransitions = listLength(t)
              tDims = list(DAE.DIM_INTEGER(nTransitions))
              tArrayInteger = DAE.T_ARRAY(DAE.T_INTEGER_DEFAULT, tDims)
              tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, tDims)
              tFromRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tToRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tImmediateRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tResetRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tSynchronizeRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tPriorityRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              tFromVars = arrayCreate(nTransitions, defaultIntVar)
              tToVars = arrayCreate(nTransitions, defaultIntVar)
              tImmediateVars = arrayCreate(nTransitions, defaultBoolVar)
              tResetVars = arrayCreate(nTransitions, defaultBoolVar)
              tSynchronizeVars = arrayCreate(nTransitions, defaultBoolVar)
              tPriorityVars = arrayCreate(nTransitions, defaultIntVar)
              i = 0
              for t1 in t
                i = i + 1
                @match TRANSITION(from, to, _, immediate, reset, synchronize, priority) = t1
                tFromRefs = arrayUpdate(tFromRefs, i, qCref("tFrom", tArrayInteger, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tFromVars = arrayUpdate(tFromVars, i, createVarWithDefaults(arrayGet(tFromRefs, i), DAE.PARAM(), DAE.T_INTEGER_DEFAULT, tDims))
                tFromVars = arrayUpdate(tFromVars, i, DAEUtil.setElementVarBinding(arrayGet(tFromVars, i), SOME(DAE.ICONST(from))))
                knowns = _cons(arrayGet(tFromVars, i), knowns)
                tToRefs = arrayUpdate(tToRefs, i, qCref("tTo", tArrayInteger, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tToVars = arrayUpdate(tToVars, i, createVarWithDefaults(arrayGet(tToRefs, i), DAE.PARAM(), DAE.T_INTEGER_DEFAULT, tDims))
                tToVars = arrayUpdate(tToVars, i, DAEUtil.setElementVarBinding(arrayGet(tToVars, i), SOME(DAE.ICONST(to))))
                knowns = _cons(arrayGet(tToVars, i), knowns)
                tImmediateRefs = arrayUpdate(tImmediateRefs, i, qCref("tImmediate", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tImmediateVars = arrayUpdate(tImmediateVars, i, createVarWithDefaults(arrayGet(tImmediateRefs, i), DAE.PARAM(), DAE.T_BOOL_DEFAULT, tDims))
                tImmediateVars = arrayUpdate(tImmediateVars, i, DAEUtil.setElementVarBinding(arrayGet(tImmediateVars, i), SOME(DAE.BCONST(immediate))))
                knowns = _cons(arrayGet(tImmediateVars, i), knowns)
                tResetRefs = arrayUpdate(tResetRefs, i, qCref("tReset", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tResetVars = arrayUpdate(tResetVars, i, createVarWithDefaults(arrayGet(tResetRefs, i), DAE.PARAM(), DAE.T_BOOL_DEFAULT, tDims))
                tResetVars = arrayUpdate(tResetVars, i, DAEUtil.setElementVarBinding(arrayGet(tResetVars, i), SOME(DAE.BCONST(reset))))
                knowns = _cons(arrayGet(tResetVars, i), knowns)
                tSynchronizeRefs = arrayUpdate(tSynchronizeRefs, i, qCref("tSynchronize", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tSynchronizeVars = arrayUpdate(tSynchronizeVars, i, createVarWithDefaults(arrayGet(tSynchronizeRefs, i), DAE.PARAM(), DAE.T_BOOL_DEFAULT, tDims))
                tSynchronizeVars = arrayUpdate(tSynchronizeVars, i, DAEUtil.setElementVarBinding(arrayGet(tSynchronizeVars, i), SOME(DAE.BCONST(synchronize))))
                knowns = _cons(arrayGet(tSynchronizeVars, i), knowns)
                tPriorityRefs = arrayUpdate(tPriorityRefs, i, qCref("tPriority", tArrayInteger, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                tPriorityVars = arrayUpdate(tPriorityVars, i, createVarWithDefaults(arrayGet(tPriorityRefs, i), DAE.PARAM(), DAE.T_INTEGER_DEFAULT, tDims))
                tPriorityVars = arrayUpdate(tPriorityVars, i, DAEUtil.setElementVarBinding(arrayGet(tPriorityVars, i), SOME(DAE.ICONST(priority))))
                knowns = _cons(arrayGet(tPriorityVars, i), knowns)
              end
               #=  input Boolean c[size(t,1)] \"Transition conditions sorted in priority\";
               =#
               #=  input Boolean cImmediate[size(t,1)];
               =#
               #= /* IMPLEMENTATION NOTE in respect to MLS: cImmediate is introduced in order to delay transitions by simply doing c[i] = previous(cImmediate[i]) for delayed transitons.
                   Now, all c[i] can be treated as immediate transitions. Hence, different to MLS 17.3.4 there are no distinguished equations for 'immediate' or 'delayed' transitions needed.
                   This avoids seemingly algebraic dependency loops for delayed transitions that are introduced if MLS 17.3.4 equations are implemented directly
                   (this is because in MLS 17.3.4 delayed transitions c[i] appear in a non-delayed form in the equation for 'immediate';
                   actually, MLS 17.3.4 doesn't introduce 'real' algebraic loops for delayed transitions since if-conditions \"exclude\" the paths that would lead to algebraic loops during execution;
                   however, it requires sophisticated analysis for a tool to statically deduce that fact)
                */ =#
              cRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              cImmediateRefs = arrayCreate(nTransitions, ComponentReference.makeDummyCref())
              cVars = arrayCreate(nTransitions, defaultBoolVar)
              cImmediateVars = arrayCreate(nTransitions, defaultBoolVar)
              i = 0
              for exp in cExps
                i = i + 1
                cRefs = arrayUpdate(cRefs, i, qCref("c", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                cImmediateRefs = arrayUpdate(cImmediateRefs, i, qCref("cImmediate", tArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                cVars = arrayUpdate(cVars, i, createVarWithDefaults(arrayGet(cRefs, i), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, tDims))
                cImmediateVars = arrayUpdate(cImmediateVars, i, createVarWithStartValue(arrayGet(cImmediateRefs, i), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, DAE.BCONST(false), tDims))
                vars = _cons(arrayGet(cVars, i), vars)
                vars = _cons(arrayGet(cImmediateVars, i), vars)
              end
               #=  TODO Binding probably needs to be turned into a proper equation. Done below
               =#
               #=  cVars := arrayUpdate(cVars, i, BackendVariable.setBindExp(arrayGet(cVars,i), SOME(exp)));
               =#
               #= input Boolean active \"true if the state machine is active\";
               =#
              activeRef = qCref("active", DAE.T_BOOL_DEFAULT, nil, preRef)
              activeVar = createVarWithDefaults(activeRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              vars = _cons(activeVar, vars)
               #= input Boolean reset \"true when the state machine should be reset\";
               =#
              resetRef = qCref("reset", DAE.T_BOOL_DEFAULT, nil, preRef)
              resetVar = createVarWithDefaults(resetRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              vars = _cons(resetVar, vars)
               #= Integer selectedState
               =#
              selectedStateRef = qCref("selectedState", DAE.T_INTEGER_DEFAULT, nil, preRef)
              selectedStateVar = createVarWithDefaults(selectedStateRef, DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, nil)
              vars = _cons(selectedStateVar, vars)
               #= Boolean selectedReset
               =#
              selectedResetRef = qCref("selectedReset", DAE.T_BOOL_DEFAULT, nil, preRef)
              selectedResetVar = createVarWithDefaults(selectedResetRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              vars = _cons(selectedResetVar, vars)
               #=  Integer fired
               =#
              firedRef = qCref("fired", DAE.T_INTEGER_DEFAULT, nil, preRef)
              firedVar = createVarWithDefaults(firedRef, DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, nil)
              vars = _cons(firedVar, vars)
               #=  output Integer activeState
               =#
              activeStateRef = qCref("activeState", DAE.T_INTEGER_DEFAULT, nil, preRef)
              activeStateVar = createVarWithDefaults(activeStateRef, DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, nil)
              vars = _cons(activeStateVar, vars)
               #=  output Boolean activeReset
               =#
              activeResetRef = qCref("activeReset", DAE.T_BOOL_DEFAULT, nil, preRef)
              activeResetVar = createVarWithDefaults(activeResetRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              vars = _cons(activeResetVar, vars)
               #=  Integer nextState
               =#
              nextStateRef = qCref("nextState", DAE.T_INTEGER_DEFAULT, nil, preRef)
              nextStateVar = createVarWithStartValue(nextStateRef, DAE.DISCRETE(), DAE.T_INTEGER_DEFAULT, DAE.ICONST(0), nil)
               #=  is state -> start value, but value not specified in spec
               =#
              vars = _cons(nextStateVar, vars)
               #=  Boolean nextReset
               =#
              nextResetRef = qCref("nextReset", DAE.T_BOOL_DEFAULT, nil, preRef)
              nextResetVar = createVarWithStartValue(nextResetRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, DAE.BCONST(false), nil)
               #=  is state -> start value, but not value specified in spec
               =#
              vars = _cons(nextResetVar, vars)
               #=  ***** arrays with size nStates *****
               =#
              nStatesDims = list(DAE.DIM_INTEGER(nStates))
              nStatesArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, nStatesDims)
               #= output Boolean activeResetStates[nStates]
               =#
              activeResetStatesRefs = arrayCreate(nStates, ComponentReference.makeDummyCref())
              activeResetStatesVars = arrayCreate(nStates, defaultBoolVar)
              for i in 1:nStates
                activeResetStatesRefs = arrayUpdate(activeResetStatesRefs, i, qCref("activeResetStates", nStatesArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                activeResetStatesVars = arrayUpdate(activeResetStatesVars, i, createVarWithDefaults(arrayGet(activeResetStatesRefs, i), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nStatesDims))
                vars = _cons(arrayGet(activeResetStatesVars, i), vars)
              end
               #=  Boolean nextResetStates[nStates]
               =#
              nextResetStatesRefs = arrayCreate(nStates, ComponentReference.makeDummyCref())
              nextResetStatesVars = arrayCreate(nStates, defaultBoolVar)
              for i in 1:nStates
                nextResetStatesRefs = arrayUpdate(nextResetStatesRefs, i, qCref("nextResetStates", nStatesArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                nextResetStatesVars = arrayUpdate(nextResetStatesVars, i, createVarWithStartValue(arrayGet(nextResetStatesRefs, i), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, DAE.BCONST(false), nStatesDims))
                vars = _cons(arrayGet(nextResetStatesVars, i), vars)
              end
               #=  Boolean finalStates[nStates]
               =#
              finalStatesRefs = arrayCreate(nStates, ComponentReference.makeDummyCref())
              finalStatesVars = arrayCreate(nStates, defaultBoolVar)
              for i in 1:nStates
                finalStatesRefs = arrayUpdate(finalStatesRefs, i, qCref("finalStates", nStatesArrayBool, list(DAE.INDEX(DAE.ICONST(i))), preRef))
                finalStatesVars = arrayUpdate(finalStatesVars, i, createVarWithDefaults(arrayGet(finalStatesRefs, i), DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nStatesDims))
                vars = _cons(arrayGet(finalStatesVars, i), vars)
              end
               #=  Boolean stateMachineInFinalState
               =#
              stateMachineInFinalStateRef = qCref("stateMachineInFinalState", DAE.T_BOOL_DEFAULT, nil, preRef)
              stateMachineInFinalStateVar = createVarWithDefaults(stateMachineInFinalStateRef, DAE.DISCRETE(), DAE.T_BOOL_DEFAULT, nil)
              vars = _cons(stateMachineInFinalStateVar, vars)
               #=  ***** Create new governing equations *****
               =#
              eqs = nil
               #= input Boolean c[size(t,1)] \"Transition conditions sorted in priority\";
               =#
               #=  Delayed transitions are realized by \"c[i] = previous(cImmediate[i])\"
               =#
              i = 0
              for cExp in cExps
                i = i + 1
                exp = DAE.CREF(arrayGet(cImmediateRefs, i), DAE.T_BOOL_DEFAULT)
                eqs = _cons(DAE.EQUATION(exp, cExp, DAE.emptyElementSource), eqs)
                exp1 = DAE.CREF(arrayGet(cRefs, i), DAE.T_BOOL_DEFAULT)
                @match DAE.VAR(binding = bindExp) = arrayGet(tImmediateVars, i)
                rhs = if Util.applyOptionOrDefault(bindExp, (DAE.BCONST(true)) -> Expression.expEqual(inExp1 = DAE.BCONST(true)), false)
                      exp
                    else
                      DAE.CALL(Absyn.IDENT("previous"), list(exp), DAE.callAttrBuiltinImpureBool)
                    end
                eqs = _cons(DAE.EQUATION(exp1, rhs, DAE.emptyElementSource), eqs)
              end
               #=  Check whether it is an immediate or an delayed transition
               =#
               #=  immediate transition
               =#
               #=  delayed transition
               =#
               #=  Integer selectedState = if reset then 1 else previous(nextState);
               =#
              exp = DAE.CREF(selectedStateRef, DAE.T_INTEGER_DEFAULT)
              expCond = DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.ICONST(1)
              expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(nextStateRef, DAE.T_INTEGER_DEFAULT)), DAE.callAttrBuiltinImpureInteger)
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              selectedStateEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(selectedStateEqn, eqs)
               #=  Boolean selectedReset = if reset then true else previous(nextReset);
               =#
              exp = DAE.CREF(selectedResetRef, DAE.T_BOOL_DEFAULT)
              expCond = DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.BCONST(true)
              expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(nextResetRef, DAE.T_BOOL_DEFAULT)), DAE.callAttrBuiltinImpureBool)
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              selectedResetEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(selectedResetEqn, eqs)
               #= /*  Following semantic activation equations are specified in MLS 17.3.4:
                      Integer delayed= max(if (if not t[i].immediate and t[i].from == nextState then c[i] else false) then i else 0 for i in 1:size(t,1));
                      Integer immediate = max(if (if t[i].immediate and t[i].from == selectedState then c[i] else false) then i else 0 for i in 1:size(t,1));
                      Integer fired = max(previous(delayed), immediate);
                    This implementation doesn't implement them directly.
                    Recall that delayed transitions have been previously modeled as c[i] = previous(cImmediate[i]), so that the firing conditions is simplified to:
                      Integer fired = max(if (if t[i].from == selectedState then c[i] else false) then i else 0 for i in 1: size(t ,1)); */ =#
              exp = DAE.CREF(firedRef, DAE.T_INTEGER_DEFAULT)
              expLst = nil
              for i in 1:nTransitions
                expCond = DAE.RELATION(DAE.CREF(arrayGet(tFromRefs, i), DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.CREF(selectedStateRef, DAE.T_INTEGER_DEFAULT), -1, NONE())
                expThen = DAE.CREF(arrayGet(cRefs, i), DAE.T_BOOL_DEFAULT)
                expElse = DAE.BCONST(false)
                expIf = DAE.IFEXP(expCond, expThen, expElse)
                expLst = _cons(DAE.IFEXP(expIf, DAE.ICONST(i), DAE.ICONST(0)), expLst)
              end
               #=  t[i].from == selectedState:
               =#
               #=  if (t[i].from == selectedState) then (c[i]) else (false)
               =#
               #=  if (if t[i].from == selectedState then c[i] else false) then i else 0
               =#
              rhs = if listLength(expLst) > 1
                    DAE.CALL(Absyn.IDENT("max"), list(Expression.makeScalarArray(expLst, DAE.T_INTEGER_DEFAULT)), DAE.callAttrBuiltinInteger)
                  else
                    listHead(expLst)
                  end
               #=  runtime can't handle 'max({x})'. Hence, replace 'max({x})' by 'x'.
               =#
              firedEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(firedEqn, eqs)
               #=  output Integer activeState = if reset then 1 elseif fired > 0 then t[fired].to else selectedState;
               =#
              exp = DAE.CREF(activeStateRef, DAE.T_INTEGER_DEFAULT)
              expCond = DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.ICONST(1)
               #=  fired > 0:
               =#
              exp1 = DAE.RELATION(DAE.CREF(firedRef, DAE.T_INTEGER_DEFAULT), DAE.GREATER(DAE.T_INTEGER_DEFAULT), DAE.ICONST(0), -1, NONE())
               #=  t[fired].to:
               =#
              exp2 = DAE.CREF(qCref("tTo", tArrayInteger, list(DAE.INDEX(DAE.CREF(firedRef, DAE.T_INTEGER_DEFAULT))), preRef), DAE.T_INTEGER_DEFAULT)
               #=  elsif fired > 0 then t[fired].to else selectedState:
               =#
              expElse = DAE.IFEXP(exp1, exp2, DAE.CREF(selectedStateRef, DAE.T_INTEGER_DEFAULT))
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              activeStateEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(activeStateEqn, eqs)
               #=  output Boolean activeReset = if reset then true elseif fired > 0 then t[fired].reset else selectedReset;
               =#
              exp = DAE.CREF(activeResetRef, DAE.T_BOOL_DEFAULT)
              expCond = DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.BCONST(true)
               #=  fired > 0:
               =#
              exp1 = DAE.RELATION(DAE.CREF(firedRef, DAE.T_INTEGER_DEFAULT), DAE.GREATER(DAE.T_INTEGER_DEFAULT), DAE.ICONST(0), -1, NONE())
               #=  t[fired].reset:
               =#
              exp2 = DAE.CREF(qCref("tReset", tArrayBool, list(DAE.INDEX(DAE.CREF(firedRef, DAE.T_INTEGER_DEFAULT))), preRef), DAE.T_INTEGER_DEFAULT)
               #=  elseif fired > 0 then t[fired].reset else selectedReset:
               =#
              expElse = DAE.IFEXP(exp1, exp2, DAE.CREF(selectedResetRef, DAE.T_BOOL_DEFAULT))
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              activeResetEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(activeResetEqn, eqs)
               #=  Integer nextState = if active then activeState else previous(nextState);
               =#
              exp = DAE.CREF(nextStateRef, DAE.T_INTEGER_DEFAULT)
              expCond = DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.CREF(activeStateRef, DAE.T_INTEGER_DEFAULT)
              expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(nextStateRef, DAE.T_INTEGER_DEFAULT)), DAE.callAttrBuiltinImpureInteger)
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              nextStateEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(nextStateEqn, eqs)
               #=  Boolean nextReset = if active then false else previous(nextReset);
               =#
              exp = DAE.CREF(nextResetRef, DAE.T_BOOL_DEFAULT)
              expCond = DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT)
              expThen = DAE.BCONST(false)
              expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(nextResetRef, DAE.T_BOOL_DEFAULT)), DAE.callAttrBuiltinImpureBool)
              rhs = DAE.IFEXP(expCond, expThen, expElse)
              nextResetEqn = DAE.EQUATION(exp, rhs, DAE.emptyElementSource)
              eqs = _cons(nextResetEqn, eqs)
               #=  output Boolean activeResetStates[nStates] = {if reset then true else previous(nextResetStates[i]) for i in 1:nStates};
               =#
              for i in 1:nStates
                exp = DAE.CREF(arrayGet(activeResetStatesRefs, i), DAE.T_BOOL_DEFAULT)
                expCond = DAE.CREF(resetRef, DAE.T_BOOL_DEFAULT)
                expThen = DAE.BCONST(true)
                expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(arrayGet(nextResetStatesRefs, i), DAE.T_BOOL_DEFAULT)), DAE.callAttrBuiltinImpureBool)
                rhs = DAE.IFEXP(expCond, expThen, expElse)
                eqs = _cons(DAE.EQUATION(exp, rhs, DAE.emptyElementSource), eqs)
              end
               #=  Boolean nextResetStates[nStates] = if active then {if selectedState == i then false else activeResetStates[i] for i in 1:nStates} else previous(nextResetStates);
               =#
               #=  2017-10-10 BTH NOTE: Replaced \"selectedState\" from MLS v3.3r1 by \"activeState\"!!!
               =#
              for i in 1:nStates
                exp = DAE.CREF(arrayGet(nextResetStatesRefs, i), DAE.T_BOOL_DEFAULT)
                expCond = DAE.CREF(activeRef, DAE.T_BOOL_DEFAULT)
                exp1 = DAE.RELATION(DAE.CREF(activeStateRef, DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(i), -1, NONE())
                expThen = DAE.IFEXP(exp1, DAE.BCONST(false), DAE.CREF(arrayGet(activeResetStatesRefs, i), DAE.T_BOOL_DEFAULT))
                expElse = DAE.CALL(Absyn.IDENT("previous"), list(DAE.CREF(arrayGet(nextResetStatesRefs, i), DAE.T_BOOL_DEFAULT)), DAE.callAttrBuiltinImpureBool)
                rhs = DAE.IFEXP(expCond, expThen, expElse)
                eqs = _cons(DAE.EQUATION(exp, rhs, DAE.emptyElementSource), eqs)
              end
               #= /*===== MLS v3.3r1 specification semantics (probably wrong!): ===== */ =#
               #=  selectedState == i:
               =#
               #= exp1 := DAE.RELATION(DAE.CREF(selectedStateRef, DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(i),-1, NONE());
               =#
               #=  if (selectedState == i) then false else activeResetStates[i]
               =#
               #= expThen := DAE.IFEXP(exp1, DAE.BCONST(false), DAE.CREF(arrayGet(activeResetStatesRefs,i), DAE.T_BOOL_DEFAULT));
               =#
               #= /*===== FIXED semantics: ===== */ =#
               #=  activeState == i:
               =#
               #=  if (activeState == i) then false else activeResetStates[i]
               =#
               #= /*========== */ =#
               #=  previous(nextResetStates[i])
               =#
               #=  if active then (if selectedState == i then false else activeResetStates[i]) else previous(nextResetStates[i])
               =#
               #=  Ignore:
               =#
               #= rhs := DAE.LUNARY(DAE.NOT(DAE.T_BOOL_DEFAULT), DAE.CALL(Absyn.IDENT(\"previous\"), {DAE.CREF(arrayGet(nextResetStatesRefs,i), DAE.T_BOOL_DEFAULT)}, DAE.callAttrBuiltinImpureBool));
               =#
               #=  Boolean finalStates[nStates] = {max(if t[j].from == i then 1 else 0 for j in 1:size(t,1)) == 0 for i in 1:nStates};
               =#
              for i in 1:nStates
                exp = DAE.CREF(arrayGet(finalStatesRefs, i), DAE.T_BOOL_DEFAULT)
                expLst = nil
                for j in 1:nTransitions
                  expCond = DAE.RELATION(DAE.CREF(arrayGet(tFromRefs, j), DAE.T_INTEGER_DEFAULT), DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(i), -1, NONE())
                  expLst = _cons(DAE.IFEXP(expCond, DAE.ICONST(1), DAE.ICONST(0)), expLst)
                end
                exp1 = if listLength(expLst) > 1
                      DAE.CALL(Absyn.IDENT("max"), list(Expression.makeScalarArray(expLst, DAE.T_INTEGER_DEFAULT)), DAE.callAttrBuiltinInteger)
                    else
                      listHead(expLst)
                    end
                rhs = DAE.RELATION(exp1, DAE.EQUAL(DAE.T_INTEGER_DEFAULT), DAE.ICONST(0), -1, NONE())
                eqs = _cons(DAE.EQUATION(exp, rhs, DAE.emptyElementSource), eqs)
              end
               #=  t[j].from == i:
               =#
               #=  if t[j].from == i then 1 else 0:
               =#
               #=  max(if t[j].from == i then 1 else 0 for j in 1:size(t,1))
               =#
               #=  runtime can't handle 'max({x})'. Hence, replace 'max({x})' by 'x'.
               =#
               #=  max(if t[j].from == i then 1 else 0 for j in 1:size(t,1)) == 0
               =#
               #=  Boolean stateMachineInFinalState = finalStates[activeState];
               =#
              exp = DAE.CREF(stateMachineInFinalStateRef, DAE.T_BOOL_DEFAULT)
              rhs = DAE.CREF(qCref("finalStates", nStatesArrayBool, list(DAE.INDEX(DAE.CREF(activeStateRef, DAE.T_INTEGER_DEFAULT))), preRef), DAE.T_BOOL_DEFAULT)
              eqs = _cons(DAE.EQUATION(exp, rhs, DAE.emptyElementSource), eqs)
               #=  Now return the semantics equations of the flat state machine and associated variables and parameters
               =#
              flatSmSemantics = FLAT_SM_SEMANTICS(ident, listArray(q), t, cExps, vars, knowns, eqs, nil, nil, NONE())
          flatSmSemantics
        end

         #= 
        Author: BTH
        Helper function to basicFlatSmSemantics =#
        function qCref(ident::DAE.Ident, identType::DAE.Type #= type of the identifier, without considering the subscripts =#, subscriptLst::List{<:DAE.Subscript}, componentRef::DAE.ComponentRef) ::DAE.ComponentRef 
              local outQual::DAE.ComponentRef

              outQual = ComponentReference.joinCrefs(componentRef, DAE.CREF_IDENT(ident, identType, subscriptLst))
          outQual
        end

         #= 
        Author: BTH
        Create a DAE.VAR with some defaults =#
        function createVarWithDefaults(componentRef::DAE.ComponentRef, kind::DAE.VarKind, ty::DAE.Type, dims::DAE.InstDims) ::DAE.Element 
              local var::DAE.Element

              var = DAE.VAR(componentRef, kind, DAE.BIDIR(), DAE.NON_PARALLEL(), DAE.PUBLIC(), ty, NONE(), dims, DAE.NON_CONNECTOR(), DAE.emptyElementSource, NONE(), NONE(), Absyn.NOT_INNER_OUTER())
               #= /* VariableAttributes */ =#
          var
        end

         #= 
        Author: BTH
        Create a DAE.VAR with fixed start value and some defaults =#
        function createVarWithStartValue(componentRef::DAE.ComponentRef, kind::DAE.VarKind, ty::DAE.Type, startExp::DAE.Exp, dims::DAE.InstDims) ::DAE.Element 
              local outVar::DAE.Element

              local var::DAE.Element

              var = DAE.VAR(componentRef, kind, DAE.BIDIR(), DAE.NON_PARALLEL(), DAE.PUBLIC(), ty, NONE(), dims, DAE.NON_CONNECTOR(), DAE.emptyElementSource, NONE(), NONE(), Absyn.NOT_INNER_OUTER())
               #= /* VariableAttributes */ =#
              outVar = setVarFixedStartValue(var, startExp)
          outVar
        end

         #= 
        Author: BTH
        Helper function to basicFlatSmSemantics =#
        function createTandC(inSMComps::List{<:DAE.Element}, inTransitions::List{<:DAE.Element}) ::Tuple{List{Transition}, List{DAE.Exp}} 
              local c::List{DAE.Exp}
              local t::List{Transition}

              local transitions::List{Transition}

              transitions = ListUtil.map1(inTransitions, createTransition, inSMComps)
               #= print(\"\\nStateMachineFlatten.createTandC: UNSORTED:\\n\"+ stringDelimitList(List.map(transitions,dumpTransitionStr), \"\\n\"));
               =#
               #=  sort transtion according to priority
               =#
              t = ListUtil.sort(transitions, priorityLt)
               #= print(\"\\nStateMachineFlatten.createTandC: SORTED:\\n\"+ stringDelimitList(List.map(t,dumpTransitionStr), \"\\n\"));
               =#
               #=  TODO Check that if several transitions could fire from the same state, all transitions have different priorities
               =#
               #=  extract condtions from ordered transitions
               =#
              c = ListUtil.map(t, extractCondtionFromTransition)
          (t, c)
        end

        function extractCondtionFromTransition(trans::Transition) ::DAE.Exp 
              local condition::DAE.Exp

              @match TRANSITION(condition = condition) = trans
          condition
        end

         #= 
        Compare priority of transitions
         =#
        function priorityLt(inTrans1::Transition, inTrans2::Transition) ::Bool 
              local res::Bool

              local priority1::ModelicaInteger
              local priority2::ModelicaInteger

              @match TRANSITION(priority = priority1) = inTrans1
              @match TRANSITION(priority = priority2) = inTrans2
              res = intLt(priority1, priority2)
          res
        end

         #= 
        Author: BTH
        Helper function to flatSmToDataFlow
         =#
        function createTransition(transitionElem::DAE.Element, states::List{<:DAE.Element}) ::Transition 
              local trans::Transition

              local crefFrom::DAE.ComponentRef
              local crefTo::DAE.ComponentRef
               #=  Transition
               =#
              local from::ModelicaInteger
              local to::ModelicaInteger
              local condition::DAE.Exp
              local immediate::Bool = true
              local reset::Bool = true
              local synchronize::Bool = false
              local priority::ModelicaInteger = 1

              @match DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("transition"), expLst = _cons(DAE.CREF(componentRef = crefFrom), _cons(DAE.CREF(componentRef = crefTo), _cons(condition, _cons(DAE.BCONST(immediate), _cons(DAE.BCONST(reset), _cons(DAE.BCONST(synchronize), _cons(DAE.ICONST(priority), nil))))))))) = transitionElem
              from = ListUtil.position1OnTrue(states, sMCompEqualsRef, crefFrom)
              to = ListUtil.position1OnTrue(states, sMCompEqualsRef, crefTo)
              trans = TRANSITION(from, to, condition, immediate, reset, synchronize, priority)
          trans
        end

         #= 
        Author: BTH
        Check if element is a FLAT_SM.
         =#
        function isFlatSm(inElement::DAE.Element) ::Bool 
              local outResult::Bool

              outResult = begin
                @match inElement begin
                  DAE.FLAT_SM(__)  => begin
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
        Check if element is a SM_COMP.
         =#
        function isSMComp(inElement::DAE.Element) ::Bool 
              local outResult::Bool

              outResult = begin
                @match inElement begin
                  DAE.SM_COMP(__)  => begin
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
        Return true if element is a transition, otherwise false =#
        function isTransition(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                @match inElement begin
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("transition")))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if element is an initialState, otherwise false =#
        function isInitialState(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                @match inElement begin
                  DAE.NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("initialState")))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if element is an EQUATION, otherwise false =#
        function isEquation(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                @match inElement begin
                  DAE.EQUATION(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if element is an EQUATION or WHEN_EQUATION, otherwise false =#
        function isEquationOrWhenEquation(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                @match inElement begin
                  DAE.EQUATION(__)  => begin
                    true
                  end
                  
                  DAE.WHEN_EQUATION(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if element is an EQUATION with at least one pre(..) or previous(..) expression, otherwise false =#
        function isPreOrPreviousEquation(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                  local exp::DAE.Exp
                  local scalar::DAE.Exp
                @match inElement begin
                  DAE.EQUATION(exp, scalar, _)  => begin
                    Expression.expHasPre(exp) || Expression.expHasPre(scalar) || Expression.expHasPrevious(exp) || Expression.expHasPrevious(scalar)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if element is an VAR, otherwise false =#
        function isVar(inElement::DAE.Element) ::Bool 
              local result::Bool

              result = begin
                @match inElement begin
                  DAE.VAR(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Return true if the componentRef of the second argument equals the componentRef of the SMComp (first argument)
         =#
        function sMCompEqualsRef(inElement::DAE.Element, inCref::DAE.ComponentRef) ::Bool 
              local result::Bool

              result = begin
                  local cref::DAE.ComponentRef
                @match inElement begin
                  DAE.SM_COMP(cref) where (ComponentReference.crefEqual(cref, inCref))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          result
        end

         #= 
        Author: BTH
        Dump transition to string. =#
        function dumpTransitionStr(transition::Transition) ::String 
              local transitionStr::String

              local from::ModelicaInteger
              local to::ModelicaInteger
              local condition::DAE.Exp
              local immediate::Bool
              local reset::Bool
              local synchronize::Bool
              local priority::ModelicaInteger

              @match TRANSITION(from, to, condition, immediate, reset, synchronize, priority) = transition
              transitionStr = "TRANSITION(from=" + intString(from) + ", to=" + intString(to) + ", condition=" + ExpressionDump.printExpStr(condition) + ", immediate=" + boolString(immediate) + ", reset=" + boolString(reset) + ", synchronize=" + boolString(synchronize) + ", priority=" + intString(priority) + ")"
          transitionStr
        end

         #= 
        Author: BTH
        Wrap equations in when-clauses as long as Synchronous Features are not supported =#
        function wrapHack(cache::FCore.Cache, inElementLst::List{<:DAE.Element}) ::List{DAE.Element} 
              local outElementLst::List{DAE.Element}

              local nOfSubstitutions::ModelicaInteger
              local eqnLst::List{DAE.Element}
              local otherLst::List{DAE.Element}
              local whenEq::DAE.Element
              local cond1::DAE.Exp
              local cond2::DAE.Exp
              local condition::DAE.Exp
              local condLst::List{DAE.Exp}
              local tArrayBool::DAE.Type

               #=  == {initial(), sample(DEFAULT_CLOCK_PERIOD, DEFAULT_CLOCK_PERIOD)} ==
               =#
              cond1 = DAE.CALL(Absyn.IDENT("initial"), nil, DAE.callAttrBuiltinImpureBool)
              cond2 = DAE.CALL(Absyn.IDENT("sample"), list(DAE.RCONST(Flags.getConfigReal(Flags.DEFAULT_CLOCK_PERIOD)), DAE.RCONST(Flags.getConfigReal(Flags.DEFAULT_CLOCK_PERIOD))), DAE.callAttrBuiltinImpureBool)
              tArrayBool = DAE.T_ARRAY(DAE.T_BOOL_DEFAULT, list(DAE.DIM_INTEGER(2)))
              if Flags.getConfigBool(Flags.CT_STATE_MACHINES)
                condLst = ListUtil.filterMap1(inElementLst, extractSmOfExps, "cImmediate")
                (eqnLst, otherLst) = ListUtil.extractOnTrue(inElementLst, isPreOrPreviousEquation)
                condition = DAE.ARRAY(tArrayBool, true, _cons(cond1, condLst))
              else
                (eqnLst, otherLst) = ListUtil.extractOnTrue(inElementLst, isEquation)
                condition = DAE.ARRAY(tArrayBool, true, list(cond1, cond2))
              end
               #=  Extract transition conditions
               =#
               #=  when {initial(), sample(DEFAULT_CLOCK_PERIOD, DEFAULT_CLOCK_PERIOD)} then .. end when;
               =#
              whenEq = DAE.WHEN_EQUATION(condition, eqnLst, NONE(), DAE.emptyElementSource)
              outElementLst = listAppend(otherLst, list(whenEq))
          outElementLst
        end

         #= 
        Hack for extracting DAE.CREFs from flat state machine semantics equations.
         =#
        function extractSmOfExps(inElem::DAE.Element, inLastIdent::DAE.Ident) ::DAE.Exp 
              local outExp::DAE.Exp

              outExp = begin
                  local exp::DAE.Exp
                  local scalar::DAE.Exp
                  local cref::DAE.ComponentRef
                  local firstIdent::DAE.Ident
                  local lastIdent::DAE.Ident
                @match inElem begin
                  DAE.EQUATION(exp = exp)  => begin
                      @match DAE.CREF(componentRef = cref) = exp
                      firstIdent = ComponentReference.crefFirstIdent(cref)
                      @match true = firstIdent == "smOf"
                      lastIdent = ComponentReference.crefLastIdent(cref)
                      @match true = lastIdent == inLastIdent
                    exp
                  end
                end
              end
          outExp
        end

         #= 
        Author: BTH
        Helper function to traverse subexpressions
        Substitutes 'previous(x)' by 'pre(x)'  =#
        function traversingSubsPreForPrevious(inExp::DAE.Exp, inHitCount::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local outHitCount::ModelicaInteger
              local outExp::DAE.Exp

              (outExp, outHitCount) = begin
                  local expLst::List{DAE.Exp}
                  local attr::DAE.CallAttributes
                @match inExp begin
                  DAE.CALL(Absyn.IDENT("previous"), expLst, attr)  => begin
                    (DAE.CALL(Absyn.IDENT("pre"), expLst, attr), inHitCount + 1)
                  end
                  
                  _  => begin
                      (inExp, inHitCount)
                  end
                end
              end
          (outExp, outHitCount)
        end

         #= 
        Author: BTH
        Helper function to traverse subexpressions
        Substitutes 'sample(x, _)' by 'x'  =#
        function traversingSubsXForSampleX(inExp::DAE.Exp, inHitCount::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger} 
              local outHitCount::ModelicaInteger
              local outExp::DAE.Exp

              (outExp, outHitCount) = begin
                  local expX::DAE.Exp
                  local attr::DAE.CallAttributes
                @match inExp begin
                  DAE.CALL(Absyn.IDENT("sample"), expX <| DAE.CLKCONST(DAE.INFERRED_CLOCK(__)) <|  nil(), _)  => begin
                    (expX, inHitCount + 1)
                  end
                  
                  _  => begin
                      (inExp, inHitCount)
                  end
                end
              end
          (outExp, outHitCount)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
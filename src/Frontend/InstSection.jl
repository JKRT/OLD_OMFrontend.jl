  module InstSection


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

        import ClassInf

        # import Connect

        import ConnectionGraph

        import DAE

        import FCore

        import FGraph

        import InnerOuter

        import Prefix

        import SCode

        import Algorithm

        import Ceval

        import ComponentReference

        import Config

        import ConnectUtil

        import DAEUtil

        import Debug

        import Dump

        import ElementSource

        import Error

        import Expression

        import ExpressionDump

        import ExpressionSimplify

        import ExpressionSimplifyTypes

        import Flags

        import Inst

        import InstDAE

        import InstFunction

        import InstTypes

        import InstUtil

        import NFInstUtil

        import ListUtil

        import Lookup

        import Patternm

        import PrefixUtil
        import SCodeUtil

        import Static

        import Types

        import Util

        import Values

        import ValuesUtil

        import System

        import ErrorExt

        import SCodeDump

        import DAEDump

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

         const alwaysUnroll = true::Bool

         #= author: LS, ELN

          Instantiates an equation by calling
          instEquationCommon with Inital set
          to NON_INITIAL. =#
        function instEquation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEquation::SCode.Equation, inImpl::Bool, unrollForLoops::Bool #= Unused, to comply with Inst.instList interface. =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local eq::SCode.EEquation

              @match SCode.EQUATION(eEquation = eq) = inEquation
              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = instEquationCommon(inCache, inEnv, inIH, inPrefix, inSets, inState, eq, SCode.NON_INITIAL(), inImpl, inGraph)
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= Instantiation of EEquation, used in for loops and if-equations. =#
        function instEEquation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEEquation::SCode.EEquation, inImpl::Bool, unrollForLoops::Bool #= Unused, to comply with Inst.instList interface. =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = instEquationCommon(inCache, inEnv, inIH, inPrefix, inSets, inState, inEEquation, SCode.NON_INITIAL(), inImpl, inGraph)
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= author: LS, ELN
          Instantiates initial equation by calling inst_equation_common with Inital
          set to INITIAL. =#
        function instInitialEquation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEquation::SCode.Equation, inImpl::Bool, unrollForLoops::Bool #= Unused, to comply with Inst.instList interface. =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local eq::SCode.EEquation

              @match SCode.EQUATION(eEquation = eq) = inEquation
              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = instEquationCommon(inCache, inEnv, inIH, inPrefix, inSets, inState, eq, SCode.INITIAL(), inImpl, inGraph)
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= Instantiates initial EEquation used in for loops and if equations  =#
        function instEInitialEquation(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEEquation::SCode.EEquation, inImpl::Bool, unrollForLoops::Bool #= Unused, to comply with Inst.instList interface. =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = instEquationCommon(inCache, inEnv, inIH, inPrefix, inSets, inState, inEEquation, SCode.INITIAL(), inImpl, inGraph)
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= The DAE output of the translation contains equations which
          in most cases directly corresponds to equations in the source.
          Some of them are also generated from `connect\\' clauses.

          This function takes an equation from the source and generates DAE
          equations and connection sets. =#
        function instEquationCommon(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEEquation::SCode.EEquation, inInitial::SCode.Initial, inImpl::Bool, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local errorCount::ModelicaInteger = Error.getNumErrorMessages()

              _ = begin
                  local s::String
                  local state::ClassInf.SMNode
                @matchcontinue () begin
                  ()  => begin
                      state = ClassInf.trans(inState, ClassInf.FOUND_EQUATION())
                      (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = instEquationCommonWork(inCache, inEnv, inIH, inPrefix, inSets, state, inEEquation, inInitial, inImpl, inGraph, DAE.FLATTEN(inEEquation, NONE()))
                      outDae = DAEUtil.traverseDAE(outDae, DAE.AvlTreePathFunction.Tree.EMPTY(), Expression.traverseSubexpressionsHelper, (ExpressionSimplify.simplifyWork, ExpressionSimplifyTypes.optionSimplifyOnly))
                    ()
                  end

                  ()  => begin
                      @shouldFail _ = ClassInf.trans(inState, ClassInf.FOUND_EQUATION())
                      s = ClassInf.printStateStr(inState)
                      Error.addSourceMessage(Error.EQUATION_TRANSITION_FAILURE, list(s), SCodeUtil.equationFileInfo(inEEquation))
                    fail()
                  end

                  _  => begin
                         #=  We only want to print a generic error message if no other error message was printed
                         =#
                         #=  Providing two error messages for the same error is confusing (but better than none)
                         =#
                        @match true = errorCount == Error.getNumErrorMessages()
                        s = "\\n" + SCodeDump.equationStr(inEEquation)
                        Error.addSourceMessage(Error.EQUATION_GENERIC_FAILURE, list(s), SCodeUtil.equationFileInfo(inEEquation))
                      fail()
                  end
                end
              end
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= The DAE output of the translation contains equations which in most cases
           directly corresponds to equations in the source. Some of them are also
           generated from connect clauses.

           This function takes an equation from the source and generates DAE equations
           and connection sets. =#
        function instEquationCommonWork(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEEquation::SCode.EEquation, inInitial::SCode.Initial, inImpl::Bool, inGraph::ConnectionGraph.ConnectionGraphType, inFlattenOp::DAE.SymbolicOperation) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets = inSets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy = inIH
              local outEnv::FCore.Graph = inEnv
              local outCache::FCore.Cache = inCache

              (outDae, outState) = begin
                  local lhs_acr::Absyn.ComponentRef
                  local rhs_acr::Absyn.ComponentRef
                  local acr::Absyn.ComponentRef
                  local info::SourceInfo
                  local lhs_aexp::Absyn.Exp
                  local rhs_aexp::Absyn.Exp
                  local range_aexp::Absyn.Exp
                  local comment::SCode.Comment
                  local lhs_exp::DAE.Exp
                  local rhs_exp::DAE.Exp
                  local exp::DAE.Exp
                  local cond_exp::DAE.Exp
                  local msg_exp::DAE.Exp
                  local level_exp::DAE.Exp
                  local cr_exp::DAE.Exp
                  local lhs_prop::DAE.Properties
                  local rhs_prop::DAE.Properties
                  local prop::DAE.Properties
                  local cr_prop::DAE.Properties
                  local source::DAE.ElementSource
                  local expl::List{DAE.Exp}
                  local props::List{DAE.Properties}
                  local c::DAE.Const
                  local idx::ModelicaInteger
                  local eql::List{SCode.EEquation}
                  local else_branch::List{SCode.EEquation}
                  local branches::List{List{SCode.EEquation}}
                  local rest_branches::List{List{SCode.EEquation}}
                  local ell::List{List{DAE.Element}}
                  local el::List{DAE.Element}
                  local el2::List{DAE.Element}
                  local crefs1::List{DAE.ComponentRef}
                  local crefs2::List{DAE.ComponentRef}
                  local else_when::Option{DAE.Element}
                  local iter_crefs::List{Tuple{Absyn.ComponentRef, ModelicaInteger}}
                  local ty::DAE.Type
                  local env::FCore.Graph
                  local val::Values.Value
                  local cr::DAE.ComponentRef
                  local branch_selected::Bool
                   #=  Connect equations.
                   =#
                @matchcontinue inEEquation begin
                  SCode.EQ_CONNECT(crefLeft = lhs_acr, crefRight = rhs_acr, info = info)  => begin
                      (outCache, outEnv, outIH, outSets, outDae, outGraph) = instConnect(outCache, outEnv, outIH, outSets, inPrefix, lhs_acr, rhs_acr, inImpl, inGraph, info)
                      outState = instEquationCommonCiTrans(inState, inInitial)
                    (outDae, outState)
                  end

                  SCode.EQ_EQUALS(expLeft = lhs_aexp, expRight = rhs_aexp, info = info, comment = comment)  => begin
                       #=  Equality equations.
                       =#
                       #=  Check that the equation is valid if the lhs is a tuple.
                       =#
                      checkTupleCallEquationMessage(lhs_aexp, rhs_aexp, info)
                      (outCache, lhs_exp, lhs_prop) = Static.elabExpLHS(inCache, inEnv, lhs_aexp, inImpl, true, inPrefix, info)
                      (outCache, rhs_exp, rhs_prop) = Static.elabExp(inCache, inEnv, rhs_aexp, inImpl, true, inPrefix, info)
                      (outCache, lhs_exp, lhs_prop) = Ceval.cevalIfConstant(outCache, inEnv, lhs_exp, lhs_prop, inImpl, info)
                      (outCache, rhs_exp, rhs_prop) = Ceval.cevalIfConstant(outCache, inEnv, rhs_exp, rhs_prop, inImpl, info)
                      (outCache, lhs_exp, rhs_exp, lhs_prop) = condenseArrayEquation(outCache, inEnv, lhs_aexp, rhs_aexp, lhs_exp, rhs_exp, lhs_prop, rhs_prop, inImpl, inPrefix, info)
                      (outCache, lhs_exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, lhs_exp, inPrefix)
                      (outCache, rhs_exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, rhs_exp, inPrefix)
                       #=  Set the source of this element.
                       =#
                      source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                      source = ElementSource.addCommentToSource(source, SOME(comment))
                       #=  Check that the lhs and rhs get along.
                       =#
                      outDae = instEqEquation(lhs_exp, lhs_prop, rhs_exp, rhs_prop, source, inInitial, inImpl)
                      outState = instEquationCommonCiTrans(inState, inInitial)
                    (outDae, outState)
                  end

                  SCode.EQ_IF(thenBranch = branches, elseBranch = else_branch, info = info)  => begin
                       #=  Elaborate all of the conditions.
                       =#
                      (outCache, expl, props) = Static.elabExpList(outCache, outEnv, inEEquation.condition, inImpl, true, inPrefix, info)
                       #=  Check that all conditions are Boolean.
                       =#
                      prop = Types.propsAnd(props)
                      checkIfConditionTypes(prop, inEEquation.condition, props, info)
                       #=  Try to select one of the branches.
                       =#
                      try
                        rest_branches = branches
                        eql = else_branch
                        for cond in expl
                          @match _cons(DAE.PROP(constFlag = c), props) = props
                          @match true = Types.isParameterOrConstant(c)
                          (outCache, val) = Ceval.ceval(outCache, outEnv, cond, inImpl, Absyn.NO_MSG(), 0)
                          @match true = checkIfConditionBinding(val, info)
                          if ValuesUtil.valueBool(val)
                            eql = listHead(rest_branches)
                            break
                          end
                          rest_branches = listRest(rest_branches)
                        end
                        outCache = InstUtil.popStructuralParameters(outCache, inPrefix)
                        (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = Inst.instList(outCache, inEnv, inIH, inPrefix, inSets, inState, if SCodeUtil.isInitial(inInitial)
                              instEInitialEquation
                            else
                              instEEquation
                            end, eql, inImpl, alwaysUnroll, inGraph)
                      catch
                        (outCache, expl) = PrefixUtil.prefixExpList(outCache, inEnv, inIH, expl, inPrefix)
                        source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                        if SCodeUtil.isInitial(inInitial)
                          (outCache, outEnv, outIH, outState, ell) = instInitialIfEqBranches(outCache, inEnv, inIH, inPrefix, inState, branches, inImpl)
                          (outCache, outEnv, outIH, outState, el) = instInitialIfEqBranch(outCache, outEnv, outIH, inPrefix, outState, else_branch, inImpl)
                          outDae = DAE.DAE(list(DAE.INITIAL_IF_EQUATION(expl, ell, el, source)))
                        else
                          (outCache, outEnv, outIH, outState, ell) = instIfEqBranches(outCache, inEnv, inIH, inPrefix, inState, branches, inImpl)
                          (outCache, outEnv, outIH, outState, el) = instIfEqBranch(outCache, outEnv, outIH, inPrefix, outState, else_branch, inImpl)
                          outDae = DAE.DAE(list(DAE.IF_EQUATION(expl, ell, el, source)))
                        end
                      end
                       #=  Go through each condition and select the first branch whose
                       =#
                       #=  condition is a parameter expression evaluating to true. If a
                       =#
                       #=  non-parameter expression is encountered this will fail and fall
                       =#
                       #=  back to instantiating the whole if equation below. If all
                       =#
                       #=  conditions evaluate to false the else branch will be selected.
                       =#
                       #=  Add evaluated parameter condition to the structural parameter list to mark it final later
                       =#
                       #=  A branch was selected, instantiate it.
                       =#
                       #=  Set the source of this element.
                       =#
                       #=  Instantiate all branches.
                       =#
                    (outDae, outState)
                  end

                  SCode.EQ_WHEN(info = info)  => begin
                      if SCodeUtil.isInitial(inInitial)
                        Error.addSourceMessageAndFail(Error.INITIAL_WHEN, nil, info)
                      end
                      (outCache, outEnv, outIH, cond_exp, el, outGraph) = instWhenEqBranch(inCache, inEnv, inIH, inPrefix, inSets, inState, (inEEquation.condition, inEEquation.eEquationLst), inImpl, alwaysUnroll, inGraph, info)
                       #=  Set the source of this element.
                       =#
                      source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                      else_when = NONE()
                      for branch in listReverse(inEEquation.elseBranches)
                        (outCache, outEnv, outIH, exp, el2, outGraph) = instWhenEqBranch(outCache, outEnv, outIH, inPrefix, inSets, inState, branch, inImpl, alwaysUnroll, outGraph, info)
                        else_when = SOME(DAE.WHEN_EQUATION(exp, el2, else_when, source))
                      end
                      outState = instEquationCommonCiTrans(inState, inInitial)
                      outDae = DAE.DAE(list(DAE.WHEN_EQUATION(cond_exp, el, else_when, source)))
                    (outDae, outState)
                  end

                  SCode.EQ_FOR(info = info)  => begin
                       #=  Check if we have an explicit range, and use it if that's the case.
                       =#
                       #=  Otherwise, try to deduce the implicit range based on how the iterator is used.
                       =#
                      if isSome(inEEquation.range)
                        @match SOME(range_aexp) = inEEquation.range
                        @match (outCache, exp, DAE.PROP(type_ = DAE.T_ARRAY(ty = ty), constFlag = c)) = Static.elabExp(outCache, inEnv, range_aexp, inImpl, true, inPrefix, info)
                      else
                        iter_crefs = SCodeUtil.findIteratorIndexedCrefsInEEquations(inEEquation.eEquationLst, inEEquation.index)
                        @match (exp, DAE.PROP(type_ = DAE.T_ARRAY(ty = ty), constFlag = c), outCache) = Static.deduceIterationRange(inEEquation.index, iter_crefs, inEnv, outCache, info)
                        range_aexp = Absyn.STRING("Internal error: generated implicit range could not be evaluated.")
                      end
                       #=  Elaborate the range.
                       =#
                       #=  Ceval below should not fail on our generated range, but just in case...
                       =#
                       #=  Add the iterator to the environment.
                       =#
                      env = addForLoopScope(inEnv, inEEquation.index, ty, SCode.VAR(), SOME(c))
                       #=  Try to constant evaluate the range.
                       =#
                      try
                        (outCache, val) = Ceval.ceval(outCache, inEnv, exp, inImpl, Absyn.NO_MSG(), 0)
                      catch
                        if Flags.getConfigBool(Flags.CHECK_MODEL)
                          val = Values.ARRAY(list(Values.INTEGER(1)), list(1))
                        else
                          Error.addSourceMessageAndFail(Error.NON_PARAMETER_ITERATOR_RANGE, list(Dump.printExpStr(range_aexp)), info)
                        end
                      end
                       #=  Evaluation failed, which is normally an error since the range
                       =#
                       #=  should be a parameter expression. If we're doing checkModel we
                       =#
                       #=  allow it though, and use {1} as range to check that the loop can be
                       =#
                       #=  instantiated.
                       =#
                      (outCache, outDae, outSets, outGraph) = unroll(outCache, env, inIH, inPrefix, inSets, inState, inEEquation.index, ty, val, inEEquation.eEquationLst, inInitial, inImpl, inGraph)
                      outState = instEquationCommonCiTrans(inState, inInitial)
                    (outDae, outState)
                  end

                  SCode.EQ_ASSERT(info = info)  => begin
                      (outCache, cond_exp) = instOperatorArg(outCache, inEnv, inIH, inPrefix, inEEquation.condition, inImpl, DAE.T_BOOL_DEFAULT, "assert", "condition", 1, info)
                      (outCache, msg_exp) = instOperatorArg(outCache, inEnv, inIH, inPrefix, inEEquation.message, inImpl, DAE.T_STRING_DEFAULT, "assert", "message", 2, info)
                      (outCache, level_exp) = instOperatorArg(outCache, inEnv, inIH, inPrefix, inEEquation.level, inImpl, DAE.T_ASSERTIONLEVEL, "assert", "level", 3, info)
                      source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                      if SCodeUtil.isInitial(inInitial)
                        outDae = DAE.DAE(list(DAE.INITIAL_ASSERT(cond_exp, msg_exp, level_exp, source)))
                      else
                        outDae = DAE.DAE(list(DAE.ASSERT(cond_exp, msg_exp, level_exp, source)))
                      end
                    (outDae, inState)
                  end

                  SCode.EQ_TERMINATE(info = info)  => begin
                      (outCache, msg_exp) = instOperatorArg(outCache, inEnv, inIH, inPrefix, inEEquation.message, inImpl, DAE.T_STRING_DEFAULT, "terminate", "message", 1, info)
                      source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                      if SCodeUtil.isInitial(inInitial)
                        outDae = DAE.DAE(list(DAE.INITIAL_TERMINATE(msg_exp, source)))
                      else
                        outDae = DAE.DAE(list(DAE.TERMINATE(msg_exp, source)))
                      end
                    (outDae, inState)
                  end

                  SCode.EQ_REINIT(cref = Absyn.CREF(componentRef = acr), info = info)  => begin
                       #=  Elaborate the cref.
                       =#
                      @match (outCache, (@match DAE.CREF(cr, ty) = cr_exp), cr_prop, _) = Static.elabCrefNoEval(outCache, inEnv, acr, inImpl, false, inPrefix, info)
                      @match true = checkReinitType(ty, cr_prop, cr, info)
                       #=  Elaborate the reinit expression.
                       =#
                      (outCache, exp, prop) = Static.elabExp(outCache, inEnv, inEEquation.expReinit, inImpl, true, inPrefix, info)
                      (outCache, exp, prop) = Ceval.cevalIfConstant(outCache, inEnv, exp, prop, inImpl, info)
                       #=  Check that the cref and the expression have matching types.
                       =#
                      exp = Types.matchProp(exp, prop, cr_prop, true)
                      (outCache, cr_exp, exp, cr_prop) = condenseArrayEquation(outCache, inEnv, inEEquation.cref, inEEquation.expReinit, cr_exp, exp, cr_prop, prop, inImpl, inPrefix, info)
                      (outCache, cr_exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, cr_exp, inPrefix)
                      (outCache, exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix)
                      source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                      @match DAE.DAE(el) = instEqEquation(cr_exp, cr_prop, exp, prop, source, inInitial, inImpl)
                      el = list(makeDAEArrayEqToReinitForm(e) for e in el)
                      outDae = DAE.DAE(el)
                    (outDae, inState)
                  end

                  SCode.EQ_NORETCALL(info = info)  => begin
                      if isConnectionsOperator(inEEquation.exp)
                        (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = handleConnectionsOperators(inCache, inEnv, inIH, inPrefix, inSets, inState, inEEquation, inInitial, inImpl, inGraph, inFlattenOp)
                      else
                        (outCache, exp) = Static.elabExp(inCache, inEnv, inEEquation.exp, inImpl, false, inPrefix, info)
                        (outCache, exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix)
                        source = makeEqSource(info, inEnv, inPrefix, inFlattenOp)
                        outDae = instEquationNoRetCallVectorization(exp, inInitial, source)
                        outState = inState
                      end
                       #=  Handle Connections.* operators.
                       =#
                       #=  Handle normal no return calls.
                       =#
                       #=  This is probably an external function call that the user wants to
                       =#
                       #=  evaluate at runtime, so don't ceval it.
                       =#
                    (outDae, outState)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instEquationCommonWork failed for eqn: ")
                        Debug.traceln(SCodeDump.equationStr(inEEquation) + " in scope: " + FGraph.getGraphNameStr(inEnv))
                      fail()
                  end
                end
              end
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

        function makeEqSource(inInfo::Absyn.Info, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inFlattenOp::DAE.SymbolicOperation) ::DAE.ElementSource
              local outSource::DAE.ElementSource

              outSource = ElementSource.createElementSource(inInfo, FGraph.getScopePath(inEnv), inPrefix)
              outSource = ElementSource.addSymbolicTransformation(outSource, inFlattenOp)
          outSource
        end

         #= Checks that all conditions in an if-equation are Boolean. =#
        function checkIfConditionTypes(inAccumProp::DAE.Properties, inConditions::List{<:Absyn.Exp}, inProperties::List{<:DAE.Properties}, inInfo::SourceInfo)
              _ = begin
                  local props::List{DAE.Properties}
                  local ty::DAE.Type
                  local exp_str::String
                  local ty_str::String
                   #=  Boolean type, ok.
                   =#
                @match inAccumProp begin
                  DAE.PROP(type_ = DAE.T_BOOL(__))  => begin
                    ()
                  end

                  _  => begin
                         #=  Any other type, find the offending condition and print an error.
                         =#
                        props = inProperties
                        for cond in inConditions
                          @match _cons(DAE.PROP(type_ = ty), props) = props
                          if ! Types.isScalarBoolean(ty)
                            exp_str = Dump.printExpStr(cond)
                            ty_str = Types.unparseTypeNoAttr(ty)
                            Error.addSourceMessageAndFail(Error.IF_CONDITION_TYPE_ERROR, list(exp_str, ty_str), inInfo)
                          end
                        end
                        Error.addInternalError("InstSection.checkIfConditionTypes failed to find non-Boolean condition.", inInfo)
                      fail()
                  end
                end
              end
        end

         #= Checks that the condition of an if-branch has a binding. =#
        function checkIfConditionBinding(inValues::Values.Value, inInfo::SourceInfo) ::Bool
              local outHasBindings::Bool

              local empty_val::Option{Values.Value}
              local scope::String
              local name::String

              empty_val = ValuesUtil.containsEmpty(inValues)
              if isSome(empty_val)
                @match SOME(Values.EMPTY(scope = scope, name = name)) = empty_val
                Error.addSourceMessage(Error.NO_CONSTANT_BINDING, list(name, scope), inInfo)
                outHasBindings = false
              else
                outHasBindings = true
              end
          outHasBindings
        end

         #= Helper function to instEquationCommonWork. Elaborates and type checks an
           argument for some builtin operators, like assert and terminate. =#
        function instOperatorArg(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inArg::Absyn.Exp, inImpl::Bool, inExpectedType::DAE.Type, inOperatorName::String, inArgName::String, inArgIndex::ModelicaInteger, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp}
              local outArg::DAE.Exp
              local outCache::FCore.Cache

              local props::DAE.Properties
              local ty::DAE.Type

              (outCache, outArg, props) = Static.elabExp(inCache, inEnv, inArg, inImpl, true, inPrefix, inInfo)
              ty = Types.getPropType(props)
              if ! Types.subtype(ty, inExpectedType)
                Error.addSourceMessageAndFail(Error.ARG_TYPE_MISMATCH, list(intString(inArgIndex), inOperatorName, inArgName, Dump.printExpStr(inArg), Types.unparseTypeNoAttr(ty), Types.unparseType(inExpectedType)), inInfo)
              end
              (outCache, outArg) = Ceval.cevalIfConstant(outCache, inEnv, outArg, props, inImpl, inInfo)
              (outCache, outArg) = PrefixUtil.prefixExp(outCache, inEnv, inIH, outArg, inPrefix)
          (outCache, outArg)
        end

        function isConnectionsOperator(inExp::Absyn.Exp) ::Bool
              local yes::Bool

              yes = begin
                  local id::Absyn.Ident
                @match inExp begin
                  Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT(id,  nil())))  => begin
                    listMember(id, list("root", "potentialRoot", "branch", "uniqueRoot"))
                  end

                  _  => begin
                      false
                  end
                end
              end
          yes
        end

         #= This function handles Connections.* no return operators =#
        function handleConnectionsOperators(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inEEquation::SCode.EEquation, inInitial::SCode.Initial, inImpl::Bool, inGraph::ConnectionGraph.ConnectionGraphType, flattenOp::DAE.SymbolicOperation) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = begin
                  local props::List{DAE.Properties}
                  local csets_1::DAE.Sets
                  local csets::DAE.Sets
                  local dae::DAE.DAElist
                  local ci_state_1::ClassInf.SMNode
                  local ci_state::ClassInf.SMNode
                  local ci_state_2::ClassInf.SMNode
                  local env::FCore.Graph
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local pre::Prefix.PrefixType
                  local c1::Absyn.ComponentRef
                  local c2::Absyn.ComponentRef
                  local cr::Absyn.ComponentRef
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                  local initial_::SCode.Initial
                  local impl::Bool
                  local b1::Bool
                  local b2::Bool
                  local i::String
                  local s::String
                  local e2::Absyn.Exp
                  local e1::Absyn.Exp
                  local e::Absyn.Exp
                  local ee::Absyn.Exp
                  local e3::Absyn.Exp
                  local msg::Absyn.Exp
                  local conditions::List{Absyn.Exp}
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1_2::DAE.Exp
                  local e2_2::DAE.Exp
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3_2::DAE.Exp
                  local msg_1::DAE.Exp
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local prop3::DAE.Properties
                  local b::List{SCode.EEquation}
                  local fb::List{SCode.EEquation}
                  local el::List{SCode.EEquation}
                  local eel::List{SCode.EEquation}
                  local tb::List{List{SCode.EEquation}}
                  local eex::List{Tuple{Absyn.Exp, List{SCode.EEquation}}}
                  local id_t::DAE.Type
                  local v::Values.Value
                  local cr_1::DAE.ComponentRef
                  local eqn::SCode.EEquation
                  local eq::SCode.EEquation
                  local cache::FCore.Cache
                  local valList::List{Values.Value}
                  local expl1::List{DAE.Exp}
                  local blist::List{Bool}
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local lst::List{Tuple{Absyn.ComponentRef, ModelicaInteger}}
                  local tpl::Tuple{Absyn.ComponentRef, ModelicaInteger}
                  local source::DAE.ElementSource #= the origin of the element =#
                  local daeElts1::List{DAE.Element}
                  local daeElts2::List{DAE.Element}
                  local daeLLst::List{List{DAE.Element}}
                  local cnst::DAE.Const
                  local info::SourceInfo
                  local daeElt2::DAE.Element
                  local lhsCrefs::List{DAE.ComponentRef}
                  local lhsCrefsRec::List{DAE.ComponentRef}
                  local i1::ModelicaInteger
                  local ipriority::ModelicaInteger
                  local daeElts::List{DAE.Element}
                  local daeElts3::List{DAE.Element}
                  local cr_::DAE.ComponentRef
                  local cr1_::DAE.ComponentRef
                  local cr2_::DAE.ComponentRef
                  local t::DAE.Type
                  local tprop1::DAE.Properties
                  local tprop2::DAE.Properties
                  local priority::ModelicaReal
                  local exp::DAE.Exp
                  local containsEmpty::Option{Values.Value}
                  local comment::SCode.Comment
                  local functionArgs::Absyn.FunctionArgs
                   #=  Connections.root(cr) - zero sized cref
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inSets, inState, inEEquation, inInitial, inImpl, inGraph, flattenOp) begin
                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("root",  nil())), functionArgs = Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(),  nil()))), _, _, graph, _)  => begin
                      @match (cache, SOME((DAE.ARRAY(array = nil), _, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      s = SCodeDump.equationStr(inEEquation)
                      Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO, list(s), info)
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("root",  nil())), functionArgs = Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(),  nil()))), _, _, graph, _)  => begin
                      @match (cache, SOME((DAE.CREF(cr_, _), _, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      (cache, cr_) = PrefixUtil.prefixCref(cache, env, ih, pre, cr_)
                      graph = ConnectionGraph.addDefiniteRoot(graph, cr_)
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("potentialRoot",  nil())), functionArgs = functionArgs)), _, _, graph, _)  => begin
                      (cr, _) = potentialRootArguments(functionArgs, info, pre, inEEquation)
                      @match (cache, SOME((DAE.ARRAY(array = nil), _, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      s = SCodeDump.equationStr(inEEquation)
                      Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO, list(s), info)
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("potentialRoot",  nil())), functionArgs = functionArgs)), _, _, graph, _)  => begin
                      (cr, ipriority) = potentialRootArguments(functionArgs, info, pre, inEEquation)
                      @match (cache, SOME((DAE.CREF(cr_, _), _, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      (cache, cr_) = PrefixUtil.prefixCref(cache, env, ih, pre, cr_)
                      graph = ConnectionGraph.addPotentialRoot(graph, cr_, intReal(ipriority))
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("uniqueRoot",  nil())), functionArgs = functionArgs)), _, _, graph, _)  => begin
                      (cr, _) = uniqueRootArguments(functionArgs, info, pre, inEEquation)
                      @match (cache, SOME((DAE.ARRAY(array = nil), _, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      s = SCodeDump.equationStr(inEEquation)
                      Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO, list(s), info)
                      Error.addSourceMessage(Error.NON_STANDARD_OPERATOR, list("Connections.uniqueRoot"), info)
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("uniqueRoot",  nil())), functionArgs = functionArgs)), _, _, graph, _)  => begin
                      (cr, msg) = uniqueRootArguments(functionArgs, info, pre, inEEquation)
                      (cache, exp, _) = Static.elabExp(cache, env, Absyn.CREF(cr), false, true, pre, info)
                      (cache, msg_1, _) = Static.elabExp(cache, env, msg, false, false, pre, info)
                      (cache, exp) = PrefixUtil.prefixExp(cache, env, ih, exp, pre)
                      (cache, msg_1) = PrefixUtil.prefixExp(cache, env, ih, msg_1, pre)
                      graph = ConnectionGraph.addUniqueRoots(graph, exp, msg_1)
                      Error.addSourceMessage(Error.NON_STANDARD_OPERATOR, list("Connections.uniqueRoot"), info)
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (cache, env, ih, pre, csets, ci_state, SCode.EQ_NORETCALL(info = info, exp = Absyn.CALL(function_ = Absyn.CREF_QUAL("Connections",  nil(), Absyn.CREF_IDENT("branch",  nil())), functionArgs = Absyn.FUNCTIONARGS(Absyn.CREF(cr1) <| Absyn.CREF(cr2) <|  nil(),  nil()))), _, _, graph, _)  => begin
                      @match (cache, SOME((e_1, _, _))) = Static.elabCref(cache, env, cr1, false, false, pre, info)
                      @match (cache, SOME((e_2, _, _))) = Static.elabCref(cache, env, cr2, false, false, pre, info)
                      b1 = Types.isZeroLengthArray(Expression.typeof(e_1))
                      b2 = Types.isZeroLengthArray(Expression.typeof(e_2))
                      if boolOr(b1, b2)
                        s = SCodeDump.equationStr(inEEquation)
                        Error.addSourceMessage(Error.OVERCONSTRAINED_OPERATOR_SIZE_ZERO, list(s), info)
                      else
                        @match DAE.CREF(cr1_, _) = e_1
                        @match DAE.CREF(cr2_, _) = e_2
                        (cache, cr1_) = PrefixUtil.prefixCref(cache, env, ih, pre, cr1_)
                        (cache, cr2_) = PrefixUtil.prefixCref(cache, env, ih, pre, cr2_)
                        graph = ConnectionGraph.addBranch(graph, cr1_, cr2_)
                      end
                    (cache, env, ih, DAE.emptyDae, csets, ci_state, graph)
                  end

                  (_, env, _, _, _, _, eqn, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      s = SCodeDump.equationStr(eqn)
                      Debug.trace("- handleConnectionsOperators failed for eqn: ")
                      Debug.traceln(s + " in scope:" + FGraph.getGraphNameStr(env))
                    fail()
                  end
                end
              end
               #=  failure
               =#
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

        function potentialRootArguments(inFunctionArgs::Absyn.FunctionArgs, info::SourceInfo, inPrefix::Prefix.PrefixType, inEEquation::SCode.EEquation) ::Tuple{Absyn.ComponentRef, ModelicaInteger}
              local outPriority::ModelicaInteger
              local outCref::Absyn.ComponentRef

              (outCref, outPriority) = begin
                  local cr::Absyn.ComponentRef
                  local p::ModelicaInteger
                  local s1::String
                  local s2::String
                @matchcontinue inFunctionArgs begin
                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(),  nil())  => begin
                    (cr, 0)
                  end

                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <| Absyn.INTEGER(p) <|  nil(),  nil())  => begin
                    (cr, p)
                  end

                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(), Absyn.NAMEDARG("priority", Absyn.INTEGER(p)) <|  nil())  => begin
                    (cr, p)
                  end

                  _  => begin
                        s1 = SCodeDump.equationStr(inEEquation)
                        s2 = PrefixUtil.printPrefixStr3(inPrefix)
                        Error.addSourceMessage(Error.WRONG_TYPE_OR_NO_OF_ARGS, list(s1, s2), info)
                      fail()
                  end
                end
              end
          (outCref, outPriority)
        end

        function uniqueRootArguments(inFunctionArgs::Absyn.FunctionArgs, info::SourceInfo, inPrefix::Prefix.PrefixType, inEEquation::SCode.EEquation) ::Tuple{Absyn.ComponentRef, Absyn.Exp}
              local outMessage::Absyn.Exp
              local outCref::Absyn.ComponentRef

              (outCref, outMessage) = begin
                  local cr::Absyn.ComponentRef
                  local msg::Absyn.Exp
                  local s1::String
                  local s2::String
                @matchcontinue inFunctionArgs begin
                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(),  nil())  => begin
                    (cr, Absyn.STRING(""))
                  end

                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <| msg <|  nil(),  nil())  => begin
                    (cr, msg)
                  end

                  Absyn.FUNCTIONARGS(Absyn.CREF(cr) <|  nil(), Absyn.NAMEDARG("message", msg) <|  nil())  => begin
                    (cr, msg)
                  end

                  _  => begin
                        s1 = SCodeDump.equationStr(inEEquation)
                        s2 = PrefixUtil.printPrefixStr3(inPrefix)
                        Error.addSourceMessage(Error.WRONG_TYPE_OR_NO_OF_ARGS, list(s1, s2), info)
                      fail()
                  end
                end
              end
          (outCref, outMessage)
        end

         #= Checks that the base type of the given type is Real, otherwise it prints an
           error message that the first argument to reinit must be a subtype of Real. =#
        function checkReinitType(inType::DAE.Type, inProperties::DAE.Properties, inCref::DAE.ComponentRef, inInfo::SourceInfo) ::Bool
              local outSucceeded::Bool

              outSucceeded = begin
                  local ty::DAE.Type
                  local cref_str::String
                  local ty_str::String
                  local cnst_str::String
                  local cnst::DAE.Const
                @matchcontinue inProperties begin
                  _  => begin
                      ty = Types.arrayElementType(inType)
                      @match false = Types.isReal(ty)
                      cref_str = ComponentReference.printComponentRefStr(inCref)
                      ty_str = Types.unparseType(ty)
                      Error.addSourceMessage(Error.REINIT_MUST_BE_REAL, list(cref_str, ty_str), inInfo)
                    false
                  end

                  DAE.PROP(constFlag = cnst)  => begin
                      @match false = Types.isVar(cnst)
                      cnst_str = Types.unparseConst(cnst)
                      cref_str = ComponentReference.printComponentRefStr(inCref)
                      Error.addSourceMessage(Error.REINIT_MUST_BE_VAR, list(cref_str, cnst_str), inInfo)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outSucceeded
        end

         #= Checks that if a tuple is used on the left side of an equation, then it
           must consist only of component references and the right side must be a
           function call. =#
        function checkTupleCallEquationMessage(left::Absyn.Exp, right::Absyn.Exp, info::SourceInfo)
              _ = begin
                  local crefs::List{Absyn.Exp}
                  local left_str::String
                  local right_str::String
                @match (left, right) begin
                  (Absyn.TUPLE(crefs), Absyn.CALL(__))  => begin
                      if ! ListUtil.all(crefs, AbsynUtil.isCref)
                        left_str = Dump.printExpStr(left)
                        right_str = Dump.printExpStr(right)
                        Error.addSourceMessageAndFail(Error.TUPLE_ASSIGN_CREFS_ONLY, list(left_str + " = " + right_str + ";"), info)
                      end
                    ()
                  end

                  (Absyn.TUPLE(__), _)  => begin
                      left_str = Dump.printExpStr(left)
                      right_str = Dump.printExpStr(right)
                      Error.addSourceMessage(Error.TUPLE_ASSIGN_FUNCALL_ONLY, list(left_str + " = " + right_str + ";"), info)
                    fail()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Creates DAE for NORETCALLs and also performs vectorization if needed. =#
        function instEquationNoRetCallVectorization(exp::DAE.Exp, initial_::SCode.Initial, source::DAE.ElementSource #= the origin of the element =#) ::DAE.DAElist
              local dae::DAE.DAElist

              dae = begin
                @match initial_ begin
                  SCode.NON_INITIAL(__)  => begin
                    DAE.DAE(list(DAE.NORETCALL(exp, source)))
                  end

                  SCode.INITIAL(__)  => begin
                    DAE.DAE(list(DAE.INITIAL_NORETCALL(exp, source)))
                  end
                end
              end
          dae
        end

         #= Function for transforming DAE equations into DAE.REINIT form,
           used by instEquationCommon. =#
        function makeDAEArrayEqToReinitForm(inEq::DAE.Element) ::DAE.Element
              local outEqn::DAE.Element

              outEqn = begin
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local e2::DAE.Exp
                  local e::DAE.Exp
                  local t::DAE.Type
                  local source::DAE.ElementSource #= the origin of the element =#
                @match inEq begin
                  DAE.EQUATION(DAE.CREF(componentRef = cr1), e, source)  => begin
                    DAE.REINIT(cr1, e, source)
                  end

                  DAE.DEFINE(cr1, e, source)  => begin
                    DAE.REINIT(cr1, e, source)
                  end

                  DAE.EQUEQUATION(cr1, cr2, source)  => begin
                      t = ComponentReference.crefLastType(cr2)
                      e2 = Expression.makeCrefExp(cr2, t)
                    DAE.REINIT(cr1, e2, source)
                  end

                  DAE.ARRAY_EQUATION(exp = DAE.CREF(componentRef = cr1), array = e, source = source)  => begin
                    DAE.REINIT(cr1, e, source)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("Failure in: makeDAEArrayEqToReinitForm")
                      fail()
                  end
                end
              end
          outEqn
        end

         #= This function transforms makes the two sides of an array equation
        into its condensed form. By default, most array variables are vectorized,
        i.e. v becomes {v[1],v[2],..,v[n]}. But for array equations containing function calls this is not wanted.
        This function detect this case and elaborates expressions without vectorization. =#
        function condenseArrayEquation(inCache::FCore.Cache, inEnv::FCore.Graph, ie1::Absyn.Exp, ie2::Absyn.Exp, elabedE1::DAE.Exp, elabedE2::DAE.Exp, iprop::DAE.Properties #= To determine if array equation =#, iprop2::DAE.Properties #= To determine if array equation =#, impl::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Exp, DAE.Properties}
              local oprop::DAE.Properties #= If we have an expandable tuple =#
              local outE2::DAE.Exp
              local outE1::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outE1, outE2, oprop) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local b3::Bool
                  local b4::Bool
                  local elabedE1_2::DAE.Exp
                  local elabedE2_2::DAE.Exp
                  local prop1::DAE.Properties
                  local prop::DAE.Properties
                  local prop2::DAE.Properties
                  local pre::Prefix.PrefixType
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                @matchcontinue (inCache, inEnv, ie1, ie2, elabedE1, elabedE2, iprop, iprop2, impl, inPrefix, info) begin
                  (cache, env, e1, e2, _, _, prop, prop2, _, pre, _)  => begin
                      @match true = Flags.getConfigBool(Flags.CONDENSE_ARRAYS)
                      b3 = Types.isPropTupleArray(prop)
                      b4 = Types.isPropTupleArray(prop2)
                      @match true = boolOr(b3, b4)
                      @match true = Expression.containFunctioncall(elabedE2)
                      (e1, prop) = expandTupleEquationWithWild(e1, prop2, prop)
                      (cache, elabedE1_2, prop1) = Static.elabExpLHS(cache, env, e1, impl, false, pre, info)
                      (cache, elabedE1_2, prop1) = Ceval.cevalIfConstant(cache, env, elabedE1_2, prop1, impl, info)
                      (cache, elabedE2_2, prop2) = Static.elabExp(cache, env, e2, impl, false, pre, info)
                      (cache, elabedE2_2, prop2) = Ceval.cevalIfConstant(cache, env, elabedE2_2, prop2, impl, info)
                    (cache, elabedE1_2, elabedE2_2, prop)
                  end

                  (cache, _, _, _, _, _, prop, _, _, _, _)  => begin
                    (cache, elabedE1, elabedE2, prop)
                  end
                end
              end
          (outCache, outE1, outE2, oprop #= If we have an expandable tuple =#)
        end

         #= Author BZ 2008-06
        The function expands the inExp, Absyn.EXP, to contain as many elements as the, DAE.Properties, propCall does.
        The expand adds the elements at the end and they are containing Absyn.WILD() exps with type Types.ANYTYPE.  =#
        function expandTupleEquationWithWild(inExp::Absyn.Exp, propCall::DAE.Properties, propTuple::DAE.Properties) ::Tuple{Absyn.Exp, DAE.Properties}
              local oprop::DAE.Properties
              local outExp::Absyn.Exp

              (outExp, oprop) = begin
                  local aexpl::List{Absyn.Exp}
                  local aexpl2::List{Absyn.Exp}
                  local typeList::List{DAE.Type}
                  local fillValue::ModelicaInteger #= The amount of elements to add =#
                  local propType::DAE.Type
                  local lst::List{DAE.Type}
                  local lst2::List{DAE.Type}
                  local tupleConst::List{DAE.TupleConst}
                  local tupleConst2::List{DAE.TupleConst}
                  local tconst::DAE.Const
                  local names::Option{List{String}}
                @matchcontinue (inExp, propCall, propTuple) begin
                  (Absyn.TUPLE(aexpl), DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types = typeList, names = names)), DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types = lst), tupleConst = DAE.TUPLE_CONST(tupleConst)))  => begin
                      fillValue = listLength(typeList) - listLength(aexpl)
                      lst2 = ListUtil.fill(DAE.T_ANYTYPE_DEFAULT, fillValue) #= types =#
                      aexpl2 = ListUtil.fill(Absyn.CREF(Absyn.WILD()), fillValue) #= epxressions =#
                      tupleConst2 = ListUtil.fill(DAE.SINGLE_CONST(DAE.C_VAR()), fillValue) #= TupleConst's =#
                      aexpl2 = listAppend(aexpl, aexpl2)
                      lst2 = listAppend(lst, lst2)
                      tupleConst2 = listAppend(tupleConst, tupleConst2)
                    (Absyn.TUPLE(aexpl2), DAE.PROP_TUPLE(DAE.T_TUPLE(lst2, names), DAE.TUPLE_CONST(tupleConst2)))
                  end

                  (_, DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(typeList, names)), DAE.PROP(propType, tconst))  => begin
                      fillValue = listLength(typeList) - 1
                      aexpl2 = ListUtil.fill(Absyn.CREF(Absyn.WILD()), fillValue) #= epxressions =#
                      lst2 = ListUtil.fill(DAE.T_ANYTYPE_DEFAULT, fillValue) #= types =#
                      tupleConst2 = ListUtil.fill(DAE.SINGLE_CONST(DAE.C_VAR()), fillValue) #= TupleConst's =#
                      aexpl = _cons(inExp, aexpl2)
                      lst = _cons(propType, lst2)
                      tupleConst = _cons(DAE.SINGLE_CONST(tconst), tupleConst2)
                    (Absyn.TUPLE(aexpl), DAE.PROP_TUPLE(DAE.T_TUPLE(lst, names), DAE.TUPLE_CONST(tupleConst)))
                  end

                  (_, _, _) where (! Types.isPropTuple(propCall))  => begin
                    (inExp, propTuple)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- expandTupleEquationWithWild failed")
                      fail()
                  end
                end
              end
          (outExp, oprop)
        end

         #= updats The ClassInf state machine when an equation is instantiated. =#
        function instEquationCommonCiTrans(inState::ClassInf.SMNode, inInitial::SCode.Initial) ::ClassInf.SMNode
              local outState::ClassInf.SMNode

              outState = begin
                @match inInitial begin
                  SCode.NON_INITIAL(__)  => begin
                    ClassInf.trans(inState, ClassInf.FOUND_EQUATION())
                  end

                  _  => begin
                      inState
                  end
                end
              end
          outState
        end

         #= Unrolling a loop is a way of removing the non-linear structure of the FOR
           clause by explicitly repeating the body of the loop once for each iteration. =#
        function unroll(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inIdent::Ident, inIteratorType::DAE.Type, inValue::Values.Value, inEquations::List{<:SCode.EEquation}, inInitial::SCode.Initial, inImplicit::Bool, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, DAE.DAElist, DAE.Sets, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType = inGraph
              local outSets::DAE.Sets = inSets
              local outDae::DAE.DAElist
              local outCache::FCore.Cache = inCache

              local values::List{Values.Value}
              local env::FCore.Graph
              local ci_state::ClassInf.SMNode = inState
              local daes::List{DAE.DAElist} = nil
              local dae::DAE.DAElist

              try
                @match Values.ARRAY(valueLst = values) = inValue
                for val in values
                  env = FGraph.openScope(inEnv, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE())
                  env = FGraph.addForIterator(env, inIdent, inIteratorType, DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.CONST(), SOME(DAE.C_CONST()))
                  (outCache, _, _, dae, outSets, ci_state, outGraph) = Inst.instList(outCache, env, inIH, inPrefix, outSets, ci_state, if SCodeUtil.isInitial(inInitial)
                        instEInitialEquation
                      else
                        instEEquation
                      end, inEquations, inImplicit, alwaysUnroll, outGraph)
                  daes = _cons(dae, daes)
                end
                outDae = ListUtil.fold(daes, DAEUtil.joinDaes, DAE.emptyDae)
              catch
                @match true = Flags.isSet(Flags.FAILTRACE)
                Debug.traceln("- InstSection.unroll failed: " + ValuesUtil.valString(inValue))
                fail()
              end
               #=  The iterator is not constant but the range is constant.
               =#
          (outCache, outDae, outSets, outGraph)
        end

         #= Adds a scope to the environment used in for loops.
         adrpo NOTE:
           The variability of the iterator SHOULD
           be determined by the range constantness! =#
        function addForLoopScope(env::FCore.Graph, iterName::Ident, iterType::DAE.Type, iterVariability::SCode.Variability, constOfForIteratorRange::Option{<:DAE.Const}) ::FCore.Graph
              local newEnv::FCore.Graph

              newEnv = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE())
              newEnv = FGraph.addForIterator(newEnv, iterName, iterType, DAE.UNBOUND(), iterVariability, constOfForIteratorRange)
          newEnv
        end

         #= Adds a scope to the environment used in for loops.
         adrpo NOTE:
           The variability of the iterator SHOULD
           be determined by the range constantness! =#
        function addParForLoopScope(env::FCore.Graph, iterName::Ident, iterType::DAE.Type, iterVariability::SCode.Variability, constOfForIteratorRange::Option{<:DAE.Const}) ::FCore.Graph
              local newEnv::FCore.Graph

              newEnv = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.parForScopeName, NONE())
              newEnv = FGraph.addForIterator(newEnv, iterName, iterType, DAE.UNBOUND(), iterVariability, constOfForIteratorRange)
          newEnv
        end

         #= author: LS, ELN
          Equations follow the same typing rules as equality expressions.
          This function adds the equation to the DAE. =#
        function instEqEquation(inExp1::DAE.Exp, inProperties2::DAE.Properties, inExp3::DAE.Exp, inProperties4::DAE.Properties, source::DAE.ElementSource #= the origin of the element =#, inInitial5::SCode.Initial, inImplicit::Bool, extraInfo::SourceInfo = AbsynUtil.dummyInfo #= We have 2 sources? =#) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local e1_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e2_1::DAE.Exp
                  local t_1::DAE.Type
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local t::DAE.Type
                  local dae::DAE.DAElist
                  local p1::DAE.Properties
                  local p2::DAE.Properties
                  local initial_::SCode.Initial
                  local impl::Bool
                  local e1_str::String
                  local t1_str::String
                  local e2_str::String
                  local t2_str::String
                  local s1::String
                  local s2::String
                  local c::DAE.Const
                  local tp::DAE.TupleConst
                  local info::SourceInfo
                   #= /* TODO: Weird hack to make backend happy */ =#
                @matchcontinue (inExp1, inProperties2, inExp3, inProperties4, source, inInitial5, inImplicit) begin
                  (e1 && DAE.CREF(__), p1 && DAE.PROP(type_ = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_))), e2, p2 && DAE.PROP(constFlag = c), _, initial_, _)  => begin
                      @match (e2_1, DAE.PROP(t_1, _)) = Types.matchProp(e2, p2, p1, true)
                      (e1, _) = ExpressionSimplify.simplify(e1)
                      (e2_1, _) = ExpressionSimplify.simplify(e2_1)
                      dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_)
                    dae
                  end

                  (e1, p1 && DAE.PROP(__), e2, p2 && DAE.PROP(constFlag = c), _, initial_, _)  => begin
                      @match (e1_1, DAE.PROP(t_1, _)) = Types.matchProp(e1, p1, p2, false)
                      (e1_1, _) = ExpressionSimplify.simplify(e1_1)
                      (e2, _) = ExpressionSimplify.simplify(e2)
                      dae = instEqEquation2(e1_1, e2, t_1, c, source, initial_)
                    dae
                  end

                  (e1, p1 && DAE.PROP(__), e2, p2 && DAE.PROP(constFlag = c), _, initial_, _)  => begin
                      @match (e2_1, DAE.PROP(t_1, _)) = Types.matchProp(e2, p2, p1, true)
                      (e1, _) = ExpressionSimplify.simplify(e1)
                      (e2_1, _) = ExpressionSimplify.simplify(e2_1)
                      dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_)
                    dae
                  end

                  (e1, p1 && DAE.PROP_TUPLE(__), e2, p2 && DAE.PROP_TUPLE(tupleConst = tp), _, initial_, _)  => begin
                      @match (e1_1, DAE.PROP_TUPLE(t_1, _)) = Types.matchProp(e1, p1, p2, false)
                      (e1_1, _) = ExpressionSimplify.simplify(e1_1)
                      (e2, _) = ExpressionSimplify.simplify(e2)
                      c = Types.propTupleAllConst(tp)
                      dae = instEqEquation2(e1_1, e2, t_1, c, source, initial_)
                    dae
                  end

                  (e1, p1 && DAE.PROP_TUPLE(__), e2, p2 && DAE.PROP_TUPLE(tupleConst = tp), _, initial_, _)  => begin
                      @match (e2_1, DAE.PROP_TUPLE(t_1, _)) = Types.matchProp(e2, p2, p1, true)
                      (e1, _) = ExpressionSimplify.simplify(e1)
                      (e2_1, _) = ExpressionSimplify.simplify(e2_1)
                      c = Types.propTupleAllConst(tp)
                      dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_)
                    dae
                  end

                  (e1 && DAE.CREF(__), DAE.PROP(type_ = DAE.T_ENUMERATION(__)), e2, DAE.PROP(type_ = t && DAE.T_ENUMERATION(__), constFlag = c), _, initial_, _)  => begin
                      (e1, _) = ExpressionSimplify.simplify(e1)
                      (e2, _) = ExpressionSimplify.simplify(e2)
                      dae = instEqEquation2(e1, e2, t, c, source, initial_)
                    dae
                  end

                  (e1, p1 && DAE.PROP(__), e2, DAE.PROP_TUPLE(__), _, initial_, _)  => begin
                      p2 = Types.propTupleFirstProp(inProperties4)
                      @match DAE.PROP(constFlag = c) = p2
                      @match (e1, DAE.PROP(type_ = t_1)) = Types.matchProp(e1, p1, p2, false)
                      (e1, _) = ExpressionSimplify.simplify(e1)
                      e2 = DAE.TSUB(e2, 1, t_1)
                      (e2, _) = ExpressionSimplify.simplify(e2)
                      dae = instEqEquation2(e1, e2, t_1, c, source, initial_)
                    dae
                  end

                  (e1, DAE.PROP(type_ = t1), e2, DAE.PROP(type_ = t2), _, _, _)  => begin
                      e1_str = ExpressionDump.printExpStr(e1)
                      t1_str = Types.unparseTypeNoAttr(t1)
                      e2_str = ExpressionDump.printExpStr(e2)
                      t2_str = Types.unparseTypeNoAttr(t2)
                      s1 = stringAppendList(list(e1_str, "=", e2_str))
                      s2 = stringAppendList(list(t1_str, "=", t2_str))
                      info = ElementSource.getElementSourceFileInfo(source)
                      Types.typeErrorSanityCheck(t1_str, t2_str, info)
                      Error.addMultiSourceMessage(Error.EQUATION_TYPE_MISMATCH_ERROR, list(s1, s2), if extraInfo.fileName == ""
                            list(info)
                          else
                            list(extraInfo, info)
                          end)
                    fail()
                  end
                end
              end
               #= /* If it fails then this rule is matched. */ =#
               #= /* If e2 is not of e1's type, check if e1 has e2's type instead */ =#
               #= /* TODO: Make testsuite run properly even if this is the first case... Unknown dimensions are not matched fine here and should possibly be disallowed. */ =#
               #= /* If it fails then this rule is matched. */ =#
               #= /* PR. */ =#
               #= /* PR.
                    An assignment to a variable of T_ENUMERATION type is an explicit
                    assignment to the value componnent of the enumeration, i.e. having
                    a type T_ENUM
                 */ =#
               #=  Assignment to a single component with a function returning multiple
               =#
               #=  values.
               =#
          outDae
        end

         #= author: LS, ELN
          This is the second stage of instEqEquation, when the types are checked. =#
        function instEqEquation2(inExp1::DAE.Exp, inExp2::DAE.Exp, inType3::DAE.Type, inConst::DAE.Const, source::DAE.ElementSource #= the origin of the element =#, inInitial4::SCode.Initial) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local dae::DAE.DAElist
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local initial_::SCode.Initial
                  local cr::DAE.ComponentRef
                  local t::DAE.Type
                  local vs::List{DAE.Var}
                  local tt::DAE.Type
                  local exps1::List{DAE.Exp}
                  local exps2::List{DAE.Exp}
                  local tys::List{DAE.Type}
                  local b::Bool
                @matchcontinue (inExp1, inExp2, inType3, inConst, source, inInitial4) begin
                  (e1, e2, DAE.T_INTEGER(__), _, _, initial_)  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_REAL(__), _, _, initial_)  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_STRING(__), _, _, initial_)  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_BOOL(__), _, _, initial_)  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_CLOCK(__), _, _, initial_)  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (DAE.CREF(componentRef = cr), e2, DAE.T_ENUMERATION(__), _, _, initial_)  => begin
                      dae = makeDaeDefine(cr, e2, source, initial_)
                    dae
                  end

                  (e1, DAE.CREF(componentRef = cr), DAE.T_ENUMERATION(__), _, _, initial_)  => begin
                    makeDaeDefine(cr, e1, source, initial_)
                  end

                  (e1, e2, DAE.T_ENUMERATION(__), _, _, initial_)  => begin
                    makeDaeEquation(e1, e2, source, initial_)
                  end

                  (e1, e2, tt && DAE.T_ARRAY(__), _, _, initial_)  => begin
                      dae = instArrayEquation(e1, e2, tt, inConst, source, initial_)
                    dae
                  end

                  (DAE.TUPLE(exps1), e2, DAE.T_TUPLE(types = _ <| _), _, _, initial_)  => begin
                      exps1 = ListUtil.map(exps1, Expression.emptyToWild)
                      checkNoDuplicateAssignments(exps1, ElementSource.getElementSourceFileInfo(source))
                      e1 = DAE.TUPLE(exps1)
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_TUPLE(__), _, _, initial_) where (! Expression.isTuple(e1))  => begin
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_METALIST(__), _, _, initial_)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_METATUPLE(__), _, _, initial_)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_METAOPTION(__), _, _, initial_)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_METAUNIONTYPE(__), _, _, initial_)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      dae = makeDaeEquation(e1, e2, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_SUBTYPE_BASIC(complexType = tt), _, _, initial_)  => begin
                      dae = instEqEquation2(e1, e2, tt, inConst, source, initial_)
                    dae
                  end

                  (e1, e2, DAE.T_COMPLEX(varLst = vs), _, _, initial_)  => begin
                      exps1 = Expression.splitRecord(e1, inType3)
                      exps2 = Expression.splitRecord(e2, inType3)
                      tys = ListUtil.map(vs, Types.getVarType)
                      dae = instEqEquation2List(exps1, exps2, tys, inConst, source, initial_, nil)
                    dae
                  end

                  (e1, e2, tt && DAE.T_COMPLEX(__), _, _, initial_)  => begin
                      dae = instComplexEquation(e1, e2, tt, source, initial_)
                    dae
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instEqEquation2 failed\\n")
                      fail()
                  end
                end
              end
               #= BTH
               =#
               #=  array equations
               =#
               #=  tuples
               =#
               #=  MetaModelica types
               =#
               #=  --------------
               =#
               #=  Complex types extending basic type
               =#
               #=  split a complex equation to its elements
               =#
               #= /* all other COMPLEX equations */ =#
          outDae
        end

        function instEqEquation2List(inExps1::List{<:DAE.Exp}, inExps2::List{<:DAE.Exp}, inTypes3::List{<:DAE.Type}, constVar::DAE.Const, source::DAE.ElementSource #= the origin of the element =#, initial_::SCode.Initial, acc::List{<:DAE.DAElist}) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local rest1::List{DAE.Exp}
                  local rest2::List{DAE.Exp}
                  local rest3::List{DAE.Type}
                  local ty::DAE.Type
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local res::DAE.DAElist
                @match (inExps1, inExps2, inTypes3, constVar, source, initial_, acc) begin
                  ( nil(),  nil(),  nil(), _, _, _, _)  => begin
                    DAEUtil.joinDaeLst(listReverse(acc))
                  end

                  (exp1 <| rest1, exp2 <| rest2, ty <| rest3, _, _, _, _)  => begin
                      res = instEqEquation2(exp1, exp2, ty, constVar, source, initial_)
                    instEqEquation2List(rest1, rest2, rest3, constVar, source, initial_, _cons(res, acc))
                  end
                end
              end
          outDae
        end

         #= author: LS, ELN
          Constructs an equation in the DAE, they can be
          either an initial equation or an ordinary equation. =#
        function makeDaeEquation(inExp1::DAE.Exp, inExp2::DAE.Exp, inSource::DAE.ElementSource #= the origin of the element =#, inInitial3::SCode.Initial) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local source::DAE.ElementSource
                  local elt::DAE.Element
                @match (inExp1, inExp2, inSource, inInitial3) begin
                  (e1, e2, source, SCode.NON_INITIAL(__))  => begin
                      elt = DAE.EQUATION(e1, e2, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.EQUATION(e1, e2, source)))
                  end

                  (e1, e2, source, SCode.INITIAL(__))  => begin
                      elt = DAE.INITIALEQUATION(e1, e2, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.INITIALEQUATION(e1, e2, source)))
                  end
                end
              end
          outDae
        end

         #= author: LS, ELN  =#
        function makeDaeDefine(inComponentRef::DAE.ComponentRef, inExp::DAE.Exp, source::DAE.ElementSource #= the origin of the element =#, inInitial::SCode.Initial) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local cr::DAE.ComponentRef
                  local e2::DAE.Exp
                @match (inComponentRef, inExp, source, inInitial) begin
                  (cr, e2, _, SCode.NON_INITIAL(__))  => begin
                    DAE.DAE(list(DAE.DEFINE(cr, e2, source)))
                  end

                  (cr, e2, _, SCode.INITIAL(__))  => begin
                    DAE.DAE(list(DAE.INITIALDEFINE(cr, e2, source)))
                  end
                end
              end
          outDae
        end

         #= Instantiates an array equation, i.e. an equation where both sides are arrays. =#
        function instArrayEquation(lhs::DAE.Exp, rhs::DAE.Exp, tp::DAE.Type, inConst::DAE.Const, inSource::DAE.ElementSource, initial_::SCode.Initial) ::DAE.DAElist
              local dae::DAE.DAElist

              dae = begin
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local ds::DAE.Dimensions
                  local dim::DAE.Dimension
                  local lhs_dim::DAE.Dimension
                  local rhs_dim::DAE.Dimension
                  local lhs_idxs::List{DAE.Exp}
                  local rhs_idxs::List{DAE.Exp}
                  local t::DAE.Type
                  local lhs_str::String
                  local rhs_str::String
                  local eq_str::String
                  local elt::DAE.Element
                  local source::DAE.ElementSource
                   #= /* Initial array equations with function calls => initial array equations */ =#
                @matchcontinue (lhs, rhs, tp, inConst, inSource, initial_) begin
                  (_, _, _, _, source, SCode.INITIAL(__))  => begin
                      b1 = Expression.containVectorFunctioncall(lhs)
                      b2 = Expression.containVectorFunctioncall(rhs)
                      @match true = boolOr(b1, b2)
                      ds = Types.getDimensions(tp)
                      elt = DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source)))
                  end

                  (_, _, _, _, source, SCode.NON_INITIAL(__))  => begin
                      b1 = Expression.containVectorFunctioncall(lhs)
                      b2 = Expression.containVectorFunctioncall(rhs)
                      @match true = boolOr(b1, b2)
                      ds = Types.getDimensions(tp)
                      elt = DAE.ARRAY_EQUATION(ds, lhs, rhs, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.ARRAY_EQUATION(ds, lhs, rhs, source)))
                  end

                  (_, _, DAE.T_ARRAY(ty = t, dims = _ <|  nil()), _, _, _)  => begin
                      @match false = Config.splitArrays()
                      @match DAE.T_ARRAY(dims = _cons(lhs_dim, _)) = Expression.typeof(lhs)
                      @match DAE.T_ARRAY(dims = _cons(rhs_dim, _)) = Expression.typeof(rhs)
                      lhs_idxs = expandArrayDimension(lhs_dim, lhs)
                      rhs_idxs = expandArrayDimension(rhs_dim, rhs)
                      dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_)
                    dae
                  end

                  (_, _, DAE.T_ARRAY(ty = t, dims = dim <|  nil()), _, _, _)  => begin
                      @match true = Config.splitArrays()
                      @match true = Expression.dimensionKnown(dim)
                      @match DAE.T_ARRAY(dims = _cons(lhs_dim, _)) = Expression.typeof(lhs)
                      @match DAE.T_ARRAY(dims = _cons(rhs_dim, _)) = Expression.typeof(rhs)
                      lhs_idxs = expandArrayDimension(lhs_dim, lhs)
                      rhs_idxs = expandArrayDimension(rhs_dim, rhs)
                      dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_)
                    dae
                  end

                  (_, _, DAE.T_ARRAY(dims = dim <|  nil()), _, source, _)  => begin
                      @match true = Config.splitArrays()
                      @match true = Expression.dimensionKnown(dim)
                      @match true = Expression.isRange(lhs) || Expression.isRange(rhs) || Expression.isReduction(lhs) || Expression.isReduction(rhs)
                      ds = Types.getDimensions(tp)
                      b = SCodeUtil.isInitial(initial_)
                      elt = if b
                            DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source)
                          else
                            DAE.ARRAY_EQUATION(ds, lhs, rhs, source)
                          end
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                      elt = if b
                            DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source)
                          else
                            DAE.ARRAY_EQUATION(ds, lhs, rhs, source)
                          end
                    DAE.DAE(list(elt))
                  end

                  (_, _, DAE.T_ARRAY(ty = t, dims = dim <|  nil()), _, _, _)  => begin
                      @match true = Config.splitArrays()
                      @match false = Expression.dimensionKnown(dim)
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      @match DAE.T_ARRAY(dims = _cons(lhs_dim, _)) = Expression.typeof(lhs)
                      @match DAE.T_ARRAY(dims = _cons(rhs_dim, _)) = Expression.typeof(rhs)
                      lhs_idxs = expandArrayDimension(lhs_dim, lhs)
                      rhs_idxs = expandArrayDimension(rhs_dim, rhs)
                      dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_)
                    dae
                  end

                  (_, _, DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil()), _, source, SCode.INITIAL(__))  => begin
                      @match true = Config.splitArrays()
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      elt = DAE.INITIAL_ARRAY_EQUATION(list(DAE.DIM_INTEGER(1)), lhs, rhs, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.INITIAL_ARRAY_EQUATION(list(DAE.DIM_INTEGER(1)), lhs, rhs, source)))
                  end

                  (_, _, DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil()), _, source, SCode.NON_INITIAL(__))  => begin
                      @match true = Config.splitArrays()
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      elt = DAE.ARRAY_EQUATION(list(DAE.DIM_INTEGER(1)), lhs, rhs, source)
                      source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt)
                    DAE.DAE(list(DAE.ARRAY_EQUATION(list(DAE.DIM_INTEGER(1)), lhs, rhs, source)))
                  end

                  (_, _, DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil()), _, _, _)  => begin
                      @match true = Config.splitArrays()
                      @match false = Flags.getConfigBool(Flags.CHECK_MODEL)
                      lhs_str = ExpressionDump.printExpStr(lhs)
                      rhs_str = ExpressionDump.printExpStr(rhs)
                      eq_str = stringAppendList(list(lhs_str, "=", rhs_str))
                      Error.addSourceMessage(Error.INST_ARRAY_EQ_UNKNOWN_SIZE, list(eq_str), ElementSource.getElementSourceFileInfo(inSource))
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instArrayEquation failed\\n")
                      fail()
                  end
                end
              end
               #= /* Arrays with function calls => array equations */ =#
               #=  Array equation of any size, non-expanding case
               =#
               #=  Expand along the first dimensions of the expressions, and generate an
               =#
               #=  equation for each pair of elements.
               =#
               #=  Array dimension of known size, expanding case.
               =#
               #=  Expand along the first dimensions of the expressions, and generate an
               =#
               #=  equation for each pair of elements.
               =#
               #=  Array dimension of unknown size, expanding case.
               =#
               #=  It's ok with array equation of unknown size if checkModel is used.
               =#
               #=  Expand along the first dimensions of the expressions, and generate an
               =#
               #=  equation for each pair of elements.
               =#
               #=  Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
               =#
               #=  It's ok with array equation of unknown size if checkModel is used.
               =#
               #=  generate an initial array equation of dim 1
               =#
               #=  Now the dimension can be made DAE.DIM_UNKNOWN(), I just don't want to break anything for now -- alleb
               =#
               #=  Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
               =#
               #=  It's ok with array equation of unknown size if checkModel is used.
               =#
               #=  generate an array equation of dim 1
               =#
               #=  Now the dimension can be made DAE.DIM_UNKNOWN(), I just don't want to break anything for now -- alleb
               =#
               #=  Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
               =#
               #=  It's ok with array equation of unknown size if checkModel is used.
               =#
          dae
        end

         #= This function loops recursively through all indices in the two arrays and
          generates an equation for each pair of elements. =#
        function instArrayElEq(inLhsExp::DAE.Exp, inRhsExp::DAE.Exp, inType::DAE.Type, inConst::DAE.Const, inLhsIndices::List{<:DAE.Exp}, inRhsIndices::List{<:DAE.Exp}, inSource::DAE.ElementSource, inInitial::SCode.Initial) ::DAE.DAElist
              local outDAE::DAE.DAElist = DAE.emptyDae

              local rhs_idx::DAE.Exp
              local rhs_idxs::List{DAE.Exp} = listReverse(inRhsIndices)
              local dae::DAE.DAElist

              for lhs_idx in listReverse(inLhsIndices)
                @match _cons(rhs_idx, rhs_idxs) = rhs_idxs
                dae = instEqEquation2(lhs_idx, rhs_idx, inType, inConst, inSource, inInitial)
                outDAE = DAEUtil.joinDaes(dae, outDAE)
              end
          outDAE
        end

         #= Unrolls a for-loop that contains when-statements. =#
        function unrollForLoop(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inIterator::String, inRange::DAE.Exp, inRangeProps::DAE.Properties, inBody::List{<:SCode.Statement}, inStatement::SCode.Statement, inInfo::SourceInfo, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement}
              local outCache::FCore.Cache

              local ty::DAE.Type
              local c::DAE.Const
              local range::DAE.Exp
              local env::FCore.Graph
              local val::Values.Value
              local str::String

              try
                @match DAE.T_ARRAY(ty = ty) = Types.getPropType(inRangeProps)
                c = Types.getPropConst(inRangeProps)
                @match true = Types.isParameterOrConstant(c)
                env = addForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c))
                (outCache, val) = Ceval.ceval(inCache, env, inRange, inImpl, Absyn.MSG(inInfo), 0)
                (outCache, outStatements) = loopOverRange(inCache, env, inIH, inPrefix, inState, inIterator, val, inBody, inSource, inInitial, inImpl, inUnrollLoops)
              catch
                Error.addSourceMessageAndFail(Error.UNROLL_LOOP_CONTAINING_WHEN, list(SCodeDump.statementStr(inStatement)), inInfo)
              end
               #=  We can unroll ONLY if we have a parameter range expression.
               =#
          (outCache, outStatements)
        end

        function instForStatement(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inForStatement::SCode.Statement, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement} #= For statements can produce multiple statements due to unrolling. =#
              local outCache::FCore.Cache

              local iterator::String
              local oarange::Option{Absyn.Exp}
              local arange::Absyn.Exp
              local range::DAE.Exp
              local prop::DAE.Properties
              local body::List{SCode.Statement}
              local info::SourceInfo
              local iter_crefs::List{AbsynUtil.IteratorIndexedCref}

              @match SCode.ALG_FOR(index = iterator, range = oarange, forBody = body, info = info) = inForStatement
              if isSome(oarange)
                @match SOME(arange) = oarange
                (outCache, range, prop) = Static.elabExp(inCache, inEnv, arange, inImpl, true, inPrefix, info)
              else
                iter_crefs = SCodeUtil.findIteratorIndexedCrefsInStatements(body, iterator)
                (range, prop, outCache) = Static.deduceIterationRange(iterator, iter_crefs, inEnv, inCache, info)
              end
               #=  Only unroll for-loops containing when-statements.
               =#
              if containsWhenStatements(body)
                (outCache, outStatements) = unrollForLoop(inCache, inEnv, inIH, inPrefix, inState, iterator, range, prop, body, inForStatement, info, inSource, inInitial, inImpl, inUnrollLoops)
              else
                (outCache, outStatements) = instForStatement_dispatch(inCache, inEnv, inIH, inPrefix, inState, iterator, range, prop, body, info, inSource, inInitial, inImpl, inUnrollLoops)
              end
          (outCache, outStatements #= For statements can produce multiple statements due to unrolling. =#)
        end

        function instForStatement_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inIterator::String, inRange::DAE.Exp, inRangeProps::DAE.Properties, inBody::List{<:SCode.Statement}, inInfo::SourceInfo, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement}
              local outCache::FCore.Cache = inCache

              local ty::DAE.Type
              local c::DAE.Const
              local env::FCore.Graph
              local source::DAE.ElementSource
              local range::DAE.Exp

              c = Types.getPropConst(inRangeProps)
               #=  Remove the for-loop if the range is empty.
               =#
              if Types.isParameterOrConstant(c)
                try
                  @match (outCache, Values.ARRAY(valueLst = nil)) = Ceval.ceval(outCache, inEnv, inRange, inImpl, Absyn.MSG(inInfo), 0)
                  outStatements = nil
                  return (outCache, outStatements)
                catch
                end
              end
              ty = Types.getPropType(inRangeProps)
              ty = getIteratorType(ty, inIterator, inInfo)
              (outCache, range) = Ceval.cevalRangeIfConstant(outCache, inEnv, inRange, inRangeProps, inImpl, inInfo)
              (outCache, range) = PrefixUtil.prefixExp(outCache, inEnv, inIH, range, inPrefix)
              env = addForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c))
              (outCache, outStatements) = instStatements(outCache, env, inIH, inPrefix, inState, inBody, inSource, inInitial, inImpl, inUnrollLoops)
              source = ElementSource.addElementSourceFileInfo(inSource, inInfo)
              outStatements = list(Algorithm.makeFor(inIterator, range, inRangeProps, outStatements, source))
          (outCache, outStatements)
        end

         #= instantiate a comlex equation, i.e. c = Complex(1.0,-1.0) when Complex is a record =#
        function instComplexEquation(lhs::DAE.Exp, rhs::DAE.Exp, tp::DAE.Type, source::DAE.ElementSource #= the origin of the element =#, initial_::SCode.Initial) ::DAE.DAElist
              local dae::DAE.DAElist

              dae = begin
                  local s::String
                  local info::SourceInfo
                   #=  Records
                   =#
                @matchcontinue (lhs, rhs, tp, source, initial_) begin
                  (_, _, _, _, _)  => begin
                      @match true = Types.isRecord(tp)
                      dae = makeComplexDaeEquation(lhs, rhs, source, initial_)
                    dae
                  end

                  (_, _, _, _, _)  => begin
                      @match true = Types.isExternalObject(tp)
                      dae = makeDaeEquation(lhs, rhs, source, initial_)
                    dae
                  end

                  (_, _, _, _, _)  => begin
                      dae = makeComplexDaeEquation(lhs, rhs, source, initial_)
                    dae
                  end

                  _  => begin
                        @match false = Types.isRecord(tp)
                        s = ExpressionDump.printExpStr(lhs) + " = " + ExpressionDump.printExpStr(rhs)
                        info = ElementSource.getElementSourceFileInfo(source)
                        Error.addSourceMessage(Error.ILLEGAL_EQUATION_TYPE, list(s), info)
                      fail()
                  end
                end
              end
               #=  External objects are treated as ordinary equations
               =#
               #=  adrpo: TODO! FIXME! shouldn't we return the dae here??!!
               =#
               #=  PA: do not know, but at least return the functions.
               =#
               #=  adrpo 2009-05-15: also T_COMPLEX that is NOT record but TYPE should be allowed
               =#
               #=                    as is used in Modelica.Mechanics.MultiBody (Orientation type)
               =#
               #=  adrpo: TODO! check if T_COMPLEX(ClassInf.TYPE)!
               =#
               #=  complex equation that is not of restriction record is not allowed
               =#
          dae
        end

         #= Creates a DAE.COMPLEX_EQUATION for equations involving records =#
        function makeComplexDaeEquation(lhs::DAE.Exp, rhs::DAE.Exp, source::DAE.ElementSource #= the origin of the element =#, initial_::SCode.Initial) ::DAE.DAElist
              local dae::DAE.DAElist

              dae = begin
                @match (lhs, rhs, source, initial_) begin
                  (_, _, _, SCode.NON_INITIAL(__))  => begin
                    DAE.DAE(list(DAE.COMPLEX_EQUATION(lhs, rhs, source)))
                  end

                  (_, _, _, SCode.INITIAL(__))  => begin
                    DAE.DAE(list(DAE.INITIAL_COMPLEX_EQUATION(lhs, rhs, source)))
                  end
                end
              end
          dae
        end

         #= Algorithms are converted to the representation defined in
          the module Algorithm, and the added to the DAE result.
          This function converts an algorithm section. =#
        function instAlgorithm(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inAlgorithm::SCode.AlgorithmSection, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = begin
                  local env::FCore.Graph
                  local statements_1::List{DAE.Statement}
                  local csets::DAE.Sets
                  local ci_state::ClassInf.SMNode
                  local statements::List{SCode.Statement}
                  local stmt::SCode.Statement
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local algSCode::SCode.AlgorithmSection
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local dae::DAE.DAElist
                  local s::String
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inSets, inState, inAlgorithm, inImpl, unrollForLoops, inGraph) begin
                  (cache, env, ih, pre, csets, ci_state, SCode.ALGORITHM(statements = statements), impl, _, graph)  => begin
                      ci_state = ClassInf.trans(ci_state, ClassInf.FOUND_ALGORITHM())
                      source = ElementSource.createElementSource(AbsynUtil.dummyInfo, FGraph.getScopePath(env), pre)
                      (cache, statements_1) = instStatements(cache, env, ih, pre, ci_state, statements, source, SCode.NON_INITIAL(), impl, unrollForLoops)
                      (statements_1, _) = DAEUtil.traverseDAEEquationsStmts(statements_1, Expression.traverseSubexpressionsHelper, (ExpressionSimplify.simplifyWork, ExpressionSimplifyTypes.optionSimplifyOnly))
                      dae = DAE.DAE(list(DAE.ALGORITHM(DAE.ALGORITHM_STMTS(statements_1), source)))
                    (cache, env, ih, dae, csets, ci_state, graph)
                  end

                  (_, _, _, _, _, ci_state, SCode.ALGORITHM(statements = stmt <| _), _, _, _)  => begin
                      @shouldFail _ = ClassInf.trans(ci_state, ClassInf.FOUND_ALGORITHM())
                      s = ClassInf.printStateStr(ci_state)
                      info = SCodeUtil.getStatementInfo(stmt)
                      Error.addSourceMessage(Error.ALGORITHM_TRANSITION_FAILURE, list(s), info)
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- InstSection.instAlgorithm failed")
                      fail()
                  end
                end
              end
               #= /* impl */ =#
               #=  set the source of this element
               =#
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= Algorithms are converted to the representation defined
          in the module Algorithm, and the added to the DAE result.
          This function converts an algorithm section. =#
        function instInitialAlgorithm(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inAlgorithm::SCode.AlgorithmSection, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, inGraph::ConnectionGraph.ConnectionGraphType) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.DAElist, DAE.Sets, ClassInf.SMNode, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outState::ClassInf.SMNode
              local outSets::DAE.Sets
              local outDae::DAE.DAElist
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outDae, outSets, outState, outGraph) = begin
                  local env::FCore.Graph
                  local statements_1::List{DAE.Statement}
                  local csets::DAE.Sets
                  local ci_state::ClassInf.SMNode
                  local statements::List{SCode.Statement}
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local dae::DAE.DAElist
                @matchcontinue (inCache, inEnv, inIH, inPrefix, inSets, inState, inAlgorithm, inImpl, unrollForLoops, inGraph) begin
                  (cache, env, ih, pre, csets, ci_state, SCode.ALGORITHM(statements = statements), impl, _, graph)  => begin
                      source = ElementSource.createElementSource(AbsynUtil.dummyInfo, FGraph.getScopePath(env), pre)
                      (cache, statements_1) = instStatements(cache, env, ih, pre, ci_state, statements, source, SCode.INITIAL(), impl, unrollForLoops)
                      (statements_1, _) = DAEUtil.traverseDAEEquationsStmts(statements_1, Expression.traverseSubexpressionsHelper, (ExpressionSimplify.simplifyWork, ExpressionSimplifyTypes.optionSimplifyOnly))
                      dae = DAE.DAE(list(DAE.INITIALALGORITHM(DAE.ALGORITHM_STMTS(statements_1), source)))
                    (cache, env, ih, dae, csets, ci_state, graph)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instInitialAlgorithm failed\\n")
                      fail()
                  end
                end
              end
               #=  set the source of this element
               =#
          (outCache, outEnv, outIH, outDae, outSets, outState, outGraph)
        end

         #= Constraints are elaborated and converted to DAE =#
        function instConstraint(inCache::FCore.Cache, inEnv::FCore.Graph, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inConstraints::SCode.ConstraintSection, inImpl::Bool) ::Tuple{FCore.Cache, FCore.Graph, DAE.DAElist, ClassInf.SMNode}
              local outState::ClassInf.SMNode
              local outDae::DAE.DAElist
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outDae, outState) = begin
                  local env::FCore.Graph
                  local constraints_1::List{DAE.Exp}
                  local ci_state::ClassInf.SMNode
                  local constraints::List{Absyn.Exp}
                  local impl::Bool
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local source::DAE.ElementSource #= the origin of the element =#
                  local dae::DAE.DAElist
                @matchcontinue (inCache, inEnv, inPrefix, inState, inConstraints, inImpl) begin
                  (cache, env, pre, ci_state, SCode.CONSTRAINTS(constraints = constraints), impl)  => begin
                      ci_state = ClassInf.trans(ci_state, ClassInf.FOUND_ALGORITHM())
                      source = ElementSource.createElementSource(AbsynUtil.dummyInfo, FGraph.getScopePath(env), pre)
                      (cache, constraints_1, _) = Static.elabExpList(cache, env, constraints, impl, true, pre, AbsynUtil.dummyInfo)
                      dae = DAE.DAE(list(DAE.CONSTRAINT(DAE.CONSTRAINT_EXPS(constraints_1), source)))
                    (cache, env, dae, ci_state)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instConstraints failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outEnv, outDae, outState)
        end

         #= This function instantiates a list of algorithm statements. =#
        function instStatements(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inStatements::List{<:SCode.Statement}, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement}
              local outCache::FCore.Cache = inCache

              local stmts::List{DAE.Statement}
              local stmtsl::List{List{DAE.Statement}} = nil

              for stmt in inStatements
                (outCache, stmts) = instStatement(inCache, inEnv, inIH, inPrefix, inState, stmt, inSource, inInitial, inImpl, unrollForLoops)
                stmtsl = _cons(stmts, stmtsl)
              end
              outStatements = ListUtil.flattenReverse(stmtsl)
          (outCache, outStatements)
        end

         #= Helper function to instStatement. Elaborates, evalutes if constant, and
           prefixes an expression. =#
        function instExp(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inExp::Absyn.Exp, inImpl::Bool, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = Static.elabExp(inCache, inEnv, inExp, inImpl, true, inPrefix, inInfo)
              (outCache, outExp, outProperties) = Ceval.cevalIfConstant(outCache, inEnv, outExp, outProperties, inImpl, inInfo)
              (outCache, outExp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, outExp, inPrefix)
          (outCache, outExp, outProperties)
        end

         #= Instantiates an algorithm statement. =#
        function instStatement(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inStatement::SCode.Statement, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement} #= More statements due to loop unrolling. =#
              local outCache::FCore.Cache = inCache

              local num_errors::ModelicaInteger = Error.getNumErrorMessages()

              try
                outStatements = begin
                    local cond_exp::DAE.Exp
                    local msg_exp::DAE.Exp
                    local level_exp::DAE.Exp
                    local exp::DAE.Exp
                    local cr_exp::DAE.Exp
                    local cond_prop::DAE.Properties
                    local msg_prop::DAE.Properties
                    local level_prop::DAE.Properties
                    local prop::DAE.Properties
                    local cr_prop::DAE.Properties
                    local if_branch::List{DAE.Statement}
                    local else_branch::List{DAE.Statement}
                    local branch::List{DAE.Statement}
                    local else_if_branches::List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}
                    local aexp::Absyn.Exp
                    local sstmts::List{SCode.Statement}
                    local source::DAE.ElementSource
                    local info::SourceInfo
                    local when_stmt_opt::Option{DAE.Statement}
                    local when_stmt::DAE.Statement
                    local cases::List{DAE.MatchCase}
                  @match inStatement begin
                    SCode.ALG_ASSIGN(__)  => begin
                        (outCache, outStatements) = instAssignment(outCache, inEnv, inIH, inPrefix, inStatement, inSource, inInitial, inImpl, inUnrollLoops, num_errors)
                      outStatements
                    end

                    SCode.ALG_IF(info = info)  => begin
                         #=  Instantiate the first branch.
                         =#
                        (outCache, cond_exp, cond_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.boolExpr, inImpl, info)
                        (outCache, if_branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.trueBranch, inSource, inInitial, inImpl, inUnrollLoops)
                         #=  Instantiate the elseif branches.
                         =#
                        else_if_branches = nil
                        for else_if in inStatement.elseIfBranch
                          (aexp, sstmts) = else_if
                          (outCache, exp, prop) = instExp(outCache, inEnv, inIH, inPrefix, aexp, inImpl, info)
                          (outCache, branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, sstmts, inSource, inInitial, inImpl, inUnrollLoops)
                          else_if_branches = _cons((exp, prop, branch), else_if_branches)
                        end
                        else_if_branches = listReverse(else_if_branches)
                         #=  Instantiate the else branch.
                         =#
                        (outCache, else_branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.elseBranch, inSource, inInitial, inImpl, inUnrollLoops)
                         #=  Construct the if-statement.
                         =#
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      Algorithm.makeIf(cond_exp, cond_prop, if_branch, else_if_branches, else_branch, source)
                    end

                    SCode.ALG_FOR(__)  => begin
                        (outCache, outStatements) = instForStatement(outCache, inEnv, inIH, inPrefix, inState, inStatement, inSource, inInitial, inImpl, inUnrollLoops)
                      outStatements
                    end

                    SCode.ALG_PARFOR(__)  => begin
                        (outCache, outStatements) = instParForStatement(outCache, inEnv, inIH, inPrefix, inState, inStatement, inSource, inInitial, inImpl, inUnrollLoops)
                      outStatements
                    end

                    SCode.ALG_WHILE(info = info)  => begin
                        (outCache, cond_exp, cond_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.boolExpr, inImpl, info)
                        (outCache, branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.whileBody, inSource, inInitial, inImpl, inUnrollLoops)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      list(Algorithm.makeWhile(cond_exp, cond_prop, branch, source))
                    end

                    SCode.ALG_WHEN_A(info = info)  => begin
                         #=  When may not be used in a function.
                         =#
                        if ClassInf.isFunction(inState)
                          Error.addSourceMessageAndFail(Error.FUNCTION_ELEMENT_WRONG_KIND, list("when"), info)
                        end
                        checkWhenAlgorithm(inStatement)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                        when_stmt_opt = NONE()
                        for b in listReverse(inStatement.branches)
                          (aexp, sstmts) = b
                          (outCache, cond_exp, cond_prop) = instExp(outCache, inEnv, inIH, inPrefix, aexp, inImpl, info)
                          (outCache, branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, sstmts, inSource, inInitial, inImpl, inUnrollLoops)
                          when_stmt = Algorithm.makeWhenA(cond_exp, cond_prop, branch, when_stmt_opt, source)
                          when_stmt_opt = SOME(when_stmt)
                        end
                      list(when_stmt)
                    end

                    SCode.ALG_ASSERT(info = info)  => begin
                        (outCache, cond_exp, cond_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.condition, inImpl, info)
                        (outCache, msg_exp, msg_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.message, inImpl, info)
                        (outCache, level_exp, level_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.level, inImpl, info)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      Algorithm.makeAssert(cond_exp, msg_exp, level_exp, cond_prop, msg_prop, level_prop, source)
                    end

                    SCode.ALG_TERMINATE(info = info)  => begin
                        (outCache, msg_exp, msg_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.message, inImpl, info)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      Algorithm.makeTerminate(msg_exp, msg_prop, source)
                    end

                    SCode.ALG_REINIT(info = info)  => begin
                        (outCache, cr_exp, cr_prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.cref, inImpl, info)
                        (outCache, exp, prop) = instExp(outCache, inEnv, inIH, inPrefix, inStatement.newValue, inImpl, info)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      Algorithm.makeReinit(cr_exp, exp, cr_prop, prop, source)
                    end

                    SCode.ALG_NORETCALL(info = info)  => begin
                        (outCache, exp) = Static.elabExp(outCache, inEnv, inStatement.exp, inImpl, true, inPrefix, info)
                        checkValidNoRetcall(exp, info)
                        (outCache, exp) = PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      if Expression.isTuple(exp)
                            nil
                          else
                            list(DAE.STMT_NORETCALL(exp, source))
                          end
                    end

                    SCode.ALG_BREAK(info = info)  => begin
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      list(DAE.STMT_BREAK(source))
                    end

                    SCode.ALG_CONTINUE(info = info)  => begin
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      list(DAE.STMT_CONTINUE(source))
                    end

                    SCode.ALG_RETURN(info = info)  => begin
                        if ! ClassInf.isFunction(inState)
                          Error.addSourceMessageAndFail(Error.RETURN_OUTSIDE_FUNCTION, nil, info)
                        end
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      list(DAE.STMT_RETURN(source))
                    end

                    SCode.ALG_FAILURE(info = info)  => begin
                        @match true = Config.acceptMetaModelicaGrammar()
                        (outCache, branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.stmts, inSource, inInitial, inImpl, inUnrollLoops)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                      list(DAE.STMT_FAILURE(branch, source))
                    end

                    SCode.ALG_TRY(info = info)  => begin
                         #=  try-else becomes:
                         =#
                         #=   matchcontinue ()
                         =#
                         #=     case () equation *body* then ();
                         =#
                         #=     else equation *elseBody* then ();
                         =#
                         #=   end matchcontinue;
                         =#
                        @match true = Config.acceptMetaModelicaGrammar()
                        (outCache, if_branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.body, inSource, inInitial, inImpl, inUnrollLoops)
                        (outCache, else_branch) = instStatements(outCache, inEnv, inIH, inPrefix, inState, inStatement.elseBody, inSource, inInitial, inImpl, inUnrollLoops)
                        source = ElementSource.addElementSourceFileInfo(inSource, info)
                        cases = list(DAE.CASE(nil, NONE(), nil, if_branch, SOME(DAE.TUPLE(nil)), info, 0, info), DAE.CASE(nil, NONE(), nil, else_branch, SOME(DAE.TUPLE(nil)), info, 0, info))
                        exp = DAE.MATCHEXPRESSION(if SCodeUtil.commentHasBooleanNamedAnnotation(inStatement.comment, "__OpenModelica_stackOverflowCheckpoint")
                              DAE.TRY_STACKOVERFLOW()
                            else
                              DAE.MATCHCONTINUE()
                            end, nil, nil, nil, cases, DAE.T_NORETCALL_DEFAULT)
                      list(DAE.STMT_NORETCALL(exp, source))
                    end
                  end
                end
              catch
                @match true = num_errors == Error.getNumErrorMessages()
                Error.addSourceMessageAndFail(Error.STATEMENT_GENERIC_FAILURE, list(SCodeDump.statementStr(inStatement)), SCodeUtil.getStatementInfo(inStatement))
              end
          (outCache, outStatements #= More statements due to loop unrolling. =#)
        end

         #= Wrapper for Algorithm that calls either makeAssignment or makeTupleAssignment
          depending on whether the right side is a tuple or not. This makes it possible
          to do cref := function_that_returns_tuple(...). =#
        function makeAssignment(inLhs::DAE.Exp, inLhsProps::DAE.Properties, inRhs::DAE.Exp, inRhsProps::DAE.Properties, inAttributes::DAE.Attributes, inInitial::SCode.Initial, inSource::DAE.ElementSource) ::DAE.Statement
              local outStatement::DAE.Statement

              outStatement = begin
                  local wild_props::List{DAE.Properties}
                  local wild_count::ModelicaInteger
                  local wilds::List{DAE.Exp}
                  local wildCrefExp::DAE.Exp
                   #=  If the RHS is a function that returns a tuple while the LHS is a single
                   =#
                   #=  value, make a tuple of the LHS and fill in the missing elements with
                   =#
                   #=  wildcards.
                   =#
                @match (inLhs, inLhsProps, inRhs, inRhsProps, inAttributes, inInitial, inSource) begin
                  (_, DAE.PROP(__), DAE.CALL(__), DAE.PROP_TUPLE(__), _, _, _)  => begin
                      @match _cons(_, wild_props) = Types.propTuplePropList(inRhsProps)
                      wild_count = listLength(wild_props)
                      wildCrefExp = Expression.makeCrefExp(DAE.WILD(), DAE.T_UNKNOWN_DEFAULT)
                      wilds = ListUtil.fill(wildCrefExp, wild_count)
                      wild_props = ListUtil.fill(DAE.PROP(DAE.T_ANYTYPE_DEFAULT, DAE.C_VAR()), wild_count)
                    Algorithm.makeTupleAssignment(_cons(inLhs, wilds), _cons(inLhsProps, wild_props), inRhs, inRhsProps, inInitial, inSource)
                  end

                  _  => begin
                      Algorithm.makeAssignment(inLhs, inLhsProps, inRhs, inRhsProps, inAttributes, inInitial, inSource)
                  end
                end
              end
               #=  Otherwise, call Algorithm.makeAssignment as usual.
               =#
          outStatement
        end

         #= @author: adrpo
          this functions returns true if the given
          statement list contains when statements =#
        function containsWhenStatements(statementList::List{<:SCode.Statement}) ::Bool
              local hasWhenStatements::Bool

              hasWhenStatements = begin
                  local rest::List{SCode.Statement}
                  local tb::List{SCode.Statement}
                  local eb::List{SCode.Statement}
                  local lst::List{SCode.Statement}
                  local eib::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local b4::Bool
                  local blst::List{Bool}
                  local slst::List{List{SCode.Statement}}
                   #=  handle nothingness
                   =#
                @matchcontinue statementList begin
                   nil()  => begin
                    false
                  end

                  SCode.ALG_WHEN_A(__) <| _  => begin
                    true
                  end

                  SCode.ALG_IF(trueBranch = tb, elseIfBranch = eib, elseBranch = eb) <| rest  => begin
                      b1 = containsWhenStatements(tb)
                      b2 = containsWhenStatements(eb)
                      slst = ListUtil.map(eib, Util.tuple22)
                      blst = ListUtil.map(slst, containsWhenStatements)
                      b3 = ListUtil.reduce(_cons(false, blst), boolOr)
                      b4 = containsWhenStatements(rest)
                      b = ListUtil.reduce(list(b1, b2, b3, b4), boolOr)
                    b
                  end

                  SCode.ALG_FOR(forBody = lst) <| rest  => begin
                      b1 = containsWhenStatements(lst)
                      b2 = containsWhenStatements(rest)
                      b = boolOr(b1, b2)
                    b
                  end

                  SCode.ALG_PARFOR(parforBody = lst) <| rest  => begin
                      b1 = containsWhenStatements(lst)
                      b2 = containsWhenStatements(rest)
                      b = boolOr(b1, b2)
                    b
                  end

                  SCode.ALG_WHILE(whileBody = lst) <| rest  => begin
                      b1 = containsWhenStatements(lst)
                      b2 = containsWhenStatements(rest)
                      b = boolOr(b1, b2)
                    b
                  end

                  _ <| rest  => begin
                    containsWhenStatements(rest)
                  end
                end
              end
               #=  yeha! we have a when!
               =#
               #=  search deeper inside if
               =#
               #=  adrpo: add false to handle the case where list might be empty
               =#
               #=  search deeper inside for
               =#
               #=  search deeper inside parfor
               =#
               #=  search deeper inside for
               =#
               #=  not a when, move along
               =#
          hasWhenStatements
        end

         #= @author: adrpo
          Unrolling a for loop is explicitly repeating
          the body of the loop once for each iteration. =#
        function loopOverRange(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, ci_state::ClassInf.SMNode, inIdent::Ident, inValue::Values.Value, inAlgItmLst::List{<:SCode.Statement}, source::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement} #= for statements can produce more statements than one by unrolling =#
              local outCache::FCore.Cache

              (outCache, outStatements) = begin
                  local env_1::FCore.Graph
                  local env_2::FCore.Graph
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local i::String
                  local fst::Values.Value
                  local v::Values.Value
                  local rest::List{Values.Value}
                  local algs::List{SCode.Statement}
                  local initial_::SCode.Initial
                  local impl::Bool
                  local cache::FCore.Cache
                  local dims::List{ModelicaInteger}
                  local dim::ModelicaInteger
                  local stmts::List{DAE.Statement}
                  local stmts1::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local ih::InstanceHierarchy
                   #=  handle empty
                   =#
                @matchcontinue (inCache, inEnv, inIH, inPrefix, ci_state, inIdent, inValue, inAlgItmLst, source, inInitial, inImpl, unrollForLoops) begin
                  (cache, _, _, _, _, _, Values.ARRAY(valueLst =  nil()), _, _, _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, ih, pre, _, i, Values.ARRAY(valueLst = fst <| rest, dimLst = dim <| dims), algs, _, initial_, impl, _)  => begin
                      dim = dim - 1
                      dims = _cons(dim, dims)
                      env_1 = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE())
                      env_2 = FGraph.addForIterator(env_1, i, DAE.T_INTEGER_DEFAULT, DAE.VALBOUND(fst, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.CONST(), SOME(DAE.C_CONST()))
                      (cache, stmts1) = instStatements(cache, env_2, ih, pre, ci_state, algs, source, initial_, impl, unrollForLoops)
                      (cache, stmts2) = loopOverRange(cache, env, ih, pre, ci_state, i, Values.ARRAY(rest, dims), algs, source, initial_, impl, unrollForLoops)
                      stmts = listAppend(stmts1, stmts2)
                    (cache, stmts)
                  end

                  (_, _, _, _, _, _, v, _, _, _, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- InstSection.loopOverRange failed to loop over range: " + ValuesUtil.valString(v))
                    fail()
                  end
                end
              end
               #=  array equation, use instAlgorithms
               =#
               #=  the iterator is not constant but the range is constant
               =#
               #= /* use instEEquation*/ =#
          (outCache, outStatements #= for statements can produce more statements than one by unrolling =#)
        end

         #=
        The function takes a tuple of Absyn.ComponentRef (an array variable) and an integer i
        and constructs the range expression (Absyn.Exp) for the ith dimension of the variable =#
        function rangeExpression(inTuple::Tuple{<:Absyn.ComponentRef, ModelicaInteger}) ::Absyn.Exp
              local outExp::Absyn.Exp

              outExp = begin
                  local e::Absyn.Exp
                  local acref::Absyn.ComponentRef
                  local dimNum::ModelicaInteger
                  local tpl::Tuple{Absyn.ComponentRef, ModelicaInteger}
                @match inTuple begin
                  (acref, dimNum)  => begin
                      e = Absyn.RANGE(Absyn.INTEGER(1), NONE(), Absyn.CALL(Absyn.CREF_IDENT("size", nil), Absyn.FUNCTIONARGS(list(Absyn.CREF(acref), Absyn.INTEGER(dimNum)), nil)))
                    e
                  end
                end
              end
          outExp
        end

        function instIfEqBranch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inEquations::List{<:SCode.EEquation}, inImpl::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, ClassInf.SMNode, List{DAE.Element}}
              local outEquations::List{DAE.Element}
              local outState::ClassInf.SMNode
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              checkForConnectInIfBranch(inEquations)
              @match (outCache, outEnv, outIH, DAE.DAE(outEquations), _, outState, _) = Inst.instList(inCache, inEnv, inIH, inPrefix, DAE.emptySet, inState, instEEquation, inEquations, inImpl, alwaysUnroll, ConnectionGraph.EMPTY)
          (outCache, outEnv, outIH, outState, outEquations)
        end

        function instIfEqBranches(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inBranches::List{<:List{<:SCode.EEquation}}, inImpl::Bool, inAccumEqs::List{<:List{<:DAE.Element}} = nil) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, ClassInf.SMNode, List{List{DAE.Element}}}
              local outEquations::List{List{DAE.Element}}
              local outState::ClassInf.SMNode
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outState, outEquations) = begin
                  local mod::DAE.Mod
                  local pre::Prefix.PrefixType
                  local csets::DAE.Sets
                  local csets_1::DAE.Sets
                  local csets_2::DAE.Sets
                  local ci_state::ClassInf.SMNode
                  local ci_state_1::ClassInf.SMNode
                  local ci_state_2::ClassInf.SMNode
                  local impl::Bool
                  local llb::List{List{DAE.Element}}
                  local es::List{List{SCode.EEquation}}
                  local e::List{SCode.EEquation}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InnerOuter.InstHierarchy
                  local state::ClassInf.SMNode
                  local seq::List{SCode.EEquation}
                  local rest_seq::List{List{SCode.EEquation}}
                  local deq::List{DAE.Element}
                  local branches::List{List{DAE.Element}}
                @match (inCache, inEnv, inIH, inPrefix, inState, inBranches, inImpl, inAccumEqs) begin
                  (cache, env, ih, _, state, seq <| rest_seq, _, _)  => begin
                      (cache, env, ih, state, deq) = instIfEqBranch(cache, env, ih, inPrefix, state, seq, inImpl)
                      (cache, env, ih, state, branches) = instIfEqBranches(cache, env, ih, inPrefix, state, rest_seq, inImpl, _cons(deq, inAccumEqs))
                    (cache, env, ih, state, branches)
                  end

                  (_, _, _, _, _,  nil(), _, _)  => begin
                    (inCache, inEnv, inIH, inState, listReverse(inAccumEqs))
                  end
                end
              end
          (outCache, outEnv, outIH, outState, outEquations)
        end

        function instInitialIfEqBranch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inEquations::List{<:SCode.EEquation}, inImpl::Bool) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, ClassInf.SMNode, List{DAE.Element}}
              local outEquations::List{DAE.Element}
              local outState::ClassInf.SMNode
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              checkForConnectInIfBranch(inEquations)
              @match (outCache, outEnv, outIH, DAE.DAE(outEquations), _, outState, _) = Inst.instList(inCache, inEnv, inIH, inPrefix, DAE.emptySet, inState, instEInitialEquation, inEquations, inImpl, alwaysUnroll, ConnectionGraph.EMPTY)
          (outCache, outEnv, outIH, outState, outEquations)
        end

        function instInitialIfEqBranches(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inBranches::List{<:List{<:SCode.EEquation}}, inImpl::Bool, inAccumEqs::List{<:List{<:DAE.Element}} = nil) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, ClassInf.SMNode, List{List{DAE.Element}}}
              local outEquations::List{List{DAE.Element}}
              local outState::ClassInf.SMNode
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outState, outEquations) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InnerOuter.InstHierarchy
                  local state::ClassInf.SMNode
                  local seq::List{SCode.EEquation}
                  local rest_seq::List{List{SCode.EEquation}}
                  local deq::List{DAE.Element}
                  local branches::List{List{DAE.Element}}
                @match (inCache, inEnv, inIH, inPrefix, inState, inBranches, inImpl, inAccumEqs) begin
                  (cache, env, ih, _, state, seq <| rest_seq, _, _)  => begin
                      (cache, env, ih, state, deq) = instInitialIfEqBranch(cache, env, ih, inPrefix, state, seq, inImpl)
                      (cache, env, ih, state, branches) = instInitialIfEqBranches(cache, env, ih, inPrefix, state, rest_seq, inImpl, _cons(deq, inAccumEqs))
                    (cache, env, ih, state, branches)
                  end

                  (_, _, _, _, _,  nil(), _, _)  => begin
                    (inCache, inEnv, inIH, inState, listReverse(inAccumEqs))
                  end
                end
              end
          (outCache, outEnv, outIH, outState, outEquations)
        end

         #= Checks if an if-branch (a list of equations) contains any connects, and prints
           an error if it does. This is used to check that there are no connects in
           if-equations with non-parameter conditions. =#
        function checkForConnectInIfBranch(inEquations::List{<:SCode.EEquation})
              ListUtil.map_0(inEquations, checkForConnectInIfBranch2)
        end

        function checkForConnectInIfBranch2(inEquation::SCode.EEquation)
              _ = begin
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                  local info::SourceInfo
                  local eqs::List{SCode.EEquation}
                  local cr1_str::String
                  local cr2_str::String
                @match inEquation begin
                  SCode.EQ_CONNECT(crefLeft = cr1, crefRight = cr2, info = info)  => begin
                      cr1_str = Dump.printComponentRefStr(cr1)
                      cr2_str = Dump.printComponentRefStr(cr2)
                      Error.addSourceMessage(Error.CONNECT_IN_IF, list(cr1_str, cr2_str), info)
                    fail()
                  end

                  SCode.EQ_FOR(eEquationLst = eqs)  => begin
                      checkForConnectInIfBranch(eqs)
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
               #=  No need to recurse into if- or when-equations, they will be checked anyway.
               =#
        end

         #= This function helps instStatement to handle elseif parts. =#
        function instElseIfs(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPre::Prefix.PrefixType, ci_state::ClassInf.SMNode, inElseIfBranches::List{<:Tuple{<:Absyn.Exp, List{<:SCode.Statement}}}, source::DAE.ElementSource, initial_::SCode.Initial, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, info::SourceInfo) ::Tuple{FCore.Cache, List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}}
              local outElseIfBranches::List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}
              local outCache::FCore.Cache

              (outCache, outElseIfBranches) = begin
                  local env::FCore.Graph
                  local impl::Bool
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local prop::DAE.Properties
                  local stmts::List{DAE.Statement}
                  local tail_1::List{Tuple{DAE.Exp, DAE.Properties, List{DAE.Statement}}}
                  local e::Absyn.Exp
                  local l::List{SCode.Statement}
                  local tail::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
                  local cache::FCore.Cache
                  local pre::Prefix.PrefixType
                  local ih::InstanceHierarchy
                @matchcontinue (inCache, inEnv, inIH, inPre, ci_state, inElseIfBranches, source, initial_, inImpl, unrollForLoops, info) begin
                  (cache, _, _, _, _,  nil(), _, _, _, _, _)  => begin
                    (cache, nil)
                  end

                  (cache, env, ih, pre, _, (e, l) <| tail, _, _, impl, _, _)  => begin
                      (cache, e_1, prop) = Static.elabExp(cache, env, e, impl, true, pre, info)
                      (cache, e_1, prop) = Ceval.cevalIfConstant(cache, env, e_1, prop, impl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, env, ih, e_1, pre)
                      (cache, stmts) = instStatements(cache, env, ih, pre, ci_state, l, source, initial_, impl, unrollForLoops)
                      (cache, tail_1) = instElseIfs(cache, env, ih, pre, ci_state, tail, source, initial_, impl, unrollForLoops, info)
                    (cache, _cons((e_2, prop, stmts), tail_1))
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.instElseIfs failed\\n")
                      fail()
                  end
                end
              end
          (outCache, outElseIfBranches)
        end

        function instWhenEqBranch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inSets::DAE.Sets, inState::ClassInf.SMNode, inBranch::Tuple{<:Absyn.Exp, List{<:SCode.EEquation}}, inImpl::Bool, inUnrollLoops::Bool, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Exp, List{DAE.Element}, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outEquations::List{DAE.Element}
              local outCondition::DAE.Exp
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              local cond::Absyn.Exp
              local body::List{SCode.EEquation}
              local prop::DAE.Properties
              local aexps::List{Absyn.Exp}
              local dexps::List{DAE.Exp}
              local dexp::DAE.Exp
              local ty::DAE.Type
              local isClock::Bool

              (cond, body) = inBranch
              isClock = false
              outCondition = begin
                @match cond begin
                  Absyn.ARRAY(arrayExp = aexps)  => begin
                      dexps = nil
                      for aexp in aexps
                        (outCache, dexp, prop) = instExp(inCache, inEnv, inIH, inPrefix, aexp, inImpl, info)
                        ty = Types.getPropType(prop)
                        dexp = checkWhenCondition(dexp, ty, aexp, info)
                        dexps = _cons(dexp, dexps)
                      end
                    Expression.makeArray(listReverse(dexps), DAE.T_BOOL_DEFAULT, true)
                  end

                  _  => begin
                        (outCache, dexp, prop) = instExp(inCache, inEnv, inIH, inPrefix, cond, inImpl, info)
                        ty = Types.getPropType(prop)
                        if Types.isClockOrSubTypeClock(ty)
                          isClock = true
                        else
                          dexp = checkWhenCondition(dexp, ty, cond, info)
                        end
                      dexp
                  end
                end
              end
              if ! isClock
                ListUtil.map_0(body, checkForNestedWhenInEq)
              end
               #=  Instantiate the when body.
               =#
              @match (outCache, outEnv, outIH, DAE.DAE(outEquations), _, _, outGraph) = Inst.instList(outCache, inEnv, inIH, inPrefix, inSets, inState, instEEquation, body, inImpl, alwaysUnroll, inGraph)
          (outCache, outEnv, outIH, outCondition, outEquations, outGraph)
        end

        function checkWhenCondition(exp::DAE.Exp, ty::DAE.Type, aexp::Absyn.Exp, info::SourceInfo) ::DAE.Exp


              local tyEl::DAE.Type

              try
                if Types.isArray(ty)
                  tyEl = Types.arrayElementType(ty)
                else
                  tyEl = ty
                end
                exp = Types.matchType(exp, tyEl, DAE.T_BOOL_DEFAULT)
              catch
                Error.addSourceMessage(Error.IF_CONDITION_TYPE_ERROR, list(Dump.printExpStr(aexp), Types.unparseType(ty)), info)
                fail()
              end
              if Config.languageStandardAtLeast(Config.LanguageStandard.S3_2)
                _ = begin
                  @match exp begin
                    DAE.CALL(path = Absyn.IDENT("initial"))  => begin
                      ()
                    end

                    DAE.CALL(path = Absyn.FULLYQUALIFIED(Absyn.IDENT("initial")))  => begin
                      ()
                    end

                    _  => begin
                          if Expression.expHasInitial(exp)
                            Error.addSourceMessage(Error.INITIAL_CALL_WARNING, list(Dump.printExpStr(aexp)), info)
                          end
                        ()
                    end
                  end
                end
              end
          exp
        end

         #=
          Generates connectionsets for connections.
          Parameters and constants in connectors should generate appropriate assert statements.
          Hence, a DAE.Element list is returned as well. =#
        function instConnect(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix::Prefix.PrefixType, inComponentRefLeft::Absyn.ComponentRef, inComponentRefRight::Absyn.ComponentRef, inImplicit::Bool, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local c1_1::DAE.ComponentRef
                  local c2_1::DAE.ComponentRef
                  local c1_2::DAE.ComponentRef
                  local c2_2::DAE.ComponentRef
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local attr1::DAE.Attributes
                  local attr2::DAE.Attributes
                  local ct1::DAE.ConnectorType
                  local ct2::DAE.ConnectorType
                  local impl::Bool
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local f1::DAE.Face
                  local f2::DAE.Face
                  local sets::DAE.Sets
                  local dae::DAE.DAElist
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local c1::Absyn.ComponentRef
                  local c2::Absyn.ComponentRef
                  local cache::FCore.Cache
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local prl1::SCode.Parallelism
                  local prl2::SCode.Parallelism
                  local vt1::SCode.Variability
                  local vt2::SCode.Variability
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local subs1::List{Absyn.Subscript}
                  local subs2::List{Absyn.Subscript}
                  local crefs1::List{Absyn.ComponentRef}
                  local crefs2::List{Absyn.ComponentRef}
                  local s1::String
                  local s2::String
                  local del1::Bool
                  local del2::Bool
                   #=  adrpo: check for connect(A, A) as we should give a warning and remove it!
                   =#
                @matchcontinue (inCache, inEnv, inIH, inSets, inPrefix, inComponentRefLeft, inComponentRefRight, inImplicit, inGraph) begin
                  (cache, env, ih, sets, _, c1, c2, _, graph)  => begin
                      @match true = AbsynUtil.crefEqual(c1, c2)
                      s1 = Dump.printComponentRefStr(c1)
                      s2 = Dump.printComponentRefStr(c1)
                      Error.addSourceMessage(Error.SAME_CONNECT_INSTANCE, list(s1, s2), info)
                    (cache, env, ih, sets, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, c2, impl, graph)  => begin
                       #=  handle normal connectors!
                       =#
                      (cache, c1_2, attr1, ct1, vt1, io1, f1, ty1, del1) = instConnector(cache, env, ih, c1, impl, pre, info)
                      (cache, c2_2, attr2, _, vt2, io2, f2, ty2, del2) = instConnector(cache, env, ih, c2, impl, pre, info)
                      if del1 || del2
                        dae = DAE.emptyDae
                      elseif Types.isExpandableConnector(ty1) || Types.isExpandableConnector(ty2)
                        fail()
                      else
                        checkConnectTypes(c1_2, ty1, f1, attr1, c2_2, ty2, f2, attr2, info)
                        (cache, _, ih, sets, dae, graph) = connectComponents(cache, env, ih, sets, pre, c1_2, f1, ty1, vt1, c2_2, f2, ty2, vt2, ct1, io1, io2, graph, info)
                        sets = ConnectUtil.increaseConnectRefCount(c1_2, c2_2, sets)
                      end
                       #=  If either connector is a deleted conditional component, discard the connection.
                       =#
                       #=  If either connector is expandable, fail and use the next case.
                       =#
                       #=  Otherwise it's a normal connection.
                       =#
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, c2, impl, graph)  => begin
                      ErrorExt.setCheckpoint("expandableConnectors")
                      @match true = System.getHasExpandableConnectors()
                      (cache, env, ih, sets, dae, graph) = connectExpandableConnectors(cache, env, ih, sets, pre, c1, c2, impl, graph, info)
                      ErrorExt.rollBack("expandableConnectors")
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, _, _, pre, c1, c2, _, _)  => begin
                      ErrorExt.rollBack("expandableConnectors")
                      subs1 = AbsynUtil.getSubsFromCref(c1, true, true)
                      crefs1 = AbsynUtil.getCrefsFromSubs(subs1, true, true)
                      subs2 = AbsynUtil.getSubsFromCref(c2, true, true)
                      crefs2 = AbsynUtil.getCrefsFromSubs(subs2, true, true)
                      s1 = Dump.printComponentRefStr(c1)
                      s2 = Dump.printComponentRefStr(c2)
                      s1 = "connect(" + s1 + ", " + s2 + ")"
                      checkConstantVariability(crefs1, cache, env, s1, pre, info)
                      checkConstantVariability(crefs2, cache, env, s1, pre, info)
                    fail()
                  end

                  (cache, env, ih, sets, _, _, _, _, graph) where (Config.getGraphicsExpMode())  => begin
                    (cache, env, ih, sets, DAE.emptyDae, graph)
                  end

                  (_, _, _, _, _, c1, c2, _, _)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- InstSection.instConnect failed for: connect(" + Dump.printComponentRefStr(c1) + ", " + Dump.printComponentRefStr(c2) + ")")
                    fail()
                  end
                end
              end
               #=  adrpo: handle expandable connectors!
               =#
               #=  Case to display error for non constant subscripts in connectors
               =#
               #= print(\"Crefs in \" + Dump.printComponentRefStr(c1) + \": \" + stringDelimitList(List.map(crefs1,Dump.printComponentRefStr),\", \") + \"\\n\");
               =#
               #= print(\"Crefs in \" + Dump.printComponentRefStr(c2) + \": \" + stringDelimitList(List.map(crefs2,Dump.printComponentRefStr),\", \") + \"\\n\");
               =#
               #=  Failed in graphics mode; just continue
               =#
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

        function instConnector(inCache::FCore.Cache, env::FCore.Graph, ih::InnerOuter.InstHierarchy, connectorCref::Absyn.ComponentRef, impl::Bool, prefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.ComponentRef, DAE.Attributes, DAE.ConnectorType, SCode.Variability, Absyn.InnerOuter, DAE.Face, DAE.Type, Bool}
              local deleted::Bool
              local ty::DAE.Type
              local face::DAE.Face
              local innerOuter::Absyn.InnerOuter
              local variability::SCode.Variability
              local connectorType::DAE.ConnectorType
              local outAttr::DAE.Attributes
              local outCref::DAE.ComponentRef
              local outCache::FCore.Cache = inCache

              local status::FCore.Status
              local is_expandable::Bool

              outCref = ComponentReference.toExpCref(connectorCref)
              @match (DAE.ATTR(connectorType = connectorType, variability = variability, innerOuter = innerOuter), ty, status, is_expandable) = Lookup.lookupConnectorVar(env, outCref)
              deleted = FCore.isDeletedComp(status)
              if deleted || is_expandable
                face = DAE.NO_FACE()
                outAttr = DAE.dummyAttrVar
              else
                @match (outCache, DAE.CREF(componentRef = outCref), DAE.PROP(type_ = ty), outAttr) = Static.elabCrefNoEval(inCache, env, connectorCref, impl, false, prefix, info)
                (outCache, outCref) = Static.canonCref(outCache, env, outCref, impl)
                validConnector(ty, outCref, info)
                face = ConnectUtil.componentFace(env, outCref)
                ty = sortConnectorType(ty)
              end
          (outCache, outCref, outAttr, connectorType, variability, innerOuter, face, ty, deleted)
        end

        function sortConnectorType(inType::DAE.Type) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                  local dims::DAE.Dimensions
                  local ci_state::ClassInf.SMNode
                  local vars::List{DAE.Var}
                  local ec::DAE.EqualityConstraint
                @match inType begin
                  DAE.T_ARRAY(ty, dims)  => begin
                      ty = sortConnectorType(ty)
                    DAE.T_ARRAY(ty, dims)
                  end

                  DAE.T_COMPLEX(ci_state, vars, ec)  => begin
                      vars = ListUtil.sort(vars, connectorCompGt)
                    DAE.T_COMPLEX(ci_state, vars, ec)
                  end

                  _  => begin
                      inType
                  end
                end
              end
          outType
        end

        function connectorCompGt(inVar1::DAE.Var, inVar2::DAE.Var) ::Bool
              local outGt::Bool

              local id1::DAE.Ident
              local id2::DAE.Ident

              @match DAE.TYPES_VAR(name = id1) = inVar1
              @match DAE.TYPES_VAR(name = id2) = inVar2
              outGt = 1 == stringCompare(id1, id2)
          outGt
        end

         #=
        Author BZ, 2009-09
          Helper function for instConnect, prints error message for the case with non constant(or parameter) subscript(/s) =#
        function checkConstantVariability(inrefs::List{<:Absyn.ComponentRef}, cache::FCore.Cache, env::FCore.Graph, affectedConnector::String, inPrefix::Prefix.PrefixType, info::SourceInfo)
              _ = begin
                  local cr::Absyn.ComponentRef
                  local prop::DAE.Properties
                  local constVar::DAE.Const
                  local pre::Prefix.PrefixType
                  local s1::String
                  local refs::List{Absyn.ComponentRef}
                @matchcontinue (inrefs, cache, env, affectedConnector, inPrefix, info) begin
                  ( nil(), _, _, _, _, _)  => begin
                    ()
                  end

                  (cr <| refs, _, _, _, pre, _)  => begin
                      @match (_, SOME((_, prop, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      constVar = Types.propertiesListToConst(list(prop))
                      @match true = Types.isParameterOrConstant(constVar)
                      checkConstantVariability(refs, cache, env, affectedConnector, pre, info)
                    ()
                  end

                  (cr <| _, _, _, _, pre, _)  => begin
                      @match (_, SOME((_, prop, _))) = Static.elabCref(cache, env, cr, false, false, pre, info)
                      constVar = Types.propertiesListToConst(list(prop))
                      @match false = Types.isParameterOrConstant(constVar)
                      s1 = Dump.printComponentRefStr(cr)
                      Error.addSourceMessage(Error.CONNECTOR_ARRAY_NONCONSTANT, list(affectedConnector, s1), info)
                    ()
                  end
                end
              end
        end

         #= @author: adrpo
          this function handle the connections of expandable connectors =#
        function connectExpandableConnectors(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix::Prefix.PrefixType, inComponentRefLeft::Absyn.ComponentRef, inComponentRefRight::Absyn.ComponentRef, inImpl::Bool, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local c1_1::DAE.ComponentRef
                  local c2_1::DAE.ComponentRef
                  local c1_2::DAE.ComponentRef
                  local c2_2::DAE.ComponentRef
                  local c1p::DAE.ComponentRef
                  local c2p::DAE.ComponentRef
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local attr1::DAE.Attributes
                  local attr2::DAE.Attributes
                  local attr::DAE.Attributes
                  local ct1::DAE.ConnectorType
                  local ct2::DAE.ConnectorType
                  local impl::Bool
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local ty::DAE.Type
                  local sets::DAE.Sets
                  local dae::DAE.DAElist
                  local daeExpandable::DAE.DAElist
                  local env::FCore.Graph
                  local envExpandable::FCore.Graph
                  local envComponent::FCore.Graph
                  local env1::FCore.Graph
                  local env2::FCore.Graph
                  local envComponentEmpty::FCore.Graph
                  local pre::Prefix.PrefixType
                  local c1::Absyn.ComponentRef
                  local c2::Absyn.ComponentRef
                  local c1_prefix::Absyn.ComponentRef
                  local cache::FCore.Cache
                  local io1::Absyn.InnerOuter
                  local io2::Absyn.InnerOuter
                  local vt1::SCode.Variability
                  local vt2::SCode.Variability
                  local prl1::SCode.Parallelism
                  local prl2::SCode.Parallelism
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local componentName::String
                  local dir1::Absyn.Direction
                  local dir2::Absyn.Direction
                  local binding::DAE.Binding
                  local cnstForRange::Option{DAE.Const}
                  local splicedExpData::InstTypes.SplicedExpData
                  local state::ClassInf.SMNode
                  local variables1::List{String}
                  local variables2::List{String}
                  local variablesUnion::List{String}
                  local source::DAE.ElementSource
                  local vis1::SCode.Visibility
                  local vis2::SCode.Visibility
                  local arrDims::Absyn.ArrayDim
                  local daeDims::DAE.Dimensions
                   #=  both c1 and c2 are expandable
                   =#
                @matchcontinue (inCache, inEnv, inIH, inSets, inPrefix, inComponentRefLeft, inComponentRefRight, inImpl, inGraph, info) begin
                  (cache, env, ih, sets, pre, c1, c2, impl, graph, _)  => begin
                      @match (cache, SOME((DAE.CREF(c1_1, _), _, attr1))) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      @match (cache, SOME((DAE.CREF(c2_1, _), _, attr2))) = Static.elabCref(cache, env, c2, impl, false, pre, info)
                      (cache, c1_2) = Static.canonCref(cache, env, c1_1, impl)
                      (cache, c2_2) = Static.canonCref(cache, env, c2_1, impl)
                      (attr1, ty1) = Lookup.lookupConnectorVar(env, c1_2)
                      (attr2, ty2) = Lookup.lookupConnectorVar(env, c2_2)
                      @match DAE.ATTR(connectorType = DAE.POTENTIAL()) = attr1
                      @match DAE.ATTR(connectorType = DAE.POTENTIAL()) = attr2
                      @match true = Types.isExpandableConnector(ty1)
                      @match true = Types.isExpandableConnector(ty2)
                      (_, _, _, _, _, _, _, env1, _) = Lookup.lookupVar(cache, env, c1_2)
                      (_, _, _, _, _, _, _, env2, _) = Lookup.lookupVar(cache, env, c2_2)
                      variables1 = FGraph.getVariablesFromGraphScope(env1)
                      variables2 = FGraph.getVariablesFromGraphScope(env2)
                      variablesUnion = ListUtil.union(variables1, variables2)
                      variablesUnion = ListUtil.sort(variablesUnion, Util.strcmpBool)
                      (cache, env, ih, sets, dae, graph) = connectExpandableVariables(cache, env, ih, sets, pre, c1, c2, variablesUnion, impl, graph, info)
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, c2, impl, graph, _)  => begin
                      @match (cache, NONE()) = Static.elabCref(cache, env, c2, impl, false, pre, info)
                      @match (cache, SOME((DAE.CREF(_, _), _, _))) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      (cache, env, ih, sets, dae, graph) = connectExpandableConnectors(cache, env, ih, sets, pre, c2, c1, impl, graph, info)
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, _, _, pre, c1 && Absyn.CREF_IDENT(__), c2, impl, _, _)  => begin
                      @match (cache, NONE()) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      print("Error: The marked virtual expandable component reference in connect([" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + "." + AbsynUtil.printComponentRefStr(c1) + "], " + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + "." + AbsynUtil.printComponentRefStr(c2) + "); should be qualified, i.e. expandableConnectorName.virtualName!\\n")
                    fail()
                  end

                  (cache, env, ih, sets, pre, c1 && Absyn.CREF_QUAL(__), c2, impl, graph, _)  => begin
                      @match (cache, NONE()) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      @match (cache, SOME((DAE.CREF(c2_1, _), _, attr2))) = Static.elabCref(cache, env, c2, impl, false, pre, info)
                      (cache, c2_2) = Static.canonCref(cache, env, c2_1, impl)
                      (attr2, ty2) = Lookup.lookupConnectorVar(env, c2_2)
                      @match DAE.ATTR(ct2, prl2, vt2, _, io2, vis2) = attr2
                      c1_prefix = AbsynUtil.crefStripLast(c1)
                      @match (cache, SOME((DAE.CREF(c1_1, _), _, _))) = Static.elabCref(cache, env, c1_prefix, impl, false, pre, info)
                      (cache, c1_2) = Static.canonCref(cache, env, c1_1, impl)
                      (_, ty1) = Lookup.lookupConnectorVar(env, c1_2)
                      @match true = Types.isExpandableConnector(ty1)
                      c1_2 = ComponentReference.crefStripLastSubs(c1_2)
                      (_, attr, ty, binding, cnstForRange, _, _, envExpandable, _) = Lookup.lookupVar(cache, env, c1_2)
                      (_, _, _, _, _, _, _, envComponent, _) = Lookup.lookupVar(cache, env, c2_2)
                      variablesUnion = FGraph.getVariablesFromGraphScope(envComponent)
                      @match true = listLength(variablesUnion) > 1
                      @match Absyn.CREF_IDENT(componentName, _) = AbsynUtil.crefGetLastIdent(c1)
                      envComponentEmpty = FGraph.removeComponentsFromScope(envComponent)
                      daeDims = Types.getDimensions(ty2)
                      arrDims = ListUtil.map(daeDims, Expression.unelabDimension)
                      envExpandable = FGraph.cloneLastScopeRef(envExpandable)
                      envExpandable = FGraph.mkComponentNode(envExpandable, DAE.TYPES_VAR(componentName, DAE.ATTR(ct2, prl2, vt2, Absyn.BIDIR(), io2, vis2), ty2, DAE.UNBOUND(), NONE()), SCode.COMPONENT(componentName, SCode.defaultPrefixes, SCode.ATTR(arrDims, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), DAE.NOMOD(), FCore.VAR_TYPED(), envComponentEmpty)
                      env = updateEnvComponentsOnQualPath(cache, env, c1_2, attr, ty, binding, cnstForRange, envExpandable)
                      (cache, env, ih, sets, dae, graph) = connectExpandableVariables(cache, env, ih, sets, pre, c1, c2, variablesUnion, impl, graph, info)
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1 && Absyn.CREF_QUAL(__), c2, impl, graph, _)  => begin
                      @match (cache, NONE()) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      @match (cache, SOME((DAE.CREF(c2_1, _), _, attr2))) = Static.elabCref(cache, env, c2, impl, false, pre, info)
                      (cache, c2_2) = Static.canonCref(cache, env, c2_1, impl)
                      (attr2, ty2) = Lookup.lookupConnectorVar(env, c2_2)
                      @match DAE.ATTR(ct2, prl2, vt2, _, io2, vis2) = attr2
                      c1_prefix = AbsynUtil.crefStripLast(c1)
                      @match (cache, SOME((DAE.CREF(c1_1, _), _, _))) = Static.elabCref(cache, env, c1_prefix, impl, false, pre, info)
                      (cache, c1_2) = Static.canonCref(cache, env, c1_1, impl)
                      (attr1, ty1) = Lookup.lookupConnectorVar(env, c1_2)
                      @match true = Types.isExpandableConnector(ty1)
                      c1_2 = ComponentReference.crefStripLastSubs(c1_2)
                      (_, attr, ty, binding, cnstForRange, _, _, envExpandable, _) = Lookup.lookupVar(cache, env, c1_2)
                      (_, _, _, _, _, _, _, envComponent, _) = Lookup.lookupVar(cache, env, c2_2)
                      variablesUnion = FGraph.getVariablesFromGraphScope(envComponent)
                      @match false = listLength(variablesUnion) > 1
                      @match Absyn.CREF_IDENT(componentName, _) = AbsynUtil.crefGetLastIdent(c1)
                      envComponentEmpty = FGraph.removeComponentsFromScope(envComponent)
                      daeDims = Types.getDimensions(ty2)
                      arrDims = ListUtil.map(daeDims, Expression.unelabDimension)
                      envExpandable = FGraph.mkComponentNode(envExpandable, DAE.TYPES_VAR(componentName, DAE.ATTR(ct2, prl2, vt2, Absyn.BIDIR(), io2, vis2), ty2, DAE.UNBOUND(), NONE()), SCode.COMPONENT(componentName, SCode.defaultPrefixes, SCode.ATTR(arrDims, SCode.POTENTIAL(), SCode.NON_PARALLEL(), SCode.VAR(), Absyn.BIDIR(), Absyn.NONFIELD()), Absyn.TPATH(Absyn.IDENT(""), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), DAE.NOMOD(), FCore.VAR_TYPED(), envComponentEmpty)
                      env = updateEnvComponentsOnQualPath(cache, env, c1_2, attr, ty, binding, cnstForRange, envExpandable)
                      @match (cache, SOME((DAE.CREF(c1_1, _), _, _))) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      (cache, c1_2) = Static.canonCref(cache, env, c1_1, impl)
                      (attr1, ty1) = Lookup.lookupConnectorVar(env, c1_2)
                      @match DAE.ATTR(ct1, prl1, vt1, _, io1, vis1) = attr1
                      (cache, env, ih, sets, dae, graph) = instConnect(cache, env, ih, sets, pre, c1, c2, impl, graph, info)
                      state = ClassInf.CONNECTOR(Absyn.IDENT("expandable connector"), true)
                      (cache, c1p) = PrefixUtil.prefixCref(cache, env, ih, pre, c1_2)
                      (cache, c2p) = PrefixUtil.prefixCref(cache, env, ih, pre, c2_2)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1p, c2p))
                      (cache, c1_2) = PrefixUtil.prefixCref(cache, env, ih, pre, c1_2)
                      daeDims = Types.getDimensions(ty1)
                      arrDims = ListUtil.map(daeDims, Expression.unelabDimension)
                      daeExpandable = generateExpandableDAE(cache, env, envExpandable, c1_2, state, ty1, SCode.ATTR(arrDims, DAEUtil.toSCodeConnectorType(ct1), prl1, vt1, Absyn.BIDIR(), Absyn.NONFIELD()), vis1, io1, source)
                      dae = DAEUtil.joinDaes(dae, daeExpandable)
                    (cache, env, ih, sets, dae, graph)
                  end

                  (cache, env, _, _, pre, c1, c2, impl, _, _)  => begin
                      @match (cache, SOME((DAE.CREF(c1_1, _), _, _))) = Static.elabCref(cache, env, c1, impl, false, pre, info)
                      @match (cache, SOME((DAE.CREF(c2_1, _), _, _))) = Static.elabCref(cache, env, c2, impl, false, pre, info)
                      (cache, c1_2) = Static.canonCref(cache, env, c1_1, impl)
                      (cache, c2_2) = Static.canonCref(cache, env, c2_1, impl)
                      (_, ty1) = Lookup.lookupConnectorVar(env, c1_2)
                      (_, ty2) = Lookup.lookupConnectorVar(env, c2_2)
                      @match false = Types.isExpandableConnector(ty1)
                      @match false = Types.isExpandableConnector(ty2)
                    fail()
                  end
                end
              end
               #=  do the union of the connectors by adding the missing
               =#
               #=  components from one to the other and vice-versa.
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \">>>> connect(expandable, expandable)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\" );
               =#
               #=  get the environments of the expandable connectors
               =#
               #=  which contain all the virtual components.
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"1 connect(expandable, expandable)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\" );
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env ===>\\n\" + FGraph.printGraphStr(env));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env(c1) ===>\\n\" + FGraph.printGraphStr(env1));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env(c2) ===>\\n\" + FGraph.printGraphStr(env2));
               =#
               #=  get the virtual components
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"Variables1: \" + stringDelimitList(variables1, \", \"));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"Variables2: \" + stringDelimitList(variables2, \", \"));
               =#
               #=  sort so we have them in order
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"Union of expandable connector variables: \" + stringDelimitList(variablesUnion, \", \"));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"2 connect(expandable, expandable)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  then connect each of the components normally.
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"<<<< connect(expandable, expandable)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  c2 is expandable, forward to c1 expandable by switching arguments.
               =#
               #=  c2 is expandable
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"connect(existing, expandable)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  c1 is expandable, catch error that c1 is an IDENT! it should be at least a.x
               =#
               #=  c1 is expandable
               =#
               #=  adrpo: TODO! FIXME! add this as an Error not as a print!
               =#
               #=  c1 is expandable and c2 is existing BUT contains MORE THAN 1 component
               =#
               #=  c1 is expandable and SHOULD be qualified!
               =#
               #=  c1 is expandable
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \">>>> connect(expandable, existing)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  lookup the existing connector
               =#
               #=  bind the attributes
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"1 connect(expandable, existing)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  strip the last prefix!
               =#
               #=  elab expandable connector
               =#
               #=  lookup the expandable connector
               =#
               #=  make sure is expandable!
               =#
               #=  strip last subs to get the full type!
               =#
               #=  we have more than 1 variables in the envComponent, we need to add an empty environment for c1
               =#
               #=  and dive into!
               =#
               #=  more than 1 variables
               =#
               #=  print(\"VARS MULTIPLE: [\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \"/\" + ComponentReference.printComponentRefStr(c2_2) + \"] \" + stringDelimitList(variablesUnion, \", \") + \"\\n\");
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"2 connect(expandable, existing[MULTIPLE])(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  get the virtual component name
               =#
               #=  get the dimensions from the type!
               =#
               #=  add to the environment of the expandable
               =#
               #=  connector the new virtual variable.
               =#
               #=  add empty here to connect individual components!
               =#
               #=  ******************************************************************************
               =#
               #=  here we need to update the correct environment.
               =#
               #=  walk the cref: c1_2 and update all the corresponding environments on the path:
               =#
               #=  Example: c1_2 = a.b.c -> update env c, update env b with c, update env a with b!
               =#
               #=  ******************************************************************************
               =#
               #=  c1 = AbsynUtil.joinCrefs(ComponentReference.unelabCref(c1_2), Absyn.CREF_IDENT(componentName, {}));
               =#
               #=  then connect each of the components normally.
               =#
               #=  c1 is expandable and SHOULD be qualified!
               =#
               #=  c1 is expandable
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \">>>> connect(expandable, existing)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  lookup the existing connector
               =#
               #=  bind the attributes
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"1 connect(expandable, existing)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  strip the last prefix!
               =#
               #=  elab expandable connector
               =#
               #=  lookup the expandable connector
               =#
               #=  make sure is expandable!
               =#
               #=  strip last subs to get the full type!
               =#
               #=  we have more than 1 variables in the envComponent, we need to add an empty environment for c1
               =#
               #=  and dive into!
               =#
               #=  max 1 variable, should check for empty!
               =#
               #=  print(\"VARS SINGLE: [\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \"/\" + ComponentReference.printComponentRefStr(c2_2) + \"] \" + stringDelimitList(variablesUnion, \", \") + \"\\n\");
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"2 connect(expandable, existing[SINGLE])(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  get the virtual component name
               =#
               #=  get the dimensions from the type!
               =#
               #=  add to the environment of the expandable
               =#
               #=  connector the new virtual variable.
               =#
               #=  ******************************************************************************
               =#
               #=  here we need to update the correct environment.
               =#
               #=  walk the cref: c1_2 and update all the corresponding environments on the path:
               =#
               #=  Example: c1_2 = a.b.c -> update env c, update env b with c, update env a with b!
               =#
               #=  ******************************************************************************
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"3 connect(expandable, existing[SINGLE])(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env expandable: \" + FGraph.printGraphStr(envExpandable));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env component: \" + FGraph.printGraphStr(envComponent));
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"env: \" + FGraph.printGraphStr(env));
               =#
               #=  use the cannon cref here as we will NOT find [i] in this environment!!!!
               =#
               #=  c1 = AbsynUtil.joinCrefs(ComponentReference.unelabCref(c1_2), Absyn.CREF_IDENT(componentName, {}));
               =#
               #=  now it should be in the Env, fetch the info!
               =#
               #=  bind the attributes
               =#
               #=  then connect the components normally.
               =#
               #=  adrpo: TODO! FIXME! check if is OK
               =#
               #=  declare the added component in the DAE!
               =#
               #=  get the dimensions from the ty1 type!
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"<<<< connect(expandable, existing)(\" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c1) + \", \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \".\" + Dump.printComponentRefStr(c2) + \")\");  \\nDAE:\" + DAEDump.dumpStr(daeExpandable, DAE.AvlTreePathFunction.Tree.EMPTY()));
               =#
               #=  both c1 and c2 are non expandable!
               =#
               #=  both of these are OK
               =#
               #=  non-expandable
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"connect(non-expandable, non-expandable)(\" + Dump.printComponentRefStr(c1) + \", \" + Dump.printComponentRefStr(c2) + \")\");
               =#
               #=  then connect the components normally.
               =#
               #=  fail to enter connect normally
               =#
               #= /*/ failtrace
                  case (cache,env,_,_,pre,c1,c2,impl,_,_)
                    equation
                      true = Flags.isSet(Flags.SHOW_EXPANDABLE_INFO);
                      (cache,_) = Static.elabCref(cache, env, c1, impl, false, pre, info);
                      (cache,_) = Static.elabCref(cache, env, c2, impl, false, pre, info);

                      fprintln(Flags.SHOW_EXPANDABLE_INFO,
                         \"connect(?, ?)(\" +
                           Dump.printComponentRefStr(c1) + \", \" +
                           Dump.printComponentRefStr(c2) + \")\"
                         );
                    then
                      fail();*/ =#
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

         #= @author: adrpo
         connect(expandable, non-expandable)
         should generate a DAE for the expandable part.
         Expand the array if needed. =#
        function generateExpandableDAE(inCache::FCore.Cache, inParentEnv::FCore.Graph, inClassEnv::FCore.Graph, cref::DAE.ComponentRef, state::ClassInf.SMNode, ty::DAE.Type, attrs::SCode.Attributes, vis::SCode.Visibility, io::Absyn.InnerOuter, source::DAE.ElementSource) ::DAE.DAElist
              local outDAE::DAE.DAElist

              outDAE = begin
                  local arrDims::Absyn.ArrayDim
                  local daeDims::DAE.Dimensions
                  local daeExpandable::DAE.DAElist
                  local crefs::List{DAE.ComponentRef}
                   #=  scalars and arrays
                   =#
                @match (inCache, inParentEnv, inClassEnv, cref, state, ty, attrs, vis, io, source) begin
                  (_, _, _, _, _, _, _, _, _, _)  => begin
                      daeDims = Types.getDimensions(ty)
                      _ = ListUtil.map(daeDims, Expression.unelabDimension)
                      if listEmpty(daeDims)
                        daeExpandable = InstDAE.daeDeclare(inCache, inParentEnv, inClassEnv, cref, state, ty, attrs, vis, NONE(), nil, NONE(), NONE(), SOME(SCode.COMMENT(NONE(), SOME("virtual variable in expandable connector"))), io, SCode.NOT_FINAL(), source, true)
                      else
                        crefs = ComponentReference.expandCref(cref, false)
                        daeExpandable = daeDeclareList(inCache, inParentEnv, inClassEnv, listReverse(crefs), state, ty, attrs, vis, io, source, DAE.emptyDae)
                      end
                    daeExpandable
                  end
                end
              end
          outDAE
        end

         #= declare a list of crefs, one for each array element =#
        function daeDeclareList(inCache::FCore.Cache, inParentEnv::FCore.Graph, inClassEnv::FCore.Graph, crefs::List{<:DAE.ComponentRef}, state::ClassInf.SMNode, ty::DAE.Type, attrs::SCode.Attributes, vis::SCode.Visibility, io::Absyn.InnerOuter, source::DAE.ElementSource, acc::DAE.DAElist) ::DAE.DAElist
              local outDAE::DAE.DAElist

              outDAE = begin
                  local arrDims::Absyn.ArrayDim
                  local daeDims::DAE.Dimensions
                  local daeExpandable::DAE.DAElist
                  local lst::List{DAE.ComponentRef}
                  local cref::DAE.ComponentRef
                @match (inCache, inParentEnv, inClassEnv, crefs, state, ty, attrs, vis, io, source, acc) begin
                  (_, _, _,  nil(), _, _, _, _, _, _, _)  => begin
                    acc
                  end

                  (_, _, _, cref <| lst, _, _, _, _, _, _, _)  => begin
                      daeExpandable = InstDAE.daeDeclare(inCache, inParentEnv, inClassEnv, cref, state, ty, attrs, vis, NONE(), nil, NONE(), NONE(), SOME(SCode.COMMENT(NONE(), SOME("virtual variable in expandable connector"))), io, SCode.NOT_FINAL(), source, true)
                      daeExpandable = DAEUtil.joinDaes(daeExpandable, acc)
                      daeExpandable = daeDeclareList(inCache, inParentEnv, inClassEnv, lst, state, ty, attrs, vis, io, source, daeExpandable)
                    daeExpandable
                  end
                end
              end
          outDAE
        end

         #= @author: adrpo 2010-10-05
          This function will fetch the environments on the
          cref path and update the last one with the given input,
          then update all the environment back to the root.
          Example:
            input: env[a], a.b.c.d, env[d]
            update env[c] with env[d]
            update env[b] with env[c]
            update env[a] with env[b] =#
        function updateEnvComponentsOnQualPath(inCache::FCore.Cache #= cache =#, inEnv::FCore.Graph #= the environment we should update! =#, virtualExpandableCref::DAE.ComponentRef, virtualExpandableAttr::DAE.Attributes, virtualExpandableTy::DAE.Type, virtualExpandableBinding::DAE.Binding, virtualExpandableCnstForRange::Option{<:DAE.Const}, virtualExpandableEnv::FCore.Graph #= the virtual component environment! =#) ::FCore.Graph
              local outEnv::FCore.Graph #= the returned updated environment =#

              outEnv = begin
                  local cache::FCore.Cache
                  local topEnv::FCore.Graph #= the environment we should update! =#
                  local veCref::DAE.ComponentRef
                  local qualCref::DAE.ComponentRef
                  local veAttr::DAE.Attributes
                  local currentAttr::DAE.Attributes
                  local veTy::DAE.Type
                  local currentTy::DAE.Type
                  local veBinding::DAE.Binding
                  local currentBinding::DAE.Binding
                  local veCnstForRange::Option{DAE.Const}
                  local currentCnstForRange::Option{DAE.Const}
                  local veEnv::FCore.Graph #= the virtual component environment! =#
                  local updatedEnv::FCore.Graph #= the returned updated environment =#
                  local currentEnv::FCore.Graph
                  local realEnv::FCore.Graph
                  local forLoopScope::FCore.Scope
                  local currentName::String
                   #=  we have reached the top, update and return!
                   =#
                @match (inCache, inEnv, virtualExpandableCref, virtualExpandableAttr, virtualExpandableTy, virtualExpandableBinding, virtualExpandableCnstForRange, virtualExpandableEnv) begin
                  (_, topEnv, DAE.CREF_IDENT(ident = currentName), veAttr, veTy, veBinding, veCnstForRange, veEnv)  => begin
                      (realEnv, forLoopScope) = FGraph.splitGraphScope(topEnv)
                      updatedEnv = FGraph.updateComp(realEnv, DAE.TYPES_VAR(currentName, veAttr, veTy, veBinding, veCnstForRange), FCore.VAR_TYPED(), veEnv)
                      updatedEnv = FGraph.pushScope(updatedEnv, forLoopScope)
                    updatedEnv
                  end

                  (cache, topEnv, veCref && DAE.CREF_QUAL(__), veAttr, veTy, veBinding, veCnstForRange, veEnv)  => begin
                      currentName = ComponentReference.crefLastIdent(veCref)
                      qualCref = ComponentReference.crefStripLastIdent(veCref)
                      qualCref = ComponentReference.crefStripLastSubs(qualCref)
                      (_, currentAttr, currentTy, currentBinding, currentCnstForRange, _, _, currentEnv, _) = Lookup.lookupVar(cache, topEnv, qualCref)
                      (realEnv, forLoopScope) = FGraph.splitGraphScope(currentEnv)
                      currentEnv = FGraph.updateComp(realEnv, DAE.TYPES_VAR(currentName, veAttr, veTy, veBinding, veCnstForRange), FCore.VAR_TYPED(), veEnv)
                      currentEnv = FGraph.pushScope(currentEnv, forLoopScope)
                      updatedEnv = updateEnvComponentsOnQualPath(cache, topEnv, qualCref, currentAttr, currentTy, currentBinding, currentCnstForRange, currentEnv)
                    updatedEnv
                  end
                end
              end
               #=  update the topEnv
               =#
               #=  if we have a.b.x, update b with x and call us recursively with a.b
               =#
               #=  get the last one
               =#
               #=  strip the last one
               =#
               #=  strip the last subs
               =#
               #=  find the correct environment to update
               =#
               #=  update the current environment!
               =#
               #=  call us recursively to reach the top!
               =#
          outEnv #= the returned updated environment =#
        end

         #= @author: adrpo
          this function handle the connections of expandable connectors
          that contain components =#
        function connectExpandableVariables(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix::Prefix.PrefixType, inComponentRefLeft::Absyn.ComponentRef, inComponentRefRight::Absyn.ComponentRef, inVariablesUnion::List{<:String}, inImpl::Bool, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local impl::Bool
                  local sets::DAE.Sets
                  local dae::DAE.DAElist
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local c1::Absyn.ComponentRef
                  local c2::Absyn.ComponentRef
                  local c1_full::Absyn.ComponentRef
                  local c2_full::Absyn.ComponentRef
                  local cache::FCore.Cache
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local names::List{String}
                  local name::String
                   #=  handle empty case
                   =#
                @match (inCache, inEnv, inIH, inSets, inPrefix, inComponentRefLeft, inComponentRefRight, inVariablesUnion, inImpl, inGraph, info) begin
                  (cache, env, ih, sets, _, _, _,  nil(), _, graph, _)  => begin
                    (cache, env, ih, sets, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, c2, name <| names, impl, graph, _)  => begin
                      c1_full = AbsynUtil.joinCrefs(c1, Absyn.CREF_IDENT(name, nil))
                      c2_full = AbsynUtil.joinCrefs(c2, Absyn.CREF_IDENT(name, nil))
                      (cache, env, ih, sets, dae1, graph) = instConnect(cache, env, ih, sets, pre, c1_full, c2_full, impl, graph, info)
                      (cache, env, ih, sets, dae2, graph) = connectExpandableVariables(cache, env, ih, sets, pre, c1, c2, names, impl, graph, info)
                      dae = DAEUtil.joinDaes(dae1, dae2)
                    (cache, env, ih, sets, dae, graph)
                  end
                end
              end
               #=  handle recursive call
               =#
               #=  add name to both c1 and c2, then connect normally
               =#
               #=  fprintln(Flags.SHOW_EXPANDABLE_INFO, \"connect(full_expandable, full_expandable)(\" + Dump.printComponentRefStr(c1_full) + \", \" + Dump.printComponentRefStr(c2_full) + \")\");
               =#
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

         #= @author: adrpo
          this function gets the ClassInf.SMNode from the given type.
          it will fail if the type is not a complex type. =#
        function getStateFromType(ty::DAE.Type) ::ClassInf.SMNode
              local outState::ClassInf.SMNode

              outState = begin
                  local state::ClassInf.SMNode
                @match ty begin
                  DAE.T_COMPLEX(complexClassType = state)  => begin
                    state
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = state)  => begin
                    state
                  end

                  _  => begin
                      fail()
                  end
                end
              end
               #=  TODO! check if subtype is needed here
               =#
               #=  adpo: TODO! FIXME! add a debug print here!
               =#
          outState
        end

         #= @author: adrpo
          this function checks if the given type is an expandable connector =#
        function isConnectorType(ty::DAE.Type) ::Bool
              local isConnector::Bool

              isConnector = begin
                @match ty begin
                  DAE.T_COMPLEX(complexClassType = ClassInf.CONNECTOR(_, false))  => begin
                    true
                  end

                  DAE.T_SUBTYPE_BASIC(complexClassType = ClassInf.CONNECTOR(_, false))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  TODO! check if subtype is needed here
               =#
          isConnector
        end

         #= @author: adrpo
          this function will flip direction:
          input  -> output
          output -> input
          bidir  -> bidir =#
        function flipDirection(inDir::Absyn.Direction) ::Absyn.Direction
              local outDir::Absyn.Direction

              outDir = begin
                @match inDir begin
                  Absyn.INPUT(__)  => begin
                    Absyn.OUTPUT()
                  end

                  Absyn.OUTPUT(__)  => begin
                    Absyn.INPUT()
                  end

                  Absyn.BIDIR(__)  => begin
                    Absyn.BIDIR()
                  end
                end
              end
          outDir
        end

         #= This function tests whether a type is a eligible to be used in connections. =#
        function validConnector(inType::DAE.Type, inCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local state::ClassInf.SMNode
                  local tp::DAE.Type
                  local str::String
                @matchcontinue (inType, inCref, inInfo) begin
                  (DAE.T_REAL(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_INTEGER(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_STRING(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_BOOL(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_ENUMERATION(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_CLOCK(__), _, _)  => begin
                    ()
                  end

                  (DAE.T_COMPLEX(complexClassType = state), _, _)  => begin
                      ClassInf.valid(state, SCode.R_CONNECTOR(false))
                    ()
                  end

                  (DAE.T_COMPLEX(complexClassType = state), _, _)  => begin
                      ClassInf.valid(state, SCode.R_CONNECTOR(true))
                    ()
                  end

                  (DAE.T_SUBTYPE_BASIC(complexClassType = state), _, _)  => begin
                      ClassInf.valid(state, SCode.R_CONNECTOR(false))
                    ()
                  end

                  (DAE.T_SUBTYPE_BASIC(complexClassType = state), _, _)  => begin
                      ClassInf.valid(state, SCode.R_CONNECTOR(true))
                    ()
                  end

                  (DAE.T_ARRAY(ty = tp), _, _)  => begin
                      validConnector(tp, inCref, inInfo)
                    ()
                  end

                  (_, _, _)  => begin
                      @match true = ConnectUtil.isExpandable(inCref)
                    ()
                  end

                  _  => begin
                        str = ComponentReference.printComponentRefStr(inCref)
                        Error.addSourceMessage(Error.INVALID_CONNECTOR_TYPE, list(str), inInfo)
                      fail()
                  end
                end
              end
               #=  clocks TODO! FIXME! check if +std=3.3
               =#
               #=  TODO, check if subtype is needed here
               =#
               #=  TODO, check if subtype is needed here
               =#
               #=  everything in expandable is a connector!
               =#
        end

        function checkConnectTypes(inLhsCref::DAE.ComponentRef, inLhsType::DAE.Type, inLhsFace::DAE.Face, inLhsAttributes::DAE.Attributes, inRhsCref::DAE.ComponentRef, inRhsType::DAE.Type, inRhsFace::DAE.Face, inRhsAttributes::DAE.Attributes, inInfo::SourceInfo)
              local lhs_ct::DAE.ConnectorType
              local rhs_ct::DAE.ConnectorType
              local lhs_dir::Absyn.Direction
              local rhs_dir::Absyn.Direction
              local lhs_io::Absyn.InnerOuter
              local rhs_io::Absyn.InnerOuter
              local lhs_vis::SCode.Visibility
              local rhs_vis::SCode.Visibility

              ComponentReference.checkCrefSubscriptsBounds(inLhsCref, inInfo)
              ComponentReference.checkCrefSubscriptsBounds(inRhsCref, inInfo)
              @match DAE.ATTR(connectorType = lhs_ct, direction = lhs_dir, innerOuter = lhs_io, visibility = lhs_vis) = inLhsAttributes
              @match DAE.ATTR(connectorType = rhs_ct, direction = rhs_dir, innerOuter = rhs_io, visibility = rhs_vis) = inRhsAttributes
              checkConnectTypesType(inLhsType, inRhsType, inLhsCref, inRhsCref, inInfo)
              checkConnectTypesFlowStream(lhs_ct, rhs_ct, inLhsCref, inRhsCref, inInfo)
              checkConnectTypesDirection(lhs_dir, inLhsFace, lhs_vis, rhs_dir, inRhsFace, rhs_vis, inLhsCref, inRhsCref, inInfo)
              checkConnectTypesInnerOuter(lhs_io, rhs_io, inLhsCref, inRhsCref, inInfo)
        end

        function checkConnectTypesType(inLhsType::DAE.Type, inRhsType::DAE.Type, inLhsCref::DAE.ComponentRef, inRhsCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local cs1::String
                  local cs2::String
                  local cref_str1::String
                  local cref_str2::String
                  local str1::String
                  local str2::String
                  local dims1::List{DAE.Dimension}
                  local dims2::List{DAE.Dimension}
                @matchcontinue (inLhsType, inRhsType, inLhsCref, inRhsCref, inInfo) begin
                  (_, _, _, _, _)  => begin
                      @match true = Types.equivtypesOrRecordSubtypeOf(inLhsType, inRhsType)
                    ()
                  end

                  (_, _, _, _, _)  => begin
                      t1 = Types.arrayElementType(inLhsType)
                      t2 = Types.arrayElementType(inRhsType)
                      @match false = Types.equivtypesOrRecordSubtypeOf(t1, t2)
                      (_, cs1) = Types.printConnectorTypeStr(t1)
                      (_, cs2) = Types.printConnectorTypeStr(t2)
                      cref_str1 = ComponentReference.printComponentRefStr(inLhsCref)
                      cref_str2 = ComponentReference.printComponentRefStr(inRhsCref)
                      Error.addSourceMessage(Error.CONNECT_INCOMPATIBLE_TYPES, list(cref_str1, cref_str2, cref_str1, cs1, cref_str2, cs2), inInfo)
                    fail()
                  end

                  (_, _, _, _, _)  => begin
                      dims1 = Types.getDimensions(inLhsType)
                      dims2 = Types.getDimensions(inRhsType)
                      @match false = ListUtil.isEqualOnTrue(dims1, dims2, Expression.dimensionsEqual)
                      @match false = listEmpty(dims1) && listEmpty(dims2)
                      cref_str1 = ComponentReference.printComponentRefStr(inLhsCref)
                      cref_str2 = ComponentReference.printComponentRefStr(inRhsCref)
                      str1 = "[" + ExpressionDump.dimensionsString(dims1) + "]"
                      str2 = "[" + ExpressionDump.dimensionsString(dims2) + "]"
                      Error.addSourceMessage(Error.CONNECTOR_ARRAY_DIFFERENT, list(cref_str1, cref_str2, str1, str2), inInfo)
                    fail()
                  end
                end
              end
               #=  The type is not identical hence error.
               =#
               #=  Different dimensionality.
               =#
        end

        function checkConnectTypesFlowStream(inLhsConnectorType::DAE.ConnectorType, inRhsConnectorType::DAE.ConnectorType, inLhsCref::DAE.ComponentRef, inRhsCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local cref_str1::String
                  local cref_str2::String
                  local pre_str1::String
                  local pre_str2::String
                  local err_strl::List{String}
                @matchcontinue (inLhsConnectorType, inRhsConnectorType, inLhsCref, inRhsCref, inInfo) begin
                  (_, _, _, _, _)  => begin
                      @match true = DAEUtil.connectorTypeEqual(inLhsConnectorType, inRhsConnectorType)
                    ()
                  end

                  _  => begin
                        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref)
                        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref)
                        pre_str1 = DAEUtil.connectorTypeStr(inLhsConnectorType)
                        pre_str2 = DAEUtil.connectorTypeStr(inRhsConnectorType)
                        err_strl = if DAEUtil.potentialBool(inLhsConnectorType)
                              list(pre_str2, cref_str2, cref_str1)
                            else
                              list(pre_str1, cref_str1, cref_str2)
                            end
                        Error.addSourceMessage(Error.CONNECT_PREFIX_MISMATCH, err_strl, inInfo)
                      fail()
                  end
                end
              end
        end

        function checkConnectTypesDirection(inLhsDirection::Absyn.Direction, inLhsFace::DAE.Face, inLhsVisibility::SCode.Visibility, inRhsDirection::Absyn.Direction, inRhsFace::DAE.Face, inRhsVisibility::SCode.Visibility, inLhsCref::DAE.ComponentRef, inRhsCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local cref_str1::String
                  local cref_str2::String
                   #=  Two connectors with the same directions but different faces or different
                   =#
                   #=  directions may be connected.
                   =#
                @matchcontinue (inLhsDirection, inLhsFace, inLhsVisibility, inRhsDirection, inRhsFace, inRhsVisibility, inLhsCref, inRhsCref, inInfo) begin
                  (_, _, _, _, _, _, _, _, _)  => begin
                      @match false = isSignalSource(inLhsDirection, inLhsFace, inLhsVisibility) && isSignalSource(inRhsDirection, inRhsFace, inRhsVisibility)
                    ()
                  end

                  _  => begin
                        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref)
                        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref)
                        Error.addSourceMessage(Error.CONNECT_TWO_SOURCES, list(cref_str1, cref_str2), inInfo)
                      ()
                  end
                end
              end
        end

        function isSignalSource(inDirection::Absyn.Direction, inFace::DAE.Face, inVisibility::SCode.Visibility) ::Bool
              local outIsSignal::Bool

              outIsSignal = begin
                @match (inDirection, inFace, inVisibility) begin
                  (Absyn.OUTPUT(__), DAE.INSIDE(__), _)  => begin
                    true
                  end

                  (Absyn.INPUT(__), DAE.OUTSIDE(__), SCode.PUBLIC(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          outIsSignal
        end

        function checkConnectTypesInnerOuter(inLhsIO::Absyn.InnerOuter, inRhsIO::Absyn.InnerOuter, inLhsCref::DAE.ComponentRef, inRhsCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local cref_str1::String
                  local cref_str2::String
                @match (inLhsIO, inRhsIO, inLhsCref, inRhsCref, inInfo) begin
                  (Absyn.OUTER(__), Absyn.OUTER(__), _, _, _)  => begin
                      cref_str1 = ComponentReference.printComponentRefStr(inLhsCref)
                      cref_str2 = ComponentReference.printComponentRefStr(inRhsCref)
                      Error.addSourceMessage(Error.CONNECT_OUTER_OUTER, list(cref_str1, cref_str2), inInfo)
                    fail()
                  end

                  _  => begin
                      ()
                  end
                end
              end
        end

         #=
          This function connects two components and generates connection
          sets along the way.  For simple components (of type Real) it
          adds the components to the set, and for complex types it traverses
          the subcomponents and recursively connects them to each other.
          A DAE.Element list is returned for assert statements. =#
        function connectComponents(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix3::Prefix.PrefixType, cr1::DAE.ComponentRef, inFace5::DAE.Face, inType6::DAE.Type, vt1::SCode.Variability, cr2::DAE.ComponentRef, inFace8::DAE.Face, inType9::DAE.Type, vt2::SCode.Variability, inConnectorType::DAE.ConnectorType, io1::Absyn.InnerOuter, io2::Absyn.InnerOuter, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local c1_1::DAE.ComponentRef
                  local c2_1::DAE.ComponentRef
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local c1p::DAE.ComponentRef
                  local c2p::DAE.ComponentRef
                  local sets_1::DAE.Sets
                  local sets::DAE.Sets
                  local env::FCore.Graph
                  local pre::Prefix.PrefixType
                  local f1::DAE.Face
                  local f2::DAE.Face
                  local t1::DAE.Type
                  local t2::DAE.Type
                  local bc_tp1::DAE.Type
                  local bc_tp2::DAE.Type
                  local equalityConstraintFunctionReturnType::DAE.Type
                  local dim1::DAE.Dimension
                  local dim2::DAE.Dimension
                  local dae::DAE.DAElist
                  local l1::List{DAE.Var}
                  local l2::List{DAE.Var}
                  local ct::DAE.ConnectorType
                  local c1_str::String
                  local t1_str::String
                  local t2_str::String
                  local c2_str::String
                  local cache::FCore.Cache
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                  local source::DAE.ElementSource #= the origin of the element =#
                  local inlineType1::DAE.InlineType
                  local inlineType2::DAE.InlineType
                  local fpath1::Absyn.Path
                  local fpath2::Absyn.Path
                  local idim1::ModelicaInteger
                  local idim2::ModelicaInteger
                  local dim_int::ModelicaInteger
                  local zeroVector::DAE.Exp
                  local crefExp1::DAE.Exp
                  local crefExp2::DAE.Exp
                  local exp::DAE.Exp
                  local breakDAEElements::List{DAE.Element}
                  local elts::List{DAE.Element}
                  local equalityConstraintFunction::SCode.Element
                  local dims::DAE.Dimensions
                  local dims2::DAE.Dimensions
                  local crefs1::List{DAE.ComponentRef}
                  local crefs2::List{DAE.ComponentRef}
                  local const1::DAE.Const
                  local const2::DAE.Const
                  local lhsl::List{DAE.Exp}
                  local rhsl::List{DAE.Exp}
                   #=  connections to outer components
                   =#
                @matchcontinue (inCache, inEnv, inIH, inSets, inPrefix3, cr1, inFace5, inType6, vt1, cr2, inFace8, inType9, vt2, inConnectorType, io1, io2, inGraph, info) begin
                  (cache, env, ih, sets, pre, c1, f1, _, _, c2, f2, _, _, ct, _, _, graph, _)  => begin
                      @match false = DAEUtil.streamBool(ct)
                      @match true = InnerOuter.outerConnection(io1, io2)
                      @match (cache, DAE.CREF(c1_1, _)) = PrefixUtil.prefixExp(cache, env, ih, Expression.crefExp(c1), pre)
                      @match (cache, DAE.CREF(c2_1, _)) = PrefixUtil.prefixExp(cache, env, ih, Expression.crefExp(c2), pre)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      sets = ConnectUtil.addOuterConnection(pre, sets, c1_1, c2_1, io1, io2, f1, f2, source)
                    (cache, env, ih, sets, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, _, t1, _, c2, _, t2, _, DAE.POTENTIAL(__), _, _, graph, _)  => begin
                      @match true = SCodeUtil.isParameterOrConst(vt1) && SCodeUtil.isParameterOrConst(vt2)
                      @match true = Types.basicType(Types.arrayElementType(t1))
                      @match true = Types.basicType(Types.arrayElementType(t2))
                      (cache, c1_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      crefExp1 = Expression.crefExp(c1_1)
                      crefExp2 = Expression.crefExp(c2_1)
                      const1 = NFInstUtil.toConst(vt1)
                      const2 = NFInstUtil.toConst(vt2)
                      (cache, crefExp1) = Ceval.cevalIfConstant(cache, env, crefExp1, DAE.PROP(t1, const1), true, info)
                      (cache, crefExp2) = Ceval.cevalIfConstant(cache, env, crefExp2, DAE.PROP(t2, const2), true, info)
                      lhsl = Expression.arrayElements(crefExp1)
                      rhsl = Expression.arrayElements(crefExp2)
                      elts = ListUtil.threadMap1(lhsl, rhsl, generateConnectAssert, source)
                    (cache, env, ih, sets, DAE.DAE(elts), graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, t1, _, c2, f2, t2, _, _, _, _, graph, _)  => begin
                      @match true = Types.basicType(t1)
                      @match true = Types.basicType(t2)
                      (cache, c1_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      sets_1 = ConnectUtil.addConnection(sets, c1, f1, c2, f2, inConnectorType, source)
                    (cache, env, ih, sets_1, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_ARRAY(dims = dim1 <|  nil(), ty = t1), _, c2, f2, DAE.T_ARRAY(dims = dim2 <|  nil(), ty = t2), _, ct && DAE.POTENTIAL(__), _, _, graph, _)  => begin
                      @match DAE.T_COMPLEX() = Types.arrayElementType(t1)
                      @match DAE.T_COMPLEX() = Types.arrayElementType(t2)
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      _ = Expression.dimensionSize(dim1)
                      crefs1 = ComponentReference.expandCref(c1, false)
                      crefs2 = ComponentReference.expandCref(c2, false)
                      (cache, _, ih, sets_1, dae, graph) = connectArrayComponents(cache, env, ih, sets, pre, crefs1, f1, t1, vt1, io1, crefs2, f2, t2, vt2, io2, ct, graph, info)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_ARRAY(dims = dim1 <|  nil(), ty = t1), _, c2, f2, DAE.T_ARRAY(dims = dim2 <|  nil(), ty = t2), _, ct && DAE.POTENTIAL(__), _, _, graph, _)  => begin
                      @match DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_)) = Types.arrayElementType(t1)
                      @match DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_)) = Types.arrayElementType(t2)
                      @match true = Expression.dimensionsKnownAndEqual(dim1, dim2)
                      _ = Expression.dimensionSize(dim1)
                      crefs1 = ComponentReference.expandCref(c1, false)
                      crefs2 = ComponentReference.expandCref(c2, false)
                      (cache, _, ih, sets_1, dae, graph) = connectArrayComponents(cache, env, ih, sets, pre, crefs1, f1, t1, vt1, io1, crefs2, f2, t2, vt2, io2, ct, graph, info)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, t1 && DAE.T_ARRAY(__), _, c2, f2, t2 && DAE.T_ARRAY(__), _, ct, _, _, graph, _)  => begin
                      dims = Types.getDimensions(t1)
                      dims2 = Types.getDimensions(t2)
                      @match true = ListUtil.isEqualOnTrue(dims, dims2, Expression.dimensionsKnownAndEqual)
                      (cache, c1p) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2p) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1p, c2p))
                      sets_1 = ConnectUtil.addArrayConnection(sets, c1, f1, c2, f2, source, ct)
                    (cache, env, ih, sets_1, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, t1 && DAE.T_COMPLEX(equalityConstraint = SOME((fpath1, idim1, inlineType1))), _, c2, f2, t2 && DAE.T_COMPLEX(equalityConstraint = SOME((_, _, _))), _, ct && DAE.POTENTIAL(__), _, _, graph && ConnectionGraph.GRAPH(updateGraph = true), _)  => begin
                      (cache, c1_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      (cache, env, ih, sets_1, dae, _) = connectComponents(cache, env, ih, sets, pre, c1, f1, t1, vt1, c2, f2, t2, vt2, ct, io1, io2, ConnectionGraph.NOUPDATE_EMPTY, info)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      zeroVector = Expression.makeRealArrayOfZeros(idim1)
                      crefExp1 = Expression.crefExp(c1_1)
                      crefExp2 = Expression.crefExp(c2_1)
                      equalityConstraintFunctionReturnType = DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_INTEGER(idim1)))
                      source = ElementSource.addAdditionalComment(source, " equation generated by overconstrained connection graph breaking")
                      breakDAEElements = list(DAE.ARRAY_EQUATION(list(DAE.DIM_INTEGER(idim1)), zeroVector, DAE.CALL(fpath1, list(crefExp1, crefExp2), DAE.CALL_ATTR(equalityConstraintFunctionReturnType, false, false, false, false, inlineType1, DAE.NO_TAIL())), source))
                      graph = ConnectionGraph.addConnection(graph, c1_1, c2_1, breakDAEElements)
                      (cache, equalityConstraintFunction, env) = Lookup.lookupClass(cache, env, fpath1)
                      (cache, fpath1) = Inst.makeFullyQualified(cache, env, fpath1)
                      cache = FCore.addCachedInstFuncGuard(cache, fpath1)
                      (cache, env, ih) = InstFunction.implicitFunctionInstantiation(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), equalityConstraintFunction, nil)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_SUBTYPE_BASIC(complexType = t1, equalityConstraint = SOME((fpath1, idim1, inlineType1))), _, c2, f2, DAE.T_SUBTYPE_BASIC(complexType = t2, equalityConstraint = SOME((_, _, _))), _, ct && DAE.POTENTIAL(__), _, _, graph && ConnectionGraph.GRAPH(updateGraph = true), _)  => begin
                      (cache, c1_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      (cache, env, ih, sets_1, dae, _) = connectComponents(cache, env, ih, sets, pre, c1, f1, t1, vt1, c2, f2, t2, vt2, ct, io1, io2, ConnectionGraph.NOUPDATE_EMPTY, info)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      zeroVector = Expression.makeRealArrayOfZeros(idim1)
                      crefExp1 = Expression.crefExp(c1_1)
                      crefExp2 = Expression.crefExp(c2_1)
                      equalityConstraintFunctionReturnType = DAE.T_ARRAY(DAE.T_REAL_DEFAULT, list(DAE.DIM_INTEGER(idim1)))
                      source = ElementSource.addAdditionalComment(source, " equation generated by overconstrained connection graph breaking")
                      breakDAEElements = list(DAE.ARRAY_EQUATION(list(DAE.DIM_INTEGER(idim1)), zeroVector, DAE.CALL(fpath1, list(crefExp1, crefExp2), DAE.CALL_ATTR(equalityConstraintFunctionReturnType, false, false, false, false, inlineType1, DAE.NO_TAIL())), source))
                      graph = ConnectionGraph.addConnection(graph, ComponentReference.crefStripLastSubs(c1_1), ComponentReference.crefStripLastSubs(c2_1), breakDAEElements)
                      (cache, equalityConstraintFunction, env) = Lookup.lookupClass(cache, env, fpath1)
                      (cache, fpath1) = Inst.makeFullyQualified(cache, env, fpath1)
                      cache = FCore.addCachedInstFuncGuard(cache, fpath1)
                      (cache, env, ih) = InstFunction.implicitFunctionInstantiation(cache, env, ih, DAE.NOMOD(), Prefix.NOPRE(), equalityConstraintFunction, nil)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_SUBTYPE_BASIC(complexType = bc_tp1), _, c2, f2, t2, _, ct, _, _, graph, _)  => begin
                      (cache, _, ih, sets_1, dae, graph) = connectComponents(cache, env, ih, sets, pre, c1, f1, bc_tp1, vt1, c2, f2, t2, vt2, ct, io1, io2, graph, info)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, t1, _, c2, f2, DAE.T_SUBTYPE_BASIC(complexType = bc_tp2), _, ct, _, _, graph, _)  => begin
                      (cache, _, ih, sets_1, dae, graph) = connectComponents(cache, env, ih, sets, pre, c1, f1, t1, vt1, c2, f2, bc_tp2, vt2, ct, io1, io2, graph, info)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(__), varLst =  nil()), _, c2, f2, DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(__), varLst =  nil()), _, _, _, _, graph, _)  => begin
                      (cache, c1_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, c2_1) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      source = ElementSource.createElementSource(info, FGraph.getScopePath(env), pre, (c1_1, c2_1))
                      sets_1 = ConnectUtil.addConnection(sets, c1, f1, c2, f2, inConnectorType, source)
                    (cache, env, ih, sets_1, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, pre, c1, f1, DAE.T_COMPLEX(varLst = l1), _, c2, f2, DAE.T_COMPLEX(varLst = l2), _, ct, _, _, graph, _)  => begin
                      (cache, _, ih, sets_1, dae, graph) = connectVars(cache, env, ih, sets, pre, c1, f1, l1, vt1, c2, f2, l2, vt2, ct, io1, io2, graph, info)
                    (cache, env, ih, sets_1, dae, graph)
                  end

                  (cache, env, ih, _, pre, c1, _, t1, _, c2, _, t2, _, _, _, _, _, _)  => begin
                      (cache, _) = PrefixUtil.prefixCref(cache, env, ih, pre, c1)
                      (cache, _) = PrefixUtil.prefixCref(cache, env, ih, pre, c2)
                      c1_str = ComponentReference.printComponentRefStr(c1)
                      t1_str = Types.unparseType(t1)
                      c2_str = ComponentReference.printComponentRefStr(c2)
                      t2_str = Types.unparseType(t2)
                      c1_str = stringAppendList(list("\\n", c1_str, " type:\\n", t1_str))
                      c2_str = stringAppendList(list("\\n", c2_str, " type:\\n", t2_str))
                      Error.addSourceMessage(Error.INVALID_CONNECTOR_VARIABLE, list(c1_str, c2_str), info)
                    fail()
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- InstSection.connectComponents failed\\n")
                      fail()
                  end
                end
              end
               #=  print(\"Connecting components: \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \"/\" +
               =#
               #=     ComponentReference.printComponentRefStr(c1) + \"[\" + Dump.unparseInnerouterStr(io1) + \"]\" + \" = \" +
               =#
               #=     ComponentReference.printComponentRefStr(c2) + \"[\" + Dump.unparseInnerouterStr(io2) + \"]\\n\");
               =#
               #=  prefix outer with the prefix of the inner directly!
               =#
               #=  set the source of this element
               =#
               #=  print(\"CONNECT: \" + PrefixUtil.printPrefixStrIgnoreNoPre(pre) + \"/\" +
               =#
               #=     ComponentReference.printComponentRefStr(c1_1) + \"[\" + Dump.unparseInnerouterStr(io1) + \"]\" + \" = \" +
               =#
               #=     ComponentReference.printComponentRefStr(c2_1) + \"[\" + Dump.unparseInnerouterStr(io2) + \"]\\n\");
               =#
               #=  Non-flow and Non-stream type Parameters and constants generate assert statements
               =#
               #=  set the source of this element
               =#
               #=  Evaluate constant crefs away
               =#
               #=  Connection of two components of basic type.
               =#
               #=  TODO: FIXME!
               =#
               #=  adrpo 2012-10-14: should we not prefix here??!!
               =#
               #=  set the source of this element
               =#
               #= /* - weird, seems not to be needed
                   Connection of arrays of size zero!
                  case (cache,env,ih,sets,pre,
                      c1,f1,t1 as DAE.T_ARRAY(dims = {dim1}, ty = _),_,
                      c2,f2,t2 as DAE.T_ARRAY(dims = {dim2}, ty = _),_,
                      ct,_,_,graph,_)
                    equation
                      0 = Expression.dimensionSize(dim1);
                      0 = Expression.dimensionSize(dim2);
                      (cache,_) = PrefixUtil.prefixCref(cache,env,ih,pre,c1);
                      (cache,_) = PrefixUtil.prefixCref(cache,env,ih,pre,c2);
                      c1_str = Types.connectorTypeStr(ct) + ComponentReference.printComponentRefStr(c1);
                      (t1, _) = Types.stripTypeVars(t1);
                      t1_str = Types.unparseType(t1);
                      c2_str = Types.connectorTypeStr(ct) + ComponentReference.printComponentRefStr(c2);
                      (t2, _) = Types.stripTypeVars(t2);
                      t2_str = Types.unparseType(t2);
                      c1_str = stringAppendList({c1_str,\" type: \",t1_str});
                      c2_str = stringAppendList({c2_str,\" type: \",t2_str});
                      Error.addSourceMessage(Error.CONNECT_ARRAY_SIZE_ZERO, {c1_str,c2_str},info);
                    then
                      (cache,env,ih,sets,DAE.emptyDae,graph);*/ =#
               #=  Connection of arrays of complex types
               =#
               #=  Connection of arrays of subtype basic types with equality constraint
               =#
               #=  Connection of arrays
               =#
               #=  set the source of this element
               =#
               #=  Connection of connectors with an equality constraint.
               =#
               #=  Connect components ignoring equality constraints
               =#
               #=  set the source of this element
               =#
               #=  Add an edge to connection graph. The edge contains the
               =#
               #=  dae to be added in the case where the edge is broken.
               =#
               #=  use the inline type
               =#
               #=  set the origin of the element
               =#
               #=  deal with equalityConstraint function!
               =#
               #=  instantiate and add the equalityConstraint function to the dae function tree!
               =#
               #=  Connection of connectors with an equality constraint extending BASIC TYPES
               =#
               #=  Connect components ignoring equality constraints
               =#
               #=  set the source of this element
               =#
               #=  Add an edge to connection graph. The edge contains the
               =#
               #=  dae to be added in the case where the edge is broken.
               =#
               #=  use the inline type
               =#
               #=  set the origin of the element
               =#
               #=  deal with equalityConstraint function!
               =#
               #=  instantiate and add the equalityConstraint function to the dae function tree!
               =#
               #=  Complex types t1 extending basetype
               =#
               #=  Complex types t2 extending basetype
               =#
               #=  Connection of ExternalObject!
               =#
               #=  set the source of this element
               =#
               #=  Connection of complex connector, e.g. Pin
               =#
               #=  Error
               =#
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

        function generateConnectAssert(inLhsExp::DAE.Exp, inRhsExp::DAE.Exp, inSource::DAE.ElementSource) ::DAE.Element
              local outAssert::DAE.Element

              local exp::DAE.Exp

              exp = DAE.RELATION(inLhsExp, DAE.EQUAL(DAE.T_BOOL_DEFAULT), inRhsExp, -1, NONE())
              (exp, _) = ExpressionSimplify.simplify(exp)
              outAssert = DAE.ASSERT(exp, DAE.SCONST("automatically generated from connect"), DAE.ASSERTIONLEVEL_ERROR, inSource)
          outAssert
        end

        function connectArrayComponents(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix::Prefix.PrefixType, inLhsCrefs::List{<:DAE.ComponentRef}, inLhsFace::DAE.Face, inLhsType::DAE.Type, inLhsVar::SCode.Variability, inLhsIO::Absyn.InnerOuter, inRhsCrefs::List{<:DAE.ComponentRef}, inRhsFace::DAE.Face, inRhsType::DAE.Type, inRhsVar::SCode.Variability, inRhsIO::Absyn.InnerOuter, inConnectorType::DAE.ConnectorType, inGraph::ConnectionGraph.ConnectionGraphType, inInfo::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local lhs::DAE.ComponentRef
                  local rhs::DAE.ComponentRef
                  local rest_lhs::List{DAE.ComponentRef}
                  local rest_rhs::List{DAE.ComponentRef}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ih::InstanceHierarchy
                  local sets::DAE.Sets
                  local dae1::DAE.DAElist
                  local dae2::DAE.DAElist
                  local graph::ConnectionGraph.ConnectionGraphType
                @match (inCache, inEnv, inIH, inSets, inPrefix, inLhsCrefs, inLhsFace, inLhsType, inLhsVar, inLhsIO, inRhsCrefs, inRhsFace, inRhsType, inRhsVar, inRhsIO, inConnectorType, inGraph, inInfo) begin
                  (_, _, _, _, _, lhs <| rest_lhs, _, _, _, _, rhs <| rest_rhs, _, _, _, _, _, _, _)  => begin
                      (cache, env, ih, sets, dae1, graph) = connectComponents(inCache, inEnv, inIH, inSets, inPrefix, lhs, inLhsFace, inLhsType, inLhsVar, rhs, inRhsFace, inRhsType, inRhsVar, inConnectorType, inLhsIO, inRhsIO, inGraph, inInfo)
                      (cache, env, ih, sets, dae2, graph) = connectArrayComponents(cache, env, ih, sets, inPrefix, rest_lhs, inLhsFace, inLhsType, inLhsVar, inLhsIO, rest_rhs, inRhsFace, inRhsType, inRhsVar, inRhsIO, inConnectorType, graph, inInfo)
                      dae1 = DAEUtil.joinDaes(dae1, dae2)
                    (cache, env, ih, sets, dae1, graph)
                  end

                  _  => begin
                      (inCache, inEnv, inIH, inSets, DAE.emptyDae, inGraph)
                  end
                end
              end
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

         #= This function connects two subcomponents by adding the component
          name to the current path and recursively connecting the components
          using the function connectComponents. =#
        function connectVars(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inSets::DAE.Sets, inPrefix::Prefix.PrefixType, inComponentRef3::DAE.ComponentRef, inFace4::DAE.Face, inTypesVarLst5::List{<:DAE.Var}, vt1::SCode.Variability, inComponentRef6::DAE.ComponentRef, inFace7::DAE.Face, inTypesVarLst8::List{<:DAE.Var}, vt2::SCode.Variability, inConnectorType::DAE.ConnectorType, io1::Absyn.InnerOuter, io2::Absyn.InnerOuter, inGraph::ConnectionGraph.ConnectionGraphType, info::SourceInfo) ::Tuple{FCore.Cache, FCore.Graph, InnerOuter.InstHierarchy, DAE.Sets, DAE.DAElist, ConnectionGraph.ConnectionGraphType}
              local outGraph::ConnectionGraph.ConnectionGraphType
              local outDae::DAE.DAElist
              local outSets::DAE.Sets
              local outIH::InnerOuter.InstHierarchy
              local outEnv::FCore.Graph
              local outCache::FCore.Cache

              (outCache, outEnv, outIH, outSets, outDae, outGraph) = begin
                  local sets::DAE.Sets
                  local sets_1::DAE.Sets
                  local sets_2::DAE.Sets
                  local env::FCore.Graph
                  local c1_1::DAE.ComponentRef
                  local c2_1::DAE.ComponentRef
                  local c1::DAE.ComponentRef
                  local c2::DAE.ComponentRef
                  local dae::DAE.DAElist
                  local dae2::DAE.DAElist
                  local dae_1::DAE.DAElist
                  local f1::DAE.Face
                  local f2::DAE.Face
                  local n::String
                  local attr1::DAE.Attributes
                  local attr2::DAE.Attributes
                  local ct::DAE.ConnectorType
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local xs1::List{DAE.Var}
                  local xs2::List{DAE.Var}
                  local vta::SCode.Variability
                  local vtb::SCode.Variability
                  local ty_2::DAE.Type
                  local cache::FCore.Cache
                  local graph::ConnectionGraph.ConnectionGraphType
                  local ih::InstanceHierarchy
                @match (inCache, inEnv, inIH, inSets, inPrefix, inComponentRef3, inFace4, inTypesVarLst5, vt1, inComponentRef6, inFace7, inTypesVarLst8, vt2, inConnectorType, io1, io2, inGraph, info) begin
                  (cache, env, ih, sets, _, _, _,  nil(), _, _, _,  nil(), _, _, _, _, graph, _)  => begin
                    (cache, env, ih, sets, DAE.emptyDae, graph)
                  end

                  (cache, env, ih, sets, _, c1, f1, DAE.TYPES_VAR(name = n, attributes = attr1 && DAE.ATTR(connectorType = ct, variability = vta), ty = ty1) <| xs1, _, c2, f2, DAE.TYPES_VAR(attributes = attr2 && DAE.ATTR(variability = vtb), ty = ty2) <| xs2, _, _, _, _, graph, _)  => begin
                      ty_2 = Types.simplifyType(ty1)
                      ct = propagateConnectorType(inConnectorType, ct)
                      c1_1 = ComponentReference.crefPrependIdent(c1, n, nil, ty_2)
                      c2_1 = ComponentReference.crefPrependIdent(c2, n, nil, ty_2)
                      checkConnectTypes(c1_1, ty1, f1, attr1, c2_1, ty2, f2, attr2, info)
                      (cache, _, ih, sets_1, dae, graph) = connectComponents(cache, env, ih, sets, inPrefix, c1_1, f1, ty1, vta, c2_1, f2, ty2, vtb, ct, io1, io2, graph, info)
                      (cache, _, ih, sets_2, dae2, graph) = connectVars(cache, env, ih, sets_1, inPrefix, c1, f1, xs1, vt1, c2, f2, xs2, vt2, inConnectorType, io1, io2, graph, info)
                      dae_1 = DAEUtil.joinDaes(dae, dae2)
                    (cache, env, ih, sets_2, dae_1, graph)
                  end
                end
              end
          (outCache, outEnv, outIH, outSets, outDae, outGraph)
        end

        function propagateConnectorType(inConnectorType::DAE.ConnectorType, inSubConnectorType::DAE.ConnectorType) ::DAE.ConnectorType
              local outSubConnectorType::DAE.ConnectorType

              outSubConnectorType = begin
                @match (inConnectorType, inSubConnectorType) begin
                  (DAE.POTENTIAL(__), _)  => begin
                    inSubConnectorType
                  end

                  _  => begin
                      inConnectorType
                  end
                end
              end
          outSubConnectorType
        end

         #= Expands an array into elements given a dimension, i.e.
            (3, x) => {x[1], x[2], x[3]} =#
        function expandArrayDimension(inDim::DAE.Dimension, inArray::DAE.Exp) ::List{DAE.Exp}
              local outExpl::List{DAE.Exp}

              outExpl = begin
                  local expl::List{DAE.Exp}
                  local sz::ModelicaInteger
                  local ints::List{ModelicaInteger}
                  local name::Absyn.Path
                  local ls::List{String}
                @matchcontinue (inDim, inArray) begin
                  (_, DAE.ARRAY(array = outExpl))  => begin
                    outExpl
                  end

                  (DAE.DIM_INTEGER(integer = 0), _)  => begin
                    nil
                  end

                  (DAE.DIM_INTEGER(integer = sz), _)  => begin
                      ints = ListUtil.intRange(sz)
                      expl = ListUtil.map1(ints, makeAsubIndex, inArray)
                    expl
                  end

                  (DAE.DIM_BOOLEAN(__), _)  => begin
                      expl = list(ExpressionSimplify.simplify1(Expression.makeASUB(inArray, list(DAE.BCONST(false)))), ExpressionSimplify.simplify1(Expression.makeASUB(inArray, list(DAE.BCONST(true)))))
                    expl
                  end

                  (DAE.DIM_ENUM(enumTypeName = name, literals = ls), _)  => begin
                      expl = makeEnumLiteralIndices(name, ls, 1, inArray)
                    expl
                  end

                  (DAE.DIM_UNKNOWN(__), _)  => begin
                      @match true = Flags.getConfigBool(Flags.CHECK_MODEL)
                      ints = ListUtil.intRange(1)
                      expl = ListUtil.map1(ints, makeAsubIndex, inArray)
                    expl
                  end
                end
              end
               #=  Empty integer list. List.intRange is not defined for size < 1,
               =#
               #=  so we need to handle empty lists here.
               =#
               #= /* adrpo: these are completly wrong!
                            will result in equations 1 = 1!
                  case (DAE.DIM_EXP(exp = _), _) then {DAE.ICONST(1)};
                  case (DAE.DIM_UNKNOWN(), _) then {DAE.ICONST(1)};
                  */ =#
               #=  try to make an array index of 1 when we don't know the dimension
               =#
          outExpl
        end

         #= Creates an ASUB expression given an expression and an integer index. =#
        function makeAsubIndex(index::ModelicaInteger, expr::DAE.Exp) ::DAE.Exp
              local asub::DAE.Exp

              (asub, _) = ExpressionSimplify.simplify1(Expression.makeASUB(expr, list(DAE.ICONST(index))))
          asub
        end

         #= Creates a list of enumeration literal expressions from an enumeration. =#
        function makeEnumLiteralIndices(enumTypeName::Absyn.Path, enumLiterals::List{<:String}, enumIndex::ModelicaInteger, expr::DAE.Exp) ::List{DAE.Exp}
              local enumIndices::List{DAE.Exp}

              enumIndices = begin
                  local l::String
                  local ls::List{String}
                  local e::DAE.Exp
                  local expl::List{DAE.Exp}
                  local enum_type_name::Absyn.Path
                  local index::ModelicaInteger
                @match (enumTypeName, enumLiterals, enumIndex, expr) begin
                  (_,  nil(), _, _)  => begin
                    nil
                  end

                  (_, l <| ls, _, _)  => begin
                      enum_type_name = AbsynUtil.joinPaths(enumTypeName, Absyn.IDENT(l))
                      e = DAE.ENUM_LITERAL(enum_type_name, enumIndex)
                      (e, _) = ExpressionSimplify.simplify1(Expression.makeASUB(expr, list(e)))
                      e = if Expression.isCref(e)
                            Expression.unliftExp(e)
                          else
                            e
                          end
                      index = enumIndex + 1
                      expl = makeEnumLiteralIndices(enumTypeName, ls, index, expr)
                    _cons(e, expl)
                  end
                end
              end
          enumIndices
        end

         #= for a vectorized cref, return the originial cref without vector subscripts =#
        function getVectorizedCref(crefOrArray::DAE.Exp) ::DAE.Exp
              local cref::DAE.Exp

              cref = begin
                  local cr::DAE.ComponentRef
                  local t::DAE.Type
                  local crefExp::DAE.Exp
                @match crefOrArray begin
                  cref && DAE.CREF(_, _)  => begin
                    cref
                  end

                  DAE.ARRAY(_, _, DAE.CREF(cr, t) <| _)  => begin
                      cr = ComponentReference.crefStripLastSubs(cr)
                      crefExp = Expression.makeCrefExp(cr, t)
                    crefExp
                  end
                end
              end
          cref
        end

         #= @author: adrpo
         checks when equation for:
         - when alg in when alg is not allowed
         - reinit in when with initial condition is not allowed
           when (initial()) then
             reinit(x, y);
           end when;
         =#
        function checkWhenAlgorithm(inWhenAlgorithm::SCode.Statement)
              @match true = checkForReinitInWhenInitialAlg(inWhenAlgorithm)
              checkForNestedWhenInStatements(inWhenAlgorithm)
        end

         #= Fails if a when (initial()) alg contains
           reinit which is not allowed in Modelica. =#
        function checkForReinitInWhenInitialAlg(inWhenAlgorithm::SCode.Statement) ::Bool
              local outOK::Bool

              outOK = begin
                  local b1::Bool
                  local b2::Bool
                  local exp::Absyn.Exp
                  local info::SourceInfo
                  local algs::List{SCode.Statement}
                   #=  add an error
                   =#
                @matchcontinue inWhenAlgorithm begin
                  SCode.ALG_WHEN_A(branches = (exp, algs) <| _, info = info)  => begin
                      @match true = AbsynUtil.expContainsInitial(exp)
                      @match true = SCodeUtil.algorithmsContainReinit(algs)
                      Error.addSourceMessage(Error.REINIT_IN_WHEN_INITIAL, nil, info)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outOK
        end

         #= Fails if a when alg contains nested when
           alg, which are not allowed in Modelica.
           An error message is added when failing. =#
        function checkForNestedWhenInStatements(inWhenAlgorithm::SCode.Statement)
              local branches::List{Tuple{Absyn.Exp, List{SCode.Statement}}}
              local info::SourceInfo
              local body::List{SCode.Statement}

              @match SCode.ALG_WHEN_A(branches = branches, info = info) = inWhenAlgorithm
              for branch in branches
                (_, body) = branch
                if containsWhenStatements(body)
                  Error.addSourceMessageAndFail(Error.NESTED_WHEN, nil, info)
                end
              end
        end

         #= @author: adrpo
         checks when equation for:
         - when equation in when equation is not allowed
         - reinit in when with initial condition is not allowed
           when (initial()) then
             reinit(x, y);
           end when; =#
        function checkWhenEquation(inWhenEq::SCode.EEquation)
              @match true = checkForReinitInWhenInitialEq(inWhenEq)
              checkForNestedWhenInEquation(inWhenEq)
        end

         #= Fails if a when (initial()) equation contains
           reinit which is not allowed in Modelica. =#
        function checkForReinitInWhenInitialEq(inWhenEq::SCode.EEquation) ::Bool
              local outOK::Bool

              outOK = begin
                  local b1::Bool
                  local b2::Bool
                  local exp::Absyn.Exp
                  local info::SourceInfo
                  local el::List{SCode.EEquation}
                  local tpl_el::List{Tuple{Absyn.Exp, List{SCode.EEquation}}}
                   #=  Add an error for when initial() then reinit().
                   =#
                @matchcontinue inWhenEq begin
                  SCode.EQ_WHEN(condition = exp, eEquationLst = el, info = info)  => begin
                      @match true = AbsynUtil.expContainsInitial(exp)
                      @match true = SCodeUtil.equationsContainReinit(el)
                      Error.addSourceMessage(Error.REINIT_IN_WHEN_INITIAL, nil, info)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outOK
        end

         #= Fails if a when equation contains nested when
           equations, which are not allowed in Modelica.
           An error message is added when failing. =#
        function checkForNestedWhenInEquation(inWhenEq::SCode.EEquation)
              _ = begin
                  local info::SourceInfo
                  local eqs::List{SCode.EEquation}
                  local eqs_lst::List{List{SCode.EEquation}}
                  local tpl_el::List{Tuple{Absyn.Exp, List{SCode.EEquation}}}
                   #=  continue if when equations are not nested
                   =#
                @match inWhenEq begin
                  SCode.EQ_WHEN(eEquationLst = eqs, elseBranches = tpl_el)  => begin
                      checkForNestedWhenInEqList(eqs)
                      eqs_lst = ListUtil.map(tpl_el, Util.tuple22)
                      ListUtil.map_0(eqs_lst, checkForNestedWhenInEqList)
                    ()
                  end
                end
              end
        end

         #= Helper function to checkForNestedWhen. Searches for nested when equations in
          a list of equations. =#
        function checkForNestedWhenInEqList(inEqs::List{<:SCode.EEquation})
              ListUtil.map_0(inEqs, checkForNestedWhenInEq)
        end

         #= Helper function to checkForNestedWhen. Searches for nested when equations in
          an equation. =#
        function checkForNestedWhenInEq(inEq::SCode.EEquation)
              _ = begin
                  local eqs::List{SCode.EEquation}
                  local eqs_lst::List{List{SCode.EEquation}}
                  local cr1::Absyn.ComponentRef
                  local cr2::Absyn.ComponentRef
                  local info::SourceInfo
                  local cr1_str::String
                  local cr2_str::String
                @match inEq begin
                  SCode.EQ_WHEN(info = info)  => begin
                      Error.addSourceMessage(Error.NESTED_WHEN, nil, info)
                    fail()
                  end

                  SCode.EQ_IF(thenBranch = eqs_lst, elseBranch = eqs)  => begin
                      ListUtil.map_0(eqs_lst, checkForNestedWhenInEqList)
                      checkForNestedWhenInEqList(eqs)
                    ()
                  end

                  SCode.EQ_FOR(eEquationLst = eqs)  => begin
                      checkForNestedWhenInEqList(eqs)
                    ()
                  end

                  SCode.EQ_EQUALS(__)  => begin
                    ()
                  end

                  SCode.EQ_PDE(__)  => begin
                    ()
                  end

                  SCode.EQ_CONNECT(crefLeft = cr1, crefRight = cr2, info = info)  => begin
                      cr1_str = Dump.printComponentRefStr(cr1)
                      cr2_str = Dump.printComponentRefStr(cr2)
                      Error.addSourceMessage(Error.CONNECT_IN_WHEN, list(cr1_str, cr2_str), info)
                    fail()
                  end

                  SCode.EQ_ASSERT(__)  => begin
                    ()
                  end

                  SCode.EQ_TERMINATE(__)  => begin
                    ()
                  end

                  SCode.EQ_REINIT(__)  => begin
                    ()
                  end

                  SCode.EQ_NORETCALL(__)  => begin
                    ()
                  end

                  _  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- InstSection.checkForNestedWhenInEq failed.\\n")
                    fail()
                  end
                end
              end
               #=  connect is not allowed in when equations.
               =#
        end

        function instAssignment(inCache::FCore.Cache, inEnv::FCore.Graph, ih::InnerOuter.InstHierarchy, inPre::Prefix.PrefixType, alg::SCode.Statement, source::DAE.ElementSource, initial_::SCode.Initial, impl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, numError::ModelicaInteger) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local stmts::List{DAE.Statement} #= more statements due to loop unrolling =#
              local outCache::FCore.Cache

              (outCache, stmts) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local e_1::DAE.Exp
                  local eprop::DAE.Properties
                  local pre::Prefix.PrefixType
                  local var::Absyn.Exp
                  local value::Absyn.Exp
                  local info::SourceInfo
                  local str::String
                  local t::DAE.Type
                @matchcontinue (inCache, inEnv, ih, inPre, alg, source, initial_, impl, unrollForLoops, numError) begin
                  (cache, env, _, pre, SCode.ALG_ASSIGN(assignComponent = var, value = value, info = info), _, _, _, _, _)  => begin
                      (cache, e_1, eprop) = Static.elabExp(cache, env, value, impl, true, pre, info)
                      (cache, stmts) = instAssignment2(cache, env, ih, pre, var, value, e_1, eprop, info, ElementSource.addAnnotation(source, alg.comment), initial_, impl, unrollForLoops, numError)
                    (cache, stmts)
                  end

                  (cache, env, _, pre, SCode.ALG_ASSIGN(value = value, info = info), _, _, _, _, _)  => begin
                      @match true = numError == Error.getNumErrorMessages()
                      @shouldFail Static.elabExp(cache, env, value, impl, true, pre, info)
                      str = Dump.unparseAlgorithmStr(SCodeUtil.statementToAlgorithmItem(alg))
                      Error.addSourceMessage(Error.ASSIGN_RHS_ELABORATION, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, stmts #= more statements due to loop unrolling =#)
        end

        function instAssignment2(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPre::Prefix.PrefixType, var::Absyn.Exp, inRhs::Absyn.Exp, value::DAE.Exp, props::DAE.Properties, info::SourceInfo, inSource::DAE.ElementSource, initial_::SCode.Initial, inImpl::Bool, unrollForLoops::Bool #= we should unroll for loops if they are part of an algorithm in a model =#, numError::ModelicaInteger) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local stmts::List{DAE.Statement} #= more statements due to loop unrolling =#
              local outCache::FCore.Cache

              (outCache, stmts) = begin
                  local ce::DAE.ComponentRef
                  local ce_1::DAE.ComponentRef
                  local cprop::DAE.Properties
                  local eprop::DAE.Properties
                  local prop::DAE.Properties
                  local prop1::DAE.Properties
                  local prop2::DAE.Properties
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local cre::DAE.Exp
                  local cre2::DAE.Exp
                  local e2_2::DAE.Exp
                  local e2_2_2::DAE.Exp
                  local lhs::DAE.Exp
                  local rhs::DAE.Exp
                  local stmt::DAE.Statement
                  local cr::Absyn.ComponentRef
                  local e::Absyn.Exp
                  local e1::Absyn.Exp
                  local e2::Absyn.Exp
                  local left::Absyn.Exp
                  local expl::List{Absyn.Exp}
                  local expl_1::List{DAE.Exp}
                  local expl_2::List{DAE.Exp}
                  local cprops::List{DAE.Properties}
                  local eprops::List{DAE.Properties}
                  local attrs::List{DAE.Attributes}
                  local lt::DAE.Type
                  local rt::DAE.Type
                  local ty::DAE.Type
                  local t::DAE.Type
                  local s::String
                  local lhs_str::String
                  local rhs_str::String
                  local lt_str::String
                  local rt_str::String
                  local s1::String
                  local s2::String
                  local cache::FCore.Cache
                  local pattern::DAE.Pattern
                  local attr::DAE.Attributes
                  local source::DAE.ElementSource
                  local dim::DAE.Dimension
                  local lhs_dim::DAE.Dimension
                  local rhs_dim::DAE.Dimension
                  local lhs_idxs::List{DAE.Exp}
                  local rhs_idxs::List{DAE.Exp}
                   #=  v := expr; where v or expr are size 0
                   =#
                @matchcontinue (inCache, var, value, props) begin
                  (cache, Absyn.CREF(cr), e_1, _)  => begin
                      @match (cache, (@match DAE.CREF(_, t) = lhs), _, attr) = Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info)
                      @match DAE.T_ARRAY(dims = list(_)) = t
                      rhs = e_1
                      Static.checkAssignmentToInput(var, attr, inEnv, false, info)
                      @match DAE.T_ARRAY(dims = _cons(lhs_dim, _)) = Expression.typeof(lhs)
                      @match DAE.T_ARRAY(dims = _cons(rhs_dim, _)) = Expression.typeof(rhs)
                      @match nil = expandArrayDimension(lhs_dim, lhs)
                      @match nil = expandArrayDimension(rhs_dim, rhs)
                    (cache, nil)
                  end

                  (cache, Absyn.CREF(cr), e_1, eprop)  => begin
                      @match (cache, DAE.CREF(ce, t), cprop, attr) = Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info)
                      Static.checkAssignmentToInput(var, attr, inEnv, false, info)
                      (cache, ce_1) = Static.canonCref(cache, inEnv, ce, inImpl)
                      (cache, ce_1) = PrefixUtil.prefixCrefInnerOuter(cache, inEnv, inIH, ce_1, inPre)
                      (cache, t) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, t)
                      lt = Types.getPropType(cprop)
                      (cache, lt) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, lt)
                      cprop = Types.setPropType(cprop, lt)
                      (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre)
                      rt = Types.getPropType(eprop)
                      (cache, rt) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, rt)
                      eprop = Types.setPropType(eprop, rt)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = makeAssignment(Expression.makeCrefExp(ce_1, t), cprop, e_2, eprop, attr, initial_, source)
                    (cache, list(stmt))
                  end

                  (cache, e2 && Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "der"), functionArgs = Absyn.FUNCTIONARGS(args = Absyn.CREF(cr) <|  nil())), e_1, eprop)  => begin
                      (cache, _, cprop, attr) = Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info)
                      @match (cache, (@match DAE.CALL() = e2_2), _) = Static.elabExp(cache, inEnv, e2, inImpl, true, inPre, info)
                      (cache, e2_2_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e2_2, inPre)
                      (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = makeAssignment(e2_2_2, cprop, e_2, eprop, attr, initial_, source)
                    (cache, list(stmt))
                  end

                  (cache, Absyn.CREF(cr), e_1, eprop)  => begin
                      (cache, cre, cprop, attr) = Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info)
                      Static.checkAssignmentToInput(var, attr, inEnv, false, info)
                      (cache, cre2) = PrefixUtil.prefixExp(cache, inEnv, inIH, cre, inPre)
                      (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = makeAssignment(cre2, cprop, e_2, eprop, attr, initial_, source)
                    (cache, list(stmt))
                  end

                  (cache, Absyn.TUPLE(expressions = expl), e_1, eprop)  => begin
                      @match true = ListUtil.all(expl, AbsynUtil.isCref)
                      @match (cache, (@match DAE.CALL() = e_1), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre)
                      (cache, expl_1, cprops, attrs) = Static.elabExpCrefNoEvalList(cache, inEnv, expl, inImpl, false, inPre, info)
                      Static.checkAssignmentToInputs(expl, attrs, inEnv, info)
                      checkNoDuplicateAssignments(expl_1, info)
                      (cache, expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_1, inPre)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = Algorithm.makeTupleAssignment(expl_2, cprops, e_2, eprop, initial_, source)
                    (cache, list(stmt))
                  end

                  (cache, Absyn.TUPLE(expressions = expl), e_1, eprop)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match true = ListUtil.all(expl, AbsynUtil.isCref)
                      @match true = Types.isTuple(Types.getPropType(eprop))
                      @match (cache, (@match DAE.MATCHEXPRESSION() = e_1), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre)
                      (cache, expl_1, cprops, attrs) = Static.elabExpCrefNoEvalList(cache, inEnv, expl, inImpl, false, inPre, info)
                      Static.checkAssignmentToInputs(expl, attrs, inEnv, info)
                      checkNoDuplicateAssignments(expl_1, info)
                      (cache, expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_1, inPre)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = Algorithm.makeTupleAssignment(expl_2, cprops, e_2, eprop, initial_, source)
                    (cache, list(stmt))
                  end

                  (cache, left, e_1, prop)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      ty = Types.getPropType(prop)
                      (e_1, ty) = Types.convertTupleToMetaTuple(e_1, ty)
                      (cache, pattern) = Patternm.elabPatternCheckDuplicateBindings(cache, inEnv, left, ty, info)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmt = if Types.isEmptyOrNoRetcall(ty)
                            DAE.STMT_NORETCALL(e_1, source)
                          else
                            DAE.STMT_ASSIGN(DAE.T_UNKNOWN_DEFAULT, DAE.PATTERN(pattern), e_1, source)
                          end
                    (cache, list(stmt))
                  end

                  (cache, Absyn.TUPLE(expressions = expl), e_1, eprop)  => begin
                      @match (cache, (@match DAE.TUPLE(PR = expl_1) = e_1), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info)
                      (cache, expl_2, cprops, attrs) = Static.elabExpCrefNoEvalList(cache, inEnv, expl, inImpl, false, inPre, info)
                      Static.checkAssignmentToInputs(expl, attrs, inEnv, info)
                      checkNoDuplicateAssignments(expl_2, info)
                      (cache, expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_2, inPre)
                      eprops = Types.propTuplePropList(eprop)
                      source = ElementSource.addElementSourceFileInfo(inSource, info)
                      stmts = Algorithm.makeAssignmentsList(expl_2, cprops, expl_1, eprops, DAE.dummyAttrVar, initial_, source)
                    (cache, stmts)
                  end

                  (_, e && Absyn.TUPLE(expressions = expl), _, _)  => begin
                      @match false = ListUtil.all(expl, AbsynUtil.isCref)
                      s = Dump.printExpStr(e)
                      Error.addSourceMessage(Error.TUPLE_ASSIGN_CREFS_ONLY, list(s), info)
                    fail()
                  end

                  (cache, e1 && Absyn.TUPLE(expressions = expl), _, prop2)  => begin
                      @match Absyn.CALL() = inRhs
                      @match true = ListUtil.all(expl, AbsynUtil.isCref)
                      (cache, e_1, prop1) = Static.elabExpLHS(cache, inEnv, e1, inImpl, false, inPre, info)
                      lt = Types.getPropType(prop1)
                      rt = Types.getPropType(prop2)
                      @match false = Types.subtype(lt, rt)
                      lhs_str = ExpressionDump.printExpStr(e_1)
                      rhs_str = Dump.printExpStr(inRhs)
                      lt_str = Types.unparseTypeNoAttr(lt)
                      rt_str = Types.unparseTypeNoAttr(rt)
                      Types.typeErrorSanityCheck(lt_str, rt_str, info)
                      Error.addSourceMessage(Error.ASSIGN_TYPE_MISMATCH_ERROR, list(lhs_str, rhs_str, lt_str, rt_str), info)
                    fail()
                  end

                  (_, Absyn.TUPLE(expressions = expl), e_1, _)  => begin
                      @match true = ListUtil.all(expl, AbsynUtil.isCref)
                      @shouldFail @match Absyn.CALL() = inRhs
                      s = ExpressionDump.printExpStr(e_1)
                      Error.addSourceMessage(Error.TUPLE_ASSIGN_FUNCALL_ONLY, list(s), info)
                    fail()
                  end

                  _  => begin
                        @match true = numError == Error.getNumErrorMessages()
                        s1 = Dump.printExpStr(var)
                        s2 = ExpressionDump.printExpStr(value)
                        Error.addSourceMessage(Error.ASSIGN_UNKNOWN_ERROR, list(s1, s2), info)
                      fail()
                  end
                end
              end
               #=  v := expr;
               =#
               #=  der(x) := ...
               =#
               #= /*SCode.RW()*/ =#
               #=  v[i] := expr (in e.g. for loops)
               =#
               #=  (v1,v2,..,vn) := func(...)
               =#
               #=  (v1,v2,..,vn) := match...
               =#
               #= /* Tuple with rhs constant */ =#
               #= /* SCode.RW() */ =#
               #= /* Tuple with lhs being a tuple NOT of crefs => Error */ =#
               #= /* Tuple with rhs not CALL or CONSTANT => Error */ =#
          (outCache, stmts #= more statements due to loop unrolling =#)
        end

        function checkNoDuplicateAssignments(inExps::List{<:DAE.Exp}, info::SourceInfo)
              local exp::DAE.Exp
              local exps::List{DAE.Exp} = inExps

              while ! listEmpty(exps)
                @match _cons(exp, exps) = exps
                if Expression.isWild(exp)
                  continue
                elseif listMember(exp, exps)
                  Error.addSourceMessage(Error.DUPLICATE_DEFINITION, list(ExpressionDump.printExpStr(exp)), info)
                  fail()
                end
              end
        end

        function generateNoConstantBindingError(emptyValueOpt::Option{<:Values.Value}, info::SourceInfo)
              _ = begin
                  local scope::String #= the scope where we could not find the binding =#
                  local name::String #= the name of the variable =#
                  local ty::Values.Value #= the DAE.Type translated to Value using defaults =#
                  local tyStr::String #= the type of the variable =#
                @match (emptyValueOpt, info) begin
                  (NONE(), _)  => begin
                    ()
                  end

                  (SOME(Values.EMPTY(scope, name, _, _)), _)  => begin
                      Error.addSourceMessage(Error.NO_CONSTANT_BINDING, list(name, scope), info)
                    fail()
                  end
                end
              end
        end

        function getIteratorType(ty::DAE.Type, id::String, info::SourceInfo) ::DAE.Type
              local oty::DAE.Type

              oty = begin
                  local str::String
                @match ty begin
                  DAE.T_ARRAY(ty = DAE.T_ARRAY(__))  => begin
                      str = Types.unparseType(ty)
                      Error.addSourceMessage(Error.ITERATOR_NON_ARRAY, list(id, str), info)
                    fail()
                  end

                  DAE.T_ARRAY(ty = oty)  => begin
                    oty
                  end

                  DAE.T_METALIST(ty = oty)  => begin
                    Types.boxIfUnboxedType(oty)
                  end

                  DAE.T_METAARRAY(ty = oty)  => begin
                    Types.boxIfUnboxedType(oty)
                  end

                  DAE.T_METATYPE(ty = oty)  => begin
                    getIteratorType(ty.ty, id, info)
                  end

                  _  => begin
                        str = Types.unparseType(ty)
                        Error.addSourceMessage(Error.ITERATOR_NON_ARRAY, list(id, str), info)
                      fail()
                  end
                end
              end
          oty
        end

        function instParForStatement(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inForStatement::SCode.Statement, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement} #= For statements can produce multiple statements due to unrolling. =#
              local outCache::FCore.Cache

              local iterator::String
              local oarange::Option{Absyn.Exp}
              local arange::Absyn.Exp
              local range::DAE.Exp
              local prop::DAE.Properties
              local body::List{SCode.Statement}
              local info::SourceInfo
              local iter_crefs::List{AbsynUtil.IteratorIndexedCref}

              @match SCode.ALG_PARFOR(index = iterator, range = oarange, parforBody = body, info = info) = inForStatement
              if isSome(oarange)
                @match SOME(arange) = oarange
                (outCache, range, prop) = Static.elabExp(inCache, inEnv, arange, inImpl, true, inPrefix, info)
              else
                iter_crefs = SCodeUtil.findIteratorIndexedCrefsInStatements(body, iterator)
                (range, prop, outCache) = Static.deduceIterationRange(iterator, iter_crefs, inEnv, inCache, info)
              end
               #=  Always unroll for-loops containing when-statements.
               =#
              if containsWhenStatements(body)
                (outCache, outStatements) = unrollForLoop(inCache, inEnv, inIH, inPrefix, inState, iterator, range, prop, body, inForStatement, info, inSource, inInitial, inImpl, inUnrollLoops)
              else
                (outCache, outStatements) = instParForStatement_dispatch(inCache, inEnv, inIH, inPrefix, inState, iterator, range, prop, body, info, inSource, inInitial, inImpl, inUnrollLoops)
              end
          (outCache, outStatements #= For statements can produce multiple statements due to unrolling. =#)
        end

        function instParForStatement_dispatch(inCache::FCore.Cache, inEnv::FCore.Graph, inIH::InnerOuter.InstHierarchy, inPrefix::Prefix.PrefixType, inState::ClassInf.SMNode, inIterator::String, inRange::DAE.Exp, inRangeProps::DAE.Properties, inBody::List{<:SCode.Statement}, inInfo::SourceInfo, inSource::DAE.ElementSource, inInitial::SCode.Initial, inImpl::Bool, inUnrollLoops::Bool) ::Tuple{FCore.Cache, List{DAE.Statement}}
              local outStatements::List{DAE.Statement}
              local outCache::FCore.Cache = inCache

              local ty::DAE.Type
              local c::DAE.Const
              local env::FCore.Graph
              local source::DAE.ElementSource
              local loop_prl_vars::List{Tuple{DAE.ComponentRef, SourceInfo}}
              local parfor_iter::DAE.ComponentRef
              local range::DAE.Exp

              c = Types.getPropConst(inRangeProps)
               #=  Remove the for-loop if the range is empty.
               =#
              if Types.isParameterOrConstant(c)
                try
                  @match (outCache, Values.ARRAY(valueLst = nil)) = Ceval.ceval(outCache, inEnv, inRange, inImpl, Absyn.MSG(inInfo), 0)
                  outStatements = nil
                  return (outCache, outStatements)
                catch
                end
              end
              ty = Types.getPropType(inRangeProps)
              ty = getIteratorType(ty, inIterator, inInfo)
              (outCache, range) = Ceval.cevalRangeIfConstant(outCache, inEnv, inRange, inRangeProps, inImpl, inInfo)
              (outCache, range) = PrefixUtil.prefixExp(outCache, inEnv, inIH, range, inPrefix)
              env = addParForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c))
              (outCache, outStatements) = instStatements(outCache, env, inIH, inPrefix, inState, inBody, inSource, inInitial, inImpl, inUnrollLoops)
               #=  this is where we check the parfor loop for data parallel specific
               =#
               #=  situations. Start with empty list and collect all variables cref'ed
               =#
               #=  in the loop body.
               =#
              loop_prl_vars = collectParallelVariables(nil, outStatements)
               #=  Remove the parfor loop iterator from the list(implicitly declared).
               =#
              parfor_iter = DAE.CREF_IDENT(inIterator, ty, nil)
              loop_prl_vars = ListUtil.deleteMemberOnTrue(parfor_iter, loop_prl_vars, crefInfoListCrefsEqual)
               #=  Check the cref's in the list one by one to make
               =#
               #=  sure that they are parallel variables.
               =#
               #=  checkParallelVariables(cache,env_1,loopPrlVars);
               =#
              ListUtil.map2_0(loop_prl_vars, isCrefParGlobalOrForIterator, outCache, env)
              source = ElementSource.addElementSourceFileInfo(inSource, inInfo)
              outStatements = list(Algorithm.makeParFor(inIterator, range, inRangeProps, outStatements, loop_prl_vars, source))
          (outCache, outStatements)
        end

         #= Checks if a component reference is referencing a parglobal
        variable or the loop iterator(implicitly declared is OK).
        All other references are errors. =#
        function isCrefParGlobalOrForIterator(inCrefInfo::Tuple{<:DAE.ComponentRef, SourceInfo}, inCache::FCore.Cache, inEnv::FCore.Graph)
              _ = begin
                  local errorString::String
                  local cref::DAE.ComponentRef
                  local info::SourceInfo
                  local prl::SCode.Parallelism
                  local isParglobal::Bool
                  local cnstForRange::Option{DAE.Const}
                @matchcontinue (inCrefInfo, inCache, inEnv) begin
                  ((cref, _), _, _)  => begin
                      @match (_, DAE.ATTR(parallelism = prl), _, _, _, _, _, _, _) = Lookup.lookupVar(inCache, inEnv, cref)
                      isParglobal = SCodeUtil.parallelismEqual(prl, SCode.PARGLOBAL())
                      @match true = isParglobal
                    ()
                  end

                  ((cref, info), _, _)  => begin
                      errorString = "\\n" + "- Component '" + AbsynUtil.pathString(ComponentReference.crefToPath(cref)) + "' is used in a parallel for loop." + "\\n" + "- Parallel for loops can only contain references to parglobal variables."
                      Error.addSourceMessage(Error.PARMODELICA_ERROR, list(errorString), info)
                    fail()
                  end
                end
              end
               #=  Look up the variable
               =#
               #=  is it parglobal var?
               =#
               #=  Now the iterator is already removed. No need for this.
               =#
               #=  is it the iterator of the parfor loop(implicitly declared)?
               =#
               #=  isForiterator = isSome(cnstForRange);
               =#
               #= is it either a parglobal var or for iterator
               =#
               #= true = isParglobal or isForiterator;
               =#
        end

         #= Compares if two <DAE.ComponentRef,SourceInfo> tuples have
        are the same in the sense that they have the same cref (which
        means they are references to the same component).
        The info is
        just for error messages. =#
        function crefInfoListCrefsEqual(inFoundCref::DAE.ComponentRef, inCrefInfos::Tuple{<:DAE.ComponentRef, SourceInfo}) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local cref1::DAE.ComponentRef
                @match (inFoundCref, inCrefInfos) begin
                  (_, (cref1, _))  => begin
                    ComponentReference.crefEqualWithoutSubs(cref1, inFoundCref)
                  end
                end
              end
          outBoolean
        end

         #= Traverses the body of a parallel for loop and collects
        all variable references. the list should not include implictly
        declared variables like loop iterators. Only references to
        components declared to outside of the parfor loop need to be
        collected.
        We need the list of referenced variables for Code generation in the backend.
        EXPENSIVE operation but needs to be done. =#
        function collectParallelVariables(inCrefInfos::List{<:Tuple{<:DAE.ComponentRef, SourceInfo}}, inStatments::List{<:DAE.Statement}) ::List{Tuple{DAE.ComponentRef, SourceInfo}}
              local outCrefInfos::List{Tuple{DAE.ComponentRef, SourceInfo}}

              outCrefInfos = begin
                  local restStmts::List{DAE.Statement}
                  local stmtList::List{DAE.Statement}
                  local crefInfoList::List{Tuple{DAE.ComponentRef, SourceInfo}}
                  local foundCref::DAE.ComponentRef
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local info::SourceInfo
                  local iter::DAE.Ident
                  local iterType::DAE.Type
                  local debugStmt::DAE.Statement
                @matchcontinue (inCrefInfos, inStatments) begin
                  (_,  nil())  => begin
                    inCrefInfos
                  end

                  (crefInfoList, DAE.STMT_ASSIGN(_, exp1, exp2, DAE.SOURCE(info = info)) <| restStmts)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1, exp2), info)
                      crefInfoList = collectParallelVariables(crefInfoList, restStmts)
                    crefInfoList
                  end

                  (crefInfoList, DAE.STMT_FOR(type_ = iterType, iter = iter, range = exp1, statementLst = stmtList, source = DAE.SOURCE(info = info)) <| restStmts)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), info)
                      crefInfoList = collectParallelVariables(crefInfoList, stmtList)
                      foundCref = DAE.CREF_IDENT(iter, iterType, nil)
                      (crefInfoList, _) = ListUtil.deleteMemberOnTrue(foundCref, crefInfoList, crefInfoListCrefsEqual)
                      crefInfoList = collectParallelVariables(crefInfoList, restStmts)
                    crefInfoList
                  end

                  (crefInfoList, DAE.STMT_IF(exp1, stmtList, _, DAE.SOURCE(info = info)) <| restStmts)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), info)
                      crefInfoList = collectParallelVariables(crefInfoList, stmtList)
                      crefInfoList = collectParallelVariables(crefInfoList, restStmts)
                    crefInfoList
                  end

                  (crefInfoList, DAE.STMT_WHILE(exp1, stmtList, DAE.SOURCE(info = info)) <| restStmts)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), info)
                      crefInfoList = collectParallelVariables(crefInfoList, stmtList)
                      crefInfoList = collectParallelVariables(crefInfoList, restStmts)
                    crefInfoList
                  end

                  (crefInfoList, _ <| restStmts)  => begin
                    collectParallelVariables(crefInfoList, restStmts)
                  end
                end
              end
               #= check the lhs and rhs.
               =#
               #= check the rest
               =#
               #=  for statment
               =#
               #= check the range exp.
               =#
               #=  check the body of the loop.
               =#
               #=         crefInfoList_tmp = collectParallelVariables(crefInfoList,stmtList);
               =#
               #=  We need to remove the iterator from
               =#
               #=  the list generated for the loop bofy. For iterators are implicitly declared.
               =#
               #=  This should be done here since the iterator is in scope only as long as we
               =#
               #=  are in the loop body.
               =#
               #=  (crefInfoList_tmp,_) = List.deleteMemberOnTrue(foundCref,crefInfoList_tmp,crefInfoListCrefsEqual);
               =#
               #=  Now that the iterator is removed cocatenate the two lists
               =#
               #=  crefInfoList = listAppend(expandableEqs(crefInfoList_tmp,crefInfoList);
               =#
               #= check the rest
               =#
               #=  If statment
               =#
               #=  mahge TODO: Fix else Exps.
               =#
               #= check the condition exp.
               =#
               #= check the body of the if statment
               =#
               #= check the rest
               =#
               #= check the condition exp.
               =#
               #= check the body of the while loop
               =#
               #= check the rest
               =#
          outCrefInfos
        end

        function collectParallelVariablesinExps(inCrefInfos::List{<:Tuple{<:DAE.ComponentRef, SourceInfo}}, inExps::List{<:DAE.Exp}, inInfo::SourceInfo) ::List{Tuple{DAE.ComponentRef, SourceInfo}}
              local outCrefInfos::List{Tuple{DAE.ComponentRef, SourceInfo}}

              outCrefInfos = begin
                  local restExps::List{DAE.Exp}
                  local crefInfoList::List{Tuple{DAE.ComponentRef, SourceInfo}}
                  local foundCref::DAE.ComponentRef
                  local exp1::DAE.Exp
                  local exp2::DAE.Exp
                  local exp3::DAE.Exp
                  local expLst1::List{DAE.Exp}
                  local subscriptLst::List{DAE.Subscript}
                  local alreadyInList::Bool
                  local debugExp::DAE.Exp
                @matchcontinue (inCrefInfos, inExps, inInfo) begin
                  (_,  nil(), _)  => begin
                    inCrefInfos
                  end

                  (crefInfoList, DAE.CREF(foundCref, _) <| restExps, _)  => begin
                      alreadyInList = ListUtil.isMemberOnTrue(foundCref, crefInfoList, crefInfoListCrefsEqual)
                      crefInfoList = if alreadyInList
                            crefInfoList
                          else
                            _cons((foundCref, inInfo), crefInfoList)
                          end
                      @match DAE.CREF_IDENT(_, _, subscriptLst) = foundCref
                      crefInfoList = collectParallelVariablesInSubscriptList(crefInfoList, subscriptLst, inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.ASUB(exp1, expLst1) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, _cons(exp1, expLst1), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.BINARY(exp1, _, exp2) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1, exp2), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.UNARY(_, exp1) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.LBINARY(exp1, _, exp2) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1, exp2), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.LUNARY(_, exp1) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.RANGE(_, exp1, SOME(exp2), exp3) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1, exp2, exp3), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.RANGE(_, exp1, NONE(), exp3) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1, exp3), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, DAE.CAST(_, exp1) <| restExps, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), inInfo)
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, _ <| restExps, _)  => begin
                    collectParallelVariablesinExps(crefInfoList, restExps, inInfo)
                  end
                end
              end
               #=  Check if the cref is already added to the list
               =#
               #=  avoid repeated lookup.
               =#
               #=  and we don't care about subscript differences.
               =#
               #=  add it to the list if it is not in there
               =#
               #= check the subscripts (that is: if they are crefs)
               =#
               #=  check the rest
               =#
               #=  Array subscripting
               =#
               #= check the ASUB specific expressions
               =#
               #=  check the rest
               =#
               #=  Binary Operations
               =#
               #= check the lhs and rhs
               =#
               #=  check the rest
               =#
               #=  Unary Operations
               =#
               #= check the exp
               =#
               #=  check the rest
               =#
               #=  Logical Binary Operations
               =#
               #= check the lhs and rhs
               =#
               #=  check the rest
               =#
               #=  Logical Unary Operations
               =#
               #= check the exp
               =#
               #=  check the rest
               =#
               #=  range with step value.
               =#
               #= check the range specific expressions
               =#
               #=  check the rest
               =#
               #=  range withOUT step value.
               =#
               #= check the range specific expressions
               =#
               #=  check the rest
               =#
               #=  cast stmt
               =#
               #= check the range specific expressions
               =#
               #=  check the rest
               =#
               #=  ICONST, RCONST, SCONST, BCONST, ENUM_LITERAL
               =#
               #=
               =#
          outCrefInfos
        end

        function collectParallelVariablesInSubscriptList(inCrefInfos::List{<:Tuple{<:DAE.ComponentRef, SourceInfo}}, inSubscriptLst::List{<:DAE.Subscript}, inInfo::SourceInfo) ::List{Tuple{DAE.ComponentRef, SourceInfo}}
              local outCrefInfos::List{Tuple{DAE.ComponentRef, SourceInfo}}

              outCrefInfos = begin
                  local restSubs::List{DAE.Subscript}
                  local crefInfoList::List{Tuple{DAE.ComponentRef, SourceInfo}}
                  local exp1::DAE.Exp
                @matchcontinue (inCrefInfos, inSubscriptLst, inInfo) begin
                  (_,  nil(), _)  => begin
                    inCrefInfos
                  end

                  (crefInfoList, DAE.INDEX(exp1) <| restSubs, _)  => begin
                      crefInfoList = collectParallelVariablesinExps(crefInfoList, list(exp1), inInfo)
                      crefInfoList = collectParallelVariablesInSubscriptList(crefInfoList, restSubs, inInfo)
                    crefInfoList
                  end

                  (crefInfoList, _ <| restSubs, _)  => begin
                    collectParallelVariablesInSubscriptList(crefInfoList, restSubs, inInfo)
                  end
                end
              end
               #= check the sub exp.
               =#
               #= check the rest
               =#
          outCrefInfos
        end

        function checkValidNoRetcall(exp::DAE.Exp, info::SourceInfo)
              _ = begin
                  local str::String
                @match (exp, info) begin
                  (DAE.CALL(__), _)  => begin
                    ()
                  end

                  (DAE.REDUCTION(__), _)  => begin
                    ()
                  end

                  (DAE.TUPLE( nil()), _)  => begin
                    ()
                  end

                  _  => begin
                        str = ExpressionDump.printExpStr(exp)
                        Error.addSourceMessage(Error.NORETCALL_INVALID_EXP, list(str), info)
                      fail()
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

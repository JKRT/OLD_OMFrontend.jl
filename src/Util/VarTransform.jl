  module VarTransform


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl VariableReplacements

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    VisitFunc = Function

    VisitFunc = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

    FuncTypeExp_ExpToBoolean = Function

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

        import DAE

        import HashTable2

        import HashTable3

        import SCode

        import MetaModelica.Dangerous.listReverseInPlace

          #= VariableReplacements consists of a mapping between variables and expressions, the first binary tree of this type.
          To eliminate a variable from an equation system a replacement rule varname->expression is added to this
          datatype.
          To be able to update these replacement rules incrementally a backward lookup mechanism is also required.
          For instance, having a rule a->b and adding a rule b->c requires to find the first rule a->b and update it to
          a->c. This is what the second binary tree is used for. =#
         @Uniontype VariableReplacements begin
              @Record REPLACEMENTS begin

                       hashTable #= src -> dst, used for replacing. src is variable, dst is expression. =#::HashTable2.HashTable
                       invHashTable #= dst -> list of sources. dst is a variable, sources are variables. =#::HashTable3.HashTable
              end
         end

        import Absyn

        import BaseHashTable

        import ComponentReference
         #= protected import Debug;
         =#

        import Expression

        import ExpressionDump

        import ExpressionSimplify

        import ListUtil

        import Util

         #= Apply a set of replacement rules on a DAE  =#
        function applyReplacementsDAE(dae::DAE.DAElist, repl::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local elts::List{DAE.Element}
                  local funcs::DAE.FunctionTree
                  local funcLst::List{Tuple{DAE.AvlTreePathFunction.Key, DAE.AvlTreePathFunction.Value}}
                @match (dae, repl, condExpFunc) begin
                  (DAE.DAE_LIST(elementLst = elts), _, _)  => begin
                      elts = applyReplacementsDAEElts(elts, repl, condExpFunc)
                    DAE.DAE_LIST(elts)
                  end
                end
              end
          outDae
        end

         #= Help function to applyReplacementsDAE, goes though the element list =#
        function applyReplacementsDAEElts(inDae::List{<:DAE.Element}, repl::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::List{DAE.Element}
              local outDae::List{DAE.Element}

              if BaseHashTable.hashTableCurrentSize(repl.hashTable) == 0
                outDae = inDae
                return outDae
              end
              outDae = list(begin
                  local cr::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr1_2::DAE.ComponentRef
                  local elist::List{DAE.Element}
                  local elist2::List{DAE.Element}
                  local elist22::List{DAE.Element}
                  local elist1::List{DAE.Element}
                  local elist11::List{DAE.Element}
                  local elt2::DAE.Element
                  local elt22::DAE.Element
                  local elt1::DAE.Element
                  local elt11::DAE.Element
                  local kind::DAE.VarKind
                  local dir::DAE.VarDirection
                  local tp::DAE.Type
                  local ftp::DAE.Type
                  local bindExp::DAE.Exp
                  local bindExp2::DAE.Exp
                  local e::DAE.Exp
                  local e2::DAE.Exp
                  local e22::DAE.Exp
                  local e1::DAE.Exp
                  local e11::DAE.Exp
                  local e3::DAE.Exp
                  local e32::DAE.Exp
                  local dims::DAE.InstDims
                  local start::DAE.StartValue
                  local ct::DAE.ConnectorType
                  local source::DAE.ElementSource #= the origin of the element =#
                  local attr::Option{DAE.VariableAttributes}
                  local cmt::Option{SCode.Comment}
                  local io::Absyn.InnerOuter
                  local idims::DAE.Dimensions
                  local extDecl::DAE.ExternalDecl
                  local id::DAE.Ident
                  local path::Absyn.Path
                  local stmts::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local prl::DAE.VarParallelism
                  local prot::DAE.VarVisibility
                  local partialPrefix::Bool
                  local extdecl::DAE.ExternalDecl
                  local f1::DAE.Function
                  local f2::DAE.Function
                  local str::String
                  local tbs::List{List{DAE.Element}}
                  local tbs_1::List{List{DAE.Element}}
                  local conds::List{DAE.Exp}
                  local conds_1::List{DAE.Exp}
                @match elt begin
                  DAE.VAR(cr, kind, dir, prl, prot, tp, SOME(bindExp), dims, ct, source, attr, cmt, io)  => begin
                      (bindExp2, _) = replaceExp(bindExp, repl, condExpFunc)
                      attr = applyReplacementsVarAttr(attr, repl, condExpFunc)
                    DAE.VAR(cr, kind, dir, prl, prot, tp, SOME(bindExp2), dims, ct, source, attr, cmt, io)
                  end

                  DAE.VAR(cr, kind, dir, prl, prot, tp, NONE(), dims, ct, source, attr, cmt, io)  => begin
                      attr = applyReplacementsVarAttr(attr, repl, condExpFunc)
                    DAE.VAR(cr, kind, dir, prl, prot, tp, NONE(), dims, ct, source, attr, cmt, io)
                  end

                  DAE.DEFINE(cr, e, source)  => begin
                      (e2, _) = replaceExp(e, repl, condExpFunc)
                      @match (DAE.CREF(cr2, _), _) = replaceExp(Expression.crefExp(cr), repl, condExpFunc)
                    DAE.DEFINE(cr2, e2, source)
                  end

                  DAE.INITIALDEFINE(cr, e, source)  => begin
                      (e2, _) = replaceExp(e, repl, condExpFunc)
                      @match (DAE.CREF(cr2, _), _) = replaceExp(Expression.crefExp(cr), repl, condExpFunc)
                    DAE.INITIALDEFINE(cr2, e2, source)
                  end

                  DAE.EQUEQUATION(cr, cr1, source)  => begin
                      @match (DAE.CREF(cr2, _), _) = replaceExp(Expression.crefExp(cr), repl, condExpFunc)
                      @match (DAE.CREF(cr1_2, _), _) = replaceExp(Expression.crefExp(cr1), repl, condExpFunc)
                    DAE.EQUEQUATION(cr2, cr1_2, source)
                  end

                  DAE.EQUATION(e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.EQUATION(e11, e22, source)
                  end

                  DAE.ARRAY_EQUATION(idims, e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.ARRAY_EQUATION(idims, e11, e22, source)
                  end

                  DAE.INITIAL_ARRAY_EQUATION(idims, e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.INITIAL_ARRAY_EQUATION(idims, e11, e22, source)
                  end

                  DAE.WHEN_EQUATION(e1, elist, SOME(elt2), source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      @match elt2 <| nil = applyReplacementsDAEElts(list(elt2), repl, condExpFunc)
                      elist2 = applyReplacementsDAEElts(elist, repl, condExpFunc)
                    DAE.WHEN_EQUATION(e11, elist2, SOME(elt2), source)
                  end

                  DAE.WHEN_EQUATION(e1, elist, NONE(), source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      elist2 = applyReplacementsDAEElts(elist, repl, condExpFunc)
                    DAE.WHEN_EQUATION(e11, elist2, NONE(), source)
                  end

                  DAE.IF_EQUATION(conds, tbs, elist2, source)  => begin
                      (conds_1, _) = replaceExpList(conds, repl, condExpFunc)
                      tbs_1 = ListUtil.map2(tbs, applyReplacementsDAEElts, repl, condExpFunc)
                      elist22 = applyReplacementsDAEElts(elist2, repl, condExpFunc)
                    DAE.IF_EQUATION(conds_1, tbs_1, elist22, source)
                  end

                  DAE.INITIAL_IF_EQUATION(conds, tbs, elist2, source)  => begin
                      (conds_1, _) = replaceExpList(conds, repl, condExpFunc)
                      tbs_1 = ListUtil.map2(tbs, applyReplacementsDAEElts, repl, condExpFunc)
                      elist22 = applyReplacementsDAEElts(elist2, repl, condExpFunc)
                    DAE.INITIAL_IF_EQUATION(conds_1, tbs_1, elist22, source)
                  end

                  DAE.INITIALEQUATION(e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.INITIALEQUATION(e11, e22, source)
                  end

                  DAE.ALGORITHM(DAE.ALGORITHM_STMTS(stmts), source)  => begin
                      (stmts2, _) = replaceEquationsStmts(stmts, repl, condExpFunc)
                    DAE.ALGORITHM(DAE.ALGORITHM_STMTS(stmts2), source)
                  end

                  DAE.INITIALALGORITHM(DAE.ALGORITHM_STMTS(stmts), source)  => begin
                      (stmts2, _) = replaceEquationsStmts(stmts, repl, condExpFunc)
                    DAE.INITIALALGORITHM(DAE.ALGORITHM_STMTS(stmts2), source)
                  end

                  DAE.COMP(id, elist, source, cmt)  => begin
                      elist = applyReplacementsDAEElts(elist, repl, condExpFunc)
                    DAE.COMP(id, elist, source, cmt)
                  end

                  DAE.EXTOBJECTCLASS(__)  => begin
                    elt
                  end

                  DAE.ASSERT(e1, e2, e3, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                      (e32, _) = replaceExp(e3, repl, condExpFunc)
                    DAE.ASSERT(e11, e22, e32, source)
                  end

                  DAE.INITIAL_ASSERT(e1, e2, e3, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                      (e32, _) = replaceExp(e3, repl, condExpFunc)
                    DAE.INITIAL_ASSERT(e11, e22, e32, source)
                  end

                  DAE.TERMINATE(e1, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                    DAE.TERMINATE(e11, source)
                  end

                  DAE.INITIAL_TERMINATE(e1, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                    DAE.INITIAL_TERMINATE(e11, source)
                  end

                  DAE.REINIT(cr, e1, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      @match (DAE.CREF(cr2, _), _) = replaceExp(Expression.crefExp(cr), repl, condExpFunc)
                    DAE.REINIT(cr2, e11, source)
                  end

                  DAE.COMPLEX_EQUATION(e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.COMPLEX_EQUATION(e11, e22, source)
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(e1, e2, source)  => begin
                      (e11, _) = replaceExp(e1, repl, condExpFunc)
                      (e22, _) = replaceExp(e2, repl, condExpFunc)
                    DAE.INITIAL_COMPLEX_EQUATION(e11, e22, source)
                  end

                  _  => begin
                        Error.addInternalError("applyReplacementsDAEElts should not fail", sourceInfo())
                      fail()
                  end
                end
              end for elt in inDae)
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #= /* TODO: Add operation to source */ =#
               #=  failtrace. adrpo: TODO! FIXME! this SHOULD NOT FAIL!
               =#
               #=  Debug.fprintln(Flags.FAILTRACE, \"- VarTransform.applyReplacementsDAEElts could not apply replacements to: \" + DAEDump.dumpElementsStr({elt}));
               =#
          outDae
        end

         #= Help function to applyReplacementsDAEElts =#
        function applyReplacementsVarAttr(attr::Option{<:DAE.VariableAttributes}, repl::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::Option{DAE.VariableAttributes}
              local outAttr::Option{DAE.VariableAttributes}

              outAttr = begin
                  local quantity::Option{DAE.Exp}
                  local unit::Option{DAE.Exp}
                  local displayUnit::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local initial_::Option{DAE.Exp}
                  local fixed::Option{DAE.Exp}
                  local nominal::Option{DAE.Exp}
                  local startOrigin::Option{DAE.Exp}
                  local stateSelect::Option{DAE.StateSelect}
                  local unc::Option{DAE.Uncertainty}
                  local dist::Option{DAE.Distribution}
                  local eb::Option{DAE.Exp}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                @match (attr, repl, condExpFunc) begin
                  (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, initial_, fixed, nominal, stateSelect, unc, dist, eb, ip, fn, startOrigin)), _, _)  => begin
                      quantity = replaceExpOpt(quantity, repl, condExpFunc)
                      unit = replaceExpOpt(unit, repl, condExpFunc)
                      displayUnit = replaceExpOpt(displayUnit, repl, condExpFunc)
                      min = replaceExpOpt(min, repl, condExpFunc)
                      max = replaceExpOpt(max, repl, condExpFunc)
                      initial_ = replaceExpOpt(initial_, repl, condExpFunc)
                      fixed = replaceExpOpt(fixed, repl, condExpFunc)
                      nominal = replaceExpOpt(nominal, repl, condExpFunc)
                    SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, initial_, fixed, nominal, stateSelect, unc, dist, eb, ip, fn, startOrigin))
                  end

                  (SOME(DAE.VAR_ATTR_INT(quantity, min, max, initial_, fixed, unc, dist, eb, ip, fn, startOrigin)), _, _)  => begin
                      quantity = replaceExpOpt(quantity, repl, condExpFunc)
                      min = replaceExpOpt(min, repl, condExpFunc)
                      max = replaceExpOpt(max, repl, condExpFunc)
                      initial_ = replaceExpOpt(initial_, repl, condExpFunc)
                      fixed = replaceExpOpt(fixed, repl, condExpFunc)
                    SOME(DAE.VAR_ATTR_INT(quantity, min, max, initial_, fixed, unc, dist, eb, ip, fn, startOrigin))
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(quantity, initial_, fixed, eb, ip, fn, startOrigin)), _, _)  => begin
                      quantity = replaceExpOpt(quantity, repl, condExpFunc)
                      initial_ = replaceExpOpt(initial_, repl, condExpFunc)
                      fixed = replaceExpOpt(fixed, repl, condExpFunc)
                    SOME(DAE.VAR_ATTR_BOOL(quantity, initial_, fixed, eb, ip, fn, startOrigin))
                  end

                  (SOME(DAE.VAR_ATTR_STRING(quantity, initial_, fixed, eb, ip, fn, startOrigin)), _, _)  => begin
                      quantity = replaceExpOpt(quantity, repl, condExpFunc)
                      initial_ = replaceExpOpt(initial_, repl, condExpFunc)
                      fixed = replaceExpOpt(fixed, repl, condExpFunc)
                    SOME(DAE.VAR_ATTR_STRING(quantity, initial_, fixed, eb, ip, fn, startOrigin))
                  end

                  (NONE(), _, _)  => begin
                    NONE()
                  end
                end
              end
               #= TODO: replace expressions also in uncertainty attributes (unc and dist)
               =#
          outAttr
        end

         #= This function takes a VariableReplacements and two component references.
          It applies the replacements to each component reference.
         =#
        function applyReplacements(inVariableReplacements1::VariableReplacements, inComponentRef2::DAE.ComponentRef, inComponentRef3::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
              local outComponentRef2::DAE.ComponentRef
              local outComponentRef1::DAE.ComponentRef

              (outComponentRef1, outComponentRef2) = begin
                  local cr1_1::DAE.ComponentRef
                  local cr2_1::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local repl::VariableReplacements
                @match (inVariableReplacements1, inComponentRef2, inComponentRef3) begin
                  (repl, cr1, cr2)  => begin
                      @match (DAE.CREF(cr1_1, _), _) = replaceExp(Expression.crefExp(cr1), repl, NONE())
                      @match (DAE.CREF(cr2_1, _), _) = replaceExp(Expression.crefExp(cr2), repl, NONE())
                    (cr1_1, cr2_1)
                  end
                end
              end
          (outComponentRef1, outComponentRef2)
        end

         #=  Author: BZ, 2008-11

          This function takes a VariableReplacements and a list of component references.
          It applies the replacements to each component reference.
         =#
        function applyReplacementList(repl::VariableReplacements, increfs::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local ocrefs::List{DAE.ComponentRef}

              ocrefs = begin
                  local cr1_1::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                @match (repl, increfs) begin
                  (_,  nil())  => begin
                    nil
                  end

                  (_, cr1 <| ocrefs)  => begin
                      @match (DAE.CREF(cr1_1, _), _) = replaceExp(Expression.crefExp(cr1), repl, NONE())
                      ocrefs = applyReplacementList(repl, ocrefs)
                    _cons(cr1_1, ocrefs)
                  end
                end
              end
          ocrefs
        end

         #=

        Similar to applyReplacements but for expressions instead of component references.
         =#
        function applyReplacementsExp(repl::VariableReplacements, inExp1::DAE.Exp, inExp2::DAE.Exp) ::Tuple{DAE.Exp, DAE.Exp}
              local outExp2::DAE.Exp
              local outExp1::DAE.Exp

              (outExp1, outExp2) = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local b1::Bool
                  local b2::Bool
                @match (repl, inExp1, inExp2) begin
                  (_, e1, e2)  => begin
                      (e1, _) = replaceExp(e1, repl, NONE())
                      (e2, _) = replaceExp(e2, repl, NONE())
                      (e1, _) = ExpressionSimplify.simplify1(e1)
                      (e2, _) = ExpressionSimplify.simplify1(e2)
                    (e1, e2)
                  end
                end
              end
          (outExp1, outExp2)
        end

         #= create an array of n empty replacements =#
        function emptyReplacementsArray(n::ModelicaInteger) ::Array{VariableReplacements}
              local repl::Array{VariableReplacements}

              repl = listArray(emptyReplacementsArray2(n))
          repl
        end

         #= help function =#
        function emptyReplacementsArray2(n::ModelicaInteger) ::List{VariableReplacements}
              local replLst::List{VariableReplacements}

              replLst = begin
                  local r::VariableReplacements
                @matchcontinue n begin
                  0  => begin
                    nil
                  end

                  _  => begin
                      @match true = n < 0
                      print("Internal error, emptyReplacementsArray2 called with negative n!")
                    fail()
                  end

                  _  => begin
                        @match true = n > 0
                        r = emptyReplacements()
                        replLst = emptyReplacementsArray2(n - 1)
                      _cons(r, replLst)
                  end
                end
              end
          replLst
        end

         #=
          Returns an empty set of replacement rules
         =#
        function emptyReplacements() ::VariableReplacements
              local outVariableReplacements::VariableReplacements

              outVariableReplacements = begin
                  local ht::HashTable2.HashTable
                  local invHt::HashTable3.HashTable
                @match () begin
                  ()  => begin
                      ht = HashTable2.emptyHashTable()
                      invHt = HashTable3.emptyHashTable()
                    REPLACEMENTS(ht, invHt)
                  end
                end
              end
          outVariableReplacements
        end

         #=
          Returns an empty set of replacement rules, giving a size of hashtables to allocate
         =#
        function emptyReplacementsSized(size::ModelicaInteger) ::VariableReplacements
              local outVariableReplacements::VariableReplacements

              outVariableReplacements = begin
                  local ht::HashTable2.HashTable
                  local invHt::HashTable3.HashTable
                @match size begin
                  _  => begin
                      ht = HashTable2.emptyHashTableSized(size)
                      invHt = HashTable3.emptyHashTableSized(size)
                    REPLACEMENTS(ht, invHt)
                  end
                end
              end
          outVariableReplacements
        end

         #=
          Helper function to replace_equations,
          Handles the replacement of DAE.Statement.
         =#
        function replaceEquationsStmts(inAlgorithmStatementLst::List{<:DAE.Statement}, repl::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{List{DAE.Statement}, Bool}
              local replacementPerformed::Bool
              local outAlgorithmStatementLst::List{DAE.Statement}

              (outAlgorithmStatementLst, replacementPerformed) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local e_3::DAE.Exp
                  local expl1::List{DAE.Exp}
                  local expl2::List{DAE.Exp}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local xs_1::List{DAE.Statement}
                  local xs::List{DAE.Statement}
                  local stmts::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local tp::DAE.Type
                  local tt::DAE.Type
                  local x::DAE.Statement
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local id1::String
                  local source::DAE.ElementSource
                  local fnName::Absyn.Path
                  local ew::Option{DAE.Statement}
                  local ew_1::Option{DAE.Statement}
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                  local iterIsArray::Bool
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local ix::ModelicaInteger
                @matchcontinue (inAlgorithmStatementLst, repl, condExpFunc) begin
                  ( nil(), _, _)  => begin
                    (nil, false)
                  end

                  (DAE.STMT_ASSIGN(type_ = tp, exp1 = e2, exp = e, source = source) <| xs, _, _)  => begin
                      (e_1, b1) = replaceExp(e, repl, condExpFunc)
                      (e_2, b2) = replaceExp(e2, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_ASSIGN(tp, e_2, e_1, source), xs_1), true)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(type_ = tp, expExpLst = expl1, exp = e, source = source) <| xs, _, _)  => begin
                      (e_1, b1) = replaceExp(e, repl, condExpFunc)
                      (expl2, b2) = replaceExpList(expl1, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_TUPLE_ASSIGN(tp, expl2, e_1, source), xs_1), true)
                  end

                  (DAE.STMT_ASSIGN_ARR(type_ = tp, lhs = e1, exp = e2, source = source) <| xs, _, _)  => begin
                      (e_1, b1) = replaceExp(e1, repl, condExpFunc)
                      (e_2, b2) = replaceExp(e2, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_ASSIGN_ARR(tp, e_1, e_2, source), xs_1), true)
                  end

                  (DAE.STMT_IF(exp = e, statementLst = stmts, else_ = el, source = source) <| xs, _, _)  => begin
                      (el_1, b1) = replaceEquationsElse(el, repl, condExpFunc)
                      (stmts2, b2) = replaceEquationsStmts(stmts, repl, condExpFunc)
                      (e_1, b3) = replaceExp(e, repl, condExpFunc)
                      @match true = b1 || b2 || b3
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_IF(e_1, stmts2, el_1, source), xs_1), true)
                  end

                  (DAE.STMT_FOR(type_ = tp, iterIsArray = iterIsArray, iter = id1, index = ix, range = e, statementLst = stmts, source = source) <| xs, _, _)  => begin
                      (stmts2, b1) = replaceEquationsStmts(stmts, repl, condExpFunc)
                      (e_1, b2) = replaceExp(e, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_FOR(tp, iterIsArray, id1, ix, e_1, stmts2, source), xs_1), true)
                  end

                  (DAE.STMT_WHILE(exp = e, statementLst = stmts, source = source) <| xs, _, _)  => begin
                      (stmts2, b1) = replaceEquationsStmts(stmts, repl, condExpFunc)
                      (e_1, b2) = replaceExp(e, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_WHILE(e_1, stmts2, source), xs_1), true)
                  end

                  (DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = ew, source = source) <| xs, _, _)  => begin
                      (ew_1, b1) = replaceOptEquationsStmts(ew, repl, condExpFunc)
                      (stmts2, b2) = replaceEquationsStmts(stmts, repl, condExpFunc)
                      (e_1, b3) = replaceExp(e, repl, condExpFunc)
                      @match true = b1 || b2 || b3
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, ew_1, source), xs_1), true)
                  end

                  (DAE.STMT_ASSERT(cond = e, msg = e2, level = e3, source = source) <| xs, _, _)  => begin
                      (e_1, b1) = replaceExp(e, repl, condExpFunc)
                      (e_2, b2) = replaceExp(e2, repl, condExpFunc)
                      (e_3, b3) = replaceExp(e3, repl, condExpFunc)
                      @match true = b1 || b2 || b3
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_ASSERT(e_1, e_2, e_3, source), xs_1), true)
                  end

                  (DAE.STMT_TERMINATE(msg = e, source = source) <| xs, _, _)  => begin
                      @match (e_1, true) = replaceExp(e, repl, condExpFunc)
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_TERMINATE(e_1, source), xs_1), true)
                  end

                  (DAE.STMT_REINIT(var = e, value = e2, source = source) <| xs, _, _)  => begin
                      (e_1, b1) = replaceExp(e, repl, condExpFunc)
                      (e_2, b2) = replaceExp(e2, repl, condExpFunc)
                      @match true = b1 || b2
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_REINIT(e_1, e_2, source), xs_1), true)
                  end

                  (DAE.STMT_NORETCALL(exp = e, source = source) <| xs, _, _)  => begin
                      @match (e_1, true) = replaceExp(e, repl, condExpFunc)
                      (xs_1, _) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(DAE.STMT_NORETCALL(e_1, source), xs_1), true)
                  end

                  (x <| xs, _, _)  => begin
                      (xs_1, b1) = replaceEquationsStmts(xs, repl, condExpFunc)
                    (_cons(x, xs_1), b1)
                  end
                end
              end
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #=  case ((DAE.STMT_ASSIGN_ARR(type_ = tp,componentRef = cr, exp = e,source = source) :: xs),_,_)
               =#
               #=  equation
               =#
               #=  (e_1,true) = replaceExp(e, repl, condExpFunc);
               =#
               #=  /* TODO: Add operation to source; do simplify? */
               =#
               #=  (xs_1,_) = replaceEquationsStmts(xs, repl,condExpFunc);
               =#
               #=  then
               =#
               #=  (DAE.STMT_ASSIGN_ARR(tp,cr,e_1,source) :: xs_1,true);
               =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
               #= /* TODO: Add operation to source; do simplify? */ =#
          (outAlgorithmStatementLst, replacementPerformed)
        end

         #=
        Helper function for replaceEquationsStmts, replaces DAE.Else =#
        function replaceEquationsElse(inElse::DAE.Else, repl::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{DAE.Else, Bool}
              local replacementPerformed::Bool
              local outElse::DAE.Else

              (outElse, replacementPerformed) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local st::List{DAE.Statement}
                  local st_1::List{DAE.Statement}
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                @matchcontinue (inElse, repl, condExpFunc) begin
                  (DAE.ELSEIF(e, st, el), _, _)  => begin
                      (el_1, b1) = replaceEquationsElse(el, repl, condExpFunc)
                      (st_1, b2) = replaceEquationsStmts(st, repl, condExpFunc)
                      (e_1, b3) = replaceExp(e, repl, condExpFunc)
                      @match true = b1 || b2 || b3
                    (DAE.ELSEIF(e_1, st_1, el_1), true)
                  end

                  (DAE.ELSE(st), _, _)  => begin
                      @match (st_1, true) = replaceEquationsStmts(st, repl, condExpFunc)
                    (DAE.ELSE(st_1), true)
                  end

                  _  => begin
                      (inElse, false)
                  end
                end
              end
          (outElse, replacementPerformed)
        end

         #=
        Helper function for replaceEquationsStmts, replaces optional statement =#
        function replaceOptEquationsStmts(optStmt::Option{<:DAE.Statement}, inVariableReplacements::VariableReplacements, condExpFunc::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{Option{DAE.Statement}, Bool}
              local replacementPerformed::Bool
              local outAlgorithmStatementLst::Option{DAE.Statement}

              (outAlgorithmStatementLst, replacementPerformed) = begin
                  local stmt::DAE.Statement
                  local stmt2::DAE.Statement
                @matchcontinue (optStmt, inVariableReplacements, condExpFunc) begin
                  (SOME(stmt), _, _)  => begin
                      @match (stmt2 <| nil, true) = replaceEquationsStmts(list(stmt), inVariableReplacements, condExpFunc)
                    (SOME(stmt2), true)
                  end

                  _  => begin
                      (optStmt, false)
                  end
                end
              end
          (outAlgorithmStatementLst, replacementPerformed)
        end

         #= Prints the variable replacements on form var1 -> var2 =#
        function dumpReplacements(inVariableReplacements::VariableReplacements)
              _ = begin
                  local str::String
                  local len_str::String
                  local len::ModelicaInteger
                  local ht::HashTable2.HashTable
                  local tplLst::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                @match inVariableReplacements begin
                  REPLACEMENTS(hashTable = ht)  => begin
                      tplLst = BaseHashTable.hashTableList(ht)
                      str = stringDelimitList(ListUtil.map(tplLst, printReplacementTupleStr), "\\n")
                      print("Replacements: (")
                      len = listLength(tplLst)
                      len_str = intString(len)
                      print(len_str)
                      print(")\\n")
                      print("=============\\n")
                      print(str)
                      print("\\n")
                    ()
                  end
                end
              end
        end

         #=
        Author BZ 2009-04
        Function for dumping replacements to string.
         =#
        function dumpReplacementsStr(inVariableReplacements::VariableReplacements) ::String
              local ostr::String

              ostr = begin
                  local srcs::List{DAE.Exp}
                  local dsts::List{DAE.Exp}
                  local srcstrs::List{String}
                  local dststrs::List{String}
                  local dststrs_1::List{String}
                  local strs::List{String}
                  local str::String
                  local len_str::String
                  local s1::String
                  local len::ModelicaInteger
                  local ht::HashTable2.HashTable
                  local tplLst::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                @match inVariableReplacements begin
                  REPLACEMENTS(hashTable = ht)  => begin
                      tplLst = BaseHashTable.hashTableList(ht)
                      str = stringDelimitList(ListUtil.map(tplLst, printReplacementTupleStr), "\\n")
                      s1 = "Replacements: (" + intString(listLength(tplLst)) + ")\\n=============\\n" + str + "\\n"
                    s1
                  end
                end
              end
          ostr
        end

         #=
        Author BZ 2009-04
        Extract all crefs -> exp to two separate lists.
         =#
        function getAllReplacements(inVariableReplacements::VariableReplacements) ::Tuple{List{DAE.ComponentRef}, List{DAE.Exp}}
              local dsts::List{DAE.Exp}
              local crefs::List{DAE.ComponentRef}

              (crefs, dsts) = begin
                  local ht::HashTable2.HashTable
                  local tplLst::List{Tuple{DAE.ComponentRef, DAE.Exp}}
                @match inVariableReplacements begin
                  REPLACEMENTS(hashTable = ht)  => begin
                      tplLst = BaseHashTable.hashTableList(ht)
                      crefs = ListUtil.map(tplLst, Util.tuple21)
                      dsts = ListUtil.map(tplLst, Util.tuple22)
                    (crefs, dsts)
                  end
                end
              end
          (crefs, dsts)
        end

         #= help function to dumpReplacements =#
        function printReplacementTupleStr(tpl::Tuple{<:DAE.ComponentRef, DAE.Exp}) ::String
              local str::String

               #=  optional exteded type debugging
               =#
               #= str := ComponentReference.debugPrintComponentRefTypeStr(Util.tuple21(tpl)) + \" -> \" + ExpressionDump.debugPrintComponentRefExp(Util.tuple22(tpl));
               =#
               #=  Normal debugging, without type&dimension information on crefs.
               =#
              str = ComponentReference.printComponentRefStr(Util.tuple21(tpl)) + " -> " + ExpressionDump.printExpStr(Util.tuple22(tpl))
          str
        end

         #= Returns all sources of the replacement rules =#
        function replacementSources(repl::VariableReplacements) ::List{DAE.ComponentRef}
              local sources::List{DAE.ComponentRef}

              sources = begin
                  local srcs::List{DAE.Exp}
                  local ht::HashTable2.HashTable
                @match repl begin
                  REPLACEMENTS(ht, _)  => begin
                      sources = BaseHashTable.hashTableKeyList(ht)
                    sources
                  end
                end
              end
          sources
        end

         #= Returns all targets of the replacement rules =#
        function replacementTargets(repl::VariableReplacements) ::List{DAE.ComponentRef}
              local sources::List{DAE.ComponentRef}

              sources = begin
                  local targets::List{DAE.Exp}
                  local targets2::List{DAE.ComponentRef}
                  local ht::HashTable2.HashTable
                @match repl begin
                  REPLACEMENTS(ht, _)  => begin
                      targets = BaseHashTable.hashTableValueList(ht)
                      targets2 = ListUtil.flatten(ListUtil.map(targets, Expression.extractCrefsFromExp))
                    targets2
                  end
                end
              end
          sources
        end

         #=  adds several replacements given by list of crefs and list of expressions by repeatedly calling addReplacement =#
        function addReplacementLst(inRepl::VariableReplacements, crs::List{<:DAE.ComponentRef}, dsts::List{<:DAE.Exp}) ::VariableReplacements
              local repl::VariableReplacements

              repl = begin
                  local cr::DAE.ComponentRef
                  local dst::DAE.Exp
                  local crrest::List{DAE.ComponentRef}
                  local dstrest::List{DAE.Exp}
                @match (inRepl, crs, dsts) begin
                  (repl,  nil(),  nil())  => begin
                    repl
                  end

                  (repl, cr <| crrest, dst <| dstrest)  => begin
                      repl = addReplacement(repl, cr, dst)
                      repl = addReplacementLst(repl, crrest, dstrest)
                    repl
                  end
                end
              end
          repl
        end

         #=
          Adds a replacement rule to the set of replacement rules given as argument.
          If a replacement rule a->b already exists and we add a new rule b->c then
          the rule a->b is updated to a->c. This is done using the make_transitive
          function.
         =#
        function addReplacement(repl::VariableReplacements, inSrc::DAE.ComponentRef, inDst::DAE.Exp) ::VariableReplacements
              local outRepl::VariableReplacements

              outRepl = begin
                  local src::DAE.ComponentRef
                  local src_1::DAE.ComponentRef
                  local dst::DAE.Exp
                  local dst_1::DAE.Exp
                  local ht::HashTable2.HashTable
                  local ht_1::HashTable2.HashTable
                  local invHt::HashTable3.HashTable
                  local invHt_1::HashTable3.HashTable
                   #=  PA: Commented out this, since it will only slow things down without adding any functionality.
                   =#
                   #=  Once match is available as a complement to matchcontinue, this case could be useful again.
                   =#
                   #= case ((repl as REPLACEMENTS(ht,invHt)),src,dst) /* source dest */
                   =#
                   #=  equation
                   =#
                   #=    olddst = BaseHashTable.get(src, ht) \"if rule a->b exists, fail\" ;
                   =#
                   #=  then
                   =#
                   #=    fail();
                   =#
                @matchcontinue (repl, inSrc, inDst) begin
                  (REPLACEMENTS(__), src, dst)  => begin
                      @match (REPLACEMENTS(ht, invHt), src_1, dst_1) = makeTransitive(repl, src, dst)
                      ht_1 = BaseHashTable.add((src_1, dst_1), ht)
                      invHt_1 = addReplacementInv(invHt, src_1, dst_1)
                    REPLACEMENTS(ht_1, invHt_1)
                  end

                  _  => begin
                        print("-add_replacement failed\\n")
                      fail()
                  end
                end
              end
               #= /*s1 = ComponentReference.printComponentRefStr(src);
                      s2 = ExpressionDump.printExpStr(dst);
                      s3 = ComponentReference.printComponentRefStr(src_1);
                      s4 = ExpressionDump.printExpStr(dst_1);
                      s = stringAppendList(
                        {\"add_replacement(\",s1,\", \",s2,\") -> add_replacement(\",s3,
                        \", \",s4,\")\\n\"});
                        print(s);
                      Debug.fprint(Flags.ADD_REPL, s);*/ =#
          outRepl
        end

         #= Similar to addReplacement but
        does not make transitive replacement rules.
         =#
        function addReplacementNoTransitive(repl::VariableReplacements, src::DAE.ComponentRef, dst::DAE.Exp) ::VariableReplacements
              local outRepl::VariableReplacements = repl

              local ht::HashTable2.HashTable
              local invHt::HashTable3.HashTable

              @match REPLACEMENTS(ht, invHt) = outRepl
              ht = BaseHashTable.add((src, dst), ht)
              invHt = addReplacementInv(invHt, src, dst)
              outRepl = REPLACEMENTS(ht, invHt)
          outRepl
        end

         #=
          Helper function to addReplacement
          Adds the inverse rule of a replacement to the second binary tree
          of VariableReplacements.
         =#
        function addReplacementInv(invHt::HashTable3.HashTable, src::DAE.ComponentRef, dst::DAE.Exp) ::HashTable3.HashTable
              local outInvHt::HashTable3.HashTable

              outInvHt = begin
                  local invHt_1::HashTable3.HashTable
                  local dests::List{DAE.ComponentRef}
                @match (invHt, src, dst) begin
                  (_, _, _)  => begin
                      dests = Expression.extractCrefsFromExp(dst)
                      invHt_1 = ListUtil.fold1r(dests, addReplacementInv2, src, invHt)
                    invHt_1
                  end
                end
              end
          outInvHt
        end

         #=
          Helper function to addReplacementInv
          Adds the inverse rule for one of the variables of a replacement to the second binary tree
          of VariableReplacements.
          Since a replacement is on the form var -> expression of vars(v1,v2,...,vn) the inverse binary tree
          contains rules for v1 -> var, v2 -> var, ...., vn -> var so that any of the variables of the expression
          will update the rule.
         =#
        function addReplacementInv2(invHt::HashTable3.HashTable, dst::DAE.ComponentRef, src::DAE.ComponentRef) ::HashTable3.HashTable
              local outInvHt::HashTable3.HashTable

              local srcs::List{DAE.ComponentRef}

              if BaseHashTable.hasKey(dst, invHt)
                srcs = BaseHashTable.get(dst, invHt)
                srcs = amortizeUnion(_cons(src, srcs))
                outInvHt = BaseHashTable.add((dst, srcs), invHt)
              else
                outInvHt = BaseHashTable.add((dst, list(src)), invHt)
              end
               #=  previous elt for dst -> src, append.
               =#
               #= List.union({},src::srcs);
               =#
               #=  No previous elt for dst -> src
               =#
          outInvHt
        end

         #= performs listUnion but in an 'amortized' way, by only doing it occasionally =#
        function amortizeUnion(inCrefs::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local crefs::List{DAE.ComponentRef}

              crefs = begin
                @match inCrefs begin
                  _ where (intMod(listLength(inCrefs), 7) == 0)  => begin
                    ListUtil.union(nil, inCrefs)
                  end

                  _  => begin
                      inCrefs
                  end
                end
              end
               #=  Experiments performed on different values: {{5, 102}, {6, 99}, {7, 98.8}, {8, 101}, {10, 101}, 20, 104}}
               =#
          crefs
        end

         #= Calls addReplacement() if condition (first argument) is false,
          otherwise does nothing.

          Author: asodja, 2010-03-03
         =#
        function addReplacementIfNot(condition::Bool, repl::VariableReplacements, inSrc::DAE.ComponentRef, inDst::DAE.Exp) ::VariableReplacements
              local outRepl::VariableReplacements

              outRepl = begin
                  local src::DAE.ComponentRef
                  local dst::DAE.Exp
                  local repl_1::VariableReplacements
                @match (condition, repl, inSrc, inDst) begin
                  (false, _, src, dst)  => begin
                      repl_1 = addReplacement(repl, src, dst)
                    repl_1
                  end

                  (true, _, _, _)  => begin
                    repl
                  end
                end
              end
               #= /* source dest */ =#
          outRepl
        end

         #=
          This function takes a set of replacement rules and a new replacement rule
          in the form of two ComponentRef:s and makes sure the new replacement rule
          is replaced with the transitive value.
          For example, if we have the rule a->b and a new rule c->a it is changed to c->b.
          Also, if we have a rule a->b and a new rule b->c then the -old- rule a->b is changed
          to a->c.
          For arbitrary expressions: if we have a rule ax-> expr(b1,..,bn) and a new rule c->expr(a1,ax,..,an)
          it is changed to c-> expr(a1,expr(b1,...,bn),..,an).
          And similary for a rule ax -> expr(b1,bx,..,bn) and a new rule bx->expr(c1,..,cn) then old rule is changed to
          ax -> expr(b1,expr(c1,..,cn),..,bn).
         =#
        function makeTransitive(repl::VariableReplacements, src::DAE.ComponentRef, dst::DAE.Exp) ::Tuple{VariableReplacements, DAE.ComponentRef, DAE.Exp}
              local outDst::DAE.Exp
              local outSrc::DAE.ComponentRef
              local outRepl::VariableReplacements

              (outRepl, outSrc, outDst) = begin
                  local repl_1::VariableReplacements
                  local repl_2::VariableReplacements
                  local src_1::DAE.ComponentRef
                  local src_2::DAE.ComponentRef
                  local dst_1::DAE.Exp
                  local dst_2::DAE.Exp
                  local dst_3::DAE.Exp
                @match (repl, src, dst) begin
                  (_, _, _)  => begin
                      (repl_1, src_1, dst_1) = makeTransitive1(repl, src, dst)
                      (repl_2, src_2, dst_2) = makeTransitive2(repl_1, src_1, dst_1)
                      (dst_3, _) = ExpressionSimplify.simplify1(dst_2) #= to remove e.g. --a =#
                    (repl_2, src_2, dst_3)
                  end
                end
              end
          (outRepl, outSrc, outDst)
        end

         #=
          helper function to makeTransitive
         =#
        function makeTransitive1(repl::VariableReplacements, src::DAE.ComponentRef, dst::DAE.Exp) ::Tuple{VariableReplacements, DAE.ComponentRef, DAE.Exp}
              local outDst::DAE.Exp
              local outSrc::DAE.ComponentRef
              local outRepl::VariableReplacements

              (outRepl, outSrc, outDst) = begin
                  local lst::List{DAE.ComponentRef}
                  local repl_1::VariableReplacements
                  local singleRepl::VariableReplacements
                  local ht::HashTable2.HashTable
                  local invHt::HashTable3.HashTable
                   #=  old rule a->expr(b1,..,bn) must be updated to a->expr(c_exp,...,bn) when new rule b1->c_exp
                   =#
                   #=  is introduced
                   =#
                @matchcontinue (repl, src, dst) begin
                  (REPLACEMENTS(_, invHt), _, _)  => begin
                      lst = BaseHashTable.get(src, invHt)
                      singleRepl = addReplacementNoTransitive(emptyReplacementsSized(53), src, dst)
                      repl_1 = makeTransitive12(lst, repl, singleRepl)
                    (repl_1, src, dst)
                  end

                  _  => begin
                      (repl, src, dst)
                  end
                end
              end
          (outRepl, outSrc, outDst)
        end

         #= Helper function to makeTransitive1
        For each old rule a->expr(b1,..,bn) update dest by applying the new rule passed as argument
        in singleRepl. =#
        function makeTransitive12(lst::List{<:DAE.ComponentRef}, repl::VariableReplacements, singleRepl::VariableReplacements #= contain one replacement rule: the rule to be added =#) ::VariableReplacements
              local outRepl::VariableReplacements

              outRepl = begin
                  local crDst::DAE.Exp
                  local cr::DAE.ComponentRef
                  local crs::List{DAE.ComponentRef}
                  local repl1::VariableReplacements
                  local repl2::VariableReplacements
                  local ht::HashTable2.HashTable
                @match (lst, repl, singleRepl) begin
                  ( nil(), _, _)  => begin
                    repl
                  end

                  (cr <| crs, REPLACEMENTS(hashTable = ht), _)  => begin
                      crDst = BaseHashTable.get(cr, ht)
                      (crDst, _) = replaceExp(crDst, singleRepl, NONE())
                      repl1 = addReplacementNoTransitive(repl, cr, crDst) #= add updated old rule =#
                      repl2 = makeTransitive12(crs, repl1, singleRepl)
                    repl2
                  end
                end
              end
          outRepl
        end

         #=
          Helper function to makeTransitive
         =#
        function makeTransitive2(repl::VariableReplacements, src::DAE.ComponentRef, dst::DAE.Exp) ::Tuple{VariableReplacements, DAE.ComponentRef, DAE.Exp}
              local outDst::DAE.Exp
              local outSrc::DAE.ComponentRef
              local outRepl::VariableReplacements

              (outRepl, outSrc, outDst) = begin
                  local dst_1::DAE.Exp
                   #=  for rule a->b1+..+bn, replace all b1 to bn's in the expression;
                   =#
                @matchcontinue (repl, src, dst) begin
                  (_, _, _)  => begin
                      (dst_1, _) = replaceExp(dst, repl, NONE())
                    (repl, src, dst_1)
                  end

                  _  => begin
                      (repl, src, dst)
                  end
                end
              end
               #=  replace Exp failed, keep old rule.
               =#
               #= /* dst has no own replacement, return */ =#
          (outRepl, outSrc, outDst)
        end

         #=
          Retrives a replacement variable given a set of replacement rules and a
          source variable.
         =#
        function getReplacement(inVariableReplacements::VariableReplacements, inComponentRef::DAE.ComponentRef) ::DAE.Exp
              local outComponentRef::DAE.Exp

              outComponentRef = begin
                  local src::DAE.ComponentRef
                  local dst::DAE.Exp
                  local ht::HashTable2.HashTable
                @match (inVariableReplacements, inComponentRef) begin
                  (REPLACEMENTS(hashTable = ht), src)  => begin
                      dst = BaseHashTable.get(src, ht)
                    dst
                  end
                end
              end
          outComponentRef
        end

         #= Similar to replaceExp but takes Option<Exp> instead of Exp =#
        function replaceExpOpt(inExp::Option{<:DAE.Exp}, repl::VariableReplacements, funcOpt::Option{<:FuncTypeExp_ExpToBoolean}) ::Option{DAE.Exp}
              local outExp::Option{DAE.Exp}

              outExp = begin
                  local e::DAE.Exp
                @match (inExp, repl, funcOpt) begin
                  (SOME(e), _, _)  => begin
                      (e, _) = replaceExp(e, repl, funcOpt)
                    SOME(e)
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
               #= /* TODO: Propagate this boolean? */ =#
          outExp
        end

         #=
        Author BZ 200X-XX modified 2008-06
        When adding replacement rules, we might not have the correct type availible at the moment.
        Then DAE.T_UNKNOWN_DEFAULT is used, so when replacing exp and finding DAE.T_UNKNOWN(_), we use the
        type of the expression to be replaced instead.
        TODO: find out why array residual functions containing arrays as xloc[] does not work,
              doing that will allow us to use this function for all crefs. =#
        function avoidDoubleHashLookup(inExp::DAE.Exp, inType::DAE.Type) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local cr::DAE.ComponentRef
                @matchcontinue (inExp, inType) begin
                  (DAE.CREF(cr, DAE.T_UNKNOWN(__)), _)  => begin
                    Expression.makeCrefExp(cr, inType)
                  end

                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

         #= similar to replaceExp but repeats the replacements until expression no longer changes.
        Note: This is only required/useful if replacements are built with addReplacementNoTransitive. =#
        function replaceExpRepeated(e::DAE.Exp, repl::VariableReplacements, func::Option{<:VisitFunc}, maxIter::ModelicaInteger #= max iterations =#) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = replaceExpRepeated2(e, repl, func, maxIter, 1, false)
          outExp
        end

         #= help function to replaceExpRepeated =#
        function replaceExpRepeated2(e::DAE.Exp, repl::VariableReplacements, func::Option{<:VisitFunc}, maxIter::ModelicaInteger, i::ModelicaInteger, equal::Bool) ::DAE.Exp
              local outExp::DAE.Exp

              outExp = begin
                  local e1::DAE.Exp
                  local res::DAE.Exp
                  local b::Bool
                @matchcontinue (e, repl, func, maxIter, i, equal) begin
                  (_, _, _, _, _, _)  => begin
                      @match true = i > maxIter
                    e
                  end

                  (_, _, _, _, _, true)  => begin
                    e
                  end

                  _  => begin
                        (e1, b) = replaceExp(e, repl, func)
                        res = replaceExpRepeated2(e1, repl, func, maxIter, i + 1, ! b)
                      res
                  end
                end
              end
               #= /*Expression.expEqual(e,e1)*/ =#
          outExp
        end

         #=
          Takes a set of replacement rules and an expression and a function
          giving a boolean value for an expression.
          The function replaces all variables in the expression using
          the replacement rules, if the boolean value is true children of the
          expression is visited (including the expression itself). If it is false,
          no replacemet is performed. =#
        function replaceExp(inExp::DAE.Exp, inVariableReplacements::VariableReplacements, inFuncTypeExpExpToBooleanOption::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{DAE.Exp, Bool}
              local replacementPerformed::Bool
              local outExp::DAE.Exp

              (outExp, replacementPerformed) = begin
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local e1_1::DAE.Exp
                  local e2_1::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3_1::DAE.Exp
                  local e3::DAE.Exp
                  local t::DAE.Type
                  local tp::DAE.Type
                  local ety::DAE.Type
                  local repl::VariableReplacements
                  local cond::Option{FuncTypeExp_ExpToBoolean}
                  local op::DAE.Operator
                  local expl_1::List{DAE.Exp}
                  local expl::List{DAE.Exp}
                  local path::Absyn.Path
                  local c::Bool
                  local c1::Bool
                  local c2::Bool
                  local c3::Bool
                  local b::ModelicaInteger
                  local a::Absyn.CodeNode
                  local bexpl_1::List{List{DAE.Exp}}
                  local bexpl::List{List{DAE.Exp}}
                  local index_::ModelicaInteger
                  local isExpisASUB::Option{Tuple{DAE.Exp, ModelicaInteger, ModelicaInteger}}
                  local reductionInfo::DAE.ReductionInfo
                  local iters::DAE.ReductionIterators
                  local attr::DAE.CallAttributes
                   #=  Note: Most of these functions check if a subexpression did a replacement.
                   =#
                   #=  If it did not, we do not create a new copy of the expression (to save some memory).
                   =#
                @matchcontinue (inExp, inVariableReplacements, inFuncTypeExpExpToBooleanOption) begin
                  (DAE.CREF(componentRef = cr, ty = t), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      e1 = getReplacement(repl, cr)
                      e2 = avoidDoubleHashLookup(e1, t)
                    (e2, true)
                  end

                  (DAE.BINARY(exp1 = e1, operator = op, exp2 = e2), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      @match true = c1 || c2
                    (DAE.BINARY(e1_1, op, e2_1), true)
                  end

                  (DAE.LBINARY(exp1 = e1, operator = op, exp2 = e2), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      @match true = c1 || c2
                    (DAE.LBINARY(e1_1, op, e2_1), true)
                  end

                  (DAE.UNARY(operator = op, exp = e1), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (e1_1, true) = replaceExp(e1, repl, cond)
                    (DAE.UNARY(op, e1_1), true)
                  end

                  (DAE.LUNARY(operator = op, exp = e1), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (e1_1, true) = replaceExp(e1, repl, cond)
                    (DAE.LUNARY(op, e1_1), true)
                  end

                  (DAE.RELATION(exp1 = e1, operator = op, exp2 = e2, index = index_, optionExpisASUB = isExpisASUB), repl, cond)  => begin
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      @match true = c1 || c2
                    (DAE.RELATION(e1_1, op, e2_1, index_, isExpisASUB), true)
                  end

                  (DAE.IFEXP(expCond = e1, expThen = e2, expElse = e3), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      (e3_1, c3) = replaceExp(e3, repl, cond)
                      @match true = c1 || c2 || c3
                    (DAE.IFEXP(e1_1, e2_1, e3_1), true)
                  end

                  (DAE.CALL(path = path && Absyn.IDENT("pre"), expLst = e && DAE.CREF(__) <|  nil(), attr = attr), repl, cond)  => begin
                      @match true = replaceExpCond(cond, e)
                      @match (DAE.UNARY(DAE.UMINUS(ety), e_1), true) = replaceExp(e, repl, cond)
                    (DAE.UNARY(DAE.UMINUS(ety), DAE.CALL(path, list(e_1), attr)), true)
                  end

                  (e && DAE.CALL(path = path, expLst = expl, attr = attr), repl, cond)  => begin
                      @match true = replaceExpCond(cond, e)
                      @match (expl_1, true) = replaceExpList(expl, repl, cond)
                    (DAE.CALL(path, expl_1, attr), true)
                  end

                  (DAE.ARRAY(ty = tp, scalar = c, array = expl), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (expl_1, true) = replaceExpList(expl, repl, cond)
                    (DAE.ARRAY(tp, c, expl_1), true)
                  end

                  (DAE.MATRIX(ty = t, integer = b, matrix = bexpl), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (bexpl_1, true) = replaceExpMatrix(bexpl, repl, cond)
                    (DAE.MATRIX(t, b, bexpl_1), true)
                  end

                  (DAE.RANGE(ty = tp, start = e1, step = NONE(), stop = e2), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      @match true = c1 || c2
                    (DAE.RANGE(tp, e1_1, NONE(), e2_1), true)
                  end

                  (DAE.RANGE(ty = tp, start = e1, step = SOME(e3), stop = e2), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      (e3_1, c3) = replaceExp(e3, repl, cond)
                      @match true = c1 || c2 || c3
                    (DAE.RANGE(tp, e1_1, SOME(e3_1), e2_1), true)
                  end

                  (DAE.TUPLE(PR = expl), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (expl_1, true) = replaceExpList(expl, repl, cond)
                    (DAE.TUPLE(expl_1), true)
                  end

                  (DAE.CAST(ty = tp, exp = e1), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (e1_1, true) = replaceExp(e1, repl, cond)
                    (DAE.CAST(tp, e1_1), true)
                  end

                  (DAE.ASUB(exp = e1, sub = expl), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (expl_1, c2) = replaceExpList(expl, repl, cond)
                      @match true = c1 || c2
                    (Expression.makeASUB(e1_1, expl_1), true)
                  end

                  (DAE.SIZE(exp = e1, sz = NONE()), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      @match (e1_1, true) = replaceExp(e1, repl, cond)
                    (DAE.SIZE(e1_1, NONE()), true)
                  end

                  (DAE.SIZE(exp = e1, sz = SOME(e2)), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, c1) = replaceExp(e1, repl, cond)
                      (e2_1, c2) = replaceExp(e2, repl, cond)
                      @match true = c1 || c2
                    (DAE.SIZE(e1_1, SOME(e2_1)), true)
                  end

                  (DAE.CODE(code = a, ty = tp), _, _)  => begin
                      print("replace_exp on CODE not impl.\\n")
                    (DAE.CODE(a, tp), false)
                  end

                  (DAE.REDUCTION(reductionInfo = reductionInfo, expr = e1, iterators = iters), repl, cond)  => begin
                      @match true = replaceExpCond(cond, inExp)
                      (e1_1, _) = replaceExp(e1, repl, cond)
                      @match (iters, true) = replaceExpIters(iters, repl, cond)
                    (DAE.REDUCTION(reductionInfo, e1_1, iters), true)
                  end

                  (e, _, _)  => begin
                    (e, false)
                  end
                end
              end
               #= /* Special case when a variable in pre() is an alias for unary minus of another */ =#
          (outExp, replacementPerformed)
        end

        function replaceExpList(iexpl::List{<:DAE.Exp}, repl::VariableReplacements, cond::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{List{DAE.Exp}, Bool}
              local replacementPerformed::Bool
              local outExpl::List{DAE.Exp}

              local acc1::List{DAE.Exp} = nil
              local acc2::Bool = false
              local c::Bool

              for exp in iexpl
                (exp, c) = replaceExp(exp, repl, cond)
                acc2 = acc2 || c
                acc1 = _cons(exp, acc1)
              end
              outExpl = listReverseInPlace(acc1)
              replacementPerformed = acc2
          (outExpl, replacementPerformed)
        end

        function replaceExpIters(inIters::List{<:DAE.ReductionIterator}, repl::VariableReplacements, cond::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{List{DAE.ReductionIterator}, Bool}
              local replacementPerformed::Bool
              local outIter::List{DAE.ReductionIterator}

              local acc1::List{DAE.ReductionIterator} = nil
              local acc2::Bool = false

              for iter in inIters
                _ = begin
                    local id::String
                    local exp::DAE.Exp
                    local gexp::DAE.Exp
                    local ty::DAE.Type
                    local b1::Bool
                    local b2::Bool
                  @match iter begin
                    DAE.REDUCTIONITER(id, exp, NONE(), ty)  => begin
                        (exp, b1) = replaceExp(exp, repl, cond)
                        if b1
                          acc1 = _cons(DAE.REDUCTIONITER(id, exp, NONE(), ty), acc1)
                          acc2 = true
                        else
                          acc1 = _cons(iter, acc1)
                        end
                      ()
                    end

                    DAE.REDUCTIONITER(id, exp, SOME(gexp), ty)  => begin
                        (exp, b1) = replaceExp(exp, repl, cond)
                        (gexp, b2) = replaceExp(gexp, repl, cond)
                        if b1 || b2
                          acc1 = _cons(DAE.REDUCTIONITER(id, exp, SOME(gexp), ty), acc1)
                          acc2 = true
                        else
                          acc1 = _cons(iter, acc1)
                        end
                      ()
                    end

                    _  => begin
                          acc1 = _cons(iter, acc1)
                        ()
                    end
                  end
                end
              end
              outIter = listReverseInPlace(acc1)
              replacementPerformed = acc2
          (outIter, replacementPerformed)
        end

         #= function replaceExpCond(cond,e) => true &

          Helper function to replace_Expression. Evaluates a condition function if
          SOME otherwise returns true.
         =#
        function replaceExpCond(inFuncTypeExpExpToBooleanOption::Option{<:FuncTypeExp_ExpToBoolean}, inExp::DAE.Exp) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local res::Bool
                  local cond::FuncTypeExp_ExpToBoolean
                  local e::DAE.Exp
                @match (inFuncTypeExpExpToBooleanOption, inExp) begin
                  (SOME(cond), e)  => begin
                      res = cond(e)
                    res
                  end

                  _  => begin
                      true
                  end
                end
              end
               #= /* cond e */ =#
          outBoolean
        end

         #= author: PA
          Helper function to replaceExp, traverses Matrix expression list. =#
        function replaceExpMatrix(inTplExpExpBooleanLstLst::List{<:List{<:DAE.Exp}}, inVariableReplacements::VariableReplacements, inFuncTypeExpExpToBooleanOption::Option{<:FuncTypeExp_ExpToBoolean}) ::Tuple{List{List{DAE.Exp}}, Bool}
              local replacementPerformed::Bool
              local outTplExpExpBooleanLstLst::List{List{DAE.Exp}}

              local acc1::List{List{DAE.Exp}} = nil
              local acc2::Bool = false
              local c::Bool

              for exp in inTplExpExpBooleanLstLst
                (exp, c) = replaceExpList(exp, inVariableReplacements, inFuncTypeExpExpToBooleanOption)
                acc2 = acc2 || c
                acc1 = _cons(exp, acc1)
              end
              outTplExpExpBooleanLstLst = listReverseInPlace(acc1)
              replacementPerformed = acc2
          (outTplExpExpBooleanLstLst, replacementPerformed)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

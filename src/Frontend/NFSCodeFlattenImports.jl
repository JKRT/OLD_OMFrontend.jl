  module NFSCodeFlattenImports 


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

        import NFSCodeEnv

        Env = NFSCodeEnv.Env 

        import Debug

        import Error

        import Flags

        import ListUtil

        import NFSCodeLookup

        import System
        import SCodeUtil

        Item = NFSCodeEnv.Item 

        Extends = NFSCodeEnv.Extends 

        FrameType = NFSCodeEnv.FrameType 

        Import = Absyn.Import 

        function flattenProgram(inProgram::SCode.Program, inEnv::Env) ::Tuple{SCode.Program, Env} 
              local outEnv::Env
              local outProgram::SCode.Program

              (outProgram, outEnv) = ListUtil.mapFold(inProgram, flattenClass, inEnv)
          (outProgram, outEnv)
        end

        function flattenClass(inClass::SCode.Element, inEnv::Env) ::Tuple{SCode.Element, Env} 
              local outEnv::Env
              local outClass::SCode.Element

              (outClass, outEnv) = begin
                  local name::SCode.Ident
                  local cdef::SCode.ClassDef
                  local info::SourceInfo
                  local item::Item
                  local env::Env
                  local cls_env::NFSCodeEnv.Frame
                  local cls::SCode.Element
                  local cls_ty::NFSCodeEnv.ClassType
                @matchcontinue (inClass, inEnv) begin
                  (SCode.CLASS(name = name, classDef = cdef, info = info), _)  => begin
                      @match (NFSCodeEnv.CLASS(env = list(cls_env), classType = cls_ty), _) = NFSCodeLookup.lookupInClass(name, inEnv)
                      env = NFSCodeEnv.enterFrame(cls_env, inEnv)
                      (cdef, _cons(cls_env, env)) = flattenClassDef(cdef, env, info)
                      cls = SCodeUtil.setElementClassDefinition(cdef, inClass)
                      item = NFSCodeEnv.newClassItem(cls, list(cls_env), cls_ty)
                      env = NFSCodeEnv.updateItemInEnv(item, env, name)
                    (cls, env)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- NFSCodeFlattenImports.flattenClass failed on " + SCodeUtil.elementName(inClass) + " in " + NFSCodeEnv.getEnvName(inEnv))
                      fail()
                  end
                end
              end
          (outClass, outEnv)
        end

        function flattenClassDef(inClassDef::SCode.ClassDef, inEnv::Env, inInfo::SourceInfo) ::Tuple{SCode.ClassDef, Env} 
              local outEnv::Env
              local outClassDef::SCode.ClassDef

              (outClassDef, outEnv) = begin
                  local el::List{SCode.Element}
                  local neql::List{SCode.Equation}
                  local ieql::List{SCode.Equation}
                  local nal::List{SCode.AlgorithmSection}
                  local ial::List{SCode.AlgorithmSection}
                  local nco::List{SCode.ConstraintSection}
                  local clats::List{Absyn.NamedArg}
                   #= class attributes
                   =#
                  local extdecl::Option{SCode.ExternalDecl}
                  local annl::List{SCode.Annotation}
                  local cmt::Option{SCode.Comment}
                  local ty::Absyn.TypeSpec
                  local mods::SCode.Mod
                  local attr::SCode.Attributes
                  local env::Env
                  local cdef::SCode.ClassDef
                @match (inClassDef, inEnv, inInfo) begin
                  (SCode.PARTS(el, neql, ieql, nal, ial, nco, clats, extdecl), _, _)  => begin
                      el = ListUtil.filterOnTrue(el, isNotImport)
                      (el, env) = ListUtil.mapFold(el, flattenElement, inEnv)
                      neql = ListUtil.map1(neql, flattenEquation, env)
                      ieql = ListUtil.map1(ieql, flattenEquation, env)
                      nal = ListUtil.map1(nal, flattenAlgorithm, env)
                      ial = ListUtil.map1(ial, flattenAlgorithm, env)
                      nco = ListUtil.map2(nco, flattenConstraints, env, inInfo)
                    (SCode.PARTS(el, neql, ieql, nal, ial, nco, clats, extdecl), env)
                  end
                  
                  (SCode.CLASS_EXTENDS(mods, cdef), _, _)  => begin
                      (cdef, env) = flattenClassDef(cdef, inEnv, inInfo)
                      mods = flattenModifier(mods, env, inInfo)
                    (SCode.CLASS_EXTENDS(mods, cdef), env)
                  end
                  
                  (SCode.DERIVED(ty, mods, attr), env, _)  => begin
                      mods = flattenModifier(mods, env, inInfo)
                      env = NFSCodeEnv.removeExtendsFromLocalScope(env)
                      ty = flattenTypeSpec(ty, env, inInfo)
                    (SCode.DERIVED(ty, mods, attr), inEnv)
                  end
                  
                  _  => begin
                      (inClassDef, inEnv)
                  end
                end
              end
               #=  Lookup elements.
               =#
               #=  Lookup equations and algorithm names.
               =#
               #=  Remove the extends from the local scope before flattening the derived
               =#
               #=  type, because the type should not be looked up via itself.
               =#
          (outClassDef, outEnv)
        end

        function flattenDerivedClassDef(inClassDef::SCode.ClassDef, inEnv::Env, inInfo::SourceInfo) ::SCode.ClassDef 
              local outClassDef::SCode.ClassDef

              local ty::Absyn.TypeSpec
              local mods::SCode.Mod
              local attr::SCode.Attributes

              @match SCode.DERIVED(ty, mods, attr) = inClassDef
              ty = flattenTypeSpec(ty, inEnv, inInfo)
              mods = flattenModifier(mods, inEnv, inInfo)
              outClassDef = SCode.DERIVED(ty, mods, attr)
          outClassDef
        end

        function isNotImport(inElement::SCode.Element) ::Bool 
              local outB::Bool

              outB = begin
                @match inElement begin
                  SCode.IMPORT(__)  => begin
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          outB
        end

        function flattenElement(inElement::SCode.Element, inEnv::Env) ::Tuple{SCode.Element, Env} 
              local outEnv::Env
              local outElement::SCode.Element

              (outElement, outEnv) = begin
                  local env::Env
                  local elem::SCode.Element
                  local name::String
                  local item::Item
                   #=  Lookup component types, modifications and conditions.
                   =#
                @match (inElement, inEnv) begin
                  (SCode.COMPONENT(name = name), _)  => begin
                      elem = flattenComponent(inElement, inEnv)
                      item = NFSCodeEnv.newVarItem(elem, true)
                      env = NFSCodeEnv.updateItemInEnv(item, inEnv, name)
                    (elem, env)
                  end
                  
                  (SCode.CLASS(__), _)  => begin
                      (elem, env) = flattenClass(inElement, inEnv)
                    (elem, env)
                  end
                  
                  (SCode.EXTENDS(__), _)  => begin
                    (flattenExtends(inElement, inEnv), inEnv)
                  end
                  
                  _  => begin
                      (inElement, inEnv)
                  end
                end
              end
               #=  Lookup class definitions.
               =#
               #=  Lookup base class and modifications in extends clauses.
               =#
          (outElement, outEnv)
        end

        function flattenComponent(inComponent::SCode.Element, inEnv::Env) ::SCode.Element 
              local outComponent::SCode.Element

              local name::SCode.Ident
              local io::Absyn.InnerOuter
              local prefixes::SCode.Prefixes
              local attr::SCode.Attributes
              local type_spec::Absyn.TypeSpec
              local mod::SCode.Mod
              local cmt::SCode.Comment
              local cond::Option{Absyn.Exp}
              local cc::Option{Absyn.ConstrainClass}
              local info::SourceInfo

              @match SCode.COMPONENT(name, prefixes, attr, type_spec, mod, cmt, cond, info) = inComponent
              attr = flattenAttributes(attr, inEnv, info)
              type_spec = flattenTypeSpec(type_spec, inEnv, info)
              mod = flattenModifier(mod, inEnv, info)
              cond = flattenOptExp(cond, inEnv, info)
              outComponent = SCode.COMPONENT(name, prefixes, attr, type_spec, mod, cmt, cond, info)
          outComponent
        end

        function flattenAttributes(inAttributes::SCode.Attributes, inEnv::Env, inInfo::SourceInfo) ::SCode.Attributes 
              local outAttributes::SCode.Attributes

              local ad::Absyn.ArrayDim
              local ct::SCode.ConnectorType
              local prl::SCode.Parallelism
              local var::SCode.Variability
              local dir::Absyn.Direction
              local isf::Absyn.IsField

              @match SCode.ATTR(ad, ct, prl, var, dir, isf) = inAttributes
              ad = ListUtil.map2(ad, flattenSubscript, inEnv, inInfo)
              outAttributes = SCode.ATTR(ad, ct, prl, var, dir, isf)
          outAttributes
        end

        function flattenTypeSpec(inTypeSpec::Absyn.TypeSpec, inEnv::Env, inInfo::SourceInfo) ::Absyn.TypeSpec 
              local outTypeSpec::Absyn.TypeSpec

              outTypeSpec = begin
                  local path::Absyn.Path
                  local ad::Option{Absyn.ArrayDim}
                  local tys::List{Absyn.TypeSpec}
                   #=  A normal type.
                   =#
                @match (inTypeSpec, inEnv, inInfo) begin
                  (Absyn.TPATH(path = path, arrayDim = ad), _, _)  => begin
                      (_, path, _) = NFSCodeLookup.lookupClassName(path, inEnv, inInfo)
                    Absyn.TPATH(path, ad)
                  end
                  
                  (Absyn.TCOMPLEX(path = Absyn.IDENT("polymorphic")), _, _)  => begin
                    inTypeSpec
                  end
                  
                  (Absyn.TCOMPLEX(path = path, typeSpecs = tys, arrayDim = ad), _, _)  => begin
                      tys = ListUtil.map2(tys, flattenTypeSpec, inEnv, inInfo)
                    Absyn.TCOMPLEX(path, tys, ad)
                  end
                end
              end
               #=  A polymorphic type, i.e. replaceable type Type subtypeof Any.
               =#
               #=  A MetaModelica type such as list or tuple.
               =#
          outTypeSpec
        end

        function flattenExtends(inExtends::SCode.Element, inEnv::Env) ::SCode.Element 
              local outExtends::SCode.Element

              local path::Absyn.Path
              local mod::SCode.Mod
              local ann::Option{SCode.Annotation}
              local info::SourceInfo
              local env::Env
              local vis::SCode.Visibility

              @match SCode.EXTENDS(path, vis, mod, ann, info) = inExtends
              env = NFSCodeEnv.removeExtendsFromLocalScope(inEnv)
              (_, path, _) = NFSCodeLookup.lookupBaseClassName(path, env, info)
              mod = flattenModifier(mod, inEnv, info)
              outExtends = SCode.EXTENDS(path, vis, mod, ann, info)
          outExtends
        end

        function flattenEquation(inEquation::SCode.Equation, inEnv::Env) ::SCode.Equation 
              local outEquation::SCode.Equation

              local equ::SCode.EEquation

              @match SCode.EQUATION(equ) = inEquation
              (equ, _) = SCodeUtil.traverseEEquations(equ, (flattenEEquationTraverser, inEnv))
              outEquation = SCode.EQUATION(equ)
          outEquation
        end

        function flattenEEquationTraverser(inTuple::Tuple{<:SCode.EEquation, Env}) ::Tuple{SCode.EEquation, Env} 
              local outTuple::Tuple{SCode.EEquation, Env}

              outTuple = begin
                  local equ::SCode.EEquation
                  local iter_name::SCode.Ident
                  local env::Env
                  local info::SourceInfo
                  local cref::Absyn.ComponentRef
                  local cmt::SCode.Comment
                  local crefExp::Absyn.Exp
                  local exp::Absyn.Exp
                @match inTuple begin
                  (equ && SCode.EQ_FOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                  
                  (SCode.EQ_REINIT(cref = crefExp && Absyn.CREF(componentRef = cref), expReinit = exp, comment = cmt, info = info), env)  => begin
                      cref = NFSCodeLookup.lookupComponentRef(cref, env, info)
                      equ = SCode.EQ_REINIT(crefExp, exp, cmt, info)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                  
                  (equ, env)  => begin
                      info = SCodeUtil.getEEquationInfo(equ)
                      (equ, _) = SCodeUtil.traverseEEquationExps(equ, traverseExp, (env, info))
                    (equ, env)
                  end
                end
              end
          outTuple
        end

        function traverseExp(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              (outExp, outTuple) = AbsynUtil.traverseExpBidir(inExp, flattenExpTraverserEnter, flattenExpTraverserExit, inTuple)
          (outExp, outTuple)
        end

        function flattenConstraints(inConstraints::SCode.ConstraintSection, inEnv::Env, inInfo::SourceInfo) ::SCode.ConstraintSection 
              local outConstraints::SCode.ConstraintSection

              local exps::List{Absyn.Exp}

              @match SCode.CONSTRAINTS(exps) = inConstraints
              exps = ListUtil.map2(exps, flattenExp, inEnv, inInfo)
              outConstraints = SCode.CONSTRAINTS(exps)
          outConstraints
        end

        function flattenAlgorithm(inAlgorithm::SCode.AlgorithmSection, inEnv::Env) ::SCode.AlgorithmSection 
              local outAlgorithm::SCode.AlgorithmSection

              local statements::List{SCode.Statement}

              @match SCode.ALGORITHM(statements) = inAlgorithm
              statements = ListUtil.map1(statements, flattenStatement, inEnv)
              outAlgorithm = SCode.ALGORITHM(statements)
          outAlgorithm
        end

        function flattenStatement(inStatement::SCode.Statement, inEnv::Env) ::SCode.Statement 
              local outStatement::SCode.Statement

              (outStatement, _) = SCodeUtil.traverseStatements(inStatement, (flattenStatementTraverser, inEnv))
          outStatement
        end

        function flattenStatementTraverser(inTuple::Tuple{<:SCode.Statement, Env}) ::Tuple{SCode.Statement, Env} 
              local outTuple::Tuple{SCode.Statement, Env}

              outTuple = begin
                  local env::Env
                  local iter_name::String
                  local stmt::SCode.Statement
                  local info::SourceInfo
                @match inTuple begin
                  (stmt && SCode.ALG_FOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (stmt, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                  
                  (stmt && SCode.ALG_PARFOR(index = iter_name, info = info), env)  => begin
                      env = NFSCodeEnv.extendEnvWithIterators(list(Absyn.ITERATOR(iter_name, NONE(), NONE())), System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      (stmt, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                  
                  (stmt, env)  => begin
                      info = SCodeUtil.getStatementInfo(stmt)
                      (stmt, _) = SCodeUtil.traverseStatementExps(stmt, traverseExp, (env, info))
                    (stmt, env)
                  end
                end
              end
          outTuple
        end

        function flattenModifier(inMod::SCode.Mod, inEnv::Env, inInfo::SourceInfo) ::SCode.Mod 
              local outMod::SCode.Mod

              outMod = begin
                  local fp::SCode.Final
                  local ep::SCode.Each
                  local sub_mods::List{SCode.SubMod}
                  local opt_exp::Option{Absyn.Exp}
                  local el::SCode.Element
                  local info::SourceInfo
                @match (inMod, inEnv, inInfo) begin
                  (SCode.MOD(fp, ep, sub_mods, opt_exp, info), _, _)  => begin
                      opt_exp = flattenModOptExp(opt_exp, inEnv, inInfo)
                      sub_mods = ListUtil.map2(sub_mods, flattenSubMod, inEnv, inInfo)
                    SCode.MOD(fp, ep, sub_mods, opt_exp, info)
                  end
                  
                  (SCode.REDECL(fp, ep, el), _, _)  => begin
                      el = flattenRedeclare(el, inEnv)
                    SCode.REDECL(fp, ep, el)
                  end
                  
                  (SCode.NOMOD(__), _, _)  => begin
                    inMod
                  end
                end
              end
          outMod
        end

        function flattenModOptExp(inOptExp::Option{<:Absyn.Exp}, inEnv::Env, inInfo::SourceInfo) ::Option{Absyn.Exp} 
              local outOptExp::Option{Absyn.Exp}

              outOptExp = begin
                  local exp::Absyn.Exp
                @match inOptExp begin
                  SOME(exp)  => begin
                      exp = flattenExp(exp, inEnv, inInfo)
                    SOME(exp)
                  end
                  
                  _  => begin
                      inOptExp
                  end
                end
              end
          outOptExp
        end

        function flattenSubMod(inSubMod::SCode.SubMod, inEnv::Env, inInfo::SourceInfo) ::SCode.SubMod 
              local outSubMod::SCode.SubMod

              outSubMod = begin
                  local ident::SCode.Ident
                  local subs::List{SCode.Subscript}
                  local mod::SCode.Mod
                @match (inSubMod, inEnv, inInfo) begin
                  (SCode.NAMEMOD(ident = ident, mod = mod), _, _)  => begin
                      mod = flattenModifier(mod, inEnv, inInfo)
                    SCode.NAMEMOD(ident, mod)
                  end
                end
              end
          outSubMod
        end

        function flattenRedeclare(inElement::SCode.Element, inEnv::Env) ::SCode.Element 
              local outElement::SCode.Element

              outElement = begin
                  local name::SCode.Ident
                  local prefixes::SCode.Prefixes
                  local pp::SCode.Partial
                  local ep::SCode.Encapsulated
                  local res::SCode.Restriction
                  local info::SourceInfo
                  local element::SCode.Element
                  local cdef::SCode.ClassDef
                  local cdef2::SCode.ClassDef
                  local cmt::SCode.Comment
                @match (inElement, inEnv) begin
                  (SCode.CLASS(name, prefixes, ep, pp, res, cdef && SCode.DERIVED(__), cmt, info), _)  => begin
                      cdef2 = flattenDerivedClassDef(cdef, inEnv, info)
                    SCode.CLASS(name, prefixes, ep, pp, res, cdef2, cmt, info)
                  end
                  
                  (SCode.CLASS(classDef = SCode.ENUMERATION(__)), _)  => begin
                    inElement
                  end
                  
                  (SCode.COMPONENT(__), _)  => begin
                      element = flattenComponent(inElement, inEnv)
                    element
                  end
                  
                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Unknown redeclare in NFSCodeFlattenImports.flattenRedeclare"))
                      fail()
                  end
                end
              end
          outElement
        end

        function flattenSubscript(inSub::SCode.Subscript, inEnv::Env, inInfo::SourceInfo) ::SCode.Subscript 
              local outSub::SCode.Subscript

              outSub = begin
                  local exp::Absyn.Exp
                @match (inSub, inEnv, inInfo) begin
                  (Absyn.SUBSCRIPT(subscript = exp), _, _)  => begin
                      exp = flattenExp(exp, inEnv, inInfo)
                    Absyn.SUBSCRIPT(exp)
                  end
                  
                  (Absyn.NOSUB(__), _, _)  => begin
                    inSub
                  end
                end
              end
          outSub
        end

        function flattenExp(inExp::Absyn.Exp, inEnv::Env, inInfo::SourceInfo) ::Absyn.Exp 
              local outExp::Absyn.Exp

              (outExp, _) = AbsynUtil.traverseExpBidir(inExp, flattenExpTraverserEnter, flattenExpTraverserExit, (inEnv, inInfo))
          outExp
        end

        function flattenOptExp(inExp::Option{<:Absyn.Exp}, inEnv::Env, inInfo::SourceInfo) ::Option{Absyn.Exp} 
              local outExp::Option{Absyn.Exp}

              outExp = begin
                  local exp::Absyn.Exp
                @match (inExp, inEnv, inInfo) begin
                  (SOME(exp), _, _)  => begin
                      exp = flattenExp(exp, inEnv, inInfo)
                    SOME(exp)
                  end
                  
                  _  => begin
                      inExp
                  end
                end
              end
          outExp
        end

        function flattenExpTraverserEnter(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              (outExp, outTuple) = begin
                  local env::Env
                  local cref::Absyn.ComponentRef
                  local args::Absyn.FunctionArgs
                  local exp::Absyn.Exp
                  local iters::Absyn.ForIterators
                  local info::SourceInfo
                  local tup::Tuple{Env, SourceInfo}
                  local iterType::Absyn.ReductionIterType
                @match (inExp, inTuple) begin
                  (Absyn.CREF(componentRef = cref), tup && (env, info))  => begin
                      cref = NFSCodeLookup.lookupComponentRef(cref, env, info)
                    (Absyn.CREF(cref), tup)
                  end
                  
                  (Absyn.CALL(function_ = cref, functionArgs = Absyn.FOR_ITER_FARG(exp = exp, iterType = iterType, iterators = iters)), (env, info))  => begin
                      cref = NFSCodeLookup.lookupComponentRef(cref, env, info)
                      env = NFSCodeEnv.extendEnvWithIterators(iters, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                      exp = flattenExp(exp, env, info)
                    (Absyn.CALL(cref, Absyn.FOR_ITER_FARG(exp, iterType, iters)), (env, info))
                  end
                  
                  (Absyn.CALL(function_ = Absyn.CREF_IDENT(name = "SOME")), _)  => begin
                    (inExp, inTuple)
                  end
                  
                  (Absyn.CALL(function_ = cref, functionArgs = args), tup && (env, info))  => begin
                      cref = NFSCodeLookup.lookupComponentRef(cref, env, info)
                    (Absyn.CALL(cref, args), tup)
                  end
                  
                  (Absyn.PARTEVALFUNCTION(function_ = cref, functionArgs = args), tup && (env, info))  => begin
                      cref = NFSCodeLookup.lookupComponentRef(cref, env, info)
                    (Absyn.PARTEVALFUNCTION(cref, args), tup)
                  end
                  
                  (exp && Absyn.MATCHEXP(__), (env, info))  => begin
                      env = NFSCodeEnv.extendEnvWithMatch(exp, System.tmpTickIndex(NFSCodeEnv.tmpTickIndex), env)
                    (exp, (env, info))
                  end
                  
                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
               #=  TODO: handle function arguments
               =#
               #=  TODO: handle function arguments
               =#
          (outExp, outTuple)
        end

        function flattenExpTraverserExit(inExp::Absyn.Exp, inTuple::Tuple{<:Env, SourceInfo}) ::Tuple{Absyn.Exp, Tuple{Env, SourceInfo}} 
              local outTuple::Tuple{Env, SourceInfo}
              local outExp::Absyn.Exp

              (outExp, outTuple) = begin
                  local e::Absyn.Exp
                  local env::Env
                  local info::SourceInfo
                @match (inExp, inTuple) begin
                  (Absyn.CALL(functionArgs = Absyn.FOR_ITER_FARG(__)), (NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)) <| env, info))  => begin
                    (inExp, (env, info))
                  end
                  
                  (Absyn.MATCHEXP(__), (NFSCodeEnv.FRAME(frameType = NFSCodeEnv.IMPLICIT_SCOPE(__)) <| env, info))  => begin
                    (inExp, (env, info))
                  end
                  
                  _  => begin
                      (inExp, inTuple)
                  end
                end
              end
          (outExp, outTuple)
        end

        function flattenComponentRefSubs(inCref::Absyn.ComponentRef, inEnv::Env, inInfo::SourceInfo) ::Absyn.ComponentRef 
              local outCref::Absyn.ComponentRef

              outCref = begin
                  local name::Absyn.Ident
                  local cref::Absyn.ComponentRef
                  local subs::List{Absyn.Subscript}
                @match (inCref, inEnv, inInfo) begin
                  (Absyn.CREF_IDENT(name, subs), _, _)  => begin
                      subs = ListUtil.map2(subs, flattenSubscript, inEnv, inInfo)
                    Absyn.CREF_IDENT(name, subs)
                  end
                  
                  (Absyn.CREF_QUAL(name, subs, cref), _, _)  => begin
                      subs = ListUtil.map2(subs, flattenSubscript, inEnv, inInfo)
                      cref = flattenComponentRefSubs(cref, inEnv, inInfo)
                    Absyn.CREF_QUAL(name, subs, cref)
                  end
                  
                  (Absyn.CREF_FULLYQUALIFIED(componentRef = cref), _, _)  => begin
                      cref = flattenComponentRefSubs(cref, inEnv, inInfo)
                    AbsynUtil.crefMakeFullyQualified(cref)
                  end
                end
              end
          outCref
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
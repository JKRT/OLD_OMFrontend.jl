
  module DAETraverse


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
    using Setfield

    FuncExpType = Function
    Type_a = Any

    import Absyn
    import ClassInf
    import DAE
    import Config


    function local_flattenArrayType(inType::DAE.Type) ::Tuple{DAE.Type, DAE.Dimensions}
          local outDimensions::DAE.Dimensions
          local outType::DAE.Type

          (outType, outDimensions) = begin
              local ty::Type
              local dims::DAE.Dimensions
              local dim::DAE.Dimension
               #=  Array type
               =#
            @match inType begin
              DAE.T_ARRAY(__)  => begin
                  (ty, dims) = local_flattenArrayType(inType.ty)
                  dims = listAppend(inType.dims, dims)
                (ty, dims)
              end

              DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
                (inType, nil)
              end

              DAE.T_SUBTYPE_BASIC(__)  => begin
                local_flattenArrayType(inType.complexType)
              end

              _  => begin
                  (inType, nil)
              end
            end
          end
           #=  Complex type extending basetype with equality constraint
           =#
           #=  Complex type extending basetype.
           =#
           #=  Element type
           =#
      (outType, outDimensions)
    end

    #= @author: adrpo
     simplifies the given type, to be used in an expression or component reference =#
   function local_simplifyType(inType::DAE.Type) ::DAE.Type
         local outExpType::DAE.Type

         outExpType = begin
             local str::String
             local t::Type
             local t_1::DAE.Type
             local dims::DAE.Dimensions
             local tys::List{DAE.Type}
             local varLst::List{DAE.Var}
             local CIS::ClassInf.SMNode
             local ec::DAE.EqualityConstraint
           @matchcontinue inType begin
             DAE.T_FUNCTION(__)  => begin
               DAE.T_FUNCTION_REFERENCE_VAR(inType)
             end

             DAE.T_METAUNIONTYPE(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METARECORD(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METAPOLYMORPHIC(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METALIST(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METAARRAY(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METAOPTION(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_METATUPLE(__)  => begin
               DAE.T_METATYPE(inType)
             end

             DAE.T_UNKNOWN(__)  => begin
               DAE.T_UNKNOWN_DEFAULT
             end

             DAE.T_ANYTYPE(__)  => begin
               DAE.T_UNKNOWN_DEFAULT
             end

             t && DAE.T_ARRAY(__)  => begin
                 (t, dims) = local_flattenArrayType(t)
                 t_1 = local_simplifyType(t)
               DAE.T_ARRAY(t_1, dims)
             end

             DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_))  => begin
               inType
             end

             DAE.T_SUBTYPE_BASIC(complexType = t)  => begin
               local_simplifyType(t)
             end

             DAE.T_INTEGER(__)  => begin
               DAE.T_INTEGER_DEFAULT
             end

             DAE.T_REAL(__)  => begin
               DAE.T_REAL_DEFAULT
             end

             DAE.T_BOOL(__)  => begin
               DAE.T_BOOL_DEFAULT
             end

             DAE.T_CLOCK(__)  => begin
               DAE.T_CLOCK_DEFAULT
             end

             DAE.T_STRING(__)  => begin
               DAE.T_STRING_DEFAULT
             end

             DAE.T_NORETCALL(__)  => begin
               DAE.T_NORETCALL_DEFAULT
             end

             DAE.T_TUPLE(types = tys)  => begin
                 tys = ListUtil.map(tys, local_simplifyType)
               DAE.T_TUPLE(tys, inType.names)
             end

             DAE.T_ENUMERATION(__)  => begin
               inType
             end

             DAE.T_COMPLEX(CIS, varLst, ec)  => begin
                 @match true = Config.acceptMetaModelicaGrammar()
                 varLst = list(local_simplifyVar(v) for v in varLst)
               DAE.T_COMPLEX(CIS, varLst, ec)
             end

             DAE.T_COMPLEX(CIS && ClassInf.RECORD(__), varLst, ec)  => begin
                 varLst = list(local_simplifyVar(v) for v in varLst)
               DAE.T_COMPLEX(CIS, varLst, ec)
             end

             DAE.T_COMPLEX(__)  => begin
               inType
             end

             DAE.T_METABOXED(ty = t)  => begin
                 t_1 = local_simplifyType(t)
               DAE.T_METABOXED(t_1)
             end

             _  => begin
               DAE.T_UNKNOWN_DEFAULT
             end

             _  => begin
                   println("DAETraverse.local_simplifyType failed!")
                 fail()
             end
           end
         end
          #=  do NOT simplify out equality constraint
          =#
          #=  BTH watch out: Due to simplification some type info is lost here
          =#
          #=  for metamodelica we need this for some reson!
          =#
          #=  do this for records too, otherwise:
          =#
          #=  frame.R = Modelica.Mechanics.MultiBody.Frames.Orientation({const_matrix);
          =#
          #=  does not get expanded into the component equations.
          =#
          #=  otherwise just return the same!
          =#
          #=  This is the case when the type is currently UNTYPED
          =#
          #= /*
                 print(\" untyped \");
                 print(unparseType(inType));
                 print(\"\\n\");
                 */ =#
     outExpType
   end

   function local_simplifyVar(inVar::DAE.Var) ::DAE.Var
         local outVar::DAE.Var = inVar

         outVar = begin
           @match outVar begin
             DAE.TYPES_VAR(__)  => begin
                 @set outVar.ty = local_simplifyType(outVar.ty)
               outVar
             end
           end
         end
     outVar
   end


    function local_unliftArray(inType::DAE.Type) ::DAE.Type
          local outType::DAE.Type

          outType = begin
              local tp::Type
              local t::Type
              local d::DAE.Dimension
              local ds::DAE.Dimensions
            @match inType begin
              DAE.T_ARRAY(ty = tp, dims = _ <|  nil())  => begin
                tp
              end

              DAE.T_ARRAY(ty = tp, dims = _ <| ds)  => begin
                DAE.T_ARRAY(tp, ds)
              end

              DAE.T_METATYPE(ty = tp)  => begin
                Types.simplifyType(local_unliftArray(tp))
              end

              DAE.T_METAARRAY(ty = tp)  => begin
                tp
              end

              _  => begin
                  inType
              end
            end
          end
      outType
    end

    function local_unliftArrayTypeWithSubs(subs::List{<:DAE.Subscript}, ity::DAE.Type) ::DAE.Type
          local oty::DAE.Type

          oty = begin
              local rest::List{DAE.Subscript}
              local ty::Type
            @match (subs, ity) begin
              ( nil(), ty)  => begin
                ty
              end

              (_ <| rest, ty)  => begin
                  ty = local_unliftArray(ty)
                  ty = local_unliftArrayTypeWithSubs(rest, ty)
                ty
              end
            end
          end
      oty
    end


    function local_crefLastSubs(inComponentRef::DAE.ComponentRef) ::List{DAE.Subscript}
          local outSubscriptLst::List{DAE.Subscript}

          outSubscriptLst = begin
              local id::DAE.Ident
              local subs::List{DAE.Subscript}
              local cr::DAE.ComponentRef
            @match inComponentRef begin
              DAE.CREF_IDENT(subscriptLst = subs)  => begin
                subs
              end

              DAE.CREF_QUAL(componentRef = cr)  => begin
                local_crefLastSubs(cr)
              end
            end
          end
      outSubscriptLst
    end

    function local_crefLastType(inRef::DAE.ComponentRef) ::DAE.Type
          local res::DAE.Type

          res = begin
              local t2::DAE.Type
              local cr::DAE.ComponentRef
            @match inRef begin
              DAE.CREF_IDENT(_, t2, _)  => begin
                t2
              end

              DAE.CREF_QUAL(_, _, _, cr)  => begin
                local_crefLastType(cr)
              end
            end
          end
      res
    end


    function local_crefExp(cr::DAE.ComponentRef) ::DAE.Exp
          local cref::DAE.Exp

          cref = begin
              local ty1::Type
              local ty2::Type
              local subs::List{DAE.Subscript}
            @match cr begin
              _  => begin
                  ty1 = local_crefLastType(cr)
                  cref = begin
                    @match ty1 begin
                      DAE.T_ARRAY(__)  => begin
                          subs = local_crefLastSubs(cr)
                          ty2 = local_unliftArrayTypeWithSubs(subs, ty1)
                        DAE.CREF(cr, ty2)
                      end

                      _  => begin
                          DAE.CREF(cr, ty1)
                      end
                    end
                  end
                cref
              end
            end
          end
      cref
    end


         #= joins two daes by appending the element lists and joining the function trees =#
        function joinDaes(dae1::DAE.DAElist, dae2::DAE.DAElist) ::DAE.DAElist
              local outDae::DAE.DAElist

              outDae = begin
                  local elts1::List{DAE.Element}
                  local elts2::List{DAE.Element}
                  local elts::List{DAE.Element}
                   #=  just append lists
                   =#
                @match (dae1, dae2) begin
                  (DAE.DAE_LIST(elts1), DAE.DAE_LIST(elts2))  => begin
                      elts = listAppend(elts1, elts2)
                    DAE.DAE_LIST(elts)
                  end
                end
              end
               #=  t1 = clock();
               =#
               #=  t2 = clock();
               =#
               #=  ti = t2 -. t1;
               =#
               #=  fprintln(Flags.INNER_OUTER, \" joinDAEs: (\" + realString(ti) + \") -> \" + intString(listLength(elts1)) + \" + \" +  intString(listLength(elts2)));
               =#
          outDae
        end



         #= author: BZ, 2008-12, adrpo, 2010-12
           This function traverses all dae exps.
           NOTE, it also traverses DAE.VAR(componenname) as an expression. =#
        function traverseDAEElementList(elements::List{DAE.Element}, func::FuncExpType, arg::ArgT)  where {ArgT}



              (elements, arg) = ListUtil.mapFold(elements, (func) -> traverseDAEElement(func = func), arg)
          (elements, arg)
        end

         #= author: adrpo, 2010-12
           This function is a tail recursive function that traverses all dae exps.
           NOTE, it also traverses DAE.VAR(componenname) as an expression. =#
        function traverseDAEElement(element::DAE.Element, func::FuncExpType, arg::ArgT)  where {ArgT}



              _ = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local e3::DAE.Exp
                  local new_e1::DAE.Exp
                  local new_e2::DAE.Exp
                  local new_e3::DAE.Exp
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local new_cr1::DAE.ComponentRef
                  local new_cr2::DAE.ComponentRef
                  local el::List{DAE.Element}
                  local new_el::List{DAE.Element}
                  local eqll::List{List{DAE.Element}}
                  local new_eqll::List{List{DAE.Element}}
                  local e::DAE.Element
                  local new_e::DAE.Element
                  local stmts::List{DAE.Statement}
                  local new_stmts::List{DAE.Statement}
                  local expl::List{DAE.Exp}
                  local new_expl::List{DAE.Exp}
                  local binding::Option{DAE.Exp}
                  local new_binding::Option{DAE.Exp}
                  local attr::Option{DAE.VariableAttributes}
                  local new_attr::Option{DAE.VariableAttributes}
                  local varLst::List{DAE.Var}
                  local daebinding::DAE.Binding
                  local new_daebinding::DAE.Binding
                  local changed::Bool
                  local new_ty::DAE.Type
                @match element begin
                  DAE.VAR(componentRef = cr1, binding = binding, variableAttributesOption = attr)  => begin
                      (e1, arg) = func(local_crefExp(cr1), arg)
                      if local_isCref(e1)
                        new_cr1 = local_expCref(e1)
                        if ! referenceEq(cr1, new_cr1)
                          element.componentRef = new_cr1
                        end
                      end
                      element.dims = list(begin
                        @match d begin
                          DAE.DIM_EXP(e1)  => begin
                              (new_e1, arg) = func(e1, arg)
                            if referenceEq(e1, new_e1)
                                  d
                                else
                                  DAE.DIM_EXP(new_e1)
                                end
                          end

                          _  => begin
                              d
                          end
                        end
                      end for d in element.dims)
                      new_ty = begin
                        ty = element.ty
                        @match ty begin
                          DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(__))  => begin
                              changed = false
                              varLst = list(begin
                                @match v begin
                                  DAE.TYPES_VAR(binding = daebinding && DAE.EQBOUND(__))  => begin
                                      (e2, arg) = func(daebinding.exp, arg)
                                      if ! referenceEq(daebinding.exp, e2)
                                        daebinding = DAE.EQBOUND(e2, NONE(), daebinding.constant_, daebinding.source)
                                        v.binding = daebinding
                                        changed = true
                                      end
                                    v
                                  end

                                  DAE.TYPES_VAR(binding = daebinding && DAE.VALBOUND(__))  => begin
                                      e1 = ValuesUtil.valueExp(daebinding.valBound)
                                      (e2, arg) = func(e1, arg)
                                      if ! referenceEq(e1, e2)
                                        new_daebinding = DAE.EQBOUND(e2, NONE(), DAE.C_CONST(), daebinding.source)
                                        v.binding = new_daebinding
                                        changed = true
                                      end
                                    v
                                  end

                                  _  => begin
                                      v
                                  end
                                end
                              end for v in ty.varLst)
                              if ! referenceEq(varLst, ty.varLst)
                                ty.varLst = varLst
                              end
                            ty
                          end

                          _  => begin
                              ty
                          end
                        end
                      end
                      if ! referenceEq(element.ty, new_ty)
                        element.ty = new_ty
                      end
                      (new_binding, arg) = traverseDAEOptExp(binding, func, arg)
                      if ! referenceEq(binding, new_binding)
                        element.binding = new_binding
                      end
                      (new_attr, arg) = traverseDAEVarAttr(attr, func, arg)
                      if ! referenceEq(attr, new_attr)
                        element.variableAttributesOption = new_attr
                      end
                    ()
                  end

                  DAE.DEFINE(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(local_crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.INITIALDEFINE(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(local_crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.EQUEQUATION(cr1 = cr1, cr2 = cr2)  => begin
                      @match (DAE.CREF(new_cr1), arg) = func(local_crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.cr1 = new_cr1
                      end
                      @match (DAE.CREF(new_cr2), arg) = func(local_crefExp(cr2), arg)
                      if ! referenceEq(cr2, new_cr2)
                        element.cr2 = new_cr2
                      end
                    ()
                  end

                  DAE.EQUATION(exp = e1, scalar = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.scalar = new_e2
                      end
                    ()
                  end

                  DAE.INITIALEQUATION(exp1 = e1, exp2 = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp1 = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.exp2 = new_e2
                      end
                    ()
                  end

                  DAE.COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.lhs = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.rhs = new_e2
                      end
                    ()
                  end

                  DAE.INITIAL_COMPLEX_EQUATION(lhs = e1, rhs = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.lhs = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.rhs = new_e2
                      end
                    ()
                  end

                  DAE.ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.array = new_e2
                      end
                    ()
                  end

                  DAE.INITIAL_ARRAY_EQUATION(exp = e1, array = e2)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.array = new_e2
                      end
                    ()
                  end

                  DAE.WHEN_EQUATION(condition = e1, equations = el)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations = new_el
                      end
                      if isSome(element.elsewhen_)
                        @match SOME(e) = element.elsewhen_
                        (new_e, arg) = traverseDAEElement(e, func, arg)
                        if ! referenceEq(e, new_e)
                          element.elsewhen_ = SOME(new_e)
                        end
                      end
                    ()
                  end

                  DAE.FOR_EQUATION(range = e1, equations = el)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.range = new_e1
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations = new_el
                      end
                    ()
                  end

                  DAE.COMP(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.EXTOBJECTCLASS(__)  => begin
                    ()
                  end

                  DAE.ASSERT(condition = e1, message = e2, level = e3)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.message = new_e2
                      end
                      (new_e3, arg) = func(e3, arg)
                      if ! referenceEq(e3, new_e3)
                        element.level = new_e3
                      end
                    ()
                  end

                  DAE.INITIAL_ASSERT(condition = e1, message = e2, level = e3)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.condition = new_e1
                      end
                      (new_e2, arg) = func(e2, arg)
                      if ! referenceEq(e2, new_e2)
                        element.message = new_e2
                      end
                      (new_e3, arg) = func(e3, arg)
                      if ! referenceEq(e3, new_e3)
                        element.level = new_e3
                      end
                    ()
                  end

                  DAE.TERMINATE(message = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.message = new_e1
                      end
                    ()
                  end

                  DAE.INITIAL_TERMINATE(message = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.message = new_e1
                      end
                    ()
                  end

                  DAE.NORETCALL(exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                    ()
                  end

                  DAE.INITIAL_NORETCALL(exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                    ()
                  end

                  DAE.REINIT(componentRef = cr1, exp = e1)  => begin
                      (new_e1, arg) = func(e1, arg)
                      if ! referenceEq(e1, new_e1)
                        element.exp = new_e1
                      end
                      @match (DAE.CREF(new_cr1), arg) = func(local_crefExp(cr1), arg)
                      if ! referenceEq(cr1, new_cr1)
                        element.componentRef = new_cr1
                      end
                    ()
                  end

                  DAE.ALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(stmts))  => begin
                      (new_stmts, arg) = traverseDAEEquationsStmts(stmts, func, arg)
                      if ! referenceEq(stmts, new_stmts)
                        element.algorithm_ = DAE.ALGORITHM_STMTS(new_stmts)
                      end
                    ()
                  end

                  DAE.INITIALALGORITHM(algorithm_ = DAE.ALGORITHM_STMTS(stmts))  => begin
                      (new_stmts, arg) = traverseDAEEquationsStmts(stmts, func, arg)
                      if ! referenceEq(stmts, new_stmts)
                        element.algorithm_ = DAE.ALGORITHM_STMTS(new_stmts)
                      end
                    ()
                  end

                  DAE.CONSTRAINT(constraints = DAE.CONSTRAINT_EXPS(expl))  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.constraints = DAE.CONSTRAINT_EXPS(new_expl)
                      end
                    ()
                  end

                  DAE.CLASS_ATTRIBUTES(__)  => begin
                    ()
                  end

                  DAE.IF_EQUATION(condition1 = expl, equations2 = eqll, equations3 = el)  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.condition1 = new_expl
                      end
                      (new_eqll, arg) = traverseDAEList(eqll, func, arg)
                      if ! referenceEq(eqll, new_eqll)
                        element.equations2 = new_eqll
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations3 = new_el
                      end
                    ()
                  end

                  DAE.INITIAL_IF_EQUATION(condition1 = expl, equations2 = eqll, equations3 = el)  => begin
                      (new_expl, arg) = traverseDAEExpList(expl, func, arg)
                      if ! referenceEq(expl, new_expl)
                        element.condition1 = new_expl
                      end
                      (new_eqll, arg) = traverseDAEList(eqll, func, arg)
                      if ! referenceEq(eqll, new_eqll)
                        element.equations2 = new_eqll
                      end
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.equations3 = new_el
                      end
                    ()
                  end

                  DAE.FLAT_SM(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.SM_COMP(dAElist = el)  => begin
                      (new_el, arg) = traverseDAEElementList(el, func, arg)
                      if ! referenceEq(el, new_el)
                        element.dAElist = new_el
                      end
                    ()
                  end

                  DAE.COMMENT(__)  => begin
                    ()
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("traverseDAEElement not implemented correctly for element: " + " NO DAEDUMP! " #= DAEDump.dumpElementsStr(list(element)) =#))
                      fail()
                  end
                end
              end
          (element, arg)
        end

         @Uniontype TraverseStatementsOptions begin
              @Record TRAVERSE_ALL begin

              end

              @Record TRAVERSE_RHS_ONLY begin

              end
         end

         #=
          This function goes through the Algorithm structure and finds all the
          expressions and performs the function on them
         =#
        function traverseAlgorithmExps(inAlgorithm::DAE.Algorithm, func::FuncExpType, inTypeA::Type_a) ::Type_a
              local outTypeA::Type_a

              outTypeA = begin
                  local stmts::List{DAE.Statement}
                  local ext_arg_1::Type_a
                @match (inAlgorithm, func, inTypeA) begin
                  (DAE.ALGORITHM_STMTS(statementLst = stmts), _, _)  => begin
                      (_, ext_arg_1) = traverseDAEEquationsStmts(stmts, func, inTypeA)
                    ext_arg_1
                  end
                end
              end
          outTypeA
        end

         #= Traversing of DAE.Statement. =#
        function traverseDAEEquationsStmts(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = traverseDAEEquationsStmtsList(inStmts, func, TRAVERSE_ALL(), iextraArg)
          (outStmts, oextraArg)
        end

         #= Traversing of DAE.Statement. Only rhs expressions are replaced, keeping lhs intact. =#
        function traverseDAEEquationsStmtsRhsOnly(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = traverseDAEEquationsStmtsList(inStmts, func, TRAVERSE_RHS_ONLY(), iextraArg)
          (outStmts, oextraArg)
        end

         #= Traversing of DAE.Statement. =#
        function traverseDAEEquationsStmtsList(inStmts::List{<:DAE.Statement}, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              local outStmtsLst::List{List{DAE.Statement}}
              local b::Bool

              (outStmtsLst, oextraArg) = ListUtil.map2Fold(inStmts, traverseDAEEquationsStmtsWork, func, opt, iextraArg)
              outStmts = ListUtil.flatten(outStmtsLst)
              b = ListUtil.allReferenceEq(inStmts, outStmts)
              outStmts = if b
                    inStmts
                  else
                    outStmts
                  end
          (outStmts, oextraArg)
        end

        function traverseStatementsOptionsEvalLhs(inExp::DAE.Exp, inA::Type_a, func::FuncExpType, opt::TraverseStatementsOptions) ::Tuple{DAE.Exp, Type_a}
              local outA::Type_a
              local outExp::DAE.Exp

              (outExp, outA) = begin
                @match (inExp, inA, func, opt) begin
                  (_, _, _, TRAVERSE_ALL(__))  => begin
                      (outExp, outA) = func(inExp, inA)
                    (outExp, outA)
                  end

                  _  => begin
                      (inExp, inA)
                  end
                end
              end
          (outExp, outA)
        end

         #= Handles the traversing of DAE.Statement. =#
        function traverseDAEEquationsStmtsWork(inStmt::DAE.Statement, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
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
                  local stmts1::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local tp::DAE.Type
                  local x::DAE.Statement
                  local ew::DAE.Statement
                  local ew_1::DAE.Statement
                  local b1::Bool
                  local id1::String
                  local str::String
                  local ix::ModelicaInteger
                  local source::DAE.ElementSource
                  local algElse::DAE.Else
                  local algElse1::DAE.Else
                  local extraArg::Type_a
                  local loopPrlVars::List{Tuple{DAE.ComponentRef, SourceInfo}} #= list of parallel variables used/referenced in the parfor loop =#
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                  local b::Bool
                @matchcontinue (inStmt, func, opt, iextraArg) begin
                  (DAE.STMT_ASSIGN(type_ = tp, exp1 = e, exp = e2, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = traverseStatementsOptionsEvalLhs(e, extraArg, func, opt)
                      (e_2, extraArg) = func(e2, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2)
                            inStmt
                          else
                            DAE.STMT_ASSIGN(tp, e_1, e_2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_TUPLE_ASSIGN(type_ = tp, expExpLst = expl1, exp = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      @match (DAE.TUPLE(expl2), extraArg) = traverseStatementsOptionsEvalLhs(DAE.TUPLE(expl1), extraArg, func, opt)
                      x = if referenceEq(e, e_1) && referenceEq(expl1, expl2)
                            inStmt
                          else
                            DAE.STMT_TUPLE_ASSIGN(tp, expl2, e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_ASSIGN_ARR(type_ = tp, lhs = e, exp = e2, source = source), _, _, extraArg)  => begin
                      (e_2, extraArg) = func(e2, extraArg)
                      _ = begin
                        @matchcontinue () begin
                          ()  => begin
                              @match ((@match DAE.CREF(_, _) = e_1), extraArg) = traverseStatementsOptionsEvalLhs(e, extraArg, func, opt)
                              x = if referenceEq(e2, e_2) && referenceEq(e, e_1)
                                    inStmt
                                  else
                                    DAE.STMT_ASSIGN_ARR(tp, e_1, e_2, source)
                                  end
                            ()
                          end

                          _  => begin
                                @shouldFail @match (DAE.CREF(_, _), _) = func(e, extraArg)
                                x = if referenceEq(e2, e_2)
                                      inStmt
                                    else
                                      DAE.STMT_ASSIGN_ARR(tp, e, e_2, source)
                                    end
                              ()
                          end
                        end
                      end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_IF(exp = e, statementLst = stmts, else_ = algElse, source = source), _, _, extraArg)  => begin
                      (algElse1, extraArg) = traverseDAEEquationsStmtsElse(algElse, func, opt, extraArg)
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      (stmts1, b) = Algorithm.optimizeIf(e_1, stmts2, algElse1, source)
                      stmts1 = if ! b && referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(algElse, algElse1)
                            _cons(inStmt, nil)
                          else
                            stmts1
                          end
                    (stmts1, extraArg)
                  end

                  (DAE.STMT_FOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_FOR(tp, b1, id1, ix, e_1, stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_PARFOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, loopPrlVars = loopPrlVars, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_PARFOR(tp, b1, id1, ix, e_1, stmts2, loopPrlVars, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHILE(exp = e, statementLst = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHILE(e_1, stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = NONE(), source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, NONE(), source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = SOME(ew), source = source), _, _, extraArg)  => begin
                      @match (list(ew_1), extraArg) = traverseDAEEquationsStmtsList(list(ew), func, opt, extraArg)
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(ew, ew_1) && referenceEq(e, e_1) && referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, SOME(ew_1), source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_ASSERT(cond = e, msg = e2, level = e3, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      (e_2, extraArg) = func(e2, extraArg)
                      (e_3, extraArg) = func(e3, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(e3, e_3)
                            inStmt
                          else
                            DAE.STMT_ASSERT(e_1, e_2, e_3, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_TERMINATE(msg = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1)
                            inStmt
                          else
                            DAE.STMT_TERMINATE(e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_REINIT(var = e, value = e2, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      (e_2, extraArg) = func(e2, extraArg)
                      x = if referenceEq(e, e_1) && referenceEq(e2, e_2)
                            inStmt
                          else
                            DAE.STMT_REINIT(e_1, e_2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_NORETCALL(exp = e, source = source), _, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, extraArg)
                      x = if referenceEq(e, e_1)
                            inStmt
                          else
                            DAE.STMT_NORETCALL(e_1, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_RETURN(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_BREAK(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (x && DAE.STMT_CONTINUE(__), _, _, extraArg)  => begin
                    (_cons(x, nil), extraArg)
                  end

                  (DAE.STMT_FAILURE(body = stmts, source = source), _, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEEquationsStmtsList(stmts, func, opt, extraArg)
                      x = if referenceEq(stmts, stmts2)
                            inStmt
                          else
                            DAE.STMT_FAILURE(stmts2, source)
                          end
                    (_cons(x, nil), extraArg)
                  end

                  (x, _, _, _)  => begin
                      str = " NO DAEDUMP! "# DAEDump.ppStatementStr(x)
                      str = "traverseDAEEquationsStmts not implemented correctly: " + str
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #= /* We need to pass this through because simplify/etc may scalarize the cref...
                               true = Flags.isSet(Flags.FAILTRACE);
                               print(DAEDump.ppStatementStr(x));
                               print(\"Warning, not allowed to set the componentRef to a expression in traverseDAEEquationsStmts\\n\");
                            */ =#
               #=  MetaModelica extension. KS
               =#
          (outStmts, oextraArg)
        end

         #= Helper function for traverseDAEEquationsStmts =#
        function traverseDAEEquationsStmtsElse(inElse::DAE.Else, func::FuncExpType, opt::TraverseStatementsOptions, iextraArg::Type_a) ::Tuple{DAE.Else, Type_a}
              local oextraArg::Type_a
              local outElse::DAE.Else

              (outElse, oextraArg) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local st::List{DAE.Statement}
                  local st_1::List{DAE.Statement}
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local extraArg::Type_a
                  local b::Bool
                @match (inElse, func, opt, iextraArg) begin
                  (DAE.NOELSE(__), _, _, extraArg)  => begin
                    (DAE.NOELSE(), extraArg)
                  end

                  (DAE.ELSEIF(e, st, el), _, _, extraArg)  => begin
                      (el_1, extraArg) = traverseDAEEquationsStmtsElse(el, func, opt, extraArg)
                      (st_1, extraArg) = traverseDAEEquationsStmtsList(st, func, opt, extraArg)
                      (e_1, extraArg) = func(e, extraArg)
                      outElse = Algorithm.optimizeElseIf(e_1, st_1, el_1)
                      b = referenceEq(el, el_1) && referenceEq(st, st_1) && referenceEq(e, e_1)
                      outElse = if b
                            inElse
                          else
                            outElse
                          end
                    (outElse, extraArg)
                  end

                  (DAE.ELSE(st), _, _, extraArg)  => begin
                      (st_1, extraArg) = traverseDAEEquationsStmtsList(st, func, opt, extraArg)
                      outElse = if referenceEq(st, st_1)
                            inElse
                          else
                            DAE.ELSE(st_1)
                          end
                    (outElse, extraArg)
                  end
                end
              end
          (outElse, oextraArg)
        end

         #= Author: BZ, 2008-12, wbraun 2012-09
          Traversing statemeant and provide current statement
          to FuncExptype
          Handles the traversing of DAE.Statement. =#
        function traverseDAEStmts(inStmts::List{<:DAE.Statement}, func::FuncExpType, iextraArg::Type_a) ::Tuple{List{DAE.Statement}, Type_a}
              local oextraArg::Type_a
              local outStmts::List{DAE.Statement}

              (outStmts, oextraArg) = begin
                  local e_1::DAE.Exp
                  local e_2::DAE.Exp
                  local e::DAE.Exp
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
                  local stmts1::List{DAE.Statement}
                  local stmts2::List{DAE.Statement}
                  local tp::DAE.Type
                  local x::DAE.Statement
                  local ew::DAE.Statement
                  local ew_1::DAE.Statement
                  local b1::Bool
                  local id1::String
                  local str::String
                  local ix::ModelicaInteger
                  local source::DAE.ElementSource
                  local algElse::DAE.Else
                  local extraArg::Type_a
                  local loopPrlVars::List{Tuple{DAE.ComponentRef, SourceInfo}} #= list of parallel variables used/referenced in the parfor loop =#
                  local conditions::List{DAE.ComponentRef}
                  local initialCall::Bool
                @matchcontinue (inStmts, func, iextraArg) begin
                  ( nil(), _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (x && DAE.STMT_ASSIGN(type_ = tp, exp1 = e2, exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSIGN(tp, e_2, e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_TUPLE_ASSIGN(type_ = tp, expExpLst = expl1, exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (expl2, extraArg) = traverseDAEExpListStmt(expl1, func, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(expl2, expl1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_TUPLE_ASSIGN(tp, expl2, e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_ASSIGN_ARR(type_ = tp, lhs = e, exp = e2, source = source) <| xs, _, extraArg)  => begin
                      (e_2, extraArg) = func(e2, x, extraArg)
                      try
                        @match ((@match DAE.CREF(_, _) = e_1), extraArg) = func(e, x, extraArg)
                      catch
                        e_1 = e
                      end
                       #=  We need to pass this through because simplify/etc may scalarize the cref...
                       =#
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSIGN_ARR(tp, e_1, e_2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_IF(exp = e, statementLst = stmts, else_ = algElse, source = source) <| xs, _, extraArg)  => begin
                      (algElse, extraArg) = traverseDAEStmtsElse(algElse, func, x, extraArg)
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (stmts1, _) = Algorithm.optimizeIf(e_1, stmts2, algElse, source)
                    (listAppend(stmts1, xs_1), extraArg)
                  end

                  (x && DAE.STMT_FOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_FOR(tp, b1, id1, ix, e_1, stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_PARFOR(type_ = tp, iterIsArray = b1, iter = id1, index = ix, range = e, statementLst = stmts, loopPrlVars = loopPrlVars, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_PARFOR(tp, b1, id1, ix, e_1, stmts2, loopPrlVars, source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_WHILE(exp = e, statementLst = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_WHILE(e_1, stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = NONE(), source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, NONE(), source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_WHEN(exp = e, conditions = conditions, initialCall = initialCall, statementLst = stmts, elseWhen = SOME(ew), source = source) <| xs, _, extraArg)  => begin
                      @match (list(_), extraArg) = traverseDAEStmts(list(ew), func, extraArg)
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                    (_cons(DAE.STMT_WHEN(e_1, conditions, initialCall, stmts2, SOME(ew), source), xs_1), extraArg)
                  end

                  (x && DAE.STMT_ASSERT(cond = e, msg = e2, level = e3, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (e_3, extraArg) = func(e3, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(e3, e_3) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_ASSERT(e_1, e_2, e_3, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_TERMINATE(msg = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_TERMINATE(e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_REINIT(var = e, value = e2, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (e_2, extraArg) = func(e2, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(e2, e_2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_REINIT(e_1, e_2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_NORETCALL(exp = e, source = source) <| xs, _, extraArg)  => begin
                      (e_1, extraArg) = func(e, x, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(e, e_1) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_NORETCALL(e_1, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x && DAE.STMT_RETURN(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (x && DAE.STMT_BREAK(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (x && DAE.STMT_CONTINUE(__) <| xs, _, extraArg)  => begin
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      (_, extraArg) = func(DAE.ICONST(-1), x, extraArg)
                    (if referenceEq(xs, xs_1)
                          inStmts
                        else
                          _cons(x, xs_1)
                        end, extraArg)
                  end

                  (DAE.STMT_FAILURE(body = stmts, source = source) <| xs, _, extraArg)  => begin
                      (stmts2, extraArg) = traverseDAEStmts(stmts, func, extraArg)
                      (xs_1, extraArg) = traverseDAEStmts(xs, func, extraArg)
                      outStmts = if referenceEq(stmts, stmts2) && referenceEq(xs, xs_1)
                            inStmts
                          else
                            _cons(DAE.STMT_FAILURE(stmts2, source), xs_1)
                          end
                    (outStmts, extraArg)
                  end

                  (x <| _, _, _)  => begin
                      str = " NO DAEDUMP! " # DAEDump.ppStatementStr(x)
                      str = "traverseDAEStmts not implemented correctly: " + str
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  Dummy argument, so we can traverse over statements without expressions
               =#
               #=  MetaModelica extension. KS
               =#
          (outStmts, oextraArg)
        end

         #= Helper function for traverseDAEEquationsStmts =#
        function traverseDAEStmtsElse(inElse::DAE.Else, func::FuncExpType, istmt::DAE.Statement, iextraArg::Type_a) ::Tuple{DAE.Else, Type_a}
              local oextraArg::Type_a
              local outElse::DAE.Else

              (outElse, oextraArg) = begin
                  local e::DAE.Exp
                  local e_1::DAE.Exp
                  local st::List{DAE.Statement}
                  local st_1::List{DAE.Statement}
                  local el::DAE.Else
                  local el_1::DAE.Else
                  local extraArg::Type_a
                @match (inElse, func, istmt, iextraArg) begin
                  (DAE.NOELSE(__), _, _, extraArg)  => begin
                    (DAE.NOELSE(), extraArg)
                  end

                  (DAE.ELSEIF(e, st, el), _, _, extraArg)  => begin
                      (el_1, extraArg) = traverseDAEStmtsElse(el, func, istmt, extraArg)
                      (st_1, extraArg) = traverseDAEStmts(st, func, extraArg)
                      (e_1, extraArg) = func(e, istmt, extraArg)
                    (Algorithm.optimizeElseIf(e_1, st_1, el_1), extraArg)
                  end

                  (DAE.ELSE(st), _, _, extraArg)  => begin
                      (st_1, extraArg) = traverseDAEStmts(st, func, extraArg)
                    (DAE.ELSE(st_1), extraArg)
                  end
                end
              end
          (outElse, oextraArg)
        end

         #=
        Author: BZ, 2008-12
        Traverse an list of expressions, helper function for traverseDAE =#
        function traverseDAEExpListStmt(iexps::List{<:DAE.Exp}, func::FuncExpType, istmt::DAE.Statement, iextraArg::Type_a) ::Tuple{List{DAE.Exp}, Type_a}
              local oextraArg::Type_a
              local oexps::List{DAE.Exp}

              (oexps, oextraArg) = begin
                  local e::DAE.Exp
                  local extraArg::Type_a
                  local exps::List{DAE.Exp}
                @match (iexps, func, istmt, iextraArg) begin
                  ( nil(), _, _, extraArg)  => begin
                    (nil, extraArg)
                  end

                  (e <| exps, _, _, extraArg)  => begin
                      (e, extraArg) = func(e, istmt, extraArg)
                      (oexps, extraArg) = traverseDAEExpListStmt(exps, func, istmt, extraArg)
                    (_cons(e, oexps), extraArg)
                  end
                end
              end
          (oexps, oextraArg)
        end

         #=
        Author: BZ, 2008-12
        Help function to traverseDAE
         =#
        function traverseDAEVarAttr(attr::Option{<:DAE.VariableAttributes}, func::FuncExpType, iextraArg::Type_a) ::Tuple{Option{DAE.VariableAttributes}, Type_a}
              local oextraArg::Type_a
              local traversedDaeList::Option{DAE.VariableAttributes}

              (traversedDaeList, oextraArg) = begin
                  local quantity::Option{DAE.Exp}
                  local unit::Option{DAE.Exp}
                  local displayUnit::Option{DAE.Exp}
                  local min::Option{DAE.Exp}
                  local max::Option{DAE.Exp}
                  local start::Option{DAE.Exp}
                  local fixed::Option{DAE.Exp}
                  local nominal::Option{DAE.Exp}
                  local eb::Option{DAE.Exp}
                  local so::Option{DAE.Exp}
                  local stateSelect::Option{DAE.StateSelect}
                  local uncertainty::Option{DAE.Uncertainty}
                  local distribution::Option{DAE.Distribution}
                  local ip::Option{Bool}
                  local fn::Option{Bool}
                  local extraArg::Type_a
                @match (attr, func, iextraArg) begin
                  (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, start, fixed, nominal, stateSelect, uncertainty, distribution, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (unit, extraArg) = traverseDAEOptExp(unit, func, extraArg)
                      (displayUnit, extraArg) = traverseDAEOptExp(displayUnit, func, extraArg)
                      (min, extraArg) = traverseDAEOptExp(min, func, extraArg)
                      (max, extraArg) = traverseDAEOptExp(max, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                      (nominal, extraArg) = traverseDAEOptExp(nominal, func, extraArg)
                    (SOME(DAE.VAR_ATTR_REAL(quantity, unit, displayUnit, min, max, start, fixed, nominal, stateSelect, uncertainty, distribution, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_INT(quantity, min, max, start, fixed, uncertainty, distribution, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (min, extraArg) = traverseDAEOptExp(min, func, extraArg)
                      (max, extraArg) = traverseDAEOptExp(max, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_INT(quantity, min, max, start, fixed, uncertainty, distribution, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_BOOL(quantity, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_BOOL(quantity, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_CLOCK(_, _)), _, extraArg)  => begin
                    (attr, extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_STRING(quantity, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                      (fixed, extraArg) = traverseDAEOptExp(fixed, func, extraArg)
                    (SOME(DAE.VAR_ATTR_STRING(quantity, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (SOME(DAE.VAR_ATTR_ENUMERATION(quantity, min, max, start, fixed, eb, ip, fn, so)), _, extraArg)  => begin
                      (quantity, extraArg) = traverseDAEOptExp(quantity, func, extraArg)
                      (start, extraArg) = traverseDAEOptExp(start, func, extraArg)
                    (SOME(DAE.VAR_ATTR_ENUMERATION(quantity, min, max, start, fixed, eb, ip, fn, so)), extraArg)
                  end

                  (NONE(), _, extraArg)  => begin
                    (NONE(), extraArg)
                  end
                end
              end
               #=  BTH
               =#
          (traversedDaeList, oextraArg)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

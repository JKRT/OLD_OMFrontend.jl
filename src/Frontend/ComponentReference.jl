  module ComponentReference


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    FuncType = Function

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
         #=  public imports
         =#
  println("ComponentReference.jl 0")
        import Absyn

        import DAE

        import File
         #=  protected imports
         =#
  println("ComponentReference.jl 1")

        import ClassInf

        import Config

        import Debug

        import Dump
  println("ComponentReference.jl 2")
        import Error

        import Expression

        import ExpressionDump

        import Flags
  println("ComponentReference.jl 3")
        import ListUtil

        import MetaModelica.Dangerous

        import Print
  println("ComponentReference.jl 4")
        import System

        import Types

        import Util
         #=  do not make this public. instead use the function below.
         =#
println("ComponentReference.jl 5")
         const dummyCref = DAE.CREF_IDENT("dummy", DAE.T_UNKNOWN_DEFAULT, nil)::DAE.ComponentRef

         #=
          author: PA

          Calculates a hash value for DAE.ComponentRef, by hashing each individual part separately and summing the values, and then apply
          intMod to it, to return a value in range [0,mod-1].
          Also hashes subscripts in a clever way avoiding [1,2] and [2,1] to hash to the same value. This is done by investigating array type
          to find dimension of array.
         =#
        function hashComponentRefMod(cr::DAE.ComponentRef, mod::ModelicaInteger) ::ModelicaInteger
              local res::ModelicaInteger

              local h::ModelicaInteger

               #=  hash might overflow => force positive
               =#
              h = intAbs(hashComponentRef(cr))
              res = intMod(h, mod)
          res
        end

         #= new hashing that properly deals with subscripts so [1,2] and [2,1] hash to different values =#
        function hashComponentRef(cr::DAE.ComponentRef) ::ModelicaInteger
              local hash::ModelicaInteger

              hash = begin
                  local id::DAE.Ident
                  local tp::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cr1::DAE.ComponentRef
                @match cr begin
                  DAE.CREF_IDENT(id, tp, subs)  => begin
                    stringHashDjb2(id) + hashSubscripts(tp, subs)
                  end

                  DAE.CREF_QUAL(id, tp, subs, cr1)  => begin
                    stringHashDjb2(id) + hashSubscripts(tp, subs) + hashComponentRef(cr1)
                  end

                  DAE.CREF_ITER(id, _, tp, subs)  => begin
                    stringHashDjb2(id) + hashSubscripts(tp, subs)
                  end

                  _  => begin
                      0
                  end
                end
              end
               #= print(\"IDENT, \"+id+\" hashed to \"+intString(stringHashDjb2(id))+\", subs hashed to \"+intString(hashSubscripts(tp,subs))+\"\\n\");
               =#
               #= print(\"QUAL, \"+id+\" hashed to \"+intString(stringHashDjb2(id))+\", subs hashed to \"+intString(hashSubscripts(tp,subs))+\"\\n\");
               =#
          hash
        end

         #= help function, hashing subscripts making sure [1,2] and [2,1] doesn't match to the same number =#
        function hashSubscripts(tp::DAE.Type, subs::List{<:DAE.Subscript}) ::ModelicaInteger
              local hash::ModelicaInteger

              hash = begin
                @match (tp, subs) begin
                  (_,  nil())  => begin
                    0
                  end

                  _  => begin
                      hashSubscripts2(ListUtil.fill(1, listLength(subs)), subs, 1)
                  end
                end
              end
               #=  TODO: Currently, the types of component references are wrong, they consider the subscripts but they should not.
               =#
               #=  For example, given Real a[10,10];  the component reference 'a[1,2]' should have type Real[10,10] but it has type Real.
               =#
               #= /*DAEUtil.expTypeArrayDimensions(tp),*/ =#
          hash
        end

         #= help function =#
        function hashSubscripts2(dims::List{<:ModelicaInteger}, subs::List{<:DAE.Subscript}, factor::ModelicaInteger) ::ModelicaInteger
              local hash::ModelicaInteger

              hash = begin
                  local i1::ModelicaInteger
                  local s::DAE.Subscript
                  local rest_dims::List{ModelicaInteger}
                  local rest_subs::List{DAE.Subscript}
                @match (dims, subs, factor) begin
                  ( nil(),  nil(), _)  => begin
                    0
                  end

                  (_ <| rest_dims, s <| rest_subs, _)  => begin
                    hashSubscript(s) * factor + hashSubscripts2(rest_dims, rest_subs, factor * 1000)
                  end
                end
              end
               #=  TODO: change to using dimensions once cref types has been fixed.
               =#
               #= /* *i1 */ =#
          hash
        end

         #= help function =#
        function hashSubscript(sub::DAE.Subscript) ::ModelicaInteger
              local hash::ModelicaInteger

              hash = begin
                  local exp::DAE.Exp
                  local i::ModelicaInteger
                @match sub begin
                  DAE.WHOLEDIM(__)  => begin
                    0
                  end

                  DAE.INDEX(DAE.ICONST(i))  => begin
                    i
                  end

                  DAE.SLICE(exp)  => begin
                    Expression.hashExp(exp)
                  end

                  DAE.INDEX(exp)  => begin
                    Expression.hashExp(exp)
                  end

                  DAE.WHOLE_NONEXP(exp)  => begin
                    Expression.hashExp(exp)
                  end
                end
              end
          hash
        end

         #= @author: adrpo
          creates an array, with one element for each record in ComponentRef! =#
        function createEmptyCrefMemory() ::Array{List{DAE.ComponentRef}}
              local crefMemory::Array{List{DAE.ComponentRef}}

              crefMemory = arrayCreate(3, nil)
          crefMemory
        end

         #= /***************************************************/ =#
         #= /* generate a ComponentRef */ =#
         #= /***************************************************/ =#

         #= @author: adrpo
          This function creates a dummy component reference =#
        function makeDummyCref() ::DAE.ComponentRef
              local outCrefIdent::DAE.ComponentRef

              outCrefIdent = dummyCref
          outCrefIdent
        end

         #= @author: adrpo
          This function creates a DAE.CREF_IDENT(ident, identType, subscriptLst) =#
        function makeCrefIdent(ident::DAE.Ident, identType::DAE.Type #= type of the identifier, without considering the subscripts =#, subscriptLst::List{<:DAE.Subscript}) ::DAE.ComponentRef
              local outCrefIdent::DAE.ComponentRef

              outCrefIdent = DAE.CREF_IDENT(ident, identType, subscriptLst)
          outCrefIdent
        end

        function makeUntypedCrefIdent(ident::DAE.Ident) ::DAE.ComponentRef
              local outCrefIdent::DAE.ComponentRef

              outCrefIdent = DAE.CREF_IDENT(ident, DAE.T_UNKNOWN_DEFAULT, nil)
          outCrefIdent
        end

         #= @author: adrpo
          This function creates a DAE.CREF_QUAL(ident, identType, subscriptLst, componentRef) =#
        function makeCrefQual(ident::DAE.Ident, identType::DAE.Type #= type of the identifier, without considering the subscripts =#, subscriptLst::List{<:DAE.Subscript}, componentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outCrefQual::DAE.ComponentRef

              local subCref::DAE.ComponentRef

               #=  subCref := shareCref(componentRef);
               =#
               #=  outCrefQual := shareCref(DAE.CREF_QUAL(ident, identType, subscriptLst, subCref));
               =#
              outCrefQual = DAE.CREF_QUAL(ident, identType, subscriptLst, componentRef)
          outCrefQual
        end

         #= /***************************************************/ =#
         #= /* transform to other types */ =#
         #= /***************************************************/ =#

         #= This function converts a ComponentRef to a Path, if possible.
          If the component reference contains subscripts, it will silently
          fail. =#
        function crefToPath(inComponentRef::DAE.ComponentRef) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local i::DAE.Ident
                  local p::Absyn.Path
                  local c::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = i, subscriptLst =  nil())  => begin
                    Absyn.IDENT(i)
                  end

                  DAE.CREF_QUAL(ident = i, subscriptLst =  nil(), componentRef = c)  => begin
                      p = crefToPath(c)
                    Absyn.QUALIFIED(i, p)
                  end
                end
              end
          outPath
        end

        function crefToPathIgnoreSubs(inComponentRef::DAE.ComponentRef) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local i::DAE.Ident
                  local p::Absyn.Path
                  local c::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = i)  => begin
                    Absyn.IDENT(i)
                  end

                  DAE.CREF_QUAL(ident = i, componentRef = c)  => begin
                      p = crefToPathIgnoreSubs(c)
                    Absyn.QUALIFIED(i, p)
                  end
                end
              end
          outPath
        end

         #= This function converts a Absyn.Path to a ComponentRef. =#
        function pathToCref(inPath::Absyn.Path) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local i::DAE.Ident
                  local c::DAE.ComponentRef
                  local p::Absyn.Path
                @match inPath begin
                  Absyn.IDENT(name = i)  => begin
                    makeCrefIdent(i, DAE.T_UNKNOWN_DEFAULT, nil)
                  end

                  Absyn.FULLYQUALIFIED(p)  => begin
                    pathToCref(p)
                  end

                  Absyn.QUALIFIED(name = i, path = p)  => begin
                      c = pathToCref(p)
                    makeCrefQual(i, DAE.T_UNKNOWN_DEFAULT, nil, c)
                  end
                end
              end
          outComponentRef
        end

         #=   author: Frenkel TUD
          generates a cref from DAE.Var =#
        function creffromVar(inVar::DAE.Var) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local name::String
                  local ty::DAE.Type
                @match inVar begin
                  DAE.TYPES_VAR(name = name, ty = ty)  => begin
                    makeCrefIdent(name, ty, nil)
                  end
                end
              end
          outComponentRef
        end

         #= Transform an ComponentRef into Absyn.ComponentRef. =#
        function unelabCref(inComponentRef::DAE.ComponentRef) ::Absyn.ComponentRef
              local outComponentRef::Absyn.ComponentRef

              outComponentRef = begin
                  local subs_1::List{Absyn.Subscript}
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr_1::Absyn.ComponentRef
                  local cr::DAE.ComponentRef
                   #=  iterators
                   =#
                @matchcontinue inComponentRef begin
                  DAE.CREF_ITER(ident = id, subscriptLst = subs)  => begin
                      subs_1 = unelabSubscripts(subs)
                    Absyn.CREF_IDENT(id, subs_1)
                  end

                  DAE.CREF_IDENT(ident = id, subscriptLst = subs)  => begin
                      subs_1 = unelabSubscripts(subs)
                    Absyn.CREF_IDENT(id, subs_1)
                  end

                  DAE.CREF_QUAL(ident = id, subscriptLst = subs, componentRef = cr)  => begin
                      cr_1 = unelabCref(cr)
                      subs_1 = unelabSubscripts(subs)
                    Absyn.CREF_QUAL(id, subs_1, cr_1)
                  end

                  _  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      print("ComponentReference.unelabCref failed on: " + printComponentRefStr(inComponentRef) + "\\n")
                    fail()
                  end
                end
              end
               #=  identifiers
               =#
               #=  qualified
               =#
          outComponentRef
        end

         #= Helper function to unelabCref, handles subscripts. =#
        function unelabSubscripts(inSubscriptLst::List{<:DAE.Subscript}) ::List{Absyn.Subscript}
              local outAbsynSubscriptLst::List{Absyn.Subscript}

              outAbsynSubscriptLst = begin
                  local xs_1::List{Absyn.Subscript}
                  local xs::List{DAE.Subscript}
                  local e_1::Absyn.Exp
                  local e::DAE.Exp
                   #=  empty list
                   =#
                @match inSubscriptLst begin
                   nil()  => begin
                    nil
                  end

                  DAE.WHOLEDIM(__) <| xs  => begin
                      xs_1 = unelabSubscripts(xs)
                    _cons(Absyn.NOSUB(), xs_1)
                  end

                  DAE.SLICE(exp = e) <| xs  => begin
                      xs_1 = unelabSubscripts(xs)
                      e_1 = Expression.unelabExp(e)
                    _cons(Absyn.SUBSCRIPT(e_1), xs_1)
                  end

                  DAE.INDEX(exp = e) <| xs  => begin
                      xs_1 = unelabSubscripts(xs)
                      e_1 = Expression.unelabExp(e)
                    _cons(Absyn.SUBSCRIPT(e_1), xs_1)
                  end

                  DAE.WHOLE_NONEXP(exp = e) <| xs  => begin
                      xs_1 = unelabSubscripts(xs)
                      e_1 = Expression.unelabExp(e)
                    _cons(Absyn.SUBSCRIPT(e_1), xs_1)
                  end
                end
              end
               #=  whole dimension
               =#
               #=  slices
               =#
               #=  indexes
               =#
          outAbsynSubscriptLst
        end

         #= Translates an Absyn cref to an untyped DAE cref. =#
        function toExpCref(absynCref::Absyn.ComponentRef) ::DAE.ComponentRef
              local daeCref::DAE.ComponentRef

              daeCref = begin
                @match absynCref begin
                  Absyn.CREF_IDENT(__)  => begin
                    makeCrefIdent(absynCref.name, DAE.T_UNKNOWN_DEFAULT, toExpCrefSubs(absynCref.subscripts))
                  end

                  Absyn.CREF_QUAL(__)  => begin
                    makeCrefQual(absynCref.name, DAE.T_UNKNOWN_DEFAULT, toExpCrefSubs(absynCref.subscripts), toExpCref(absynCref.componentRef))
                  end

                  Absyn.CREF_FULLYQUALIFIED(__)  => begin
                    toExpCref(absynCref.componentRef)
                  end

                  Absyn.WILD(__)  => begin
                    DAE.WILD()
                  end

                  Absyn.ALLWILD(__)  => begin
                    DAE.WILD()
                  end
                end
              end
          daeCref
        end

         #= Translates a list of Absyn subscripts to a list of untyped DAE subscripts. =#
        function toExpCrefSubs(absynSubs::List{<:Absyn.Subscript}) ::List{DAE.Subscript}
              local daeSubs::List{DAE.Subscript}

              local i::ModelicaInteger

              daeSubs = list(begin
                @match sub begin
                  Absyn.SUBSCRIPT(__)  => begin
                    DAE.INDEX(Expression.fromAbsynExp(sub.subscript))
                  end

                  Absyn.NOSUB(__)  => begin
                    DAE.WHOLEDIM()
                  end
                end
              end for sub in absynSubs)
          daeSubs
        end

         #= This function simply converts a ComponentRef to a String. =#
        function crefStr(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = stringDelimitList(toStringList(inComponentRef), if Flags.getConfigBool(Flags.MODELICA_OUTPUT)
                    "__"
                  else
                    "."
                  end)
          outString
        end

         #= Same as crefStr, but uses _ instead of .  =#
        function crefModelicaStr(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = stringDelimitList(toStringList(inComponentRef), "_")
          outString
        end

         #= @autor: adrpo
          Print a cref or none =#
        function printComponentRefOptStr(inComponentRefOpt::Option{<:DAE.ComponentRef}) ::String
              local outString::String

              outString = begin
                  local str::String
                  local cref::DAE.ComponentRef
                   #=  none
                   =#
                @match inComponentRefOpt begin
                  NONE()  => begin
                    "NONE()"
                  end

                  SOME(cref)  => begin
                      str = printComponentRefStr(cref)
                      str = "SOME(" + str + ")"
                    str
                  end
                end
              end
               #=  some
               =#
          outString
        end

         #= Print a ComponentRef.
          LS: print functions that return a string instead of printing
              Had to duplicate the huge printExp2 and modify.
              An alternative would be to implement sprint somehow
          which would need internal state, with reset and
              getString methods.
              Once these are tested and ok, the printExp above can
              be replaced by a call to these _str functions and
              printing the result. =#
        function printComponentRefStr(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = begin
                  local s::DAE.Ident
                  local str::DAE.Ident
                  local strrest::DAE.Ident
                  local strseb::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local b::Bool
                  local ix::ModelicaInteger
                   #=  Optimize -- a function call less
                   =#
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = s, subscriptLst =  nil())  => begin
                    s
                  end

                  DAE.CREF_IDENT(ident = s, subscriptLst = subs)  => begin
                      str = printComponentRef2Str(s, subs)
                    str
                  end

                  DAE.CREF_ITER(ident = s, index = ix, subscriptLst =  nil())  => begin
                    s + "/* iter index " + intString(ix) + " */"
                  end

                  DAE.CREF_ITER(ident = s, index = ix, subscriptLst = subs)  => begin
                      str = printComponentRef2Str(s, subs)
                    str + "/* iter index " + intString(ix) + " */"
                  end

                  DAE.CREF_QUAL(ident = s, subscriptLst = subs, componentRef = cr)  => begin
                      b = Config.modelicaOutput()
                      str = printComponentRef2Str(s, subs)
                      strrest = printComponentRefStr(cr)
                      strseb = if b
                            "__"
                          else
                            "."
                          end
                      str = stringAppendList(list(str, strseb, strrest))
                    str
                  end

                  DAE.WILD(__)  => begin
                    "_"
                  end
                end
              end
               #=  idents with subscripts
               =#
               #=  Optimize -- a function call less
               =#
               #=  idents with subscripts
               =#
               #=  Qualified - Modelica output - does not handle names with underscores
               =#
               #=  Qualified - non Modelica output
               =#
               #=  Wild
               =#
          outString
        end

         #= Like printComponentRefStr but also fixes the special dollar-sign variables =#
        function printComponentRefStrFixDollarDer(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = begin
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_QUAL(ident = "\$DER", subscriptLst =  nil(), componentRef = cr)  => begin
                    "der(" + printComponentRefStr(cr) + ")"
                  end

                  _  => begin
                      printComponentRefStr(inComponentRef)
                  end
                end
              end
          outString
        end

         #= Helper function to printComponentRefStr. =#
        function printComponentRef2Str(inIdent::DAE.Ident, inSubscriptLst::List{<:DAE.Subscript}) ::String
              local outString::String

              outString = begin
                  local s::DAE.Ident
                  local str::DAE.Ident
                  local strseba::DAE.Ident
                  local strsebb::DAE.Ident
                  local l::List{DAE.Subscript}
                  local b::Bool
                   #=  no subscripts
                   =#
                @match (inIdent, inSubscriptLst) begin
                  (s,  nil())  => begin
                    s
                  end

                  (s, l)  => begin
                      b = Config.modelicaOutput()
                      str = ExpressionDump.printListStr(l, ExpressionDump.printSubscriptStr, ",")
                      (strseba, strsebb) = if b
                            ("_L", "_R")
                          else
                            ("[", "]")
                          end
                      str = stringAppendList(list(s, strseba, str, strsebb))
                    str
                  end
                end
              end
               #=  some subscripts, Modelica output
               =#
               #=  some subscripts, non Modelica output
               =#
          outString
        end

         #= Function: debugPrintComponentRefTypeStr
        This function is equal to debugPrintComponentRefTypeStr with the extra feature that it
        prints the base type of each ComponentRef.
        NOTE Only used for debugging. =#
        function debugPrintComponentRefTypeStr(inComponentRef::DAE.ComponentRef) ::String
              local outString::String

              outString = begin
                  local s::DAE.Ident
                  local str::DAE.Ident
                  local str2::DAE.Ident
                  local strrest::DAE.Ident
                  local str_1::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                @match inComponentRef begin
                  DAE.WILD(__)  => begin
                    "_"
                  end

                  DAE.CREF_IDENT(ident = s, identType = ty, subscriptLst = subs)  => begin
                      str_1 = ExpressionDump.printListStr(subs, ExpressionDump.debugPrintSubscriptStr, ", ")
                      str = s + (if stringLength(str_1) > 0
                            "[" + str_1 + "]"
                          else
                            ""
                          end)
                      str2 = Types.unparseType(ty)
                      str = stringAppendList(list(str, " [", str2, "]"))
                    str
                  end

                  DAE.CREF_QUAL(ident = s, identType = ty, subscriptLst = subs, componentRef = cr)  => begin
                      if Config.modelicaOutput()
                        str = printComponentRef2Str(s, subs)
                        str2 = Types.unparseType(ty)
                        strrest = debugPrintComponentRefTypeStr(cr)
                        str = stringAppendList(list(str, " [", str2, "] ", "__", strrest))
                      else
                        str_1 = ExpressionDump.printListStr(subs, ExpressionDump.debugPrintSubscriptStr, ", ")
                        str = s + (if stringLength(str_1) > 0
                              "[" + str_1 + "]"
                            else
                              ""
                            end)
                        str2 = Types.unparseType(ty)
                        strrest = debugPrintComponentRefTypeStr(cr)
                        str = stringAppendList(list(str, " [", str2, "] ", ".", strrest))
                      end
                    str
                  end
                end
              end
          outString
        end

         #= /***************************************************/ =#
         #= /* Compare  */ =#
         #= /***************************************************/ =#

         #= author: Frenkel TUD
          Returns true if the ComponentRefs has the same name (the last identifier). =#
        function crefLastIdentEqual(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local equal::Bool

              local id1::DAE.Ident
              local id2::DAE.Ident

              id1 = crefLastIdent(cr1)
              id2 = crefLastIdent(cr2)
              equal = stringEq(id1, id2)
          equal
        end

         #= author: Frenkel TUD
          Returns true if the ComponentRefs have the same first Cref. =#
        function crefFirstCrefEqual(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local equal::Bool

              local pcr1::DAE.ComponentRef
              local pcr2::DAE.ComponentRef

              pcr1 = crefFirstCref(cr1)
              pcr2 = crefFirstCref(cr2)
              equal = crefEqual(pcr1, pcr2)
          equal
        end

         #= author: Frenkel TUD
          Returns true if the ComponentRefs have the same first Cref. =#
        function crefFirstCrefLastCrefEqual(cr1::DAE.ComponentRef #= First Cref =#, cr2::DAE.ComponentRef #= Last Cref =#) ::Bool
              local equal::Bool

              local pcr1::DAE.ComponentRef
              local pcr2::DAE.ComponentRef

              pcr1 = crefFirstCref(cr1)
              pcr2 = crefLastCref(cr2)
              equal = crefEqual(pcr1, pcr2)
          equal
        end

         #= Returns true if the first identifier in both crefs are the same, otherwise false. =#
        function crefFirstIdentEqual(inCref1::DAE.ComponentRef, inCref2::DAE.ComponentRef) ::Bool
              local outEqual::Bool

              local id1::DAE.Ident
              local id2::DAE.Ident

              id1 = crefFirstIdent(inCref1)
              id2 = crefFirstIdent(inCref2)
              outEqual = stringEq(id1, id2)
          outEqual
        end

      module CompareWithSubsType 
        using ExportAll
        
        const WithoutSubscripts = 1
        const WithGenericSubscript = 2
        const WithGenericSubscriptNotAlphabetic = 3
        const WithIntSubscrip = 4
        
        @exportAll()
      end

        module CompareWithGenericSubscript

          using MetaModelica
          #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
          using ExportAll

              import CompareWithSubsType
              
              compareSubscript = CompareWithSubsType.WithGenericSubscript::Int64

              function compare(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
                    local res::ModelicaInteger

                    res = begin
                      @match (cr1, cr2) begin
                        (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
                            res = stringCompare(cr1.ident, cr2.ident)
                            if compareSubscript == CompareWithSubsType.WithoutSubscripts || res != 0
                              return
                            end
                          compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                        end

                        (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
                            res = stringCompare(cr1.ident, cr2.ident)
                            if res != 0
                              return
                            end
                            if compareSubscript != CompareWithSubsType.WithoutSubscripts
                              res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                              if res != 0
                                return
                              end
                            end
                          compare(cr1.componentRef, cr2.componentRef)
                        end

                        (DAE.CREF_QUAL(__), DAE.CREF_IDENT(__))  => begin
                            res = stringCompare(cr1.ident, cr2.ident)
                            if res != 0
                              return
                            end
                            if compareSubscript != CompareWithSubsType.WithoutSubscripts
                              res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                            end
                            if res != 0
                              return
                            end
                          1
                        end

                        (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
                            res = stringCompare(cr1.ident, cr2.ident)
                            if res != 0
                              return
                            end
                            if compareSubscript != CompareWithSubsType.WithoutSubscripts
                              res = compareSubs(cr1.subscriptLst, cr2.subscriptLst)
                            end
                            if res != 0
                              return
                            end
                          -1
                        end
                      end
                    end
                res
              end

              function compareSubs(ss1::List{<:DAE.Subscript}, ss2::List{<:DAE.Subscript}) ::ModelicaInteger
                    local res::ModelicaInteger = 0

                    local ss::List{DAE.Subscript} = ss2
                    local s2::DAE.Subscript
                    local i1::ModelicaInteger
                    local i2::ModelicaInteger
                    local e1::DAE.Exp
                    local e2::DAE.Exp

                    for s1 in ss1
                      if listEmpty(ss)
                        res = -1
                        return res
                      end
                      @match _cons(s2, ss) = ss
                      if compareSubscript == CompareWithSubsType.WithGenericSubscript
                        res = stringCompare(ExpressionDump.printSubscriptStr(s1), ExpressionDump.printSubscriptStr(s2))
                      elseif compareSubscript == CompareWithSubsType.WithGenericSubscriptNotAlphabetic
                        res = Expression.compareSubscripts(s1, s2)
                      else
                        i1 = Expression.subscriptInt(s1)
                        i2 = Expression.subscriptInt(s2)
                        res = if i1 < i2
                              -1
                            elseif (i1 > i2)
                                  1
                            else
                              0
                            end
                      end
                      if res != 0
                        return res
                      end
                    end
                    if ! listEmpty(ss)
                      res = 1
                    end
                res
              end

          #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
          @exportAll()
        end

        module CompareWithGenericSubscriptNotAlphabetic


          using MetaModelica
          #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
          using ExportAll


          using CompareWithGenericSubscript
          
          compareSubscript = CompareWithSubsType.WithGenericSubscriptNotAlphabetic

          #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
          @exportAll()
        end

        module CompareWithoutSubscripts


          using MetaModelica
          #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
          using ExportAll

          using CompareWithGenericSubscript

          compareSubscript = CompareWithSubsType.WithoutSubscripts

          #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
          @exportAll()
        end

        module CompareWithIntSubscript


          using MetaModelica
          #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
          using ExportAll

          using CompareWithGenericSubscript
          
          compareSubscript = CompareWithSubsType.WithIntSubscript

          #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
          @exportAll()
        end

         #= A sorting function (greatherThan) for crefs =#
        function crefSortFunc(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local greaterThan::Bool
              greaterThan = CompareWithGenericSubscript.compare(cr1, cr2) > 0
          greaterThan
        end

         #= A sorting function for crefs =#
        function crefCompareGeneric(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
              local comp::ModelicaInteger
              comp = CompareWithGenericSubscript.compare(cr1, cr2)
          comp
        end

         #= A sorting function for crefs =#
        function crefCompareIntSubscript(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
              local comp::ModelicaInteger

              comp = CompareWithIntSubscript.compare(cr1, cr2)
          comp
        end

         #= A sorting function for crefs =#
        function crefCompareGenericNotAlphabetic(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
              local comp::ModelicaInteger

              comp = CompareWithGenericSubscriptNotAlphabetic.compare(cr1, cr2)
          comp
        end

         #= mahge:
          Compares two crefs lexically. Subscripts are treated as if they are
          they are at the end of the whole component reference.
          e.g. r[1].i is greater than r[2].a.
          returns true if the first cref is greater than the second =#
        function crefLexicalGreaterSubsAtEnd(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local isGreater::Bool

              isGreater = crefLexicalCompareSubsAtEnd(cr1, cr2) > 0
          isGreater
        end

         #= mahge:
          Compares two crefs lexically. Subscripts are treated as if they are
          they are at the end of the whole component reference.
          e.g. r[1].i is greater than r[2].a.
          returns value is same as C strcmp. 0 if equal, 1 if first is greater, -1 otherwise =#
        function crefLexicalCompareSubsAtEnd(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::ModelicaInteger
              local res::ModelicaInteger

              local subs1::List{ModelicaInteger}
              local subs2::List{ModelicaInteger}

              res = CompareWithoutSubscripts.compare(cr1, cr2)
              if res != 0
                return res
              end
              subs1 = Expression.subscriptsInt(crefSubs(cr1))
              subs2 = Expression.subscriptsInt(crefSubs(cr2))
              res = crefLexicalCompareSubsAtEnd2(subs1, subs2)
          res
        end

         #= mahge:
          Helper function for crefLexicalCompareubsAtEnd
          compares subs. However only if the crefs with out subs are equal.
          (i.e. identsCompared is 0)
          otherwise just returns =#
        function crefLexicalCompareSubsAtEnd2(inSubs1::List{<:ModelicaInteger}, inSubs2::List{<:ModelicaInteger}) ::ModelicaInteger
              local res::ModelicaInteger = 0

              local rest::List{ModelicaInteger} = inSubs2

              for i in inSubs1
                @match _cons(res, rest) = rest
                res = if i > res
                      1
                    elseif (i < res)
                          -1
                    else
                      0
                    end
                if res != 0
                  return res
                end
              end
          res
        end

         #= author: PA
          Returns true if second arg is a sub component ref of first arg.
          For instance, b.c. is a sub_component of a.b.c. =#
        function crefContainedIn(containerCref::DAE.ComponentRef #= the cref that might contain =#, containedCref::DAE.ComponentRef #= cref that might be contained =#) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local full::DAE.ComponentRef
                  local partOf::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local res::Bool
                   #=  a qualified cref cannot be contained in an ident cref.
                   =#
                @matchcontinue (containerCref, containedCref) begin
                  (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
                    false
                  end

                  (full, partOf)  => begin
                      @match true = crefEqualNoStringCompare(full, partOf)
                    true
                  end

                  (full && DAE.CREF_QUAL(componentRef = cr2), partOf)  => begin
                      @match false = crefEqualNoStringCompare(full, partOf)
                      res = crefContainedIn(cr2, partOf)
                    res
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  see if they are equal
               =#
               #=  dive into
               =#
               #=  anything else is false
               =#
          outBoolean
        end

         #= author: PA
          Returns true if prefixCref is a prefix of fullCref
          For example, a.b is a prefix of a.b.c.
          adrpo 2010-10-07,
            added also that a.b.c is a prefix of a.b.c[1].*! =#
        function crefPrefixOf(prefixCref::DAE.ComponentRef, fullCref::DAE.ComponentRef) ::Bool
              local outPrefixOf::Bool

              outPrefixOf = begin
                @match (prefixCref, fullCref) begin
                  (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
                    prefixCref.ident == fullCref.ident && Expression.subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst) && crefPrefixOf(prefixCref.componentRef, fullCref.componentRef)
                  end

                  (DAE.CREF_IDENT(subscriptLst =  nil()), DAE.CREF_QUAL(__))  => begin
                    prefixCref.ident == fullCref.ident
                  end

                  (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
                    prefixCref.ident == fullCref.ident && Expression.subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst)
                  end

                  (DAE.CREF_IDENT(subscriptLst =  nil()), DAE.CREF_IDENT(__))  => begin
                    stringEq(prefixCref.ident, fullCref.ident)
                  end

                  (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
                    prefixCref.ident == fullCref.ident && Expression.subscriptEqual(prefixCref.subscriptLst, fullCref.subscriptLst)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  both are qualified, dive into
               =#
               #=  adrpo: 2010-10-07: first is an ID, second is qualified, see if one is prefix of the other
               =#
               #=                     even if the first one DOESN'T HAVE SUBSCRIPTS!
               =#
               #=  first is an ID, second is qualified, see if one is prefix of the other
               =#
               #=  adrpo: 2010-10-07: first is an ID, second is an ID, see if one is prefix of the other
               =#
               #=                     even if the first one DOESN'T HAVE SUBSCRIPTS!
               =#
               #=  they are not a prefix of one-another
               =#
          outPrefixOf
        end

         #= author: PA
          Returns true if prefixCref is a prefix of fullCref
          For example, a.b is a prefix of a.b.c.
          This function ignores the subscripts =#
        function crefPrefixOfIgnoreSubscripts(prefixCref::DAE.ComponentRef, fullCref::DAE.ComponentRef) ::Bool
              local outPrefixOf::Bool

              outPrefixOf = begin
                @match (prefixCref, fullCref) begin
                  (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
                    prefixCref.ident == fullCref.ident && crefPrefixOfIgnoreSubscripts(prefixCref.componentRef, fullCref.componentRef)
                  end

                  (DAE.CREF_IDENT(__), DAE.CREF_QUAL(__))  => begin
                    prefixCref.ident == fullCref.ident
                  end

                  (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
                    prefixCref.ident == fullCref.ident
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  both are qualified, dive into
               =#
               #=  first is an ID, second is qualified, see if one is prefix of the other
               =#
               #=  they are not a prefix of one-another
               =#
          outPrefixOf
        end

         #= negation of crefPrefixOf =#
        function crefNotPrefixOf(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                @match (cr1, cr2) begin
                  (DAE.CREF_QUAL(__), DAE.CREF_IDENT(__))  => begin
                    true
                  end

                  _  => begin
                      ! crefPrefixOf(cr1, cr2)
                  end
                end
              end
               #=  first is qualified, second is an unqualified ident, return false!
               =#
          outBoolean
        end

         #= Returns true if two component references are equal.
          No string comparison of unparsed crefs is performed! =#
        function crefEqual(inComponentRef1::DAE.ComponentRef, inComponentRef2::DAE.ComponentRef) ::Bool
              local outBoolean::Bool

              outBoolean = crefEqualNoStringCompare(inComponentRef1, inComponentRef2)
          outBoolean
        end

         #= returns true if the cref is in the list of crefs =#
        function crefInLst(cref::DAE.ComponentRef, lst::List{<:DAE.ComponentRef}) ::Bool
              local b::Bool

              b = ListUtil.isMemberOnTrue(cref, lst, crefEqual)
          b
        end

         #= returns true if the cref is not in the list of crefs =#
        function crefNotInLst(cref::DAE.ComponentRef, lst::List{<:DAE.ComponentRef}) ::Bool
              local b::Bool

              b = ! ListUtil.isMemberOnTrue(cref, lst, crefEqual)
          b
        end

         #= Returns true if two component references are equal,
          comparing strings if no other solution is found =#
        function crefEqualVerySlowStringCompareDoNotUse(inComponentRef1::DAE.ComponentRef, inComponentRef2::DAE.ComponentRef) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local n1::DAE.Ident
                  local n2::DAE.Ident
                  local s1::DAE.Ident
                  local s2::DAE.Ident
                  local idx1::List{DAE.Subscript}
                  local idx2::List{DAE.Subscript}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                   #=  check for pointer equality first, if they point to the same thing, they are equal
                   =#
                @matchcontinue (inComponentRef1, inComponentRef2) begin
                  (_, _)  => begin
                      @match true = referenceEq(inComponentRef1, inComponentRef2)
                    true
                  end

                  (DAE.CREF_IDENT(ident = n1, subscriptLst =  nil()), DAE.CREF_IDENT(ident = n2, subscriptLst =  nil()))  => begin
                      @match true = stringEq(n1, n2)
                    true
                  end

                  (DAE.CREF_IDENT(ident = n1, subscriptLst = idx1 && _ <| _), DAE.CREF_IDENT(ident = n2, subscriptLst = idx2 && _ <| _))  => begin
                      @match true = stringEq(n1, n2)
                      @match true = Expression.subscriptEqual(idx1, idx2)
                    true
                  end

                  (DAE.CREF_IDENT(ident = n1, subscriptLst =  nil()), DAE.CREF_IDENT(ident = n2, subscriptLst = idx2 && _ <| _))  => begin
                      @match 0 = System.stringFind(n1, n2)
                      s1 = n2 + "[" + ExpressionDump.printListStr(idx2, ExpressionDump.printSubscriptStr, ",") + "]"
                      @match true = stringEq(s1, n1)
                    true
                  end

                  (DAE.CREF_IDENT(ident = n1, subscriptLst = idx2 && _ <| _), DAE.CREF_IDENT(ident = n2, subscriptLst =  nil()))  => begin
                      @match 0 = System.stringFind(n2, n1)
                      s1 = n1 + "[" + ExpressionDump.printListStr(idx2, ExpressionDump.printSubscriptStr, ",") + "]"
                      @match true = stringEq(s1, n2)
                    true
                  end

                  (DAE.CREF_QUAL(ident = n1, subscriptLst = idx1, componentRef = cr1), DAE.CREF_QUAL(ident = n2, subscriptLst = idx2, componentRef = cr2))  => begin
                      @match true = stringEq(n1, n2)
                      @match true = crefEqualVerySlowStringCompareDoNotUse(cr1, cr2)
                      @match true = Expression.subscriptEqual(idx1, idx2)
                    true
                  end

                  (cr1 && DAE.CREF_QUAL(ident = n1), cr2 && DAE.CREF_IDENT(ident = n2))  => begin
                      @match 0 = System.stringFind(n2, n1)
                      s1 = printComponentRefStr(cr1)
                      s2 = printComponentRefStr(cr2)
                      @match true = stringEq(s1, s2)
                    true
                  end

                  (cr1 && DAE.CREF_IDENT(ident = n1), cr2 && DAE.CREF_QUAL(ident = n2))  => begin
                      @match 0 = System.stringFind(n1, n2)
                      s1 = printComponentRefStr(cr1)
                      s2 = printComponentRefStr(cr2)
                      @match true = stringEq(s1, s2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  simple identifiers
               =#
               #=  BZ 2009-12
               =#
               #=  For some reason in some examples we get crefs on different forms.
               =#
               #=  the compare can be crefEqual(CREF_IDENT(\"mycref\",_,{1,2,3}),CREF_IDENT(\"mycref[1,2,3]\",_,{}))
               =#
               #=  I do belive this has something to do with variable replacement and BackendDAE.
               =#
               #=  TODO: investigate reason, until then keep as is.
               =#
               #=  I do believe that this is the same bug as adrians qual-ident bug below.
               =#
               #=  n2 should be first in n1!
               =#
               #=  n1 should be first in n2!
               =#
               #=  qualified crefs
               =#
               #=  this is a VERY expensive case! Do we NEED IT??!!
               =#
               #=  There is a bug here somewhere or in MetaModelica Compiler (MMC).
               =#
               #=  Therefore as a last resort, print the strings and compare.
               =#
               #=  adrpo: this is really not needed BUT unfortunately IT IS as
               =#
               #=         QUAL(x, IDENT(y)) == IDENT(x.y)
               =#
               #=         somewhere in the compiler the lhs is replaced by the rhs
               =#
               #=         and makes this case needed! THIS SHOULD BE FIXED!! TODO! FIXME!
               =#
               #=         NOTE: THIS IS NOT A BUG IN MMC!
               =#
               #= /* adrpo: comment this and try to make it work faster with the two cases below!
                  case (cr1 as DAE.CREF_QUAL(ident = n1),cr2 as DAE.CREF_IDENT)
                    equation
                      s1 = printComponentRefStr(cr1);
                      s2 = printComponentRefStr(cr2);
                      true = stringEq(s1, s2);
                       debug_print(\"cr1\", cr1);
                       debug_print(\"cr2\", cr2);
                       enableTrace();
                    then
                      true;
                  */ =#
               #=  the following two cases replaces the one below
               =#
               #=  right cref is stringified!
               =#
               #=  n1 should be first in n2!
               =#
               #=  left cref is stringified!
               =#
               #=  n2 should be first in n1!
               =#
               #=  the crefs are not equal!
               =#
          outBoolean
        end

         #= Returns true if two component references are equal!
          IMPORTANT! do not use this function if you have
          stringified components, meaning this function will
          return false for: cref1: QUAL(x, IDENT(x)) != cref2: IDENT(x.y) =#
        function crefEqualNoStringCompare(inCref1::DAE.ComponentRef, inCref2::DAE.ComponentRef) ::Bool
              local outEqual::Bool

              if referenceEq(inCref1, inCref2)
                outEqual = true
                return outEqual
              end
              outEqual = begin
                @match (inCref1, inCref2) begin
                  (DAE.CREF_IDENT(__), DAE.CREF_IDENT(__))  => begin
                    inCref1.ident == inCref2.ident && Expression.subscriptEqual(inCref1.subscriptLst, inCref2.subscriptLst)
                  end

                  (DAE.CREF_QUAL(__), DAE.CREF_QUAL(__))  => begin
                    inCref1.ident == inCref2.ident && crefEqualNoStringCompare(inCref1.componentRef, inCref2.componentRef) && Expression.subscriptEqual(inCref1.subscriptLst, inCref2.subscriptLst)
                  end

                  _  => begin
                      false
                  end
                end
              end
          outEqual
        end

         #= author: PA
          Checks if two crefs are equal and if
          so returns the cref, otherwise fail. =#
        function crefEqualReturn(cr::DAE.ComponentRef, cr2::DAE.ComponentRef) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              @match true = crefEqualNoStringCompare(cr, cr2)
              ocr = cr
          ocr
        end

         #= Checks if two crefs are equal, without considering their last subscripts. =#
        function crefEqualWithoutLastSubs(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local res::Bool

              res = crefEqualNoStringCompare(crefStripLastSubs(cr1), crefStripLastSubs(cr2))
          res
        end

         #= Checks if two crefs are equal, without considering their subscripts. =#
        function crefEqualWithoutSubs(cr1::DAE.ComponentRef, cr2::DAE.ComponentRef) ::Bool
              local res::Bool

              res = crefEqualWithoutSubs2(referenceEq(cr1, cr2), cr1, cr2)
          res
        end

        function crefEqualWithoutSubs2(refEq::Bool, icr1::DAE.ComponentRef, icr2::DAE.ComponentRef) ::Bool
              local res::Bool

              res = begin
                  local n1::DAE.Ident
                  local n2::DAE.Ident
                  local r::Bool
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                @match (refEq, icr1, icr2) begin
                  (true, _, _)  => begin
                    true
                  end

                  (_, DAE.CREF_IDENT(ident = n1), DAE.CREF_IDENT(ident = n2))  => begin
                    stringEq(n1, n2)
                  end

                  (_, DAE.CREF_QUAL(ident = n1, componentRef = cr1), DAE.CREF_QUAL(ident = n2, componentRef = cr2))  => begin
                      r = stringEq(n1, n2)
                      r = if r
                            crefEqualWithoutSubs2(referenceEq(cr1, cr2), cr1, cr2)
                          else
                            false
                          end
                    r
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if ComponentRef is an ident,
         i.e a => true , a.b => false =#
        function crefIsIdent(cr::DAE.ComponentRef) ::Bool
              local res::Bool

              res = begin
                @match cr begin
                  DAE.CREF_IDENT(__)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          res
        end

         #= returns true if ComponentRef is not an ident,
         i.e a => false , a.b => true =#
        function crefIsNotIdent(cr::DAE.ComponentRef) ::Bool
              local res::Bool

              res = begin
                @match cr begin
                  DAE.CREF_IDENT(__)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          res
        end

         #=
        function isRecord
          returns true if the type of the last ident is a record =#
        function isRecord(cr::DAE.ComponentRef) ::Bool
              local b::Bool

              b = begin
                  local comp::DAE.ComponentRef
                @match cr begin
                  DAE.CREF_IDENT(identType = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)))  => begin
                    true
                  end

                  DAE.CREF_QUAL(componentRef = comp)  => begin
                    isRecord(comp)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #= /* this case is false because it is not the last ident.
                  case(DAE.CREF_QUAL(identType = DAE.T_COMPLEX(complexClassType=ClassInf.RECORD(_)))) then true;*/ =#
          b
        end

         #= returns true if cref is elemnt of an array =#
        function isArrayElement(cr::DAE.ComponentRef) ::Bool
              local b::Bool

              b = begin
                  local comp::DAE.ComponentRef
                @match cr begin
                  DAE.CREF_IDENT(identType = DAE.T_ARRAY(__))  => begin
                    true
                  end

                  DAE.CREF_QUAL(identType = DAE.T_ARRAY(__))  => begin
                    true
                  end

                  DAE.CREF_QUAL(componentRef = comp)  => begin
                    isArrayElement(comp)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isPreCref(cr::DAE.ComponentRef) ::Bool
              local b::Bool

              b = begin
                @match cr begin
                  DAE.CREF_QUAL(ident = DAE.preNamePrefix)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isPreviousCref(cr::DAE.ComponentRef) ::Bool
              local b::Bool

              b = begin
                @match cr begin
                  DAE.CREF_QUAL(ident = DAE.previousNamePrefix)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isStartCref(cr::DAE.ComponentRef) ::Bool
              local b::Bool

              b = begin
                @match cr begin
                  DAE.CREF_QUAL(ident = DAE.startNamePrefix)  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function popPreCref(inCR::DAE.ComponentRef) ::DAE.ComponentRef
              local outCR::DAE.ComponentRef

              outCR = begin
                  local cr::DAE.ComponentRef
                @match inCR begin
                  DAE.CREF_QUAL(ident = "\$PRE", componentRef = cr)  => begin
                    cr
                  end

                  _  => begin
                      inCR
                  end
                end
              end
          outCR
        end

        function popCref(inCR::DAE.ComponentRef) ::DAE.ComponentRef
              local outCR::DAE.ComponentRef

              outCR = begin
                  local cr::DAE.ComponentRef
                @match inCR begin
                  DAE.CREF_QUAL(componentRef = cr)  => begin
                    cr
                  end

                  _  => begin
                      inCR
                  end
                end
              end
          outCR
        end

         #= This function returns true for component references that
          are arrays and references the first element of the array.
          like for instance a.b{1,1} and a{1} returns true but
          a.b{1,2} or a{2} returns false. =#
        function crefIsFirstArrayElt(inComponentRef::DAE.ComponentRef) ::Bool
              local outBoolean::Bool

              outBoolean = begin
                  local subs::List{DAE.Subscript}
                  local exps::List{DAE.Exp}
                  local cr::DAE.ComponentRef
                @matchcontinue inComponentRef begin
                  cr  => begin
                      if stringEqual(Config.simCodeTarget(), "Cpp")
                        @match (@match _cons(_, _) = subs) = crefLastSubs(cr)
                      else
                        @match (@match _cons(_, _) = subs) = crefSubs(cr)
                      end
                    ListUtil.mapAllValueBool(subs, Expression.subscriptIsFirst, true)
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  fails if any mapped functions returns false
               =#
          outBoolean
        end

         #= Function: crefHaveSubs
          Checks whether Componentref has any subscripts, recursive  =#
        function crefHaveSubs(icr::DAE.ComponentRef) ::Bool
              local ob::Bool

              ob = begin
                  local cr::DAE.ComponentRef
                  local b::Bool
                  local str::DAE.Ident
                  local idx::ModelicaInteger
                @matchcontinue icr begin
                  DAE.CREF_QUAL(subscriptLst = _ <| _)  => begin
                    true
                  end

                  DAE.CREF_IDENT(subscriptLst = _ <| _)  => begin
                    true
                  end

                  DAE.CREF_IDENT(ident = str, subscriptLst =  nil())  => begin
                      idx = System.stringFind(str, "[")
                      if ! idx > 0
                        fail()
                      end
                    true
                  end

                  DAE.CREF_QUAL(subscriptLst =  nil(), componentRef = cr)  => begin
                      b = crefHaveSubs(cr)
                    b
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  for stringified crefs!
               =#
               #=  (-1 on failure)
               =#
               #=  index should be more than 0!
               =#
          ob
        end

         #= returns true if the subscripts of the cref results in a scalar variable.
        For example given Real x[3,3]
          x[1,2] has scalar subscripts
          x[1] has not scalar subscripts
          x[:,1] has not scalar subscripts
          x[{1,2},1] has not scalar subscripts
         =#
        function crefHasScalarSubscripts(cr::DAE.ComponentRef) ::Bool
              local hasScalarSubs::Bool

              hasScalarSubs = begin
                  local subs::List{DAE.Subscript}
                  local tp::DAE.Type
                  local dims::DAE.Dimensions
                   #= /* No subscripts */ =#
                @matchcontinue cr begin
                  _  => begin
                      @match nil = crefLastSubs(cr)
                    true
                  end

                  _  => begin
                      @match (@match _cons(_, _) = subs) = crefLastSubs(cr)
                      @match true = Expression.subscriptConstants(subs)
                      tp = crefLastType(cr)
                      dims = Expression.arrayDimension(tp)
                      @match true = listLength(dims) <= listLength(subs)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #= /* constant Subscripts that match type => true */ =#
               #=  Since all subscripts are constants, sufficient to compare length of dimensions
               =#
               #=  Dimensions may be removed when a component is instantiated if it has
               =#
               #=  constant subscripts though, so it may have more subscripts than
               =#
               #=  dimensions.
               =#
               #= /* All other cases are false */ =#
          hasScalarSubs
        end

         #=  =#
        function crefIsScalarWithAllConstSubs(inCref::DAE.ComponentRef) ::Bool
              local isScalar::Bool

              isScalar = begin
                  local res::Bool
                  local subs::List{DAE.Subscript}
                  local dims::List{DAE.Dimension}
                  local tempcrefs::List{DAE.ComponentRef}
                  local ndim::ModelicaInteger
                  local nsub::ModelicaInteger
                @matchcontinue inCref begin
                  _  => begin
                      @match nil = crefSubs(inCref)
                    true
                  end

                  _  => begin
                      @match (@match _cons(_, _) = subs) = crefSubs(inCref)
                      dims = crefDims(inCref)
                      @match true = listLength(dims) <= listLength(subs)
                      @match true = Expression.subscriptConstants(subs)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  Dimensions may be removed when a component is instantiated if it has
               =#
               #=  constant subscripts though, so it may have more subscripts than
               =#
               #=  dimensions.
               =#
               #=  mahge: TODO: Does this still happen?
               =#
          isScalar
        end

         #=  =#
        function crefIsScalarWithVariableSubs(inCref::DAE.ComponentRef) ::Bool
              local isScalar::Bool

              isScalar = begin
                  local res::Bool
                  local subs::List{DAE.Subscript}
                  local dims::List{DAE.Dimension}
                  local tempcrefs::List{DAE.ComponentRef}
                  local ndim::ModelicaInteger
                  local nsub::ModelicaInteger
                @matchcontinue inCref begin
                  _  => begin
                      @match (@match _cons(_, _) = subs) = crefSubs(inCref)
                      dims = crefDims(inCref)
                      @match true = listLength(dims) <= listLength(subs)
                      @match false = Expression.subscriptConstants(subs)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  Dimensions may be removed when a component is instantiated if it has
               =#
               #=  constant subscripts though, so it may have more subscripts than
               =#
               #=  dimensions.
               =#
               #=  mahge: TODO: Does this still happen?
               =#
          isScalar
        end

         #=  A function to check if a cref contains a [:] wholedim element in the subscriptlist.
         =#
        function containWholeDim(inRef::DAE.ComponentRef) ::Bool
              local wholedim::Bool

              wholedim = begin
                  local cr::DAE.ComponentRef
                  local ssl::List{DAE.Subscript}
                  local name::DAE.Ident
                  local ty::DAE.Type
                @match inRef begin
                  DAE.CREF_IDENT(_, ty, ssl)  => begin
                      wholedim = containWholeDim2(ssl, ty)
                    wholedim
                  end

                  DAE.CREF_QUAL(_, _, _, cr)  => begin
                      wholedim = containWholeDim(cr)
                    wholedim
                  end

                  _  => begin
                      false
                  end
                end
              end
          wholedim
        end

        function traverseCref(cref::DAE.ComponentRef, func::FuncType, argIn::Type_a) ::Type_a
              local argOut::Type_a

              argOut = begin
                  local cr::DAE.ComponentRef
                  local arg::Type_a
                @matchcontinue (cref, func, argIn) begin
                  (DAE.CREF_IDENT(_, _, _), _, _)  => begin
                      arg = func(cref, argIn)
                    arg
                  end

                  (DAE.CREF_QUAL(_, _, _, cr), _, _)  => begin
                      arg = func(cref, argIn)
                    traverseCref(cr, func, arg)
                  end

                  _  => begin
                        print("traverseCref failed!")
                      fail()
                  end
                end
              end
          argOut
        end

         #= traverse function to check if one of the crefs is a record =#
        function crefIsRec(cref::DAE.ComponentRef, isRecIn::Bool) ::Bool
              local isRec::Bool

               #=  is this case the last ident needs a consideration
               =#
              isRec = isRecIn || Types.isRecord(crefLastType(cref))
          isRec
        end

         #=
          A function to check if a cref contains a [:] wholedim element in the subscriptlist. =#
        function containWholeDim2(inRef::List{<:DAE.Subscript}, inType::DAE.Type) ::Bool
              local wholedim::Bool

              wholedim = begin
                  local ss::DAE.Subscript
                  local ssl::List{DAE.Subscript}
                  local name::DAE.Ident
                  local b::Bool
                  local tty::DAE.Type
                  local ad::DAE.Dimensions
                  local es1::DAE.Exp
                @matchcontinue (inRef, inType) begin
                  ( nil(), _)  => begin
                    false
                  end

                  (DAE.WHOLEDIM(__) <| _, DAE.T_ARRAY(__))  => begin
                    true
                  end

                  (DAE.SLICE(es1) <| _, DAE.T_ARRAY(dims = ad))  => begin
                      @match true = containWholeDim3(es1, ad)
                    true
                  end

                  (_ <| ssl, DAE.T_ARRAY(tty, ad))  => begin
                      ad = ListUtil.stripFirst(ad)
                      b = containWholeDim2(ssl, DAE.T_ARRAY(tty, ad))
                    b
                  end

                  (_ <| ssl, _)  => begin
                      wholedim = containWholeDim2(ssl, inType)
                    wholedim
                  end
                end
              end
          wholedim
        end

         #= Verify that a slice adresses all dimensions =#
        function containWholeDim3(inExp::DAE.Exp, ad::DAE.Dimensions) ::Bool
              local ob::Bool

              ob = begin
                  local expl::List{DAE.Exp}
                  local x1::ModelicaInteger
                  local x2::ModelicaInteger
                  local d::DAE.Dimension
                @matchcontinue (inExp, ad) begin
                  (DAE.ARRAY(array = expl), d <| _)  => begin
                      x1 = listLength(expl)
                      x2 = Expression.dimensionSize(d)
                      @match true = intEq(x1, x2)
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
          ob
        end

         #= /***************************************************/ =#
         #= /* Getter  */ =#
         #= /***************************************************/ =#

         #= mahge: This function is used to get the first element in
        an array cref if the cref was to be expanded. e.g.
             (a->nonarray, b->array) given a.b[1]   return a.b[1].
             (a->nonarray, b->array) given a.b      return a.b[1].
             (a->array, b->array) given a[1].b   return a[1].b[1]
             (a->array, b->array) given a[2].b   return a[2].b[1]
          i.e essentially filling the missing subs with 1.
         =#
        function crefArrayGetFirstCref(inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local cr::DAE.ComponentRef
                  local dims::List{DAE.Dimension}
                  local subs::List{DAE.Subscript}
                  local newsubs::List{DAE.Subscript}
                  local diff::ModelicaInteger
                  local ty::DAE.Type
                  local i::DAE.Ident
                @match inComponentRef begin
                  DAE.CREF_IDENT(i, ty, subs)  => begin
                      dims = Types.getDimensions(ty)
                      diff = listLength(dims) - listLength(subs)
                      newsubs = ListUtil.fill(DAE.INDEX(DAE.ICONST(1)), diff)
                      subs = listAppend(subs, newsubs)
                    DAE.CREF_IDENT(i, ty, subs)
                  end

                  DAE.CREF_QUAL(i, ty, subs, cr)  => begin
                      dims = Types.getDimensions(ty)
                      diff = listLength(dims) - listLength(subs)
                      newsubs = ListUtil.fill(DAE.INDEX(DAE.ICONST(1)), diff)
                      subs = listAppend(subs, newsubs)
                      cr = crefArrayGetFirstCref(cr)
                    DAE.CREF_QUAL(i, ty, subs, cr)
                  end
                end
              end
          outComponentRef
        end

         #= Returns the last identifier of a cref as an Absyn.IDENT. =#
        function crefLastPath(inComponentRef::DAE.ComponentRef) ::Absyn.Path
              local outPath::Absyn.Path

              outPath = begin
                  local i::DAE.Ident
                  local c::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = i, subscriptLst =  nil())  => begin
                    Absyn.IDENT(i)
                  end

                  DAE.CREF_QUAL(componentRef = c, subscriptLst =  nil())  => begin
                    crefLastPath(c)
                  end
                end
              end
          outPath
        end

         #= Returns the first identifier of a component reference. =#
        function crefFirstIdent(inComponentRef::DAE.ComponentRef) ::DAE.Ident
              local outIdent::DAE.Ident

              outIdent = begin
                  local id::DAE.Ident
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = id)  => begin
                    id
                  end

                  DAE.CREF_QUAL(ident = id)  => begin
                    id
                  end
                end
              end
          outIdent
        end

         #= author: PA
          Returns the last identfifier of a ComponentRef. =#
        function crefLastIdent(inComponentRef::DAE.ComponentRef) ::DAE.Ident
              local outIdent::DAE.Ident

              outIdent = begin
                  local id::DAE.Ident
                  local res::DAE.Ident
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = id)  => begin
                    id
                  end

                  DAE.CREF_QUAL(componentRef = cr)  => begin
                      res = crefLastIdent(cr)
                    res
                  end
                end
              end
          outIdent
        end

         #=
          Return the last ComponentRef =#
        function crefLastCref(inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local res::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(__)  => begin
                    inComponentRef
                  end

                  DAE.CREF_QUAL(componentRef = cr)  => begin
                      res = crefLastCref(cr)
                    res
                  end
                end
              end
          outComponentRef
        end

        function crefRest(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              @match DAE.CREF_QUAL(componentRef = outCref) = inCref
          outCref
        end

         #= Helper function to crefTypeFull. =#
        function crefTypeFull2(inCref::DAE.ComponentRef, accumDims::List{<:DAE.Dimension} = nil) ::Tuple{DAE.Type, List{DAE.Dimension}}
              local outDims::List{DAE.Dimension}
              local outType::DAE.Type

              (outType, outDims) = begin
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local basety::DAE.Type
                  local dims::List{DAE.Dimension}
                  local subs::List{DAE.Subscript}
                @match inCref begin
                  DAE.CREF_IDENT(identType = ty, subscriptLst = subs)  => begin
                      (ty, dims) = Types.flattenArrayType(ty)
                      dims = ListUtil.stripN(dims, listLength(subs))
                      if ! listEmpty(accumDims)
                        dims = listReverse(ListUtil.append_reverse(dims, accumDims))
                      end
                    (ty, dims)
                  end

                  DAE.CREF_QUAL(identType = ty, subscriptLst = subs, componentRef = cr)  => begin
                      (ty, dims) = Types.flattenArrayType(ty)
                      dims = ListUtil.stripN(dims, listLength(subs))
                      (basety, dims) = crefTypeFull2(cr, ListUtil.append_reverse(dims, accumDims))
                    (basety, dims)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("ComponentReference.crefTypeFull2 failed on cref: ")
                        Debug.traceln(printComponentRefStr(inCref))
                      fail()
                  end
                end
              end
          (outType, outDims)
        end

         #= mahge:
           This function gives the type of a cref.
           This is done by considering how many dimensions and subscripts
           the cref has. It also takes in to consideration where the subscripts
           are loacated in a qualifed cref. e.g. consider :
            record R
              Real [4]
            end R;

            R a[3][2];

            if we have a cref a[1][1].b[1] --> Real
                              a[1].b --> Real[2][4]
                              a.b[1] --> Real[3][2]
                              a[1][1].b --> Real[4]
                              a[1].b[1] --> Real[2]

            =#
        function crefTypeFull(inCref::DAE.ComponentRef) ::DAE.Type
              local outType::DAE.Type

              local ty::DAE.Type
              local dims::List{DAE.Dimension}

              (ty, dims) = crefTypeFull2(inCref)
              if listEmpty(dims)
                outType = ty
              else
                outType = DAE.T_ARRAY(ty, dims)
              end
          outType
        end

         #=  ***deprecated. Use crefTypeFull unless you really specifically want the type of the first cref.
          Function for extracting the type of the first identifier of a cref.
           =#
        function crefType(inCref::DAE.ComponentRef) ::DAE.Type
              local outType::DAE.Type

              outType = begin
                  local ty::DAE.Type
                @match inCref begin
                  DAE.CREF_IDENT(identType = ty)  => begin
                    ty
                  end

                  DAE.CREF_QUAL(identType = ty)  => begin
                    ty
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("ComponentReference.crefType failed on cref: ")
                        Debug.traceln(printComponentRefStr(inCref))
                      fail()
                  end
                end
              end
          outType
        end

         #=  ***deprecated.
          mahge: Use crefTypeFull unless you really specifically want the type of the last cref.
          Remember the type of a cref is not the same as the type of the last cref!!.

        returns the 'last' type of a cref.
        For instance, for the cref 'a.b' it returns the type in identifier 'b'
        adrpo:
          NOTE THAT THIS WILL BE AN ARRAY TYPE IF THE LAST CREF IS AN ARRAY TYPE
          If you want to get the component reference type considering subscripts use:
          crefTypeConsiderSubs =#
        function crefLastType(inRef::DAE.ComponentRef) ::DAE.Type
              local res::DAE.Type

              res = begin
                  local t2::DAE.Type
                  local cr::DAE.ComponentRef
                @match inRef begin
                  DAE.CREF_IDENT(_, t2, _)  => begin
                    t2
                  end

                  DAE.CREF_QUAL(_, _, _, cr)  => begin
                    crefLastType(cr)
                  end
                end
              end
          res
        end

         #=
        function: crefDims
          Return the all dimension (contained in the types) of a ComponentRef =#
        function crefDims(inComponentRef::DAE.ComponentRef) ::List{DAE.Dimension}
              local outDimensionLst::List{DAE.Dimension}

              outDimensionLst = begin
                  local dims::List{DAE.Dimension}
                  local res::List{DAE.Dimension}
                  local idType::DAE.Type
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(identType = idType)  => begin
                    Types.getDimensions(idType)
                  end

                  DAE.CREF_QUAL(componentRef = cr, identType = idType)  => begin
                      dims = Types.getDimensions(idType)
                      res = crefDims(cr)
                      res = listAppend(dims, res)
                    res
                  end
                end
              end
          outDimensionLst
        end

         #=
        function: crefSubs
          Return all subscripts of a ComponentRef =#
        function crefSubs(inComponentRef::DAE.ComponentRef) ::List{DAE.Subscript}
              local outSubscriptLst::List{DAE.Subscript}

              outSubscriptLst = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local res::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(subscriptLst = subs)  => begin
                    subs
                  end

                  DAE.CREF_QUAL(componentRef = cr, subscriptLst = subs)  => begin
                      res = crefSubs(cr)
                      res = listAppend(subs, res)
                    res
                  end
                end
              end
          outSubscriptLst
        end

        function crefFirstSubs(inCref::DAE.ComponentRef) ::List{DAE.Subscript}
              local outSubscripts::List{DAE.Subscript}

              outSubscripts = begin
                @match inCref begin
                  DAE.CREF_IDENT(__)  => begin
                    inCref.subscriptLst
                  end

                  DAE.CREF_QUAL(__)  => begin
                    inCref.subscriptLst
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outSubscripts
        end

         #= Return the last subscripts of a ComponentRef =#
        function crefLastSubs(inComponentRef::DAE.ComponentRef) ::List{DAE.Subscript}
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
                    crefLastSubs(cr)
                  end
                end
              end
          outSubscriptLst
        end

         #= Returns the first part of a component reference, i.e the identifier =#
        function crefFirstCref(inCr::DAE.ComponentRef) ::DAE.ComponentRef
              local outCr::DAE.ComponentRef

              outCr = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @match inCr begin
                  DAE.CREF_QUAL(id, t2, subs, _)  => begin
                    makeCrefIdent(id, t2, subs)
                  end

                  DAE.CREF_IDENT(_, _, _)  => begin
                    inCr
                  end
                end
              end
          outCr
        end

         #=  ***deprecated.
          mahge: use crefTypeFull(). This is not what you want. We need to consider not just the last subs but all subs.
          We can have slices.

        Function: crefTypeConsiderSubs
        Author: PA
        Function for extracting the type out of a componentReference and consider the influence of the last subscript list.
        For exampel. If the last cref type is Real[3,3] and the last subscript list is {Expression.INDEX(1)}, the type becomes Real[3], i.e
        one dimension is lifted.
        See also, crefType.
         =#
        function crefTypeConsiderSubs(cr::DAE.ComponentRef) ::DAE.Type
              local res::DAE.Type

              res = Expression.unliftArrayTypeWithSubs(crefLastSubs(cr), crefLastType(cr))
          res
        end

         #= Function: crefType
        Function for extracting the name and type out of the first cref of a componentReference.
         =#
        function crefNameType(inRef::DAE.ComponentRef) ::Tuple{DAE.Ident, DAE.Type}
              local res::DAE.Type
              local id::DAE.Ident

              (id, res) = begin
                  local t2::DAE.Type
                  local name::DAE.Ident
                  local s::String
                @matchcontinue inRef begin
                  DAE.CREF_IDENT(name, t2, _)  => begin
                    (name, t2)
                  end

                  DAE.CREF_QUAL(name, t2, _, _)  => begin
                    (name, t2)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("-ComponentReference.crefType failed on Cref:")
                        s = printComponentRefStr(inRef)
                        Debug.traceln(s)
                      fail()
                  end
                end
              end
          (id, res)
        end

        function getArrayCref(name::DAE.ComponentRef) ::Option{DAE.ComponentRef}
              local arrayCref::Option{DAE.ComponentRef}

              arrayCref = begin
                  local arrayCrefInner::DAE.ComponentRef
                @matchcontinue name begin
                  _  => begin
                      @match true = crefIsFirstArrayElt(name)
                      if stringEqual(Config.simCodeTarget(), "Cpp")
                        arrayCrefInner = crefStripLastSubs(name)
                      else
                        arrayCrefInner = crefStripSubs(name)
                      end
                    SOME(arrayCrefInner)
                  end

                  _  => begin
                      NONE()
                  end
                end
              end
          arrayCref
        end

        function getArraySubs(name::DAE.ComponentRef) ::List{DAE.Subscript}
              local arraySubs::List{DAE.Subscript}

              arraySubs = begin
                  local arrayCrefSubs::List{DAE.Subscript}
                @matchcontinue name begin
                  _  => begin
                      arrayCrefSubs = crefSubs(name)
                    arrayCrefSubs
                  end

                  _  => begin
                      nil
                  end
                end
              end
          arraySubs
        end

         #= /***************************************************/ =#
         #= /* Change  */ =#
         #= /***************************************************/ =#

         #= prepends (e..g as a suffix) an identifier to a component reference, given the identifier, subscript and the type
        author: PA

          The crefPrependIdent function extends a ComponentRef by appending
          an identifier and a (possibly empty) list of subscripts.  Adding
          the identifier A to the component reference x.y[10] would
          produce the component reference x.y[10].A, for instance.

        Example
        crefPrependIdent(a.b,c,{},Real) => a.b.c [Real]
        crefPrependIdent(a,c,{1},Integer[1]) => a.c[1] [Integer[1]]

        alternative names: crefAddSuffix, crefAddIdent
         =#
        function crefPrependIdent(icr::DAE.ComponentRef, ident::String, subs::List{<:DAE.Subscript}, tp::DAE.Type) ::DAE.ComponentRef
              local newCr::DAE.ComponentRef

              newCr = begin
                  local tp1::DAE.Type
                  local id1::String
                  local subs1::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match (icr, ident, subs, tp) begin
                  (DAE.CREF_IDENT(id1, tp1, subs1), _, _, _)  => begin
                    makeCrefQual(id1, tp1, subs1, makeCrefIdent(ident, tp, subs))
                  end

                  (DAE.CREF_QUAL(id1, tp1, subs1, cr), _, _, _)  => begin
                      cr = crefPrependIdent(cr, ident, subs, tp)
                    makeCrefQual(id1, tp1, subs1, cr)
                  end
                end
              end
          newCr
        end

         #= public function crefPrefixDer
          Appends $DER to a cref, so a => $DER.a =#
        function crefPrefixDer(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(DAE.derivativeNamePrefix, DAE.T_REAL_DEFAULT, nil, inCref)
          outCref
        end

         #= public function crefPrefixPre
          Appends $PRE to a cref, so a => $PRE.a =#
        function crefPrefixPre(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(DAE.preNamePrefix, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
          outCref
        end

         #= public function crefPrefixPrevious
          Appends $CLKPRE to a cref, so a => $CLKPRE.a =#
        function crefPrefixPrevious(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(DAE.previousNamePrefix, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
          outCref
        end

         #= public function crefPrefixAux
          Appends $AUX to a cref, so a => $AUX.a =#
        function crefPrefixAux(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(DAE.auxNamePrefix, DAE.T_REAL_DEFAULT, nil, inCref)
          outCref
        end

        function crefRemovePrePrefix(cref::DAE.ComponentRef) ::DAE.ComponentRef


              cref = begin
                @match cref begin
                  DAE.CREF_QUAL(ident = DAE.preNamePrefix)  => begin
                    cref.componentRef
                  end

                  _  => begin
                      cref
                  end
                end
              end
          cref
        end

         #= public function crefPrefixStart
          Appends $START to a cref, so a => $START.a =#
        function crefPrefixStart(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(DAE.startNamePrefix, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
          outCref
        end

         #= Prefixes a cref with a string identifier, e.g.:
            crefPrefixString(a, b.c) => a.b.c =#
        function crefPrefixString(inString::String, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = makeCrefQual(inString, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
          outCref
        end

         #= Prefixes a cref with a list of strings, e.g.:
            crefPrefixStringList({a, b, c}, d.e.f) => a.b.c.d.e.f =#
        function crefPrefixStringList(inStrings::List{<:String}, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local str::String
                  local rest_str::List{String}
                  local cref::DAE.ComponentRef
                @match (inStrings, inCref) begin
                  (str <| rest_str, cref)  => begin
                      cref = crefPrefixStringList(rest_str, cref)
                      cref = crefPrefixString(str, cref)
                    cref
                  end

                  _  => begin
                      inCref
                  end
                end
              end
          outCref
        end

        function prefixWithPath(inCref::DAE.ComponentRef, inPath::Absyn.Path) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local name::Absyn.Ident
                  local rest_path::Absyn.Path
                  local cref::DAE.ComponentRef
                @match (inCref, inPath) begin
                  (_, Absyn.IDENT(name = name))  => begin
                    DAE.CREF_QUAL(name, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
                  end

                  (_, Absyn.QUALIFIED(name = name, path = rest_path))  => begin
                      cref = prefixWithPath(inCref, rest_path)
                    DAE.CREF_QUAL(name, DAE.T_UNKNOWN_DEFAULT, nil, cref)
                  end

                  (_, Absyn.FULLYQUALIFIED(path = rest_path))  => begin
                    prefixWithPath(inCref, rest_path)
                  end
                end
              end
          outCref
        end

         #= Prepend a string to a component reference.
          For qualified named, this means prepending a
          string to the first identifier. =#
        function prependStringCref(inString::String, inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local i_1::DAE.Ident
                  local p::DAE.Ident
                  local i::DAE.Ident
                  local s::List{DAE.Subscript}
                  local c::DAE.ComponentRef
                  local t2::DAE.Type
                @match (inString, inComponentRef) begin
                  (p, DAE.CREF_QUAL(ident = i, identType = t2, subscriptLst = s, componentRef = c))  => begin
                      i_1 = stringAppend(p, i)
                    makeCrefQual(i_1, t2, s, c)
                  end

                  (p, DAE.CREF_IDENT(ident = i, identType = t2, subscriptLst = s))  => begin
                      i_1 = stringAppend(p, i)
                    makeCrefIdent(i_1, t2, s)
                  end
                end
              end
          outComponentRef
        end

        function appendStringCref(str::String, cr::DAE.ComponentRef) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              ocr = joinCrefs(cr, DAE.CREF_IDENT(str, DAE.T_UNKNOWN_DEFAULT, nil))
          ocr
        end

         #= Appends a string to the first identifier of a cref. =#
        function appendStringFirstIdent(inString::String, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local idx::ModelicaInteger
                @match (inString, inCref) begin
                  (_, DAE.CREF_QUAL(id, ty, subs, cr))  => begin
                      id = stringAppend(id, inString)
                    DAE.CREF_QUAL(id, ty, subs, cr)
                  end

                  (_, DAE.CREF_IDENT(id, ty, subs))  => begin
                      id = stringAppend(id, inString)
                    DAE.CREF_IDENT(id, ty, subs)
                  end

                  (_, DAE.CREF_ITER(id, idx, ty, subs))  => begin
                      id = stringAppend(id, inString)
                    DAE.CREF_ITER(id, idx, ty, subs)
                  end
                end
              end
          outCref
        end

         #= Appends a string to the last identifier of a cref. =#
        function appendStringLastIdent(inString::String, inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local idx::ModelicaInteger
                @match (inString, inCref) begin
                  (_, DAE.CREF_QUAL(id, ty, subs, cr))  => begin
                      cr = appendStringLastIdent(inString, cr)
                    DAE.CREF_QUAL(id, ty, subs, cr)
                  end

                  (_, DAE.CREF_IDENT(id, ty, subs))  => begin
                      id = stringAppend(id, inString)
                    DAE.CREF_IDENT(id, ty, subs)
                  end

                  (_, DAE.CREF_ITER(id, idx, ty, subs))  => begin
                      id = stringAppend(id, inString)
                    DAE.CREF_ITER(id, idx, ty, subs)
                  end
                end
              end
          outCref
        end

         #= Joins two component references by concatenating them.
          alternative names: crefAppend
           =#
        function joinCrefs(inComponentRef1::DAE.ComponentRef #=  first part of the new componentref =#, inComponentRef2::DAE.ComponentRef #=  last part of the new componentref =#) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local sub::List{DAE.Subscript}
                  local cr2::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @match (inComponentRef1, inComponentRef2) begin
                  (DAE.CREF_IDENT(ident = id, identType = t2, subscriptLst = sub), cr2)  => begin
                    makeCrefQual(id, t2, sub, cr2)
                  end

                  (DAE.CREF_QUAL(ident = id, identType = t2, subscriptLst = sub, componentRef = cr), cr2)  => begin
                      cr_1 = joinCrefs(cr, cr2)
                    makeCrefQual(id, t2, sub, cr_1)
                  end
                end
              end
          outComponentRef
        end

         #= like joinCrefs but with last part as first argument. =#
        function joinCrefsR(inComponentRef2::DAE.ComponentRef #=  last part of the new componentref =#, inComponentRef1::DAE.ComponentRef #=  first part of the new componentref =#) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local sub::List{DAE.Subscript}
                  local cr2::DAE.ComponentRef
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @match (inComponentRef2, inComponentRef1) begin
                  (cr2, DAE.CREF_IDENT(ident = id, identType = t2, subscriptLst = sub))  => begin
                    makeCrefQual(id, t2, sub, cr2)
                  end

                  (cr2, DAE.CREF_QUAL(ident = id, identType = t2, subscriptLst = sub, componentRef = cr))  => begin
                      cr_1 = joinCrefs(cr, cr2)
                    makeCrefQual(id, t2, sub, cr_1)
                  end
                end
              end
          outComponentRef
        end

         #= Like joinCrefs but first argument is an expression =#
        function joinCrefsExp(exp::DAE.Exp, cref::DAE.ComponentRef) ::Tuple{DAE.Exp, DAE.ComponentRef}



              exp = begin
                  local cr::DAE.ComponentRef
                  local tp::DAE.Type
                @match exp begin
                  DAE.CREF(cr, tp)  => begin
                      cr = joinCrefs(cref, cr)
                    DAE.CREF(cr, tp)
                  end

                  _  => begin
                      exp
                  end
                end
              end
          (exp, cref)
        end

         #= The subscriptCref function adds a subscript to the ComponentRef
          For instance a.b with subscript 10 becomes a.b[10] and c.d[1,2]
          with subscript 3,4 becomes c.d[1,2,3,4] =#
        function subscriptCref(inComponentRef::DAE.ComponentRef, inSubscriptLst::List{<:DAE.Subscript}) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local newsub_1::List{DAE.Subscript}
                  local sub::List{DAE.Subscript}
                  local newsub::List{DAE.Subscript}
                  local id::DAE.Ident
                  local cref_1::DAE.ComponentRef
                  local cref::DAE.ComponentRef
                  local t2::DAE.Type
                @match (inComponentRef, inSubscriptLst) begin
                  (DAE.CREF_IDENT(ident = id, subscriptLst = sub, identType = t2), newsub)  => begin
                      newsub_1 = listAppend(sub, newsub)
                    makeCrefIdent(id, t2, newsub_1)
                  end

                  (DAE.CREF_QUAL(ident = id, subscriptLst = sub, componentRef = cref, identType = t2), newsub)  => begin
                      cref_1 = subscriptCref(cref, newsub)
                    makeCrefQual(id, t2, sub, cref_1)
                  end
                end
              end
          outComponentRef
        end

         #= Subscripts a component reference with a constant integer. It also unlifts the
          type of the components reference so that the type of the reference is correct
          with regards to the subscript. If the reference is not of array type this
          function will fail. =#
        function subscriptCrefWithInt(inComponentRef::DAE.ComponentRef, inSubscript::ModelicaInteger) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local subs::List{DAE.Subscript}
                  local new_sub::DAE.Subscript
                  local id::DAE.Ident
                  local rest_cref::DAE.ComponentRef
                  local ty::DAE.Type
                @match (inComponentRef, inSubscript) begin
                  (DAE.CREF_IDENT(ident = id, subscriptLst = subs, identType = ty), _)  => begin
                      new_sub = DAE.INDEX(DAE.ICONST(inSubscript))
                      subs = ListUtil.appendElt(new_sub, subs)
                      ty = Expression.unliftArray(ty)
                    makeCrefIdent(id, ty, subs)
                  end

                  (DAE.CREF_QUAL(ident = id, subscriptLst = subs, componentRef = rest_cref, identType = ty), _)  => begin
                      rest_cref = subscriptCrefWithInt(rest_cref, inSubscript)
                    makeCrefQual(id, ty, subs, rest_cref)
                  end
                end
              end
          outComponentRef
        end

         #= sets the subs of the last componenentref ident =#
        function crefSetLastSubs(inComponentRef::DAE.ComponentRef, inSubs::List{<:DAE.Subscript}) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local tp::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match (inComponentRef, inSubs) begin
                  (DAE.CREF_IDENT(ident = id, identType = tp), _)  => begin
                    makeCrefIdent(id, tp, inSubs)
                  end

                  (DAE.CREF_QUAL(ident = id, identType = tp, subscriptLst = subs, componentRef = cr), _)  => begin
                      cr = crefSetLastSubs(cr, inSubs)
                    makeCrefQual(id, tp, subs, cr)
                  end
                end
              end
          outComponentRef
        end

         #= Apply subs to the first componenentref ident that is of array type.
           TODO: must not apply subs whose list length exceeds array dimensions.
           author: rfranke =#
        function crefApplySubs(inComponentRef::DAE.ComponentRef, inSubs::List{<:DAE.Subscript}) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local tp::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = id, identType = tp && DAE.T_ARRAY(__), subscriptLst = subs)  => begin
                    makeCrefIdent(id, tp, listAppend(subs, inSubs))
                  end

                  DAE.CREF_QUAL(ident = id, identType = tp && DAE.T_ARRAY(__), subscriptLst = subs, componentRef = cr)  => begin
                    makeCrefQual(id, tp, listAppend(subs, inSubs), cr)
                  end

                  DAE.CREF_QUAL(ident = id, identType = tp, subscriptLst = subs, componentRef = cr)  => begin
                      cr = crefApplySubs(cr, inSubs)
                    makeCrefQual(id, tp, subs, cr)
                  end

                  _  => begin
                        Error.addInternalError("function ComponentReference.crefApplySubs to non array\\n", sourceInfo())
                      fail()
                  end
                end
              end
          outComponentRef
        end

         #=
        sets the type of a cref. =#
        function crefSetType(inRef::DAE.ComponentRef, newType::DAE.Type) ::DAE.ComponentRef
              local outRef::DAE.ComponentRef

              outRef = begin
                  local ty::DAE.Type
                  local child::DAE.ComponentRef
                  local subs::List{DAE.Subscript}
                  local id::DAE.Ident
                @match (inRef, newType) begin
                  (DAE.CREF_IDENT(id, _, subs), _)  => begin
                    makeCrefIdent(id, newType, subs)
                  end

                  (DAE.CREF_QUAL(id, _, subs, child), _)  => begin
                    makeCrefQual(id, newType, subs, child)
                  end
                end
              end
          outRef
        end

         #=
        sets the 'last' type of a cref. =#
        function crefSetLastType(inRef::DAE.ComponentRef, newType::DAE.Type) ::DAE.ComponentRef
              local outRef::DAE.ComponentRef

              outRef = begin
                  local ty::DAE.Type
                  local child::DAE.ComponentRef
                  local subs::List{DAE.Subscript}
                  local id::DAE.Ident
                  local idx::ModelicaInteger
                @match inRef begin
                  DAE.CREF_IDENT(id, _, subs)  => begin
                    makeCrefIdent(id, newType, subs)
                  end

                  DAE.CREF_QUAL(id, ty, subs, child)  => begin
                      child = crefSetLastType(child, newType)
                    makeCrefQual(id, ty, subs, child)
                  end

                  DAE.CREF_ITER(id, idx, _, subs)  => begin
                    DAE.CREF_ITER(id, idx, newType, subs)
                  end
                end
              end
          outRef
        end

         #=
        Go trough ComponentRef searching for a slice eighter in
        qual's or finaly ident. if none find, add dimension to DAE.CREF_IDENT(,ss:INPUTARG,) =#
        function replaceCrefSliceSub(inCr::DAE.ComponentRef, newSub::List{<:DAE.Subscript}) ::DAE.ComponentRef
              local outCr::DAE.ComponentRef

              outCr = begin
                  local t2::DAE.Type
                  local identType::DAE.Type
                  local child::DAE.ComponentRef
                  local subs::List{DAE.Subscript}
                  local name::String
                   #=  debugging case, uncomment for enabling
                   =#
                   #=  case(child,newSub)
                   =#
                   #=   equation
                   =#
                   #=     str1 = printComponentRefStr(child);
                   =#
                   #=     str2 = stringDelimitList(List.map(newSub, printSubscriptStr), \", \");
                   =#
                   #=     str  = \"replaceCrefSliceSub(\" + str1 + \" subs: [\" + str2 + \"]\\n\";
                   =#
                   #=     print(str);
                   =#
                   #=   then
                   =#
                   #=     fail();
                   =#
                   #=  Case where we try to find a Expression.DAE.SLICE()
                   =#
                @matchcontinue (inCr, newSub) begin
                  (DAE.CREF_IDENT(name, identType, subs), _)  => begin
                      subs = replaceSliceSub(subs, newSub)
                    makeCrefIdent(name, identType, subs)
                  end

                  (DAE.CREF_IDENT(identType = t2, subscriptLst = subs), _)  => begin
                      @match true = listLength(Expression.arrayTypeDimensions(t2)) >= listLength(subs) + 1
                      child = subscriptCref(inCr, newSub)
                    child
                  end

                  (DAE.CREF_IDENT(identType = t2, subscriptLst = subs), _)  => begin
                      @match false = listLength(Expression.arrayTypeDimensions(t2)) >= listLength(subs) + listLength(newSub)
                      child = subscriptCref(inCr, newSub)
                      if Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("WARNING - Expression.replaceCref_SliceSub setting subscript last, not containing dimension\\n")
                      end
                    child
                  end

                  (DAE.CREF_QUAL(name, identType, subs, child), _)  => begin
                      subs = replaceSliceSub(subs, newSub)
                    makeCrefQual(name, identType, subs, child)
                  end

                  (DAE.CREF_QUAL(name, identType, subs, child), _)  => begin
                      @match true = listLength(Expression.arrayTypeDimensions(identType)) >= listLength(subs) + 1
                    makeCrefQual(name, identType, listAppend(subs, newSub), child)
                  end

                  (DAE.CREF_QUAL(name, identType, subs, child), _)  => begin
                      child = replaceCrefSliceSub(child, newSub)
                    makeCrefQual(name, identType, subs, child)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Expression.replaceCref_SliceSub failed\\n")
                      fail()
                  end
                end
              end
               #=  Try DAE.CREF_QUAL with DAE.SLICE subscript
               =#
               #=  case where there is not existant Expression.DAE.SLICE() as subscript in CREF_QUAL
               =#
               #=  DAE.CREF_QUAL without DAE.SLICE, search child
               =#
          outCr
        end

         #=
        A function for replacing any occurance of DAE.SLICE or DAE.WHOLEDIM with new sub. =#
        function replaceSliceSub(inSubs::List{<:DAE.Subscript}, inSub::List{<:DAE.Subscript}) ::List{DAE.Subscript}
              local osubs::List{DAE.Subscript}

              osubs = begin
                  local subs::List{DAE.Subscript}
                  local sub::DAE.Subscript
                @matchcontinue (inSubs, inSub) begin
                  (DAE.SLICE(_) <| subs, _)  => begin
                      subs = listAppend(inSub, subs)
                    subs
                  end

                  (DAE.WHOLEDIM(__) <| subs, _)  => begin
                      subs = listAppend(inSub, subs)
                    subs
                  end

                  (sub <| subs, _)  => begin
                      subs = replaceSliceSub(subs, inSub)
                    _cons(sub, subs)
                  end
                end
              end
               #=  adrpo, 2010-02-23:
               =#
               #=    WHOLEDIM is *also* a special case of SLICE
               =#
               #=    that contains the all subscripts, so we need
               =#
               #=    to handle that too here!
               =#
          osubs
        end

         #=
        Author BZ
        Strips the SLICE-subscripts fromt the -last- subscript list. All other subscripts are not changed.
        For example
        x[1].y[{1,2},3,{1,3,7}] => x[1].y[3]
        Alternative names: stripLastSliceSubs =#
        function stripCrefIdentSliceSubs(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::DAE.Ident
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                @match inCref begin
                  DAE.CREF_IDENT(ident = id, subscriptLst = subs, identType = ty)  => begin
                      subs = removeSliceSubs(subs)
                    makeCrefIdent(id, ty, subs)
                  end

                  DAE.CREF_QUAL(componentRef = cr, identType = ty, subscriptLst = subs, ident = id)  => begin
                      outCref = stripCrefIdentSliceSubs(cr)
                    makeCrefQual(id, ty, subs, outCref)
                  end
                end
              end
          outCref
        end

         #= strips the cref at the array-cref. remove subscripts, outputs appended crefs =#
        function stripArrayCref(crefIn::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, ModelicaInteger, Option{DAE.ComponentRef}}
              local crefTail::Option{DAE.ComponentRef}
              local idxOut::ModelicaInteger
              local crefHead::DAE.ComponentRef

              (crefHead, idxOut, crefTail) = begin
                  local idx::ModelicaInteger
                  local id::DAE.Ident
                  local cr::DAE.ComponentRef
                  local outCref::DAE.ComponentRef
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                @match crefIn begin
                  DAE.CREF_IDENT(ident = id, subscriptLst = DAE.INDEX(DAE.ICONST(idx)) <|  nil(), identType = ty)  => begin
                    (makeCrefIdent(id, ty, nil), idx, NONE())
                  end

                  DAE.CREF_QUAL(componentRef = cr, identType = ty, subscriptLst = DAE.INDEX(DAE.ICONST(idx)) <|  nil(), ident = id)  => begin
                    (makeCrefIdent(id, ty, nil), idx, SOME(cr))
                  end

                  DAE.CREF_QUAL(componentRef = cr, identType = ty, ident = id)  => begin
                      outCref = stripCrefIdentSliceSubs(cr)
                    (makeCrefQual(id, ty, nil, outCref), -1, NONE())
                  end
                end
              end
               #=  the complete cref is an array
               =#
               #=  strip the cref here
               =#
               #=  continue
               =#
          (crefHead, idxOut, crefTail)
        end

         #=
        helper function for stripCrefIdentSliceSubs =#
        function removeSliceSubs(subs::List{<:DAE.Subscript}) ::List{DAE.Subscript}
              local osubs::List{DAE.Subscript} = nil

              for s in subs
                osubs = begin
                  @match s begin
                    DAE.SLICE(__)  => begin
                      osubs
                    end

                    _  => begin
                        _cons(s, osubs)
                    end
                  end
                end
              end
              osubs = Dangerous.listReverseInPlace(osubs)
          osubs
        end

         #=
        Removes all subscript of a componentref =#
        function crefStripSubs(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::DAE.Ident
                  local cr::DAE.ComponentRef
                  local ty::DAE.Type
                @match inCref begin
                  DAE.CREF_IDENT(ident = id, identType = ty)  => begin
                    makeCrefIdent(id, ty, nil)
                  end

                  DAE.CREF_QUAL(componentRef = cr, identType = ty, ident = id)  => begin
                      outCref = crefStripSubs(cr)
                    makeCrefQual(id, ty, nil, outCref)
                  end
                end
              end
          outCref
        end

         #= Strips a prefix/cref from a component reference =#
        function crefStripPrefix(cref::DAE.ComponentRef, prefix::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local subs1::List{DAE.Subscript}
                  local subs2::List{DAE.Subscript}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local id1::DAE.Ident
                  local id2::DAE.Ident
                @match (cref, prefix) begin
                  (DAE.CREF_QUAL(id1, _, subs1, cr1), DAE.CREF_IDENT(id2, _, subs2))  => begin
                      @match true = stringEq(id1, id2)
                      @match true = Expression.subscriptEqual(subs1, subs2)
                    cr1
                  end

                  (DAE.CREF_QUAL(id1, _, subs1, cr1), DAE.CREF_QUAL(id2, _, subs2, cr2))  => begin
                      @match true = stringEq(id1, id2)
                      @match true = Expression.subscriptEqual(subs1, subs2)
                    crefStripPrefix(cr1, cr2)
                  end
                end
              end
          outCref
        end

         #= Strips the last part of a component reference, i.e ident and subs =#
        function crefStripLastIdent(inCr::DAE.ComponentRef) ::DAE.ComponentRef
              local outCr::DAE.ComponentRef

              outCr = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @matchcontinue inCr begin
                  DAE.CREF_QUAL(id, t2, subs, DAE.CREF_IDENT(_, _, _))  => begin
                    makeCrefIdent(id, t2, subs)
                  end

                  DAE.CREF_QUAL(id, t2, subs, cr)  => begin
                      cr1 = crefStripLastIdent(cr)
                    makeCrefQual(id, t2, subs, cr1)
                  end
                end
              end
          outCr
        end

         #= Strips the last subscripts of a ComponentRef =#
        function crefStripLastSubs(inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local id::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local s::List{DAE.Subscript}
                  local cr_1::DAE.ComponentRef
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = id, identType = t2)  => begin
                    makeCrefIdent(id, t2, nil)
                  end

                  DAE.CREF_QUAL(ident = id, identType = t2, subscriptLst = s, componentRef = cr)  => begin
                      cr_1 = crefStripLastSubs(cr)
                    makeCrefQual(id, t2, s, cr_1)
                  end
                end
              end
          outComponentRef
        end

         #= Recursively looks up subscripts and strips the given iter sub.
           This gives an array variable that is defined in a for loop (no NF_SCALARIZE).
           author: rfranke =#
        function crefStripIterSub(inComponentRef::DAE.ComponentRef, iter::DAE.Ident) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              local ident::DAE.Ident
              local index::DAE.Ident
              local ty::DAE.Type
              local subs::List{DAE.Subscript}
              local cref::DAE.ComponentRef

              outComponentRef = begin
                @match inComponentRef begin
                  DAE.CREF_IDENT(ident = ident, identType = ty, subscriptLst = subs && DAE.INDEX(exp = DAE.CREF(componentRef = DAE.CREF_IDENT(ident = index))) <|  nil())  => begin
                    makeCrefIdent(ident, ty, if index == iter
                          nil
                        else
                          subs
                        end)
                  end

                  DAE.CREF_QUAL(ident = ident, identType = ty, componentRef = cref, subscriptLst = subs && DAE.INDEX(exp = DAE.CREF(componentRef = DAE.CREF_IDENT(ident = index))) <|  nil())  => begin
                      if index == iter
                        subs = nil
                      else
                        cref = crefStripIterSub(cref, iter)
                      end
                    makeCrefQual(ident, ty, subs, cref)
                  end

                  DAE.CREF_QUAL(ident = ident, identType = ty, componentRef = cref, subscriptLst = subs)  => begin
                    makeCrefQual(ident, ty, subs, crefStripIterSub(cref, iter))
                  end

                  _  => begin
                      inComponentRef
                  end
                end
              end
          outComponentRef
        end

         #= Strips the first part of a component reference,
        i.e the identifier and eventual subscripts =#
        function crefStripFirstIdent(inCr::DAE.ComponentRef) ::DAE.ComponentRef
              local outCr::DAE.ComponentRef

              outCr = begin
                  local cr::DAE.ComponentRef
                @match inCr begin
                  DAE.CREF_QUAL(componentRef = cr)  => begin
                    cr
                  end
                end
              end
          outCr
        end

         #= author: PA
          Same as crefStripLastSubs but works on
          a stringified component ref instead. =#
        function crefStripLastSubsStringified(inComponentRef::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              outComponentRef = begin
                  local lst::List{DAE.Ident}
                  local lst_1::List{DAE.Ident}
                  local id_1::DAE.Ident
                  local id::DAE.Ident
                  local cr::DAE.ComponentRef
                  local t2::DAE.Type
                @matchcontinue inComponentRef begin
                  DAE.CREF_IDENT(ident = id, identType = t2, subscriptLst =  nil())  => begin
                      lst = Util.stringSplitAtChar(id, "[")
                      lst_1 = ListUtil.stripLast(lst)
                      id_1 = stringDelimitList(lst_1, "[")
                    makeCrefIdent(id_1, t2, nil)
                  end

                  cr  => begin
                    cr
                  end
                end
              end
               #= print(\"\\n +++++++++++++++++++++++++++++ \");print(id);print(\"\\n\");
               =#
          outComponentRef
        end

         #= Translates a ComponentRef into a DAE.CREF_IDENT by putting
          the string representation of the ComponentRef into it.
          See also stringigyCrefs.

          NOTE: This function should not be used in OMC, since the OMC backend no longer
            uses stringified components. It is still used by MathCore though. =#
        function stringifyComponentRef(cr::DAE.ComponentRef) ::DAE.ComponentRef
              local outComponentRef::DAE.ComponentRef

              local subs::List{DAE.Subscript}
              local cr_1::DAE.ComponentRef
              local crs::DAE.Ident
              local ty::DAE.Type

              subs = crefLastSubs(cr)
              cr_1 = crefStripLastSubs(cr)
              crs = printComponentRefStr(cr_1)
              ty = crefLastType(cr) #= The type of the stringified cr is taken from the last identifier =#
              outComponentRef = makeCrefIdent(crs, ty, subs)
          outComponentRef
        end

         #= /***************************************************/ =#
         #= /* Print and Dump */ =#
         #= /***************************************************/ =#

         #= Print a ComponentRef. =#
        function printComponentRef(inComponentRef::DAE.ComponentRef)
              _ = begin
                  local s::DAE.Ident
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                   #=  _
                   =#
                @match inComponentRef begin
                  DAE.WILD(__)  => begin
                      Print.printBuf("_")
                    ()
                  end

                  DAE.CREF_IDENT(ident = s, subscriptLst = subs)  => begin
                      printComponentRef2(s, subs)
                    ()
                  end

                  DAE.CREF_QUAL(ident = s, subscriptLst = subs, componentRef = cr)  => begin
                      if Config.modelicaOutput()
                        printComponentRef2(s, subs)
                        Print.printBuf("__")
                        printComponentRef(cr)
                      else
                        printComponentRef2(s, subs)
                        Print.printBuf(".")
                        printComponentRef(cr)
                      end
                    ()
                  end
                end
              end
        end

         #= Helper function to printComponentRef =#
        function printComponentRef2(inString::DAE.Ident, inSubscriptLst::List{<:DAE.Subscript})
              _ = begin
                  local s::DAE.Ident
                  local l::List{DAE.Subscript}
                @matchcontinue (inString, inSubscriptLst) begin
                  (s,  nil())  => begin
                      Print.printBuf(s)
                    ()
                  end

                  (s, l)  => begin
                      if Config.modelicaOutput()
                        Print.printBuf(s)
                        Print.printBuf("_L")
                        ExpressionDump.printList(l, ExpressionDump.printSubscript, ",")
                        Print.printBuf("_R")
                      else
                        Print.printBuf(s)
                        Print.printBuf("[")
                        ExpressionDump.printList(l, ExpressionDump.printSubscript, ",")
                        Print.printBuf("]")
                      end
                    ()
                  end
                end
              end
        end

        function printComponentRefListStr(crs::List{<:DAE.ComponentRef}) ::String
              local res::String

              res = "{" + stringDelimitList(ListUtil.map(crs, printComponentRefStr), ",") + "}"
          res
        end

        function printComponentRefList(crs::List{<:DAE.ComponentRef})
              local buffer::String

              buffer = "{" + stringDelimitList(ListUtil.map(crs, printComponentRefStr), ", ") + "}\\n"
              print(buffer)
        end

        function replaceWholeDimSubscript(icr::DAE.ComponentRef, index::ModelicaInteger) ::DAE.ComponentRef
              local ocr::DAE.ComponentRef

              ocr = begin
                  local id::String
                  local et::DAE.Type
                  local ss::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @matchcontinue (icr, index) begin
                  (DAE.CREF_QUAL(id, et, ss, cr), _)  => begin
                      ss = replaceWholeDimSubscript2(ss, index)
                    DAE.CREF_QUAL(id, et, ss, cr)
                  end

                  (DAE.CREF_QUAL(id, et, ss, cr), _)  => begin
                      cr = replaceWholeDimSubscript(cr, index)
                    DAE.CREF_QUAL(id, et, ss, cr)
                  end

                  (DAE.CREF_IDENT(id, et, ss), _)  => begin
                      ss = replaceWholeDimSubscript2(ss, index)
                    DAE.CREF_IDENT(id, et, ss)
                  end
                end
              end
          ocr
        end

        function replaceWholeDimSubscript2(isubs::List{<:DAE.Subscript}, index::ModelicaInteger) ::List{DAE.Subscript}
              local osubs::List{DAE.Subscript}

              osubs = begin
                  local sub::DAE.Subscript
                  local subs::List{DAE.Subscript}
                @match (isubs, index) begin
                  (DAE.WHOLEDIM(__) <| subs, _)  => begin
                      sub = DAE.INDEX(DAE.ICONST(index))
                    _cons(sub, subs)
                  end

                  (sub <| subs, _)  => begin
                      subs = replaceWholeDimSubscript2(subs, index)
                    _cons(sub, subs)
                  end
                end
              end
               #=  TODO: SLICE, NONEXP
               =#
          osubs
        end

         #= Splits a cref at the end, e.g. a.b.c.d => {a.b.c, d}. =#
        function splitCrefLast(inCref::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
              local outLastCref::DAE.ComponentRef
              local outPrefixCref::DAE.ComponentRef

              (outPrefixCref, outLastCref) = begin
                  local id::DAE.Ident
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local prefix::DAE.ComponentRef
                  local last::DAE.ComponentRef
                @match inCref begin
                  DAE.CREF_QUAL(id, ty, subs, last && DAE.CREF_IDENT(__))  => begin
                    (DAE.CREF_IDENT(id, ty, subs), last)
                  end

                  DAE.CREF_QUAL(id, ty, subs, last)  => begin
                      (prefix, last) = splitCrefLast(last)
                    (DAE.CREF_QUAL(id, ty, subs, prefix), last)
                  end
                end
              end
          (outPrefixCref, outLastCref)
        end

         #= Gets the first a cref at the n-th cref, e.g. (a.b.c.d,2) => a.b. =#
        function firstNCrefs(inCref::DAE.ComponentRef, nIn::ModelicaInteger) ::DAE.ComponentRef
              local outFirstCrefs::DAE.ComponentRef

              outFirstCrefs = begin
                  local id::DAE.Ident
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local prefix::DAE.ComponentRef
                  local last::DAE.ComponentRef
                @matchcontinue (inCref, nIn) begin
                  (_, 0)  => begin
                    inCref
                  end

                  (DAE.CREF_QUAL(id, ty, subs, _), 1)  => begin
                    DAE.CREF_IDENT(id, ty, subs)
                  end

                  (DAE.CREF_IDENT(_, _, _), _)  => begin
                    inCref
                  end

                  (DAE.CREF_QUAL(id, ty, subs, last), _)  => begin
                      prefix = firstNCrefs(last, nIn - 1)
                    DAE.CREF_QUAL(id, ty, subs, prefix)
                  end

                  _  => begin
                      inCref
                  end
                end
              end
          outFirstCrefs
        end

        function splitCrefFirst(inCref::DAE.ComponentRef) ::Tuple{DAE.ComponentRef, DAE.ComponentRef}
              local outCrefRest::DAE.ComponentRef
              local outCrefFirst::DAE.ComponentRef

              local id::DAE.Ident
              local ty::DAE.Type
              local subs::List{DAE.Subscript}

              @match DAE.CREF_QUAL(id, ty, subs, outCrefRest) = inCref
              outCrefFirst = DAE.CREF_IDENT(id, ty, subs)
          (outCrefFirst, outCrefRest)
        end

         #= Converts a component reference to a list of strings. =#
        function toStringList(inCref::DAE.ComponentRef) ::List{String}
              local outStringList::List{String}

              outStringList = Dangerous.listReverseInPlace(toStringList_tail(inCref, nil))
          outStringList
        end

         #= Tail-recursive implementation of toStringList. =#
        function toStringList_tail(inCref::DAE.ComponentRef, inAccumStrings::List{<:String}) ::List{String}
              local outStringList::List{String}

              outStringList = begin
                  local id::String
                  local cref::DAE.ComponentRef
                @match (inCref, inAccumStrings) begin
                  (DAE.CREF_QUAL(ident = id, componentRef = cref), _)  => begin
                    toStringList_tail(cref, _cons(id, inAccumStrings))
                  end

                  (DAE.CREF_IDENT(ident = id), _)  => begin
                    _cons(id, inAccumStrings)
                  end

                  _  => begin
                      nil
                  end
                end
              end
          outStringList
        end

        function crefDepth(inCref::DAE.ComponentRef) ::ModelicaInteger
              local depth::ModelicaInteger

              depth = begin
                  local n::DAE.ComponentRef
                @match inCref begin
                  DAE.WILD(__)  => begin
                    0
                  end

                  DAE.CREF_IDENT(__)  => begin
                    1
                  end

                  DAE.CREF_QUAL(componentRef = n)  => begin
                    crefDepth1(n, 1)
                  end
                end
              end
          depth
        end

        function crefDepth1(inCref::DAE.ComponentRef, iDepth::ModelicaInteger) ::ModelicaInteger
              local depth::ModelicaInteger

              depth = begin
                  local n::DAE.ComponentRef
                @match (inCref, iDepth) begin
                  (DAE.WILD(__), _)  => begin
                    iDepth
                  end

                  (DAE.CREF_IDENT(__), _)  => begin
                    1 + iDepth
                  end

                  (DAE.CREF_QUAL(componentRef = n), _)  => begin
                    crefDepth1(n, 1 + iDepth)
                  end
                end
              end
          depth
        end

         #= Expands an array cref into a list of elements, e.g.:

             expandCref(x) => {x[1], x[2], x[3]}

           This function expects the subscripts of the cref to be constant evaluated,
           otherwise it will fail. =#
        function expandCref(inCref::DAE.ComponentRef, expandRecord::Bool) ::List{DAE.ComponentRef}
              local outCref::List{DAE.ComponentRef}

              outCref = begin
                @matchcontinue (inCref, expandRecord) begin
                  (_, _)  => begin
                    expandCref_impl(inCref, expandRecord)
                  end

                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.traceln("- ComponentReference.expandCref failed on " + printComponentRefStr(inCref))
                      fail()
                  end
                end
              end
          outCref
        end

        function expandCref_impl(inCref::DAE.ComponentRef, expandRecord::Bool) ::List{DAE.ComponentRef}
              local outCref::List{DAE.ComponentRef}

              outCref = begin
                  local id::DAE.Ident
                  local ty::DAE.Type
                  local basety::DAE.Type
                  local correctTy::DAE.Type
                  local dims::List{DAE.Dimension}
                  local subs::List{DAE.Subscript}
                  local cref::DAE.ComponentRef
                  local crefs::List{DAE.ComponentRef}
                  local crefs2::List{DAE.ComponentRef}
                  local varLst::List{DAE.Var}
                  local missing_subs::ModelicaInteger
                   #=  A scalar record ident cref. Expand record true
                   =#
                @matchcontinue (inCref, expandRecord) begin
                  (DAE.CREF_IDENT(_, DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD(_)),  nil()), true)  => begin
                      crefs = ListUtil.map(varLst, creffromVar)
                      crefs = ListUtil.map1r(crefs, joinCrefs, inCref)
                    ListUtil.map1Flat(crefs, expandCref_impl, true)
                  end

                  (DAE.CREF_IDENT(id, ty && DAE.T_ARRAY(__),  nil()), true)  => begin
                      @match ((@match DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD()) = basety), dims) = Types.flattenArrayType(ty)
                      correctTy = DAE.T_ARRAY(basety, dims)
                      subs = ListUtil.fill(DAE.WHOLEDIM(), listLength(dims))
                      crefs = expandCref2(id, correctTy, subs, dims)
                    expandCrefLst(crefs, varLst, nil)
                  end

                  (DAE.CREF_IDENT(id, ty && DAE.T_ARRAY(__),  nil()), _)  => begin
                      (basety, dims) = Types.flattenArrayType(ty)
                      correctTy = DAE.T_ARRAY(basety, dims)
                      subs = ListUtil.fill(DAE.WHOLEDIM(), listLength(dims))
                    expandCref2(id, correctTy, subs, dims)
                  end

                  (DAE.CREF_IDENT(id, ty && DAE.T_ARRAY(__), subs), true)  => begin
                      @match ((@match DAE.T_COMPLEX(varLst = varLst, complexClassType = ClassInf.RECORD()) = basety), dims) = Types.flattenArrayType(ty)
                      correctTy = DAE.T_ARRAY(basety, dims)
                      missing_subs = listLength(dims) - listLength(subs)
                      if missing_subs > 0
                        subs = listAppend(subs, ListUtil.fill(DAE.WHOLEDIM(), missing_subs)) #= annotation(
                          __OpenModelica_DisableListAppendWarning = true) =#
                      end
                      crefs = expandCref2(id, correctTy, subs, dims)
                    expandCrefLst(crefs, varLst, nil)
                  end

                  (DAE.CREF_IDENT(id, ty && DAE.T_ARRAY(__), subs), _)  => begin
                      (basety, dims) = Types.flattenArrayType(ty)
                      correctTy = DAE.T_ARRAY(basety, dims)
                      missing_subs = listLength(dims) - listLength(subs)
                      if missing_subs > 0
                        subs = listAppend(subs, ListUtil.fill(DAE.WHOLEDIM(), missing_subs)) #= annotation(
                          __OpenModelica_DisableListAppendWarning = true) =#
                      end
                    expandCref2(id, correctTy, subs, dims)
                  end

                  (DAE.CREF_QUAL(id, ty && DAE.T_ARRAY(__), subs, cref), _)  => begin
                      crefs = expandCref_impl(cref, expandRecord)
                      (basety, dims) = Types.flattenArrayType(ty)
                      correctTy = DAE.T_ARRAY(basety, dims)
                      cref = DAE.CREF_IDENT(id, correctTy, subs)
                      crefs2 = expandCref_impl(cref, false)
                      crefs2 = listReverse(crefs2)
                      crefs = expandCrefQual(crefs2, crefs)
                    crefs
                  end

                  (DAE.CREF_QUAL(id, ty, subs, cref), _)  => begin
                      crefs = expandCref_impl(cref, expandRecord)
                      crefs = ListUtil.map3r(crefs, makeCrefQual, id, ty, subs)
                    crefs
                  end

                  _  => begin
                      list(inCref)
                  end
                end
              end
               #=  Use the subscripts to generate only the wanted elements.
               =#
               #=  A qualified cref with array type.
               =#
               #=  Expand the rest of the cref.
               =#
               #=  Flatten T_ARRAY(T_ARRAY(T_..., dim2,src), dim1,src) types to one level T_ARRAY(simpletype, alldims, src)
               =#
               #=  Create a simple identifier for the head of the cref and expand it.
               =#
               #=  crefs2 = List.map1(crefs2,crefSetType,correctTy);
               =#
               #=  Create all combinations of the two lists.
               =#
               #=  A qualified cref with scalar type.
               =#
               #=  Expand the rest of the cref.
               =#
               #=  Append the head of this cref to all of the generated crefs.
               =#
               #=  All other cases, no expansion.
               =#
          outCref
        end

        function expandCrefLst(inCrefs::List{<:DAE.ComponentRef}, varLst::List{<:DAE.Var}, inCrefsAcc::List{<:List{<:DAE.ComponentRef}}) ::List{DAE.ComponentRef}
              local outCref::List{DAE.ComponentRef}

              outCref = begin
                  local cr::DAE.ComponentRef
                  local crefs::List{DAE.ComponentRef}
                  local rest::List{DAE.ComponentRef}
                @match (inCrefs, varLst, inCrefsAcc) begin
                  ( nil(), _, _)  => begin
                    ListUtil.flatten(inCrefsAcc)
                  end

                  (cr <| rest, _, _)  => begin
                      crefs = ListUtil.map(varLst, creffromVar)
                      crefs = ListUtil.map1r(crefs, joinCrefs, cr)
                    expandCrefLst(rest, varLst, _cons(crefs, inCrefsAcc))
                  end
                end
              end
               #=  Create a list of crefs from names
               =#
          outCref
        end

         #= Helper function to expandCref_impl. Constructs all combinations of the head
           and rest cref lists. E.g.:
            expandCrefQual({x, y}, {a, b}) => {x.a, x.b, y.a, y.b}  =#
        function expandCrefQual(inHeadCrefs::List{<:DAE.ComponentRef}, inRestCrefs::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef} = nil

              local crefs::List{DAE.ComponentRef}

              for cref in inHeadCrefs
                crefs = list(joinCrefs(cref, rest_cref) for rest_cref in inRestCrefs)
                outCrefs = listAppend(crefs, outCrefs)
              end
          outCrefs
        end

        function expandCref2(inId::DAE.Ident, inType::DAE.Type, inSubscripts::List{<:DAE.Subscript}, inDimensions::List{<:DAE.Dimension}) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef} = nil

              local subslst::List{List{DAE.Subscript}}

               #=  Expand each subscript into a list of subscripts.
               =#
              subslst = ListUtil.threadMap(inSubscripts, inDimensions, Expression.expandSubscript)
              subslst = ListUtil.combination(subslst)
              for subs in subslst
                outCrefs = _cons(makeCrefIdent(inId, inType, subs), outCrefs)
              end
              outCrefs = listReverse(outCrefs)
          outCrefs
        end

        function replaceSubsWithString(inCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local ident::DAE.Ident
                  local ident1::DAE.Ident
                  local identType::DAE.Type
                  local subscriptLst::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                  local cr1::DAE.ComponentRef
                  local str::String
                @match inCref begin
                  DAE.CREF_QUAL(ident = ident, identType = identType, subscriptLst =  nil(), componentRef = cr)  => begin
                      cr1 = replaceSubsWithString(cr)
                    DAE.CREF_QUAL(ident, identType, nil, cr1)
                  end

                  DAE.CREF_QUAL(ident = ident, identType = identType, subscriptLst = subscriptLst, componentRef = cr)  => begin
                      identType = Expression.unliftArrayTypeWithSubs(subscriptLst, identType)
                      cr1 = replaceSubsWithString(cr)
                      cr = makeCrefsFromSubScriptLst(subscriptLst, DAE.CREF_IDENT(ident, identType, nil))
                    joinCrefs(cr, cr1)
                  end

                  DAE.CREF_IDENT(subscriptLst =  nil())  => begin
                    inCref
                  end

                  DAE.CREF_IDENT(ident = ident, identType = identType, subscriptLst = subscriptLst)  => begin
                      identType = Expression.unliftArrayTypeWithSubs(subscriptLst, identType)
                      cr = makeCrefsFromSubScriptLst(subscriptLst, DAE.CREF_IDENT(ident, identType, nil))
                    cr
                  end

                  DAE.CREF_ITER(__)  => begin
                    inCref
                  end

                  DAE.WILD(__)  => begin
                    inCref
                  end
                end
              end
          outCref
        end

        function makeCrefsFromSubScriptLst(inSubscriptLst::List{<:DAE.Subscript}, inPreCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef = inPreCref

              for subScript in inSubscriptLst
                outCref = begin
                    local cr::DAE.ComponentRef
                    local e::DAE.Exp
                    local str::String
                  @match subScript begin
                    DAE.INDEX(exp = e)  => begin
                        cr = makeCrefsFromSubScriptExp(e)
                      joinCrefs(outCref, cr)
                    end

                    _  => begin
                          str = ExpressionDump.printSubscriptStr(subScript)
                          Error.addInternalError("function ComponentReference.makeCrefsFromSubScriptLst for:" + str + "\\n", sourceInfo())
                        fail()
                    end
                  end
                end
              end
               #=  all other should probably fails or evaluated before
               =#
          outCref
        end

        function makeCrefsFromSubScriptExp(inExp::DAE.Exp) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local op::DAE.Operator
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local str::String
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local enum_lit::Absyn.Path
                @match inExp begin
                  DAE.ICONST(__)  => begin
                      str = ExpressionDump.printExpStr(inExp)
                    DAE.CREF_IDENT(str, DAE.T_UNKNOWN_DEFAULT, nil)
                  end

                  DAE.CREF(__)  => begin
                    Expression.expCref(inExp)
                  end

                  DAE.BINARY(operator = op, exp1 = e1, exp2 = e2)  => begin
                      str = ExpressionDump.binopSymbol(op)
                      cr1 = makeCrefsFromSubScriptExp(e1)
                      cr2 = makeCrefsFromSubScriptExp(e2)
                      outCref = prependStringCref(str, cr1)
                      outCref = joinCrefs(outCref, cr2)
                    outCref
                  end

                  DAE.ENUM_LITERAL(name = enum_lit)  => begin
                      str = System.stringReplace(AbsynUtil.pathString(enum_lit), ".", "P")
                    DAE.CREF_IDENT(str, DAE.T_UNKNOWN_DEFAULT, nil)
                  end

                  _  => begin
                        str = ExpressionDump.dumpExpStr(inExp, 0)
                        Error.addInternalError("function ComponentReference.makeCrefsFromSubScriptExp for:" + str + "\\n", sourceInfo())
                      fail()
                  end
                end
              end
          outCref
        end

         #= Replaces the last part of a cref with a new cref. =#
        function replaceLast(inCref::DAE.ComponentRef, inNewLast::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local ident::DAE.Ident
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local cref::DAE.ComponentRef
                @match (inCref, inNewLast) begin
                  (DAE.CREF_QUAL(ident, ty, subs, cref), _)  => begin
                      cref = replaceLast(cref, inNewLast)
                    DAE.CREF_QUAL(ident, ty, subs, cref)
                  end

                  (DAE.CREF_IDENT(__), _)  => begin
                    inNewLast
                  end
                end
              end
          outCref
        end

         #= deprecated. use expandArray =#
        function expandArrayCref(inCr::DAE.ComponentRef, inDims::List{<:DAE.Dimension}) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              local lasttype::DAE.Type
              local tmpcref::DAE.ComponentRef

              lasttype = crefLastType(inCr)
              lasttype = Types.liftTypeWithDims(lasttype, inDims)
              tmpcref = crefSetLastType(inCr, lasttype)
              outCrefs = expandCref(tmpcref, false)
          outCrefs
        end

        function expandArrayCref1(inCr::DAE.ComponentRef, inSubscripts::List{<:List{<:DAE.Subscript}}, inAccumSubs::List{<:DAE.Subscript}, inAccumCrefs::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local outCrefs::List{DAE.ComponentRef}

              outCrefs = begin
                  local sub::DAE.Subscript
                  local subs::List{DAE.Subscript}
                  local rest_subs::List{List{DAE.Subscript}}
                  local crefs::List{DAE.ComponentRef}
                  local cref::DAE.ComponentRef
                @match (inCr, inSubscripts, inAccumSubs, inAccumCrefs) begin
                  (_, sub <| subs <| rest_subs, _, _)  => begin
                      crefs = expandArrayCref1(inCr, _cons(subs, rest_subs), inAccumSubs, inAccumCrefs)
                      crefs = expandArrayCref1(inCr, rest_subs, _cons(sub, inAccumSubs), crefs)
                    crefs
                  end

                  (_, _ <| _, _, _)  => begin
                    inAccumCrefs
                  end

                  _  => begin
                        cref = crefSetLastSubs(inCr, inAccumSubs)
                      _cons(cref, inAccumCrefs)
                  end
                end
              end
          outCrefs
        end

         #= Explodes a cref into a list of CREF_IDENTs. =#
        function explode(inCref::DAE.ComponentRef) ::List{DAE.ComponentRef}
              local outParts::List{DAE.ComponentRef}

              outParts = Dangerous.listReverse(explode_tail(inCref, nil))
          outParts
        end

        function explode_tail(inCref::DAE.ComponentRef, inParts::List{<:DAE.ComponentRef}) ::List{DAE.ComponentRef}
              local outParts::List{DAE.ComponentRef}

              outParts = begin
                  local first_cr::DAE.ComponentRef
                  local rest_cr::DAE.ComponentRef
                @match (inCref, inParts) begin
                  (DAE.CREF_QUAL(componentRef = rest_cr), _)  => begin
                      first_cr = crefFirstCref(inCref)
                    explode_tail(rest_cr, _cons(first_cr, inParts))
                  end

                  _  => begin
                      _cons(inCref, inParts)
                  end
                end
              end
          outParts
        end

         #= Constructs a cref from a list of CREF_IDENTs. =#
        function implode(inParts::List{<:DAE.ComponentRef}) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              local first::DAE.ComponentRef
              local rest::List{DAE.ComponentRef}

              outCref = implode_reverse(listReverse(inParts))
          outCref
        end

         #= Constructs a cref from a reversed list of CREF_IDENTs. =#
        function implode_reverse(inParts::List{<:DAE.ComponentRef}) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              local first::DAE.ComponentRef
              local rest::List{DAE.ComponentRef}

              @match _cons(first, rest) = inParts
              outCref = implode_tail(rest, first)
          outCref
        end

        function implode_tail(inParts::List{<:DAE.ComponentRef}, inAccumCref::DAE.ComponentRef) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              outCref = begin
                  local id::DAE.Ident
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local rest::List{DAE.ComponentRef}
                  local cr::DAE.ComponentRef
                @match (inParts, inAccumCref) begin
                  (DAE.CREF_IDENT(id, ty, subs) <| rest, _)  => begin
                      cr = DAE.CREF_QUAL(id, ty, subs, inAccumCref)
                    implode_tail(rest, cr)
                  end

                  ( nil(), _)  => begin
                    inAccumCref
                  end
                end
              end
          outCref
        end

        function identifierCount(inCref::DAE.ComponentRef) ::ModelicaInteger
              local outIdCount::ModelicaInteger

              outIdCount = identifierCount_tail(inCref, 0)
          outIdCount
        end

        function identifierCount_tail(inCref::DAE.ComponentRef, inAccumCount::ModelicaInteger) ::ModelicaInteger
              local outIdCount::ModelicaInteger

              outIdCount = begin
                  local cr::DAE.ComponentRef
                @match (inCref, inAccumCount) begin
                  (DAE.CREF_QUAL(componentRef = cr), _)  => begin
                    identifierCount_tail(cr, inAccumCount + 1)
                  end

                  _  => begin
                      inAccumCount + 1
                  end
                end
              end
          outIdCount
        end

         #= Checks that the subscripts in a cref are valid given the dimensions of the
           cref's type. Prints an error if they are not. =#
        function checkCrefSubscriptsBounds(inCref::DAE.ComponentRef, inInfo::SourceInfo)
              checkCrefSubscriptsBounds2(inCref, inCref, inInfo)
        end

        function checkCrefSubscriptsBounds2(inCref::DAE.ComponentRef, inWholeCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local ty::DAE.Type
                  local subs::List{DAE.Subscript}
                  local dims::List{DAE.Dimension}
                  local rest_cr::DAE.ComponentRef
                @match (inCref, inWholeCref, inInfo) begin
                  (DAE.CREF_QUAL(identType = ty, subscriptLst = subs, componentRef = rest_cr), _, _)  => begin
                      checkCrefSubscriptsBounds3(ty, subs, inWholeCref, inInfo)
                      checkCrefSubscriptsBounds2(rest_cr, inWholeCref, inInfo)
                    ()
                  end

                  (DAE.CREF_IDENT(identType = ty, subscriptLst = subs), _, _)  => begin
                      checkCrefSubscriptsBounds3(ty, subs, inWholeCref, inInfo)
                    ()
                  end

                  (DAE.CREF_ITER(identType = ty, subscriptLst = subs), _, _)  => begin
                      checkCrefSubscriptsBounds3(ty, subs, inWholeCref, inInfo)
                    ()
                  end
                end
              end
        end

        function checkCrefSubscriptsBounds3(inCrefType::DAE.Type, inSubscripts::List{<:DAE.Subscript}, inWholeCref::DAE.ComponentRef, inInfo::SourceInfo)
              local dims::List{DAE.Dimension}
              local subs::List{DAE.Subscript}

              dims = Types.getDimensions(inCrefType)
               #=  The type might contain dimensions from the cref part's prefix here, so
               =#
               #=  reverse the lists and check them from the back to pair up each subscript
               =#
               #=  with the correct dimension.
               =#
              dims = listReverse(dims)
              subs = listReverse(inSubscripts)
              checkCrefSubscriptsBounds4(subs, dims, 1, inWholeCref, inInfo)
        end

        function checkCrefSubscriptsBounds4(inSubscripts::List{<:DAE.Subscript}, inDimensions::List{<:DAE.Dimension}, inIndex::ModelicaInteger, inWholeCref::DAE.ComponentRef, inInfo::SourceInfo)
              _ = begin
                  local sub::DAE.Subscript
                  local rest_subs::List{DAE.Subscript}
                  local dim::DAE.Dimension
                  local rest_dims::List{DAE.Dimension}
                @match (inSubscripts, inDimensions, inIndex, inWholeCref, inInfo) begin
                  (sub <| rest_subs, dim <| rest_dims, _, _, _)  => begin
                      @match true = checkCrefSubscriptBounds(sub, dim, inIndex, inWholeCref, inInfo)
                      checkCrefSubscriptsBounds4(rest_subs, rest_dims, inIndex + 1, inWholeCref, inInfo)
                    ()
                  end

                  ( nil(), _, _, _, _)  => begin
                    ()
                  end

                  (_,  nil(), _, _, _)  => begin
                    ()
                  end
                end
              end
               #=  Cref types are sometimes messed up, and we might get a cref with
               =#
               #=  subscripts but no dimensions here. That's usually fine, since the
               =#
               #=  subscripts in those cases are generated by the compiler.
               =#
        end

        function checkCrefSubscriptBounds(inSubscript::DAE.Subscript, inDimension::DAE.Dimension, inIndex::ModelicaInteger, inWholeCref::DAE.ComponentRef, inInfo::SourceInfo) ::Bool
              local outIsValid::Bool

              outIsValid = begin
                  local idx::ModelicaInteger
                  local idx2::ModelicaInteger
                  local dim::ModelicaInteger
                  local expl::List{DAE.Exp}
                  local exp::DAE.Exp
                   #= /*/ allow index 0 with dimension 0
                      case (DAE.INDEX(exp = exp as DAE.ICONST(integer = idx)),
                            DAE.DIM_INTEGER(integer = dim), _, _, _)
                        equation
                          true = idx == 0 and dim == 0;
                        then
                          true;*/ =#
                @matchcontinue (inSubscript, inDimension, inIndex, inWholeCref, inInfo) begin
                  (DAE.INDEX(exp = exp && DAE.ICONST(integer = idx)), DAE.DIM_INTEGER(integer = dim), _, _, _)  => begin
                      @match false = idx > 0 && idx <= dim
                      printSubscriptBoundsError(exp, inDimension, inIndex, inWholeCref, inInfo)
                    false
                  end

                  (DAE.SLICE(exp = DAE.ARRAY(array = expl)), DAE.DIM_INTEGER(integer = dim), _, _, _)  => begin
                      exp = ListUtil.getMemberOnTrue(dim, expl, subscriptExpOutOfBounds)
                      printSubscriptBoundsError(exp, inDimension, inIndex, inWholeCref, inInfo)
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outIsValid
        end

        function subscriptExpOutOfBounds(inDimSize::ModelicaInteger, inSubscriptExp::DAE.Exp) ::Bool
              local outOutOfBounds::Bool

              outOutOfBounds = begin
                  local i::ModelicaInteger
                @match (inDimSize, inSubscriptExp) begin
                  (_, DAE.ICONST(integer = i))  => begin
                    i < 1 || i > inDimSize
                  end

                  _  => begin
                      false
                  end
                end
              end
          outOutOfBounds
        end

        function printSubscriptBoundsError(inSubscriptExp::DAE.Exp, inDimension::DAE.Dimension, inIndex::ModelicaInteger, inCref::DAE.ComponentRef, inInfo::SourceInfo)
              local sub_str::String
              local dim_str::String
              local idx_str::String
              local cref_str::String

              sub_str = ExpressionDump.printExpStr(inSubscriptExp)
              dim_str = ExpressionDump.dimensionString(inDimension)
              idx_str = intString(inIndex)
              cref_str = printComponentRefStr(inCref)
              Error.addSourceMessage(Error.ARRAY_INDEX_OUT_OF_BOUNDS, list(sub_str, idx_str, dim_str, cref_str), inInfo)
        end

        function crefAppendedSubs(cref::DAE.ComponentRef) ::String
              local s::String

              local s1::String
              local s2::String

              s1 = stringDelimitList(toStringList(cref), "_P")
              s2 = stringDelimitList(ListUtil.mapMap(crefSubs(cref), Expression.getSubscriptExp, ExpressionDump.printExpStr), ",")
              s = s1 + "[" + s2 + "]"
          s
        end

        function writeCref(file::File.File, cref::DAE.ComponentRef, escape::File.Escape = File.Escape.None)
              local c::DAE.ComponentRef = cref

              while true
                c = begin
                  @match c begin
                    DAE.CREF_IDENT(__)  => begin
                        File.writeEscape(file, c.ident, escape)
                        writeSubscripts(file, c.subscriptLst, escape)
                        return
                      fail()
                    end

                    DAE.CREF_QUAL(ident = "\$DER")  => begin
                        File.write(file, "der(")
                        writeCref(file, c.componentRef, escape)
                        File.write(file, ")")
                        return
                      fail()
                    end

                    DAE.CREF_QUAL(ident = "\$CLKPRE")  => begin
                        File.write(file, "previous(")
                        writeCref(file, c.componentRef, escape)
                        File.write(file, ")")
                        return
                      fail()
                    end

                    DAE.CREF_QUAL(__)  => begin
                        File.writeEscape(file, c.ident, escape)
                        writeSubscripts(file, c.subscriptLst, escape)
                        File.write(file, ".")
                      c.componentRef
                    end
                  end
                end
              end
        end

        function writeSubscripts(file::File.File, subs::List{<:DAE.Subscript}, escape::File.Escape = File.Escape.None)
              local first::Bool = true
              local i::ModelicaInteger
              local exp::DAE.Exp

              if listEmpty(subs)
                return
              end
              File.write(file, "[")
              for s in subs
                if ! first
                  File.write(file, ",")
                else
                  first = false
                end
                _ = begin
                  @match s begin
                    DAE.WHOLEDIM(__)  => begin
                        File.write(file, ":")
                      ()
                    end

                    DAE.SLICE(DAE.ICONST(i))  => begin
                        File.writeInt(file, i)
                      ()
                    end

                    DAE.INDEX(DAE.ICONST(i))  => begin
                        File.writeInt(file, i)
                      ()
                    end

                    DAE.WHOLE_NONEXP(DAE.ICONST(i))  => begin
                        File.writeInt(file, i)
                      ()
                    end

                    DAE.SLICE(exp)  => begin
                        File.write(file, ExpressionDump.printExpStr(exp))
                      ()
                    end

                    DAE.INDEX(exp)  => begin
                        File.write(file, ExpressionDump.printExpStr(exp))
                      ()
                    end

                    DAE.WHOLE_NONEXP(exp)  => begin
                        File.write(file, ExpressionDump.printExpStr(exp))
                      ()
                    end
                  end
                end
              end
              File.write(file, "]")
        end

        function getConsumedMemory(inCref::DAE.ComponentRef) ::Tuple{ModelicaReal, ModelicaReal, ModelicaReal}
              local szSubs::ModelicaReal = 0
              local szTypes::ModelicaReal = 0
              local szIdents::ModelicaReal = 0

              local cr::DAE.ComponentRef = inCref
              local b::Bool = true

              while b
                (b, cr) = begin
                  @match cr begin
                    DAE.CREF_IDENT(__)  => begin
                        szIdents = szIdents + System.getSizeOfData(cr.ident)
                        szTypes = szTypes + System.getSizeOfData(cr.identType)
                        szSubs = szSubs + System.getSizeOfData(cr.subscriptLst)
                      (false, cr)
                    end

                    DAE.CREF_ITER(__)  => begin
                        szIdents = szIdents + System.getSizeOfData(cr.ident)
                        szTypes = szTypes + System.getSizeOfData(cr.identType)
                      (false, cr)
                    end

                    DAE.CREF_QUAL(__)  => begin
                        szIdents = szIdents + System.getSizeOfData(cr.ident)
                        szTypes = szTypes + System.getSizeOfData(cr.identType)
                        szSubs = szSubs + System.getSizeOfData(cr.subscriptLst)
                      (true, cr.componentRef)
                    end

                    _  => begin
                        (false, cr)
                    end
                  end
                end
              end
          (szIdents, szTypes, szSubs)
        end

        function createDifferentiatedCrefName(inCref::DAE.ComponentRef, inX::DAE.ComponentRef, inMatrixName::String) ::DAE.ComponentRef
              local outCref::DAE.ComponentRef

              local subs::List{DAE.Subscript}
              local debug::Bool = false

              if debug
                print("inCref: " + ComponentReference.printComponentRefStr(inCref) + "\\n")
              end
               #=  move subs and and type to lastCref, to move type replace by last type
               =#
               #=  and move last cref type to the last cref.
               =#
              subs = ComponentReference.crefLastSubs(inCref)
              outCref = ComponentReference.crefStripLastSubs(inCref)
              outCref = ComponentReference.replaceSubsWithString(outCref)
              if debug
                print("after full type  " + Types.printTypeStr(ComponentReference.crefTypeConsiderSubs(inCref)) + "\\n")
              end
              outCref = ComponentReference.crefSetLastType(outCref, DAE.T_UNKNOWN_DEFAULT)
              if debug
                print("after strip: " + ComponentReference.printComponentRefListStr(ComponentReference.expandCref(outCref, true)) + "\\n")
              end
               #=  join crefs
               =#
              outCref = ComponentReference.joinCrefs(outCref, ComponentReference.makeCrefIdent(DAE.partialDerivativeNamePrefix + inMatrixName, DAE.T_UNKNOWN_DEFAULT, nil))
              outCref = ComponentReference.joinCrefs(outCref, inX)
              if debug
                print("after join: " + ComponentReference.printComponentRefListStr(ComponentReference.expandCref(outCref, true)) + "\\n")
              end
               #=  fix subs and type of the last cref
               =#
              outCref = ComponentReference.crefSetLastSubs(outCref, subs)
              outCref = ComponentReference.crefSetLastType(outCref, ComponentReference.crefLastType(inCref))
              if debug
                print("outCref: " + ComponentReference.printComponentRefStr(outCref) + "\\n")
              end
          outCref
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

  module UnitAbsynBuilder


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

        import UnitAbsyn

        import DAE

        import MMath

        import FCore

        import HashTable

        import Absyn

        import AbsynUtil

        import ArrayUtil

        import BaseHashTable

        import ComponentReference

        import DAEUtil

        import Expression

        import ExpressionDump

        import Flags

        import FNode

        import FGraph

        import ListUtil

        import Lookup

        import SCode

        import AbsynToSCode

        import Types

        import UnitParserExt

        import Util

         #= traverses all dae variables and adjusts weights depending on defineunits defined
        in the scopes of the classLst for each variable =#
        function registerUnitWeights(cache::FCore.Cache, env::FCore.Graph, dae::DAE.DAElist)
              local paths::List{Absyn.Path}
              local du::List{SCode.Element}

              _ = begin
                  local elts::List{DAE.Element}
                @matchcontinue (cache, env, dae) begin
                  (_, _, _)  => begin
                      @match false = Flags.getConfigBool(Flags.UNIT_CHECKING)
                    ()
                  end

                  (_, _, DAE.DAE_LIST(elementLst = elts))  => begin
                      paths = ListUtil.unionList(ListUtil.map(elts, DAEUtil.getClassList))
                      du = ListUtil.unionList(ListUtil.map1(paths, retrieveUnitsFromEnv, (cache, env)))
                      registerUnitWeightDefineunits(du)
                    ()
                  end
                end
              end
               #= /* TODO: This is very unefficient. It increases instantiationtime by factor 2 for
                     instantiation of largeTests/TestNandTotal.mo */ =#
        end

         #= help function to registerUnitWeights =#
        function retrieveUnitsFromEnv(p::Absyn.Path, tpl::Tuple{<:FCore.Cache, FCore.Graph}) ::List{SCode.Element}
              local du::List{SCode.Element}

              du = begin
                  local env::FCore.Graph
                  local r::FCore.MMRef
                @matchcontinue (p, tpl) begin
                  (_, _)  => begin
                      (_, _, env) = Lookup.lookupClass(Util.tuple21(tpl), Util.tuple22(tpl), p, NONE())
                      r = FGraph.lastScopeRef(env)
                      r = FNode.child(r, FNode.duNodeName)
                      @match FCore.N(data = FCore.DU(du)) = FNode.fromRef(r)
                    du
                  end

                  _  => begin
                      nil
                  end
                end
              end
               #=  get the defined units node
               =#
          du
        end

         #= help function to registerUnitWeightForClass =#
        function registerUnitWeightDefineunits(du::List{<:SCode.Element})
              _ = begin
                @matchcontinue du begin
                   nil()  => begin
                      registerUnitWeightDefineunits2(list(SCode.DEFINEUNIT("m", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("kg", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("s", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("A", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("k", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("mol", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("cd", SCode.PUBLIC(), NONE(), NONE()), SCode.DEFINEUNIT("rad", SCode.PUBLIC(), SOME("m/m"), NONE()), SCode.DEFINEUNIT("sr", SCode.PUBLIC(), SOME("m2/m2"), NONE()), SCode.DEFINEUNIT("Hz", SCode.PUBLIC(), SOME("s-1"), SOME(0.8)), SCode.DEFINEUNIT("N", SCode.PUBLIC(), SOME("m.kg.s-2"), NONE()), SCode.DEFINEUNIT("Pa", SCode.PUBLIC(), SOME("N/m2"), NONE()), SCode.DEFINEUNIT("W", SCode.PUBLIC(), SOME("J/s"), NONE()), SCode.DEFINEUNIT("J", SCode.PUBLIC(), SOME("N.m"), NONE()), SCode.DEFINEUNIT("C", SCode.PUBLIC(), SOME("s.A"), NONE()), SCode.DEFINEUNIT("V", SCode.PUBLIC(), SOME("W/A"), NONE()), SCode.DEFINEUNIT("F", SCode.PUBLIC(), SOME("C/V"), NONE()), SCode.DEFINEUNIT("Ohm", SCode.PUBLIC(), SOME("V/A"), NONE()), SCode.DEFINEUNIT("S", SCode.PUBLIC(), SOME("A/V"), NONE()), SCode.DEFINEUNIT("Wb", SCode.PUBLIC(), SOME("V.s"), NONE()), SCode.DEFINEUNIT("T", SCode.PUBLIC(), SOME("Wb/m2"), NONE()), SCode.DEFINEUNIT("H", SCode.PUBLIC(), SOME("Wb/A"), NONE()), SCode.DEFINEUNIT("lm", SCode.PUBLIC(), SOME("cd.sr"), NONE()), SCode.DEFINEUNIT("lx", SCode.PUBLIC(), SOME("lm/m2"), NONE()), SCode.DEFINEUNIT("Bq", SCode.PUBLIC(), SOME("s-1"), SOME(0.8)), SCode.DEFINEUNIT("Gy", SCode.PUBLIC(), SOME("J/kg"), NONE()), SCode.DEFINEUNIT("Sv", SCode.PUBLIC(), SOME("cd.sr"), NONE()), SCode.DEFINEUNIT("kat", SCode.PUBLIC(), SOME("s-1.mol"), NONE())))
                    ()
                  end

                  _  => begin
                        registerUnitWeightDefineunits2(du)
                      ()
                  end
                end
              end
               #= /* No defineunits found, for backward compatibility, use default implementation:
                   SI system ,with lower cost on Hz and Bq */ =#
        end

         #= help function to registerUnitWeightDefineunits =#
        function registerUnitWeightDefineunits2(idu::List{<:SCode.Element})
              _ = begin
                  local n::String
                  local w::ModelicaReal
                  local du::List{SCode.Element}
                @matchcontinue idu begin
                  SCode.DEFINEUNIT(name = n, weight = SOME(w)) <| du  => begin
                      UnitParserExt.registerWeight(n, w)
                      registerUnitWeightDefineunits2(du)
                    ()
                  end

                  SCode.DEFINEUNIT(weight = NONE()) <| du  => begin
                      registerUnitWeightDefineunits2(du)
                    ()
                  end

                  _ <| du  => begin
                      registerUnitWeightDefineunits2(du)
                    ()
                  end

                   nil()  => begin
                    ()
                  end
                end
              end
        end

         #= traverses the Absyn.Program and registers all defineunits.
        Note: this requires that instantiation is done on a 'total program', so only defineunits that
        are referenced in the model are picked up
         =#
        function registerUnits(prg::Absyn.Program)
              _ = begin
                @matchcontinue prg begin
                  _  => begin
                      @match true = Flags.getConfigBool(Flags.UNIT_CHECKING)
                      (_, _, _) = AbsynUtil.traverseClasses(prg, NONE(), registerUnitInClass, 0, false)
                    ()
                  end

                  _  => begin
                        @match false = Flags.getConfigBool(Flags.UNIT_CHECKING)
                      ()
                  end
                end
              end
               #=  defineunits must be in public section.
               =#
        end

         #=  help function to registerUnits =#
        function registerUnitInClass(inTpl::Tuple{<:Absyn.Class, Option{<:Absyn.Path}, ModelicaInteger}) ::Tuple{Absyn.Class, Option{Absyn.Path}, ModelicaInteger}
              local outTpl::Tuple{Absyn.Class, Option{Absyn.Path}, ModelicaInteger}

              outTpl = begin
                  local cl::Absyn.Class
                  local pa::Option{Absyn.Path}
                  local i::ModelicaInteger
                  local defunits::List{Absyn.Element}
                  local elts::List{Absyn.ElementItem}
                  local n::String
                @matchcontinue inTpl begin
                  (cl && Absyn.CLASS(__), pa, i)  => begin
                      elts = AbsynUtil.getElementItemsInClass(cl)
                      defunits = AbsynUtil.getDefineUnitsInElements(elts)
                      registerDefineunits(defunits)
                    (cl, pa, i)
                  end

                  (cl, pa, i)  => begin
                    (cl, pa, i)
                  end
                end
              end
          outTpl
        end

         #= help function to registerUnitInClass =#
        function registerDefineunits(elts::List{<:Absyn.Element})
              _ = begin
                  local name::String
                  local args::List{Absyn.NamedArg}
                  local du::Absyn.Element
                  local exp::String
                  local weight::ModelicaReal
                @matchcontinue elts begin
                   nil()  => begin
                      registerDefineunits2(list(Absyn.DEFINEUNIT("m", nil), Absyn.DEFINEUNIT("kg", nil), Absyn.DEFINEUNIT("s", nil), Absyn.DEFINEUNIT("A", nil), Absyn.DEFINEUNIT("k", nil), Absyn.DEFINEUNIT("mol", nil), Absyn.DEFINEUNIT("cd", nil), Absyn.DEFINEUNIT("rad", list(Absyn.NAMEDARG("exp", Absyn.STRING("m/m")))), Absyn.DEFINEUNIT("sr", list(Absyn.NAMEDARG("exp", Absyn.STRING("m2/m2")))), Absyn.DEFINEUNIT("Hz", list(Absyn.NAMEDARG("exp", Absyn.STRING("s-1")), Absyn.NAMEDARG("weight", Absyn.REAL("0.8")))), Absyn.DEFINEUNIT("N", list(Absyn.NAMEDARG("exp", Absyn.STRING("m.kg.s-2")))), Absyn.DEFINEUNIT("Pa", list(Absyn.NAMEDARG("exp", Absyn.STRING("N/m2")))), Absyn.DEFINEUNIT("W", list(Absyn.NAMEDARG("exp", Absyn.STRING("J/s")))), Absyn.DEFINEUNIT("J", list(Absyn.NAMEDARG("exp", Absyn.STRING("N.m")))), Absyn.DEFINEUNIT("C", list(Absyn.NAMEDARG("exp", Absyn.STRING("s.A")))), Absyn.DEFINEUNIT("V", list(Absyn.NAMEDARG("exp", Absyn.STRING("W/A")))), Absyn.DEFINEUNIT("F", list(Absyn.NAMEDARG("exp", Absyn.STRING("C/V")))), Absyn.DEFINEUNIT("Ohm", list(Absyn.NAMEDARG("exp", Absyn.STRING("V/A")))), Absyn.DEFINEUNIT("S", list(Absyn.NAMEDARG("exp", Absyn.STRING("A/V")))), Absyn.DEFINEUNIT("Wb", list(Absyn.NAMEDARG("exp", Absyn.STRING("V.s")))), Absyn.DEFINEUNIT("T", list(Absyn.NAMEDARG("exp", Absyn.STRING("Wb/m2")))), Absyn.DEFINEUNIT("H", list(Absyn.NAMEDARG("exp", Absyn.STRING("Wb/A")))), Absyn.DEFINEUNIT("lm", list(Absyn.NAMEDARG("exp", Absyn.STRING("cd.sr")))), Absyn.DEFINEUNIT("lx", list(Absyn.NAMEDARG("exp", Absyn.STRING("lm/m2")))), Absyn.DEFINEUNIT("Bq", list(Absyn.NAMEDARG("exp", Absyn.STRING("s-1")), Absyn.NAMEDARG("weight", Absyn.REAL("0.8")))), Absyn.DEFINEUNIT("Gy", list(Absyn.NAMEDARG("exp", Absyn.STRING("J/kg")))), Absyn.DEFINEUNIT("Sv", list(Absyn.NAMEDARG("exp", Absyn.STRING("cd.sr")))), Absyn.DEFINEUNIT("kat", list(Absyn.NAMEDARG("exp", Absyn.STRING("s-1.mol"))))))
                    ()
                  end

                  _  => begin
                        registerDefineunits2(elts)
                      ()
                  end
                end
              end
        end

         #= help function to registerUnitInClass =#
        function registerDefineunits2(elts::List{<:Absyn.Element})
              _ = begin
                  local exp::String
                  local name::String
                  local args::List{Absyn.NamedArg}
                  local du::Absyn.Element
                  local weight::ModelicaReal
                  local rest::List{Absyn.Element}
                @matchcontinue elts begin
                   nil()  => begin
                    ()
                  end

                  du && Absyn.DEFINEUNIT(__) <| rest  => begin
                      @match list(SCode.DEFINEUNIT(name, _, SOME(exp), _)) = AbsynToSCode.translateElement(du, SCode.PUBLIC())
                      UnitParserExt.addDerived(name, exp)
                      registerDefineunits2(rest)
                    ()
                  end

                  du && Absyn.DEFINEUNIT(__) <| rest  => begin
                      @match list(SCode.DEFINEUNIT(name, _, NONE(), _)) = AbsynToSCode.translateElement(du, SCode.PUBLIC())
                      UnitParserExt.addBase(name)
                      registerDefineunits2(rest)
                    ()
                  end

                  _  => begin
                        print("registerDefineunits failed\\n")
                      fail()
                  end
                end
              end
               #= /* Derived unit with weigth */ =#
               #= /*case((du as Absyn.DEFINEUNIT(name=_))::elts) equation
                     {SCode.DEFINEUNIT(name,SOME(exp),_)} = AbsynToSCode.translateElement(du,false);
                     UnitParserExt.addDerivedWeight(name,exp,weight);
                     registerDefineunits(elts);
                   then ();*/ =#
               #= /* Derived unit without weigth */ =#
               #= /* base unit does not not have weight*/ =#
        end

         #= Adds a unit to the UnitAbsyn.Store =#
        function add(unit::UnitAbsyn.Unit, ist::UnitAbsyn.Store) ::Tuple{UnitAbsyn.Store, ModelicaInteger}
              local index::ModelicaInteger
              local outSt::UnitAbsyn.Store

              (outSt, index) = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local newIndx::ModelicaInteger
                  local numElts::ModelicaInteger
                  local st::UnitAbsyn.Store
                @matchcontinue (unit, ist) begin
                  (_, st && UnitAbsyn.STORE(storeVector = vector, numElts = numElts))  => begin
                      @match true = numElts == arrayLength(vector)
                      st = expandStore(st)
                      (st, index) = add(unit, st)
                    (st, index)
                  end

                  (_, UnitAbsyn.STORE(storeVector = vector, numElts = numElts))  => begin
                      newIndx = numElts + 1
                      vector = arrayUpdate(vector, newIndx, SOME(unit))
                    (UnitAbsyn.STORE(vector, newIndx), newIndx)
                  end
                end
              end
          (outSt, index)
        end

         #=    =#
        function updateInstStore(store::UnitAbsyn.InstStore, st::UnitAbsyn.Store) ::UnitAbsyn.InstStore
              local outStore::UnitAbsyn.InstStore

              outStore = begin
                  local ht::HashTable.HashTableType
                  local res::Option{UnitAbsyn.UnitCheckResult}
                @match (store, st) begin
                  (UnitAbsyn.INSTSTORE(_, ht, res), _)  => begin
                    UnitAbsyn.INSTSTORE(st, ht, res)
                  end

                  (UnitAbsyn.NOSTORE(__), _)  => begin
                    UnitAbsyn.NOSTORE()
                  end
                end
              end
          outStore
        end

         #= Expands store to make room for more entries.
        Expansion factor: 1.4
         =#
        function expandStore(st::UnitAbsyn.Store) ::UnitAbsyn.Store
              local outSt::UnitAbsyn.Store

              outSt = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local indx::ModelicaInteger
                  local incr::ModelicaInteger
                @match st begin
                  UnitAbsyn.STORE(vector, indx)  => begin
                      incr = intMin(1, realInt(intReal(indx) * 0.4))
                      vector = ArrayUtil.expand(incr, vector, NONE())
                    UnitAbsyn.STORE(vector, indx)
                  end
                end
              end
          outSt
        end

         #= Updates  unit at index in UnitAbsyn.Store =#
        function update(unit::UnitAbsyn.Unit, index::ModelicaInteger, st::UnitAbsyn.Store) ::UnitAbsyn.Store
              local outSt::UnitAbsyn.Store

              outSt = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local indx::ModelicaInteger
                @matchcontinue (unit, index, st) begin
                  (_, _, UnitAbsyn.STORE(vector, indx))  => begin
                      vector = arrayUpdate(vector, index, SOME(unit)) #= destroys  =#
                    UnitAbsyn.STORE(vector, indx)
                  end

                  _  => begin
                        print("storing unit at index ")
                        print(intString(index))
                        print(" failed\\n")
                      fail()
                  end
                end
              end
          outSt
        end

         #= finds a unit in the UnitAbsyn.Store given an index =#
        function find(index::ModelicaInteger, st::UnitAbsyn.Store) ::UnitAbsyn.Unit
              local unit::UnitAbsyn.Unit

              unit = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local indx::ModelicaInteger
                @matchcontinue (index, st) begin
                  (_, UnitAbsyn.STORE(vector, _))  => begin
                      @match SOME(unit) = vector[index]
                    unit
                  end

                  _  => begin
                        print(" finding store at index ")
                        print(intString(index))
                        print(" failed\\n")
                      fail()
                  end
                end
              end
          unit
        end

         #= Retrives the Store from an InstStore =#
        function instGetStore(store::UnitAbsyn.InstStore) ::UnitAbsyn.Store
              local st::UnitAbsyn.Store

              st = begin
                @match store begin
                  UnitAbsyn.INSTSTORE(st, _, _)  => begin
                    st
                  end

                  UnitAbsyn.NOSTORE(__)  => begin
                    emptyStore()
                  end
                end
              end
          st
        end

         #= returns an empty InstStore =#
        function emptyInstStore() ::UnitAbsyn.InstStore
              local st::UnitAbsyn.InstStore

              st = emptyInstStore2(Flags.getConfigBool(Flags.UNIT_CHECKING))
          st
        end

         #= returns an empty InstStore =#
        function emptyInstStore2(wantInstStore::Bool) ::UnitAbsyn.InstStore
              local st::UnitAbsyn.InstStore

              st = begin
                  local s::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                @match wantInstStore begin
                  true  => begin
                      s = emptyStore()
                      ht = HashTable.emptyHashTable()
                    UnitAbsyn.INSTSTORE(s, ht, NONE())
                  end

                  _  => begin
                      UnitAbsyn.noStore
                  end
                end
              end
          st
        end

         #= Returns an empty store with 10 empty array elements =#
        function emptyStore() ::UnitAbsyn.Store
              local st::UnitAbsyn.Store

              local vector::Array{Option{UnitAbsyn.Unit}}

              vector = arrayCreate(10, NONE())
              st = UnitAbsyn.STORE(vector, 0)
          st
        end

         #= print the terms to stdout =#
        function printTerms(terms::UnitAbsyn.UnitTerms)
              print(printTermsStr(terms))
        end

         #= print the terms to a string =#
        function printTermsStr(terms::UnitAbsyn.UnitTerms) ::String
              local str::String

              str = "{" + stringDelimitList(ListUtil.map(terms, printTermStr), ",") + "}"
          str
        end

         #= print one term to a string =#
        function printTermStr(term::UnitAbsyn.UnitTerm) ::String
              local str::String

              str = begin
                  local ut1::UnitAbsyn.UnitTerm
                  local ut2::UnitAbsyn.UnitTerm
                  local s1::String
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local e::DAE.Exp
                @match term begin
                  UnitAbsyn.ADD(_, _, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.SUB(_, _, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.MUL(_, _, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.DIV(_, _, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.EQN(_, _, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.LOC(_, e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end

                  UnitAbsyn.POW(_, MMath.RATIONAL(_, _), e)  => begin
                      s1 = ExpressionDump.printExpStr(e)
                    s1
                  end
                end
              end
          str
        end

         #= prints the inst store to stdout =#
        function printInstStore(st::UnitAbsyn.InstStore)
              _ = begin
                  local s::UnitAbsyn.Store
                  local h::HashTable.HashTableType
                @match st begin
                  UnitAbsyn.INSTSTORE(s, h, _)  => begin
                      print("instStore, s:")
                      printStore(s)
                      print("\\nht:")
                      BaseHashTable.dumpHashTable(h)
                    ()
                  end

                  UnitAbsyn.NOSTORE(__)  => begin
                    ()
                  end
                end
              end
        end

         #= prints the store to stdout =#
        function printStore(st::UnitAbsyn.Store)
              _ = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local indx::ModelicaInteger
                  local lst::List{Option{UnitAbsyn.Unit}}
                @match st begin
                  UnitAbsyn.STORE(vector, _)  => begin
                      lst = arrayList(vector)
                      printStore2(lst, 1)
                    ()
                  end
                end
              end
        end

         #= help function to printStore =#
        function printStore2(lst::List{<:Option{<:UnitAbsyn.Unit}}, indx::ModelicaInteger)
              _ = begin
                  local unit::UnitAbsyn.Unit
                  local rest::List{Option{UnitAbsyn.Unit}}
                @match (lst, indx) begin
                  ( nil(), _)  => begin
                    ()
                  end

                  (SOME(unit) <| rest, _)  => begin
                      print(intString(indx))
                      print("->")
                      printUnit(unit)
                      print("\\n")
                      printStore2(rest, indx + 1)
                    ()
                  end

                  (NONE() <| _, _)  => begin
                    ()
                  end
                end
              end
        end

         #= prints a unit to stdout (only for debugging) =#
        function printUnit(unit::UnitAbsyn.Unit)
              _ = begin
                  local typeparams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local baseunits::List{MMath.Rational}
                   #= /*case(unit) equation
                        print(unit2str(unit));
                      then();*/ =#
                @matchcontinue unit begin
                  UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT( nil(), baseunits))  => begin
                      print(printBaseUnitsStr(baseunits))
                      print(" [")
                      print(unit2str(unit))
                      print("]")
                    ()
                  end

                  UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(typeparams, baseunits))  => begin
                      print(stringDelimitList(ListUtil.map(typeparams, printTypeParameterStr), ","))
                      print(printBaseUnitsStr(baseunits))
                      print(" [")
                      print(unit2str(unit))
                      print("]")
                    ()
                  end

                  UnitAbsyn.UNSPECIFIED(__)  => begin
                      print("Unspecified")
                    ()
                  end
                end
              end
        end

         #= help function to printUnit =#
        function printBaseUnitsStr(lst::List{<:MMath.Rational}) ::String
              local str::String

              str = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                @matchcontinue lst begin
                  MMath.RATIONAL(i1, i2) <| MMath.RATIONAL(i3, i4) <| _  => begin
                      str = "m^(" + intString(i1) + "/" + intString(i2) + ")" + "s^(" + intString(i3) + "/" + intString(i4) + ")"
                    str
                  end

                   nil()  => begin
                    ""
                  end

                  _  => begin
                      "printBaseUnitsStr failed len:" + intString(listLength(lst)) + "\\n"
                  end
                end
              end
          str
        end

         #= help function to printUnit =#
        function printTypeParameterStr(typeParam::Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}) ::String
              local str::String

              str = begin
                  local name::String
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local indx::ModelicaInteger
                @match typeParam begin
                  (MMath.RATIONAL(0, 0), UnitAbsyn.TYPEPARAMETER(name, indx))  => begin
                      str = name + "[indx =" + intString(indx) + "]"
                    str
                  end

                  (MMath.RATIONAL(i1, 1), UnitAbsyn.TYPEPARAMETER(name, indx))  => begin
                      str = name + "^" + intString(i1) + "[indx=" + intString(indx) + "]"
                    str
                  end

                  (MMath.RATIONAL(i1, i2), UnitAbsyn.TYPEPARAMETER(name, indx))  => begin
                      str = name + "^(" + intString(i1) + "/" + intString(i2) + ")" + "[indx=" + intString(indx) + "]"
                    str
                  end
                end
              end
          str
        end

         #= splits a list of Rationals into a list of numerators and denominators =#
        function splitRationals(inRationals::List{<:MMath.Rational}) ::Tuple{List{ModelicaInteger}, List{ModelicaInteger}}
              local denoms::List{ModelicaInteger}
              local nums::List{ModelicaInteger}

              (nums, denoms) = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local rationals::List{MMath.Rational}
                @match inRationals begin
                   nil()  => begin
                    (nil, nil)
                  end

                  MMath.RATIONAL(i1, i2) <| rationals  => begin
                      (nums, denoms) = splitRationals(rationals)
                    (_cons(i1, nums), _cons(i2, denoms))
                  end
                end
              end
          (nums, denoms)
        end

         #= joins a lists of numerators and denominators into list of Rationals =#
        function joinRationals(inums::List{<:ModelicaInteger}, idenoms::List{<:ModelicaInteger}) ::List{MMath.Rational}
              local rationals::List{MMath.Rational}

              rationals = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local nums::List{ModelicaInteger}
                  local denoms::List{ModelicaInteger}
                @match (inums, idenoms) begin
                  ( nil(),  nil())  => begin
                    nil
                  end

                  (i1 <| nums, i2 <| denoms)  => begin
                      rationals = joinRationals(nums, denoms)
                    _cons(MMath.RATIONAL(i1, i2), rationals)
                  end
                end
              end
          rationals
        end

         #= creates type parameter lists from list of numerators , denominators and typeparameter names =#
        function joinTypeParams(inums::List{<:ModelicaInteger}, idenoms::List{<:ModelicaInteger}, itpstrs::List{<:String}, funcInstIdOpt::Option{<:ModelicaInteger}) ::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
              local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}

              typeParams = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local tpParam::String
                  local s::String
                  local nums::List{ModelicaInteger}
                  local denoms::List{ModelicaInteger}
                  local tpstrs::List{String}
                @match (inums, idenoms, itpstrs, funcInstIdOpt) begin
                  ( nil(),  nil(),  nil(), _)  => begin
                    nil
                  end

                  (i1 <| nums, i2 <| denoms, tpParam <| tpstrs, _)  => begin
                      typeParams = joinTypeParams(nums, denoms, tpstrs, funcInstIdOpt)
                      s = Util.stringOption(Util.applyOption(funcInstIdOpt, intString))
                      tpParam = tpParam + s
                    _cons((MMath.RATIONAL(i1, i2), UnitAbsyn.TYPEPARAMETER(tpParam, 0)), typeParams)
                  end
                end
              end
          typeParams
        end

         #= splits type parameter lists into numerators, denominators and typeparameter names =#
        function splitTypeParams(iTypeParams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}) ::Tuple{List{ModelicaInteger}, List{ModelicaInteger}, List{String}}
              local tpstrs::List{String}
              local denoms::List{ModelicaInteger}
              local nums::List{ModelicaInteger}

              (nums, denoms, tpstrs) = begin
                  local tpParam::String
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                @match iTypeParams begin
                   nil()  => begin
                    (nil, nil, nil)
                  end

                  (MMath.RATIONAL(i1, i2), UnitAbsyn.TYPEPARAMETER(tpParam, _)) <| typeParams  => begin
                      (nums, denoms, tpstrs) = splitTypeParams(typeParams)
                    (_cons(i1, nums), _cons(i2, denoms), _cons(tpParam, tpstrs))
                  end
                end
              end
          (nums, denoms, tpstrs)
        end

         #= builds unit terms and stores for a DAE. It also returns a hashtable that maps
        variable names to store locations. =#
        function instBuildUnitTerms(env::FCore.Graph, dae::DAE.DAElist, compDae::DAE.DAElist #= to collect variable bindings =#, store::UnitAbsyn.InstStore) ::Tuple{UnitAbsyn.InstStore, UnitAbsyn.UnitTerms}
              local terms::UnitAbsyn.UnitTerms
              local outStore::UnitAbsyn.InstStore

              (outStore, terms) = begin
                  local st::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                  local terms2::UnitAbsyn.UnitTerms
                  local res::Option{UnitAbsyn.UnitCheckResult}
                @matchcontinue (env, dae, compDae, store) begin
                  (_, _, _, UnitAbsyn.NOSTORE(__))  => begin
                    (UnitAbsyn.NOSTORE(), nil)
                  end

                  (_, _, _, UnitAbsyn.INSTSTORE(st, ht, res))  => begin
                      (terms, st) = buildTerms(env, dae, ht, st)
                      (terms2, st) = buildTerms(env, compDae, ht, st) #= to get bindings of scalar variables =#
                      terms = listReverse(terms)
                      terms = ListUtil.append_reverse(terms2, terms)
                      st = createTypeParameterLocations(st)
                    (UnitAbsyn.INSTSTORE(st, ht, res), terms)
                  end

                  _  => begin
                        print("instBuildUnitTerms failed!!\\n")
                      fail()
                  end
                end
              end
               #= print(\"built terms, store :\"); printStore(st);
               =#
               #= print(\"ht =\");BaseHashTable.dumpHashTable(ht);
               =#
               #=  print(\"built type param, store :\"); printStore(st);
               =#
          (outStore, terms)
        end

         #= builds unit terms and stores for a DAE. It also returns a hashtable that maps
        variable names to store locations. =#
        function buildUnitTerms(env::FCore.Graph, dae::DAE.DAElist) ::Tuple{UnitAbsyn.UnitTerms, UnitAbsyn.Store, HashTable.HashTableType}
              local ht::HashTable.HashTableType
              local store::UnitAbsyn.Store
              local terms::UnitAbsyn.UnitTerms

              (store, ht) = buildStores(dae)
              (terms, store) = buildTerms(env, dae, ht, store)
              store = createTypeParameterLocations(store)
          (terms, store, ht)
        end

         #= Called when instantiating a Real class =#
        function instAddStore(istore::UnitAbsyn.InstStore, itp::DAE.Type, cr::DAE.ComponentRef) ::UnitAbsyn.InstStore
              local outStore::UnitAbsyn.InstStore

              outStore = begin
                  local st::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                  local unitStr::String
                  local unit::UnitAbsyn.Unit
                  local indx::ModelicaInteger
                  local varLst::List{DAE.Var}
                  local res::Option{UnitAbsyn.UnitCheckResult}
                  local store::UnitAbsyn.InstStore
                  local tp::DAE.Type
                @matchcontinue (istore, itp, cr) begin
                  (UnitAbsyn.NOSTORE(__), _, _)  => begin
                    istore
                  end

                  (UnitAbsyn.INSTSTORE(st, ht, res), DAE.T_REAL(varLst = varLst), _)  => begin
                      for v in varLst
                        _ = begin
                          @match v begin
                            DAE.TYPES_VAR(name = "unit", binding = DAE.EQBOUND(exp = DAE.SCONST(unitStr)))  => begin
                                unit = str2unit(unitStr, NONE())
                                unit = if 0 == stringCompare(unitStr, "")
                                      UnitAbsyn.UNSPECIFIED()
                                    else
                                      unit
                                    end
                                (st, indx) = add(unit, st)
                                ht = BaseHashTable.add((cr, indx), ht)
                                outStore = UnitAbsyn.INSTSTORE(st, ht, res)
                                return
                              ()
                            end

                            _  => begin
                                ()
                            end
                          end
                        end
                      end
                      (st, indx) = add(UnitAbsyn.UNSPECIFIED(), st)
                      ht = BaseHashTable.add((cr, indx), ht)
                    UnitAbsyn.INSTSTORE(st, ht, res)
                  end

                  (store, DAE.T_SUBTYPE_BASIC(complexType = tp), _)  => begin
                    instAddStore(store, tp, cr)
                  end

                  _  => begin
                      istore
                  end
                end
              end
          outStore
        end

         #= return the number of elements of the store =#
        function storeSize(store::UnitAbsyn.Store) ::ModelicaInteger
              local size::ModelicaInteger

              size = begin
                @match store begin
                  UnitAbsyn.STORE(_, size)  => begin
                    size
                  end
                end
              end
          size
        end

         #= for each unique type parameter, create an UNSPECIFIED unit
        and add to the store. =#
        function createTypeParameterLocations(store::UnitAbsyn.Store) ::UnitAbsyn.Store
              local outStore::UnitAbsyn.Store

              local nextElement::ModelicaInteger
              local storeSz::ModelicaInteger

              storeSz = storeSize(store)
              (outStore, _, nextElement) = createTypeParameterLocations2(store, HashTable.emptyHashTable(), 1, storeSz + 1)
              outStore = addUnspecifiedStores(nextElement - storeSz - 1, outStore)
          outStore
        end

         #=  adds n unspecified =#
        function addUnspecifiedStores(n::ModelicaInteger, istore::UnitAbsyn.Store) ::UnitAbsyn.Store
              local outStore::UnitAbsyn.Store

              outStore = begin
                  local store::UnitAbsyn.Store
                @matchcontinue (n, istore) begin
                  (0, store)  => begin
                    store
                  end

                  (_, _)  => begin
                      @match true = n < 0
                      print("addUnspecifiedStores n < 0!\\n")
                    fail()
                  end

                  (_, store)  => begin
                      @match true = n > 0
                      (store, _) = add(UnitAbsyn.UNSPECIFIED(), store)
                      store = addUnspecifiedStores(n - 1, store)
                    store
                  end
                end
              end
          outStore
        end

         #= help function =#
        function createTypeParameterLocations2(istore::UnitAbsyn.Store, iht::HashTable.HashTableType, i::ModelicaInteger #= iterated =#, inextElt::ModelicaInteger) ::Tuple{UnitAbsyn.Store, HashTable.HashTableType, ModelicaInteger}
              local outNextElt::ModelicaInteger
              local outHt::HashTable.HashTableType
              local outStore::UnitAbsyn.Store

              (outStore, outHt, outNextElt) = begin
                  local numElts::ModelicaInteger
                  local vect::Array{Option{UnitAbsyn.Unit}}
                  local unit::UnitAbsyn.Unit
                  local store::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                  local nextElt::ModelicaInteger
                @matchcontinue (istore, iht, i, inextElt) begin
                  (store && UnitAbsyn.STORE(_, numElts), ht, _, nextElt)  => begin
                      @match true = i > numElts
                    (store, ht, nextElt)
                  end

                  (UnitAbsyn.STORE(vect, numElts), ht, _, nextElt)  => begin
                      @match SOME(unit) = vect[i]
                      (unit, ht, nextElt) = createTypeParameterLocations3(unit, ht, nextElt)
                      vect = arrayUpdate(vect, i, SOME(unit))
                      (store, ht, nextElt) = createTypeParameterLocations2(UnitAbsyn.STORE(vect, numElts), ht, i + 1, nextElt)
                    (store, ht, nextElt)
                  end

                  (UnitAbsyn.STORE(vect, numElts), ht, _, nextElt)  => begin
                      (store, ht, nextElt) = createTypeParameterLocations2(UnitAbsyn.STORE(vect, numElts), ht, i + 1, nextElt)
                    (store, ht, nextElt)
                  end
                end
              end
          (outStore, outHt, outNextElt)
        end

         #= help function to createTypeParameterLocations2 =#
        function createTypeParameterLocations3(unit::UnitAbsyn.Unit, iht::HashTable.HashTableType, inextElt::ModelicaInteger) ::Tuple{UnitAbsyn.Unit, HashTable.HashTableType, ModelicaInteger}
              local outNextElt::ModelicaInteger
              local outHt::HashTable.HashTableType
              local outUnit::UnitAbsyn.Unit

              (outUnit, outHt, outNextElt) = begin
                  local params::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local units::List{MMath.Rational}
                  local ht::HashTable.HashTableType
                  local nextElt::ModelicaInteger
                   #=  Only succeeds for units with type parameters
                   =#
                @match (unit, iht, inextElt) begin
                  (UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(params && _ <| _, units)), ht, nextElt)  => begin
                      (params, ht, nextElt) = createTypeParameterLocations4(params, ht, nextElt)
                    (UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(params, units)), ht, nextElt)
                  end
                end
              end
          (outUnit, outHt, outNextElt)
        end

         #= help function to createTypeParameterLocations3 =#
        function createTypeParameterLocations4(iparams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}, iht::HashTable.HashTableType, inextElt::ModelicaInteger) ::Tuple{List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}, HashTable.HashTableType, ModelicaInteger}
              local outNextElt::ModelicaInteger
              local outHt::HashTable.HashTableType
              local outParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}

              (outParams, outHt, outNextElt) = begin
                  local indx::ModelicaInteger
                  local name::String
                  local r::MMath.Rational
                  local param::Tuple{MMath.Rational, UnitAbsyn.TypeParameter}
                  local cref_::DAE.ComponentRef
                  local params::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local ht::HashTable.HashTableType
                  local nextElt::ModelicaInteger
                @matchcontinue (iparams, iht, inextElt) begin
                  ( nil(), ht, nextElt)  => begin
                    (nil, ht, nextElt)
                  end

                  ((r, UnitAbsyn.TYPEPARAMETER(name, 0)) <| params, ht, nextElt)  => begin
                      cref_ = ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil)
                      indx = BaseHashTable.get(cref_, ht)
                      (params, ht, nextElt) = createTypeParameterLocations4(params, ht, nextElt)
                    (_cons((r, UnitAbsyn.TYPEPARAMETER(name, indx)), params), ht, nextElt)
                  end

                  ((r, UnitAbsyn.TYPEPARAMETER(name, 0)) <| params, ht, nextElt)  => begin
                      cref_ = ComponentReference.makeCrefIdent(name, DAE.T_UNKNOWN_DEFAULT, nil)
                      ht = BaseHashTable.add((cref_, nextElt), ht)
                      (params, ht, nextElt) = createTypeParameterLocations4(params, ht, nextElt)
                    (_cons((r, UnitAbsyn.TYPEPARAMETER(name, nextElt)), params), ht, nextElt + 1)
                  end

                  (param <| params, ht, nextElt)  => begin
                      (params, ht, nextElt) = createTypeParameterLocations4(params, ht, nextElt)
                    (_cons(param, params), ht, nextElt)
                  end

                  _  => begin
                        print("createTypeParameterLocations4 failed\\n")
                      fail()
                  end
                end
              end
          (outParams, outHt, outNextElt)
        end

         #= builds the stores and creates a hashtable from variable names to store locations =#
        function buildStores(dae::DAE.DAElist) ::Tuple{UnitAbsyn.Store, HashTable.HashTableType}
              local ht::HashTable.HashTableType
              local store::UnitAbsyn.Store

              (store, ht) = buildStores2(dae, emptyStore(), HashTable.emptyHashTable()) #= Build stores from variables =#
              (store, ht) = buildStores3(dae, store, ht) #= build stores from constants and function calls in expressions =#
          (store, ht)
        end

         #= builds the unit terms from DAE elements (equations) =#
        function buildTerms(env::FCore.Graph, dae::DAE.DAElist, ht::HashTable.HashTableType, istore::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitTerms, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local terms::UnitAbsyn.UnitTerms

              (terms, outStore) = begin
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local crefExp1::DAE.Exp
                  local crefExp2::DAE.Exp
                  local ut1::UnitAbsyn.UnitTerm
                  local ut2::UnitAbsyn.UnitTerm
                  local terms1::List{UnitAbsyn.UnitTerm}
                  local terms2::List{UnitAbsyn.UnitTerm}
                  local cr1::DAE.ComponentRef
                  local cr2::DAE.ComponentRef
                  local elts::List{DAE.Element}
                  local store::UnitAbsyn.Store
                @matchcontinue (env, dae, ht, istore) begin
                  (_, DAE.DAE_LIST(elementLst =  nil()), _, store)  => begin
                    (nil, store)
                  end

                  (_, DAE.DAE_LIST(elementLst = DAE.EQUATION(e1, e2, _) <| elts), _, store)  => begin
                      (ut1, terms1, store) = buildTermExp(env, e1, false, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, e2, false, ht, store)
                      (terms, store) = buildTerms(env, DAE.DAE_LIST(elts), ht, store)
                      terms = listAppend(terms1, listAppend(terms2, terms))
                    (_cons(UnitAbsyn.EQN(ut1, ut2, DAE.BINARY(e1, DAE.SUB(DAE.T_REAL_DEFAULT), e2)), terms), store)
                  end

                  (_, DAE.DAE_LIST(elementLst = DAE.EQUEQUATION(cr1, cr2, _) <| elts), _, store)  => begin
                      crefExp1 = Expression.crefExp(cr1)
                      crefExp2 = Expression.crefExp(cr2)
                      (ut1, terms1, store) = buildTermExp(env, crefExp1, false, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, crefExp2, false, ht, store)
                      (terms, store) = buildTerms(env, DAE.DAE_LIST(elts), ht, store)
                      terms = listAppend(terms1, listAppend(terms2, terms))
                    (_cons(UnitAbsyn.EQN(ut1, ut2, DAE.BINARY(crefExp1, DAE.SUB(DAE.T_REAL_DEFAULT), crefExp2)), terms), store)
                  end

                  (_, DAE.DAE_LIST(elementLst = DAE.VAR(componentRef = cr1 && DAE.CREF_IDENT(_, _, _), binding = SOME(e1)) <| elts), _, store)  => begin
                      crefExp1 = Expression.crefExp(cr1)
                      (ut1, terms1, store) = buildTermExp(env, crefExp1, false, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, e1, false, ht, store)
                      (terms, store) = buildTerms(env, DAE.DAE_LIST(elts), ht, store)
                      terms = listAppend(terms1, listAppend(terms2, terms))
                    (_cons(UnitAbsyn.EQN(ut1, ut2, DAE.BINARY(crefExp1, DAE.SUB(DAE.T_REAL_DEFAULT), e1)), terms), store)
                  end

                  (_, DAE.DAE_LIST(elementLst = DAE.DEFINE(cr1, e1, _) <| elts), _, store)  => begin
                      crefExp1 = Expression.crefExp(cr1)
                      (ut1, terms1, store) = buildTermExp(env, crefExp1, false, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, e1, false, ht, store)
                      (terms, store) = buildTerms(env, DAE.DAE_LIST(elts), ht, store)
                      terms = listAppend(terms1, listAppend(terms2, terms))
                    (_cons(UnitAbsyn.EQN(ut1, ut2, DAE.BINARY(crefExp1, DAE.SUB(DAE.T_REAL_DEFAULT), e1)), terms), store)
                  end

                  (_, DAE.DAE_LIST(elementLst = _ <| elts), _, store)  => begin
                      (terms, store) = buildTerms(env, DAE.DAE_LIST(elts), ht, store)
                    (terms, store)
                  end
                end
              end
               #= /* Only consider variables with binding from this instance level, not furhter down */ =#
          (terms, outStore)
        end

         #= help function to buildTerms, handles expressions =#
        function buildTermExp(env::FCore.Graph, exp::DAE.Exp, idivOrMul::Bool #= is true if surrounding expression is division or multiplication. In that case
           the constant will be treated as dimensionless, otherwise it will be treated as unspecified
           =#, iht::HashTable.HashTableType, istore::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitTerm, List{UnitAbsyn.UnitTerm}, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local extraTerms::List{UnitAbsyn.UnitTerm} #= additional terms from e.g. function calls =#
              local ut::UnitAbsyn.UnitTerm

              (ut, extraTerms, outStore) = begin
                  local r::ModelicaReal
                  local op::DAE.Operator
                  local indx::ModelicaInteger
                  local i::ModelicaInteger
                  local ut1::UnitAbsyn.UnitTerm
                  local ut2::UnitAbsyn.UnitTerm
                  local s1::String
                  local cr::DAE.ComponentRef
                  local e::DAE.Exp
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local path::Absyn.Path
                  local mexpl::List{List{DAE.Exp}}
                  local terms1::List{UnitAbsyn.UnitTerm}
                  local terms2::List{UnitAbsyn.UnitTerm}
                  local terms::List{UnitAbsyn.UnitTerm}
                  local uts::List{UnitAbsyn.UnitTerm}
                  local expl::List{DAE.Exp}
                  local u::UnitAbsyn.Unit
                  local ht::HashTable.HashTableType
                  local store::UnitAbsyn.Store
                  local divOrMul::Bool
                   #= /*case(env,e as DAE.RCONST(r),ht,store) equation
                        s1 = realString(r);
                        indx = BaseHashTable.get(ComponentReference.makeCrefIdent(s1,DAE.T_UNKNOWN_DEFAULT,{}),ht);
                      then (UnitAbsyn.LOC(indx,e),{},store);*/ =#
                @matchcontinue (env, exp, idivOrMul, iht, istore) begin
                  (_, e && DAE.ICONST(i), divOrMul, ht, store)  => begin
                      s1 = "" + intString(tick()) + "_" + intString(i)
                      u = if divOrMul
                            str2unit("1", NONE())
                          else
                            UnitAbsyn.UNSPECIFIED()
                          end
                      (store, indx) = add(u, store)
                      ht = BaseHashTable.add((ComponentReference.makeCrefIdent(s1, DAE.T_UNKNOWN_DEFAULT, nil), indx), ht)
                    (UnitAbsyn.LOC(indx, e), nil, store)
                  end

                  (_, e && DAE.RCONST(r), divOrMul, ht, store)  => begin
                      s1 = "" + intString(tick()) + "_" + realString(r)
                      u = if divOrMul
                            str2unit("1", NONE())
                          else
                            UnitAbsyn.UNSPECIFIED()
                          end
                      (store, indx) = add(u, store)
                      ht = BaseHashTable.add((ComponentReference.makeCrefIdent(s1, DAE.T_UNKNOWN_DEFAULT, nil), indx), ht)
                    (UnitAbsyn.LOC(indx, e), nil, store)
                  end

                  (_, DAE.CAST(_, e1), divOrMul, ht, store)  => begin
                      (ut, terms, store) = buildTermExp(env, e1, divOrMul, ht, store)
                    (ut, terms, store)
                  end

                  (_, e && DAE.CREF(cr, _), _, ht, store)  => begin
                      indx = BaseHashTable.get(cr, ht)
                    (UnitAbsyn.LOC(indx, e), nil, store)
                  end

                  (_, e && DAE.BINARY(e1, DAE.POW(_), e2 && DAE.ICONST(i)), divOrMul, ht, store)  => begin
                      (ut1, terms1, store) = buildTermExp(env, e1, divOrMul, ht, store)
                      (_, terms2, store) = buildTermExp(env, e2, divOrMul, ht, store)
                      terms = listAppend(terms1, terms2)
                      ut = UnitAbsyn.POW(ut1, MMath.RATIONAL(i, 1), e)
                    (ut, terms, store)
                  end

                  (_, e && DAE.BINARY(e1, DAE.POW(_), e2 && DAE.RCONST(r)), divOrMul, ht, store)  => begin
                      (ut1, terms1, store) = buildTermExp(env, e1, divOrMul, ht, store)
                      (_, terms2, store) = buildTermExp(env, e2, divOrMul, ht, store)
                      terms = listAppend(terms1, terms2)
                      i = realInt(r)
                      @match true = intReal(i) - r == 0.0
                      ut = UnitAbsyn.POW(ut1, MMath.RATIONAL(i, 1), e)
                    (ut, terms, store)
                  end

                  (_, e && DAE.BINARY(e1, op, e2), divOrMul, ht, store)  => begin
                      divOrMul = Expression.operatorDivOrMul(op)
                      (ut1, terms1, store) = buildTermExp(env, e1, divOrMul, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, e2, divOrMul, ht, store)
                      terms = listAppend(terms1, terms2)
                      ut = buildTermOp(ut1, ut2, op, e)
                    (ut, terms, store)
                  end

                  (_, DAE.BINARY(e1, op, _), divOrMul, ht, store)  => begin
                      divOrMul = Expression.operatorDivOrMul(op)
                      (ut, terms, store) = buildTermExp(env, e1, divOrMul, ht, store)
                      @shouldFail (_, _, _) = buildTermExp(env, e1, divOrMul, ht, store)
                    (ut, terms, store)
                  end

                  (_, DAE.BINARY(e1, op, e2), divOrMul, ht, store)  => begin
                      divOrMul = Expression.operatorDivOrMul(op)
                      @shouldFail (_, _, _) = buildTermExp(env, e1, divOrMul, ht, store)
                      (ut, terms, store) = buildTermExp(env, e2, divOrMul, ht, store)
                    (ut, terms, store)
                  end

                  (_, DAE.UNARY(_, e1), divOrMul, ht, store)  => begin
                      (ut, terms, store) = buildTermExp(env, e1, divOrMul, ht, store)
                    (ut, terms, store)
                  end

                  (_, e && DAE.IFEXP(_, e1, e2), divOrMul, ht, store)  => begin
                      divOrMul = false
                      (ut1, terms1, store) = buildTermExp(env, e1, divOrMul, ht, store)
                      (ut2, terms2, store) = buildTermExp(env, e2, divOrMul, ht, store)
                      terms = listAppend(terms1, terms2)
                    (UnitAbsyn.EQN(ut1, ut2, e), terms, store)
                  end

                  (_, e && DAE.CALL(path = path, expLst = expl), divOrMul, ht, store)  => begin
                      divOrMul = false
                      (ut, terms, store) = buildTermCall(env, path, e, expl, divOrMul, ht, store)
                    (ut, terms, store)
                  end

                  (_, e && DAE.ARRAY(_, _, expl), _, ht, store)  => begin
                      print("vector =" + ExpressionDump.printExpStr(e) + "\\n")
                      (uts, terms, store) = buildTermExpList(env, expl, ht, store)
                      @match _cons(ut, uts) = buildArrayElementTerms(uts, expl)
                      uts = listAppend(terms, uts)
                    (ut, uts, store)
                  end

                  (_, e && DAE.MATRIX(matrix = mexpl), _, ht, store)  => begin
                      print("Matrix =" + ExpressionDump.printExpStr(e) + "\\n")
                      expl = ListUtil.flatten(mexpl)
                      (uts, terms, store) = buildTermExpList(env, expl, ht, store)
                      @match _cons(ut, uts) = buildArrayElementTerms(uts, expl)
                      uts = listAppend(terms, uts)
                    (ut, uts, store)
                  end

                  (_, e && DAE.CALL(__), _, _, _)  => begin
                      print("buildTermDAE.CALL failed exp: " + ExpressionDump.printExpStr(e) + "\\n")
                    fail()
                  end
                end
              end
               #= /* for each constant, add new unspecified unit*/ =#
               #= /* special case for pow */ =#
               #= /* failed to build term for e2, use e1*/ =#
               #= /* failed to build term for e1, use e2*/ =#
               #= /* function call */ =#
               #= /* Array, all elements must be of same dimension, since an array with different units in different positions
                  can not be declared in Modelica, since modifiers on arrays must affect the whole array */ =#
          (ut, extraTerms #= additional terms from e.g. function calls =#, outStore)
        end

         #= help function to buildTermExpression. For each two terms from an array expression, it create
        and EQN to make the constraint that they must have the same unit =#
        function buildArrayElementTerms(iuts::List{<:UnitAbsyn.UnitTerm}, iexpl::List{<:DAE.Exp}) ::List{UnitAbsyn.UnitTerm}
              local outUts::List{UnitAbsyn.UnitTerm} = nil

              local rest_ut::List{UnitAbsyn.UnitTerm} = iuts
              local ut1::UnitAbsyn.UnitTerm
              local ut2::UnitAbsyn.UnitTerm
              local ty::DAE.Type
              local rest_expl::List{DAE.Exp} = iexpl
              local e1::DAE.Exp
              local e2::DAE.Exp

              while ! listEmpty(rest_ut)
                @match _cons(ut1, _cons(ut2, rest_ut)) = rest_ut
                @match _cons(e1, _cons(e2, rest_expl)) = rest_expl
                ty = Expression.typeof(e1)
                outUts = _cons(UnitAbsyn.EQN(ut1, ut2, DAE.ARRAY(ty, true, list(e1, e2))), outUts)
              end
              outUts = listReverse(outUts)
          outUts
        end

         #= builds a term and additional terms from a function call =#
        function buildTermCall(env::FCore.Graph, path::Absyn.Path, funcCallExp::DAE.Exp, expl::List{<:DAE.Exp}, divOrMul::Bool, ht::HashTable.HashTableType, istore::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitTerm, List{UnitAbsyn.UnitTerm}, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local extraTerms::List{UnitAbsyn.UnitTerm} #= additional terms from e.g. function calls =#
              local ut::UnitAbsyn.UnitTerm

              (ut, extraTerms, outStore) = begin
                  local formalParamIndxs::List{ModelicaInteger}
                  local funcInstId::ModelicaInteger
                  local actTermLst::List{UnitAbsyn.UnitTerm}
                  local terms::List{UnitAbsyn.UnitTerm}
                  local terms2::List{UnitAbsyn.UnitTerm}
                  local extraTerms2::List{UnitAbsyn.UnitTerm}
                  local functp::DAE.Type
                  local store::UnitAbsyn.Store
                @match (env, path, funcCallExp, expl, divOrMul, ht, istore) begin
                  (_, _, _, _, _, _, store)  => begin
                      (_, functp, _) = Lookup.lookupType(FCore.noCache(), env, path, NONE())
                      funcInstId = tick()
                      (store, formalParamIndxs) = buildFuncTypeStores(functp, funcInstId, store)
                      (actTermLst, extraTerms, store) = buildTermExpList(env, expl, ht, store)
                      terms = buildFormal2ActualParamTerms(formalParamIndxs, actTermLst)
                      @match (list(ut), extraTerms2, store) = buildResultTerms(functp, funcInstId, funcCallExp, store)
                      extraTerms = ListUtil.flatten(list(extraTerms, extraTerms2, terms))
                    (ut, extraTerms, store)
                  end
                end
              end
          (ut, extraTerms #= additional terms from e.g. function calls =#, outStore)
        end

         #= build stores and terms for assigning formal output arguments to
        new locations =#
        function buildResultTerms(ifunctp::DAE.Type, funcInstId::ModelicaInteger, funcCallExp::DAE.Exp, istore::UnitAbsyn.Store) ::Tuple{List{UnitAbsyn.UnitTerm}, List{UnitAbsyn.UnitTerm}, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local extraTerms::List{UnitAbsyn.UnitTerm}
              local terms::List{UnitAbsyn.UnitTerm}

              (terms, extraTerms, outStore) = begin
                  local unitStr::String
                  local unit::UnitAbsyn.Unit
                  local indx::ModelicaInteger
                  local indx2::ModelicaInteger
                  local unspec::Bool
                  local typeLst::List{DAE.Type}
                  local functp::DAE.Type
                  local store::UnitAbsyn.Store
                   #=  Real
                   =#
                @matchcontinue (ifunctp, funcInstId, funcCallExp, istore) begin
                  (DAE.T_FUNCTION(_, functp, _, _), _, _, store)  => begin
                      unitStr = getUnitStr(functp)
                      unspec = 0 == stringCompare(unitStr, "")
                      unit = str2unit(unitStr, SOME(funcInstId))
                      unit = if unspec
                            UnitAbsyn.UNSPECIFIED()
                          else
                            unit
                          end
                      (store, indx) = add(unit, store)
                      (store, indx2) = add(UnitAbsyn.UNSPECIFIED(), store)
                    (list(UnitAbsyn.LOC(indx2, funcCallExp)), list(UnitAbsyn.EQN(UnitAbsyn.LOC(indx2, funcCallExp), UnitAbsyn.LOC(indx, funcCallExp), funcCallExp)), store)
                  end

                  (DAE.T_FUNCTION(funcResultType = DAE.T_TUPLE(types = typeLst)), _, _, store)  => begin
                      (terms, extraTerms, store) = buildTupleResultTerms(typeLst, funcInstId, funcCallExp, store)
                    (terms, extraTerms, store)
                  end

                  _  => begin
                        print("buildResultTerms failed\\n")
                      fail()
                  end
                end
              end
               #= print(\"Got unit='\"+unitStr+\"'\\n\");
               =#
               #=  Tuple
               =#
          (terms, extraTerms, outStore)
        end

         #= help function to buildResultTerms =#
        function buildTupleResultTerms(ifunctps::List{<:DAE.Type}, funcInstId::ModelicaInteger, funcCallExp::DAE.Exp, istore::UnitAbsyn.Store) ::Tuple{List{UnitAbsyn.UnitTerm}, List{UnitAbsyn.UnitTerm}, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local extraTerms::List{UnitAbsyn.UnitTerm}
              local terms::List{UnitAbsyn.UnitTerm}

              (terms, extraTerms, outStore) = begin
                  local terms1::List{UnitAbsyn.UnitTerm}
                  local terms2::List{UnitAbsyn.UnitTerm}
                  local extraTerms1::List{UnitAbsyn.UnitTerm}
                  local extraTerms2::List{UnitAbsyn.UnitTerm}
                  local tp::DAE.Type
                  local functps::List{DAE.Type}
                  local store::UnitAbsyn.Store
                @match (ifunctps, funcInstId, funcCallExp, istore) begin
                  ( nil(), _, _, store)  => begin
                    (nil, nil, store)
                  end

                  (tp <| functps, _, _, store)  => begin
                      (terms1, extraTerms1, store) = buildResultTerms(tp, funcInstId, funcCallExp, store)
                      (terms2, extraTerms2, store) = buildTupleResultTerms(functps, funcInstId, funcCallExp, store)
                      terms = listAppend(terms1, terms2)
                      extraTerms = listAppend(extraTerms1, extraTerms2)
                    (terms, extraTerms, store)
                  end
                end
              end
          (terms, extraTerms, outStore)
        end

         #= build terms from list of expressions =#
        function buildTermExpList(env::FCore.Graph, iexpl::List{<:DAE.Exp}, ht::HashTable.HashTableType, istore::UnitAbsyn.Store) ::Tuple{List{UnitAbsyn.UnitTerm}, List{UnitAbsyn.UnitTerm}, UnitAbsyn.Store}
              local outStore::UnitAbsyn.Store
              local extraTerms::List{UnitAbsyn.UnitTerm}
              local terms::List{UnitAbsyn.UnitTerm}

              (terms, extraTerms, outStore) = begin
                  local e::DAE.Exp
                  local eterms1::List{UnitAbsyn.UnitTerm}
                  local eterms2::List{UnitAbsyn.UnitTerm}
                  local ut::UnitAbsyn.UnitTerm
                  local expl::List{DAE.Exp}
                  local store::UnitAbsyn.Store
                @matchcontinue (env, iexpl, ht, istore) begin
                  (_,  nil(), _, store)  => begin
                    (nil, nil, store)
                  end

                  (_, e <| expl, _, store)  => begin
                      (ut, eterms1, store) = buildTermExp(env, e, false, ht, store)
                      (terms, eterms2, store) = buildTermExpList(env, expl, ht, store)
                      extraTerms = listAppend(eterms1, eterms2)
                    (_cons(ut, terms), extraTerms, store)
                  end

                  (_, e <| _, _, _)  => begin
                      print("buildTermExpList failed for exp" + ExpressionDump.printExpStr(e) + "\\n")
                    fail()
                  end
                end
              end
          (terms, extraTerms, outStore)
        end

         #= help function to buildTermCall =#
        function buildFuncTypeStores(funcType::DAE.Type, funcInstId::ModelicaInteger #= unique id for each function call to make unique type parameter names =#, istore::UnitAbsyn.Store) ::Tuple{UnitAbsyn.Store, List{ModelicaInteger}}
              local indxs::List{ModelicaInteger}
              local outStore::UnitAbsyn.Store

              (outStore, indxs) = begin
                  local args::List{DAE.FuncArg}
                  local tp::DAE.Type
                  local store::UnitAbsyn.Store
                @matchcontinue (funcType, funcInstId, istore) begin
                  (DAE.T_FUNCTION(funcArg = args), _, store)  => begin
                      (store, indxs) = buildFuncTypeStores2(args, funcInstId, store)
                    (store, indxs)
                  end

                  (tp, _, _)  => begin
                      print("buildFuncTypeStores failed, tp" + Types.unparseType(tp) + "\\n")
                    fail()
                  end
                end
              end
          (outStore, indxs)
        end

         #= help function to buildFuncTypeStores =#
        function buildFuncTypeStores2(ifargs::List{<:DAE.FuncArg}, funcInstId::ModelicaInteger, istore::UnitAbsyn.Store) ::Tuple{UnitAbsyn.Store, List{ModelicaInteger}}
              local indxs::List{ModelicaInteger}
              local outStore::UnitAbsyn.Store

              (outStore, indxs) = begin
                  local unitStr::String
                  local indx::ModelicaInteger
                  local tp::DAE.Type
                  local unit::UnitAbsyn.Unit
                  local fargs::List{DAE.FuncArg}
                  local store::UnitAbsyn.Store
                @match (ifargs, funcInstId, istore) begin
                  ( nil(), _, store)  => begin
                    (store, nil)
                  end

                  (DAE.FUNCARG(ty = tp) <| fargs, _, store)  => begin
                      unitStr = getUnitStr(tp)
                      unit = str2unit(unitStr, SOME(funcInstId))
                      unit = if 0 == stringCompare(unitStr, "")
                            UnitAbsyn.UNSPECIFIED()
                          else
                            unit
                          end
                      (store, indx) = add(unit, store)
                      (store, indxs) = buildFuncTypeStores2(fargs, funcInstId, store)
                    (store, _cons(indx, indxs))
                  end
                end
              end
          (outStore, indxs)
        end

         #= help function to e.g. buildFuncTypeStores2, retrieve a unit string
        from a Type (must be T_REAL) =#
        function getUnitStr(itp::DAE.Type) ::String
              local str::String

              str = begin
                  local varLst::List{DAE.Var}
                  local tp::DAE.Type
                @matchcontinue itp begin
                  DAE.T_REAL(varLst = varLst)  => begin
                      for v in varLst
                        _ = begin
                          @match v begin
                            DAE.TYPES_VAR(name = "unit", binding = DAE.EQBOUND(exp = DAE.SCONST(str)))  => begin
                                return
                              ()
                            end

                            _  => begin
                                ()
                            end
                          end
                        end
                      end
                    ""
                  end

                  DAE.T_INTEGER(__)  => begin
                    ""
                  end

                  DAE.T_ARRAY(ty = tp)  => begin
                    getUnitStr(tp)
                  end

                  tp  => begin
                      print("getUnitStr for type " + Types.unparseType(tp) + " failed\\n")
                    fail()
                  end
                end
              end
          str
        end

         #=  help function to buildTermCall =#
        function buildFormal2ActualParamTerms(iformalParamIndxs::List{<:ModelicaInteger}, iactualParamIndxs::List{<:UnitAbsyn.UnitTerm}) ::UnitAbsyn.UnitTerms
              local terms::UnitAbsyn.UnitTerms

              terms = begin
                  local loc1::ModelicaInteger
                  local ut::UnitAbsyn.UnitTerm
                  local e::DAE.Exp
                  local formalParamIndxs::List{ModelicaInteger}
                  local actualParamIndxs::List{UnitAbsyn.UnitTerm}
                @matchcontinue (iformalParamIndxs, iactualParamIndxs) begin
                  ( nil(),  nil())  => begin
                    nil
                  end

                  (loc1 <| formalParamIndxs, ut <| actualParamIndxs)  => begin
                      terms = buildFormal2ActualParamTerms(formalParamIndxs, actualParamIndxs)
                      e = origExpInTerm(ut)
                    _cons(UnitAbsyn.EQN(UnitAbsyn.LOC(loc1, e), ut, e), terms)
                  end

                  _  => begin
                        print("buildFormal2ActualParamTerms failed\\n")
                      fail()
                  end
                end
              end
          terms
        end

         #= Returns the origExp of a term =#
        function origExpInTerm(ut::UnitAbsyn.UnitTerm) ::DAE.Exp
              local origExp::DAE.Exp

              origExp = begin
                  local e::DAE.Exp
                @match ut begin
                  UnitAbsyn.ADD(_, _, e)  => begin
                    e
                  end

                  UnitAbsyn.SUB(_, _, e)  => begin
                    e
                  end

                  UnitAbsyn.MUL(_, _, e)  => begin
                    e
                  end

                  UnitAbsyn.DIV(_, _, e)  => begin
                    e
                  end

                  UnitAbsyn.EQN(_, _, e)  => begin
                    e
                  end

                  UnitAbsyn.LOC(_, e)  => begin
                    e
                  end

                  UnitAbsyn.POW(_, _, e)  => begin
                    e
                  end
                end
              end
          origExp
        end

         #= Takes two UnitTerms and and DAE.Operator and creates a new UnitTerm  =#
        function buildTermOp(ut1::UnitAbsyn.UnitTerm, ut2::UnitAbsyn.UnitTerm, op::DAE.Operator, origExp::DAE.Exp) ::UnitAbsyn.UnitTerm
              local ut::UnitAbsyn.UnitTerm

              ut = begin
                @match (ut1, ut2, op, origExp) begin
                  (_, _, DAE.ADD(__), _)  => begin
                    UnitAbsyn.ADD(ut1, ut2, origExp)
                  end

                  (_, _, DAE.SUB(__), _)  => begin
                    UnitAbsyn.SUB(ut1, ut2, origExp)
                  end

                  (_, _, DAE.MUL(__), _)  => begin
                    UnitAbsyn.MUL(ut1, ut2, origExp)
                  end

                  (_, _, DAE.DIV(__), _)  => begin
                    UnitAbsyn.DIV(ut1, ut2, origExp)
                  end
                end
              end
          ut
        end

         #= help function =#
        function buildStores2(dae::DAE.DAElist, inStore::UnitAbsyn.Store, inHt::HashTable.HashTableType) ::Tuple{UnitAbsyn.Store, HashTable.HashTableType}
              local outHt::HashTable.HashTableType
              local outStore::UnitAbsyn.Store

              (outStore, outHt) = begin
                  local cr::DAE.ComponentRef
                  local attropt::Option{DAE.VariableAttributes}
                  local indx::ModelicaInteger
                  local unitStr::String
                  local units::List{MMath.Rational}
                  local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unit::UnitAbsyn.Unit
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local funcs::DAE.FunctionTree
                  local elts::List{DAE.Element}
                  local store::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                @matchcontinue (dae, inStore, inHt) begin
                  (DAE.DAE_LIST(elementLst =  nil()), _, _)  => begin
                    (inStore, inHt)
                  end

                  (DAE.DAE_LIST(elementLst = DAE.VAR(componentRef = cr, variableAttributesOption = attropt) <| elts), _, _)  => begin
                      @match DAE.SCONST(unitStr) = DAEUtil.getUnitAttr(attropt)
                      unit = str2unit(unitStr, NONE())
                      (store, indx) = add(unit, inStore)
                      ht = BaseHashTable.add((cr, indx), inHt)
                      (store, ht) = buildStores2(DAE.DAE_LIST(elts), store, ht)
                    (store, ht)
                  end

                  (DAE.DAE_LIST(elementLst = DAE.VAR(componentRef = cr) <| _), _, _)  => begin
                      (store, indx) = add(UnitAbsyn.UNSPECIFIED(), inStore)
                      ht = BaseHashTable.add((cr, indx), inHt)
                    (store, ht)
                  end

                  (DAE.DAE_LIST(elementLst = _ <| elts), _, _)  => begin
                      (store, ht) = buildStores2(DAE.DAE_LIST(elts), inStore, inHt)
                    (store, ht)
                  end
                end
              end
               #= /* Scale and offset not used yet*/ =#
               #= /* Failed to parse will give unspecified unit*/ =#
          (outStore, outHt)
        end

         #= help function =#
        function buildStores3(dae::DAE.DAElist, inStore::UnitAbsyn.Store, inHt::HashTable.HashTableType) ::Tuple{UnitAbsyn.Store, HashTable.HashTableType}
              local outHt::HashTable.HashTableType
              local outStore::UnitAbsyn.Store

              (outStore, outHt) = begin
                  local cr::DAE.ComponentRef
                  local attropt::Option{DAE.VariableAttributes}
                  local indx::ModelicaInteger
                  local unitStr::String
                  local units::List{MMath.Rational}
                  local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unit::UnitAbsyn.Unit
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local funcs::DAE.FunctionTree
                  local elts::List{DAE.Element}
                  local store::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                @matchcontinue (dae, inStore, inHt) begin
                  (DAE.DAE_LIST( nil()), store, ht)  => begin
                    (store, ht)
                  end

                  (DAE.DAE_LIST(DAE.EQUATION(e1, e2, _) <| elts), store, ht)  => begin
                      (store, ht) = buildStoreExp(e1, store, ht, NONE())
                      (store, ht) = buildStoreExp(e2, store, ht, NONE())
                      (store, ht) = buildStores3(DAE.DAE_LIST(elts), store, ht)
                    (store, ht)
                  end

                  (DAE.DAE_LIST(_ <| elts), store, ht)  => begin
                      (store, ht) = buildStores3(DAE.DAE_LIST(elts), store, ht)
                    (store, ht)
                  end
                end
              end
          (outStore, outHt)
        end

         #=  build stores from constants in expressions and from function calls =#
        function buildStoreExp(exp::DAE.Exp, inStore::UnitAbsyn.Store, inHt::HashTable.HashTableType, parentOp::Option{<:DAE.Operator}) ::Tuple{UnitAbsyn.Store, HashTable.HashTableType}
              local outHt::HashTable.HashTableType
              local outStore::UnitAbsyn.Store

              (outStore, outHt) = begin
                  local r::ModelicaReal
                  local s1::String
                  local i::ModelicaInteger
                  local indx::ModelicaInteger
                  local unit::UnitAbsyn.Unit
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                  local op::DAE.Operator
                  local cref_::DAE.ComponentRef
                  local store::UnitAbsyn.Store
                  local ht::HashTable.HashTableType
                   #= /* Constant on top level, e.g. x = 1 => unspecified type */ =#
                @matchcontinue (exp, inStore, inHt, parentOp) begin
                  (DAE.RCONST(r), store, ht, _)  => begin
                      unit = selectConstantUnit(parentOp)
                      (store, indx) = add(unit, store)
                      s1 = realString(r)
                      cref_ = ComponentReference.makeCrefIdent(s1, DAE.T_UNKNOWN_DEFAULT, nil)
                      ht = BaseHashTable.add((cref_, indx), ht)
                    (store, ht)
                  end

                  (DAE.CAST(_, DAE.ICONST(i)), store, ht, _)  => begin
                      unit = selectConstantUnit(parentOp)
                      (store, indx) = add(unit, store)
                      s1 = intString(i)
                      cref_ = ComponentReference.makeCrefIdent(s1, DAE.T_UNKNOWN_DEFAULT, nil)
                      ht = BaseHashTable.add((cref_, indx), ht)
                    (store, ht)
                  end

                  (DAE.BINARY(e1, op, e2), store, ht, _)  => begin
                      (store, ht) = buildStoreExp(e1, store, ht, SOME(op))
                      (store, ht) = buildStoreExp(e2, store, ht, SOME(op))
                    (store, ht)
                  end

                  (DAE.UNARY(_, e1), store, ht, _)  => begin
                      (store, ht) = buildStoreExp(e1, store, ht, parentOp)
                    (store, ht)
                  end

                  (DAE.IFEXP(_, e1, e2), store, ht, _)  => begin
                      (store, ht) = buildStoreExp(e1, store, ht, parentOp)
                      (store, ht) = buildStoreExp(e2, store, ht, parentOp)
                    (store, ht)
                  end

                  (_, store, ht, _)  => begin
                    (store, ht)
                  end
                end
              end
          (outStore, outHt)
        end

         #= Multiplying two units corresponds to adding the units and joining the typeParameter list =#
        function unitMultiply(u1::UnitAbsyn.Unit, u2::UnitAbsyn.Unit) ::UnitAbsyn.Unit
              local u::UnitAbsyn.Unit

              u = begin
                  local tparams1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local units::List{MMath.Rational}
                  local units1::List{MMath.Rational}
                  local units2::List{MMath.Rational}
                @match (u1, u2) begin
                  (UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(tparams1, units1)), UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(tparams2, units2)))  => begin
                      tparams = listAppend(tparams1, tparams2)
                      units = ListUtil.threadMap(units1, units2, MMath.addRational)
                    UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(tparams, units))
                  end
                end
              end
          u
        end

         #= returns UNSPECIFIED or dimensionless depending on
        parent expression as type of a constant expression =#
        function selectConstantUnit(op::Option{<:DAE.Operator}) ::UnitAbsyn.Unit
              local unit::UnitAbsyn.Unit

              unit = begin
                @match op begin
                  NONE()  => begin
                    UnitAbsyn.UNSPECIFIED()
                  end

                  SOME(DAE.ADD(_))  => begin
                    UnitAbsyn.UNSPECIFIED()
                  end

                  SOME(DAE.SUB(_))  => begin
                    UnitAbsyn.UNSPECIFIED()
                  end

                  SOME(_)  => begin
                    str2unit("1", NONE())
                  end
                end
              end
          unit
        end

         #= Translate a unit to a string =#
        function unit2str(unit::UnitAbsyn.Unit) ::String
              local res::String

              res = begin
                  local nums::List{ModelicaInteger}
                  local denoms::List{ModelicaInteger}
                  local tpnoms::List{ModelicaInteger}
                  local tpdenoms::List{ModelicaInteger}
                  local tpstrs::List{String}
                  local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local units::List{MMath.Rational}
                @match unit begin
                  UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(typeParams, units))  => begin
                      (nums, denoms) = splitRationals(units)
                      (tpnoms, tpdenoms, tpstrs) = splitTypeParams(typeParams)
                      res = UnitParserExt.unit2str(nums, denoms, tpnoms, tpdenoms, tpstrs, 1.0, 0.0)
                    res
                  end

                  UnitAbsyn.UNSPECIFIED(__)  => begin
                    "unspecified"
                  end
                end
              end
               #= /*scaleFactor*/ =#
               #= /*offset*/ =#
          res
        end

         #= Translate a unit string to a unit =#
        function str2unit(res::String, funcInstIdOpt::Option{<:ModelicaInteger}) ::UnitAbsyn.Unit
              local unit::UnitAbsyn.Unit

              local nums::List{ModelicaInteger}
              local denoms::List{ModelicaInteger}
              local tpnoms::List{ModelicaInteger}
              local tpdenoms::List{ModelicaInteger}
              local tpstrs::List{String}
              local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
              local units::List{MMath.Rational}

              (unit, _, _) = str2unitWithScaleFactor(res, funcInstIdOpt)
          unit
        end

         #= Translate a unit string to a unit =#
        function str2unitWithScaleFactor(res::String, funcInstIdOpt::Option{<:ModelicaInteger}) ::Tuple{UnitAbsyn.Unit, ModelicaReal, ModelicaReal}
              local offset::ModelicaReal
              local scaleFactor::ModelicaReal
              local unit::UnitAbsyn.Unit

              local nums::List{ModelicaInteger}
              local denoms::List{ModelicaInteger}
              local tpnoms::List{ModelicaInteger}
              local tpdenoms::List{ModelicaInteger}
              local tpstrs::List{String}
              local typeParams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
              local units::List{MMath.Rational}

              (nums, denoms, tpnoms, tpdenoms, tpstrs, scaleFactor, offset) = UnitParserExt.str2unit(res)
              units = joinRationals(nums, denoms)
              typeParams = joinTypeParams(tpnoms, tpdenoms, tpstrs, funcInstIdOpt)
              unit = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(typeParams, units))
          (unit, scaleFactor, offset)
        end

        function getDerivedUnitsHelper(baseUnit::UnitAbsyn.Unit, baseUnitStr::String, inUnits::List{<:String}) ::List{String}
              local outUnits::List{String} = nil

              local unit::UnitAbsyn.Unit
              local b::Bool

              for unitStr in inUnits
                if boolNot(stringEq(baseUnitStr, unitStr))
                  unit = str2unit(unitStr, NONE())
                  b = valueEq(baseUnit, unit)
                  if b
                    outUnits = _cons(unitStr, outUnits)
                  end
                end
              end
               #=  skip same units
               =#
          outUnits
        end

        function getDerivedUnits(baseUnit::UnitAbsyn.Unit, baseUnitStr::String) ::List{String}
              local derivedUnits::List{String}

              local unitSymbols::List{String}

              unitSymbols = UnitParserExt.allUnitSymbols()
              derivedUnits = getDerivedUnitsHelper(baseUnit, baseUnitStr, unitSymbols)
          derivedUnits
        end

         #= /* Tests  */ =#
         #= /* Test1:

        model Test1 \"CONSISTENT: All units defined. No inference\"
          Position x;
          Velocity v;
          Acceleration a;
        equation
          der(x) = v;
          der(v) = a;
        end Test1;
        */ =#

        function buildTest1() ::Tuple{UnitAbsyn.UnitTerms, UnitAbsyn.Store}
              local sigma::UnitAbsyn.Store
              local ut::UnitAbsyn.UnitTerms

              local r0::MMath.Rational
              local r1::MMath.Rational
              local nr1::MMath.Rational
              local nr2::MMath.Rational
              local unitderx::UnitAbsyn.Unit
              local unitderv::UnitAbsyn.Unit
              local unitx::UnitAbsyn.Unit
              local unitv::UnitAbsyn.Unit
              local unita::UnitAbsyn.Unit

              r0 = MMath.RATIONAL(0, 0)
              r1 = MMath.RATIONAL(1, 0)
              nr1 = MMath.RATIONAL(-1, 0)
              nr2 = MMath.RATIONAL(-2, 0)
              ut = list(UnitAbsyn.EQN(UnitAbsyn.LOC(1, DAE.SCONST("1")), UnitAbsyn.LOC(4, DAE.SCONST("4")), DAE.SCONST("1==4")), UnitAbsyn.EQN(UnitAbsyn.LOC(2, DAE.SCONST("2")), UnitAbsyn.LOC(5, DAE.SCONST("5")), DAE.SCONST("2==5")))
              unitderx = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(nil, list(r1, nr1, r0, r0, r0, r0, r0)))
               #= /* der(\"m\") -> m/s*/ =#
              unitderv = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(nil, list(r1, nr2, r0, r0, r0, r0, r0)))
               #= /* der(\"m/s\") -> m/s2 */ =#
              unitx = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(nil, list(r1, r0, r0, r0, r0, r0, r0)))
               #= /* x -> m */ =#
              unitv = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(nil, list(r1, nr1, r0, r0, r0, r0, r0)))
               #= /* v -> m/s */ =#
              unita = UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(nil, list(r1, nr2, r0, r0, r0, r0, r0)))
              sigma = emptyStore()
              (sigma, _) = add(unitderx, sigma)
               #= /*1*/ =#
              (sigma, _) = add(unitderv, sigma)
               #= /*2*/ =#
              (sigma, _) = add(unitx, sigma)
               #= /*3*/ =#
              (sigma, _) = add(unitv, sigma)
               #= /*4*/ =#
              (sigma, _) = add(unita, sigma)
               #= /*5*/ =#
              printStore(sigma)
          (ut, sigma)
        end

         #= /* Test2:
        model Test2 \"CONSISTENT: Subtraction operator. All units defined. No inference\"
        Position x,y,z;
        equation
        z = x-y;
        end Test2;
        */ =#
         #= /*public function buildTest2

          output UnitAbsyn.UnitTerms ut;
          output UnitAbsyn.Locations sigma;
        protected
          MMath.Rational r0,r1;
          algorithm
            r0 := MMath.RATIONAL(0,0);
            r1 := MMath.RATIONAL(1,0);
            ut := {
            UnitAbsyn.EQN(UnitAbsyn.LOC(\"z\"),UnitAbsyn.SUB(UnitAbsyn.LOC(\"x\"),UnitAbsyn.LOC(\"y\")))
            };
            sigma := {
            UnitAbsyn.LOCATION(\"x\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  x -> m
            UnitAbsyn.LOCATION(\"y\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  y -> m
            UnitAbsyn.LOCATION(\"z\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0})))  z -> m
            };
         end buildTest2;
         */ =#
         #= /* Test3
         model Test3 \"OVERDETERMINED: All units defined. No inference\"
         Position x,y;
         Velocity z;
        equation
         z = x-y;
        end Test3;
         */ =#
         #= /*public function buildTest3
          output UnitAbsyn.UnitTerms ut;
          output UnitAbsyn.Locations sigma;
        protected
          MMath.Rational r0,r1,nr1;
          algorithm
            r0 := MMath.RATIONAL(0,0);
            r1 := MMath.RATIONAL(1,0);
            nr1 := MMath.RATIONAL(-1,0);
            ut := {
            UnitAbsyn.EQN(UnitAbsyn.LOC(\"z\"),UnitAbsyn.SUB(UnitAbsyn.LOC(\"x\"),UnitAbsyn.LOC(\"y\")))
            };
            sigma := {
            UnitAbsyn.LOCATION(\"x\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  x -> m
            UnitAbsyn.LOCATION(\"y\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  y -> m
            UnitAbsyn.LOCATION(\"z\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,nr1,r0,r0,r0,r0,r0})))  z -> m/s
            };
         end buildTest3;
         */ =#
         #= /*
         Test5

         model Test5 \"CONSTISTENT: Multiplication operator. Not all units defined. inference\"
          Position x,y;
          Real z;
         equation
         z = x*y;
        end test5;
        */ =#
         #= /*
         public function buildTest5
          output UnitAbsyn.UnitTerms ut;
          output UnitAbsyn.Locations sigma;
        protected
          MMath.Rational r0,r1,nr1;
          algorithm
            r0 := MMath.RATIONAL(0,0);
            r1 := MMath.RATIONAL(1,0);
            nr1 := MMath.RATIONAL(-1,0);
            ut := {
            UnitAbsyn.EQN(UnitAbsyn.LOC(\"z\"),UnitAbsyn.MUL(UnitAbsyn.LOC(\"x\"),UnitAbsyn.LOC(\"y\")))
            };
            sigma := {
            UnitAbsyn.LOCATION(\"x\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  x -> m
            UnitAbsyn.LOCATION(\"y\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  y -> m
            UnitAbsyn.LOCATION(\"z\",UnitAbsyn.UNSPECIFIED())                                              z -> unspecified
            };
         end buildTest5;
         */ =#
         #= /* Test 8


        function Foo8
          input Real x;
          output Real y;
        algorithm
          y := x+1;  1 has unkown unit
        end Foo8;

        model Test8 \"CONSISTENT. type inference in function call \"
          Position x,y;
          Velocity v1,v2;

        equation
          x = Foo8(y);
          v1 = Foo8(v2);
        end Test8;
         */ =#
         #= /*public function buildTest8
          output UnitAbsyn.UnitTerms ut;
          output UnitAbsyn.Locations sigma;
        protected
          MMath.Rational r0,r1,nr1;
          algorithm
            r0 := MMath.RATIONAL(0,0);
            r1 := MMath.RATIONAL(1,0);
            nr1 := MMath.RATIONAL(-1,0);
            ut := {
            UnitAbsyn.EQN(UnitAbsyn.LOC(\"x\"),UnitAbsyn.LOC(\"Foo8(x)\")),
            UnitAbsyn.EQN(UnitAbsyn.LOC(\"v1\"),UnitAbsyn.LOC(\"Foo8(v2)\"))
            };
            sigma := {
            UnitAbsyn.LOCATION(\"Foo8(y)\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0}))),  Foo8(x) -> m
            UnitAbsyn.LOCATION(\"Foo8(v2)\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,nr1,r0,r0,r0,r0,r0}))),  Foo8(v2) -> m/s
            UnitAbsyn.LOCATION(\"v1\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,nr1,r0,r0,r0,r0,r0}))),  Foo8(v2) -> m/s
            UnitAbsyn.LOCATION(\"x\",UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT({},{r1,r0,r0,r0,r0,r0,r0})))  Foo8(v2) -> m
            };
         end buildTest8;
         */ =#

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

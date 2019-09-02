  module UnitChecker 


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

        import MMath

        import UnitAbsynBuilder

        import Debug

        import Error

        import Flags

        import HashTable

         #= Check if a list of unit terms are consistent =#
        function check(tms::UnitAbsyn.UnitTerms, ist::UnitAbsyn.InstStore) ::UnitAbsyn.InstStore 
              local outSt::UnitAbsyn.InstStore

              outSt = begin
                  local st1::UnitAbsyn.Store
                  local st2::UnitAbsyn.Store
                  local rest1::UnitAbsyn.UnitTerms
                  local tm1::UnitAbsyn.UnitTerm
                  local res::Option{UnitAbsyn.UnitCheckResult}
                  local su1::UnitAbsyn.SpecUnit
                  local su2::UnitAbsyn.SpecUnit
                  local s1::String
                  local s2::String
                  local s3::String
                  local ht::HashTable.HashTable
                  local st::UnitAbsyn.InstStore
                @matchcontinue (tms, ist) begin
                  (_, st)  => begin
                      @match false = Flags.getConfigBool(Flags.UNIT_CHECKING)
                    st
                  end
                  
                  ( nil(), UnitAbsyn.INSTSTORE(st1, ht, _))  => begin
                    UnitAbsyn.INSTSTORE(st1, ht, SOME(UnitAbsyn.CONSISTENT()))
                  end
                  
                  (tm1 <| rest1, UnitAbsyn.INSTSTORE(st1, ht, _))  => begin
                      @match (UnitAbsyn.CONSISTENT(), _, st2) = checkTerm(tm1, st1)
                      st = check(rest1, UnitAbsyn.INSTSTORE(st2, ht, SOME(UnitAbsyn.CONSISTENT())))
                    st
                  end
                  
                  (tm1 <| _, UnitAbsyn.INSTSTORE(st1, ht, _))  => begin
                      @match (UnitAbsyn.INCONSISTENT(su1, su2), _, _) = checkTerm(tm1, st1)
                      s1 = UnitAbsynBuilder.printTermsStr(list(tm1))
                      s2 = UnitAbsynBuilder.unit2str(UnitAbsyn.SPECIFIED(su1))
                      s3 = UnitAbsynBuilder.unit2str(UnitAbsyn.SPECIFIED(su2))
                      Error.addMessage(Error.INCONSISTENT_UNITS, list(s1, s2, s3))
                    UnitAbsyn.INSTSTORE(st1, ht, SOME(UnitAbsyn.INCONSISTENT(su1, su2)))
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::check() failed\\n")
                        print("check failed\\n")
                      fail()
                  end
                end
              end
               #=  No more terms?
               =#
               #=  Is consistent?
               =#
               #=  Is inconsistent?
               =#
               #=  failtrace
               =#
          outSt
        end

         #= returns true if the store is complete, else false =#
        function isComplete(st::UnitAbsyn.Store) ::Tuple{Bool, UnitAbsyn.Store} 
              local stout::UnitAbsyn.Store
              local complete::Bool

              (complete, stout) = begin
                  local vector::Array{Option{UnitAbsyn.Unit}}
                  local indx::ModelicaInteger
                  local lst::List{Option{UnitAbsyn.Unit}}
                  local comp::Bool
                  local st2::UnitAbsyn.Store
                @match st begin
                  UnitAbsyn.STORE(vector, indx)  => begin
                      lst = arrayList(vector)
                      (comp, st2) = completeCheck(lst, 1, UnitAbsyn.STORE(vector, indx))
                    (comp, st2)
                  end
                end
              end
          (complete, stout)
        end

         #= help function to isComplete =#
        function completeCheck(ilst::List{<:Option{<:UnitAbsyn.Unit}}, indx::ModelicaInteger, st::UnitAbsyn.Store) ::Tuple{Bool, UnitAbsyn.Store} 
              local stout::UnitAbsyn.Store
              local isComplete::Bool

              (isComplete, stout) = begin
                  local u1::UnitAbsyn.Unit
                  local u2::UnitAbsyn.Unit
                  local comp1::Bool
                  local st2::UnitAbsyn.Store
                  local st3::UnitAbsyn.Store
                  local st4::UnitAbsyn.Store
                  local lst::List{Option{UnitAbsyn.Unit}}
                @matchcontinue (ilst, indx, st) begin
                  ( nil(), _, st2)  => begin
                    (true, st2)
                  end
                  
                  (SOME(_) <| lst, _, st2)  => begin
                      (u2, st3) = normalize(indx, st2)
                      @match false = unitHasUnknown(u2)
                      (comp1, _) = completeCheck(lst, indx + 1, st3)
                    (comp1, st3)
                  end
                  
                  (SOME(_) <| _, _, st2)  => begin
                      (u2, _) = normalize(indx, st2)
                      @match true = unitHasUnknown(u2)
                    (false, st2)
                  end
                  
                  (NONE() <| _, _, st2)  => begin
                    (true, st2)
                  end
                end
              end
          (isComplete, stout)
        end

         #= check if one term is ok =#
        function checkTerm(tm::UnitAbsyn.UnitTerm, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitCheckResult, UnitAbsyn.SpecUnit, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local outUnit::UnitAbsyn.SpecUnit
              local result::UnitAbsyn.UnitCheckResult

              (result, outUnit, outSt) = begin
                  local st1::UnitAbsyn.Store
                  local st2::UnitAbsyn.Store
                  local st3::UnitAbsyn.Store
                  local st4::UnitAbsyn.Store
                  local res1::UnitAbsyn.UnitCheckResult
                  local res2::UnitAbsyn.UnitCheckResult
                  local res3::UnitAbsyn.UnitCheckResult
                  local res4::UnitAbsyn.UnitCheckResult
                  local ut1::UnitAbsyn.UnitTerm
                  local ut2::UnitAbsyn.UnitTerm
                  local su1::UnitAbsyn.SpecUnit
                  local su2::UnitAbsyn.SpecUnit
                  local su3::UnitAbsyn.SpecUnit
                  local expo1::MMath.Rational
                  local loc::ModelicaInteger
                @matchcontinue (tm, st) begin
                  (UnitAbsyn.ADD(ut1, ut2, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      (res2, su2, st3) = checkTerm(ut2, st2)
                      (res3, st4) = unify(su1, su2, st3)
                      res4 = chooseResult(res1, res2, res3)
                    (res4, su1, st4)
                  end
                  
                  (UnitAbsyn.SUB(ut1, ut2, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      (res2, su2, st3) = checkTerm(ut2, st2)
                      (res3, st4) = unify(su1, su2, st3)
                      res4 = chooseResult(res1, res2, res3)
                    (res4, su1, st4)
                  end
                  
                  (UnitAbsyn.MUL(ut1, ut2, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      (res2, su2, st3) = checkTerm(ut2, st2)
                      su3 = mulSpecUnit(su1, su2)
                      res4 = chooseResult(res1, res2, UnitAbsyn.CONSISTENT())
                    (res4, su3, st3)
                  end
                  
                  (UnitAbsyn.DIV(ut1, ut2, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      (res2, su2, st3) = checkTerm(ut2, st2)
                      su3 = divSpecUnit(su1, su2)
                      res4 = chooseResult(res1, res2, UnitAbsyn.CONSISTENT())
                    (res4, su3, st3)
                  end
                  
                  (UnitAbsyn.EQN(ut1, ut2, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      (res2, su2, st3) = checkTerm(ut2, st2)
                      (res3, st4) = unify(su1, su2, st3)
                      res4 = chooseResult(res1, res2, res3)
                    (res4, su1, st4)
                  end
                  
                  (UnitAbsyn.LOC(loc, _), st1)  => begin
                      @match UnitAbsyn.UNSPECIFIED() = UnitAbsynBuilder.find(loc, st1)
                    (UnitAbsyn.CONSISTENT(), UnitAbsyn.SPECUNIT(_cons((MMath.RATIONAL(1, 1), UnitAbsyn.TYPEPARAMETER("", loc)), nil), nil), st1)
                  end
                  
                  (UnitAbsyn.LOC(loc, _), st1)  => begin
                      @match UnitAbsyn.SPECIFIED(su1) = UnitAbsynBuilder.find(loc, st1)
                    (UnitAbsyn.CONSISTENT(), su1, st1)
                  end
                  
                  (UnitAbsyn.POW(ut1, expo1, _), st1)  => begin
                      (res1, su1, st2) = checkTerm(ut1, st1)
                      su2 = powSpecUnit(su1, expo1)
                    (res1, su2, st2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::checkTerm() failed\\n")
                      fail()
                  end
                end
              end
          (result, outUnit, outSt)
        end

         #= Returns the first result that is UnitAbsyn.INCONSISTENT. If not, CONISTENT will be returned =#
        function chooseResult(res1::UnitAbsyn.UnitCheckResult, res2::UnitAbsyn.UnitCheckResult, res3::UnitAbsyn.UnitCheckResult) ::UnitAbsyn.UnitCheckResult 
              local resout::UnitAbsyn.UnitCheckResult

              local incon::UnitAbsyn.UnitCheckResult

              resout = begin
                @match (res1, res2, res3) begin
                  (UnitAbsyn.CONSISTENT(__), UnitAbsyn.CONSISTENT(__), UnitAbsyn.CONSISTENT(__))  => begin
                    UnitAbsyn.CONSISTENT()
                  end
                  
                  (UnitAbsyn.CONSISTENT(__), UnitAbsyn.CONSISTENT(__), incon)  => begin
                    incon
                  end
                  
                  (UnitAbsyn.CONSISTENT(__), incon, _)  => begin
                    incon
                  end
                  
                  (incon, _, _)  => begin
                    incon
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::chooseResult() failed\\n")
                      fail()
                  end
                end
              end
          resout
        end

        function unify(insu1::UnitAbsyn.SpecUnit, insu2::UnitAbsyn.SpecUnit, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitCheckResult, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local outresult::UnitAbsyn.UnitCheckResult

              local su1::UnitAbsyn.SpecUnit
              local su2::UnitAbsyn.SpecUnit
              local st1::UnitAbsyn.Store
              local st2::UnitAbsyn.Store

              @match (UnitAbsyn.SPECIFIED(su1), st1) = normalizeOnUnit(UnitAbsyn.SPECIFIED(insu1), st)
              @match (UnitAbsyn.SPECIFIED(su2), st2) = normalizeOnUnit(UnitAbsyn.SPECIFIED(insu2), st1)
              (outresult, outSt) = unifyunits(su1, su2, st2)
          (outresult, outSt)
        end

         #= checks if twp spec units are equal (presupposed that they have no unknowns =#
        function isSpecUnitEq(insu1::UnitAbsyn.SpecUnit, insu2::UnitAbsyn.SpecUnit) ::Bool 
              local res::Bool

              res = begin
                  local r1::Bool
                  local i1a::ModelicaInteger
                  local i1b::ModelicaInteger
                  local i2a::ModelicaInteger
                  local i2b::ModelicaInteger
                  local rest1::List{MMath.Rational}
                  local rest2::List{MMath.Rational}
                @matchcontinue (insu1, insu2) begin
                  (UnitAbsyn.SPECUNIT(_,  nil()), UnitAbsyn.SPECUNIT(_,  nil()))  => begin
                    true
                  end
                  
                  (UnitAbsyn.SPECUNIT(_,  nil()), UnitAbsyn.SPECUNIT(_, MMath.RATIONAL(0, _) <| rest1))  => begin
                      r1 = isSpecUnitEq(UnitAbsyn.SPECUNIT(nil, nil), UnitAbsyn.SPECUNIT(nil, rest1))
                    r1
                  end
                  
                  (UnitAbsyn.SPECUNIT(_, MMath.RATIONAL(0, _) <| rest1), UnitAbsyn.SPECUNIT(_,  nil()))  => begin
                      r1 = isSpecUnitEq(UnitAbsyn.SPECUNIT(nil, rest1), UnitAbsyn.SPECUNIT(nil, nil))
                    r1
                  end
                  
                  (UnitAbsyn.SPECUNIT(_, MMath.RATIONAL(i1a, i1b) <| rest1), UnitAbsyn.SPECUNIT(_, MMath.RATIONAL(i2a, i2b) <| rest2))  => begin
                      @match true = intEq(i1a, i2a)
                      @match true = intEq(i1b, i2b)
                      r1 = isSpecUnitEq(UnitAbsyn.SPECUNIT(nil, rest1), UnitAbsyn.SPECUNIT(nil, rest2))
                    r1
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          res
        end

        function unifyunits(insu1::UnitAbsyn.SpecUnit, insu2::UnitAbsyn.SpecUnit, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.UnitCheckResult, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local outresult::UnitAbsyn.UnitCheckResult

              (outresult, outSt) = begin
                  local su1::UnitAbsyn.SpecUnit
                  local su2::UnitAbsyn.SpecUnit
                  local su3::UnitAbsyn.SpecUnit
                  local su4::UnitAbsyn.SpecUnit
                  local st1::UnitAbsyn.Store
                  local st2::UnitAbsyn.Store
                  local loc1::ModelicaInteger
                   #=  No unknown and the same on both sides
                   =#
                @matchcontinue (insu1, insu2, st) begin
                  (su1, su2, st1)  => begin
                      @match false = hasUnknown(su1)
                      @match false = hasUnknown(su2)
                      @match true = isSpecUnitEq(su1, su2)
                    (UnitAbsyn.CONSISTENT(), st1)
                  end
                  
                  (su1, su2, st1)  => begin
                      @match false = hasUnknown(su1)
                      @match false = hasUnknown(su2)
                    (UnitAbsyn.INCONSISTENT(su1, su2), st1)
                  end
                  
                  (su1, su2, st1)  => begin
                      su3 = divSpecUnit(su2, su1)
                      (loc1, su4) = getUnknown(su3)
                      st2 = UnitAbsynBuilder.update(UnitAbsyn.SPECIFIED(su4), loc1, st1)
                    (UnitAbsyn.CONSISTENT(), st2)
                  end
                  
                  (_, _, st1)  => begin
                    (UnitAbsyn.CONSISTENT(), st1)
                  end
                end
              end
               #=  No unknown, but different on the sides
               =#
               #=  Move the unknown to left side and substitute
               =#
               #=  Unknowns are cancelling each other out
               =#
          (outresult, outSt)
        end

         #= creates a new dimensionless unit =#
        function newDimlessSpecUnit() ::UnitAbsyn.SpecUnit 
              local su::UnitAbsyn.SpecUnit

              @match UnitAbsyn.SPECIFIED(su) = UnitAbsynBuilder.str2unit("1", NONE())
          su
        end

         #= gets the first unknown in a specified unit =#
        function getUnknown(suin::UnitAbsyn.SpecUnit) ::Tuple{ModelicaInteger, UnitAbsyn.SpecUnit} 
              local suout::UnitAbsyn.SpecUnit
              local loc::ModelicaInteger

              (loc, suout) = begin
                  local su1::UnitAbsyn.SpecUnit
                  local su2::UnitAbsyn.SpecUnit
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local loc1::ModelicaInteger
                  local name::String
                  local unitvec1::List{MMath.Rational}
                  local rest1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                @matchcontinue suin begin
                  UnitAbsyn.SPECUNIT((expo1, UnitAbsyn.TYPEPARAMETER(_, loc1)) <| rest1, unitvec1)  => begin
                      su1 = divSpecUnit(newDimlessSpecUnit(), UnitAbsyn.SPECUNIT(rest1, unitvec1))
                      expo2 = MMath.divRational(MMath.RATIONAL(1, 1), expo1)
                      su2 = powSpecUnit(su1, expo2)
                    (loc1, su2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::getUnknown() failed\\n")
                      fail()
                  end
                end
              end
          (loc, suout)
        end

        function hasUnknown(su::UnitAbsyn.SpecUnit) ::Bool 
              local res::Bool

              res = begin
                @matchcontinue su begin
                  UnitAbsyn.SPECUNIT( nil(), _)  => begin
                    false
                  end
                  
                  UnitAbsyn.SPECUNIT(_, _)  => begin
                    true
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::hasUnknown() failed\\n")
                      fail()
                  end
                end
              end
          res
        end

        function unitHasUnknown(u::UnitAbsyn.Unit) ::Bool 
              local res::Bool

              res = begin
                  local su::UnitAbsyn.SpecUnit
                  local unk::Bool
                @match u begin
                  UnitAbsyn.SPECIFIED(su)  => begin
                      unk = hasUnknown(su)
                    unk
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
          res
        end

         #= Multiplying two units corresponds to adding the units and joining the typeParameter list. =#
        function mulSpecUnit(u1::UnitAbsyn.SpecUnit, u2::UnitAbsyn.SpecUnit) ::UnitAbsyn.SpecUnit 
              local u::UnitAbsyn.SpecUnit

              u = begin
                  local tparams1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams3::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams4::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local units::List{MMath.Rational}
                  local units1::List{MMath.Rational}
                  local units2::List{MMath.Rational}
                @matchcontinue (u1, u2) begin
                  (UnitAbsyn.SPECUNIT(tparams1, units1), UnitAbsyn.SPECUNIT(tparams2, units2))  => begin
                      tparams3 = listAppend(tparams1, tparams2)
                      tparams4 = normalizeParamsExponents(tparams3)
                      units = mulUnitVec(units1, units2)
                    UnitAbsyn.SPECUNIT(tparams4, units)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::mulSpecUnit() failed\\n")
                      fail()
                  end
                end
              end
          u
        end

         #= multiplication of two unit vector =#
        function mulUnitVec(inunitvec1::List{<:MMath.Rational}, inunitvec2::List{<:MMath.Rational}) ::List{MMath.Rational} 
              local outunitvec::List{MMath.Rational}

              outunitvec = begin
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local expo3::MMath.Rational
                  local rest1::List{MMath.Rational}
                  local rest2::List{MMath.Rational}
                  local rest3::List{MMath.Rational}
                   #=  empty list
                   =#
                @matchcontinue (inunitvec1, inunitvec2) begin
                  ( nil(),  nil())  => begin
                    nil
                  end
                  
                  (expo1 <| rest1, expo2 <| rest2)  => begin
                      expo3 = MMath.addRational(expo1, expo2)
                      rest3 = mulUnitVec(rest1, rest2)
                    _cons(expo3, rest3)
                  end
                  
                  (expo1 <| rest1,  nil())  => begin
                      rest3 = mulUnitVec(rest1, nil)
                    _cons(expo1, rest3)
                  end
                  
                  ( nil(), expo1 <| rest1)  => begin
                      rest3 = mulUnitVec(nil, rest1)
                    _cons(expo1, rest3)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::powUnitVec() failed\\n")
                      fail()
                  end
                end
              end
          outunitvec
        end

         #= Divide two specified units =#
        function divSpecUnit(u1::UnitAbsyn.SpecUnit, u2::UnitAbsyn.SpecUnit) ::UnitAbsyn.SpecUnit 
              local u::UnitAbsyn.SpecUnit

              u = begin
                  local tparams1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams3::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams4::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local tparams5::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local units::List{MMath.Rational}
                  local units1::List{MMath.Rational}
                  local units2::List{MMath.Rational}
                @matchcontinue (u1, u2) begin
                  (UnitAbsyn.SPECUNIT(tparams1, units1), UnitAbsyn.SPECUNIT(tparams2, units2))  => begin
                      tparams3 = negParamList(tparams2, nil)
                      tparams4 = listAppend(tparams1, tparams3)
                      tparams5 = normalizeParamsExponents(tparams4)
                      units = divUnitVec(units1, units2)
                    UnitAbsyn.SPECUNIT(tparams5, units)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::divSpecUnit() failed\\n")
                      fail()
                  end
                end
              end
          u
        end

         #= division of two unit vectors =#
        function divUnitVec(inunitvec1::List{<:MMath.Rational}, inunitvec2::List{<:MMath.Rational}) ::List{MMath.Rational} 
              local outunitvec::List{MMath.Rational}

              outunitvec = begin
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local expo3::MMath.Rational
                  local rest1::List{MMath.Rational}
                  local rest2::List{MMath.Rational}
                  local rest3::List{MMath.Rational}
                @matchcontinue (inunitvec1, inunitvec2) begin
                  ( nil(),  nil())  => begin
                    nil
                  end
                  
                  (expo1 <| rest1, expo2 <| rest2)  => begin
                      expo3 = MMath.subRational(expo1, expo2)
                      rest3 = divUnitVec(rest1, rest2)
                    _cons(expo3, rest3)
                  end
                  
                  (expo1 <| rest1,  nil())  => begin
                      rest3 = divUnitVec(rest1, nil)
                    _cons(expo1, rest3)
                  end
                  
                  ( nil(), expo1 <| rest1)  => begin
                      expo2 = MMath.subRational(MMath.RATIONAL(0, 1), expo1)
                      rest3 = divUnitVec(nil, rest1)
                    _cons(expo2, rest3)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::powUnitVec() failed\\n")
                      fail()
                  end
                end
              end
          outunitvec
        end

         #= Power of a specified unit =#
        function powSpecUnit(suin::UnitAbsyn.SpecUnit, expo::MMath.Rational) ::UnitAbsyn.SpecUnit 
              local uout::UnitAbsyn.SpecUnit

              uout = begin
                  local params1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local params2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unitvec1::List{MMath.Rational}
                  local unitvec2::List{MMath.Rational}
                @matchcontinue (suin, expo) begin
                  (UnitAbsyn.SPECUNIT(params1, unitvec1), _)  => begin
                      params2 = powUnitParams(params1, expo)
                      unitvec2 = powUnitVec(unitvec1, expo)
                    UnitAbsyn.SPECUNIT(params2, unitvec2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::powSpecUnit() failed\\n")
                      fail()
                  end
                end
              end
          uout
        end

         #= exponent power of the unit type parameters =#
        function powUnitParams(inparams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}, expo::MMath.Rational) ::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}} 
              local outparams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}

              outparams = begin
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local expo3::MMath.Rational
                  local param::UnitAbsyn.TypeParameter
                  local rest1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local rest2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                @matchcontinue (inparams, expo) begin
                  ( nil(), _)  => begin
                    nil
                  end
                  
                  ((expo1, param) <| rest1, expo2)  => begin
                      expo3 = MMath.multRational(expo1, expo2)
                      rest2 = powUnitParams(rest1, expo2)
                    _cons((expo3, param), rest2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::powUnitParams() failed\\n")
                      fail()
                  end
                end
              end
          outparams
        end

         #= exponent power of the unit vector =#
        function powUnitVec(inunitvec::List{<:MMath.Rational}, expo::MMath.Rational) ::List{MMath.Rational} 
              local outunitvec::List{MMath.Rational}

              outunitvec = begin
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local expo3::MMath.Rational
                  local rest1::List{MMath.Rational}
                  local rest2::List{MMath.Rational}
                @matchcontinue (inunitvec, expo) begin
                  ( nil(), _)  => begin
                    nil
                  end
                  
                  (expo1 <| rest1, expo2)  => begin
                      expo3 = MMath.multRational(expo1, expo2)
                      rest2 = powUnitVec(rest1, expo2)
                    _cons(expo3, rest2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::powUnitVec() failed\\n")
                      fail()
                  end
                end
              end
          outunitvec
        end

        function negParamList(ine::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}, ac::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}) ::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}} 
              local oute::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}

              oute = begin
                  local qr::MMath.Rational
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local indx::ModelicaInteger
                  local name::String
                  local rest::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local pres::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local ac2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                @matchcontinue (ine, ac) begin
                  ( nil(), ac2)  => begin
                    ac2
                  end
                  
                  ((MMath.RATIONAL(i1, i2), UnitAbsyn.TYPEPARAMETER(name, indx)) <| rest, ac2)  => begin
                      qr = MMath.multRational(MMath.RATIONAL(-1, 1), MMath.RATIONAL(i1, i2))
                      pres = negParamList(rest, _cons((qr, UnitAbsyn.TYPEPARAMETER(name, indx)), ac2))
                    pres
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::negParamList() failed\\n")
                      fail()
                  end
                end
              end
          oute
        end

         #= normalizes the unit pointed by 'loc'. Returns the normalized unit. =#
        function normalize(loc::ModelicaInteger, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.Unit, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local unit::UnitAbsyn.Unit

              local u1::UnitAbsyn.Unit
              local u2::UnitAbsyn.Unit
              local st2::UnitAbsyn.Store

              u1 = UnitAbsynBuilder.find(loc, st)
              (u2, st2) = normalizeOnUnit(u1, st)
              outSt = UnitAbsynBuilder.update(u2, loc, st2)
              unit = u2
          (unit, outSt)
        end

         #= switch on each kind of unit =#
        function normalizeOnUnit(u::UnitAbsyn.Unit, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.Unit, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local unit::UnitAbsyn.Unit

              (unit, outSt) = begin
                  local params1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local params2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local params3::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unitvec1::List{MMath.Rational}
                  local unitvec2::List{MMath.Rational}
                  local st2::UnitAbsyn.Store
                @matchcontinue (u, st) begin
                  (UnitAbsyn.UNSPECIFIED(__), _)  => begin
                    (UnitAbsyn.UNSPECIFIED(), st)
                  end
                  
                  (UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(params1, unitvec1)), _)  => begin
                      @match (UnitAbsyn.SPECUNIT(params2, unitvec2), st2) = normalizeParamsValues(params1, UnitAbsyn.SPECUNIT(nil, unitvec1), st)
                      params3 = normalizeParamsExponents(params2)
                    (UnitAbsyn.SPECIFIED(UnitAbsyn.SPECUNIT(params3, unitvec2)), st2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::normalizeOnUnit() failed\\n")
                      fail()
                  end
                end
              end
          (unit, outSt)
        end

         #= normalize the exponents of a parameter list =#
        function normalizeParamsExponents(inparams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}) ::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}} 
              local outparams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}

              outparams = begin
                  local rest1::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local rest2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local rest3::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local name::String
                  local loc1::ModelicaInteger
                  local expo1::MMath.Rational
                  local expo2::MMath.Rational
                  local expo3::MMath.Rational
                  local param::Tuple{MMath.Rational, UnitAbsyn.TypeParameter}
                   #=  Case: No more elements in list
                   =#
                @matchcontinue inparams begin
                   nil()  => begin
                    nil
                  end
                  
                  (expo1, UnitAbsyn.TYPEPARAMETER(name, loc1)) <| rest1  => begin
                      @match (true, expo2, rest2) = getParam(rest1, loc1)
                      expo3 = MMath.addRational(expo1, expo2)
                      rest3 = normalizeParamsExponents(_cons((expo3, UnitAbsyn.TYPEPARAMETER(name, loc1)), rest2))
                    rest3
                  end
                  
                  (MMath.RATIONAL(0, 1), _) <| rest1  => begin
                      rest2 = normalizeParamsExponents(rest1)
                    rest2
                  end
                  
                  param <| rest1  => begin
                      rest2 = normalizeParamsExponents(rest1)
                    _cons(param, rest2)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::normalizeParamsExponents() failed\\n")
                      fail()
                  end
                end
              end
               #=  Case: Found duplicate parameter in list
               =#
               #=  Case: No duplicates in list and exponent IS zero
               =#
               #=  Case: No duplicates in list and exponent is not zero
               =#
          outparams
        end

         #= returns the next param in list and removes it from the list. 'found'=true if an location existed =#
        function getParam(inparams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}, loc::ModelicaInteger) ::Tuple{Bool, MMath.Rational, List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}} 
              local outparams::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
              local outexpo::MMath.Rational
              local found::Bool

              (found, outexpo, outparams) = begin
                  local rest::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local rest2::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local name::String
                  local loc2::ModelicaInteger
                  local expo::MMath.Rational
                  local found2::Bool
                  local param::Tuple{MMath.Rational, UnitAbsyn.TypeParameter}
                @matchcontinue (inparams, loc) begin
                  ( nil(), _)  => begin
                    (false, MMath.RATIONAL(1, 1), nil)
                  end
                  
                  ((expo, UnitAbsyn.TYPEPARAMETER(_, loc2)) <| rest, _)  => begin
                      @match true = intEq(loc2, loc)
                    (true, expo, rest)
                  end
                  
                  (param <| rest, _)  => begin
                      (found2, expo, rest2) = getParam(rest, loc)
                    (found2, expo, _cons(param, rest2))
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::getParam() failed\\n")
                      fail()
                  end
                end
              end
          (found, outexpo, outparams)
        end

         #= normalize the values that the the list of unit parameters points at =#
        function normalizeParamsValues(inparams::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}}, suin::UnitAbsyn.SpecUnit, st::UnitAbsyn.Store) ::Tuple{UnitAbsyn.SpecUnit, UnitAbsyn.Store} 
              local outSt::UnitAbsyn.Store
              local uout::UnitAbsyn.SpecUnit

              (uout, outSt) = begin
                  local rest::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local st2::UnitAbsyn.Store
                  local st3::UnitAbsyn.Store
                  local u2::UnitAbsyn.Unit
                  local su2::UnitAbsyn.SpecUnit
                  local su3::UnitAbsyn.SpecUnit
                  local name::String
                  local loc::ModelicaInteger
                  local expo::MMath.Rational
                @matchcontinue (inparams, suin, st) begin
                  ( nil(), _, _)  => begin
                    (suin, st)
                  end
                  
                  ((expo, UnitAbsyn.TYPEPARAMETER(name, loc)) <| rest, _, _)  => begin
                      (u2, st2) = normalize(loc, st)
                      su2 = mulSpecUnitWithNorm(suin, u2, name, loc, expo)
                      (su3, st3) = normalizeParamsValues(rest, su2, st2)
                    (su3, st3)
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::normalizeParamsValues() failed\\n")
                      fail()
                  end
                end
              end
          (uout, outSt)
        end

        function mulSpecUnitWithNorm(suin::UnitAbsyn.SpecUnit, normunit::UnitAbsyn.Unit, name::String, loc::ModelicaInteger, expo::MMath.Rational) ::UnitAbsyn.SpecUnit 
              local suout::UnitAbsyn.SpecUnit

              suout = begin
                  local params::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unitvec::List{MMath.Rational}
                  local su2::UnitAbsyn.SpecUnit
                  local sunorm::UnitAbsyn.SpecUnit
                  local su3::UnitAbsyn.SpecUnit
                  local su4::UnitAbsyn.SpecUnit
                @matchcontinue (suin, normunit, name, loc, expo) begin
                  (UnitAbsyn.SPECUNIT(params, unitvec), UnitAbsyn.UNSPECIFIED(__), _, _, _)  => begin
                    UnitAbsyn.SPECUNIT(_cons((expo, UnitAbsyn.TYPEPARAMETER(name, loc)), params), unitvec)
                  end
                  
                  (su2, UnitAbsyn.SPECIFIED(sunorm), _, _, _)  => begin
                      su3 = powSpecUnit(sunorm, expo)
                      su4 = mulSpecUnit(su2, su3)
                    su4
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("UnitChecker::mulSpecUnitWithNorm() failed\\n")
                      fail()
                  end
                end
              end
          suout
        end

        function printSpecUnit(text::String, su::UnitAbsyn.SpecUnit)  
              _ = begin
                  local params::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                  local unitvec::List{MMath.Rational}
                  local str::String
                @match (text, su) begin
                  (str, UnitAbsyn.SPECUNIT(params, _))  => begin
                      print(str)
                      print(" \\")
                      print(UnitAbsynBuilder.unit2str(UnitAbsyn.SPECIFIED(su)))
                      print("\\ {")
                      printSpecUnitParams(params)
                      print("}\\n")
                    ()
                  end
                end
              end
        end

        function printSpecUnitParams(params::List{<:Tuple{<:MMath.Rational, UnitAbsyn.TypeParameter}})  
              _ = begin
                  local name::String
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local loc::ModelicaInteger
                  local rest::List{Tuple{MMath.Rational, UnitAbsyn.TypeParameter}}
                @match params begin
                   nil()  => begin
                    ()
                  end
                  
                  (MMath.RATIONAL(i1, i2), UnitAbsyn.TYPEPARAMETER(name, loc)) <| rest  => begin
                      print("(\\")
                      print(name)
                      print("\\,")
                      print(intString(loc))
                      print(")^(")
                      print(intString(i1))
                      print("/")
                      print(intString(i2))
                      print("),")
                      printSpecUnitParams(rest)
                    ()
                  end
                end
              end
        end

         #= Test unit operations =#
        function testUnitOp()  
              local u1::UnitAbsyn.Unit
              local u2::UnitAbsyn.Unit
              local u3::UnitAbsyn.Unit
              local u4::UnitAbsyn.Unit
              local str1::String
              local str2::String

              print("test")
        end

         #= Print out the result from the unit check =#
        function printResult(res::UnitAbsyn.UnitCheckResult)  
              _ = begin
                  local u1::UnitAbsyn.SpecUnit
                  local u2::UnitAbsyn.SpecUnit
                  local str1::String
                  local str2::String
                @match res begin
                  UnitAbsyn.CONSISTENT(__)  => begin
                      print("\\n---\\nThe system of units is consistent.\\n---\\n")
                    ()
                  end
                  
                  UnitAbsyn.INCONSISTENT(u1, u2)  => begin
                      print("\\n---\\nThe system of units is inconsistent. \\")
                      str1 = UnitAbsynBuilder.unit2str(UnitAbsyn.SPECIFIED(u1))
                      print(str1)
                      print("\\ != \\")
                      str2 = UnitAbsynBuilder.unit2str(UnitAbsyn.SPECIFIED(u2))
                      print(str2)
                      print("\\\\n---\\n")
                    ()
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
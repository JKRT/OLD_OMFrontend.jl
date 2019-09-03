  module MMath 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Rational 

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

         @Uniontype Rational begin
              @Record RATIONAL begin

                       nom #= numerator =#::ModelicaInteger
                       denom #= denominator =#::ModelicaInteger
              end
         end

         const RAT0 = RATIONAL(0, 1)::Rational

         const RAT1 = RATIONAL(1, 1)::Rational

         #= comparison if greater than =#
        function isGreaterThan(r1::Rational, r2::Rational) ::Bool 
              local b::Bool

              b = realGt(r1.nom / r1.denom, r2.nom / r2.denom)
          b
        end

         #= adds two rationals =#
        function addRational(r1::Rational, r2::Rational) ::Rational 
              local r::Rational

              r = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local d::ModelicaInteger
                @match (r1, r2) begin
                  (RATIONAL(i1, i2), RATIONAL(i3, i4))  => begin
                      ri1 = i1 * i4 + i3 * i2
                      ri2 = i2 * i4
                      d = intGcd(ri1, ri2)
                      ri1 = intDiv(ri1, d)
                      ri2 = intDiv(ri2, d)
                    normalizeZero(RATIONAL(ri1, ri2))
                  end
                end
              end
          r
        end

         #= if numerator is zero, set denominator to 1 =#
        function normalizeZero(r::Rational) ::Rational 
              local outR::Rational

              outR = begin
                @match r begin
                  RATIONAL(0, _)  => begin
                    RATIONAL(0, 1)
                  end
                  
                  _  => begin
                      r
                  end
                end
              end
          outR
        end

         #= converts a rational to a string =#
        function rationalString(r::Rational) ::String 
              local str::String

              str = begin
                  local n::ModelicaInteger
                  local d::ModelicaInteger
                @match r begin
                  RATIONAL(n, d)  => begin
                      str = intString(n) + "/" + intString(d)
                    str
                  end
                end
              end
          str
        end

        function equals(r1::Rational, r2::Rational) ::Bool 
              local res::Bool

              res = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                @match (r1, r2) begin
                  (RATIONAL(i1, i2), RATIONAL(i3, i4))  => begin
                    i1 * i4 - i3 * i2 == 0
                  end
                end
              end
          res
        end

         #= subtracts two rationals =#
        function subRational(r1::Rational, r2::Rational) ::Rational 
              local r::Rational

              r = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local d::ModelicaInteger
                @match (r1, r2) begin
                  (RATIONAL(i1, i2), RATIONAL(i3, i4))  => begin
                      ri1 = i1 * i4 - i3 * i2
                      ri2 = i2 * i4
                      d = intGcd(ri1, ri2)
                      ri1 = intDiv(ri1, d)
                      ri2 = intDiv(ri2, d)
                    normalizeZero(RATIONAL(ri1, ri2))
                  end
                end
              end
          r
        end

         #= multiply two rationals =#
        function multRational(r1::Rational, r2::Rational) ::Rational 
              local r::Rational

              r = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local d::ModelicaInteger
                @match (r1, r2) begin
                  (RATIONAL(i1, i2), RATIONAL(i3, i4))  => begin
                      ri1 = i1 * i3
                      ri2 = i2 * i4
                      d = intGcd(ri1, ri2)
                      ri1 = intDiv(ri1, d)
                      ri2 = intDiv(ri2, d)
                    normalizeZero(RATIONAL(ri1, ri2))
                  end
                end
              end
          r
        end

         #= division of two rationals i1/i2 / i3/i4 = (i1*i4) / (i3*i2)  =#
        function divRational(r1::Rational, r2::Rational) ::Rational 
              local r::Rational

              r = begin
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local i4::ModelicaInteger
                  local ri1::ModelicaInteger
                  local ri2::ModelicaInteger
                  local d::ModelicaInteger
                @match (r1, r2) begin
                  (RATIONAL(i1, i2), RATIONAL(i3, i4))  => begin
                      ri1 = i1 * i4
                      ri2 = i3 * i2
                      d = intGcd(ri1, ri2)
                      ri1 = intDiv(ri1, d)
                      ri2 = intDiv(ri2, d)
                    normalizeZero(RATIONAL(ri1, ri2))
                  end
                end
              end
          r
        end

         #= returns the greatest common divisor for two Integers =#
        function intGcd(i1::ModelicaInteger, i2::ModelicaInteger) ::ModelicaInteger 
              local i::ModelicaInteger

              i = begin
                @match (i1, i2) begin
                  (_, 0)  => begin
                    i1
                  end
                  
                  _  => begin
                      intGcd(i2, intMod(i1, i2))
                  end
                end
              end
          i
        end

         #= /* Tests */ =#

         #= test rational operators =#
        function testRational()  
              _ = begin
                @matchcontinue () begin
                  ()  => begin
                      @match RATIONAL(7, 6) = addRational(RATIONAL(1, 2), RATIONAL(2, 3))
                      @match RATIONAL(2, 1) = addRational(RATIONAL(1, 2), RATIONAL(3, 2))
                      @match RATIONAL(1, 1) = subRational(RATIONAL(3, 2), RATIONAL(1, 2))
                      @match RATIONAL(1, 3) = subRational(RATIONAL(1, 2), RATIONAL(1, 6))
                      @match RATIONAL(4, 3) = multRational(RATIONAL(2, 3), RATIONAL(4, 2))
                      @match RATIONAL(1, 1) = multRational(RATIONAL(1, 1), RATIONAL(1, 1))
                      @match RATIONAL(1, 2) = divRational(RATIONAL(1, 3), RATIONAL(2, 3))
                      print("testRational succeeded\\n")
                    ()
                  end
                  
                  _  => begin
                        print("testRationals failed\\n")
                      ()
                  end
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
  module StackOverflow


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

        import Config
        import System

        function unmangle(inSymbol::String) ::String
              local outSymbol::String

              outSymbol = inSymbol
              if stringLength(inSymbol) > 4
                if substring(inSymbol, 1, 4) == "omc_"
                  outSymbol = substring(outSymbol, 5, stringLength(outSymbol))
                  outSymbol = System.stringReplace(outSymbol, "__", "#")
                  outSymbol = System.stringReplace(outSymbol, "_", ".")
                  outSymbol = System.stringReplace(outSymbol, "#", "_")
                end
              end
          outSymbol
        end

        function stripAddresses(inSymbol::String) ::String
              local outSymbol::String

              local n::ModelicaInteger
              local strs::List{String}
              local so::String
              local fun::String

               #=  regex for Linux messages
               =#
              (n, strs) = System.regex(inSymbol, "^([^(]*)[(]([^+]*[^+]*)[+][^)]*[)] *[[]0x[0-9a-fA-F]*[]]", 3, extended = true)
              if n == 3
                @match _ <| so <| fun <| nil = strs
                outSymbol = so + "(" + unmangle(fun) + ")"
              else
                (n, strs) = System.regex(inSymbol, "^[0-9 ]*([A-Za-z0-9.]*) *0x[0-9a-fA-F]* ([A-Za-z0-9_]*) *[+] *[0-9]*", 3, extended = true)
                if n == 3
                  @match _ <| so <| fun <| nil = strs
                  outSymbol = so + "(" + unmangle(fun) + ")"
                else
                  outSymbol = inSymbol
                end
              end
               #=  regex for OSX messages
               =#
          outSymbol
        end

        function triggerStackOverflow()
            #= TODO: Defined in the runtime =#
        end

        function generateReadableMessage(numFrames::ModelicaInteger = 1000, numSkip::ModelicaInteger = 4, delimiter::String = "\\n") ::String
              local str::String

              StackOverflow.setStacktraceMessages(numSkip, numFrames)
              str = getReadableMessage(delimiter = delimiter)
          str
        end

        function getReadableMessage(delimiter::String = "\\n") ::String
              local str::String

              str = stringDelimitList(StackOverflow.readableStacktraceMessages(), delimiter)
          str
        end

        function readableStacktraceMessages() ::List{String}
              local symbols::List{String} = nil

              local prev::String = ""
              local n::ModelicaInteger = 1
              local prevN::ModelicaInteger = 1

              if Config.getRunningTestsuite()
                symbols = list("[bt] [Symbols are not generated when running the test suite]")
                return symbols
              end
              for symbol in list(stripAddresses(s) for s in getStacktraceMessages())
                if prev == ""
                elseif symbol != prev
                  symbols = _cons("[bt] #" + StringFunction(prevN) + (if n != prevN
                        "..." + StringFunction(n)
                      else
                        ""
                      end) + " " + prev, symbols)
                  n = n + 1
                  prevN = n
                else
                  n = n + 1
                end
                prev = symbol
              end
              symbols = _cons("[bt] #" + StringFunction(prevN) + (if n != prevN
                    "..." + StringFunction(n)
                  else
                    ""
                  end) + " " + prev, symbols)
              symbols = listReverse(symbols)
          symbols
        end

        function getStacktraceMessages() ::List{String}
              local symbols::List{String}

            #= TODO: Defined in the runtime =#
          symbols
        end

        function setStacktraceMessages(numSkip::ModelicaInteger, numFrames::ModelicaInteger)
            #= TODO: Defined in the runtime =#
        end

        function hasStacktraceMessages() ::Bool
              local b::Bool

            #= TODO: Defined in the runtime =#
          b
        end

        function clearStacktraceMessages()
            #= TODO: Defined in the runtime =#
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

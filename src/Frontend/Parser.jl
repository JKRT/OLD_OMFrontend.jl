
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

module Parser

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
#= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
@UniontypeDecl ParserResult

import Absyn
import BaseHashTable
import HashTableStringToProgram
import Config
import ErrorExt
import Flags
import ParserExt
import AbsynToSCode
import System
import Util

#= Parse a mo-file =#
function parse(filename::String, encoding::String, libraryPath::String = "", lveInstance::Option{<:ModelicaInteger} = NONE()) ::Absyn.Program
  local outProgram::Absyn.Program

  outProgram = parsebuiltin(filename, encoding, libraryPath, lveInstance)
  #= /* Check that the program is not totally off the charts */ =#
  _ = AbsynToSCode.translateAbsyn2SCode(outProgram)
  outProgram
end

#= Parse a mos-file =#
function parseexp(filename::String)
end

#= Parse a string as if it were a stored definition =#
function parsestring(str::String, infoFilename::String = "<interactive>") ::Absyn.Program
  local outProgram::Absyn.Program

  outProgram = ParserExt.parsestring(str, infoFilename, Config.acceptedGrammar(), Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), Config.getRunningTestsuite())
  #= /* Check that the program is not totally off the charts */ =#
  _ = AbsynToSCode.translateAbsyn2SCode(outProgram)
  outProgram
end

#= Like parse, but skips the SCode check to avoid infinite loops for ModelicaBuiltin.mo. =#
function parsebuiltin(filename::String, encoding::String, libraryPath::String = "", lveInstance::Option{<:ModelicaInteger} = NONE(),
                      acceptedGram::ModelicaInteger = Config.acceptedGrammar(),
                      languageStandardInt::ModelicaInteger = Flags.getConfigEnum(Flags.LANGUAGE_STANDARD))::Absyn.Program
  local outProgram::Absyn.Program
  local realpath::String
  println("Filename for parsebuiltin!: $filename")  
  realpath = Util.replaceWindowsBackSlashWithPathDelimiter(System.realpath(filename))
  outProgram = ParserExt.parse(realpath, Util.testsuiteFriendly(realpath), acceptedGram, encoding, languageStandardInt, Config.getRunningTestsuite(), libraryPath, lveInstance)
  outProgram
end

#= Parse a string as if it was a sequence of statements =#
function parsestringexp(str::String, infoFilename::String = "<interactive>")
end

function stringPath(str::String) ::Absyn.Path
  local path::Absyn.Path

  path = ParserExt.stringPath(str, "<internal>", Config.acceptedGrammar(), Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), Config.getRunningTestsuite())
  path
end

function stringCref(str::String) ::Absyn.ComponentRef
  local cref::Absyn.ComponentRef

  cref = ParserExt.stringCref(str, "<internal>", Config.acceptedGrammar(), Flags.getConfigEnum(Flags.LANGUAGE_STANDARD), Config.getRunningTestsuite())
  cref
end

function parallelParseFiles(filenames::List{<:String}, encoding::String, numThreads::ModelicaInteger = Config.noProc(), libraryPath::String = "", lveInstance::Option{<:ModelicaInteger} = NONE()) ::HashTableStringToProgram.HashTable
  local ht::HashTableStringToProgram.HashTable

  local partialResults::List{ParserResult}

  partialResults = parallelParseFilesWork(filenames, encoding, numThreads, libraryPath, lveInstance)
  ht = HashTableStringToProgram.emptyHashTableSized(Util.nextPrime(listLength(partialResults)))
  for res in partialResults
    ht = begin
      local p::Absyn.Program
      @match res begin
        PARSERRESULT(program = SOME(p))  => begin
          BaseHashTable.add((res.filename, p), ht)
        end
      end
    end
  end
  ht
end

function parallelParseFilesToProgramList(filenames::List{<:String}, encoding::String, numThreads::ModelicaInteger = Config.noProc()) ::List{Absyn.Program}
  local result::List{Absyn.Program} = nil

  for r in parallelParseFilesWork(filenames, encoding, numThreads)
    result = _cons(begin
                   local p::Absyn.Program
                   @match r begin
                   PARSERRESULT(program = SOME(p))  => begin
                   p
                   end
                   end
                   end, result)
  end
  result = MetaModelica.Dangerous.listReverseInPlace(result)
  result
end

function startLibraryVendorExecutable(lvePath::String) ::Tuple{Bool, Option{ModelicaInteger}}
  local lveInstance::Option{ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#
  local success::Bool

  (success, lveInstance) = ParserExt.startLibraryVendorExecutable(lvePath)
  (success, lveInstance #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#)
end

function stopLibraryVendorExecutable(lveInstance::Option{<:ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#)
  ParserExt.stopLibraryVendorExecutable(lveInstance)
end

@Uniontype ParserResult begin
  @Record PARSERRESULT begin

    filename::String
    program::Option{Absyn.Program}
  end
end

function parallelParseFilesWork(filenames::List{<:String}, encoding::String, numThreads::ModelicaInteger, libraryPath::String = "", lveInstance::Option{<:ModelicaInteger} = NONE()) ::List{ParserResult}
  local partialResults::List{ParserResult}

  local workList::List{Tuple{String, String, String, Option{ModelicaInteger}}} = list((file, encoding, libraryPath, lveInstance) for file in filenames)

  if Config.getRunningTestsuite() || Config.noProc() == 1 || numThreads == 1 || listLength(filenames) < 2 || ! libraryPath == ""
    partialResults = list(loadFileThread(t) for t in workList)
  else
    partialResults = System.launchParallelTasks(min(8, numThreads), workList, loadFileThread)
  end
  #=  GC.disable();  Seems to sometimes break building nightly omc
  =#
  #= /* Boehm GC does not scale to infinity */ =#
  #=  GC.enable();
  =#
  partialResults
end

function loadFileThread(inFileEncoding::Tuple{<:String, String, String, Option{<:ModelicaInteger}}) ::ParserResult
  local result::ParserResult

  result = begin
    local filename::String
    local encoding::String
    local libraryPath::String
    local lveInstance::Option{ModelicaInteger}
    @matchcontinue inFileEncoding begin
      (filename, encoding, libraryPath, lveInstance)  => begin
        PARSERRESULT(filename, SOME(Parser.parse(filename, encoding, libraryPath, lveInstance)))
      end

      (filename, _, _, _)  => begin
        PARSERRESULT(filename, NONE())
      end
    end
  end
  if ErrorExt.getNumMessages() > 0
    ErrorExt.moveMessagesToParentThread()
  end
  result
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

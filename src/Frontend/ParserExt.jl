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

#= TODO: these are currently stubs. Needs a new C-interface. =#
module ParserExt
using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
using ExportAll
import Absyn

#= Parse a mo-file =#
function parse(filename::String, infoFilename::String, acceptedGram::ModelicaInteger, encoding::String, languageStandardInt::ModelicaInteger, runningTestsuite::Bool, libraryPath::String, lveInstance::Option{<:ModelicaInteger}) ::Absyn.Program
  #= TODO: Defined in the runtime =#
  outProgram
end

#= Parse a mos-file =#
function parseexp(filename::String, infoFilename::String, acceptedGram::ModelicaInteger, languageStandardInt::ModelicaInteger, runningTestsuite::Bool)
  #= TODO: Defined in the runtime =#
end

#= Parse a string as if it were a stored definition =#
function parsestring(str::String, infoFilename::String = "<interactive>", acceptedGram::ModelicaInteger = 0, languageStandardInt::ModelicaInteger = 0, runningTestsuite::Bool = false) ::Absyn.Program
  #= TODO: Defined in the runtime =#
end

#= Parse a string as if it was a sequence of statements =#
function parsestringexp(str::String, infoFilename::String = "<interactive>", acceptedGram::ModelicaInteger = 0, languageStandardInt::ModelicaInteger = 0, runningTestsuite::Bool = false)
  #= TODO: Defined in the runtime =#
  outStatements
end

function stringPath(str::String, infoFilename::String, acceptedGram::ModelicaInteger, languageStandardInt::ModelicaInteger, runningTestsuite::Bool) ::Absyn.Path
  local path::Absyn.Path
  #= TODO: Defined in the runtime =#
  path
end

function stringCref(str::String, infoFilename::String, acceptedGram::ModelicaInteger, languageStandardInt::ModelicaInteger, runningTestsuite::Bool) ::Absyn.ComponentRef
  local cref::Absyn.ComponentRef
  #= TODO: Defined in the runtime =#
  cref
end

#= Starts the library vendor executable =#
function startLibraryVendorExecutable(lvePath::String) ::Tuple{Bool, Option{ModelicaInteger}}
  local lveInstance::Option{ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#
  local success::Bool
  #= TODO: Defined in the runtime =#
  (success, lveInstance #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#)
end

function stopLibraryVendorExecutable(lveInstance::Option{<:ModelicaInteger} #= Stores a pointer. If it is declared as Integer, it is truncated to 32-bit. =#)
  #= TODO: Defined in the runtime =#
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

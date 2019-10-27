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


module Settings 

using MetaModelica
using ExportAll

import Pkg

#=The directory path. Can be modified=#
INSTALLATION_DIRECTORY_PATH = realpath(realpath(Base.find_package("OMCompiler") * "./../.."))

#= Returns the version number of this release =#
function getVersionNr() ::String 
 "TODO"       
end

function setCompilePath(inString::String)  
    #= TODO: Defined in the runtime =#
end

function setCompileCommand(inString::String)  
    #= TODO: Defined in the runtime =#
end

function getCompileCommand() ::String 
    #= TODO: Defined in the runtime =#
end

function setTempDirectoryPath(inString::String)  
    #= TODO: Defined in the runtime =#
end

function getTempDirectoryPath() ::String 
    #= TODO: Defined in the runtime =#
    "TODO getTempDirectoryPath"
end


function setInstallationDirectoryPath(path::String)  
  global INSTALLATION_DIRECTORY_PATH = path
end

function getInstallationDirectoryPath()::String
  if INSTALLATION_DIRECTORY_PATH != nothing
    INSTALLATION_DIRECTORY_PATH
  else #The default variant
    #= pathToOMC is always in src. We need to go up two steps =#
    local pathToOMC = realpath(realpath(Base.find_package("OMCompiler") * "./../.."))
    global INSTALLATION_DIRECTORY_PATH = pathToOMC    
  end
end

function setModelicaPath(inString::String)  
  #= TODO: Defined in the runtime =#
end

function getModelicaPath(runningTestsuite::Bool) ::String 
    #= TODO: Defined in the runtime =#
    "modelicaPath"
end

function getHomeDir(runningTestsuite::Bool) ::String 
    #= TODO: Defined in the runtime =#
    "getHomeDir"
end

function getEcho()::ModelicaInteger 
    #= TODO: Defined in the runtime =#
    0
end

function setEcho(echo::ModelicaInteger)  
    #= TODO: Defined in the runtime =#
end

@exportAll()
end

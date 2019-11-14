#=
# This file is part of OpenModelica.
#
# Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
# c/o Linköpings universitet, Department of Computer and Information Science,
# SE-58183 Linköping, Sweden.
#
# All rights reserved.
#
# THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
# THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
# ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
# RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
# ACCORDING TO RECIPIENTS CHOICE.
#
# The OpenModelica software and the Open Source Modelica
# Consortium (OSMC) Public License (OSMC-PL) are obtained
# from OSMC, either from the above address,
# from the URLs: http:www.ida.liu.se/projects/OpenModelica or
# http:www.openmodelica.org, and in the OpenModelica distribution.
# GNU version 3 is obtained from: http:www.gnu.org/copyleft/gpl.html.
#
# This program is distributed WITHOUT ANY WARRANTY; without
# even the implied warranty of  MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
# IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
#
# See the full OSMC Public License conditions for more details.
#
=#

module OMCompiler

#=TODO make it call the parserscript from OpenModelica home=#
const UTIL = "src/Util/."
const FRONTEND = "src/Frontend/."
const FFRONTEND = "src/FFrontend/."
const CURRENT_DIRECTORY = "."
if ! (CURRENT_DIRECTORY in LOAD_PATH && FRONTEND in LOAD_PATH && FFRONTEND in LOAD_PATH)
  push!(LOAD_PATH, CURRENT_DIRECTORY)
  push!(LOAD_PATH, UTIL)
  push!(LOAD_PATH, FRONTEND)
  push!(LOAD_PATH, FFRONTEND)
end
println(LOAD_PATH)
#include("./AbsynUtil.jl")
#include("./List.jl")
#include("./SCode.jl")

#include("../Frontend/Global.jl")
#include("../FFrontend/FCoreUtil.jl")
#include("../Util/Flags.jl")
#include("../Frontend/AbsynToSCode.jl")
#include("../Frontend/Inst.jl")
#include("../Frontend/InnerOuter.jl")
#include("./SCodeUtil.jl")

import Global
import Flags
import AbsynToSCode
import SCode
import Absyn
import FCoreUtil
import Inst
import InstHashTable
import InnerOuterTypes

module AbsynPrograms
  using Absyn
  using MetaModelica
  import OpenModelicaParser

path = realpath(realpath(Base.find_package("OMCompiler") * "./../.."))

path = joinpath(path, "lib", "omc", "HelloWorld.mo")
const HelloWorld = OpenModelicaParser.parseFile(path)
@show HelloWorld

end

function run()

  # initialize globals
  Global.initialize()
  # make sure we have all the flags loaded!
  Flags.new(Flags.emptyFlags)

  @time scode = AbsynToSCode.translateAbsyn2SCode(AbsynPrograms.HelloWorld)
  @show scode

  #= Try the bouncing ball =#
  #@time scode = AbsynToSCode.translateAbsyn2SCode(AbsynPrograms.BouncingBall)
  #@show scode
  #using Modelica_Standard_Library_AST
  #using BenchmarkTools
  #using Profile
  # P = Modelica_Standard_Library_AST.Program
  #@time AbsynToSCode.translateAbsyn2SCode(P)
  #@time AbsynToSCode.translateAbsyn2SCode(P)

  println("*******************************")
  println("SCode done")
  println("*******************************")

  InstHashTable.init()
  #= Creating a cache. At this point the SCode is the bouncing ball... =#
  println("empty cache")
  # don't do this, it will load NFModelicaBuiltin.mo
  # Flags.set(Flags.SCODE_INST, true)
  # Flags.set(Flags.EXEC_STAT, true) # not yet working!
  cache = FCoreUtil.emptyCache()
  println("after empty cache")
  className = Absyn.IDENT("HelloWorld")
  println("dive in inst")
  (cache,_,_,dae) = Inst.instantiateClass(cache, InnerOuterTypes.emptyInstHierarchy, scode, className)
  println("after inst")
  @show dae
  println("*******************************")
  println("DAE done")
  println("*******************************")
  println("Goodbye")
end

end

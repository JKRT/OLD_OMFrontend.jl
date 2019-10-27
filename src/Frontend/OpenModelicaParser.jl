module OpenModelicaParser

import Absyn
using MetaModelica

#import Settings
INSTALLATION_DIRECTORY_PATH = realpath(realpath(Base.find_package("OMCompiler") * "./../.."))

struct ParseError end

function isDerCref(exp::Absyn.Exp)::Bool
  @match exp begin
    Absyn.CALL(Absyn.CREF_IDENT("der",  nil()), Absyn.FUNCTIONARGS(Absyn.CREF(__) <|  nil(),  nil()))  => true
    _ => false
  end
end
  
const _libpath = if Sys.iswindows()
  #global ajaj = realpath(Settings.getInstallationDirectoryPath())
  local instDir = INSTALLATION_DIRECTORY_PATH
  joinpath(instDir, "lib", "ext", "libomparse-julia.dll")
else
  #joinpath(Settings.getInstallationDirectoryPath(), "/lib/ext/libomparse-julia.so")
end
  
function parseFile(fileName::String)::Absyn.Program
  local res = ccall((:parseFile, _libpath), Any, (String,) , fileName)
  if res == nothing
    throw(ParseError())
  end
  res
end

#parseFile("Banan.mo")
  
end

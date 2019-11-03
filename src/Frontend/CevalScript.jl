  module CevalScript 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    ReductionOperator = Function

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
        import Absyn
        import AbsynUtil
        import Ceval
        import DAE
        import FCore
        import Error
        import GlobalScript
        import Interactive
        import Values
        import SimCode
         #=  protected imports
         =#

        import Autoconf
        import BaseHashSet
        import CevalScriptBackend
        import CevalFunction
        import ClassInf
        import ClassLoader
        import CodegenCFunctions
        import Config
        import Corba
        import DAEUtil
        import Debug
        import Dump
        import DynLoad
        import Expression
        import ExpressionDump
        import FBuiltin
        import FCoreUtil
        import Flags
        import FGraph
        import FNode
        import GC
        import GenerateAPIFunctionsTpl
        import Global
        import GlobalScriptUtil
        import Graph
        import HashSetString
        import Inst
        import InstFunction
        import InteractiveUtil
        import ListUtil
        import Lookup
        import Mod
        import Prefix
        import Parser
        import Print
        import SCodeDump
        import SimCodeFunction
        using ExecStat: execStat, execStatReset
        import StackOverflow
        import System
        import Static
        import SCode
        import SCodeUtil
        import Settings
        import SymbolTable
        import Tpl
        import Types
        import Unparsing
        import Util
        import ValuesUtil
        import ComponentReference
        import ErrorExt

         #= 
          This is a wrapper funtion to Ceval.ceval. The purpose of this
          function is to concetrate all the calls to Ceval.ceval made from
          the Script files. This will simplify the separation of the scripting
          environment from the FrontEnd =#
        function ceval(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inBoolean::Bool #= impl =#, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local impl::Bool
                  local env::FCore.Graph
                  local msg::Absyn.Msg
                  local vallst::List{Values.Value}
                  local expl::List{DAE.Exp}
                  local newval::Values.Value
                  local value::Values.Value
                  local e::DAE.Exp
                  local funcpath::Absyn.Path
                  local cache::FCore.Cache
                   #=  adrpo: TODO! this needs more work as if we don't have a symtab we run into unloading of dlls problem
                   =#
                @matchcontinue (inCache, inEnv, inExp, inBoolean, inMsg, numIter) begin
                  (cache, env, e && DAE.CALL(path = funcpath, expLst = expl), impl, msg, _)  => begin
                      @match false = stringEq("Connection.isRoot", AbsynUtil.pathString(funcpath))
                      (cache, vallst) = Ceval.cevalList(cache, env, expl, impl, msg, numIter)
                      (cache, newval) = cevalCallFunction(cache, env, e, vallst, impl, msg, numIter + 1)
                    (cache, newval)
                  end
                  
                  (cache, env, e && DAE.CALL(__), true, msg, _)  => begin
                      (cache, value) = cevalInteractiveFunctions(cache, env, e, msg, numIter + 1)
                    (cache, value)
                  end
                  
                  (cache, env, e, impl, msg, _)  => begin
                      (cache, value) = Ceval.ceval(cache, env, e, impl, msg, numIter + 1)
                    (cache, value)
                  end
                end
              end
               #=  do not handle Connection.isRoot here!
               =#
               #=  do not roll back errors generated by evaluating the arguments
               =#
               #=  Try Interactive functions last
               =#
          (outCache, outValue)
        end

         #= a function is complete if is:
         - not partial
         - not replaceable (without redeclare)
         - replaceable and called functions are not partial or not replaceable (without redeclare) =#
        function isCompleteFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inFuncPath::Absyn.Path) ::Bool 
              local isComplete::Bool

              isComplete = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local fpath::Absyn.Path
                   #=  external functions are complete :)
                   =#
                @matchcontinue (inCache, inEnv, inFuncPath) begin
                  (cache, env, fpath)  => begin
                      @match (_, SCode.CLASS(classDef = SCode.PARTS(externalDecl = SOME(_))), _) = Lookup.lookupClass(cache, env, fpath)
                    true
                  end
                  
                  (_, _, _)  => begin
                      @match true = System.getPartialInstantiation()
                    false
                  end
                  
                  (cache, env, fpath)  => begin
                      @match (_, SCode.CLASS(partialPrefix = SCode.PARTIAL()), _) = Lookup.lookupClass(cache, env, fpath)
                    false
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
               #=  if is partial instantiation no function evaluation/generation
               =#
               #=  partial functions are not complete!
               =#
          isComplete
        end

         #= Compiles a model given a file-prefix, helper function to buildModel. =#
        function compileModel(fileprefix::String, libs::List{<:String}, workingDir::String = "", makeVars::List{<:String} = nil)  
              local omhome::String = Settings.getInstallationDirectoryPath()
              local omhome_1::String = System.stringReplace(omhome, "\\", "")
              local pd::String = Autoconf.pathDelimiter
              local cdWorkingDir::String
              local setMakeVars::String
              local libsfilename::String
              local libs_str::String
              local s_call::String
              local filename::String
              local winCompileMode::String
              local workDir::String = if stringEq(workingDir, "")
                    ""
                  else
                    workingDir + pd
                  end
              local fileDLL::String = workDir + fileprefix + Autoconf.dllExt
              local fileEXE::String = workDir + fileprefix + Autoconf.exeExt
              local fileLOG::String = workDir + fileprefix + ".log"
              local numParallel::ModelicaInteger
              local res::ModelicaInteger
              local isWindows::Bool = Autoconf.os == "Windows_NT"
              local makeVarsNoBinding::List{String}

              libsfilename = workDir + fileprefix + ".libs"
              libs_str = stringDelimitList(libs, " ")
              makeVarsNoBinding = makeVars
               #=  OMC is stupid and wants to constant evaluate inputs with bindings for iterator variables...
               =#
              System.writeFile(libsfilename, libs_str)
              if isWindows
                omhome = "set OPENMODELICAHOME=" + System.stringReplace(omhome_1, "/", "\\\\") + "&& "
                setMakeVars = sum("set " + var + "&& " for var in makeVarsNoBinding)
                cdWorkingDir = if stringEmpty(workingDir)
                      ""
                    else
                      "cd \\" + workingDir + "\\&& "
                    end
                winCompileMode = if Config.getRunningTestsuite()
                      "serial"
                    else
                      "parallel"
                    end
                s_call = stringAppendList(list(omhome, cdWorkingDir, setMakeVars, "\\", omhome_1, pd, "share", pd, "omc", pd, "scripts", pd, "Compile", "\\", " ", fileprefix, " ", Config.simulationCodeTarget(), " ", System.openModelicaPlatform(), " ", winCompileMode))
              else
                numParallel = if Config.getRunningTestsuite()
                      1
                    else
                      Config.noProc()
                    end
                cdWorkingDir = if stringEmpty(workingDir)
                      ""
                    else
                      " -C \\" + workingDir + "\\"
                    end
                setMakeVars = sum(" " + var for var in makeVarsNoBinding)
                s_call = stringAppendList(list(Autoconf.make, " -j", intString(numParallel), cdWorkingDir, " -f ", fileprefix, ".makefile", setMakeVars))
              end
               #=  We only need to set OPENMODELICAHOME on Windows, and set doesn't work in bash shells anyway
               =#
               #=  adrpo: 2010-10-05:
               =#
               #=         whatever you do, DO NOT add a space before the && otherwise
               =#
               #=         OPENMODELICAHOME that we set will contain a SPACE at the end!
               =#
               #=         set OPENMODELICAHOME=DIR && actually adds the space between the DIR and &&
               =#
               #=         to the environment variable! Don't ask me why, ask Microsoft.
               =#
              if Flags.isSet(Flags.DYN_LOAD)
                Debug.traceln("compileModel: running " + s_call)
              end
               #=  remove .exe .dll .log!
               =#
              if System.regularFileExists(fileEXE)
                @match 0 = System.removeFile(fileEXE)
              end
              if System.regularFileExists(fileDLL)
                @match 0 = System.removeFile(fileDLL)
              end
              if System.regularFileExists(fileLOG)
                @match 0 = System.removeFile(fileLOG)
              end
              if Config.getRunningTestsuite()
                System.appendFile(Config.getRunningTestsuiteFile(), fileEXE + "\\n" + fileDLL + "\\n" + fileLOG + "\\n" + fileprefix + ".o\\n" + fileprefix + ".libs\\n" + fileprefix + "_records.o\\n" + fileprefix + "_res.mat\\n")
              end
               #=  call the system command to compile the model!
               =#
              if System.systemCall(s_call, if isWindows
                    ""
                  else
                    fileLOG
                  end) != 0
                if System.regularFileExists(fileLOG)
                  Error.addMessage(Error.SIMULATOR_BUILD_ERROR, list(System.readFile(fileLOG)))
                elseif isWindows
                  s_call = stringAppendList(list(omhome_1, pd, "share", pd, "omc", pd, "scripts", pd, "Compile.bat"))
                  if ! System.regularFileExists(s_call)
                    Error.addMessage(Error.SIMULATOR_BUILD_ERROR, list(stringAppendList(list("command ", s_call, " not found. Check OPENMODELICAHOME"))))
                  end
                end
                if Flags.isSet(Flags.DYN_LOAD)
                  Debug.trace("compileModel: failed!\\n")
                end
                fail()
              end
               #=  We failed, print error
               =#
               #=  Check that it is a correct OPENMODELICAHOME, on Windows only
               =#
              if Flags.isSet(Flags.DYN_LOAD)
                Debug.trace("compileModel: successful!\\n")
              end
        end

         #= load the file or the directory structure if the file is named package.mo =#
        function loadFile(name::String, encoding::String, p::Absyn.Program, checkUses::Bool) ::Absyn.Program 
              local outProgram::Absyn.Program

              local dir::String
              local filename::String
              local cname::String
              local prio::String
              local mp::String
              local rest::List{String}

              @match true = System.regularFileExists(name)
              (dir, filename) = Util.getAbsoluteDirectoryAndFile(name)
              if filename == "package.mo" || filename == "package.moc"
                @match _cons(cname, rest) = System.strtok(ListUtil.last(System.strtok(dir, "/")), " ")
                prio = stringDelimitList(rest, " ")
                mp = System.realpath(dir + "/../") + Autoconf.groupDelimiter + Settings.getModelicaPath(Config.getRunningTestsuite())
                @match (outProgram, true) = loadModel(_cons((Absyn.IDENT(cname), list(prio), true), nil), mp, p, true, true, checkUses, true, filename == "package.moc")
                return outProgram
              end
               #=  send \"\" priority if that is it, don't send \"default\"
               =#
               #=  see https:trac.openmodelica.org/OpenModelica/ticket/2422
               =#
               #=  prio = if_(stringEq(prio,\"\"), \"default\", prio);
               =#
              outProgram = Parser.parse(name, encoding)
              ClassLoader.checkOnLoadMessage(outProgram)
              outProgram = checkUsesAndUpdateProgram(outProgram, p, checkUses, Settings.getModelicaPath(Config.getRunningTestsuite()))
          outProgram
        end

        function checkUsesAndUpdateProgram(newp::Absyn.Program, p::Absyn.Program, checkUses::Bool, modelicaPath::String) ::Absyn.Program 


              local modelsToLoad::List{Tuple{Absyn.Path, List{String}, Bool}}

              modelsToLoad = if checkUses
                    Interactive.getUsesAnnotationOrDefault(newp, requireExactVersion = true)
                  else
                    nil
                  end
              p = Interactive.updateProgram(newp, p)
              (p, _) = loadModel(modelsToLoad, modelicaPath, p, false, true, true, true, false)
          p
        end

        LoadModelFoldArg = Tuple 
         #= /*modelicaPath*/ =#
         #= /*forceLoad*/ =#
         #= /*notifyLoad*/ =#
         #= /*checkUses*/ =#
         #= /*requireExactVersion*/ =#
         #= /*encrypted*/ =#

        function loadModel(imodelsToLoad::List{<:Tuple{<:Absyn.Path, List{<:String}, Bool}}, modelicaPath::String, ip::Absyn.Program, forceLoad::Bool, notifyLoad::Bool, checkUses::Bool, requireExactVersion::Bool, encrypted::Bool = false) ::Tuple{Absyn.Program, Bool} 
              local success::Bool
              local pnew::Absyn.Program

              local arg::LoadModelFoldArg = (modelicaPath, forceLoad, notifyLoad, checkUses, requireExactVersion, encrypted)

              (pnew, success) = ListUtil.fold1(imodelsToLoad, loadModel1, arg, (ip, true))
          (pnew, success)
        end

        function loadModel1(modelToLoad::Tuple{<:Absyn.Path, List{<:String}, Bool}, inArg::LoadModelFoldArg, inTpl::Tuple{<:Absyn.Program, Bool}) ::Tuple{Absyn.Program, Bool} 
              local outTpl::Tuple{Absyn.Program, Bool}

              local modelsToLoad::List{Tuple{Absyn.Path, List{String}, Bool}}
              local b::Bool
              local b1::Bool
              local success::Bool
              local forceLoad::Bool
              local notifyLoad::Bool
              local checkUses::Bool
              local requireExactVersion::Bool
              local onlyCheckFirstModelicaPath::Bool
              local encrypted::Bool
              local path::Absyn.Path
              local versionsLst::List{String}
              local pathStr::String
              local versions::String
              local className::String
              local version::String
              local modelicaPath::String
              local thisModelicaPath::String
              local p::Absyn.Program
              local pnew::Absyn.Program
              local msgTokens::Error.MessageTokens

              (path, versionsLst, onlyCheckFirstModelicaPath) = modelToLoad
              (modelicaPath, forceLoad, notifyLoad, checkUses, requireExactVersion, encrypted) = inArg
              if onlyCheckFirstModelicaPath
                @match _cons(thisModelicaPath, _) = System.strtok(modelicaPath, Autoconf.groupDelimiter)
              else
                thisModelicaPath = modelicaPath
              end
               #= /* Using loadFile() */ =#
              try
                (p, success) = inTpl
                if checkModelLoaded(modelToLoad, p, forceLoad, NONE())
                  pnew = Absyn.PROGRAM(nil, Absyn.TOP())
                  version = ""
                else
                  pnew = ClassLoader.loadClass(path, versionsLst, thisModelicaPath, NONE(), requireExactVersion, encrypted)
                  version = getPackageVersion(path, pnew)
                  b = ! notifyLoad || forceLoad
                  msgTokens = list(AbsynUtil.pathString(path), version)
                  Error.assertionOrAddSourceMessage(b, Error.NOTIFY_NOT_LOADED, msgTokens, AbsynUtil.dummyInfo)
                end
                p = Interactive.updateProgram(pnew, p)
                b = true
                if checkUses
                  modelsToLoad = Interactive.getUsesAnnotationOrDefault(pnew, requireExactVersion)
                  (p, b) = loadModel(modelsToLoad, modelicaPath, p, false, notifyLoad, checkUses, requireExactVersion, false)
                end
                outTpl = (p, success && b)
              catch
                (p, _) = inTpl
                pathStr = AbsynUtil.pathString(path)
                versions = stringDelimitList(versionsLst, ",")
                msgTokens = list(pathStr, versions, thisModelicaPath)
                if forceLoad
                  Error.addMessage(Error.LOAD_MODEL, msgTokens)
                  outTpl = (p, false)
                else
                  Error.addMessage(Error.NOTIFY_LOAD_MODEL_FAILED, msgTokens)
                  outTpl = inTpl
                end
              end
          outTpl
        end

        function checkModelLoaded(tpl::Tuple{<:Absyn.Path, List{<:String}, Bool}, p::Absyn.Program, forceLoad::Bool, failNonLoad::Option{<:String}) ::Bool 
              local loaded::Bool

              loaded = begin
                  local cdef::Absyn.Class
                  local str1::String
                  local str2::String
                  local ostr2::Option{String}
                  local path::Absyn.Path
                @matchcontinue (tpl, p, forceLoad, failNonLoad) begin
                  (_, _, true, _)  => begin
                    false
                  end
                  
                  ((path, str1 <| _, _), _, false, _)  => begin
                      cdef = Interactive.getPathedClassInProgram(path, p)
                      ostr2 = AbsynUtil.getNamedAnnotationInClass(cdef, Absyn.IDENT("version"), Interactive.getAnnotationStringValueOrFail)
                      checkValidVersion(path, str1, ostr2)
                    true
                  end
                  
                  (_, _, _, NONE())  => begin
                    false
                  end
                  
                  ((path, _, _), _, _, SOME(str2))  => begin
                      str1 = AbsynUtil.pathString(path)
                      Error.addMessage(Error.INST_NON_LOADED, list(str1, str2))
                    false
                  end
                end
              end
          loaded
        end

        function checkValidVersion(path::Absyn.Path, version::String, actualVersion::Option{<:String})  
              _ = begin
                  local pathStr::String
                  local str1::String
                  local str2::String
                @matchcontinue (path, version, actualVersion) begin
                  (_, str1, SOME(str2))  => begin
                      @match true = stringEq(str1, str2)
                    ()
                  end
                  
                  (_, str1, SOME(str2))  => begin
                      pathStr = AbsynUtil.pathString(path)
                      Error.addMessage(Error.LOAD_MODEL_DIFFERENT_VERSIONS, list(pathStr, str1, str2))
                    ()
                  end
                  
                  (_, str1, NONE())  => begin
                      pathStr = AbsynUtil.pathString(path)
                      Error.addMessage(Error.LOAD_MODEL_DIFFERENT_VERSIONS, list(pathStr, str1, "unknown"))
                    ()
                  end
                end
              end
        end

         #= defined in the interactive environment. =#
        function cevalInteractiveFunctions(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp #= expression to evaluate =#, msg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local exp::DAE.Exp
                  local eLst::List{DAE.Exp}
                  local valLst::List{Values.Value}
                  local name::String
                  local value::Values.Value
                  local t1::ModelicaReal
                  local t2::ModelicaReal
                  local t::ModelicaReal
                   #=  This needs to be first because otherwise it takes 0 time to get the value :)
                   =#
                @matchcontinue (inCache, inEnv, inExp, msg, numIter) begin
                  (cache, env, DAE.CALL(path = Absyn.IDENT(name = "timing"), expLst = exp <|  nil()), _, _)  => begin
                      t1 = System.time()
                      (cache, _) = Ceval.ceval(cache, env, exp, true, msg, numIter + 1)
                      t2 = System.time()
                      t = t2 - t1
                    (cache, Values.REAL(t))
                  end
                  
                  (cache, env, DAE.CALL(path = Absyn.IDENT(name), attr = DAE.CALL_ATTR(builtin = true), expLst = eLst), _, _)  => begin
                      (cache, valLst) = Ceval.cevalList(cache, env, eLst, true, msg, numIter)
                      valLst = ListUtil.map1(valLst, evalCodeTypeName, env)
                      (cache, value) = cevalInteractiveFunctions2(cache, env, name, valLst, msg)
                    (cache, value)
                  end
                end
              end
          (outCache, outValue)
        end

         #= defined in the interactive environment. =#
        function cevalInteractiveFunctions2(inCache::FCore.Cache, inEnv::FCore.Graph, inFunctionName::String, inVals::List{<:Values.Value}, msg::Absyn.Msg) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local omdev::String
                  local simflags::String
                  local s1::String
                  local s2::String
                  local s3::String
                  local str::String
                  local str1::String
                  local str2::String
                  local str3::String
                  local token::String
                  local varid::String
                  local cmd::String
                  local executable::String
                  local executable1::String
                  local encoding::String
                  local method_str::String
                  local outputFormat_str::String
                  local initfilename::String
                  local pd::String
                  local executableSuffixedExe::String
                  local sim_call::String
                  local result_file::String
                  local filename_1::String
                  local filename::String
                  local filename1::String
                  local filename2::String
                  local call::String
                  local str_1::String
                  local mp::String
                  local pathstr::String
                  local name::String
                  local cname::String
                  local errMsg::String
                  local errorStr::String
                  local title::String
                  local xLabel::String
                  local yLabel::String
                  local filename2::String
                  local varNameStr::String
                  local xml_filename::String
                  local xml_contents::String
                  local visvar_str::String
                  local pwd::String
                  local omhome::String
                  local omlib::String
                  local omcpath::String
                  local os::String
                  local platform::String
                  local usercflags::String
                  local senddata::String
                  local res::String
                  local workdir::String
                  local gcc::String
                  local confcmd::String
                  local touch_file::String
                  local uname::String
                  local filenameprefix::String
                  local compileDir::String
                  local libDir::String
                  local exeDir::String
                  local configDir::String
                  local from::String
                  local to::String
                  local gridStr::String
                  local logXStr::String
                  local logYStr::String
                  local x1Str::String
                  local x2Str::String
                  local y1Str::String
                  local y2Str::String
                  local curveWidthStr::String
                  local curveStyleStr::String
                  local legendPosition::String
                  local footer::String
                  local autoScaleStr::String
                  local scriptFile::String
                  local logFile::String
                  local simflags2::String
                  local outputFile::String
                  local systemPath::String
                  local gccVersion::String
                  local gd::String
                  local strlinearizeTime::String
                  local direction::String
                  local suffix::String
                  local simOptions::List{DAE.Exp}
                  local vals::List{Values.Value}
                  local path::Absyn.Path
                  local classpath::Absyn.Path
                  local className::Absyn.Path
                  local baseClassPath::Absyn.Path
                  local parentClass::Absyn.Path
                  local scodeP::SCode.Program
                  local sp::SCode.Program
                  local fp::Option{List{SCode.Element}}
                  local env::FCore.Graph
                  local p::Absyn.Program
                  local ip::Absyn.Program
                  local pnew::Absyn.Program
                  local newp::Absyn.Program
                  local ptot::Absyn.Program
                  local newps::List{Absyn.Program}
                  local iv::List{GlobalScript.Variable}
                  local simOpt::GlobalScript.SimulationOptions
                  local startTime::ModelicaReal
                  local stopTime::ModelicaReal
                  local tolerance::ModelicaReal
                  local reltol::ModelicaReal
                  local reltolDiffMinMax::ModelicaReal
                  local rangeDelta::ModelicaReal
                  local startTimeExp::DAE.Exp
                  local stopTimeExp::DAE.Exp
                  local toleranceExp::DAE.Exp
                  local intervalExp::DAE.Exp
                  local tp::DAE.Type
                  local ty::DAE.Type
                  local tys::List{DAE.Type}
                  local absynClass::Absyn.Class
                  local cdef::Absyn.ClassDef
                  local aexp::Absyn.Exp
                  local dae::DAE.DAElist
                  local m::Array{List{ModelicaInteger}}
                  local mt::Array{List{ModelicaInteger}}
                  local ret_val::Values.Value
                  local simValue::Values.Value
                  local value::Values.Value
                  local v::Values.Value
                  local cvar::Values.Value
                  local cvar2::Values.Value
                  local v1::Values.Value
                  local v2::Values.Value
                  local v3::Values.Value
                  local gcStatRec::Values.Value
                  local cr::Absyn.ComponentRef
                  local cr_1::Absyn.ComponentRef
                  local size::ModelicaInteger
                  local resI::ModelicaInteger
                  local i::ModelicaInteger
                  local i1::ModelicaInteger
                  local i2::ModelicaInteger
                  local i3::ModelicaInteger
                  local n::ModelicaInteger
                  local curveStyle::ModelicaInteger
                  local numberOfIntervals::ModelicaInteger
                  local status::ModelicaInteger
                  local access::ModelicaInteger
                  local is::List{ModelicaInteger}
                  local vars_1::List{String}
                  local args::List{String}
                  local strings::List{String}
                  local strs::List{String}
                  local strs1::List{String}
                  local strs2::List{String}
                  local visvars::List{String}
                  local postOptModStrings::List{String}
                  local postOptModStringsOrg::List{String}
                  local mps::List{String}
                  local files::List{String}
                  local dirs::List{String}
                  local timeTotal::ModelicaReal
                  local timeSimulation::ModelicaReal
                  local timeStamp::ModelicaReal
                  local val::ModelicaReal
                  local x1::ModelicaReal
                  local x2::ModelicaReal
                  local y1::ModelicaReal
                  local y2::ModelicaReal
                  local r::ModelicaReal
                  local r1::ModelicaReal
                  local r2::ModelicaReal
                  local linearizeTime::ModelicaReal
                  local curveWidth::ModelicaReal
                  local offset::ModelicaReal
                  local offset1::ModelicaReal
                  local offset2::ModelicaReal
                  local scaleFactor::ModelicaReal
                  local scaleFactor1::ModelicaReal
                  local scaleFactor2::ModelicaReal
                  local istmts::GlobalScript.Statements
                  local istmtss::List{GlobalScript.Statements}
                  local have_corba::Bool
                  local bval::Bool
                  local anyCode::Bool
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local externalWindow::Bool
                  local logX::Bool
                  local logY::Bool
                  local autoScale::Bool
                  local forceOMPlot::Bool
                  local gcc_res::Bool
                  local omcfound::Bool
                  local rm_res::Bool
                  local touch_res::Bool
                  local uname_res::Bool
                  local ifcpp::Bool
                  local ifmsvc::Bool
                  local sort::Bool
                  local builtin::Bool
                  local showProtected::Bool
                  local includeConstants::Bool
                  local inputConnectors::Bool
                  local outputConnectors::Bool
                  local myMergeAST::Bool
                  local includePartial::Bool
                  local qualified::Bool
                  local cache::FCore.Cache
                  local crefCName::Absyn.ComponentRef
                  local resultValues::List{Tuple{String, Values.Value}}
                  local realVals::List{ModelicaReal}
                  local deps::List{Tuple{String, List{String}}}
                  local depstransitive::List{Tuple{String, List{String}}}
                  local depstransposed::List{Tuple{String, List{String}}}
                  local depstransposedtransitive::List{Tuple{String, List{String}}}
                  local depsmyMerged::List{Tuple{String, List{String}}}
                  local depschanged::List{Tuple{String, List{String}}}
                  local codeNode::Absyn.CodeNode
                  local cvars::List{Values.Value}
                  local vals2::List{Values.Value}
                  local paths::List{Absyn.Path}
                  local nargs::List{Absyn.NamedArg}
                  local classes::List{Absyn.Class}
                  local within_::Absyn.Within
                  local defaulSimOpt::GlobalScript.SimulationOptions
                  local simSettings::SimCode.SimulationSettings
                  local dumpExtractionSteps::Bool
                  local requireExactVersion::Bool
                  local uses::List{Tuple{Absyn.Path, List{String}}}
                  local oldLanguageStd::Config.LanguageStandard
                  local cl::SCode.Element
                  local cls::List{SCode.Element}
                  local elts::List{SCode.Element}
                  local names::List{String}
                  local namesPublic::List{String}
                  local namesProtected::List{String}
                  local namesChanged::List{String}
                  local fileNames::List{String}
                  local hashSetString::HashSetString.HashSet
                  local blst::List{Bool}
                  local messages::List{Error.TotalMessage}
                  local stoptime::ModelicaReal
                  local starttime::ModelicaReal
                  local tol::ModelicaReal
                  local stepsize::ModelicaReal
                  local interval::ModelicaReal
                  local stoptime_str::String
                  local stepsize_str::String
                  local starttime_str::String
                  local tol_str::String
                  local num_intervalls_str::String
                  local description::String
                  local prefix::String
                  local interfaceType::List{String}
                  local interfaceTypeAssoc::List{Tuple{String, List{String}}}
                  local encflag::SCode.Encapsulated
                  local restr::SCode.Restriction
                  local valsLst::List{List{Values.Value}}
                  local new_inst::Bool
                  local interactiveSymbolTable::SymbolTable
                  local interactiveSymbolTable2::SymbolTable
                  local gcStats::GC.ProfStats
                  local restriction::Absyn.Restriction
                @matchcontinue (inCache, inEnv, inFunctionName, inVals, msg) begin
                  (cache, _, "parseString", Values.STRING(str1) <| Values.STRING(str2) <|  nil(), _)  => begin
                      @match Absyn.PROGRAM(classes = classes, within_ = within_) = Parser.parsestring(str1, str2)
                      paths = ListUtil.map(classes, AbsynUtil.className)
                      paths = ListUtil.map1r(paths, AbsynUtil.joinWithinPath, within_)
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "parseString", _, _)  => begin
                    (cache, ValuesUtil.makeArray(nil))
                  end
                  
                  (cache, _, "parseFile", Values.STRING(str1) <| Values.STRING(encoding) <|  nil(), _)  => begin
                      Error.clearMessages() #= Clear messages =#
                      Print.clearErrorBuf() #= Clear error buffer =#
                      paths = Interactive.parseFile(str1, encoding)
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "loadFileInteractiveQualified", Values.STRING(str1) <| Values.STRING(encoding) <|  nil(), _)  => begin
                      Error.clearMessages() #= Clear messages =#
                      Print.clearErrorBuf() #= Clear error buffer =#
                      paths = Interactive.parseFile(str1, encoding, updateProgram = true)
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "loadFileInteractive", Values.STRING(str1) <| Values.STRING(encoding) <|  nil(), _)  => begin
                      pnew = loadFile(str1, encoding, SymbolTable.getAbsyn(), false) #= System.regularFileExists(name) => 0 &    Parser.parse(name) => p1 & =#
                      vals = ListUtil.map(Interactive.getTopClassnames(pnew), ValuesUtil.makeCodeTypeName)
                      SymbolTable.setAbsyn(pnew)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "getSourceFile", Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      str = Interactive.getSourceFile(path, SymbolTable.getAbsyn())
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setSourceFile", Values.CODE(Absyn.C_TYPENAME(path)) <| Values.STRING(str) <|  nil(), _)  => begin
                      @match Values.ENUM_LITERAL(index = access) = Interactive.checkAccessAnnotationAndEncryption(path, SymbolTable.getAbsyn())
                      if access >= 9
                        (b, p) = Interactive.setSourceFile(path, str, SymbolTable.getAbsyn())
                        SymbolTable.setAbsyn(p)
                      else
                        Error.addMessage(Error.SAVE_ENCRYPTED_CLASS_ERROR, nil)
                        b = false
                      end
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "basename", Values.STRING(str) <|  nil(), _)  => begin
                      str = System.basename(str)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "dirname", Values.STRING(str) <|  nil(), _)  => begin
                      str = System.dirname(str)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "codeToString", Values.CODE(codeNode) <|  nil(), _)  => begin
                      str = Dump.printCodeStr(codeNode)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "typeOf", Values.CODE(Absyn.C_VARIABLENAME(Absyn.CREF_IDENT(name = varid))) <|  nil(), _)  => begin
                      tp = Interactive.getTypeOfVariable(varid, SymbolTable.getVars())
                      str = Types.unparseType(tp)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "GC_gcollect_and_unmap",  nil(), _)  => begin
                      GC.gcollectAndUnmap()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "GC_expand_hp", Values.INTEGER(i) <|  nil(), _)  => begin
                      b = GC.expandHeap(i)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "GC_set_max_heap_size", Values.INTEGER(i) <|  nil(), _)  => begin
                      GC.setMaxHeapSize(i)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "GC_get_prof_stats",  nil(), _)  => begin
                      gcStats = GC.getProfStats()
                      gcStatRec = begin
                        @match gcStats begin
                          GC.PROFSTATS(__)  => begin
                            Values.RECORD(Absyn.IDENT("GC_PROFSTATS"), list(Values.INTEGER(gcStats.heapsize_full), Values.INTEGER(gcStats.free_bytes_full), Values.INTEGER(gcStats.unmapped_bytes), Values.INTEGER(gcStats.bytes_allocd_since_gc), Values.INTEGER(gcStats.allocd_bytes_before_gc), Values.INTEGER(gcStats.bytes_allocd_since_gc + gcStats.allocd_bytes_before_gc), Values.INTEGER(gcStats.non_gc_bytes), Values.INTEGER(gcStats.gc_no), Values.INTEGER(gcStats.markers_m1), Values.INTEGER(gcStats.bytes_reclaimed_since_gc), Values.INTEGER(gcStats.reclaimed_bytes_before_gc)), list("heapsize_full", "free_bytes_full", "unmapped_bytes: ", "bytes_allocd_since_gc", "allocd_bytes_before_gc", "total_allocd_bytes", "non_gc_bytes", "gc_no", "markers_m1", "bytes_reclaimed_since_gc", "reclaimed_bytes_before_gc"), -1)
                          end
                        end
                      end
                    (cache, gcStatRec)
                  end
                  
                  (cache, _, "clear",  nil(), _)  => begin
                      SymbolTable.reset()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "clearProgram",  nil(), _)  => begin
                      SymbolTable.clearProgram()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "clearVariables",  nil(), _)  => begin
                      SymbolTable.setVars(nil)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "list", _, _)  => begin
                      p = SymbolTable.getAbsyn()
                      @match true = Interactive.astContainsEncryptedClass(p)
                      Error.addMessage(Error.ACCESS_ENCRYPTED_PROTECTED_CONTENTS, nil)
                    (cache, Values.STRING(""))
                  end
                  
                  (cache, _, "list", Values.CODE(Absyn.C_TYPENAME(Absyn.IDENT("AllLoadedClasses"))) <| Values.BOOL(false) <| Values.BOOL(false) <| Values.ENUM_LITERAL(name = path) <|  nil(), _)  => begin
                      name = AbsynUtil.pathLastIdent(path)
                      str = begin
                        @match name begin
                          "Absyn"  => begin
                            Dump.unparseStr(SymbolTable.getAbsyn(), false)
                          end
                          
                          "SCode"  => begin
                            SCodeDump.programStr(SymbolTable.getSCode())
                          end
                          
                          "MetaModelicaInterface"  => begin
                            SCodeDump.programStr(SymbolTable.getSCode(), SCodeDump.OPTIONS(true, false, true, true, true, true, true, true, true))
                          end
                          
                          "Internal"  => begin
                            System.anyStringCode(SymbolTable.getAbsyn())
                          end
                          
                          _  => begin
                              ""
                          end
                        end
                      end
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "list", Values.CODE(Absyn.C_TYPENAME(className)) <| Values.BOOL(b1) <| Values.BOOL(b2) <| Values.ENUM_LITERAL(name = path) <|  nil(), _)  => begin
                      @match false = valueEq(Absyn.IDENT("AllLoadedClasses"), className)
                      name = AbsynUtil.pathLastIdent(path)
                      p = SymbolTable.getAbsyn()
                      scodeP = SymbolTable.getSCode()
                      absynClass = Interactive.getPathedClassInProgram(className, p)
                      absynClass = if b1
                            AbsynUtil.getFunctionInterface(absynClass)
                          else
                            absynClass
                          end
                      absynClass = if b2
                            AbsynUtil.getShortClass(absynClass)
                          else
                            absynClass
                          end
                      p = Absyn.PROGRAM(list(absynClass), Absyn.TOP())
                      cl = FBuiltin.getElementWithPathCheckBuiltin(scodeP, className)
                      str = begin
                        @match name begin
                          "Absyn"  => begin
                            Dump.unparseStr(p, false)
                          end
                          
                          "SCode"  => begin
                            SCodeDump.unparseElementStr(cl)
                          end
                          
                          "MetaModelicaInterface"  => begin
                            SCodeDump.unparseElementStr(cl, SCodeDump.OPTIONS(true, false, true, true, true, true, true, true, true))
                          end
                          
                          "Internal"  => begin
                            System.anyStringCode(p)
                          end
                          
                          _  => begin
                              ""
                          end
                        end
                      end
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "list", _, _)  => begin
                    (cache, Values.STRING(""))
                  end
                  
                  (cache, _, "listFile", Values.CODE(Absyn.C_TYPENAME(className)) <| Values.BOOL(b) <|  nil(), _)  => begin
                      path = begin
                        @match className begin
                          Absyn.FULLYQUALIFIED(__)  => begin
                            className.path
                          end
                          
                          _  => begin
                              className
                          end
                        end
                      end
                      @match Values.ENUM_LITERAL(index = access) = Interactive.checkAccessAnnotationAndEncryption(path, SymbolTable.getAbsyn())
                      @match (@match Absyn.CLASS(restriction = restriction, info = SOURCEINFO(fileName = str)) = absynClass) = Interactive.getPathedClassInProgram(className, SymbolTable.getAbsyn())
                      absynClass = if b
                            absynClass
                          else
                            AbsynUtil.filterNestedClasses(absynClass)
                          end
                      if access >= 7 || access >= 5 && ! AbsynUtil.isPackageRestriction(restriction)
                        str = Dump.unparseStr(Absyn.PROGRAM(list(absynClass), begin
                          @match path begin
                            Absyn.IDENT(__)  => begin
                              Absyn.TOP()
                            end
                            
                            _  => begin
                                Absyn.WITHIN(AbsynUtil.stripLast(path))
                            end
                          end
                        end), options = Dump.DUMPOPTIONS(str))
                      else
                        Error.addMessage(Error.ACCESS_ENCRYPTED_PROTECTED_CONTENTS, nil)
                        str = ""
                      end
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "listFile", _, _)  => begin
                    (cache, Values.STRING(""))
                  end
                  
                  (cache, _, "sortStrings", Values.ARRAY(valueLst = vals) <|  nil(), _)  => begin
                      strs = ListUtil.map(vals, ValuesUtil.extractValueString)
                      strs = ListUtil.sort(strs, Util.strcmpBool)
                      v = ValuesUtil.makeArray(ListUtil.map(strs, ValuesUtil.makeString))
                    (cache, v)
                  end
                  
                  (cache, _, "listVariables",  nil(), _)  => begin
                      v = ValuesUtil.makeArray(getVariableNames(SymbolTable.getVars(), nil))
                    (cache, v)
                  end
                  
                  (cache, _, "setCompileCommand", Values.STRING(cmd) <|  nil(), _)  => begin
                      Settings.setCompileCommand(cmd)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getCompileCommand",  nil(), _)  => begin
                      res = Settings.getCompileCommand()
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "setTempDirectoryPath", Values.STRING(cmd) <|  nil(), _)  => begin
                      Settings.setTempDirectoryPath(cmd)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getTempDirectoryPath",  nil(), _)  => begin
                      res = Settings.getTempDirectoryPath()
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "setEnvironmentVar", Values.STRING(varid) <| Values.STRING(str) <|  nil(), _)  => begin
                      b = 0 == System.setEnv(varid, str, true)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "getEnvironmentVar", Values.STRING(varid) <|  nil(), _)  => begin
                      res = Util.makeValueOrDefault(System.readEnv, varid, "")
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "setInstallationDirectoryPath", Values.STRING(cmd) <|  nil(), _)  => begin
                      Settings.setInstallationDirectoryPath(cmd)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getInstallationDirectoryPath",  nil(), _)  => begin
                      res = Settings.getInstallationDirectoryPath()
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "getModelicaPath",  nil(), _)  => begin
                      res = Settings.getModelicaPath(Config.getRunningTestsuite())
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "setModelicaPath", Values.STRING(cmd) <|  nil(), _)  => begin
                      Settings.setModelicaPath(cmd)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "setModelicaPath", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "getLanguageStandard",  nil(), _)  => begin
                      res = Config.languageStandardString(Config.getLanguageStandard())
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "reopenStandardStream", Values.ENUM_LITERAL(index = i) <| Values.STRING(filename) <|  nil(), _)  => begin
                      b = System.reopenStandardStream(i - 1, filename)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "iconv", Values.STRING(str) <| Values.STRING(from) <| Values.STRING(to) <|  nil(), _)  => begin
                      str = System.iconv(str, from, to)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "getCompiler",  nil(), _)  => begin
                      str = System.getCCompiler()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setCFlags", Values.STRING(str) <|  nil(), _)  => begin
                      System.setCFlags(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getCFlags",  nil(), _)  => begin
                      str = System.getCFlags()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setCompiler", Values.STRING(str) <|  nil(), _)  => begin
                      System.setCCompiler(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getCXXCompiler",  nil(), _)  => begin
                      str = System.getCXXCompiler()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setCXXCompiler", Values.STRING(str) <|  nil(), _)  => begin
                      System.setCXXCompiler(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "setCompilerFlags", Values.STRING(str) <|  nil(), _)  => begin
                      System.setCFlags(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getLinker",  nil(), _)  => begin
                      str = System.getLinker()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setLinker", Values.STRING(str) <|  nil(), _)  => begin
                      System.setLinker(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getLinkerFlags",  nil(), _)  => begin
                      str = System.getLDFlags()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "setLinkerFlags", Values.STRING(str) <|  nil(), _)  => begin
                      System.setLDFlags(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (_, _, "setCommandLineOptions", Values.STRING(str) <|  nil(), _)  => begin
                      args = System.strtok(str, " ")
                      @match nil = Flags.readArgs(args)
                    (FCoreUtil.emptyCache(), Values.BOOL(true))
                  end
                  
                  (cache, _, "setCommandLineOptions", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "getCommandLineOptions",  nil(), _)  => begin
                    (cache, ValuesUtil.makeStringArray(Flags.unparseFlags()))
                  end
                  
                  (cache, _, "getCommandLineOptions", _, _)  => begin
                    (cache, Values.META_FAIL())
                  end
                  
                  (cache, _, "clearCommandLineOptions",  nil(), _)  => begin
                      Flags.resetDebugFlags()
                      Flags.resetConfigFlags()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "clearCommandLineOptions", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "enableNewInstantiation", _, _)  => begin
                      Flags.enableDebug(Flags.SCODE_INST)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "enableNewInstantiation", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "disableNewInstantiation", _, _)  => begin
                      Flags.disableDebug(Flags.SCODE_INST)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "disableNewInstantiation", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "clearDebugFlags", _, _)  => begin
                      Flags.resetDebugFlags()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "clearDebugFlags", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "getConfigFlagValidOptions", Values.STRING(str) <|  nil(), _)  => begin
                      (strs1, str, strs2) = Flags.getValidOptionsAndDescription(str)
                      v1 = ValuesUtil.makeArray(ListUtil.map(strs1, ValuesUtil.makeString))
                      v2 = Values.STRING(str)
                      v3 = ValuesUtil.makeArray(ListUtil.map(strs2, ValuesUtil.makeString))
                      v = Values.TUPLE(list(v1, v2, v3))
                    (cache, v)
                  end
                  
                  (cache, _, "getConfigFlagValidOptions", Values.STRING(_) <|  nil(), _)  => begin
                      v1 = ValuesUtil.makeArray(nil)
                      v2 = Values.STRING("")
                      v3 = ValuesUtil.makeArray(nil)
                      v = Values.TUPLE(list(v1, v2, v3))
                    (cache, v)
                  end
                  
                  (cache, _, "cd", Values.STRING("") <|  nil(), _)  => begin
                      str_1 = System.pwd()
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "cd", Values.STRING(str) <|  nil(), _)  => begin
                      resI = System.cd(str)
                      if ! resI == 0
                        fail()
                      end
                      str_1 = System.pwd()
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "cd", Values.STRING(str) <|  nil(), _)  => begin
                      @shouldFail @match true = System.directoryExists(str)
                      res = stringAppendList(list("Error, directory ", str, " does not exist,"))
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "mkdir", Values.STRING(str) <|  nil(), _)  => begin
                      @match true = System.directoryExists(str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "mkdir", Values.STRING(str) <|  nil(), _)  => begin
                      b = Util.createDirectoryTree(str)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "copy", Values.STRING(str1) <| Values.STRING(str2) <|  nil(), _)  => begin
                      b = System.copyFile(str1, str2)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "remove", Values.STRING(str) <|  nil(), _)  => begin
                      b = System.removeDirectory(str)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "getVersion", Values.CODE(Absyn.C_TYPENAME(Absyn.IDENT("OpenModelica"))) <|  nil(), _)  => begin
                      str_1 = Settings.getVersionNr()
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "getVersion", Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      str_1 = getPackageVersion(path, SymbolTable.getAbsyn())
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "getTempDirectoryPath",  nil(), _)  => begin
                      str_1 = Settings.getTempDirectoryPath()
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "system", Values.STRING(str) <| Values.STRING(filename) <|  nil(), _)  => begin
                      resI = System.systemCall(str, filename)
                    (cache, Values.INTEGER(resI))
                  end
                  
                  (cache, _, "system_parallel", Values.ARRAY(valueLst = vals) <| Values.INTEGER(i) <|  nil(), _)  => begin
                      strs = ListUtil.map(vals, ValuesUtil.extractValueString)
                      v = ValuesUtil.makeIntArray(System.systemCallParallel(strs, i))
                    (cache, v)
                  end
                  
                  (cache, _, "timerClear", Values.INTEGER(i) <|  nil(), _)  => begin
                      System.realtimeClear(i)
                    (cache, Values.NORETCALL())
                  end
                  
                  (cache, _, "timerTick", Values.INTEGER(i) <|  nil(), _)  => begin
                      System.realtimeTick(i)
                    (cache, Values.NORETCALL())
                  end
                  
                  (cache, _, "timerTock", Values.INTEGER(i) <|  nil(), _)  => begin
                      @match true = System.realtimeNtick(i) > 0
                      r = System.realtimeTock(i)
                    (cache, Values.REAL(r))
                  end
                  
                  (cache, _, "timerTock", _, _)  => begin
                    (cache, Values.REAL(-1.0))
                  end
                  
                  (cache, _, "readFile", Values.STRING(str) <|  nil(), _)  => begin
                      str_1 = System.readFile(str)
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "readFile", _, _)  => begin
                    (cache, Values.STRING(""))
                  end
                  
                  (cache, _, "writeFile", Values.STRING(str) <| Values.STRING(str1) <| Values.BOOL(false) <|  nil(), _)  => begin
                      System.writeFile(str, str1)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "writeFile", Values.STRING(str) <| Values.STRING(str1) <| Values.BOOL(true) <|  nil(), _)  => begin
                      System.appendFile(str, str1)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "writeFile", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "deleteFile", Values.STRING(str) <|  nil(), _)  => begin
                      b = if System.removeFile(str) == 0
                            true
                          else
                            false
                          end
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "compareFiles", Values.STRING(str1) <| Values.STRING(str2) <|  nil(), _)  => begin
                      b = System.fileContentsEqual(str1, str2)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "compareFilesAndMove", Values.STRING(str1) <| Values.STRING(str2) <|  nil(), _)  => begin
                      @match true = System.regularFileExists(str1)
                      b = System.regularFileExists(str2) && System.fileContentsEqual(str1, str2)
                      b = if ! b
                            System.rename(str1, str2)
                          else
                            b
                          end
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "compareFilesAndMove", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "readFileNoNumeric", Values.STRING(str) <|  nil(), _)  => begin
                      str_1 = System.readFileNoNumeric(str)
                    (cache, Values.STRING(str_1))
                  end
                  
                  (cache, _, "getErrorString", Values.BOOL(b) <|  nil(), _)  => begin
                      str = Error.printMessagesStr(b)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "countMessages", _, _)  => begin
                      i1 = Error.getNumMessages()
                      i2 = Error.getNumErrorMessages()
                      i3 = ErrorExt.getNumWarningMessages()
                    (cache, Values.TUPLE(list(Values.INTEGER(i1), Values.INTEGER(i2), Values.INTEGER(i3))))
                  end
                  
                  (cache, _, "clearMessages",  nil(), _)  => begin
                      Error.clearMessages()
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "getMessagesStringInternal", Values.BOOL(true) <|  nil(), _)  => begin
                      messages = ListUtil.unique(Error.getMessages())
                      v = ValuesUtil.makeArray(ListUtil.map(messages, errorToValue))
                    (cache, v)
                  end
                  
                  (cache, _, "getMessagesStringInternal", Values.BOOL(false) <|  nil(), _)  => begin
                      v = ValuesUtil.makeArray(ListUtil.map(Error.getMessages(), errorToValue))
                    (cache, v)
                  end
                  
                  (cache, _, "stringTypeName", Values.STRING(str) <|  nil(), _)  => begin
                      path = Parser.stringPath(str)
                    (cache, Values.CODE(Absyn.C_TYPENAME(path)))
                  end
                  
                  (cache, _, "stringVariableName", Values.STRING(str) <|  nil(), _)  => begin
                      cr = Parser.stringCref(str)
                    (cache, Values.CODE(Absyn.C_VARIABLENAME(cr)))
                  end
                  
                  (cache, _, "typeNameString", Values.CODE(A = Absyn.C_TYPENAME(path = path)) <|  nil(), _)  => begin
                      str = AbsynUtil.pathString(path)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "typeNameStrings", Values.CODE(A = Absyn.C_TYPENAME(path = path)) <|  nil(), _)  => begin
                      v = ValuesUtil.makeArray(ListUtil.map(AbsynUtil.pathToStringList(path), ValuesUtil.makeString))
                    (cache, v)
                  end
                  
                  (cache, _, "generateHeader", Values.STRING(filename) <|  nil(), _)  => begin
                      str = Tpl.tplString(Unparsing.programExternalHeader, SymbolTable.getSCode())
                      System.writeFile(filename, str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "generateHeader", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "generateJuliaHeader", Values.STRING(filename) <|  nil(), _)  => begin
                      str = Tpl.tplString(Unparsing.programExternalHeaderJulia, SymbolTable.getSCode())
                      System.writeFile(filename, str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "generateJuliaHeader", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, env, "generateCode", Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      @match (cache, Util.SUCCESS()) = Static.instantiateDaeFunction(cache, env, path, false, NONE(), true)
                      (cache, _, _) = cevalGenerateFunction(cache, env, SymbolTable.getAbsyn(), path)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "generateCode", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, env, "generateScriptingAPI", Values.CODE(Absyn.C_TYPENAME(className)) <| Values.STRING(name) <|  nil(), _)  => begin
                       #=  cmd = Util.rawStringToInputString(cmd);
                       =#
                       #=  cmd = Util.rawStringToInputString(cmd);
                       =#
                       #=  cmd = Util.rawStringToInputString(cmd);
                       =#
                       #=  cmd = Util.rawStringToInputString(cmd);
                       =#
                      scodeP = SymbolTable.getSCode()
                      elts = begin
                        @match FBuiltin.getElementWithPathCheckBuiltin(scodeP, className) begin
                          SCode.CLASS(classDef = SCode.PARTS(elementLst = elts))  => begin
                            elts
                          end
                          
                          cl  => begin
                              Error.addSourceMessage(Error.INTERNAL_ERROR, list(AbsynUtil.pathString(className) + " does not contain SCode.PARTS"), SCodeUtil.elementInfo(cl))
                            fail()
                          end
                        end
                      end
                      tys = nil
                      for elt in elts
                        _ = begin
                          @matchcontinue elt begin
                            SCode.CLASS(partialPrefix = SCode.NOT_PARTIAL(__), restriction = SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(__)))  => begin
                                (cache, ty, _) = Lookup.lookupType(cache, env, AbsynUtil.suffixPath(className, elt.name), NONE())
                                 #= /*SOME(elt.info)*/ =#
                                if isSimpleAPIFunction(ty)
                                  tys = _cons(ty, tys)
                                end
                              ()
                            end
                            
                            _  => begin
                                ()
                            end
                          end
                        end
                      end
                      s1 = Tpl.tplString(GenerateAPIFunctionsTpl.getCevalScriptInterface, tys)
                      s2 = Tpl.tplString3(GenerateAPIFunctionsTpl.getQtInterface, tys, name + "::", name)
                      s3 = Tpl.tplString2(GenerateAPIFunctionsTpl.getQtInterfaceHeaders, tys, name)
                    (cache, Values.TUPLE(list(Values.BOOL(true), Values.STRING(s1), Values.STRING(s2), Values.STRING(s3))))
                  end
                  
                  (cache, _, "generateScriptingAPI", _, _)  => begin
                    (cache, Values.TUPLE(list(Values.BOOL(false), Values.STRING(""), Values.STRING(""))))
                  end
                  
                  (cache, _, "generateEntryPoint", Values.STRING(filename) <| Values.CODE(Absyn.C_TYPENAME(path)) <| Values.STRING(str) <|  nil(), _)  => begin
                      str = Tpl.tplString2(CodegenCFunctions.generateEntryPoint, path, str)
                      System.writeFile(filename, str)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "generateEntryPoint", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "checkInterfaceOfPackages", Values.CODE(Absyn.C_TYPENAME(path)) <| Values.ARRAY(valueLst = vals) <|  nil(), _)  => begin
                      sp = SymbolTable.getSCode()
                      cl = SCodeUtil.getElementWithPath(sp, path)
                      interfaceTypeAssoc = ListUtil.map1(vals, getInterfaceTypeAssocElt, SCodeUtil.elementInfo(cl))
                      interfaceType = getInterfaceType(cl, interfaceTypeAssoc)
                      ListUtil.map1_0(sp, verifyInterfaceType, interfaceType)
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "checkInterfaceOfPackages", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "generateSeparateCodeDependenciesMakefile", Values.STRING(filename) <| Values.STRING(prefix) <| Values.STRING(suffix) <|  nil(), _)  => begin
                      sp = SymbolTable.getSCode()
                      names = ListUtil.filterMap(sp, SCodeUtil.getElementName)
                      deps = Graph.buildGraph(names, buildDependencyGraphPublicImports, sp)
                      strs = ListUtil.map3(sp, writeModuleDepends, prefix, suffix, deps)
                      System.writeFile(filename, stringDelimitList(strs, "\\n"))
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "generateSeparateCodeDependenciesMakefile", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "generateSeparateCodeDependencies", Values.STRING(suffix) <|  nil(), _)  => begin
                      sp = SymbolTable.getSCode()
                      names = ListUtil.filterMap(sp, SCodeUtil.getElementName)
                      deps = Graph.buildGraph(names, buildDependencyGraph, sp)
                      namesPublic = ListUtil.map(ListUtil.select(sp, containsPublicInterface), SCodeUtil.getElementName)
                      namesChanged = ListUtil.filterMap1(sp, getChangedClass, suffix)
                      hashSetString = HashSetString.emptyHashSet()
                      hashSetString = ListUtil.fold(namesChanged, BaseHashSet.add, hashSetString)
                      depstransposed = Graph.transposeGraph(Graph.emptyGraph(names), deps, stringEq)
                      depstransposedtransitive = Graph.buildGraph(namesPublic, buildTransitiveDependencyGraph, depstransposed)
                      depstransitive = Graph.transposeGraph(Graph.emptyGraph(names), depstransposedtransitive, stringEq)
                      depstransitive = ListUtil.sort(depstransitive, compareNumberOfDependencies)
                      depsmyMerged = Graph.myMerge(deps, depstransitive, stringEq, compareDependencyNode)
                      depschanged = ListUtil.select1(depsmyMerged, isChanged, hashSetString)
                      names = ListUtil.map(depschanged, Util.tuple21)
                      fileNames = ListUtil.map1(names, stringAppend, suffix)
                      _ = ListUtil.map(fileNames, System.removeFile)
                      v = ValuesUtil.makeArray(ListUtil.map(names, ValuesUtil.makeString))
                    (cache, v)
                  end
                  
                  (cache, _, "generateSeparateCodeDependencies", _, _)  => begin
                    (cache, Values.META_FAIL())
                  end
                  
                  (cache, env, "generateSeparateCode", v <| Values.BOOL(b) <|  nil(), _)  => begin
                      p = SymbolTable.getAbsyn()
                      sp = SymbolTable.getSCode()
                      name = getTypeNameIdent(v)
                      setGlobalRoot(Global.instOnlyForcedFunctions, SOME(true))
                      cl = ListUtil.getMemberOnTrue(name, sp, SCodeUtil.isClassNamed)
                      (cache, env) = generateFunctions(cache, env, p, sp, list(cl), b)
                      setGlobalRoot(Global.instOnlyForcedFunctions, NONE())
                    (cache, Values.BOOL(true))
                  end
                  
                  (_, _, "generateSeparateCode", v <| Values.BOOL(_) <|  nil(), _)  => begin
                      sp = SymbolTable.getSCode()
                      name = getTypeNameIdent(v)
                      @shouldFail _ = ListUtil.getMemberOnTrue(name, sp, SCodeUtil.isClassNamed)
                      Error.addMessage(Error.LOOKUP_ERROR, list(name, "<TOP>"))
                    fail()
                  end
                  
                  (cache, _, "generateSeparateCode", _, _)  => begin
                      setGlobalRoot(Global.instOnlyForcedFunctions, NONE())
                    (cache, Values.BOOL(false))
                  end
                  
                  (_, _, "loadModel", Values.CODE(Absyn.C_TYPENAME(path)) <| Values.ARRAY(valueLst = cvars) <| Values.BOOL(b) <| Values.STRING(str) <| Values.BOOL(requireExactVersion) <|  nil(), _)  => begin
                      p = SymbolTable.getAbsyn()
                      execStatReset()
                      mp = Settings.getModelicaPath(Config.getRunningTestsuite())
                      strings = ListUtil.map(cvars, ValuesUtil.extractValueString)
                      oldLanguageStd = Config.getLanguageStandard()
                      b1 = ! stringEq(str, "")
                      if b1
                        Config.setLanguageStandard(Config.versionStringToStd(str))
                      end
                      (p, b) = loadModel(list((path, strings, false)), mp, p, true, b, true, requireExactVersion, false)
                      if b1
                        Config.setLanguageStandard(oldLanguageStd)
                      end
                      Print.clearBuf()
                      SymbolTable.setAbsyn(p)
                      execStat("loadModel(" + AbsynUtil.pathString(path) + ")")
                    (FCoreUtil.emptyCache(), Values.BOOL(b))
                  end
                  
                  (cache, _, "loadModel", Values.CODE(Absyn.C_TYPENAME(path)) <| _, _)  => begin
                      pathstr = AbsynUtil.pathString(path)
                      Error.addMessage(Error.LOAD_MODEL_ERROR, list(pathstr))
                    (cache, Values.BOOL(false))
                  end
                  
                  (_, _, "loadFile", Values.STRING(name) <| Values.STRING(encoding) <| Values.BOOL(b) <| _, _)  => begin
                      execStatReset()
                      name = Util.testsuiteFriendlyPath(name)
                      newp = loadFile(name, encoding, SymbolTable.getAbsyn(), b)
                      execStat("loadFile(" + name + ")")
                      SymbolTable.setAbsyn(newp)
                    (FCoreUtil.emptyCache(), Values.BOOL(true))
                  end
                  
                  (cache, _, "loadFile", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (_, _, "loadFiles", Values.ARRAY(valueLst = vals) <| Values.STRING(encoding) <| Values.INTEGER(i) <| _, _)  => begin
                      strs = ListUtil.mapMap(vals, ValuesUtil.extractValueString, Util.testsuiteFriendlyPath)
                      newps = Parser.parallelParseFilesToProgramList(strs, encoding, numThreads = i)
                      newp = ListUtil.fold(newps, (false, Settings.getModelicaPath(Config.getRunningTestsuite(__))) -> checkUsesAndUpdateProgram(checkUses = false, modelicaPath = Settings.getModelicaPath(Config.getRunningTestsuite())), SymbolTable.getAbsyn())
                      SymbolTable.setAbsyn(newp)
                    (FCoreUtil.emptyCache(), Values.BOOL(true))
                  end
                  
                  (cache, _, "loadFiles", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "parseEncryptedPackage", Values.STRING(filename) <| Values.STRING(workdir) <| _, _)  => begin
                      if System.regularFileExists(filename)
                        if Util.endsWith(filename, ".mol")
                          workdir = if System.directoryExists(workdir)
                                workdir
                              else
                                System.pwd()
                              end
                          if 0 == System.systemCall("unzip -q -o -d \\" + workdir + "\\ \\" + filename + "\\")
                            s1 = System.basename(filename)
                            s2 = Util.removeLast4Char(s1)
                            filename1 = workdir + "/" + s2 + "/" + s2 + ".moc"
                            filename2 = workdir + "/" + s2 + "/package.moc"
                            filename_1 = if System.regularFileExists(filename1)
                                  filename1
                                else
                                  filename2
                                end
                            str1 = workdir + "/" + s2 + "/" + s2 + ".mo"
                            str2 = workdir + "/" + s2 + "/package.mo"
                            str = if System.regularFileExists(str1)
                                  str1
                                else
                                  str2
                                end
                            filename_1 = if System.regularFileExists(filename_1)
                                  filename_1
                                else
                                  str
                                end
                            if System.regularFileExists(filename_1)
                              Error.clearMessages() #= Clear messages =#
                              Print.clearErrorBuf() #= Clear error buffer =#
                              filename_1 = Util.testsuiteFriendlyPath(filename_1)
                              paths = Interactive.parseFile(filename_1, "UTF-8")
                              vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                            else
                              Error.addMessage(Error.ENCRYPTED_FILE_NOT_FOUND_ERROR, list(filename1, filename2))
                            end
                          else
                            Error.addMessage(Error.UNABLE_TO_UNZIP_FILE, list(filename))
                          end
                        else
                          Error.addMessage(Error.EXPECTED_ENCRYPTED_PACKAGE, list(filename))
                        end
                      else
                        Error.addMessage(Error.FILE_NOT_FOUND_ERROR, list(filename))
                      end
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (_, _, "loadEncryptedPackage", Values.STRING(filename) <| Values.STRING(workdir) <| _, _)  => begin
                      b = false
                      if System.regularFileExists(filename)
                        if Util.endsWith(filename, ".mol")
                          workdir = if System.directoryExists(workdir)
                                workdir
                              else
                                System.pwd()
                              end
                          b = false
                          if 0 == System.systemCall("unzip -q -o -d \\" + workdir + "\\ \\" + filename + "\\")
                            b = true
                            s1 = System.basename(filename)
                            s2 = Util.removeLast4Char(s1)
                            filename1 = workdir + "/" + s2 + ".moc"
                            filename2 = workdir + "/" + s2 + "/package.moc"
                            filename_1 = if System.regularFileExists(filename1)
                                  filename1
                                else
                                  filename2
                                end
                            str1 = workdir + "/" + s2 + ".mo"
                            str2 = workdir + "/" + s2 + "/package.mo"
                            str = if System.regularFileExists(str1)
                                  str1
                                else
                                  str2
                                end
                            filename_1 = if System.regularFileExists(filename_1)
                                  filename_1
                                else
                                  str
                                end
                            if System.regularFileExists(filename_1)
                              execStatReset()
                              filename_1 = Util.testsuiteFriendlyPath(filename_1)
                              p = SymbolTable.getAbsyn()
                              newp = loadFile(filename_1, "UTF-8", p, true)
                              execStat("loadFile(" + filename_1 + ")")
                              SymbolTable.setAbsyn(newp)
                            else
                              Error.addMessage(Error.ENCRYPTED_FILE_NOT_FOUND_ERROR, list(filename1, filename2))
                            end
                          else
                            Error.addMessage(Error.UNABLE_TO_UNZIP_FILE, list(filename))
                          end
                        else
                          Error.addMessage(Error.EXPECTED_ENCRYPTED_PACKAGE, list(filename))
                        end
                      else
                        Error.addMessage(Error.FILE_NOT_FOUND_ERROR, list(filename))
                      end
                    (FCoreUtil.emptyCache(), Values.BOOL(b))
                  end
                  
                  (cache, _, "loadEncryptedPackage", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "alarm", Values.INTEGER(i) <|  nil(), _)  => begin
                      i = System.alarm(i)
                    (cache, Values.INTEGER(i))
                  end
                  
                  (cache, _, "getClassNames", Values.CODE(Absyn.C_TYPENAME(Absyn.IDENT("AllLoadedClasses"))) <| Values.BOOL(false) <| _ <| Values.BOOL(sort) <| Values.BOOL(builtin) <| Values.BOOL(_) <| _ <|  nil(), _)  => begin
                      (ip, _) = FBuiltin.getInitialFunctions()
                      p = SymbolTable.getAbsyn()
                      p = if builtin
                            Interactive.updateProgram(p, ip)
                          else
                            p
                          end
                      paths = Interactive.getTopClassnames(p)
                      paths = if sort
                            ListUtil.sort(paths, AbsynUtil.pathGe)
                          else
                            paths
                          end
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "getClassNames", Values.CODE(Absyn.C_TYPENAME(path)) <| Values.BOOL(false) <| Values.BOOL(b) <| Values.BOOL(sort) <| Values.BOOL(builtin) <| Values.BOOL(showProtected) <| Values.BOOL(includeConstants) <|  nil(), _)  => begin
                      (ip, _) = FBuiltin.getInitialFunctions()
                      p = SymbolTable.getAbsyn()
                      p = if builtin
                            Interactive.updateProgram(p, ip)
                          else
                            p
                          end
                      paths = Interactive.getClassnamesInPath(path, p, showProtected, includeConstants)
                      paths = if b
                            ListUtil.map1r(paths, AbsynUtil.joinPaths, path)
                          else
                            paths
                          end
                      paths = if sort
                            ListUtil.sort(paths, AbsynUtil.pathGe)
                          else
                            paths
                          end
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "getClassNames", Values.CODE(Absyn.C_TYPENAME(Absyn.IDENT("AllLoadedClasses"))) <| Values.BOOL(true) <| _ <| Values.BOOL(sort) <| Values.BOOL(builtin) <| Values.BOOL(showProtected) <| Values.BOOL(includeConstants) <|  nil(), _)  => begin
                      (ip, _) = FBuiltin.getInitialFunctions()
                      p = SymbolTable.getAbsyn()
                      p = if builtin
                            Interactive.updateProgram(p, ip)
                          else
                            p
                          end
                      (_, paths) = Interactive.getClassNamesRecursive(NONE(), p, showProtected, includeConstants, nil)
                      paths = listReverse(paths)
                      paths = if sort
                            ListUtil.sort(paths, AbsynUtil.pathGe)
                          else
                            paths
                          end
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "getClassNames", Values.CODE(Absyn.C_TYPENAME(path)) <| Values.BOOL(true) <| _ <| Values.BOOL(sort) <| Values.BOOL(builtin) <| Values.BOOL(showProtected) <| Values.BOOL(includeConstants) <|  nil(), _)  => begin
                      (ip, _) = FBuiltin.getInitialFunctions()
                      p = SymbolTable.getAbsyn()
                      p = if builtin
                            Interactive.updateProgram(p, ip)
                          else
                            p
                          end
                      (_, paths) = Interactive.getClassNamesRecursive(SOME(path), p, showProtected, includeConstants, nil)
                      paths = listReverse(paths)
                      paths = if sort
                            ListUtil.sort(paths, AbsynUtil.pathGe)
                          else
                            paths
                          end
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  (cache, _, "reloadClass", Values.CODE(Absyn.C_TYPENAME(classpath)) <| Values.STRING(encoding) <|  nil(), _)  => begin
                      @match Absyn.CLASS(info = SOURCEINFO(fileName = filename, lastModification = r2)) = Interactive.getPathedClassInProgram(classpath, SymbolTable.getAbsyn())
                      @match (true, _, r1) = System.stat(filename)
                      b = realEq(r1, r2)
                      if ! b
                        reloadClass(filename, encoding)
                      end
                    (cache, Values.BOOL(true))
                  end
                  
                  (cache, _, "reloadClass", Values.CODE(Absyn.C_TYPENAME(classpath)) <| _ <|  nil(), _)  => begin
                      @shouldFail _ = Interactive.getPathedClassInProgram(classpath, SymbolTable.getAbsyn())
                      str = AbsynUtil.pathString(classpath)
                      Error.addMessage(Error.LOAD_MODEL_ERROR, list(str))
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "reloadClass", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (_, _, "loadString", Values.STRING(str) <| Values.STRING(name) <| Values.STRING(encoding) <| Values.BOOL(myMergeAST) <| _, _)  => begin
                      str = if ! encoding == "UTF-8"
                            System.iconv(str, encoding, "UTF-8")
                          else
                            str
                          end
                      newp = Parser.parsestring(str, name)
                      newp = Interactive.updateProgram(newp, SymbolTable.getAbsyn(), myMergeAST)
                      SymbolTable.setAbsyn(newp)
                    (FCoreUtil.emptyCache(), Values.BOOL(true))
                  end
                  
                  (cache, _, "loadString", _, _)  => begin
                    (cache, Values.BOOL(false))
                  end
                  
                  (cache, _, "help", Values.STRING("") <|  nil(), _)  => begin
                      str = Flags.printUsage()
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "help", Values.STRING(str) <|  nil(), _)  => begin
                      str = Flags.printHelp(list(str))
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "getTimeStamp", Values.CODE(Absyn.C_TYPENAME(classpath)) <|  nil(), _)  => begin
                      @match Absyn.CLASS(info = SOURCEINFO(lastModification = r)) = Interactive.getPathedClassInProgram(classpath, SymbolTable.getAbsyn())
                      str = System.ctime(r)
                    (cache, Values.TUPLE(list(Values.REAL(r), Values.STRING(str))))
                  end
                  
                  (cache, _, "getTimeStamp", _, _)  => begin
                    (cache, Values.TUPLE(list(Values.REAL(0.0), Values.STRING(""))))
                  end
                  
                  (cache, _, "getClassRestriction", Values.CODE(Absyn.C_TYPENAME(classpath)) <|  nil(), _)  => begin
                      str = Interactive.getClassRestriction(classpath, SymbolTable.getAbsyn())
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "classAnnotationExists", Values.CODE(Absyn.C_TYPENAME(classpath)) <| Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      b = Interactive.getNamedAnnotation(classpath, SymbolTable.getAbsyn(), path, SOME(false), isSome)
                    (cache, Values.BOOL(b))
                  end
                  
                  (cache, _, "getBooleanClassAnnotation", Values.CODE(Absyn.C_TYPENAME(classpath)) <| Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      @match Absyn.BOOL(b) = Interactive.getNamedAnnotation(classpath, SymbolTable.getAbsyn(), path, NONE(), Interactive.getAnnotationExp)
                    (cache, Values.BOOL(b))
                  end
                  
                  (_, _, "getBooleanClassAnnotation", Values.CODE(Absyn.C_TYPENAME(classpath)) <| Values.CODE(Absyn.C_TYPENAME(path)) <|  nil(), _)  => begin
                      str1 = AbsynUtil.pathString(path)
                      str2 = AbsynUtil.pathString(classpath)
                      Error.addMessage(Error.CLASS_ANNOTATION_DOES_NOT_EXIST, list(str1, str2))
                    fail()
                  end
                  
                  (cache, _, "strtok", Values.STRING(str) <| Values.STRING(token) <|  nil(), _)  => begin
                      vals = ListUtil.map(System.strtok(str, token), ValuesUtil.makeString)
                      i = listLength(vals)
                    (cache, Values.ARRAY(vals, list(i)))
                  end
                  
                  (cache, _, "stringSplit", Values.STRING(str) <| Values.STRING(token) <|  nil(), _)  => begin
                      vals = ListUtil.map(Util.stringSplitAtChar(str, token), ValuesUtil.makeString)
                      i = listLength(vals)
                    (cache, Values.ARRAY(vals, list(i)))
                  end
                  
                  (cache, _, "stringReplace", Values.STRING(str1) <| Values.STRING(str2) <| Values.STRING(str3) <|  nil(), _)  => begin
                      str = System.stringReplace(str1, str2, str3)
                    (cache, Values.STRING(str))
                  end
                  
                  (cache, _, "checkSettings",  nil(), _)  => begin
                      vars_1 = list("OPENMODELICAHOME", "OPENMODELICALIBRARY", "OMC_PATH", "SYSTEM_PATH", "OMDEV_PATH", "OMC_FOUND", "MODELICAUSERCFLAGS", "WORKING_DIRECTORY", "CREATE_FILE_WORKS", "REMOVE_FILE_WORKS", "OS", "SYSTEM_INFO", "RTLIBS", "C_COMPILER", "C_COMPILER_VERSION", "C_COMPILER_RESPONDING", "HAVE_CORBA", "CONFIGURE_CMDLINE")
                      omhome = Settings.getInstallationDirectoryPath()
                      omlib = Settings.getModelicaPath(Config.getRunningTestsuite())
                      omcpath = omhome + "/bin/omc" + Autoconf.exeExt
                      systemPath = Util.makeValueOrDefault(System.readEnv, "PATH", "")
                      omdev = Util.makeValueOrDefault(System.readEnv, "OMDEV", "")
                      omcfound = System.regularFileExists(omcpath)
                      os = Autoconf.os
                      touch_file = "omc.checksettings.create_file_test"
                      usercflags = Util.makeValueOrDefault(System.readEnv, "MODELICAUSERCFLAGS", "")
                      workdir = System.pwd()
                      touch_res = 0 == System.systemCall("touch " + touch_file, "")
                      System.systemCall("uname -a", touch_file)
                      uname = System.readFile(touch_file)
                      rm_res = 0 == System.systemCall("rm " + touch_file, "")
                      senddata = Autoconf.ldflags_runtime
                      gcc = System.getCCompiler()
                      have_corba = Corba.haveCorba()
                      System.systemCall("rm -f " + touch_file, "")
                      gcc_res = 0 == System.systemCall(gcc + " --version", touch_file)
                      gccVersion = System.readFile(touch_file)
                      System.systemCall("rm -f " + touch_file, "")
                      confcmd = Autoconf.configureCommandLine
                      vals = list(Values.STRING(omhome), Values.STRING(omlib), Values.STRING(omcpath), Values.STRING(systemPath), Values.STRING(omdev), Values.BOOL(omcfound), Values.STRING(usercflags), Values.STRING(workdir), Values.BOOL(touch_res), Values.BOOL(rm_res), Values.STRING(os), Values.STRING(uname), Values.STRING(senddata), Values.STRING(gcc), Values.STRING(gccVersion), Values.BOOL(gcc_res), Values.BOOL(have_corba), Values.STRING(confcmd))
                    (cache, Values.RECORD(Absyn.IDENT("OpenModelica.Scripting.CheckSettingsResult"), vals, vars_1, -1))
                  end
                  
                  (cache, _, "echo", v && Values.BOOL(bval) <|  nil(), _)  => begin
                      Settings.setEcho(if bval
                            1
                          else
                            0
                          end)
                    (cache, v)
                  end
                  
                  (cache, _, "numProcessors",  nil(), _)  => begin
                      i = Config.noProc()
                    (cache, Values.INTEGER(i))
                  end
                  
                  (cache, _, "runScript", Values.STRING(str) <|  nil(), _)  => begin
                      str = Util.testsuiteFriendlyPath(str)
                      istmts = Parser.parseexp(str)
                      res = Interactive.evaluate(istmts, true)
                    (cache, Values.STRING(res))
                  end
                  
                  (cache, _, "runScript", _, _)  => begin
                    (cache, Values.STRING("Failed"))
                  end
                  
                  (_, _, "exit", Values.INTEGER(i) <|  nil(), _)  => begin
                      System.exit(i)
                    fail()
                  end
                  
                  (cache, _, "getMemorySize",  nil(), _)  => begin
                      r = System.getMemorySize()
                      v = Values.REAL(r)
                    (cache, v)
                  end
                  
                  (cache, _, "getAllSubtypeOf", Values.CODE(Absyn.C_TYPENAME(parentClass)) <| Values.CODE(Absyn.C_TYPENAME(path)) <| Values.BOOL(qualified) <| Values.BOOL(includePartial) <| Values.BOOL(sort) <|  nil(), _)  => begin
                      paths = InteractiveUtil.getAllSubtypeOf(parentClass, path, SymbolTable.getAbsyn(), qualified, includePartial)
                      paths = listReverse(paths)
                      paths = if sort
                            ListUtil.sort(paths, AbsynUtil.pathGe)
                          else
                            paths
                          end
                      vals = ListUtil.map(paths, ValuesUtil.makeCodeTypeName)
                    (cache, ValuesUtil.makeArray(vals))
                  end
                  
                  _  => begin
                         #= /* Checks the installation of OpenModelica and tries to find common errors */ =#
                         #=  _ = System.platform();
                         =#
                         #= /* Cannot reach here */ =#
                        (cache, v) = CevalScriptBackend.cevalInteractiveFunctions3(inCache, inEnv, inFunctionName, inVals, msg)
                      (cache, v)
                  end
                end
              end
          (outCache, outValue)
        end

        function evalCodeTypeName(val::Values.Value, env::FCore.Graph) ::Values.Value 
              local res::Values.Value

              res = begin
                  local path::Absyn.Path
                @matchcontinue (val, env) begin
                  (Values.CODE(Absyn.C_TYPENAME(path && Absyn.IDENT(_))), _)  => begin
                      @match (_, _, _, DAE.VALBOUND(valBound = (@match Values.CODE(A = Absyn.C_TYPENAME()) = res)), _, _, _, _, _) = Lookup.lookupVar(FCoreUtil.emptyCache(), env, ComponentReference.pathToCref(path))
                    res
                  end
                  
                  _  => begin
                      val
                  end
                end
              end
               #= /* We only want to lookup idents in the symboltable; also speeds up e.g. simulate(Modelica.A.B.C) so we do not instantiate all classes */ =#
          res
        end

        function getVariableNames(vars::List{<:GlobalScript.Variable}, acc::List{<:Values.Value}) ::List{Values.Value} 
              local ovars::List{Values.Value}

              ovars = begin
                  local vs::List{GlobalScript.Variable}
                  local p::String
                @match (vars, acc) begin
                  ( nil(), _)  => begin
                    listReverse(acc)
                  end
                  
                  (GlobalScript.IVAR(varIdent = "$echo") <| vs, _)  => begin
                    getVariableNames(vs, acc)
                  end
                  
                  (GlobalScript.IVAR(varIdent = p) <| vs, _)  => begin
                    getVariableNames(vs, _cons(Values.CODE(Absyn.C_VARIABLENAME(Absyn.CREF_IDENT(p, nil))), acc))
                  end
                end
              end
          ovars
        end

        function getPackageVersion(path::Absyn.Path, p::Absyn.Program) ::String 
              local version::String = ""

              local evalParamAnn::Bool

              evalParamAnn = Config.getEvaluateParametersInAnnotations()
              Config.setEvaluateParametersInAnnotations(true)
              try
                @match Absyn.STRING(version) = Interactive.getNamedAnnotation(path, p, Absyn.IDENT("version"), SOME(Absyn.STRING("")), Interactive.getAnnotationExp)
              catch
                version = ""
              end
              Config.setEvaluateParametersInAnnotations(evalParamAnn)
          version
        end

        function errorToValue(err::Error.TotalMessage) ::Values.Value 
              local val::Values.Value

              val = begin
                  local msgpath::Absyn.Path
                  local tyVal::Values.Value
                  local severityVal::Values.Value
                  local infoVal::Values.Value
                  local values::List{Values.Value}
                  local message::Util.TranslatableContent
                  local msg_str::String
                  local id::ModelicaInteger
                  local severity::Error.Severity
                  local ty::Error.MessageType
                  local info::SourceInfo
                @match err begin
                  Error.TOTALMESSAGE(Error.MESSAGE(id, ty, severity, message), info)  => begin
                      msg_str = Util.translateContent(message)
                      msgpath = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED("OpenModelica", Absyn.QUALIFIED("Scripting", Absyn.IDENT("ErrorMessage"))))
                      tyVal = errorTypeToValue(ty)
                      severityVal = errorLevelToValue(severity)
                      infoVal = infoToValue(info)
                      values = list(infoVal, Values.STRING(msg_str), tyVal, severityVal, Values.INTEGER(id))
                    Values.RECORD(msgpath, values, list("info", "message", "kind", "level", "id"), -1)
                  end
                end
              end
          val
        end

        function infoToValue(info::SourceInfo) ::Values.Value 
              local val::Values.Value

              val = begin
                  local values::List{Values.Value}
                  local infopath::Absyn.Path
                  local ls::ModelicaInteger
                  local cs::ModelicaInteger
                  local le::ModelicaInteger
                  local ce::ModelicaInteger
                  local filename::String
                  local readonly::Bool
                @match info begin
                  SOURCEINFO(filename, readonly, ls, cs, le, ce, _)  => begin
                      infopath = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED("OpenModelica", Absyn.QUALIFIED("Scripting", Absyn.IDENT("SourceInfo"))))
                      values = list(Values.STRING(filename), Values.BOOL(readonly), Values.INTEGER(ls), Values.INTEGER(cs), Values.INTEGER(le), Values.INTEGER(ce))
                    Values.RECORD(infopath, values, list("filename", "readonly", "lineStart", "columnStart", "lineEnd", "columnEnd"), -1)
                  end
                end
              end
          val
        end

        function makeErrorEnumLiteral(enumName::String, enumField::String, index::ModelicaInteger) ::Values.Value 
              local val::Values.Value

              val = Values.ENUM_LITERAL(Absyn.FULLYQUALIFIED(Absyn.QUALIFIED("OpenModelica", Absyn.QUALIFIED("Scripting", Absyn.QUALIFIED(enumName, Absyn.IDENT(enumField))))), index)
          val
        end

        function errorTypeToValue(ty::Error.MessageType) ::Values.Value 
              local val::Values.Value

              val = begin
                @match ty begin
                  Error.SYNTAX(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "syntax", 1)
                  end
                  
                  Error.GRAMMAR(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "grammar", 2)
                  end
                  
                  Error.TRANSLATION(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "translation", 3)
                  end
                  
                  Error.SYMBOLIC(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "symbolic", 4)
                  end
                  
                  Error.SIMULATION(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "runtime", 5)
                  end
                  
                  Error.SCRIPTING(__)  => begin
                    makeErrorEnumLiteral("ErrorKind", "scripting", 6)
                  end
                  
                  _  => begin
                        print("errorTypeToValue failed\\n")
                      fail()
                  end
                end
              end
          val
        end

        function errorLevelToValue(severity::Error.Severity) ::Values.Value 
              local val::Values.Value

              val = begin
                @match severity begin
                  Error.ERROR(__)  => begin
                    makeErrorEnumLiteral("ErrorLevel", "error", 1)
                  end
                  
                  Error.WARNING(__)  => begin
                    makeErrorEnumLiteral("ErrorLevel", "warning", 2)
                  end
                  
                  Error.NOTIFICATION(__)  => begin
                    makeErrorEnumLiteral("ErrorLevel", "notification", 3)
                  end
                  
                  _  => begin
                        print("errorLevelToValue failed\\n")
                      fail()
                  end
                end
              end
          val
        end

         #= @author adrpo:
         generate the function name from a path. =#
        function generateFunctionName(functionPath::Absyn.Path) ::String 
              local functionName::String

              functionName = AbsynUtil.pathStringUnquoteReplaceDot(functionPath, "_")
          functionName
        end

         #= @author adrpo:
         generate the function name from a path. =#
        function generateFunctionFileName(functionPath::Absyn.Path) ::String 
              local functionName::String

              functionName = begin
                  local name::String
                  local n1::String
                  local n2::String
                  local len::ModelicaInteger
                @matchcontinue functionPath begin
                  _  => begin
                      name = AbsynUtil.pathStringUnquoteReplaceDot(functionPath, "_")
                      len = stringLength(name)
                      @match true = len > Global.maxFunctionFileLength
                      n1 = AbsynUtil.pathFirstIdent(functionPath)
                      n2 = AbsynUtil.pathLastIdent(functionPath)
                      name = System.unquoteIdentifier(n1 + "_" + n2)
                      name = name + "_" + intString(tick())
                    name
                  end
                  
                  _  => begin
                        name = AbsynUtil.pathStringUnquoteReplaceDot(functionPath, "_")
                      name
                  end
                end
              end
               #=  not bigger than
               =#
          functionName
        end

         #= returns all function dependencies as paths, also the main function and the function tree =#
        function getFunctionDependencies(cache::FCore.Cache, functionName::Absyn.Path) ::Tuple{DAE.Function, List{Absyn.Path}, DAE.FunctionTree} 
              local funcs::DAE.FunctionTree #= the function tree =#
              local dependencies::List{Absyn.Path} #= the dependencies as paths =#
              local mainFunction::DAE.Function #= the main function =#

              funcs = FCoreUtil.getFunctionTree(cache)
               #=  First check if the main function exists... If it does not it might be an interactive function...
               =#
              mainFunction = DAEUtil.getNamedFunction(functionName, funcs)
              dependencies = SimCodeFunction.getCalledFunctionsInFunction(functionName, funcs)
          (mainFunction #= the main function =#, dependencies #= the dependencies as paths =#, funcs #= the function tree =#)
        end

         #= collects all function dependencies, also the main function, uniontypes, metarecords =#
        function collectDependencies(inCache::FCore.Cache, env::FCore.Graph, functionName::Absyn.Path) ::Tuple{FCore.Cache, DAE.Function, List{DAE.Function}, List{DAE.Type}} 
              local metarecordTypes::List{DAE.Type}
              local dependencies::List{DAE.Function}
              local mainFunction::DAE.Function
              local outCache::FCore.Cache

              local uniontypePaths::List{Absyn.Path}
              local paths::List{Absyn.Path}
              local funcs::DAE.FunctionTree

              (mainFunction, paths, funcs) = getFunctionDependencies(inCache, functionName)
               #=  The list of functions is not ordered, so we need to filter out the main function...
               =#
              dependencies = ListUtil.map1(paths, DAEUtil.getNamedFunction, funcs)
              dependencies = ListUtil.setDifference(dependencies, list(mainFunction))
              uniontypePaths = DAEUtil.getUniontypePaths(dependencies, nil)
              (outCache, metarecordTypes) = Lookup.lookupMetarecordsRecursive(inCache, env, uniontypePaths)
          (outCache, mainFunction, dependencies, metarecordTypes)
        end

         #= Generates code for a given function name. =#
        function cevalGenerateFunction(inCache::FCore.Cache, inEnv::FCore.Graph, program::Absyn.Program, inPath::Absyn.Path) ::Tuple{FCore.Cache, String, String} 
              local functionFileName::String
              local functionName::String
              local outCache::FCore.Cache

              (outCache, functionName, functionFileName) = begin
                  local pathstr::String
                  local fileName::String
                  local env::FCore.Graph
                  local path::Absyn.Path
                  local cache::FCore.Cache
                  local mainFunction::DAE.Function
                  local d::List{DAE.Function}
                  local metarecordTypes::List{DAE.Type}
                  local funcs::DAE.FunctionTree
                   #=  template based translation
                   =#
                @matchcontinue (inCache, inEnv, program, inPath) begin
                  (cache, env, _, path)  => begin
                      @match true = Flags.isSet(Flags.GEN)
                      @match false = Flags.isSet(Flags.GENERATE_CODE_CHEAT)
                      (cache, mainFunction, d, metarecordTypes) = collectDependencies(cache, env, path)
                      pathstr = generateFunctionName(path)
                      fileName = generateFunctionFileName(path)
                      SimCodeFunction.translateFunctions(program, fileName, SOME(mainFunction), d, metarecordTypes, nil)
                      compileModel(fileName, nil)
                    (cache, pathstr, fileName)
                  end
                  
                  (cache, _, _, path)  => begin
                      @match true = Flags.isSet(Flags.GEN)
                      @match true = Flags.isSet(Flags.GENERATE_CODE_CHEAT)
                      funcs = FCoreUtil.getFunctionTree(cache)
                      pathstr = generateFunctionName(path)
                      fileName = generateFunctionFileName(path)
                      d = DAEUtil.getFunctionList(funcs)
                      SimCodeFunction.translateFunctions(program, fileName, NONE(), d, nil, nil)
                    (cache, pathstr, fileName)
                  end
                  
                  (cache, env, _, path)  => begin
                      @match true = Flags.isSet(Flags.GEN)
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      @match (cache, false) = Static.isExternalObjectFunction(cache, env, path)
                      pathstr = generateFunctionName(path)
                      fileName = generateFunctionFileName(path)
                      Debug.trace("CevalScript.cevalGenerateFunction failed:\\nfunction: " + pathstr + "\\nfile: " + fileName + "\\n")
                    fail()
                  end
                end
              end
               #=  Cheat if we want to generate code for Main.main
               =#
               #=  * Don't do dependency analysis of what functions to generate; just generate all of them
               =#
               #=  * Don't generate extra code for unreferenced MetaRecord types (for external functions)
               =#
               #=    This could be an annotation instead anyway.
               =#
               #=  * Don't compile the generated files
               =#
               #=  First check if the main function exists... If it does not it might be an interactive function...
               =#
               #=  The list of functions is not ordered, so we need to filter out the main function...
               =#
          (outCache, functionName, functionFileName)
        end

         #= Collects the packages used by the functions =#
        function matchQualifiedCalls(inExp::DAE.Exp, inAcc::List{<:String}) ::Tuple{DAE.Exp, List{String}} 
              local outAcc::List{String}
              local outExp::DAE.Exp = inExp

              outAcc = begin
                  local name::String
                @match inExp begin
                  DAE.REDUCTION(reductionInfo = DAE.REDUCTIONINFO(path = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED(name = name))))  => begin
                    ListUtil.consOnTrue(! listMember(name, inAcc), name, inAcc)
                  end
                  
                  DAE.CALL(path = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED(name = name)), attr = DAE.CALL_ATTR(builtin = false))  => begin
                    ListUtil.consOnTrue(! listMember(name, inAcc), name, inAcc)
                  end
                  
                  DAE.CREF(componentRef = DAE.CREF_QUAL(ident = name), ty = DAE.T_FUNCTION_REFERENCE_FUNC(builtin = false))  => begin
                    ListUtil.consOnTrue(! listMember(name, inAcc), name, inAcc)
                  end
                  
                  DAE.PARTEVALFUNCTION(path = Absyn.FULLYQUALIFIED(Absyn.QUALIFIED(name = name)))  => begin
                    ListUtil.consOnTrue(! listMember(name, inAcc), name, inAcc)
                  end
                  
                  _  => begin
                      inAcc
                  end
                end
              end
          (outExp, outAcc)
        end

        function instantiateDaeFunctions(icache::FCore.Cache, ienv::FCore.Graph, ipaths::List{<:Absyn.Path}) ::FCore.Cache 
              local outCache::FCore.Cache

              outCache = begin
                  local path::Absyn.Path
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local paths::List{Absyn.Path}
                @match (icache, ienv, ipaths) begin
                  (cache, _,  nil())  => begin
                    cache
                  end
                  
                  (cache, env, path <| paths)  => begin
                      @match (cache, Util.SUCCESS()) = Static.instantiateDaeFunctionForceInst(cache, env, path, false, NONE(), true)
                      cache = instantiateDaeFunctions(cache, env, paths)
                    cache
                  end
                end
              end
               #=  print(\"force inst: \" + AbsynUtil.pathString(path));
               =#
               #=  print(\" ok\\n\");
               =#
          outCache
        end

        function generateFunctions(icache::FCore.Cache, ienv::FCore.Graph, p::Absyn.Program, fullScodeProgram::SCode.Program, isp::List{<:SCode.Element}, cleanCache::Bool) ::Tuple{FCore.Cache, FCore.Graph} 
              local env::FCore.Graph
              local cache::FCore.Cache

              (cache, env) = begin
                  local name::String
                  local names::List{String}
                  local dependencies::List{String}
                  local paths::List{Absyn.Path}
                  local elementLst::List{SCode.Element}
                  local funcs::DAE.FunctionTree
                  local d::List{DAE.Function}
                  local acc::List{Tuple{String, List{String}}}
                  local sp::List{SCode.Element}
                  local file::String
                  local nameHeader::String
                  local str::String
                  local n::ModelicaInteger
                  local info::SourceInfo
                  local cl::SCode.Element
                  local restr::SCode.Restriction
                @match (icache, ienv, p, isp, cleanCache) begin
                  (cache, env, _,  nil(), _)  => begin
                    (cache, env)
                  end
                  
                  (cache, env, _, cl && SCode.CLASS(name = name, encapsulatedPrefix = SCode.ENCAPSULATED(__), restriction = restr, info = info) <| sp, _)  => begin
                      _ = begin
                        @match restr begin
                          SCode.R_PACKAGE(__)  => begin
                            ()
                          end
                          
                          SCode.R_UNIONTYPE(__)  => begin
                            ()
                          end
                          
                          _  => begin
                                Error.addSourceMessage(Error.INTERNAL_ERROR, list("Only package and uniontype is supported as top-level classes in OpenModelica."), info)
                              fail()
                          end
                        end
                      end
                      (cache, env) = generateFunctions2(cache, env, p, fullScodeProgram, cl, name, info, cleanCache)
                      (cache, env) = generateFunctions(cache, env, p, fullScodeProgram, sp, cleanCache)
                    (cache, env)
                  end
                  
                  (_, _, _, SCode.CLASS(encapsulatedPrefix = SCode.NOT_ENCAPSULATED(__), name = name, info = info && SOURCEINFO(fileName = file)) <| _, _)  => begin
                      (n, _) = System.regex(file, "ModelicaBuiltin.mo", 1, false, false)
                      Error.assertion(n > 0, "Not an encapsulated class (required for separate compilation): " + name, info)
                    fail()
                  end
                end
              end
          (cache, env)
        end

        function generateFunctions2(icache::FCore.Cache, ienv::FCore.Graph, p::Absyn.Program, sp::SCode.Program, cl::SCode.Element, name::String, info::SourceInfo, cleanCache::Bool) ::Tuple{FCore.Cache, FCore.Graph} 
              local env::FCore.Graph
              local cache::FCore.Cache

              (cache, env) = begin
                  local names::List{String}
                  local dependencies::List{String}
                  local strs::List{String}
                  local paths::List{Absyn.Path}
                  local pathsMetarecord::List{Absyn.Path}
                  local funcs::DAE.FunctionTree
                  local d::List{DAE.Function}
                  local acc::List{Tuple{String, List{String}}}
                  local file::String
                  local nameHeader::String
                  local str::String
                  local n::ModelicaInteger
                  local env2::FCore.Graph
                  local ref::FCore.MMRef
                  local lookupCache::FCore.Cache
                  local children::FCore.Children
                  local path::Absyn.Path
                  local elements::List{SCode.Element}
                  local metarecords::List{DAE.Type}
                  local t::DAE.Type
                @matchcontinue (icache, ienv, p, cl, name, info, cleanCache) begin
                  (cache, env, _, _, _, SOURCEINFO(fileName = file), _)  => begin
                      @match (1, _) = System.regex(file, "ModelicaBuiltin.mo", 1, false, false)
                    (cache, env)
                  end
                  
                  (cache, env, _, _, _, _, _)  => begin
                      cache = if cleanCache
                            FCoreUtil.emptyCache()
                          else
                            cache
                          end
                      if SCodeUtil.isPartial(cl)
                        paths = nil
                        pathsMetarecord = nil
                      else
                        path = Absyn.FULLYQUALIFIED(Absyn.IDENT(name))
                        elements = getNonPartialElementsForInstantiatedClass(sp, cl, path)
                        (paths, pathsMetarecord) = ListUtil.fold22(elements, findFunctionsToCompile, path, sp, nil, nil)
                      end
                      metarecords = nil
                      for mr in pathsMetarecord
                        (cache, t) = Lookup.lookupType(cache, env, mr, SOME(info))
                        metarecords = _cons(t, metarecords)
                      end
                      cache = instantiateDaeFunctions(cache, env, paths)
                      funcs = FCoreUtil.getFunctionTree(cache)
                      d = ListUtil.map2(paths, DAEUtil.getNamedFunctionWithError, funcs, info)
                      (_, (_, dependencies)) = DAEUtil.traverseDAEFunctions(d, Expression.traverseSubexpressionsHelper, (matchQualifiedCalls, nil))
                       #=  print(name + \" has dependencies: \" + stringDelimitList(dependencies,\",\") + \"\\n\");
                       =#
                      dependencies = ListUtil.sort(dependencies, Util.strcmpBool)
                      dependencies = ListUtil.map1(dependencies, stringAppend, ".h")
                      nameHeader = name + ".h"
                      strs = ListUtil.map1r(_cons(nameHeader, dependencies), stringAppend, "(GEN_DIR)")
                      System.writeFile(name + ".deps", "(GEN_DIR)" + name + ".o: (GEN_DIR)" + name + ".c" + " " + stringDelimitList(strs, " "))
                      dependencies = ListUtil.map1(dependencies, stringAppend, "\\")
                      dependencies = ListUtil.map1r(dependencies, stringAppend, "#include \\")
                      SimCodeFunction.translateFunctions(p, name, NONE(), d, nil, dependencies)
                      str = Tpl.tplString(Unparsing.programExternalHeaderFromTypes, metarecords)
                      System.writeFile(name + "_records.c", "#include <meta/meta_modelica.h>\\n" + str)
                      cache = if cleanCache
                            icache
                          else
                            cache
                          end
                    (cache, env)
                  end
                  
                  _  => begin
                        Error.addSourceMessage(Error.SEPARATE_COMPILATION_PACKAGE_FAILED, list(name), info)
                      fail()
                  end
                end
              end
          (cache, env)
        end

        function findFunctionsToCompile(elt::SCode.Element, pathPrefix::Absyn.Path, sp::SCode.Program, acc::List{<:Absyn.Path}, accMetarecord::List{<:Absyn.Path}) ::Tuple{List{Absyn.Path}, List{Absyn.Path}} 
              local pathsMetarecord::List{Absyn.Path}
              local paths::List{Absyn.Path}

              local name::String
              local path::Absyn.Path
              local elements::List{SCode.Element}

              @match SCode.CLASS(name = name) = elt
              path = AbsynUtil.joinPaths(pathPrefix, Absyn.IDENT(name))
              paths = if SCodeUtil.isFunction(elt)
                    _cons(path, acc)
                  else
                    acc
                  end
              pathsMetarecord = begin
                @match elt begin
                  SCode.CLASS(restriction = SCode.R_METARECORD(__))  => begin
                    _cons(path, accMetarecord)
                  end
                  
                  _  => begin
                      accMetarecord
                  end
                end
              end
              elements = getNonPartialElementsForInstantiatedClass(sp, elt, path)
              (paths, pathsMetarecord) = ListUtil.fold22(elements, findFunctionsToCompile, path, sp, paths, pathsMetarecord)
          (paths, pathsMetarecord)
        end

         #= Gets the non-partial elements returned by instantiating the given path =#
        function getNonPartialElementsForInstantiatedClass(sp::SCode.Program, cl::SCode.Element, p::Absyn.Path) ::List{SCode.Element} 
              local elts::List{SCode.Element}

              local env::FCore.Graph
              local elt::SCode.Element
              local skip::Bool
              local eltsTmp::List{SCode.Element}

              skip = begin
                @match cl begin
                  SCode.CLASS(classDef = SCode.CLASS_EXTENDS(__))  => begin
                    false
                  end
                  
                  SCode.CLASS(classDef = SCode.PARTS(elementLst = eltsTmp))  => begin
                    ! ListUtil.exist(eltsTmp, SCodeUtil.isElementExtendsOrClassExtends)
                  end
                  
                  _  => begin
                      true
                  end
                end
              end
              if ! skip
                try
                  ErrorExt.setCheckpoint("getNonPartialElementsForInstantiatedClass")
                  (_, env) = Inst.instantiateClass(FCoreUtil.emptyCache(), InnerOuter.emptyInstHierarchy, sp, AbsynUtil.makeNotFullyQualified(p), doSCodeDep = false)
                  elts = FCore.RefTree.fold(FNode.children(FNode.fromRef(FGraph.lastScopeRef(env))), addNonPartialClassRef, nil)
                  ErrorExt.rollBack("getNonPartialElementsForInstantiatedClass")
                  return elts
                catch
                end
                ErrorExt.rollBack("getNonPartialElementsForInstantiatedClass")
              end
               #=  Failed to instantiate the class; perhaps due to being a function
               =#
               #=  that cannot be instantiated using model restrictions.
               =#
              elts = begin
                @match cl begin
                  SCode.CLASS(classDef = SCode.PARTS(elementLst = elts))  => begin
                    list(e for e in elts if ! SCodeUtil.isPartial(e) && SCodeUtil.isClass(e))
                  end
                  
                  _  => begin
                      nil
                  end
                end
              end
          elts
        end

        function addNonPartialClassRef(name::FCore.Name, ref::FCore.MMRef, accum::List{<:SCode.Element}) ::List{SCode.Element} 
              local classes::List{SCode.Element}

              local e::SCode.Element

              classes = begin
                @match FNode.fromRef(ref) begin
                  FCore.N(data = FCore.CL(e = e && SCode.CLASS(partialPrefix = SCode.NOT_PARTIAL(__))))  => begin
                    _cons(e, accum)
                  end
                  
                  _  => begin
                      accum
                  end
                end
              end
          classes
        end

         #= This function evaluates CALL expressions, i.e. function calls.
          They are currently evaluated by generating code for the function and
          then dynamicly load the function and call it. =#
        function cevalCallFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inValuesValueLst::List{<:Values.Value}, impl::Bool, inMsg::Absyn.Msg, numIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local newval::Values.Value
                  local env::FCore.Graph
                  local e::DAE.Exp
                  local funcpath::Absyn.Path
                  local expl::List{DAE.Exp}
                  local vallst::List{Values.Value}
                  local pubVallst::List{Values.Value}
                  local proVallst::List{Values.Value}
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local complexName::Absyn.Path
                  local pubVarLst::List{DAE.Var}
                  local proVarLst::List{DAE.Var}
                  local varLst::List{DAE.Var}
                  local pubVarNames::List{String}
                  local proVarNames::List{String}
                  local varNames::List{String}
                  local ty::DAE.Type
                  local info::SourceInfo
                  local str::String
                  local bIsCompleteFunction::Bool
                   #=  External functions that are \"known\" should be evaluated without compilation, e.g. all math functions
                   =#
                @matchcontinue (inCache, inEnv, inExp, inValuesValueLst, impl, inMsg, numIter) begin
                  (cache, env, DAE.CALL(path = funcpath), vallst, _, msg, _)  => begin
                      (cache, newval) = Ceval.cevalKnownExternalFuncs(cache, env, funcpath, vallst, msg)
                    (cache, newval)
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath), _, _, msg, _)  => begin
                      @match true = FGraph.isNotEmpty(env)
                      cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                    fail()
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(ty = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(complexName), varLst = varLst))), pubVallst, _, msg, _)  => begin
                      if Flags.isSet(Flags.DYN_LOAD)
                        Debug.traceln("CALL: record constructor: func: " + AbsynUtil.pathString(funcpath) + " type path: " + AbsynUtil.pathString(complexName))
                      end
                      @match true = AbsynUtil.pathEqual(funcpath, complexName)
                      (pubVarLst, proVarLst) = ListUtil.splitOnTrue(varLst, Types.isPublicVar)
                      expl = ListUtil.map1(proVarLst, Types.getBindingExp, funcpath)
                      (cache, proVallst) = Ceval.cevalList(cache, env, expl, impl, msg, numIter)
                      pubVarNames = ListUtil.map(pubVarLst, Expression.varName)
                      proVarNames = ListUtil.map(proVarLst, Expression.varName)
                      varNames = listAppend(pubVarNames, proVarNames)
                      vallst = listAppend(pubVallst, proVallst)
                    (cache, Values.RECORD(funcpath, vallst, varNames, -1))
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(ty = ty, builtin = false)), _, _, msg, _)  => begin
                      @shouldFail cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                      if Flags.isSet(Flags.DYN_LOAD)
                        Debug.traceln("CALL: try to evaluate or generate function: " + AbsynUtil.pathString(funcpath))
                      end
                      bIsCompleteFunction = isCompleteFunction(cache, env, funcpath)
                      @match false = Types.hasMetaArray(ty)
                      if Flags.isSet(Flags.DYN_LOAD)
                        Debug.traceln("CALL: is complete function: " + AbsynUtil.pathString(funcpath) + " " + (if bIsCompleteFunction
                              "[true]"
                            else
                              "[false]"
                            end))
                      end
                      (cache, newval) = cevalCallFunctionEvaluateOrGenerate(inCache, inEnv, inExp, inValuesValueLst, impl, inMsg, bIsCompleteFunction)
                    (cache, newval)
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(builtin = false)), _, _, msg, _)  => begin
                      @shouldFail cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                      @match false = isCompleteFunction(cache, env, funcpath)
                      if Flags.isSet(Flags.DYN_LOAD)
                        Debug.traceln("CALL: constant evaluation failed (not complete function): " + AbsynUtil.pathString(funcpath))
                      end
                    fail()
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(ty = ty, builtin = false)), _, _, msg && Absyn.MSG(info), _)  => begin
                      @shouldFail cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                      @match true = isCompleteFunction(cache, env, funcpath)
                      @match true = Types.hasMetaArray(ty)
                      str = ExpressionDump.printExpStr(inExp)
                      Error.addSourceMessage(Error.FUNCTION_RETURNS_META_ARRAY, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, outValue)
        end

         #= This function evaluates CALL expressions, i.e. function calls.
          They are currently evaluated by generating code for the function and
          then dynamicly load the function and call it. =#
        function cevalCallFunctionEvaluateOrGenerate(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inValuesValueLst::List{<:Values.Value}, impl::Bool, inMsg::Absyn.Msg, bIsCompleteFunction::Bool) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              local numCheckpoints::ModelicaInteger

               #=  Only add a stack overflow checkpoint for the top-most cevalCallFunctionEvaluateOrGenerate
               =#
              if isNone(getGlobalRoot(Global.stackoverFlowIndex))
                setGlobalRoot(Global.stackoverFlowIndex, SOME(1))
                numCheckpoints = ErrorExt.getNumCheckpoints()
                try
                  StackOverflow.clearStacktraceMessages()
                  (outCache, outValue) = cevalCallFunctionEvaluateOrGenerate2(inCache, inEnv, inExp, inValuesValueLst, impl, inMsg, bIsCompleteFunction)
                catch
                  setGlobalRoot(Global.stackoverFlowIndex, NONE())
                  ErrorExt.rollbackNumCheckpoints(ErrorExt.getNumCheckpoints() - numCheckpoints)
                  Error.addInternalError("Stack overflow when evaluating function call: " + ExpressionDump.printExpStr(inExp) + "...\\n" + stringDelimitList(StackOverflow.readableStacktraceMessages(), "\\n"), begin
                      local info::SourceInfo
                    @match inMsg begin
                      Absyn.MSG(info)  => begin
                        info
                      end
                      
                      _  => begin
                          sourceInfo()
                      end
                    end
                  end)
                  StackOverflow.clearStacktraceMessages()
                  outCache = inCache
                  outValue = Values.META_FAIL()
                end #= annotation(
                  __OpenModelica_stackOverflowCheckpoint = true) =#
                setGlobalRoot(Global.stackoverFlowIndex, NONE())
              else
                (outCache, outValue) = cevalCallFunctionEvaluateOrGenerate2(inCache, inEnv, inExp, inValuesValueLst, impl, inMsg, bIsCompleteFunction)
              end
               #= /* Do not fail or we can loop too much */ =#
          (outCache, outValue)
        end

         #= This function evaluates CALL expressions, i.e. function calls.
          They are currently evaluated by generating code for the function and
          then dynamicly load the function and call it. =#
        function cevalCallFunctionEvaluateOrGenerate2(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inValuesValueLst::List{<:Values.Value}, impl::Bool, inMsg::Absyn.Msg, bIsCompleteFunction::Bool) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = begin
                  local newval::Values.Value
                  local env::FCore.Graph
                  local e::DAE.Exp
                  local funcpath::Absyn.Path
                  local expl::List{DAE.Exp}
                  local print_debug::Bool
                  local vallst::List{Values.Value}
                  local msg::Absyn.Msg
                  local cache::FCore.Cache
                  local p::Absyn.Program
                  local libHandle::ModelicaInteger
                  local funcHandle::ModelicaInteger
                  local fNew::String
                  local fOld::String
                  local buildTime::ModelicaReal
                  local edit::ModelicaReal
                  local build::ModelicaReal
                  local a::Option{List{SCode.Element}}
                  local c::List{GlobalScript.Variable}
                  local funcstr::String
                  local f::String
                  local fileName::String
                  local name::String
                  local ppref::Bool
                  local fpref::Bool
                  local epref::Bool
                  local body::Absyn.ClassDef
                  local info::SourceInfo
                  local w::Absyn.Within
                  local functionDependencies::List{Absyn.Path}
                  local sc::SCode.Element
                  local cdef::SCode.ClassDef
                  local error_Str::String
                  local func::DAE.Function
                  local res::SCode.Restriction
                  local funcRest::Absyn.FunctionRestriction
                  local ty::DAE.Type
                   #=  try function interpretation
                   =#
                @matchcontinue (inCache, inEnv, inExp, inValuesValueLst, impl, inMsg, bIsCompleteFunction) begin
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(builtin = false)), vallst, _, msg, _)  => begin
                      @match true = Flags.isSet(Flags.EVAL_FUNC)
                      @shouldFail cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                      @match (cache, (@match SCode.CLASS(partialPrefix = SCode.NOT_PARTIAL()) = sc), env) = Lookup.lookupClass(cache, env, funcpath)
                      isCevaluableFunction(sc)
                      (cache, env, _) = InstFunction.implicitFunctionInstantiation(cache, env, InnerOuter.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), sc, nil)
                      func = FCoreUtil.getCachedInstFunc(cache, funcpath)
                      (cache, newval) = CevalFunction.evaluate(cache, env, func, vallst)
                    (cache, newval)
                  end
                  
                  (cache, env, DAE.CALL(path = funcpath, attr = DAE.CALL_ATTR(builtin = false)), vallst, _, msg, _) where (bIsCompleteFunction && Flags.isSet(Flags.GEN))  => begin
                       #=  bcall1(Flags.isSet(Flags.DYN_LOAD), print,\"[dynload]: try constant evaluation: \" + AbsynUtil.pathString(funcpath) + \"\\n\");
                       =#
                       #=  bcall1(Flags.isSet(Flags.DYN_LOAD), print, \"[dynload]: constant evaluation SUCCESS: \" + AbsynUtil.pathString(funcpath) + \"\\n\");
                       =#
                       #=  not in CF list, we have a symbol table, generate function and update symtab
                       =#
                       #=  yeha! we have a symboltable!
                       =#
                      @shouldFail cevalIsExternalObjectConstructor(cache, funcpath, env, msg)
                      if Flags.isSet(Flags.DYN_LOAD)
                        print("[dynload]: [SOME SYMTAB] not in in CF list: " + AbsynUtil.pathString(funcpath) + "\\n")
                      end
                      p = SymbolTable.getAbsyn()
                       #=  now is safe to generate code
                       =#
                      (cache, funcstr, fileName) = cevalGenerateFunction(cache, env, p, funcpath)
                      print_debug = Flags.isSet(Flags.DYN_LOAD)
                      libHandle = System.loadLibrary(fileName, print_debug)
                      funcHandle = System.lookupFunction(libHandle, stringAppend("in_", funcstr))
                      execStatReset()
                      newval = DynLoad.executeFunction(funcHandle, vallst, print_debug)
                      execStat("executeFunction(" + AbsynUtil.pathString(funcpath) + ")")
                      System.freeLibrary(libHandle, print_debug)
                       #=  update the build time in the class!
                       =#
                      @match Absyn.CLASS(_, _, _, _, Absyn.R_FUNCTION(_), _, info) = Interactive.getPathedClassInProgram(funcpath, p)
                      w = Interactive.buildWithin(funcpath)
                      if Flags.isSet(Flags.DYN_LOAD)
                        print("[dynload]: Updating build time for function path: " + AbsynUtil.pathString(funcpath) + " within: " + Dump.unparseWithin(w) + "\\n")
                      end
                       #=  p = Interactive.updateProgram(Absyn.PROGRAM({Absyn.CLASS(name,ppref,fpref,epref,Absyn.R_FUNCTION(funcRest),body,info)},w,ts), p);
                       =#
                      _ = AbsynUtil.getFileNameFromInfo(info)
                      if Flags.isSet(Flags.DYN_LOAD)
                        print("[dynload]: [SOME SYMTAB] not in in CF list [finished]: " + AbsynUtil.pathString(funcpath) + "\\n")
                      end
                    (cache, newval)
                  end
                  
                  (_, _, DAE.CALL(path = funcpath), _, _, _, _)  => begin
                      if Flags.isSet(Flags.DYN_LOAD)
                        print("[dynload]: FAILED to constant evaluate function: " + AbsynUtil.pathString(funcpath) + "\\n")
                      end
                      @match false = Flags.isSet(Flags.GEN)
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.trace("- codegeneration is turned off. switch \\nogen\\ flag off\\n")
                    fail()
                  end
                end
              end
               #= TODO: readd this when testsuite is okay.
               =#
               #= Error.addMessage(Error.FAILED_TO_EVALUATE_FUNCTION, {error_Str});
               =#
          (outCache, outValue)
        end

        function cevalIsExternalObjectConstructor(cache::FCore.Cache, funcpath::Absyn.Path, env::FCore.Graph, msg::Absyn.Msg)  
              local funcpath2::Absyn.Path
              local tp::DAE.Type
              local info::Option{SourceInfo}

              _ = begin
                @match (cache, funcpath, env, msg) begin
                  (_, _, FCore.EG(_), Absyn.NO_MSG(__))  => begin
                    fail()
                  end
                  
                  (_, _, _, Absyn.NO_MSG(__))  => begin
                      @match (funcpath2, Absyn.IDENT("constructor")) = AbsynUtil.splitQualAndIdentPath(funcpath)
                      info = if valueEq(msg, Absyn.NO_MSG())
                            NONE()
                          else
                            SOME(AbsynUtil.dummyInfo)
                          end
                      (_, tp, _) = Lookup.lookupType(cache, env, funcpath2, info)
                      Types.externalObjectConstructorType(tp)
                    ()
                  end
                end
              end
        end

        function checkLibraryUsage(inLibrary::String, inExp::Absyn.Exp) ::Bool 
              local isUsed::Bool

              isUsed = begin
                  local s::String
                  local exps::List{Absyn.Exp}
                @match (inLibrary, inExp) begin
                  (_, Absyn.STRING(s))  => begin
                    stringEq(s, inLibrary)
                  end
                  
                  (_, Absyn.ARRAY(exps))  => begin
                    ListUtil.isMemberOnTrue(inLibrary, exps, checkLibraryUsage)
                  end
                end
              end
          isUsed
        end

         #= Checks if an element is a function or external function that can be evaluated
          by CevalFunction. =#
        function isCevaluableFunction(inElement::SCode.Element)  
              _ = begin
                  local fid::String
                  local mod::SCode.Mod
                  local lib::Absyn.Exp
                   #= only some external functions.
                   =#
                @match inElement begin
                  SCode.CLASS(restriction = SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(_)), classDef = SCode.PARTS(externalDecl = SOME(SCode.EXTERNALDECL(funcName = SOME(fid), annotation_ = SOME(SCode.ANNOTATION(mod))))))  => begin
                      @match SCode.MOD(binding = SOME(lib)) = Mod.getUnelabedSubMod(mod, "Library")
                      @match true = checkLibraryUsage("Lapack", lib) || checkLibraryUsage("lapack", lib)
                      isCevaluableFunction2(fid)
                    ()
                  end
                  
                  SCode.CLASS(restriction = SCode.R_FUNCTION(_))  => begin
                    ()
                  end
                end
              end
               #=  All other functions can be evaluated.
               =#
        end

         #= Checks if a function name belongs to a known external function that we can
          constant evaluate. =#
        function isCevaluableFunction2(inFuncName::String)  
              _ = begin
                   #=  Lapack functions.
                   =#
                @match inFuncName begin
                  "dgbsv"  => begin
                    ()
                  end
                  
                  "dgeev"  => begin
                    ()
                  end
                  
                  "dgegv"  => begin
                    ()
                  end
                  
                  "dgels"  => begin
                    ()
                  end
                  
                  "dgelsx"  => begin
                    ()
                  end
                  
                  "dgelsy"  => begin
                    ()
                  end
                  
                  "dgeqpf"  => begin
                    ()
                  end
                  
                  "dgesv"  => begin
                    ()
                  end
                  
                  "dgesvd"  => begin
                    ()
                  end
                  
                  "dgetrf"  => begin
                    ()
                  end
                  
                  "dgetri"  => begin
                    ()
                  end
                  
                  "dgetrs"  => begin
                    ()
                  end
                  
                  "dgglse"  => begin
                    ()
                  end
                  
                  "dgtsv"  => begin
                    ()
                  end
                  
                  "dorgqr"  => begin
                    ()
                  end
                end
              end
        end

        function isSimpleAPIFunction(ty::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_FUNCTION(functionAttributes = DAE.FUNCTION_ATTRIBUTES(isBuiltin = DAE.FUNCTION_BUILTIN(__)))  => begin
                    isSimpleAPIFunctionArg(ty.funcResultType) && min(begin
                      @match fa begin
                        DAE.FUNCARG(__)  => begin
                          isSimpleAPIFunctionArg(fa.ty)
                        end
                      end
                    end for fa in ty.funcArg)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function isSimpleAPIFunctionArg(ty::DAE.Type) ::Bool 
              local b::Bool

              b = begin
                @match ty begin
                  DAE.T_INTEGER(__)  => begin
                    true
                  end
                  
                  DAE.T_REAL(__)  => begin
                    true
                  end
                  
                  DAE.T_BOOL(__)  => begin
                    true
                  end
                  
                  DAE.T_STRING(__)  => begin
                    true
                  end
                  
                  DAE.T_NORETCALL(__)  => begin
                    true
                  end
                  
                  DAE.T_ARRAY(__)  => begin
                    isSimpleAPIFunctionArg(ty.ty)
                  end
                  
                  DAE.T_CODE(ty = DAE.C_TYPENAME(__))  => begin
                    true
                  end
                  
                  DAE.T_TUPLE(__)  => begin
                    min(isSimpleAPIFunctionArg(t) for t in ty.types)
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function verifyInterfaceType(elt::SCode.Element, expected::List{<:String})  
              _ = begin
                  local str::String
                  local name::String
                  local ann::SCode.Annotation
                  local info::SourceInfo
                @matchcontinue (elt, expected) begin
                  (SCode.CLASS(restriction = SCode.R_METARECORD(moved = true)), _)  => begin
                    ()
                  end
                  
                  (SCode.CLASS(cmt = SCode.COMMENT(annotation_ = SOME(ann))), name <| _)  => begin
                      @match (Absyn.STRING(str), info) = SCodeUtil.getNamedAnnotation(ann, "__OpenModelica_Interface")
                      Error.assertionOrAddSourceMessage(listMember(str, expected), Error.MISMATCHING_INTERFACE_TYPE, list(str, name), info)
                    ()
                  end
                  
                  _  => begin
                        print(SCodeDump.unparseElementStr(elt) + "\\n")
                        Error.addSourceMessage(Error.MISSING_INTERFACE_TYPE, nil, SCodeUtil.elementInfo(elt))
                      fail()
                  end
                end
              end
        end

        function getInterfaceType(elt::SCode.Element, assoc::List{<:Tuple{<:String, List{<:String}}}) ::List{String} 
              local it::List{String}

              it = begin
                  local name::String
                  local ann::SCode.Annotation
                  local str::String
                  local info::SourceInfo
                @matchcontinue (elt, assoc) begin
                  (SCode.CLASS(cmt = SCode.COMMENT(annotation_ = SOME(ann))), _)  => begin
                      @match (Absyn.STRING(str), _) = SCodeUtil.getNamedAnnotation(ann, "__OpenModelica_Interface")
                      it = Util.assoc(str, assoc)
                    it
                  end
                  
                  _  => begin
                        Error.addSourceMessage(Error.MISSING_INTERFACE_TYPE, nil, SCodeUtil.elementInfo(elt))
                      fail()
                  end
                end
              end
          it
        end

        function getInterfaceTypeAssocElt(val::Values.Value, info::SourceInfo) ::Tuple{String, List{String}} 
              local assoc::Tuple{String, List{String}}

              assoc = begin
                  local str::String
                  local strs::List{String}
                  local vals::List{Values.Value}
                @match (val, info) begin
                  (Values.ARRAY(valueLst = Values.STRING("") <| _), _)  => begin
                      Error.addSourceMessage(Error.MISSING_INTERFACE_TYPE, nil, info)
                    fail()
                  end
                  
                  (Values.ARRAY(valueLst = Values.STRING(str) <| vals), _)  => begin
                      strs = ListUtil.select(ListUtil.map(vals, ValuesUtil.extractValueString), Util.isNotEmptyString)
                    (str, _cons(str, strs))
                  end
                end
              end
          assoc
        end

        function buildDependencyGraph(name::String, sp::SCode.Program) ::List{String} 
              local edges::List{String}

              edges = begin
                  local elts::List{SCode.Element}
                @match (name, sp) begin
                  (_, _)  => begin
                      @match SCode.CLASS(classDef = SCode.PARTS(elementLst = elts)) = ListUtil.getMemberOnTrue(name, sp, SCodeUtil.isClassNamed)
                      (_, _, _, elts, _) = SCodeUtil.partitionElements(elts)
                    ListUtil.map(elts, importDepenency)
                  end
                end
              end
          edges
        end

        function buildDependencyGraphPublicImports(name::String, sp::SCode.Program) ::List{String} 
              local edges::List{String}

              edges = begin
                  local elts::List{SCode.Element}
                @match (name, sp) begin
                  (_, _)  => begin
                      @match SCode.CLASS(classDef = SCode.PARTS(elementLst = elts)) = ListUtil.getMemberOnTrue(name, sp, SCodeUtil.isClassNamed)
                      elts = ListUtil.select(elts, SCodeUtil.elementIsPublicImport)
                    ListUtil.map(elts, importDepenency)
                  end
                end
              end
          edges
        end

        function buildTransitiveDependencyGraph(name::String, oldgraph::List{<:Tuple{<:String, List{<:String}}}) ::List{String} 
              local edges::List{String}

              edges = begin
                  local str::String
                @matchcontinue (name, oldgraph) begin
                  (_, _)  => begin
                    ListUtil.setDifference(Graph.allReachableNodes((list(name), nil), oldgraph, stringEq), list(name))
                  end
                  
                  _  => begin
                        str = "CevalScript.buildTransitiveDependencyGraph failed: " + name
                        Error.addMessage(Error.INTERNAL_ERROR, list(str))
                      fail()
                  end
                end
              end
          edges
        end

        function importDepenency(simp::SCode.Element) ::String 
              local name::String

              name = begin
                  local imp::Absyn.Import
                  local info::SourceInfo
                  local str::String
                  local path::Absyn.Path
                @match simp begin
                  SCode.IMPORT(imp = Absyn.NAMED_IMPORT(path = path))  => begin
                    AbsynUtil.pathFirstIdent(path)
                  end
                  
                  SCode.IMPORT(imp = Absyn.NAMED_IMPORT(path = path))  => begin
                    AbsynUtil.pathFirstIdent(path)
                  end
                  
                  SCode.IMPORT(imp = Absyn.QUAL_IMPORT(path = path))  => begin
                    AbsynUtil.pathFirstIdent(path)
                  end
                  
                  SCode.IMPORT(imp = Absyn.UNQUAL_IMPORT(path = path))  => begin
                    AbsynUtil.pathFirstIdent(path)
                  end
                  
                  SCode.IMPORT(imp = Absyn.GROUP_IMPORT(prefix = path))  => begin
                    AbsynUtil.pathFirstIdent(path)
                  end
                  
                  SCode.IMPORT(imp = imp, info = info)  => begin
                      str = "CevalScript.importDepenency could not handle:" + Dump.unparseImportStr(imp)
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list(str), info)
                    fail()
                  end
                end
              end
          name
        end

        function compareNumberOfDependencies(node1::Tuple{<:String, List{<:String}}, node2::Tuple{<:String, List{<:String}}) ::Bool 
              local cmp::Bool

              local deps1::List{String}
              local deps2::List{String}

              (_, deps1) = node1
              (_, deps2) = node2
              cmp = listLength(deps1) >= listLength(deps2)
          cmp
        end

        function compareDependencyNode(node1::Tuple{<:String, List{<:String}}, node2::Tuple{<:String, List{<:String}}) ::Bool 
              local cmp::Bool

              local s1::String
              local s2::String

              (s1, _) = node1
              (s2, _) = node2
              cmp = Util.strcmpBool(s1, s2)
          cmp
        end

        function dependencyString(deps::Tuple{<:String, List{<:String}}) ::String 
              local str::String

              local strs::List{String}

              (str, strs) = deps
              str = str + " (" + intString(listLength(strs)) + "): " + stringDelimitList(strs, ",")
          str
        end

        function transitiveDependencyString(deps::Tuple{<:String, List{<:String}}) ::String 
              local str::String

              local strs::List{String}

              (str, strs) = deps
              str = intString(listLength(strs)) + ": (" + str + ") " + stringDelimitList(strs, ",")
          str
        end

        function containsPublicInterface(elt::SCode.Element) ::Bool 
              local b::Bool

              b = begin
                  local elts::List{SCode.Element}
                  local name::String
                @match elt begin
                  SCode.CLASS(restriction = SCode.R_PACKAGE(__), encapsulatedPrefix = SCode.ENCAPSULATED(__), classDef = SCode.PARTS(elementLst = elts))  => begin
                    ListUtil.exist(elts, containsPublicInterface2)
                  end
                  
                  _  => begin
                        name = SCodeUtil.elementName(elt)
                        name = "CevalScript.containsPublicInterface failed: " + name
                        Error.addMessage(Error.INTERNAL_ERROR, list(name))
                      fail()
                  end
                end
              end
          b
        end

         #= If the package contains a public type or constant, we depend on this package also through other modules =#
        function containsPublicInterface2(elt::SCode.Element) ::Bool 
              local b::Bool

              b = begin
                  local name::String
                @match elt begin
                  SCode.IMPORT(__)  => begin
                    false
                  end
                  
                  SCode.EXTENDS(__)  => begin
                    false
                  end
                  
                  SCode.CLASS(restriction = SCode.R_FUNCTION(_))  => begin
                    false
                  end
                  
                  SCode.COMPONENT(prefixes = SCode.PREFIXES(visibility = SCode.PUBLIC(__)))  => begin
                    true
                  end
                  
                  SCode.CLASS(prefixes = SCode.PREFIXES(visibility = SCode.PUBLIC(__)))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
               #=  print(\"public component \" + name + \": \");
               =#
               #=  print(\"public class \" + name + \": \");
               =#
          b
        end

        function containsImport(elt::SCode.Element, visibility::SCode.Visibility) ::Bool 
              local b::Bool

              b = begin
                  local elts::List{SCode.Element}
                  local name::String
                @match (elt, visibility) begin
                  (SCode.CLASS(restriction = SCode.R_PACKAGE(__), encapsulatedPrefix = SCode.ENCAPSULATED(__), classDef = SCode.PARTS(elementLst = elts)), _)  => begin
                    ListUtil.exist1(elts, containsImport2, visibility)
                  end
                  
                  _  => begin
                        name = SCodeUtil.elementName(elt)
                        name = "CevalScript.containsPublicInterface failed: " + name
                        Error.addMessage(Error.INTERNAL_ERROR, list(name))
                      fail()
                  end
                end
              end
          b
        end

         #= If the package contains a public type or constant, we depend on this package also through other modules =#
        function containsImport2(elt::SCode.Element, visibility::SCode.Visibility) ::Bool 
              local b::Bool

              b = begin
                  local name::String
                @match (elt, visibility) begin
                  (SCode.IMPORT(visibility = SCode.PUBLIC(__)), SCode.PUBLIC(__))  => begin
                    true
                  end
                  
                  (SCode.IMPORT(visibility = SCode.PROTECTED(__)), SCode.PROTECTED(__))  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

        function printInterfaceString(elt::SCode.Element)  
              local str::String

              @match SCode.CLASS(name = str) = elt
              print(str + ": " + boolString(containsPublicInterface(elt)) + "\\n")
        end

        function writeModuleDepends(cl::SCode.Element, prefix::String, suffix::String, deps::List{<:Tuple{<:String, List{<:String}}}) ::String 
              local str::String

              str = begin
                  local name::String
                  local fileName::String
                  local tmp1::String
                  local allDepends::List{String}
                  local protectedDepends::List{String}
                  local tmp2::List{String}
                  local elts::List{SCode.Element}
                  local info::SourceInfo
                @matchcontinue (cl, prefix, suffix, deps) begin
                  (SCode.CLASS(name = name, classDef = SCode.PARTS(elementLst = elts), info = SOURCEINFO(__)), _, _, _)  => begin
                      protectedDepends = ListUtil.map(ListUtil.select(elts, SCodeUtil.elementIsProtectedImport), importDepenency)
                      protectedDepends = ListUtil.select(protectedDepends, isNotBuiltinImport)
                      @match _cons(_, allDepends) = Graph.allReachableNodes((_cons(name, protectedDepends), nil), deps, stringEq)
                      allDepends = ListUtil.map1r(allDepends, stringAppend, prefix)
                      allDepends = ListUtil.map1(allDepends, stringAppend, ".interface.mo")
                      str = prefix + name + suffix + ": (RELPATH_" + name + ") " + stringDelimitList(allDepends, " ")
                    str
                  end
                  
                  (SCode.CLASS(name = name, classDef = SCode.PARTS(elementLst = elts), info = info), _, _, _)  => begin
                      protectedDepends = ListUtil.map(ListUtil.select(elts, SCodeUtil.elementIsProtectedImport), importDepenency)
                      protectedDepends = ListUtil.select(protectedDepends, isNotBuiltinImport)
                      allDepends = list(Util.tuple21(e) for e in deps)
                      for d in protectedDepends
                        if ! listMember(d, allDepends)
                          Error.addSourceMessage(Error.GENERATE_SEPARATE_CODE_DEPENDENCIES_FAILED_UNKNOWN_PACKAGE, list(name, name, d), info)
                          fail()
                        end
                      end
                      for dep in deps
                        (tmp1, tmp2) = dep
                        for d in tmp2
                          if ! listMember(d, allDepends)
                            Error.addSourceMessage(Error.GENERATE_SEPARATE_CODE_DEPENDENCIES_FAILED_UNKNOWN_PACKAGE, list(name, tmp1, d), info)
                            fail()
                          end
                        end
                      end
                    fail()
                  end
                  
                  (SCode.CLASS(name = name, info = info), _, _, _)  => begin
                      Error.addSourceMessage(Error.GENERATE_SEPARATE_CODE_DEPENDENCIES_FAILED, list(name), info)
                    fail()
                  end
                end
              end
          str
        end

        function isNotBuiltinImport(module::String) ::Bool 
              local b::Bool = module != "MetaModelica"
          b
        end

        function getTypeNameIdent(val::Values.Value) ::String 
              local str::String

              @match Values.CODE(Absyn.C_TYPENAME(Absyn.IDENT(str))) = val
          str
        end

        function getChangedClass(elt::SCode.Element, suffix::String) ::String 
              local name::String

              name = begin
                  local fileName::String
                @matchcontinue (elt, suffix) begin
                  (SCode.CLASS(name = name, info = SOURCEINFO(__)), _)  => begin
                      @match false = System.regularFileExists(name + suffix)
                    name
                  end
                  
                  (SCode.CLASS(name = name, info = SOURCEINFO(fileName = fileName)), _)  => begin
                      @match true = System.fileIsNewerThan(fileName, name + suffix)
                    name
                  end
                end
              end
          name
        end

        function isChanged(node::Tuple{<:String, List{<:String}}, hs::HashSetString.HashSet) ::Bool 
              local b::Bool

              local str::String
              local strs::List{String}

              (str, strs) = node
              b = ListUtil.exist1(_cons(str, strs), BaseHashSet.has, hs)
               #=  print(str + \": \" +  boolString(b) + \"\\n\");
               =#
          b
        end

        function reloadClass(filename::String, encoding::String)  
              local p::Absyn.Program
              local newp::Absyn.Program

              newp = Parser.parse(filename, encoding)
               #= /* Don't use the classloader since that can pull in entire directory structures. We only want to reload one single file. */ =#
              newp = Interactive.updateProgram(newp, SymbolTable.getAbsyn())
              SymbolTable.setAbsyn(newp)
        end

        function getFullPathFromUri(program::Absyn.Program, uri::String, printError::Bool) ::String 
              local path::String

              local str1::String
              local str2::String
              local str3::String

              (str1, str2, str3) = System.uriToClassAndPath(uri)
              path = getBasePathFromUri(str1, str2, program, Settings.getModelicaPath(Config.getRunningTestsuite()), printError) + str3
          path
        end

         #= Handle modelica: URIs =#
        function getBasePathFromUri(scheme::String, iname::String, program::Absyn.Program, modelicaPath::String, printError::Bool) ::String 
              local basePath::String

              basePath = begin
                  local isDir::Bool
                  local mps::List{String}
                  local names::List{String}
                  local gd::String
                  local mp::String
                  local bp::String
                  local str::String
                  local name::String
                  local version::String
                  local fileName::String
                @matchcontinue (scheme, iname, program, modelicaPath, printError) begin
                  ("modelica://", name, _, _, _)  => begin
                      @match _cons(name, names) = System.strtok(name, ".")
                      @match Absyn.CLASS(info = SOURCEINFO(fileName = fileName)) = Interactive.getPathedClassInProgram(Absyn.IDENT(name), program)
                      mp = System.dirname(fileName)
                      bp = findModelicaPath2(mp, names, "", true)
                    bp
                  end
                  
                  ("modelica://", name, _, mp, _)  => begin
                      @match _cons(name, names) = System.strtok(name, ".")
                      @shouldFail _ = Interactive.getPathedClassInProgram(Absyn.IDENT(name), program)
                      gd = Autoconf.groupDelimiter
                      mps = System.strtok(mp, gd)
                      (mp, name, isDir) = System.getLoadModelPath(name, list("default"), mps)
                      mp = if isDir
                            mp + name
                          else
                            mp
                          end
                      bp = findModelicaPath2(mp, names, "", true)
                    bp
                  end
                  
                  ("file://", _, _, _, _)  => begin
                    ""
                  end
                  
                  ("modelica://", name, _, mp, true)  => begin
                      @match _cons(name, _) = System.strtok(name, ".")
                      str = "Could not resolve modelica://" + name + " with MODELICAPATH: " + mp
                      Error.addMessage(Error.COMPILER_ERROR, list(str))
                    fail()
                  end
                end
              end
          basePath
        end

         #= Handle modelica: URIs =#
        function findModelicaPath(imps::List{<:String}, names::List{<:String}, version::String) ::String 
              local basePath::String

              basePath = begin
                  local mp::String
                  local mps::List{String}
                @matchcontinue (imps, names, version) begin
                  (mp <| _, _, _)  => begin
                    findModelicaPath2(mp, names, version, false)
                  end
                  
                  (_ <| mps, _, _)  => begin
                    findModelicaPath(mps, names, version)
                  end
                end
              end
          basePath
        end

         #= Handle modelica: URIs =#
        function findModelicaPath2(mp::String, inames::List{<:String}, version::String, b::Bool) ::String 
              local basePath::String

              basePath = begin
                  local names::List{String}
                  local name::String
                  local file::String
                @matchcontinue (mp, inames, version, b) begin
                  (_, name <| names, _, _)  => begin
                      @match false = stringEq(version, "")
                      file = mp + "/" + name + " " + version
                      @match true = System.directoryExists(file)
                    findModelicaPath2(file, names, "", true)
                  end
                  
                  (_, name <| _, _, _)  => begin
                      @match false = stringEq(version, "")
                      file = mp + "/" + name + " " + version + ".mo"
                      @match true = System.regularFileExists(file)
                    mp
                  end
                  
                  (_, name <| names, _, _)  => begin
                      file = mp + "/" + name
                      @match true = System.directoryExists(file)
                    findModelicaPath2(file, names, "", true)
                  end
                  
                  (_, name <| _, _, _)  => begin
                      file = mp + "/" + name + ".mo"
                      @match true = System.regularFileExists(file)
                    mp
                  end
                  
                  (_, _, _, true)  => begin
                    mp
                  end
                end
              end
               #=  print(\"Found file 1: \" + file + \"\\n\");
               =#
               #=  print(\"Found file 2: \" + file + \"\\n\");
               =#
               #=  print(\"Found file 3: \" + file + \"\\n\");
               =#
               #=  print(\"Found file 4: \" + file + \"\\n\");
               =#
               #=  This class is part of the current package.mo, or whatever...
               =#
               #=  print(\"Did not find file 5: \" + mp + \" - \" + name + \"\\n\");
               =#
          basePath
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
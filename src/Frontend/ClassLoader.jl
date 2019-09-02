  module ClassLoader 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl PackageOrder 
    @UniontypeDecl LoadFileStrategy 

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
        import Absyn

        import Autoconf
        import BaseHashTable
        import Config
        import Debug
        import Error
        import Flags
        import HashTableStringToProgram
        import ListUtil
        import Parser
        import Settings
        import System
        import Util
        HashTable = HashTableStringToProgram.HashTable 

         @Uniontype PackageOrder begin
              @Record CLASSPART begin

                       cp::Absyn.ClassPart
              end

              @Record ELEMENT begin

                       element::Absyn.ElementItem
                       pub #= public =#::Bool
              end

              @Record CLASSLOAD begin

                       cl::String
              end
         end

         @Uniontype LoadFileStrategy begin
              @Record STRATEGY_HASHTABLE begin

                       ht::HashTable
              end

              @Record STRATEGY_ON_DEMAND begin

                       encoding::String
              end
         end

         #= This function takes a \\'Path\\' and the $OPENMODELICALIBRARY as a string
          and tries to load the class from the path.
          If the classname is qualified, the complete package is loaded.
          E.g. load_class(Modelica.SIunits.Voltage) -> whole Modelica package loaded. =#
        function loadClass(inPath::Absyn.Path, priorityList::List{<:String}, modelicaPath::String, encoding::Option{<:String}, requireExactVersion::Bool = false, encrypted::Bool = false) ::Absyn.Program 
              local outProgram::Absyn.Program

              outProgram = begin
                  local gd::String
                  local classname::String
                  local mp::String
                  local pack::String
                  local mps::List{String}
                  local p::Absyn.Program
                  local rest::Absyn.Path
                   #= /* Simple names: Just load the file if it can be found in $OPENMODELICALIBRARY */ =#
                @matchcontinue (inPath, priorityList, modelicaPath, encoding) begin
                  (Absyn.IDENT(name = classname), _, mp, _)  => begin
                      gd = Autoconf.groupDelimiter
                      mps = System.strtok(mp, gd)
                      p = loadClassFromMps(classname, priorityList, mps, encoding, requireExactVersion, encrypted)
                      checkOnLoadMessage(p)
                    p
                  end
                  
                  (Absyn.QUALIFIED(name = pack), _, mp, _)  => begin
                      gd = Autoconf.groupDelimiter
                      mps = System.strtok(mp, gd)
                      p = loadClassFromMps(pack, priorityList, mps, encoding, requireExactVersion, encrypted)
                      checkOnLoadMessage(p)
                    p
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("ClassLoader.loadClass failed\\n")
                      fail()
                  end
                end
              end
               #= /* Qualified names: First check if it is defined in a file pack.mo */ =#
               #= /* failure */ =#
          outProgram
        end

         #= Loads a class or classes from a set of paths in OPENMODELICALIBRARY =#
        function loadClassFromMps(id::String, prios::List{<:String}, mps::List{<:String}, encoding::Option{<:String}, requireExactVersion::Bool = false, encrypted::Bool = false) ::Absyn.Program 
              local outProgram::Absyn.Program

              local mp::String
              local name::String
              local pwd::String
              local cmd::String
              local version::String
              local userLibraries::String
              local isDir::Bool
              local impactOK::Bool
              local cl::Absyn.Class

              try
                (mp, name, isDir) = System.getLoadModelPath(id, prios, mps, requireExactVersion)
              catch
                pwd = System.pwd()
                userLibraries = Settings.getHomeDir(Config.getRunningTestsuite()) + "/.openmodelica/libraries/"
                @match true = System.directoryExists(userLibraries)
                @match true = listMember(userLibraries, mps)
                System.cd(userLibraries)
                version = begin
                  @match prios begin
                    version <| _ where (version != "default")  => begin
                      version
                    end
                    
                    _  => begin
                        ""
                    end
                  end
                end
                cmd = "impact install \\" + id + (if version != ""
                      "#" + version
                    else
                      ""
                    end) + "\\"
                impactOK = 0 == System.systemCall(cmd, "/dev/null")
                System.cd(pwd)
                if impactOK
                  Error.addMessage(Error.NOTIFY_IMPACT_FOUND, list(id, if version != ""
                        " " + version
                      else
                        ""
                      end, userLibraries))
                  (mp, name, isDir) = System.getLoadModelPath(id, prios, mps, true)
                else
                  fail()
                end
              end
               #=  print(\"System.getLoadModelPath: \" + id + \" {\" + stringDelimitList(prios,\",\") + \"} \" + stringDelimitList(mps,\",\") + \" => \" + mp + \" \" + name + \" \" + boolString(isDir));
               =#
              Config.setLanguageStandardFromMSL(name)
              cl = loadClassFromMp(id, mp, name, isDir, encoding, encrypted)
              outProgram = Absyn.PROGRAM(list(cl), Absyn.TOP())
          outProgram
        end

        function loadClassFromMp(id::String #= the actual class name =#, path::String, name::String, isDir::Bool, optEncoding::Option{<:String}, encrypted::Bool = false) ::Absyn.Class 
              local outClass::Absyn.Class

              outClass = begin
                  local pd::String
                  local encoding::String
                  local encodingfile::String
                  local cl::Absyn.Class
                  local filenames::List{String}
                  local strategy::LoadFileStrategy
                  local lveStarted::Bool
                  local lveInstance::Option{ModelicaInteger}
                @match (id, path, name, isDir, optEncoding) begin
                  (_, _, _, false, _)  => begin
                      pd = Autoconf.pathDelimiter
                      encodingfile = stringAppendList(list(path, pd, "package.encoding"))
                      encoding = System.trimChar(System.trimChar(if System.regularFileExists(encodingfile)
                            System.readFile(encodingfile)
                          else
                            Util.getOptionOrDefault(optEncoding, "UTF-8")
                          end, "\\n"), " ")
                      strategy = STRATEGY_ON_DEMAND(encoding)
                      cl = parsePackageFile(path + pd + name, strategy, false, Absyn.TOP(), id)
                    cl
                  end
                  
                  (_, _, _, true, _)  => begin
                      pd = Autoconf.pathDelimiter
                      encodingfile = stringAppendList(list(path, pd, name, pd, "package.encoding"))
                      encoding = System.trimChar(System.trimChar(if System.regularFileExists(encodingfile)
                            System.readFile(encodingfile)
                          else
                            Util.getOptionOrDefault(optEncoding, "UTF-8")
                          end, "\\n"), " ")
                      if encrypted
                        (lveStarted, lveInstance) = Parser.startLibraryVendorExecutable(path + pd + name)
                        if ! lveStarted
                          fail()
                        end
                      end
                      if (Config.getRunningTestsuite() || Config.noProc() == 1) && ! encrypted
                        strategy = STRATEGY_ON_DEMAND(encoding)
                      else
                        filenames = getAllFilesFromDirectory(path + pd + name, encrypted)
                        strategy = STRATEGY_HASHTABLE(Parser.parallelParseFiles(filenames, encoding, Config.noProc(), path + pd + name, lveInstance))
                      end
                      cl = loadCompletePackageFromMp(id, name, path, strategy, Absyn.TOP(), Error.getNumErrorMessages(), encrypted)
                      if encrypted && lveStarted
                        Parser.stopLibraryVendorExecutable(lveInstance)
                      end
                    cl
                  end
                end
              end
          outClass
        end

        function getAllFilesFromDirectory(dir::String, encrypted::Bool, acc::List{<:String} = nil) ::List{String} 
              local files::List{String}

              local subdirs::List{String}
              local pd::String = Autoconf.pathDelimiter

              if encrypted
                files = _cons(dir + pd + "package.moc", listAppend(list(dir + pd + f for f in System.mocFiles(dir)), acc))
              else
                files = _cons(dir + pd + "package.mo", listAppend(list(dir + pd + f for f in System.moFiles(dir)), acc))
              end
              subdirs = list(dir + pd + d for d in ListUtil.filter2OnTrue(System.subDirectories(dir), existPackage, dir, encrypted))
              files = ListUtil.fold1(subdirs, getAllFilesFromDirectory, encrypted, files)
          files
        end

         #= Loads a whole package from the ModelicaPaths defined in OPENMODELICALIBRARY =#
        function loadCompletePackageFromMp(id::String #= actual class identifier =#, inIdent::Absyn.Ident, inString::String, strategy::LoadFileStrategy, inWithin::Absyn.Within, numError::ModelicaInteger, encrypted::Bool = false) ::Absyn.Class 
              local cl::Absyn.Class

              cl = begin
                  local pd::String
                  local mp_1::String
                  local packagefile::String
                  local orderfile::String
                  local pack::String
                  local mp::String
                  local name::String
                  local str::String
                  local within_::Absyn.Within
                  local tv::List{String}
                  local pp::Bool
                  local fp::Bool
                  local ep::Bool
                  local r::Absyn.Restriction
                  local ca::List{Absyn.NamedArg}
                  local cp::List{Absyn.ClassPart}
                  local cmt::Option{String}
                  local info::SourceInfo
                  local path::Absyn.Path
                  local w2::Absyn.Within
                  local reverseOrder::List{PackageOrder}
                  local ann::List{Absyn.Annotation}
                @matchcontinue (id, inIdent, inString, inWithin) begin
                  (_, pack, mp, within_)  => begin
                      pd = Autoconf.pathDelimiter
                      mp_1 = stringAppendList(list(mp, pd, pack))
                      packagefile = stringAppendList(list(mp_1, pd, if encrypted
                            "package.moc"
                          else
                            "package.mo"
                          end))
                      orderfile = stringAppendList(list(mp_1, pd, "package.order"))
                      if ! System.regularFileExists(packagefile)
                        Error.addInternalError("Expected file " + packagefile + " to exist", sourceInfo())
                        fail()
                      end
                      @match (@match Absyn.CLASS(name, pp, fp, ep, r, Absyn.PARTS(tv, ca, cp, ann, cmt), info) = cl) = parsePackageFile(packagefile, strategy, true, within_, id)
                      reverseOrder = getPackageContentNames(cl, orderfile, mp_1, Error.getNumErrorMessages(), encrypted)
                      path = AbsynUtil.joinWithinPath(within_, Absyn.IDENT(id))
                      w2 = Absyn.WITHIN(path)
                      cp = ListUtil.fold4(reverseOrder, loadCompletePackageFromMp2, mp_1, strategy, w2, encrypted, nil)
                    Absyn.CLASS(name, pp, fp, ep, r, Absyn.PARTS(tv, ca, cp, ann, cmt), info)
                  end
                  
                  (_, pack, mp, _)  => begin
                      @match true = numError == Error.getNumErrorMessages()
                      Error.addInternalError("loadCompletePackageFromMp failed for unknown reason: mp=" + mp + " pack=" + pack, sourceInfo())
                    fail()
                  end
                end
              end
               #=  print(\"Look for \" + packagefile + \"\\n\");
               =#
               #=  print(\"Got \" + packagefile + \"\\n\");
               =#
          cl
        end

        function mergeBefore(cp::Absyn.ClassPart, cps::List{<:Absyn.ClassPart}) ::List{Absyn.ClassPart} 
              local ocp::List{Absyn.ClassPart}

              ocp = begin
                  local ei1::List{Absyn.ElementItem}
                  local ei2::List{Absyn.ElementItem}
                  local ei::List{Absyn.ElementItem}
                  local rest::List{Absyn.ClassPart}
                @match (cp, cps) begin
                  (Absyn.PUBLIC(ei1), Absyn.PUBLIC(ei2) <| rest)  => begin
                      ei = listAppend(ei1, ei2)
                    _cons(Absyn.PUBLIC(ei), rest)
                  end
                  
                  (Absyn.PROTECTED(ei1), Absyn.PROTECTED(ei2) <| rest)  => begin
                      ei = listAppend(ei1, ei2)
                    _cons(Absyn.PROTECTED(ei), rest)
                  end
                  
                  _  => begin
                      _cons(cp, cps)
                  end
                end
              end
          ocp
        end

         #= Loads a whole package from the ModelicaPaths defined in OPENMODELICALIBRARY =#
        function loadCompletePackageFromMp2(po::PackageOrder #= mo-file or directory =#, mp::String, strategy::LoadFileStrategy, w1::Absyn.Within #= With the parent added =#, encrypted::Bool = false, acc::List{<:Absyn.ClassPart}) ::List{Absyn.ClassPart} 
              local cps::List{Absyn.ClassPart}

              cps = begin
                  local ei::Absyn.ElementItem
                  local pd::String
                  local file::String
                  local id::String
                  local cp::Absyn.ClassPart
                  local cl::Absyn.Class
                  local bDirectoryAndFileExists::Bool
                @match po begin
                  CLASSPART(cp)  => begin
                      cps = mergeBefore(cp, acc)
                    cps
                  end
                  
                  ELEMENT(ei, true)  => begin
                      cps = mergeBefore(Absyn.PUBLIC(list(ei)), acc)
                    cps
                  end
                  
                  ELEMENT(ei, false)  => begin
                      cps = mergeBefore(Absyn.PROTECTED(list(ei)), acc)
                    cps
                  end
                  
                  CLASSLOAD(id)  => begin
                      pd = Autoconf.pathDelimiter
                      file = mp + pd + id + (if encrypted
                            "/package.moc"
                          else
                            "/package.mo"
                          end)
                      bDirectoryAndFileExists = System.directoryExists(mp + pd + id) && System.regularFileExists(file)
                      if bDirectoryAndFileExists
                        cl = loadCompletePackageFromMp(id, id, mp, strategy, w1, Error.getNumErrorMessages(), encrypted)
                        ei = AbsynUtil.makeClassElement(cl)
                        cps = mergeBefore(Absyn.PUBLIC(list(ei)), acc)
                      else
                        file = mp + pd + id + (if encrypted
                              ".moc"
                            else
                              ".mo"
                            end)
                        if ! System.regularFileExists(file)
                          Error.addInternalError("Expected file " + file + " to exist", sourceInfo())
                          fail()
                        end
                        cl = parsePackageFile(file, strategy, false, w1, id)
                        ei = AbsynUtil.makeClassElement(cl)
                        cps = mergeBefore(Absyn.PUBLIC(list(ei)), acc)
                      end
                    cps
                  end
                end
              end
          cps
        end

         #= Parses a file containing a single class that matches the within =#
        function parsePackageFile(name::String, strategy::LoadFileStrategy, expectPackage::Bool, w1::Absyn.Within #= Expected within of the package =#, pack::String #= Expected name of the package =#) ::Absyn.Class 
              local cl::Absyn.Class

              local cs::List{Absyn.Class}
              local w2::Absyn.Within
              local classNames::List{String}
              local info::SourceInfo
              local str::String
              local s1::String
              local s2::String
              local cname::String
              local body::Absyn.ClassDef

              @match Absyn.PROGRAM(cs, w2) = getProgramFromStrategy(name, strategy)
              classNames = ListUtil.map(cs, AbsynUtil.getClassName)
              str = stringDelimitList(classNames, ", ")
              if ! listLength(cs) == 1
                Error.addSourceMessage(Error.LIBRARY_ONE_PACKAGE_PER_FILE, list(str), SOURCEINFO(name, true, 0, 0, 0, 0, 0.0))
                fail()
              end
              @match _cons((@match Absyn.CLASS(name = cname, body = body, info = info) = cl), nil) = cs
              if ! stringEqual(cname, pack)
                if stringEqual(System.tolower(cname), System.tolower(pack))
                  Error.addSourceMessage(Error.LIBRARY_UNEXPECTED_NAME_CASE_SENSITIVE, list(pack, cname), info)
                else
                  Error.addSourceMessage(Error.LIBRARY_UNEXPECTED_NAME, list(pack, cname), info)
                  fail()
                end
              end
              s1 = AbsynUtil.withinString(w1)
              s2 = AbsynUtil.withinString(w2)
              if ! (AbsynUtil.withinEqual(w1, w2) || Config.languageStandardAtMost(Config.LanguageStandard.'2.x'))
                Error.addSourceMessage(Error.LIBRARY_UNEXPECTED_WITHIN, list(s1, s2), info)
                fail()
              elseif expectPackage && ! AbsynUtil.isParts(body)
                Error.addSourceMessage(Error.LIBRARY_EXPECTED_PARTS, list(pack), info)
                fail()
              end
          cl
        end

        function getBothPackageAndFilename(str::String, mp::String) ::String 
              local out::String

              out = Util.testsuiteFriendly(System.realpath(mp + "/" + str + ".mo")) + ", " + Util.testsuiteFriendly(System.realpath(mp + "/" + str + "/package.mo"))
          out
        end

         #= Gets the names of packages to load before the package.mo, and the ones to load after =#
        function getPackageContentNames(cl::Absyn.Class, filename::String, mp::String, numError::ModelicaInteger, encrypted::Bool = false) ::List{PackageOrder} 
              local po::List{PackageOrder} #= reverse =#

              po = begin
                  local contents::String
                  local duplicatesStr::String
                  local differencesStr::String
                  local classFilename::String
                  local duplicates::List{String}
                  local namesToFind::List{String}
                  local mofiles::List{String}
                  local subdirs::List{String}
                  local differences::List{String}
                  local intersection::List{String}
                  local caseInsensitiveFiles::List{String}
                  local cp::List{Absyn.ClassPart}
                  local info::SourceInfo
                  local po1::List{PackageOrder}
                  local po2::List{PackageOrder}
                @matchcontinue (cl, filename, mp, numError) begin
                  (Absyn.CLASS(body = Absyn.PARTS(classParts = cp), info = info), _, _, _)  => begin
                      if System.regularFileExists(filename)
                        contents = System.readFile(filename)
                        namesToFind = System.strtok(contents, "\\n")
                        namesToFind = ListUtil.removeOnTrue("", stringEqual, ListUtil.map(namesToFind, System.trimWhitespace))
                        duplicates = ListUtil.sortedDuplicates(ListUtil.sort(namesToFind, Util.strcmpBool), stringEq)
                        duplicatesStr = stringDelimitList(duplicates, ", ")
                        Error.assertionOrAddSourceMessage(listEmpty(duplicates), Error.PACKAGE_ORDER_DUPLICATES, list(duplicatesStr), SOURCEINFO(filename, true, 0, 0, 0, 0, 0.0))
                        if encrypted
                          mofiles = ListUtil.map(System.mocFiles(mp), Util.removeLast4Char)
                        else
                          mofiles = ListUtil.map(System.moFiles(mp), Util.removeLast3Char)
                        end
                        subdirs = System.subDirectories(mp)
                        subdirs = ListUtil.filter2OnTrue(subdirs, existPackage, mp, encrypted)
                        intersection = ListUtil.intersectionOnTrue(subdirs, mofiles, stringEq)
                        differencesStr = stringDelimitList(ListUtil.map1(intersection, getBothPackageAndFilename, mp), ", ")
                        Error.assertionOrAddSourceMessage(listEmpty(intersection), Error.PACKAGE_DUPLICATE_CHILDREN, list(differencesStr), SOURCEINFO(filename, true, 0, 0, 0, 0, 0.0))
                        mofiles = listAppend(subdirs, mofiles)
                        differences = ListUtil.setDifference(mofiles, namesToFind)
                        po1 = getPackageContentNamesinParts(namesToFind, cp, nil)
                        (po1, differences) = ListUtil.map3Fold(po1, checkPackageOrderFilesExist, mp, info, encrypted, differences)
                        differencesStr = stringDelimitList(differences, "\\n\\t")
                        Error.assertionOrAddSourceMessage(listEmpty(differences), Error.PACKAGE_ORDER_FILE_NOT_COMPLETE, list(differencesStr), SOURCEINFO(filename, true, 0, 0, 0, 0, 0.0))
                        po2 = ListUtil.map(differences, makeClassLoad)
                        po = listAppend(po2, po1)
                      else
                        mofiles = ListUtil.map(System.moFiles(mp), Util.removeLast3Char) #= Here .mo files in same directory as package.mo should be loaded as sub-packages =#
                        subdirs = System.subDirectories(mp)
                        subdirs = ListUtil.filter2OnTrue(subdirs, existPackage, mp, encrypted)
                        mofiles = ListUtil.sort(listAppend(subdirs, mofiles), Util.strcmpBool)
                        intersection = ListUtil.sortedDuplicates(mofiles, stringEq)
                        differencesStr = stringDelimitList(ListUtil.map1(intersection, getBothPackageAndFilename, mp), ", ")
                        Error.assertionOrAddSourceMessage(listEmpty(intersection), Error.PACKAGE_DUPLICATE_CHILDREN, list(differencesStr), info)
                        po = listAppend(ListUtil.map(cp, makeClassPart), ListUtil.map(mofiles, makeClassLoad))
                      end
                    po
                  end
                  
                  (Absyn.CLASS(info = info), _, _, _)  => begin
                      @match true = numError == Error.getNumErrorMessages()
                      Error.addSourceMessage(Error.INTERNAL_ERROR, list("getPackageContentNames failed for unknown reason"), info)
                    fail()
                  end
                end
              end
          po #= reverse =#
        end

        function makeClassPart(part::Absyn.ClassPart) ::PackageOrder 
              local po::PackageOrder

              po = CLASSPART(part)
          po
        end

        function makeElement(el::Absyn.ElementItem, pub::Bool) ::PackageOrder 
              local po::PackageOrder

              po = ELEMENT(el, pub)
          po
        end

        function makeClassLoad(str::String) ::PackageOrder 
              local po::PackageOrder

              po = CLASSLOAD(str)
          po
        end

        function checkPackageOrderFilesExist(po::PackageOrder, mp::String, info::SourceInfo, encrypted::Bool = false, differences::List{<:String}) ::Tuple{PackageOrder, List{String}} 



              _ = begin
                  local pd::String
                  local str::String
                  local str2::String
                  local str3::String
                  local str4::String
                  local strs::List{String}
                @match (po, mp, info) begin
                  (CLASSLOAD(str), _, _)  => begin
                      pd = Autoconf.pathDelimiter
                      str2 = str + (if encrypted
                            ".moc"
                          else
                            ".mo"
                          end)
                      if ! (System.directoryExists(mp + pd + str) || System.regularFileExists(mp + pd + str2))
                        try
                          str3 = ListUtil.find(System.moFiles(mp), (System.tolower(str2)) -> Util.stringEqCaseInsensitive(str2 = System.tolower(str2)))
                        catch
                          Error.addSourceMessage(Error.PACKAGE_ORDER_FILE_NOT_FOUND, list(str), info)
                          fail()
                        end
                        Error.addSourceMessage(Error.PACKAGE_ORDER_CASE_SENSITIVE, list(str, str2, str3), info)
                        str4 = Util.removeLastNChar(str3, if encrypted
                              4
                            else
                              3
                            end)
                        differences = ListUtil.removeOnTrue(str4, stringEq, differences)
                        po = CLASSLOAD(str4)
                      end
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
          (po, differences)
        end

        function existPackage(name::String, mp::String, encrypted::Bool = false) ::Bool 
              local b::Bool

              local pd::String

              pd = Autoconf.pathDelimiter
              b = System.regularFileExists(mp + pd + name + pd + (if encrypted
                    "package.moc"
                  else
                    "package.mo"
                  end))
          b
        end

        function getPackageContentNamesinParts(inNamesToSort::List{<:String}, cps::List{<:Absyn.ClassPart}, acc::List{<:PackageOrder}) ::List{PackageOrder} 
              local outOrder::List{PackageOrder} #= reverse =#

              outOrder = begin
                  local rcp::List{Absyn.ClassPart}
                  local elts::List{Absyn.ElementItem}
                  local namesToSort::List{String}
                  local cp::Absyn.ClassPart
                @match (inNamesToSort, cps, acc) begin
                  (namesToSort,  nil(), _)  => begin
                      outOrder = listAppend(ListUtil.mapReverse(namesToSort, makeClassLoad), acc)
                    outOrder
                  end
                  
                  (namesToSort, Absyn.PUBLIC(elts) <| rcp, _)  => begin
                      (outOrder, namesToSort) = getPackageContentNamesinElts(namesToSort, elts, acc, true)
                      outOrder = getPackageContentNamesinParts(namesToSort, rcp, outOrder)
                    outOrder
                  end
                  
                  (namesToSort, Absyn.PROTECTED(elts) <| rcp, _)  => begin
                      (outOrder, namesToSort) = getPackageContentNamesinElts(namesToSort, elts, acc, false)
                      outOrder = getPackageContentNamesinParts(namesToSort, rcp, outOrder)
                    outOrder
                  end
                  
                  (namesToSort, cp <| rcp, _)  => begin
                      outOrder = getPackageContentNamesinParts(namesToSort, rcp, _cons(CLASSPART(cp), acc))
                    outOrder
                  end
                end
              end
          outOrder #= reverse =#
        end

        function getPackageContentNamesinElts(inNamesToSort::List{<:String}, inElts::List{<:Absyn.ElementItem}, po::List{<:PackageOrder}, pub::Bool) ::Tuple{List{PackageOrder}, List{String}} 
              local outNames::List{String}
              local outOrder::List{PackageOrder}

              (outOrder, outNames) = begin
                  local name1::String
                  local name2::String
                  local namesToSort::List{String}
                  local names::List{String}
                  local compNames::List{String}
                  local elts::List{Absyn.ElementItem}
                  local b::Bool
                  local info::SourceInfo
                  local comps::List{Absyn.ComponentItem}
                  local ei::Absyn.ElementItem
                  local orderElt::PackageOrder
                  local load::PackageOrder
                @match (inNamesToSort, inElts, po, pub) begin
                  (namesToSort,  nil(), _, _)  => begin
                    (po, namesToSort)
                  end
                  
                  (name1 <| _, ei && Absyn.ELEMENTITEM(Absyn.ELEMENT(specification = Absyn.COMPONENTS(components = comps), info = info)) <| elts, _, _)  => begin
                      compNames = ListUtil.map(comps, AbsynUtil.componentName)
                      (names, b) = matchCompNames(inNamesToSort, compNames, info)
                      orderElt = if b
                            makeElement(ei, pub)
                          else
                            makeClassLoad(name1)
                          end
                      (outOrder, names) = getPackageContentNamesinElts(names, if b
                            elts
                          else
                            inElts
                          end, _cons(orderElt, po), pub)
                    (outOrder, names)
                  end
                  
                  (name1 <| namesToSort, ei && Absyn.ELEMENTITEM(Absyn.ELEMENT(specification = Absyn.CLASSDEF(class_ = Absyn.CLASS(name = name2, info = info)))) <| elts, _, _)  => begin
                      load = makeClassLoad(name1)
                      b = name1 == name2
                      Error.assertionOrAddSourceMessage(if b
                            ! listMember(load, po)
                          else
                            true
                          end, Error.PACKAGE_MO_NOT_IN_ORDER, list(name2), info)
                      orderElt = if b
                            makeElement(ei, pub)
                          else
                            load
                          end
                      (outOrder, names) = getPackageContentNamesinElts(namesToSort, if b
                            elts
                          else
                            inElts
                          end, _cons(orderElt, po), pub)
                    (outOrder, names)
                  end
                  
                  ( nil(), Absyn.ELEMENTITEM(Absyn.ELEMENT(specification = Absyn.CLASSDEF(class_ = Absyn.CLASS(name = name2, info = info)))) <| _, _, _)  => begin
                      load = makeClassLoad(name2)
                      Error.assertionOrAddSourceMessage(! listMember(load, po), Error.PACKAGE_MO_NOT_IN_ORDER, list(name2), info)
                      Error.addSourceMessage(Error.FOUND_ELEMENT_NOT_IN_ORDER_FILE, list(name2), info)
                    fail()
                  end
                  
                  ( nil(), Absyn.ELEMENTITEM(Absyn.ELEMENT(specification = Absyn.COMPONENTS(components = Absyn.COMPONENTITEM(component = Absyn.COMPONENT(name = name2)) <| _), info = info)) <| _, _, _)  => begin
                      load = makeClassLoad(name2)
                      Error.assertionOrAddSourceMessage(! listMember(load, po), Error.PACKAGE_MO_NOT_IN_ORDER, list(name2), info)
                      Error.addSourceMessage(Error.FOUND_ELEMENT_NOT_IN_ORDER_FILE, list(name2), info)
                    fail()
                  end
                  
                  (namesToSort, ei <| elts, _, _)  => begin
                      (outOrder, names) = getPackageContentNamesinElts(namesToSort, elts, _cons(ELEMENT(ei, pub), po), pub)
                    (outOrder, names)
                  end
                end
              end
          (outOrder, outNames)
        end

        function matchCompNames(names::List{<:String}, comps::List{<:String}, info::SourceInfo) ::Tuple{List{String}, Bool} 
              local matchedNames::Bool
              local outNames::List{String}

              (outNames, matchedNames) = begin
                  local b::Bool
                  local b1::Bool
                  local n1::String
                  local n2::String
                  local rest1::List{String}
                  local rest2::List{String}
                @match (names, comps, info) begin
                  (_,  nil(), _)  => begin
                    (names, true)
                  end
                  
                  (n1 <| rest1, n2 <| rest2, _)  => begin
                      if n1 == n2
                        (rest1, b) = matchCompNames(rest1, rest2, info)
                        Error.assertionOrAddSourceMessage(b, Error.ORDER_FILE_COMPONENTS, nil, info)
                        b1 = true
                      else
                        b1 = false
                      end
                    (rest1, b1)
                  end
                end
              end
          (outNames, matchedNames)
        end

        function packageOrderName(ord::PackageOrder) ::String 
              local name::String

              name = begin
                @match ord begin
                  CLASSLOAD(name)  => begin
                    name
                  end
                  
                  _  => begin
                      "#"
                  end
                end
              end
          name
        end

         #= Checks annotation __OpenModelica_messageOnLoad for a message to display =#
        function checkOnLoadMessage(p1::Absyn.Program)  
              local classes::List{Absyn.Class}

              @match Absyn.PROGRAM(classes = classes) = p1
              _ = ListUtil.map2(classes, AbsynUtil.getNamedAnnotationInClass, Absyn.IDENT("__OpenModelica_messageOnLoad"), checkOnLoadMessageWork)
        end

         #= Checks annotation __OpenModelica_messageOnLoad for a message to display =#
        function checkOnLoadMessageWork(mod::Option{<:Absyn.Modification}) ::ModelicaInteger 
              local dummy::ModelicaInteger

              dummy = begin
                  local str::String
                  local info::SourceInfo
                @match mod begin
                  SOME(Absyn.CLASSMOD(eqMod = Absyn.EQMOD(info = info, exp = Absyn.STRING(str))))  => begin
                      Error.addSourceMessage(Error.COMPILER_NOTIFICATION_SCRIPTING, list(str), info)
                    1
                  end
                end
              end
          dummy
        end

        function getProgramFromStrategy(filename::String, strategy::LoadFileStrategy) ::Absyn.Program 
              local program::Absyn.Program

              program = begin
                @match strategy begin
                  STRATEGY_HASHTABLE(__)  => begin
                    BaseHashTable.get(filename, strategy.ht)
                  end
                  
                  STRATEGY_ON_DEMAND(__)  => begin
                    Parser.parse(filename, strategy.encoding)
                  end
                end
              end
               #= /* if not BaseHashTable.hasKey(filename, strategy.ht) then
                        Error.addInternalError(\"HashTable missing file \" + filename + \" - all entries include:\\n\" + stringDelimitList(BaseHashTable.hashTableKeyList(ht), \"\\n\"), sourceInfo());
                        fail();
                      end if; */ =#
          program
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
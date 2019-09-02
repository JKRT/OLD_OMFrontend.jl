  module NFInstPrefix 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Prefix 

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

        import AbsynUtil

        import DAE

         @Uniontype Prefix begin
              @Record EMPTY_PREFIX begin

                       classPath #= The path of the class the prefix originates from. =#::Option{Absyn.Path}
              end

              @Record PREFIX begin

                       name::String
                       dims::DAE.Dimensions
                       restPrefix::Prefix
              end
         end

         const emptyPrefix = EMPTY_PREFIX(NONE())::Prefix

         const functionPrefix = EMPTY_PREFIX(NONE())::Prefix

         #= Creates a new prefix with one identifier. =#
        function makePrefix(inName::String, inDims::DAE.Dimensions) ::Prefix 
              local outPrefix::Prefix

              outPrefix = PREFIX(inName, inDims, emptyPrefix)
          outPrefix
        end

         #= Creates a new empty prefix with the given class path. =#
        function makeEmptyPrefix(inClassPath::Absyn.Path) ::Prefix 
              local outPrefix::Prefix

              outPrefix = EMPTY_PREFIX(SOME(inClassPath))
          outPrefix
        end

         #= Adds a new identifier to the given prefix. =#
        function add(inName::String, inDimensions::DAE.Dimensions, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = PREFIX(inName, inDimensions, inPrefix)
          outPrefix
        end

         #= Prefixes the prefix with the given path. =#
        function addPath(inPath::Absyn.Path, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = fromPath2(inPath, inPrefix)
          outPrefix
        end

        function addOptPath(inOptPath::Option{<:Absyn.Path}, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = begin
                  local p::Absyn.Path
                @match (inOptPath, inPrefix) begin
                  (NONE(), _)  => begin
                    inPrefix
                  end
                  
                  (SOME(p), _)  => begin
                    addPath(p, inPrefix)
                  end
                end
              end
          outPrefix
        end

         #= Prefixes the prefix with the given String. =#
        function addString(inName::String, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = PREFIX(inName, nil, inPrefix)
          outPrefix
        end

         #= Prefixes the prefix with the given list of strings. =#
        function addStringList(inStrings::List{<:String}, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = fromStringList2(inStrings, inPrefix)
          outPrefix
        end

         #= Discards the head of a prefix and returns the rest. =#
        function restPrefix(inPrefix::Prefix) ::Prefix 
              local outRestPrefix::Prefix

              @match PREFIX(restPrefix = outRestPrefix) = inPrefix
          outRestPrefix
        end

         #= Returns the name of the first scope of the prefix, or an empty string if the
           prefix is empty. =#
        function firstName(inPrefix::Prefix) ::String 
              local outStr::String

              outStr = begin
                  local name::String
                  local str::String
                  local rest_prefix::Prefix
                  local path::Absyn.Path
                @match inPrefix begin
                  EMPTY_PREFIX(__)  => begin
                    ""
                  end
                  
                  PREFIX(name = name)  => begin
                    name
                  end
                end
              end
          outStr
        end

         #= Applies a prefix to a cref. =#
        function prefixCref(inCref::DAE.ComponentRef, inPrefix::Prefix) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              outCref = begin
                  local name::String
                  local rest_prefix::Prefix
                  local cref::DAE.ComponentRef
                @match (inCref, inPrefix) begin
                  (_, EMPTY_PREFIX(__))  => begin
                    inCref
                  end
                  
                  (_, PREFIX(name = name, restPrefix = rest_prefix))  => begin
                      cref = DAE.CREF_QUAL(name, DAE.T_UNKNOWN_DEFAULT, nil, inCref)
                    prefixCref(cref, rest_prefix)
                  end
                end
              end
          outCref
        end

         #= Applies a prefix to a path. =#
        function prefixPath(inPath::Absyn.Path, inPrefix::Prefix) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local name::String
                  local rest_prefix::Prefix
                  local path::Absyn.Path
                @match (inPath, inPrefix) begin
                  (_, EMPTY_PREFIX(__))  => begin
                    inPath
                  end
                  
                  (_, PREFIX(name = name, restPrefix = rest_prefix))  => begin
                      path = Absyn.QUALIFIED(name, inPath)
                    prefixPath(path, rest_prefix)
                  end
                end
              end
          outPath
        end

         #= Applies a prefix to a string, using dot-notation. =#
        function prefixStr(inString::String, inPrefix::Prefix) ::String 
              local outString::String

              outString = begin
                  local str::String
                @match (inString, inPrefix) begin
                  (_, EMPTY_PREFIX(__))  => begin
                    inString
                  end
                  
                  _  => begin
                        str = toStr(inPrefix)
                        str = str + "." + inString
                      str
                  end
                end
              end
          outString
        end

         #= Converts a prefix to an untyped DAE.ComponentRef. =#
        function toCref(inPrefix::Prefix) ::DAE.ComponentRef 
              local outCref::DAE.ComponentRef

              outCref = begin
                  local name::String
                  local rest_prefix::Prefix
                  local cref::DAE.ComponentRef
                @match inPrefix begin
                  PREFIX(name = name, restPrefix = EMPTY_PREFIX(__))  => begin
                    DAE.CREF_IDENT(name, DAE.T_UNKNOWN_DEFAULT, nil)
                  end
                  
                  PREFIX(name = name, restPrefix = rest_prefix)  => begin
                      cref = DAE.CREF_IDENT(name, DAE.T_UNKNOWN_DEFAULT, nil)
                    prefixCref(cref, rest_prefix)
                  end
                end
              end
          outCref
        end

         #= Converts a prefix to a path. =#
        function toPath(inPrefix::Prefix) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local name::String
                  local rest_prefix::Prefix
                  local path::Absyn.Path
                @match inPrefix begin
                  PREFIX(name = name, restPrefix = EMPTY_PREFIX(__))  => begin
                    Absyn.IDENT(name)
                  end
                  
                  PREFIX(name = name, restPrefix = rest_prefix)  => begin
                      path = Absyn.IDENT(name)
                    prefixPath(path, rest_prefix)
                  end
                end
              end
          outPath
        end

         #= Converts a path to a prefix. =#
        function fromPath(inPath::Absyn.Path) ::Prefix 
              local outPrefix::Prefix

              outPrefix = fromPath2(inPath, emptyPrefix)
          outPrefix
        end

         #= Helper function to fromPath. =#
        function fromPath2(inPath::Absyn.Path, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = begin
                  local path::Absyn.Path
                  local name::String
                @match (inPath, inPrefix) begin
                  (Absyn.QUALIFIED(name, path), _)  => begin
                    fromPath2(path, PREFIX(name, nil, inPrefix))
                  end
                  
                  (Absyn.IDENT(name), _)  => begin
                    PREFIX(name, nil, inPrefix)
                  end
                  
                  (Absyn.FULLYQUALIFIED(path), _)  => begin
                    fromPath2(path, inPrefix)
                  end
                end
              end
          outPrefix
        end

         #= Converts a list of strings to a prefix. =#
        function fromStringList(inStrings::List{<:String}) ::Prefix 
              local outPrefix::Prefix

              outPrefix = fromStringList2(inStrings, emptyPrefix)
          outPrefix
        end

         #= Helper function to fromStringList. =#
        function fromStringList2(inStrings::List{<:String}, inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = begin
                  local strl::List{String}
                  local str::String
                @match (inStrings, inPrefix) begin
                  (str <| strl, _)  => begin
                    fromStringList2(strl, PREFIX(str, nil, inPrefix))
                  end
                  
                  _  => begin
                      inPrefix
                  end
                end
              end
          outPrefix
        end

         #= Converts a prefix to a string using dot-notation. =#
        function toStr(inPrefix::Prefix) ::String 
              local outStr::String

              outStr = begin
                  local name::String
                  local str::String
                  local rest_prefix::Prefix
                @match inPrefix begin
                  EMPTY_PREFIX(__)  => begin
                    ""
                  end
                  
                  PREFIX(name = name, restPrefix = EMPTY_PREFIX(__))  => begin
                    name
                  end
                  
                  PREFIX(name = name, restPrefix = rest_prefix)  => begin
                      str = toStr(rest_prefix) + "." + name
                    str
                  end
                end
              end
          outStr
        end

         #= Converts a prefix to a string using dot-notation, and also prints out the
           class path of the empty prefix (for e.g. debugging). =#
        function toStrWithEmpty(inPrefix::Prefix) ::String 
              local outStr::String

              outStr = begin
                  local name::String
                  local str::String
                  local rest_prefix::Prefix
                  local path::Absyn.Path
                @match inPrefix begin
                  EMPTY_PREFIX(classPath = NONE())  => begin
                    "E()"
                  end
                  
                  EMPTY_PREFIX(classPath = SOME(path))  => begin
                      str = "E(" + AbsynUtil.pathLastIdent(path) + ")"
                    str
                  end
                  
                  PREFIX(name = name, restPrefix = rest_prefix)  => begin
                      str = toStrWithEmpty(rest_prefix) + "." + name
                    str
                  end
                end
              end
          outStr
        end

         #= Returns true if the prefix is a package prefix, i.e. a prefix without an
           associated class path. =#
        function isPackagePrefix(inPrefix::Prefix) ::Bool 
              local outIsPackagePrefix::Bool

              outIsPackagePrefix = begin
                  local prefix::Prefix
                @match inPrefix begin
                  PREFIX(restPrefix = prefix)  => begin
                    isPackagePrefix(prefix)
                  end
                  
                  EMPTY_PREFIX(classPath = NONE())  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsPackagePrefix
        end

         #= Converts a prefix to a package prefix, i.e. strips it's associated class path. =#
        function toPackagePrefix(inPrefix::Prefix) ::Prefix 
              local outPrefix::Prefix

              outPrefix = begin
                  local name::String
                  local dims::DAE.Dimensions
                  local rest_prefix::Prefix
                @match inPrefix begin
                  PREFIX(name, dims, rest_prefix)  => begin
                      rest_prefix = toPackagePrefix(rest_prefix)
                    PREFIX(name, dims, rest_prefix)
                  end
                  
                  EMPTY_PREFIX(__)  => begin
                    EMPTY_PREFIX(NONE())
                  end
                end
              end
          outPrefix
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
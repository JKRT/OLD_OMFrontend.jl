  module Patternm


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#


    Func = Function

    Func = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    FuncExpType = Function

    Type_a = Any

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
        @importDBG Absyn
        @importDBG AbsynUtil
        @importDBG Ceval
        @importDBG ClassInf
        @importDBG ConnectionGraph
        @importDBG DAE
        @importDBG FCore
        @importDBG FGraphUtil
        @importDBG HashTableStringToPath
        @importDBG SCode
        @importDBG Dump
        @importDBG InnerOuterTypes
        @importDBG Prefix
        @importDBG Types
        @importDBG UnitAbsyn

        @importDBG Algorithm
        @importDBG AvlSetString
        @importDBG BaseHashTable
        @importDBG CrefForHashTable
        # @importDBG Connect
        # @importDBG DAEUtil
        @importDBG ElementSource
        @importDBG Expression
        #@importDBG ExpressionDump
        @importDBG Error
        @importDBG ErrorExt
        @importDBG Flags
        @importDBG FGraph
        @importDBG Inst
        @importDBG InstSection
        @importDBG InstTypes
        @importDBG InstUtil
        @importDBG ListUtil
        @importDBG Lookup
        import MetaModelica.Dangerous
        @importDBG AbsynToSCode
        @importDBG SCodeUtil
        @importDBG Static
        @importDBG System
        @importDBG Util
        @importDBG SCodeDump

         #= author: KS
          This function is used in the following cases:
          v := matchcontinue (x)
              case REC(a=1,b=2)
              ...
          The named arguments a=1 and b=2 must be sorted and transformed into
          positional arguments (a,b is not necessarely the correct order).
         =#
        function generatePositionalArgs(fieldNameList::List{<:Absyn.Ident}, namedArgList::List{<:Absyn.NamedArg}, accList::List{<:Absyn.Exp}) ::Tuple{List{Absyn.Exp}, List{Absyn.NamedArg}}
              local outInvalidNames::List{Absyn.NamedArg}
              local outList::List{Absyn.Exp}

              (outList, outInvalidNames) = begin
                  local localAccList::List{Absyn.Exp}
                  local restFieldNames::List{Absyn.Ident}
                  local firstFieldName::Absyn.Ident
                  local exp::Absyn.Exp
                  local localNamedArgList::List{Absyn.NamedArg}
                @match (fieldNameList, namedArgList, accList) begin
                  ( nil(), _, localAccList)  => begin
                    (listReverse(localAccList), namedArgList)
                  end

                  (firstFieldName <| restFieldNames, localNamedArgList, localAccList)  => begin
                      (exp, localNamedArgList) = findFieldExpInList(firstFieldName, localNamedArgList)
                      (localAccList, localNamedArgList) = generatePositionalArgs(restFieldNames, localNamedArgList, _cons(exp, localAccList))
                    (localAccList, localNamedArgList)
                  end
                end
              end
          (outList, outInvalidNames)
        end

         #= author: KS
          Helper function to generatePositionalArgs
         =#
        function findFieldExpInList(firstFieldName::Absyn.Ident, namedArgList::List{<:Absyn.NamedArg}) ::Tuple{Absyn.Exp, List{Absyn.NamedArg}}
              local outNamedArgList::List{Absyn.NamedArg}
              local outExp::Absyn.Exp

              (outExp, outNamedArgList) = begin
                  local e::Absyn.Exp
                  local localFieldName::Absyn.Ident
                  local aName::Absyn.Ident
                  local rest::List{Absyn.NamedArg}
                  local first::Absyn.NamedArg
                @matchcontinue (firstFieldName, namedArgList) begin
                  (_,  nil())  => begin
                    (Absyn.CREF(Absyn.WILD()), nil)
                  end

                  (localFieldName, Absyn.NAMEDARG(aName, e) <| rest)  => begin
                      @match true = stringEq(localFieldName, aName)
                    (e, rest)
                  end

                  (localFieldName, first <| rest)  => begin
                      (e, rest) = findFieldExpInList(localFieldName, rest)
                    (e, _cons(first, rest))
                  end
                end
              end
          (outExp, outNamedArgList)
        end

         #= Checks that there are no invalid named arguments in the pattern =#
        function checkInvalidPatternNamedArgs(args::List{<:Absyn.NamedArg}, fieldNameList::List{<:String}, status::Util.Status, info::SourceInfo) ::Util.Status
              local outStatus::Util.Status

              outStatus = begin
                  local argsNames::List{String}
                  local str1::String
                  local str2::String
                @match (args, fieldNameList, status, info) begin
                  ( nil(), _, _, _)  => begin
                    status
                  end

                  _  => begin
                        (argsNames, _) = AbsynUtil.getNamedFuncArgNamesAndValues(args)
                        str1 = stringDelimitList(argsNames, ",")
                        str2 = stringDelimitList(fieldNameList, ",")
                        Error.addSourceMessage(Error.META_INVALID_PATTERN_NAMED_FIELD, list(str1, str2), info)
                      Util.FAILURE()
                  end
                end
              end
          outStatus
        end

        function elabPatternCheckDuplicateBindings(cache::FCore.Cache, env::FCore.Graph, lhs::Absyn.Exp, ty::DAE.Type, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Pattern}
              local pattern::DAE.Pattern
              local outCache::FCore.Cache

              (outCache, pattern) = elabPattern2(cache, env, lhs, ty, info, Error.getNumErrorMessages())
              checkPatternsDuplicateAsBindings(_cons(pattern, nil), info)
          (outCache, pattern)
        end

        function elabPattern(cache::FCore.Cache, env::FCore.Graph, lhs::Absyn.Exp, ty::DAE.Type, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Pattern}
              local pattern::DAE.Pattern
              local outCache::FCore.Cache

              (outCache, pattern) = elabPattern2(cache, env, lhs, ty, info, Error.getNumErrorMessages())
          (outCache, pattern)
        end

        function checkPatternsDuplicateAsBindings(patterns::List{<:DAE.Pattern}, info::SourceInfo)
              local usedVariables::List{String}

              (_, usedVariables) = traversePatternList(patterns, findBoundVariables, nil)
              usedVariables = ListUtil.sortedUniqueOnlyDuplicates(ListUtil.sort(usedVariables, Util.strcmpBool), stringEq)
              if ! listEmpty(usedVariables)
                Error.addSourceMessage(Error.DUPLICATE_DEFINITION, list(stringDelimitList(usedVariables, ", ")), info)
                fail()
              end
        end

        function findBoundVariables(pat::DAE.Pattern, boundVars::List{<:String}) ::Tuple{DAE.Pattern, List{String}}
              local outBoundVars::List{String}
              local outPat::DAE.Pattern = pat

              outBoundVars = begin
                @match pat begin
                  DAE.PAT_AS(__)  => begin
                    _cons(pat.id, boundVars)
                  end

                  DAE.PAT_AS_FUNC_PTR(__)  => begin
                    _cons(pat.id, boundVars)
                  end

                  _  => begin
                      boundVars
                  end
                end
              end
          (outPat, outBoundVars)
        end

        function elabPattern2(inCache::FCore.Cache, env::FCore.Graph, inLhs::Absyn.Exp, ty::DAE.Type, info::SourceInfo, numError::ModelicaInteger) ::Tuple{FCore.Cache, DAE.Pattern}
              local pattern::DAE.Pattern
              local outCache::FCore.Cache

              (outCache, pattern) = begin
                  local exps::List{Absyn.Exp}
                  local tys::List{DAE.Type}
                  local patterns::List{DAE.Pattern}
                  local exp::Absyn.Exp
                  local head::Absyn.Exp
                  local tail::Absyn.Exp
                  local id::String
                  local s::String
                  local str::String
                  local i::ModelicaInteger
                  local r::ModelicaReal
                  local b::Bool
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                  local tyHead::DAE.Type
                  local tyTail::DAE.Type
                  local et::Option{DAE.Type}
                  local patternHead::DAE.Pattern
                  local patternTail::DAE.Pattern
                  local fcr::Absyn.ComponentRef
                  local fargs::Absyn.FunctionArgs
                  local utPath::Absyn.Path
                  local cache::FCore.Cache
                  local lhs::Absyn.Exp
                  local attr::DAE.Attributes
                  local elabExp::DAE.Exp
                  local prop::DAE.Properties
                  local constVar::DAE.Const
                  local val::Values.Value
                  local variability::SCode.Variability
                @matchcontinue (inCache, env, inLhs, ty, info, numError) begin
                  (cache, _, Absyn.INTEGER(i), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_INTEGER_DEFAULT, inLhs, info)
                    (cache, DAE.PAT_CONSTANT(et, DAE.ICONST(i)))
                  end

                  (cache, _, Absyn.REAL(str), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_REAL_DEFAULT, inLhs, info)
                      r = stringReal(str)
                    (cache, DAE.PAT_CONSTANT(et, DAE.RCONST(r)))
                  end

                  (cache, _, Absyn.UNARY(Absyn.UMINUS(__), Absyn.INTEGER(i)), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_INTEGER_DEFAULT, inLhs, info)
                      i = -i
                    (cache, DAE.PAT_CONSTANT(et, DAE.ICONST(i)))
                  end

                  (cache, _, Absyn.UNARY(Absyn.UMINUS(__), Absyn.REAL(str)), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_REAL_DEFAULT, inLhs, info)
                      r = stringReal(str)
                      r = realNeg(r)
                    (cache, DAE.PAT_CONSTANT(et, DAE.RCONST(r)))
                  end

                  (cache, _, Absyn.STRING(s), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_STRING_DEFAULT, inLhs, info)
                      s = System.unescapedString(s)
                    (cache, DAE.PAT_CONSTANT(et, DAE.SCONST(s)))
                  end

                  (cache, _, Absyn.BOOL(b), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_BOOL_DEFAULT, inLhs, info)
                    (cache, DAE.PAT_CONSTANT(et, DAE.BCONST(b)))
                  end

                  (cache, _, Absyn.ARRAY( nil()), _, _, _)  => begin
                      et = validPatternType(ty, DAE.T_METALIST_DEFAULT, inLhs, info)
                    (cache, DAE.PAT_CONSTANT(et, DAE.LIST(nil)))
                  end

                  (cache, _, Absyn.ARRAY(exps && _ <| _), _, _, _)  => begin
                      lhs = ListUtil.fold(listReverse(exps), AbsynUtil.makeCons, Absyn.ARRAY(nil))
                      (cache, pattern) = elabPattern(cache, env, lhs, ty, info)
                    (cache, pattern)
                  end

                  (cache, _, Absyn.CALL(Absyn.CREF_IDENT("NONE",  nil()), Absyn.FUNCTIONARGS( nil(),  nil())), _, _, _)  => begin
                      validPatternType(ty, DAE.T_NONE_DEFAULT, inLhs, info)
                    (cache, DAE.PAT_CONSTANT(NONE(), DAE.META_OPTION(NONE())))
                  end

                  (cache, _, Absyn.CALL(Absyn.CREF_IDENT("SOME",  nil()), Absyn.FUNCTIONARGS(exp <|  nil(),  nil())), DAE.T_METAOPTION(ty = ty2), _, _)  => begin
                      (cache, pattern) = elabPattern(cache, env, exp, ty2, info)
                    (cache, DAE.PAT_SOME(pattern))
                  end

                  (cache, _, Absyn.CONS(head, tail), tyTail && DAE.T_METALIST(ty = tyHead), _, _)  => begin
                      tyHead = Types.boxIfUnboxedType(tyHead)
                      (cache, patternHead) = elabPattern(cache, env, head, tyHead, info)
                      (cache, patternTail) = elabPattern(cache, env, tail, tyTail, info)
                    (cache, DAE.PAT_CONS(patternHead, patternTail))
                  end

                  (cache, _, Absyn.TUPLE(exps), DAE.T_METATUPLE(types = tys), _, _)  => begin
                      tys = ListUtil.map(tys, Types.boxIfUnboxedType)
                      (cache, patterns) = elabPatternTuple(cache, env, exps, tys, info, inLhs)
                    (cache, DAE.PAT_META_TUPLE(patterns))
                  end

                  (cache, _, Absyn.TUPLE(exps), DAE.T_TUPLE(types = tys), _, _)  => begin
                      (cache, patterns) = elabPatternTuple(cache, env, exps, tys, info, inLhs)
                    (cache, DAE.PAT_CALL_TUPLE(patterns))
                  end

                  (cache, _, lhs && Absyn.CALL(fcr, fargs), DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(utPath)), _, _)  => begin
                      (cache, pattern) = elabPatternCall(cache, env, AbsynUtil.crefToPath(fcr), fargs, utPath, info, lhs)
                    (cache, pattern)
                  end

                  (cache, _, lhs && Absyn.CALL(fcr, fargs), DAE.T_METAUNIONTYPE(path = utPath), _, _)  => begin
                      (cache, pattern) = elabPatternCall(cache, env, AbsynUtil.crefToPath(fcr), fargs, utPath, info, lhs)
                    (cache, pattern)
                  end

                  (cache, _, lhs && Absyn.CALL(fcr, fargs), DAE.T_METARECORD(utPath = utPath), _, _)  => begin
                      (cache, pattern) = elabPatternCall(cache, env, AbsynUtil.crefToPath(fcr), fargs, utPath, info, lhs)
                    (cache, pattern)
                  end

                  (cache, _, Absyn.CREF(__), ty1, _, _) where (Types.isBoxedType(ty1) || begin
                    @match Types.unboxedType(ty1) begin
                      DAE.T_ENUMERATION(__)  => begin
                        true
                      end

                      DAE.T_INTEGER(__)  => begin
                        true
                      end

                      DAE.T_REAL(__)  => begin
                        true
                      end

                      DAE.T_STRING(__)  => begin
                        true
                      end

                      DAE.T_BOOL(__)  => begin
                        true
                      end

                      _  => begin
                          false
                      end
                    end
                  end)  => begin
                      @match (cache, elabExp, DAE.PROP(type_ = ty2, constFlag = constType)) = Static.elabExp(cache, env, inLhs, false, false, Prefix.NOPRE(), info)
                      et = validPatternType(ty1, ty2, inLhs, info)
                      @match true = Types.isConstant(constType)
                      (cache, val) = Ceval.ceval(cache, env, elabExp, false, inMsg = Absyn.MSG(info))
                      elabExp = ValuesUtil.valueExp(val)
                    (cache, DAE.PAT_CONSTANT(et, elabExp))
                  end

                  (cache, _, Absyn.AS(id, exp), ty2, _, _)  => begin
                      @match (cache, DAE.TYPES_VAR(ty = ty1, attributes = attr), _, _, _, _) = Lookup.lookupIdent(cache, env, id)
                      lhs = Absyn.CREF(Absyn.CREF_IDENT(id, nil))
                      Static.checkAssignmentToInput(lhs, attr, env, false, info)
                      et = validPatternType(ty2, ty1, inLhs, info)
                      (cache, pattern) = elabPattern(cache, env, exp, ty2, info)
                      pattern = if Types.isFunctionType(ty2)
                            DAE.PAT_AS_FUNC_PTR(id, pattern)
                          else
                            DAE.PAT_AS(id, et, attr, pattern)
                          end
                    (cache, pattern)
                  end

                  (cache, _, Absyn.CREF(Absyn.CREF_IDENT(id,  nil())), ty2, _, _)  => begin
                      @match (cache, DAE.TYPES_VAR(ty = ty1, attributes = (@match DAE.ATTR(variability = variability) = attr)), _, _, _, _) = Lookup.lookupIdent(cache, env, id)
                      if SCodeUtil.isParameterOrConst(variability)
                        Error.addSourceMessage(Error.PATTERN_VAR_NOT_VARIABLE, list(id, SCodeDump.unparseVariability(variability)), info)
                        fail()
                      end
                      Static.checkAssignmentToInput(inLhs, attr, env, false, info)
                      et = validPatternType(ty2, ty1, inLhs, info)
                      pattern = if Types.isFunctionType(ty2)
                            DAE.PAT_AS_FUNC_PTR(id, DAE.PAT_WILD())
                          else
                            DAE.PAT_AS(id, et, attr, DAE.PAT_WILD())
                          end
                    (cache, pattern)
                  end

                  (cache, _, Absyn.AS(id, _), _, _, _)  => begin
                      @shouldFail (_, _, _, _, _, _) = Lookup.lookupIdent(cache, env, id)
                      Error.addSourceMessage(Error.LOOKUP_VARIABLE_ERROR, list(id, ""), info)
                    fail()
                  end

                  (cache, _, Absyn.CREF(Absyn.CREF_IDENT("NONE",  nil())), _, _, _)  => begin
                      @shouldFail (_, _, _, _, _, _) = Lookup.lookupIdent(cache, env, "NONE")
                      Error.addSourceMessage(Error.META_NONE_CREF, nil, info)
                    fail()
                  end

                  (cache, _, Absyn.CREF(Absyn.CREF_IDENT(id,  nil())), _, _, _)  => begin
                      @shouldFail (_, _, _, _, _, _) = Lookup.lookupIdent(cache, env, id)
                      @match false = "NONE" == id
                      Error.addSourceMessage(Error.LOOKUP_VARIABLE_ERROR, list(id, ""), info)
                    fail()
                  end

                  (cache, _, Absyn.CREF(Absyn.WILD(__)), _, _, _)  => begin
                    (cache, DAE.PAT_WILD())
                  end

                  (_, _, lhs, _, _, _)  => begin
                      @match true = numError == Error.getNumErrorMessages()
                      str = Dump.printExpStr(lhs) + " of type " + Types.unparseType(ty)
                      Error.addSourceMessage(Error.META_INVALID_PATTERN, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, pattern)
        end

        function elabPatternTuple(inCache::FCore.Cache, env::FCore.Graph, inExps::List{<:Absyn.Exp}, inTys::List{<:DAE.Type}, info::SourceInfo, lhs::Absyn.Exp #= for error messages =#) ::Tuple{FCore.Cache, List{DAE.Pattern}}
              local patterns::List{DAE.Pattern}
              local outCache::FCore.Cache

              (outCache, patterns) = begin
                  local exp::Absyn.Exp
                  local s::String
                  local pattern::DAE.Pattern
                  local ty::DAE.Type
                  local cache::FCore.Cache
                  local exps::List{Absyn.Exp}
                  local tys::List{DAE.Type}
                @match (inCache, env, inExps, inTys, info, lhs) begin
                  (cache, _,  nil(),  nil(), _, _)  => begin
                    (cache, nil)
                  end

                  (cache, _, exp <| exps, ty <| tys, _, _)  => begin
                      (cache, pattern) = elabPattern(cache, env, exp, ty, info)
                      (cache, patterns) = elabPatternTuple(cache, env, exps, tys, info, lhs)
                    (cache, _cons(pattern, patterns))
                  end

                  _  => begin
                        s = Dump.printExpStr(lhs)
                        s = "pattern " + s
                        Error.addSourceMessage(Error.WRONG_NO_OF_ARGS, list(s), info)
                      fail()
                  end
                end
              end
          (outCache, patterns)
        end

        function elabPatternCall(inCache::FCore.Cache, env::FCore.Graph, callPath::Absyn.Path, fargs::Absyn.FunctionArgs, utPath::Absyn.Path, info::SourceInfo, lhs::Absyn.Exp #= for error messages =#) ::Tuple{FCore.Cache, DAE.Pattern}
              local pattern::DAE.Pattern
              local outCache::FCore.Cache

              (outCache, pattern) = begin
                  local s::String
                  local t::DAE.Type
                  local utPath1::Absyn.Path
                  local utPath2::Absyn.Path
                  local fqPath::Absyn.Path
                  local index::ModelicaInteger
                  local numPosArgs::ModelicaInteger
                  local namedArgList::List{Absyn.NamedArg}
                  local invalidArgs::List{Absyn.NamedArg}
                  local funcArgsNamedFixed::List{Absyn.Exp}
                  local funcArgs::List{Absyn.Exp}
                  local funcArgs2::List{Absyn.Exp}
                  local fieldNameList::List{String}
                  local fieldNamesNamed::List{String}
                  local fieldTypeList::List{DAE.Type}
                  local typeVars::List{DAE.Type}
                  local fieldVarList::List{DAE.Var}
                  local patterns::List{DAE.Pattern}
                  local namedPatterns::List{Tuple{DAE.Pattern, String, DAE.Type}}
                  local knownSingleton::Bool
                  local cache::FCore.Cache
                  local allWild::Bool
                @matchcontinue (inCache, env, callPath, fargs, utPath, info, lhs) begin
                  (_, _, _, Absyn.FUNCTIONARGS(_ <| _, _ <| _), _, _, _)  => begin
                      Error.addSourceMessage(Error.PATTERN_MIXED_POS_NAMED, list(AbsynUtil.pathString(callPath)), info)
                    fail()
                  end

                  (cache, _, _, Absyn.FUNCTIONARGS(funcArgs, namedArgList), utPath2, _, _)  => begin
                      (cache, _, _) = Lookup.lookupType(cache, env, callPath, NONE())
                      @match (cache, DAE.T_METARECORD(utPath = utPath1, index = index, fields = fieldVarList, typeVars = typeVars, knownSingleton = knownSingleton, path = fqPath), _) = Lookup.lookupType(cache, env, callPath, NONE())
                      validUniontype(utPath1, utPath2, info, lhs)
                      fieldTypeList = ListUtil.map(fieldVarList, Types.getVarType)
                      fieldNameList = ListUtil.map(fieldVarList, Types.getVarName)
                      if Flags.isSet(Flags.PATTERNM_ALL_INFO)
                        for namedArg in namedArgList
                          _ = begin
                            @match namedArg begin
                              Absyn.NAMEDARG(argValue = Absyn.CREF(Absyn.WILD(__)))  => begin
                                  Error.addSourceMessage(Error.META_EMPTY_CALL_PATTERN, list(namedArg.argName), info)
                                ()
                              end

                              _  => begin
                                  ()
                              end
                            end
                          end
                        end
                        if listEmpty(namedArgList) && ! listEmpty(funcArgs)
                          allWild = true
                          for arg in funcArgs
                            allWild = begin
                              @match arg begin
                                Absyn.CREF(Absyn.WILD(__))  => begin
                                  true
                                end

                                _  => begin
                                    false
                                end
                              end
                            end
                            if ! allWild
                              break
                            end
                          end
                          if allWild
                            Error.addSourceMessage(Error.META_ALL_EMPTY, list(AbsynUtil.pathString(callPath)), info)
                          end
                        end
                      end
                      (funcArgs, namedArgList) = checkForAllWildCall(funcArgs, namedArgList, listLength(fieldNameList))
                      numPosArgs = listLength(funcArgs)
                      (_, fieldNamesNamed) = ListUtil.split(fieldNameList, numPosArgs)
                      checkMissingArgs(fqPath, numPosArgs, fieldNamesNamed, listLength(namedArgList), info)
                      (funcArgsNamedFixed, invalidArgs) = generatePositionalArgs(fieldNamesNamed, namedArgList, nil)
                      funcArgs2 = listAppend(funcArgs, funcArgsNamedFixed)
                      @match Util.SUCCESS() = checkInvalidPatternNamedArgs(invalidArgs, fieldNameList, Util.SUCCESS(), info)
                      (cache, patterns) = elabPatternTuple(cache, env, funcArgs2, fieldTypeList, info, lhs)
                    (cache, DAE.PAT_CALL(fqPath, index, patterns, fieldVarList, typeVars, knownSingleton))
                  end

                  (cache, _, _, Absyn.FUNCTIONARGS(funcArgs, namedArgList), utPath2, _, _)  => begin
                      @match (cache, DAE.T_FUNCTION(funcResultType = DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_), varLst = fieldVarList), path = fqPath), _) = Lookup.lookupType(cache, env, callPath, NONE())
                      @match true = AbsynUtil.pathEqual(fqPath, utPath2)
                      fieldTypeList = ListUtil.map(fieldVarList, Types.getVarType)
                      fieldNameList = ListUtil.map(fieldVarList, Types.getVarName)
                      (funcArgs, namedArgList) = checkForAllWildCall(funcArgs, namedArgList, listLength(fieldNameList))
                      numPosArgs = listLength(funcArgs)
                      (_, fieldNamesNamed) = ListUtil.split(fieldNameList, numPosArgs)
                      checkMissingArgs(fqPath, numPosArgs, fieldNamesNamed, listLength(namedArgList), info)
                      (funcArgsNamedFixed, invalidArgs) = generatePositionalArgs(fieldNamesNamed, namedArgList, nil)
                      funcArgs2 = listAppend(funcArgs, funcArgsNamedFixed)
                      @match Util.SUCCESS() = checkInvalidPatternNamedArgs(invalidArgs, fieldNameList, Util.SUCCESS(), info)
                      (cache, patterns) = elabPatternTuple(cache, env, funcArgs2, fieldTypeList, info, lhs)
                      namedPatterns = ListUtil.thread3Tuple(patterns, fieldNameList, ListUtil.map(fieldTypeList, Types.simplifyType))
                      namedPatterns = ListUtil.filterOnTrue(namedPatterns, filterEmptyPattern)
                    (cache, DAE.PAT_CALL_NAMED(fqPath, namedPatterns))
                  end

                  (cache, _, _, _, _, _, _)  => begin
                      @shouldFail (_, _, _) = Lookup.lookupType(cache, env, callPath, NONE())
                      s = AbsynUtil.pathString(callPath)
                      Error.addSourceMessage(Error.META_CONSTRUCTOR_NOT_RECORD, list(s), info)
                    fail()
                  end
                end
              end
          (outCache, pattern)
        end

        function checkMissingArgs(path::Absyn.Path, numPosArgs::ModelicaInteger, missingFieldNames::List{<:String}, numNamedArgs::ModelicaInteger, info::SourceInfo)
              _ = begin
                  local str::String
                  local strs::List{String}
                @match (path, numPosArgs, missingFieldNames, numNamedArgs, info) begin
                  (_, _,  nil(), 0, _)  => begin
                    ()
                  end

                  _  => begin
                      ()
                  end
                end
              end
               #= /* Language extension to not have to bind everything...
                  case (_,_,strs,0,_)
                    equation
                      str = stringDelimitList(strs,\",\");
                      str = AbsynUtil.pathString(path) + \" missing pattern for fields: \" + str;
                      Error.addSourceMessage(Error.META_INVALID_PATTERN,{str},info);
                    then fail();
              */ =#
               #= /*
                  case (path,_,_,_,info)
                    equation
                      str = AbsynUtil.pathString(path) + \" mixing positional and named patterns\";
                      Error.addSourceMessage(Error.META_INVALID_PATTERN,{str},info);
                    then fail();
                  */ =#
        end

         #= Converts a call REC(__) to REC(_,_,_,_) =#
        function checkForAllWildCall(args::List{<:Absyn.Exp}, named::List{<:Absyn.NamedArg}, numFields::ModelicaInteger) ::Tuple{List{Absyn.Exp}, List{Absyn.NamedArg}}
              local outNamed::List{Absyn.NamedArg}
              local outArgs::List{Absyn.Exp}

              (outArgs, outNamed) = begin
                @match (args, named, numFields) begin
                  (Absyn.CREF(Absyn.ALLWILD(__)) <|  nil(),  nil(), _)  => begin
                    (nil, nil)
                  end

                  _  => begin
                      (args, named)
                  end
                end
              end
          (outArgs, outNamed)
        end

        function validPatternType(inTy1::DAE.Type, inTy2::DAE.Type, lhs::Absyn.Exp, info::SourceInfo) ::Option{DAE.Type}
              local ty::Option{DAE.Type}

              ty = begin
                  local et::DAE.Type
                  local s::String
                  local s1::String
                  local s2::String
                  local cr::DAE.ComponentRef
                  local crefExp::DAE.Exp
                  local ty1::DAE.Type
                  local ty2::DAE.Type
                @matchcontinue (inTy1, inTy2, lhs, info) begin
                  (DAE.T_METABOXED(ty = ty1), ty2, _, _)  => begin
                      cr = CrefForHashTable.makeCrefIdent("#DUMMY#", DAE.T_UNKNOWN_DEFAULT, nil)
                      crefExp = Expression.crefExp(cr)
                      (_, ty1) = Types.matchType(crefExp, ty1, ty2, true)
                      et = Types.simplifyType(ty1)
                    SOME(et)
                  end

                  (ty1, ty2, _, _)  => begin
                      cr = CrefForHashTable.makeCrefIdent("#DUMMY#", DAE.T_UNKNOWN_DEFAULT, nil)
                      crefExp = Expression.crefExp(cr)
                      (_, _) = Types.matchType(crefExp, ty1, ty2, true)
                    NONE()
                  end

                  (ty1, ty2, _, _)  => begin
                      s = Dump.printExpStr(lhs)
                      s1 = Types.unparseType(ty1)
                      s2 = Types.unparseType(ty2)
                      Error.addSourceMessage(Error.META_TYPE_MISMATCH_PATTERN, list(s, s1, s2), info)
                    fail()
                  end
                end
              end
          ty
        end

        function validUniontype(path1::Absyn.Path, path2::Absyn.Path, info::SourceInfo, lhs::Absyn.Exp)
              _ = begin
                  local s::String
                  local s1::String
                  local s2::String
                @matchcontinue (path1, path2, info, lhs) begin
                  (_, _, _, _)  => begin
                      @match true = AbsynUtil.pathEqual(path1, path2)
                    ()
                  end

                  _  => begin
                        s = Dump.printExpStr(lhs)
                        s1 = AbsynUtil.pathString(path1)
                        s2 = AbsynUtil.pathString(path2)
                        Error.addSourceMessage(Error.META_CONSTRUCTOR_NOT_PART_OF_UNIONTYPE, list(s, s1, s2), info)
                      fail()
                  end
                end
              end
        end

         #= Pattern to String unparsing =#
        function patternStr(pattern::DAE.Pattern) ::String
              local str::String

              str = begin
                  local pats::List{DAE.Pattern}
                  local fields::List{String}
                  local patsStr::List{String}
                  local exp::DAE.Exp
                  local pat::DAE.Pattern
                  local head::DAE.Pattern
                  local tail::DAE.Pattern
                  local id::String
                  local namedpats::List{Tuple{DAE.Pattern, String, DAE.Type}}
                  local name::Absyn.Path
                @matchcontinue pattern begin
                  DAE.PAT_WILD(__)  => begin
                    "_"
                  end

                  DAE.PAT_AS(id = id, pat = DAE.PAT_WILD(__))  => begin
                    id
                  end

                  DAE.PAT_AS_FUNC_PTR(id, DAE.PAT_WILD(__))  => begin
                    id
                  end

                  DAE.PAT_SOME(pat)  => begin
                      str = patternStr(pat)
                    "SOME(" + str + ")"
                  end

                  DAE.PAT_META_TUPLE(pats)  => begin
                      str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                    "(" + str + ")"
                  end

                  DAE.PAT_CALL_TUPLE(pats)  => begin
                      str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                    "(" + str + ")"
                  end

                  DAE.PAT_CALL(name = name, patterns = pats)  => begin
                      id = AbsynUtil.pathString(name)
                      str = stringDelimitList(ListUtil.map(pats, patternStr), ",")
                    stringAppendList(list(id, "(", str, ")"))
                  end

                  DAE.PAT_CALL_NAMED(name = name, patterns = namedpats)  => begin
                      id = AbsynUtil.pathString(name)
                      fields = ListUtil.map(namedpats, Util.tuple32)
                      patsStr = ListUtil.map1r(ListUtil.mapMap(namedpats, Util.tuple31, patternStr), stringAppend, "=")
                      str = stringDelimitList(ListUtil.threadMap(fields, patsStr, stringAppend), ",")
                    stringAppendList(list(id, "(", str, ")"))
                  end

                  DAE.PAT_CONS(head, tail)  => begin
                    patternStr(head) + "::" + patternStr(tail)
                  end

                  DAE.PAT_CONSTANT(exp = exp)  => begin
                    #TODO
                    #ExpressionDump.printExpStr(exp)
                    throw("TODO error")
                  end

                  DAE.PAT_AS(id = id, pat = pat)  => begin
                    id + " as " + patternStr(pat)
                  end

                  DAE.PAT_AS_FUNC_PTR(id, pat)  => begin
                    id + " as " + patternStr(pat)
                  end

                  _  => begin
                        Error.addMessage(Error.INTERNAL_ERROR, list("Patternm.patternStr not implemented correctly"))
                      "*PATTERN*"
                  end
                end
              end
               #=  case DAE.PAT_CONSTANT(SOME(et),exp) then \"(\" + Types.unparseType(et) + \")\" + ExpressionDump.printExpStr(exp);
               =#
          str
        end

        function elabMatchExpression(inCache::FCore.Cache, inEnv::FCore.Graph, matchExp::Absyn.Exp, impl::Bool, performVectorization::Bool, inPrefix::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties}
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              local numError::ModelicaInteger = Error.getNumErrorMessages()

              (outCache, outExp, outProperties) = begin
                  local matchTy::Absyn.MatchType
                  local inExp::Absyn.Exp
                  local inExps::List{Absyn.Exp}
                  local decls::List{Absyn.ElementItem}
                  local cases::List{Absyn.Case}
                  local matchDecls::List{DAE.Element}
                  local pre::Prefix.PrefixType
                  local elabExps::List{DAE.Exp}
                  local elabCases::List{DAE.MatchCase}
                  local tys::List{DAE.Type}
                  local prop::DAE.Properties
                  local elabProps::List{DAE.Properties}
                  local resType::DAE.Type
                  local et::DAE.Type
                  local str::String
                  local exp::DAE.Exp
                  local ht::HashTableStringToPath.HashTable
                  local elabMatchTy::DAE.MatchType
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local hashSize::ModelicaInteger
                  local inputAliases::List{List{String}}
                  local inputAliasesAndCrefs::List{List{String}}
                  local declsTree::AvlSetString.Tree
                @matchcontinue (inCache, inEnv, matchExp, impl, performVectorization, inPrefix, info, numError) begin
                  (cache, env, Absyn.MATCHEXP(matchTy = matchTy, inputExp = inExp, localDecls = decls, cases = cases), _, _, pre, _, _)  => begin
                      inExps = convertExpToPatterns(inExp)
                      (inExps, inputAliases, inputAliasesAndCrefs) = ListUtil.map_3(inExps, getInputAsBinding)
                      (cache, elabExps, elabProps) = Static.elabExpList(cache, env, inExps, impl, performVectorization, pre, info)
                      @match (cache, SOME((env, DAE.DAE_LIST(matchDecls), declsTree))) = addLocalDecls(cache, env, decls, FCore.matchScopeName, impl, info)
                      tys = ListUtil.map(elabProps, Types.getPropType)
                      env = addAliasesToEnv(env, tys, inputAliases, info)
                      (cache, elabCases, resType) = elabMatchCases(cache, env, cases, tys, inputAliasesAndCrefs, declsTree, impl, performVectorization, pre, info)
                      prop = DAE.PROP(resType, DAE.C_VAR())
                      et = Types.simplifyType(resType)
                      (elabExps, inputAliases, elabCases) = filterUnusedPatterns(elabExps, inputAliases, elabCases) #= filterUnusedPatterns() First time to speed up the other optimizations. =#
                      elabCases = caseDeadCodeElimination(matchTy, elabCases, nil, nil, false)
                      matchTy = optimizeContinueToMatch(matchTy, elabCases, info)
                      elabCases = optimizeContinueJumps(matchTy, elabCases)
                      hashSize = Util.nextPrime(listLength(matchDecls))
                      ht = getUsedLocalCrefs(Flags.isSet(Flags.PATTERNM_SKIP_FILTER_UNUSED_AS_BINDINGS), DAE.MATCHEXPRESSION(DAE.MATCHCONTINUE(), elabExps, inputAliases, matchDecls, elabCases, et), hashSize)
                      (matchDecls, ht) = filterUnusedDecls(matchDecls, ht, nil, HashTableStringToPath.emptyHashTableSized(hashSize))
                      (elabExps, inputAliases, elabCases) = filterUnusedPatterns(elabExps, inputAliases, elabCases) #= filterUnusedPatterns() again to filter out the last parts. =#
                      (elabMatchTy, elabCases) = optimizeMatchToSwitch(matchTy, elabCases, info)
                      checkConstantMatchInputs(elabExps, info)
                      exp = DAE.MATCHEXPRESSION(elabMatchTy, elabExps, inputAliases, matchDecls, elabCases, et)
                    (cache, exp, prop)
                  end

                  _  => begin
                        @match true = numError == Error.getNumErrorMessages()
                        str = Dump.printExpStr(matchExp)
                        Error.addSourceMessage(Error.META_MATCH_GENERAL_FAILURE, list(str), info)
                      fail()
                  end
                end
              end
               #=  First do inputs
               =#
               #=  Then add locals
               =#
               #=  Do DCE before converting mc to m
               =#
               #=  hashSize = Util.nextPowerOf2(listLength(matchDecls)) + 1;  faster, but unstable in RML
               =#
          (outCache, outExp, outProperties)
        end

        function checkConstantMatchInputs(inputs::List{<:DAE.Exp}, info::SourceInfo)
              for i in inputs
                if Expression.isConstValue(i)
                  #TODO
                  #Error.addSourceMessage(Error.META_MATCH_CONSTANT, list(ExpressionDump.printExpStr(i)), info)
                  Error.addSourceMessage(Error.META_MATCH_CONSTANT, list(string()), info)
                end
              end
        end

         #= match str case 'str1' ... case 'str2' case 'str3' => switch hash(str)...
          match ut case UT1 ... case UT2 ... case UT3 => switch valueConstructor(ut)...
          match int case 1 ... case 17 ... case 2 => switch(int)...
          Works if all values are unique. Also works if there is one 'default' case at the end of the list (and there is only 1 pattern):
            case (1,_) ... case (_,_) ... works
            case (1,2) ... case (_,_) ... does not work
          .
           =#
        function optimizeMatchToSwitch(matchTy::Absyn.MatchType, cases::List{<:DAE.MatchCase}, info::SourceInfo) ::Tuple{DAE.MatchType, List{DAE.MatchCase}}
              local outCases::List{DAE.MatchCase}
              local outType::DAE.MatchType

              (outType, outCases) = begin
                  local tpl::Tuple{ModelicaInteger, DAE.Type, ModelicaInteger}
                  local patternMatrix::List{List{DAE.Pattern}}
                  local optPatternMatrix::List{Option{List{DAE.Pattern}}}
                  local numNonEmptyColumns::ModelicaInteger
                  local str::String
                  local ty::DAE.Type
                @matchcontinue (matchTy, cases, info) begin
                  (Absyn.MATCHCONTINUE(__), _, _)  => begin
                    (DAE.MATCHCONTINUE(), cases)
                  end

                  (_, _, _)  => begin
                      @match true = listLength(cases) > 2
                      for c in cases
                        @match DAE.CASE(patternGuard = NONE()) = c
                      end
                      patternMatrix = ListUtil.transposeList(ListUtil.map(cases, getCasePatterns))
                      (optPatternMatrix, numNonEmptyColumns) = removeWildPatternColumnsFromMatrix(patternMatrix, nil, 0)
                      tpl = findPatternToConvertToSwitch(optPatternMatrix, 1, numNonEmptyColumns, info)
                      (_, ty, _) = tpl
                      str = Types.unparseType(ty)
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.MATCH_TO_SWITCH_OPTIMIZATION, list(str), info)
                      outType = DAE.MATCH(SOME(tpl))
                      outCases = optimizeSwitchedMatchCases(outType, cases)
                    (outType, outCases)
                  end

                  _  => begin
                      (DAE.MATCH(NONE()), cases)
                  end
                end
              end
          (outType, outCases)
        end

         #= This function optimizes the cases of a match that has been optimized into a switch. =#
        function optimizeSwitchedMatchCases(inMatchType::DAE.MatchType, inCases::List{<:DAE.MatchCase}) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                  local pat::DAE.Pattern
                  local patl::List{DAE.Pattern}
                   #=  If we're switching on a uniontype, mark all cases that look like RECORD()
                   =#
                   #=  as singleton, so we can skip doing pattern matching on them (we're
                   =#
                   #=  already switching on their type, we don't need to check the type in the
                   =#
                   #=  case also.
                   =#
                @match inMatchType begin
                  DAE.MATCH(switch = SOME((_, DAE.T_METATYPE(__), _)))  => begin
                    list(begin
                      @match c begin
                        DAE.CASE(patterns = pat && DAE.PAT_CALL(patterns = patl) <|  nil())  => begin
                            if allPatternsWild(patl)
                              pat.knownSingleton = true
                              c.patterns = list(pat)
                            end
                          c
                        end

                        _  => begin
                            c
                        end
                      end
                    end for c in inCases)
                  end

                  _  => begin
                      inCases
                  end
                end
              end
          outCases
        end

        function removeWildPatternColumnsFromMatrix(inPatternMatrix::List{<:List{<:DAE.Pattern}}, inAcc::List{<:Option{<:List{<:DAE.Pattern}}}, inNumAcc::ModelicaInteger) ::Tuple{List{Option{List{DAE.Pattern}}}, ModelicaInteger}
              local numNonEmptyColumns::ModelicaInteger
              local optPatternMatrix::List{Option{List{DAE.Pattern}}}

              (optPatternMatrix, numNonEmptyColumns) = begin
                  local alwaysMatch::Bool
                  local pats::List{DAE.Pattern}
                  local optPats::Option{List{DAE.Pattern}}
                  local patternMatrix::List{List{DAE.Pattern}}
                  local acc::List{Option{List{DAE.Pattern}}}
                  local numAcc::ModelicaInteger
                @match (inPatternMatrix, inAcc, inNumAcc) begin
                  ( nil(), acc, numAcc)  => begin
                    (listReverse(acc), numAcc)
                  end

                  (pats <| patternMatrix, acc, numAcc)  => begin
                      alwaysMatch = allPatternsAlwaysMatch(ListUtil.stripLast(pats))
                      optPats = if alwaysMatch
                            NONE()
                          else
                            SOME(pats)
                          end
                      numAcc = if alwaysMatch
                            numAcc
                          else
                            numAcc + 1
                          end
                      (acc, numAcc) = removeWildPatternColumnsFromMatrix(patternMatrix, _cons(optPats, acc), numAcc)
                    (acc, numAcc)
                  end
                end
              end
          (optPatternMatrix, numNonEmptyColumns)
        end

        function findPatternToConvertToSwitch(inPatternMatrix::List{<:Option{<:List{<:DAE.Pattern}}}, index::ModelicaInteger, numPatternsInMatrix::ModelicaInteger #= If there is only 1 pattern, we can optimize the default case =#, info::SourceInfo) ::Tuple{ModelicaInteger, DAE.Type, ModelicaInteger}
              local tpl::Tuple{ModelicaInteger, DAE.Type, ModelicaInteger}

              tpl = begin
                  local pats::List{DAE.Pattern}
                  local ty::DAE.Type
                  local extraarg::ModelicaInteger
                  local patternMatrix::List{Option{List{DAE.Pattern}}}
                @matchcontinue (inPatternMatrix, index, numPatternsInMatrix, info) begin
                  (SOME(pats) <| _, _, _, _)  => begin
                      (ty, extraarg) = findPatternToConvertToSwitch2(pats, nil, DAE.T_UNKNOWN_DEFAULT, true, numPatternsInMatrix)
                    (index, ty, extraarg)
                  end

                  (_ <| patternMatrix, _, _, _)  => begin
                    findPatternToConvertToSwitch(patternMatrix, index + 1, numPatternsInMatrix, info)
                  end
                end
              end
          tpl
        end

        function findPatternToConvertToSwitch2(ipats::List{<:DAE.Pattern}, ixs::List{<:ModelicaInteger}, ity::DAE.Type, allSubPatternsMatch::Bool, numPatternsInMatrix::ModelicaInteger) ::Tuple{DAE.Type, ModelicaInteger}
              local extraarg::ModelicaInteger
              local outTy::DAE.Type

              (outTy, extraarg) = begin
                  local ix::ModelicaInteger
                  local str::String
                  local pats::List{DAE.Pattern}
                  local subpats::List{DAE.Pattern}
                  local ty::DAE.Type
                @match (ipats, ixs, ity, allSubPatternsMatch, numPatternsInMatrix) begin
                  (DAE.PAT_CONSTANT(exp = DAE.SCONST(str)) <| pats, _, _, _, _)  => begin
                      ix = stringHashDjb2Mod(str, 65536)
                      @match false = listMember(ix, ixs)
                      (ty, extraarg) = findPatternToConvertToSwitch2(pats, _cons(ix, ixs), DAE.T_STRING_DEFAULT, allSubPatternsMatch, numPatternsInMatrix)
                    (ty, extraarg)
                  end

                  (DAE.PAT_CALL(index = ix, patterns = subpats) <| pats, _, _, _, _)  => begin
                      @match false = listMember(ix, ixs)
                      (ty, extraarg) = findPatternToConvertToSwitch2(pats, _cons(ix, ixs), DAE.T_METATYPE_DEFAULT, allSubPatternsMatch && allPatternsAlwaysMatch(subpats), numPatternsInMatrix)
                    (ty, extraarg)
                  end

                  (DAE.PAT_CONSTANT(exp = DAE.ICONST(ix)) <| pats, _, _, _, _)  => begin
                      @match false = listMember(ix, ixs)
                      (ty, extraarg) = findPatternToConvertToSwitch2(pats, _cons(ix, ixs), DAE.T_INTEGER_DEFAULT, allSubPatternsMatch, numPatternsInMatrix)
                    (ty, extraarg)
                  end

                  ( nil(), _, DAE.T_STRING(__), _, _)  => begin
                      @match true = listLength(ixs) > 11
                      ix = findMinMod(ixs, 1)
                    (DAE.T_STRING_DEFAULT, ix)
                  end

                  (_ <|  nil(), _, DAE.T_STRING(__), _, 1)  => begin
                      @match true = listLength(ixs) > 11
                      ix = findMinMod(ixs, 1)
                    (DAE.T_STRING_DEFAULT, ix)
                  end

                  ( nil(), _, _, _, _)  => begin
                    (ity, 0)
                  end

                  (_ <|  nil(), _, _, true, 1)  => begin
                    (ity, 0)
                  end
                end
              end
               #=  hashing has a considerable overhead, only convert to switch if it is worth it
               =#
               #=  hashing has a considerable overhead, only convert to switch if it is worth it
               =#
               #=  Sadly, we cannot switch a default uniontype as the previous case in not guaranteed
               =#
               #=  to succeed matching if it matches for subpatterns.
               =#
          (outTy, extraarg)
        end

        function findMinMod(inIxs::List{<:ModelicaInteger}, inMod::ModelicaInteger) ::ModelicaInteger
              local outMod::ModelicaInteger

              outMod = begin
                  local ixs::List{ModelicaInteger}
                  local mod::ModelicaInteger
                @matchcontinue (inIxs, inMod) begin
                  (ixs, mod)  => begin
                      ixs = ListUtil.map1(ixs, intMod, mod)
                      ixs = ListUtil.sort(ixs, intLt)
                      @match nil = ListUtil.sortedDuplicates(ixs, intEq)
                    mod
                  end

                  _  => begin
                        @match true = inMod < 65536
                      findMinMod(inIxs, inMod * 2)
                  end
                end
              end
               #=  This mod was high enough that all values were distinct
               =#
          outMod
        end

         #= case (1,_,_) then ...; case (2,_,_) then ...; => =#
        function filterUnusedPatterns(inputs::List{<:DAE.Exp} #= We can only remove inputs that are free from side-effects =#, inAliases::List{<:List{<:String}}, inCases::List{<:DAE.MatchCase}) ::Tuple{List{DAE.Exp}, List{List{String}}, List{DAE.MatchCase}}
              local outCases::List{DAE.MatchCase}
              local outAliases::List{List{String}}
              local outInputs::List{DAE.Exp}

              (outInputs, outAliases, outCases) = begin
                  local patternMatrix::List{List{DAE.Pattern}}
                  local cases::List{DAE.MatchCase}
                @matchcontinue (inputs, inAliases, inCases) begin
                  (_, _, cases)  => begin
                      patternMatrix = ListUtil.transposeList(ListUtil.map(cases, getCasePatterns))
                      @match (true, outInputs, outAliases, patternMatrix) = filterUnusedPatterns2(inputs, inAliases, patternMatrix, false, nil, nil, nil)
                      patternMatrix = ListUtil.transposeList(patternMatrix)
                      cases = setCasePatternsCheckZero(cases, patternMatrix)
                    (outInputs, outAliases, cases)
                  end

                  _  => begin
                      (inputs, inAliases, inCases)
                  end
                end
              end
          (outInputs, outAliases, outCases)
        end

         #= Handles the case when the pattern matrix becomes empty because no input is matched =#
        function setCasePatternsCheckZero(inCases::List{<:DAE.MatchCase}, patternMatrix::List{<:List{<:DAE.Pattern}}) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                @match (inCases, patternMatrix) begin
                  ( nil(),  nil())  => begin
                    inCases
                  end

                  (_,  nil())  => begin
                    ListUtil.map1(inCases, setCasePatterns, nil)
                  end

                  _  => begin
                      ListUtil.threadMap(inCases, patternMatrix, setCasePatterns)
                  end
                end
              end
          outCases
        end

         #= case (1,_,_) then ...; case (2,_,_) then ...; => =#
        function filterUnusedPatterns2(inInputs::List{<:DAE.Exp} #= We can only remove inputs that are free from side-effects =#, inAliases::List{<:List{<:String}}, inPatternMatrix::List{<:List{<:DAE.Pattern}}, change::Bool #= Only rebuild the cases if something changed =#, inputsAcc::List{<:DAE.Exp}, aliasesAcc::List{<:List{<:String}}, patternMatrixAcc::List{<:List{<:DAE.Pattern}}) ::Tuple{Bool, List{DAE.Exp}, List{List{String}}, List{List{DAE.Pattern}}}
              local outPatternMatrix::List{List{DAE.Pattern}}
              local outAliases::List{List{String}}
              local outInputs::List{DAE.Exp}
              local outChange::Bool

              (outChange, outInputs, outAliases, outPatternMatrix) = begin
                  local e::DAE.Exp
                  local pats::List{DAE.Pattern}
                  local inputs::List{DAE.Exp}
                  local patternMatrix::List{List{DAE.Pattern}}
                  local alias::List{String}
                  local aliases::List{List{String}}
                @matchcontinue (inInputs, inAliases, inPatternMatrix, change, inputsAcc, aliasesAcc, patternMatrixAcc) begin
                  ( nil(),  nil(),  nil(), true, _, _, _)  => begin
                    (true, listReverse(inputsAcc), listReverse(aliasesAcc), listReverse(patternMatrixAcc))
                  end

                  (e <| inputs, _ <| aliases, pats <| patternMatrix, _, _, _, _)  => begin
                      @match (_, true) = Expression.traverseExpBottomUp(e, Expression.hasNoSideEffects, true)
                      @match true = allPatternsWild(pats)
                      (outChange, outInputs, outAliases, outPatternMatrix) = filterUnusedPatterns2(inputs, aliases, patternMatrix, true, inputsAcc, aliasesAcc, patternMatrixAcc)
                    (outChange, outInputs, outAliases, outPatternMatrix)
                  end

                  (e <| inputs, alias <| aliases, pats <| patternMatrix, _, _, _, _)  => begin
                      (outChange, outInputs, outAliases, outPatternMatrix) = filterUnusedPatterns2(inputs, aliases, patternMatrix, change, _cons(e, inputsAcc), _cons(alias, aliasesAcc), _cons(pats, patternMatrixAcc))
                    (outChange, outInputs, outAliases, outPatternMatrix)
                  end

                  _  => begin
                      (false, nil, nil, nil)
                  end
                end
              end
          (outChange, outInputs, outAliases, outPatternMatrix)
        end

        function getUsedLocalCrefs(skipFilterUnusedAsBindings::Bool #= if true, traverse the whole expression; else only the bodies and results =#, exp::DAE.Exp, hashSize::ModelicaInteger) ::HashTableStringToPath.HashTable
              local ht::HashTableStringToPath.HashTable

              ht = begin
                  local cases::List{DAE.MatchCase}
                @match (skipFilterUnusedAsBindings, exp, hashSize) begin
                  (true, _, _)  => begin
                      (_, ht) = Expression.traverseExpBottomUp(exp, addLocalCref, HashTableStringToPath.emptyHashTableSized(hashSize))
                    ht
                  end

                  (false, DAE.MATCHEXPRESSION(cases = cases), _)  => begin
                      (_, ht) = traverseCases(cases, addLocalCref, HashTableStringToPath.emptyHashTableSized(hashSize))
                    ht
                  end
                end
              end
          ht
        end

        function filterUnusedAsBindings(inCases::List{<:DAE.MatchCase}, ht::HashTableStringToPath.HashTable) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                  local patterns::List{DAE.Pattern}
                  local localDecls::List{DAE.Element}
                  local body::List{DAE.Statement}
                  local guardPattern::Option{DAE.Exp}
                  local result::Option{DAE.Exp}
                  local jump::ModelicaInteger
                  local resultInfo::SourceInfo
                  local info::SourceInfo
                  local cases::List{DAE.MatchCase}
                @match (inCases, ht) begin
                  ( nil(), _)  => begin
                    nil
                  end

                  (DAE.CASE(patterns, guardPattern, localDecls, body, result, resultInfo, jump, info) <| cases, _)  => begin
                      (patterns, _) = traversePatternList(patterns, removePatternAsBinding, (ht, info))
                      cases = filterUnusedAsBindings(cases, ht)
                    _cons(DAE.CASE(patterns, guardPattern, localDecls, body, result, resultInfo, jump, info), cases)
                  end
                end
              end
          outCases
        end

        function removePatternAsBinding(inPat::DAE.Pattern, inTpl::Tuple{<:HashTableStringToPath.HashTable, SourceInfo}) ::Tuple{DAE.Pattern, Tuple{HashTableStringToPath.HashTable, SourceInfo}}
              local outTpl::Tuple{HashTableStringToPath.HashTable, SourceInfo} = inTpl
              local pat::DAE.Pattern = inPat

              pat = begin
                  local ht::HashTableStringToPath.HashTable
                  local id::String
                  local info::SourceInfo
                  local tpl::Tuple{HashTableStringToPath.HashTable, SourceInfo}
                @matchcontinue (pat, inTpl) begin
                  (DAE.PAT_AS(id = id, pat = pat), (ht, info))  => begin
                      @match true = BaseHashTable.hasKey(id, ht)
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_UNUSED_AS_BINDING, list(id), info)
                    pat
                  end

                  (DAE.PAT_AS_FUNC_PTR(id = id, pat = pat), (ht, _))  => begin
                      @match true = BaseHashTable.hasKey(id, ht)
                    pat
                  end

                  _  => begin
                        pat = simplifyPattern(inPat, 1)
                      pat
                  end
                end
              end
          (pat, outTpl)
        end

         #= Use with Expression.traverseExpBottomUp to collect all CREF's that could be references to local
        variables. =#
        function addLocalCref(inExp::DAE.Exp, inHt::HashTableStringToPath.HashTable) ::Tuple{DAE.Exp, HashTableStringToPath.HashTable}
              local outHt::HashTableStringToPath.HashTable
              local outExp::DAE.Exp

              (outExp, outHt) = begin
                  local exp::DAE.Exp
                  local ht::HashTableStringToPath.HashTable
                  local name::String
                  local cases::List{DAE.MatchCase}
                  local pat::DAE.Pattern
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match (inExp, inHt) begin
                  (exp && DAE.CREF(componentRef = cr), ht)  => begin
                      ht = addLocalCrefHelper(cr, ht)
                    (exp, ht)
                  end

                  (exp && DAE.CALL(path = Absyn.IDENT(name), attr = DAE.CALL_ATTR(builtin = false)), ht)  => begin
                      ht = BaseHashTable.add((name, Absyn.IDENT("")), ht)
                    (exp, ht)
                  end

                  (exp && DAE.PATTERN(pattern = pat), ht)  => begin
                      (_, ht) = traversePattern(pat, addPatternAsBindings, ht)
                    (exp, ht)
                  end

                  (exp && DAE.MATCHEXPRESSION(cases = cases), ht)  => begin
                      ht = addCasesLocalCref(cases, ht)
                    (exp, ht)
                  end

                  _  => begin
                      (inExp, inHt)
                  end
                end
              end
          (outExp, outHt)
        end

        function addLocalCrefHelper(cr::DAE.ComponentRef, iht::HashTableStringToPath.HashTable) ::HashTableStringToPath.HashTable
              local ht::HashTableStringToPath.HashTable

              ht = begin
                  local name::String
                  local subs::List{DAE.Subscript}
                  local cr2::DAE.ComponentRef
                @match (cr, iht) begin
                  (DAE.CREF_IDENT(ident = name, subscriptLst = subs), ht)  => begin
                      ht = addLocalCrefSubs(subs, ht)
                      ht = BaseHashTable.add((name, Absyn.IDENT("")), ht)
                    ht
                  end

                  (DAE.CREF_QUAL(ident = name, subscriptLst = subs, componentRef = cr2), ht)  => begin
                      ht = addLocalCrefSubs(subs, ht)
                      ht = BaseHashTable.add((name, Absyn.IDENT("")), ht)
                    addLocalCrefHelper(cr2, ht)
                  end

                  _  => begin
                      iht
                  end
                end
              end
          ht
        end

         #= Cref subscripts may also contain crefs =#
        function addLocalCrefSubs(isubs::List{<:DAE.Subscript}, iht::HashTableStringToPath.HashTable) ::HashTableStringToPath.HashTable
              local outHt::HashTableStringToPath.HashTable

              outHt = begin
                  local exp::DAE.Exp
                  local subs::List{DAE.Subscript}
                  local ht::HashTableStringToPath.HashTable
                @match (isubs, iht) begin
                  ( nil(), ht)  => begin
                    ht
                  end

                  (DAE.SLICE(exp) <| subs, ht)  => begin
                      (_, ht) = Expression.traverseExpBottomUp(exp, addLocalCref, ht)
                      ht = addLocalCrefSubs(subs, ht)
                    ht
                  end

                  (DAE.INDEX(exp) <| subs, ht)  => begin
                      (_, ht) = Expression.traverseExpBottomUp(exp, addLocalCref, ht)
                      ht = addLocalCrefSubs(subs, ht)
                    ht
                  end

                  _  => begin
                      iht
                  end
                end
              end
          outHt
        end

         #= Use with Expression.traverseExpBottomUp to collect all CREF's that could be references to local
        variables. =#
        function checkDefUse(inExp::DAE.Exp, inTpl::Tuple{<:AvlSetString.Tree, AvlSetString.Tree, SourceInfo}) ::Tuple{DAE.Exp, Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo}}
              local outTpl::Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo}
              local outExp::DAE.Exp

              (outExp, outTpl) = begin
                  local exp::DAE.Exp
                  local localsTree::AvlSetString.Tree
                  local useTree::AvlSetString.Tree
                  local name::String
                  local pat::DAE.Pattern
                  local cr::DAE.ComponentRef
                  local info::SourceInfo
                  local ty::DAE.Type
                  local extra::Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo}
                @matchcontinue (inExp, inTpl) begin
                  (DAE.CREF(componentRef = cr, ty = ty), extra && (localsTree, useTree, info))  => begin
                      name = CrefForHashTable.crefFirstIdent(cr)
                      if AvlSetString.hasKey(localsTree, name) && ! AvlSetString.hasKey(useTree, name)
                        Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_UNUSED_ASSIGNMENT, list(name), info)
                        outExp = DAE.CREF(DAE.WILD(), ty)
                      else
                        outExp = inExp
                      end
                    (outExp, extra)
                  end

                  (DAE.PATTERN(pattern = pat), extra)  => begin
                      (pat, extra) = traversePattern(pat, checkDefUsePattern, extra)
                    (DAE.PATTERN(pat), extra)
                  end

                  _  => begin
                      (inExp, inTpl)
                  end
                end
              end
          (outExp, outTpl)
        end

         #= Replace unused assignments with wildcards =#
        function checkDefUsePattern(inPat::DAE.Pattern, inTpl::Tuple{<:AvlSetString.Tree, AvlSetString.Tree, SourceInfo}) ::Tuple{DAE.Pattern, Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo}}
              local outTpl::Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo} = inTpl
              local outPat::DAE.Pattern

              outPat = begin
                  local localsTree::AvlSetString.Tree
                  local useTree::AvlSetString.Tree
                  local name::String
                  local pat::DAE.Pattern
                  local info::SourceInfo
                  local ty::DAE.Type
                  local extra::Tuple{AvlSetString.Tree, AvlSetString.Tree, SourceInfo}
                @match (inPat, inTpl) begin
                  (DAE.PAT_AS(id = name, pat = pat), (localsTree, useTree, info))  => begin
                      if AvlSetString.hasKey(localsTree, name) && ! AvlSetString.hasKey(useTree, name)
                        Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_UNUSED_AS_BINDING, list(name), info)
                      else
                        pat = inPat
                      end
                    pat
                  end

                  (DAE.PAT_AS_FUNC_PTR(id = name, pat = pat), (localsTree, useTree, info))  => begin
                      if AvlSetString.hasKey(localsTree, name) && ! AvlSetString.hasKey(useTree, name)
                        Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_UNUSED_AS_BINDING, list(name), info)
                      else
                        pat = inPat
                      end
                    pat
                  end

                  _  => begin
                        (pat, _) = simplifyPattern(inPat, 1)
                      pat
                  end
                end
              end
          (outPat, outTpl)
        end

         #= Use with Expression.traverseExpBottomUp to collect all CREF's that could be references to local
        variables. =#
        function useLocalCref(inExp::DAE.Exp, inTree::AvlSetString.Tree) ::Tuple{DAE.Exp, AvlSetString.Tree}
              local outTree::AvlSetString.Tree
              local outExp::DAE.Exp

              (outExp, outTree) = begin
                  local exp::DAE.Exp
                  local tree::AvlSetString.Tree
                  local name::String
                  local cases::List{DAE.MatchCase}
                  local pat::DAE.Pattern
                  local subs::List{DAE.Subscript}
                  local cr::DAE.ComponentRef
                @match (inExp, inTree) begin
                  (exp && DAE.CREF(componentRef = cr), tree)  => begin
                      tree = useLocalCrefHelper(cr, tree)
                    (exp, tree)
                  end

                  (exp && DAE.CALL(path = Absyn.IDENT(name), attr = DAE.CALL_ATTR(builtin = false)), tree)  => begin
                      tree = AvlSetString.add(tree, name)
                    (exp, tree)
                  end

                  (exp && DAE.PATTERN(pattern = pat), tree)  => begin
                      (_, tree) = traversePattern(pat, usePatternAsBindings, tree)
                    (exp, tree)
                  end

                  (exp && DAE.MATCHEXPRESSION(cases = cases), tree)  => begin
                      tree = useCasesLocalCref(cases, tree)
                    (exp, tree)
                  end

                  _  => begin
                      (inExp, inTree)
                  end
                end
              end
          (outExp, outTree)
        end

        function useLocalCrefHelper(cr::DAE.ComponentRef, inTree::AvlSetString.Tree) ::AvlSetString.Tree
              local tree::AvlSetString.Tree

              tree = begin
                  local name::String
                  local subs::List{DAE.Subscript}
                  local cr2::DAE.ComponentRef
                @match (cr, inTree) begin
                  (DAE.CREF_IDENT(ident = name, subscriptLst = subs), _)  => begin
                      tree = useLocalCrefSubs(subs, inTree)
                    AvlSetString.add(tree, name)
                  end

                  (DAE.CREF_QUAL(ident = name, subscriptLst = subs, componentRef = cr2), _)  => begin
                      tree = useLocalCrefSubs(subs, inTree)
                      tree = AvlSetString.add(tree, name)
                    useLocalCrefHelper(cr2, tree)
                  end

                  _  => begin
                      inTree
                  end
                end
              end
          tree
        end

         #= Cref subscripts may also contain crefs =#
        function useLocalCrefSubs(isubs::List{<:DAE.Subscript}, inTree::AvlSetString.Tree) ::AvlSetString.Tree
              local tree::AvlSetString.Tree

              tree = begin
                  local exp::DAE.Exp
                  local subs::List{DAE.Subscript}
                @match (isubs, inTree) begin
                  ( nil(), _)  => begin
                    inTree
                  end

                  (DAE.SLICE(exp) <| subs, _)  => begin
                      (_, tree) = Expression.traverseExpBottomUp(exp, useLocalCref, inTree)
                      tree = useLocalCrefSubs(subs, tree)
                    tree
                  end

                  (DAE.INDEX(exp) <| subs, _)  => begin
                      (_, tree) = Expression.traverseExpBottomUp(exp, useLocalCref, inTree)
                      tree = useLocalCrefSubs(subs, tree)
                    tree
                  end

                  _  => begin
                      inTree
                  end
                end
              end
          tree
        end

         #= Traverse patterns and as-bindings as variable references in the hashtable =#
        function usePatternAsBindings(inPat::DAE.Pattern, inTree::AvlSetString.Tree) ::Tuple{DAE.Pattern, AvlSetString.Tree}
              local outTree::AvlSetString.Tree
              local outPat::DAE.Pattern = inPat

              outTree = begin
                @matchcontinue inPat begin
                  DAE.PAT_AS(__)  => begin
                    AvlSetString.add(inTree, inPat.id)
                  end

                  DAE.PAT_AS_FUNC_PTR(__)  => begin
                    AvlSetString.add(inTree, inPat.id)
                  end

                  _  => begin
                      inTree
                  end
                end
              end
          (outPat, outTree)
        end

        function useCasesLocalCref(icases::List{<:DAE.MatchCase}, inTree::AvlSetString.Tree) ::AvlSetString.Tree
              local tree::AvlSetString.Tree

              tree = begin
                  local pats::List{DAE.Pattern}
                  local cases::List{DAE.MatchCase}
                @match (icases, inTree) begin
                  ( nil(), _)  => begin
                    inTree
                  end

                  (DAE.CASE(patterns = pats) <| cases, _)  => begin
                      (_, tree) = traversePatternList(pats, usePatternAsBindings, inTree)
                      tree = useCasesLocalCref(cases, tree)
                    tree
                  end
                end
              end
          tree
        end

        function addCasesLocalCref(icases::List{<:DAE.MatchCase}, iht::HashTableStringToPath.HashTable) ::HashTableStringToPath.HashTable
              local outHt::HashTableStringToPath.HashTable

              outHt = begin
                  local pats::List{DAE.Pattern}
                  local cases::List{DAE.MatchCase}
                  local ht::HashTableStringToPath.HashTable
                @match (icases, iht) begin
                  ( nil(), ht)  => begin
                    ht
                  end

                  (DAE.CASE(patterns = pats) <| cases, ht)  => begin
                      (_, ht) = traversePatternList(pats, addPatternAsBindings, ht)
                      ht = addCasesLocalCref(cases, ht)
                    ht
                  end
                end
              end
          outHt
        end

         #= Simplifies a pattern, for example (_,_,_)=>_. For use with traversePattern =#
        function simplifyPattern(inPat::DAE.Pattern, extra::Type_a) ::Tuple{DAE.Pattern, Type_a}
              local outExtra::Type_a = extra
              local outPat::DAE.Pattern

              outPat = begin
                  local name::Absyn.Path
                  local pat::DAE.Pattern
                  local pat2::DAE.Pattern
                  local namedPatterns::List{Tuple{DAE.Pattern, String, DAE.Type}}
                  local patterns::List{DAE.Pattern}
                @match inPat begin
                  DAE.PAT_CALL_NAMED(name, namedPatterns)  => begin
                      namedPatterns = ListUtil.filterOnTrue(namedPatterns, filterEmptyPattern)
                    if listEmpty(namedPatterns)
                          DAE.PAT_WILD()
                        else
                          DAE.PAT_CALL_NAMED(name, namedPatterns)
                        end
                  end

                  DAE.PAT_CALL_TUPLE(patterns)  => begin
                    if allPatternsWild(patterns)
                          DAE.PAT_WILD()
                        else
                          inPat
                        end
                  end

                  DAE.PAT_META_TUPLE(patterns)  => begin
                    if allPatternsWild(patterns)
                          DAE.PAT_WILD()
                        else
                          inPat
                        end
                  end

                  _  => begin
                      inPat
                  end
                end
              end
          (outPat, outExtra)
        end

         #= Traverse patterns and as-bindings as variable references in the hashtable =#
        function addPatternAsBindings(inPat::DAE.Pattern, inHt::HashTableStringToPath.HashTable) ::Tuple{DAE.Pattern, HashTableStringToPath.HashTable}
              local ht::HashTableStringToPath.HashTable = inHt
              local pat::DAE.Pattern = inPat

              ht = begin
                  local id::String
                @matchcontinue inPat begin
                  DAE.PAT_AS(id = id)  => begin
                    BaseHashTable.add((id, Absyn.IDENT("")), ht)
                  end

                  DAE.PAT_AS_FUNC_PTR(id = id)  => begin
                    BaseHashTable.add((id, Absyn.IDENT("")), ht)
                  end

                  _  => begin
                      ht
                  end
                end
              end
          (pat, ht)
        end

        function traversePatternList(inPatterns::List{DAE.Pattern}, func::Func, inExtra::TypeA)  where {TypeA}
              local extra::TypeA = inExtra
              local outPatterns::List{DAE.Pattern} = nil

              local p::DAE.Pattern

              for pat in inPatterns
                (p, extra) = traversePattern(pat, func, extra)
                outPatterns = _cons(p, outPatterns)
              end
              outPatterns = Dangerous.listReverseInPlace(outPatterns)
          (outPatterns, extra)
        end

        function traversePattern(inPattern::DAE.Pattern, func::Func, inExtra::TypeA)  where {TypeA}
              local extra::TypeA = inExtra
              local outPattern::DAE.Pattern

              (outPattern, extra) = begin
                  local a::TypeA
                  local pat::DAE.Pattern
                  local pat1::DAE.Pattern
                  local pat2::DAE.Pattern
                  local pats::List{DAE.Pattern}
                  local fields::List{String}
                  local types::List{DAE.Type}
                  local typeVars::List{DAE.Type}
                  local id::String
                  local str::String
                  local ty::Option{DAE.Type}
                  local name::Absyn.Path
                  local index::ModelicaInteger
                  local namedpats::List{Tuple{DAE.Pattern, String, DAE.Type}}
                  local knownSingleton::Bool
                  local fieldVars::List{DAE.Var}
                  local attr::DAE.Attributes
                @match inPattern begin
                  DAE.PAT_AS(id, ty, attr, pat2)  => begin
                      (pat2, extra) = traversePattern(pat2, func, extra)
                      pat = DAE.PAT_AS(id, ty, attr, pat2)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_AS_FUNC_PTR(id, pat2)  => begin
                      (pat2, extra) = traversePattern(pat2, func, extra)
                      pat = DAE.PAT_AS_FUNC_PTR(id, pat2)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_CALL(name, index, pats, fieldVars, typeVars, knownSingleton)  => begin
                      (pats, extra) = traversePatternList(pats, func, extra)
                      pat = DAE.PAT_CALL(name, index, pats, fieldVars, typeVars, knownSingleton)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_CALL_NAMED(name, namedpats)  => begin
                      pats = ListUtil.map(namedpats, Util.tuple31)
                      fields = ListUtil.map(namedpats, Util.tuple32)
                      types = ListUtil.map(namedpats, Util.tuple33)
                      (pats, extra) = traversePatternList(pats, func, extra)
                      namedpats = ListUtil.thread3Tuple(pats, fields, types)
                      pat = DAE.PAT_CALL_NAMED(name, namedpats)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_CALL_TUPLE(pats)  => begin
                      (pats, extra) = traversePatternList(pats, func, extra)
                      pat = DAE.PAT_CALL_TUPLE(pats)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_META_TUPLE(pats)  => begin
                      (pats, extra) = traversePatternList(pats, func, extra)
                      pat = DAE.PAT_META_TUPLE(pats)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_CONS(pat1, pat2)  => begin
                      (pat1, extra) = traversePattern(pat1, func, extra)
                      (pat2, extra) = traversePattern(pat2, func, extra)
                      pat = DAE.PAT_CONS(pat1, pat2)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  pat && DAE.PAT_CONSTANT(__)  => begin
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  DAE.PAT_SOME(pat1)  => begin
                      (pat1, extra) = traversePattern(pat1, func, extra)
                      pat = DAE.PAT_SOME(pat1)
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  pat && DAE.PAT_WILD(__)  => begin
                      (pat, extra) = func(pat, extra)
                    (pat, extra)
                  end

                  pat  => begin
                      str = "Patternm.traversePattern failed: " + patternStr(pat)
                      Error.addMessage(Error.INTERNAL_ERROR, list(str))
                    fail()
                  end
                end
              end
          (outPattern, extra)
        end

         #= Filters out unused local declarations =#
        function filterUnusedDecls(matchDecls::List{<:DAE.Element}, ht::HashTableStringToPath.HashTable, iacc::List{<:DAE.Element}, iunusedHt::HashTableStringToPath.HashTable) ::Tuple{List{DAE.Element}, HashTableStringToPath.HashTable}
              local outUnusedHt::HashTableStringToPath.HashTable
              local outDecls::List{DAE.Element}

              (outDecls, outUnusedHt) = begin
                  local el::DAE.Element
                  local rest::List{DAE.Element}
                  local info::SourceInfo
                  local name::String
                  local acc::List{DAE.Element}
                  local unusedHt::HashTableStringToPath.HashTable
                @matchcontinue (matchDecls, ht, iacc, iunusedHt) begin
                  ( nil(), _, acc, unusedHt)  => begin
                    (listReverse(acc), unusedHt)
                  end

                  (DAE.VAR(componentRef = DAE.CREF_IDENT(ident = name), source = DAE.SOURCE(info = info)) <| rest, _, acc, unusedHt)  => begin
                      @match false = BaseHashTable.hasKey(name, ht)
                      unusedHt = BaseHashTable.add((name, Absyn.IDENT("")), unusedHt)
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_UNUSED_DECL, list(name), info)
                      (acc, unusedHt) = filterUnusedDecls(rest, ht, acc, unusedHt)
                    (acc, unusedHt)
                  end

                  (el <| rest, _, acc, unusedHt)  => begin
                      (acc, unusedHt) = filterUnusedDecls(rest, ht, _cons(el, acc), unusedHt)
                    (acc, unusedHt)
                  end
                end
              end
          (outDecls, outUnusedHt)
        end

         #= matchcontinue: Removes empty, failing cases
          match: Removes empty cases that can't be matched by subsequent cases
          match: Removes cases that can't be reached because a previous case has a dominating pattern
           =#
        function caseDeadCodeElimination(matchType::Absyn.MatchType, cases::List{<:DAE.MatchCase}, prevPatterns::List{<:List{<:DAE.Pattern}}, iacc::List{<:DAE.MatchCase}, iter::Bool #= If we remove some code, it may cascade. We should we loop more. =#) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                  local rest::List{DAE.MatchCase}
                  local pats::List{DAE.Pattern}
                  local case_::DAE.MatchCase
                  local info::SourceInfo
                  local acc::List{DAE.MatchCase}
                @matchcontinue (matchType, cases, prevPatterns, iacc, iter) begin
                  (_,  nil(), _, acc, false)  => begin
                    listReverse(acc)
                  end

                  (_,  nil(), _, acc, true)  => begin
                    caseDeadCodeElimination(matchType, listReverse(acc), nil, nil, false)
                  end

                  (_, DAE.CASE(body =  nil(), result = NONE(), info = info) <|  nil(), _, acc, _)  => begin
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_DEAD_CODE, list("Last pattern is empty"), info)
                    caseDeadCodeElimination(matchType, listReverse(acc), nil, nil, false)
                  end

                  (Absyn.MATCHCONTINUE(__), DAE.CASE(patterns = pats, body =  nil(), result = NONE(), info = info) <| rest, _, acc, _)  => begin
                      @match true = Flags.isSet(Flags.PATTERNM_DCE)
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_DEAD_CODE, list("Empty matchcontinue case"), info)
                      acc = caseDeadCodeElimination(matchType, rest, _cons(pats, prevPatterns), acc, true)
                    acc
                  end

                  (_, case_ && DAE.CASE(patterns = pats) <| rest, _, acc, _)  => begin
                    caseDeadCodeElimination(matchType, rest, _cons(pats, prevPatterns), _cons(case_, acc), iter)
                  end
                end
              end
               #= /* Tricky to get right; I'll try again later as it probably only gives marginal results anyway
                  case (Absyn.MATCH(),DAE.CASE(patterns=pats,info=info)::rest,prevPatterns as _::_,acc,iter)
                    equation
                      oinfo = findOverlappingPattern(pats,acc);
                      Error.assertionOrAddSourceMessage(not Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_DEAD_CODE, {\"Unreachable pattern\"}, info);
                      Error.assertionOrAddSourceMessage(not Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_DEAD_CODE, {\"Shadowing case\"}, oinfo);
                    then caseDeadCodeElimination(matchType,rest,pats::prevPatterns,acc,true);
                    */ =#
          outCases
        end

         #= /*
        protected function findOverlappingPattern
          input list<DAE.Pattern> patterns;
          input list<DAE.MatchCase> prevCases;
          output SourceInfo info;
        algorithm
          info := matchcontinue (patterns,prevCases)
            local
              list<DAE.Pattern> ps1,ps2;
            case (ps1,DAE.CASE(patterns=ps2,info=info)::_)
              equation
                true = patternListsDoOverlap(ps1,ps2); ???
              then info;
            case (ps1,_::prevCases) then findOverlappingPattern(ps1,prevCases);
          end matchcontinue;
        end findOverlappingPattern;
        */ =#

         #= If a case in a matchcontinue expression is followed by a (list of) cases that
          do not have overlapping patterns with the first one, an optimization can be made.
          If we match against the first pattern, we can jump a few positions in the loop!

          For example:
            matchcontinue i,j
              case (1,_) then ();  (1) => skip (2),(3) if this pattern matches
              case (2,_) then ();  (2) => skip (3),(4) if this pattern matches
              case (3,_) then ();  (3) => skip (4),(5) if this pattern matches
              case (1,_) then ();  (4) => skip (5),(6) if this pattern matches
              case (2,_) then ();  (5) => skip (6) if this pattern matches
              case (3,_) then ();  (6)
              case (_,2) then ();  (7) => skip (8),(9) if this pattern matches
              case (1,1) then ();  (8) => skip (9) if this pattern matches
              case (2,1) then ();  (9) => skip (10) if this pattern matches
              case (1,_) then ();  (10)
            end matchcontinue;
           =#
        function optimizeContinueJumps(matchType::Absyn.MatchType, cases::List{<:DAE.MatchCase}) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                @match (matchType, cases) begin
                  (Absyn.MATCH(__), _)  => begin
                    cases
                  end

                  _  => begin
                      optimizeContinueJumps2(cases)
                  end
                end
              end
          outCases
        end

        function optimizeContinueJumps2(icases::List{<:DAE.MatchCase}) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                  local case_::DAE.MatchCase
                  local cases::List{DAE.MatchCase}
                @match icases begin
                   nil()  => begin
                    nil
                  end

                  case_ <| cases  => begin
                      case_ = optimizeContinueJump(case_, cases, 0)
                      cases = optimizeContinueJumps2(cases)
                    _cons(case_, cases)
                  end
                end
              end
          outCases
        end

        function optimizeContinueJump(case_::DAE.MatchCase, icases::List{<:DAE.MatchCase}, jump::ModelicaInteger) ::DAE.MatchCase
              local outCase::DAE.MatchCase

              outCase = begin
                  local case1::DAE.MatchCase
                  local ps1::List{DAE.Pattern}
                  local ps2::List{DAE.Pattern}
                  local cases::List{DAE.MatchCase}
                @matchcontinue (case_, icases, jump) begin
                  (case1,  nil(), _)  => begin
                    updateMatchCaseJump(case1, jump)
                  end

                  (case1 && DAE.CASE(patterns = ps1), DAE.CASE(patterns = ps2) <| cases, _)  => begin
                      @match true = patternListsDoNotOverlap(ps1, ps2)
                    optimizeContinueJump(case1, cases, jump + 1)
                  end

                  (case1, _, _)  => begin
                    updateMatchCaseJump(case1, jump)
                  end
                end
              end
          outCase
        end

         #= Updates the jump field of a DAE.MatchCase =#
        function updateMatchCaseJump(case_::DAE.MatchCase, jump::ModelicaInteger) ::DAE.MatchCase
              local outCase::DAE.MatchCase

              outCase = begin
                  local patterns::List{DAE.Pattern}
                  local localDecls::List{DAE.Element}
                  local body::List{DAE.Statement}
                  local result::Option{DAE.Exp}
                  local guardPattern::Option{DAE.Exp}
                  local resultInfo::SourceInfo
                  local info::SourceInfo
                @match (case_, jump) begin
                  (_, 0)  => begin
                    case_
                  end

                  (DAE.CASE(patterns, guardPattern, localDecls, body, result, resultInfo, _, info), _)  => begin
                    DAE.CASE(patterns, guardPattern, localDecls, body, result, resultInfo, jump, info)
                  end
                end
              end
          outCase
        end

         #= If a matchcontinue expression has only one case, it is optimized to match instead.
          The same goes if for every case there is no overlapping pattern with a previous case.
          For example, the following example can be safely translated into a match-expression:
            matchcontinue i
              case 1 then ();
              case 2 then ();
              case 3 then ();
            end matchcontinue;
           =#
        function optimizeContinueToMatch(matchType::Absyn.MatchType, cases::List{<:DAE.MatchCase}, info::SourceInfo) ::Absyn.MatchType
              local outMatchType::Absyn.MatchType

              outMatchType = begin
                @match (matchType, cases, info) begin
                  (Absyn.MATCH(__), _, _)  => begin
                    Absyn.MATCH()
                  end

                  _  => begin
                      optimizeContinueToMatch2(cases, nil, info)
                  end
                end
              end
          outMatchType
        end

         #= If a matchcontinue expression has only one case, it is optimized to match instead.
          The same goes if for every case there is no overlapping pattern with a previous case.
          For example, the following example can be safely translated into a match-expression:
            matchcontinue i
              case 1 then ();
              case 2 then ();
              case 3 then ();
            end matchcontinue;
           =#
        function optimizeContinueToMatch2(icases::List{<:DAE.MatchCase}, prevPatterns::List{<:List{<:DAE.Pattern}} #= All cases check its patterns against all previous patterns. If they overlap, we can't optimize away the continue =#, info::SourceInfo) ::Absyn.MatchType
              local outMatchType::Absyn.MatchType

              outMatchType = begin
                  local patterns::List{DAE.Pattern}
                  local cases::List{DAE.MatchCase}
                @matchcontinue (icases, prevPatterns, info) begin
                  ( nil(), _, _)  => begin
                      Error.assertionOrAddSourceMessage(! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.MATCHCONTINUE_TO_MATCH_OPTIMIZATION, nil, info)
                    Absyn.MATCH()
                  end

                  (DAE.CASE(patterns = patterns) <| cases, _, _)  => begin
                      assertAllPatternListsDoNotOverlap(prevPatterns, patterns)
                    optimizeContinueToMatch2(cases, _cons(patterns, prevPatterns), info)
                  end

                  _  => begin
                      Absyn.MATCHCONTINUE()
                  end
                end
              end
          outMatchType
        end

         #= If a matchcontinue expression has only one case, it is optimized to match instead.
          The same goes if for every case there is no overlapping pattern with a previous case.
          For example, the following example can be safely translated into a match-expression:
            matchcontinue i
              case 1 then ();
              case 2 then ();
              case 3 then ();
            end matchcontinue;
           =#
        function assertAllPatternListsDoNotOverlap(ipss1::List{<:List{<:DAE.Pattern}}, ps2::List{<:DAE.Pattern})
              _ = begin
                  local ps1::List{DAE.Pattern}
                  local pss1::List{List{DAE.Pattern}}
                @match (ipss1, ps2) begin
                  ( nil(), _)  => begin
                    ()
                  end

                  (ps1 <| pss1, _)  => begin
                      @match true = patternListsDoNotOverlap(ps1, ps2)
                      assertAllPatternListsDoNotOverlap(pss1, ps2)
                    ()
                  end
                end
              end
        end

         #= Verifies that pats1 does not shadow pats2 =#
        function patternListsDoNotOverlap(ips1::List{<:DAE.Pattern}, ips2::List{<:DAE.Pattern}) ::Bool
              local b::Bool

              b = begin
                  local res::Bool
                  local p1::DAE.Pattern
                  local p2::DAE.Pattern
                  local ps1::List{DAE.Pattern}
                  local ps2::List{DAE.Pattern}
                @match (ips1, ips2) begin
                  ( nil(),  nil())  => begin
                    false
                  end

                  (p1 <| ps1, p2 <| ps2)  => begin
                      res = patternsDoNotOverlap(p1, p2)
                      res = if ! res
                            patternListsDoNotOverlap(ps1, ps2)
                          else
                            res
                          end
                    res
                  end
                end
              end
          b
        end

         #= Verifies that p1 do not shadow p2 =#
        function patternsDoNotOverlap(ip1::DAE.Pattern, ip2::DAE.Pattern) ::Bool
              local b::Bool

              b = begin
                  local head1::DAE.Pattern
                  local tail1::DAE.Pattern
                  local head2::DAE.Pattern
                  local tail2::DAE.Pattern
                  local p1::DAE.Pattern
                  local p2::DAE.Pattern
                  local ps1::List{DAE.Pattern}
                  local ps2::List{DAE.Pattern}
                  local res::Bool
                  local name1::Absyn.Path
                  local name2::Absyn.Path
                  local ix1::ModelicaInteger
                  local ix2::ModelicaInteger
                  local e1::DAE.Exp
                  local e2::DAE.Exp
                @match (ip1, ip2) begin
                  (DAE.PAT_WILD(__), _)  => begin
                    false
                  end

                  (_, DAE.PAT_WILD(__))  => begin
                    false
                  end

                  (DAE.PAT_AS_FUNC_PTR(__), _)  => begin
                    false
                  end

                  (DAE.PAT_AS(pat = p1), p2)  => begin
                    patternsDoNotOverlap(p1, p2)
                  end

                  (p1, DAE.PAT_AS(pat = p2))  => begin
                    patternsDoNotOverlap(p1, p2)
                  end

                  (DAE.PAT_CONS(head1, tail1), DAE.PAT_CONS(head2, tail2))  => begin
                    patternsDoNotOverlap(head1, head2) || patternsDoNotOverlap(tail1, tail2)
                  end

                  (DAE.PAT_SOME(p1), DAE.PAT_SOME(p2))  => begin
                    patternsDoNotOverlap(p1, p2)
                  end

                  (DAE.PAT_META_TUPLE(ps1), DAE.PAT_META_TUPLE(ps2))  => begin
                    patternListsDoNotOverlap(ps1, ps2)
                  end

                  (DAE.PAT_CALL_TUPLE(ps1), DAE.PAT_CALL_TUPLE(ps2))  => begin
                    patternListsDoNotOverlap(ps1, ps2)
                  end

                  (DAE.PAT_CALL(name1, ix1,  nil(), _, _), DAE.PAT_CALL(name2, ix2,  nil(), _, _))  => begin
                      res = ix1 == ix2
                      res = if res
                            AbsynUtil.pathEqual(name1, name2)
                          else
                            res
                          end
                    ! res
                  end

                  (DAE.PAT_CALL(name1, ix1, ps1, _, _), DAE.PAT_CALL(name2, ix2, ps2, _, _))  => begin
                      res = ix1 == ix2
                      res = if res
                            AbsynUtil.pathEqual(name1, name2)
                          else
                            res
                          end
                      res = if res
                            patternListsDoNotOverlap(ps1, ps2)
                          else
                            ! res
                          end
                    res
                  end

                  (DAE.PAT_CONSTANT(exp = e1), DAE.PAT_CONSTANT(exp = e2))  => begin
                    ! Expression.expEqual(e1, e2)
                  end

                  (DAE.PAT_CONSTANT(__), _)  => begin
                    true
                  end

                  (_, DAE.PAT_CONSTANT(__))  => begin
                    true
                  end

                  _  => begin
                      false
                  end
                end
              end
               #=  TODO: PAT_CALLED_NAMED?
               =#
               #=  Constant patterns...
               =#
          b
        end

        function elabMatchCases(cache::FCore.Cache, env::FCore.Graph, cases::List{<:Absyn.Case}, tys::List{<:DAE.Type}, inputAliases::List{<:List{<:String}}, matchExpLocalTree::AvlSetString.Tree, impl::Bool, performVectorization::Bool, pre::Prefix.PrefixType, info::SourceInfo) ::Tuple{FCore.Cache, List{DAE.MatchCase}, DAE.Type}
              local resType::DAE.Type
              local elabCases::List{DAE.MatchCase}
              local outCache::FCore.Cache

              local resExps::List{DAE.Exp}
              local resTypes::List{DAE.Type}
              local tysFixed::List{DAE.Type}

              tysFixed = ListUtil.map(tys, Types.getUniontypeIfMetarecordReplaceAllSubtypes)
              (outCache, elabCases, resExps, resTypes) = elabMatchCases2(cache, env, cases, tysFixed, inputAliases, matchExpLocalTree, impl, performVectorization, pre, nil, nil, nil)
              (elabCases, resType) = fixCaseReturnTypes(elabCases, resExps, resTypes, info)
          (outCache, elabCases, resType)
        end

        function elabMatchCases2(inCache::FCore.Cache, inEnv::FCore.Graph, cases::List{<:Absyn.Case}, tys::List{<:DAE.Type}, inputAliases::List{<:List{<:String}}, matchExpLocalTree::AvlSetString.Tree, impl::Bool, performVectorization::Bool, pre::Prefix.PrefixType, inAccCases::List{<:DAE.MatchCase} #= Order does matter =#, inAccExps::List{<:DAE.Exp} #= Order does matter =#, inAccTypes::List{<:DAE.Type} #= Order does not matter =#) ::Tuple{FCore.Cache, List{DAE.MatchCase}, List{DAE.Exp}, List{DAE.Type}}
              local resTypes::List{DAE.Type}
              local resExps::List{DAE.Exp}
              local elabCases::List{DAE.MatchCase}
              local outCache::FCore.Cache

              (outCache, elabCases, resExps, resTypes) = begin
                  local case_::Absyn.Case
                  local rest::List{Absyn.Case}
                  local elabCase::DAE.MatchCase
                  local optType::Option{DAE.Type}
                  local optExp::Option{DAE.Exp}
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local accExps::List{DAE.Exp}
                  local accTypes::List{DAE.Type}
                @match (inCache, inEnv, cases, inAccExps, inAccTypes) begin
                  (cache, _,  nil(), accExps, accTypes)  => begin
                    (cache, listReverse(inAccCases), listReverse(accExps), listReverse(accTypes))
                  end

                  (cache, env, case_ <| rest, accExps, accTypes)  => begin
                      (cache, elabCase, optExp, optType) = elabMatchCase(cache, env, case_, tys, inputAliases, matchExpLocalTree, impl, performVectorization, pre)
                      (cache, elabCases, accExps, accTypes) = elabMatchCases2(cache, env, rest, tys, inputAliases, matchExpLocalTree, impl, performVectorization, pre, _cons(elabCase, inAccCases), ListUtil.consOption(optExp, accExps), ListUtil.consOption(optType, accTypes))
                    (cache, elabCases, accExps, accTypes)
                  end
                end
              end
          (outCache, elabCases, resExps, resTypes)
        end

        function elabMatchCase(inCache::FCore.Cache, inEnv::FCore.Graph, acase::Absyn.Case, tys::List{<:DAE.Type}, inputAliases::List{<:List{<:String}}, matchExpLocalTree::AvlSetString.Tree, impl::Bool, performVectorization::Bool, pre::Prefix.PrefixType) ::Tuple{FCore.Cache, DAE.MatchCase, Option{DAE.Exp}, Option{DAE.Type}}
              local resType::Option{DAE.Type}
              local resExp::Option{DAE.Exp}
              local elabCase::DAE.MatchCase
              local outCache::FCore.Cache

              (outCache, elabCase, resExp, resType) = begin
                  local result::Absyn.Exp
                  local pattern::Absyn.Exp
                  local patterns::List{Absyn.Exp}
                  local elabPatterns::List{DAE.Pattern}
                  local elabPatterns2::List{DAE.Pattern}
                  local patternGuard::Option{Absyn.Exp}
                  local elabResult::Option{DAE.Exp}
                  local dPatternGuard::Option{DAE.Exp}
                  local caseDecls::List{DAE.Element}
                  local cp::Absyn.ClassPart
                  local eqAlgs::List{Absyn.AlgorithmItem}
                  local algs::List{SCode.Statement}
                  local body::List{DAE.Statement}
                  local decls::List{Absyn.ElementItem}
                  local patternInfo::SourceInfo
                  local resultInfo::SourceInfo
                  local info::SourceInfo
                  local len::ModelicaInteger
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local caseLocalTree::AvlSetString.Tree
                  local localsTree::AvlSetString.Tree
                  local useTree::AvlSetString.Tree
                @match (inCache, inEnv, acase) begin
                  (cache, env, Absyn.CASE(pattern = pattern, patternGuard = patternGuard, patternInfo = patternInfo, localDecls = decls, classPart = cp, result = result, resultInfo = resultInfo, info = info))  => begin
                      @match (cache, SOME((env, DAE.DAE_LIST(caseDecls), caseLocalTree))) = addLocalDecls(cache, env, decls, FCore.caseScopeName, impl, info)
                      patterns = convertExpToPatterns(pattern)
                      patterns = if listLength(tys) == 1
                            list(pattern)
                          else
                            patterns
                          end
                      (cache, elabPatterns) = elabPatternTuple(cache, env, patterns, tys, patternInfo, pattern)
                      checkPatternsDuplicateAsBindings(elabPatterns, patternInfo)
                      env = FGraphUtil.openNewScope(env, SCode.NOT_ENCAPSULATED(), SOME(FCore.patternTypeScope), NONE())
                      (elabPatterns2, cache) = addPatternAliasesList(elabPatterns, inputAliases, cache, inEnv)
                      (_, env) = traversePatternList(elabPatterns2, addEnvKnownAsBindings, env)
                      eqAlgs = Static.fromEquationsToAlgAssignments(cp)
                      algs = AbsynToSCode.translateClassdefAlgorithmitems(eqAlgs)
                      (cache, body) = InstSection.instStatements(cache, env, InnerOuterTypes.emptyInstHierarchy, pre, ClassInf.FUNCTION(Absyn.IDENT("match"), false), algs, ElementSource.addElementSourceFileInfo(DAE.emptyElementSource, patternInfo), SCode.NON_INITIAL(), true, InstTypes.neverUnroll)
                      (cache, body, elabResult, resultInfo, resType) = elabResultExp(cache, env, body, result, impl, performVectorization, pre, resultInfo)
                      (cache, dPatternGuard) = elabPatternGuard(cache, env, patternGuard, impl, performVectorization, pre, patternInfo)
                      localsTree = AvlSetString.join(matchExpLocalTree, caseLocalTree)
                      useTree = AvlSetString.new()
                      (_, useTree) = Expression.traverseExpBottomUp(DAE.META_OPTION(elabResult), useLocalCref, useTree)
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, useTree)
                      (_, useTree) = Expression.traverseExpBottomUp(DAE.META_OPTION(dPatternGuard), useLocalCref, useTree)
                      (elabPatterns, _) = traversePatternList(elabPatterns, checkDefUsePattern, (localsTree, useTree, patternInfo))
                      useTree = AvlSetString.new()
                      (_, useTree) = Expression.traverseExpBottomUp(DAE.META_OPTION(elabResult), useLocalCref, useTree)
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, useTree)
                      (_, useTree) = Expression.traverseExpBottomUp(DAE.META_OPTION(dPatternGuard), useLocalCref, useTree)
                      (elabPatterns, _) = traversePatternList(elabPatterns, checkDefUsePattern, (localsTree, useTree, patternInfo))
                      elabCase = DAE.CASE(elabPatterns, dPatternGuard, caseDecls, body, elabResult, resultInfo, 0, info)
                    (cache, elabCase, elabResult, resType)
                  end

                  (cache, env, Absyn.ELSE(localDecls = decls, classPart = cp, result = result, resultInfo = resultInfo, info = info))  => begin
                      len = listLength(tys)
                      patterns = ListUtil.fill(Absyn.CREF(Absyn.WILD()), listLength(tys))
                      pattern = if len == 1
                            Absyn.CREF(Absyn.WILD())
                          else
                            Absyn.TUPLE(patterns)
                          end
                      (cache, elabCase, elabResult, resType) = elabMatchCase(cache, env, Absyn.CASE(pattern, NONE(), info, decls, cp, result, resultInfo, NONE(), info), tys, inputAliases, matchExpLocalTree, impl, performVectorization, pre)
                    (cache, elabCase, elabResult, resType)
                  end
                end
              end
               #=  open a pattern type scope
               =#
               #=  and add the ID as pattern types to it
               =#
               #=  Start building the def-use chain bottom-up
               =#
               #=  Do the same thing again, for fun and glory
               =#
               #=  ELSE is the same as CASE, but without pattern
               =#
               #=  Needs to be same length as any other pattern for the simplification algorithms, etc to work properly
               =#
          (outCache, elabCase, resExp, resType)
        end

        function elabResultExp(inCache::FCore.Cache, inEnv::FCore.Graph, inBody::List{<:DAE.Statement} #= Is input in case we want to optimize for tail-recursion =#, exp::Absyn.Exp, impl::Bool, performVectorization::Bool, pre::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, List{DAE.Statement}, Option{DAE.Exp}, SourceInfo, Option{DAE.Type}}
              local resType::Option{DAE.Type}
              local resultInfo::SourceInfo
              local resExp::Option{DAE.Exp}
              local outBody::List{DAE.Statement}
              local outCache::FCore.Cache

              (outCache, outBody, resExp, resultInfo, resType) = begin
                  local elabExp::DAE.Exp
                  local prop::DAE.Properties
                  local ty::DAE.Type
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local body::List{DAE.Statement}
                  local info::SourceInfo
                @matchcontinue (inCache, inEnv, inBody, exp) begin
                  (cache, _, body, Absyn.CALL(function_ = Absyn.CREF_IDENT("fail",  nil()), functionArgs = Absyn.FUNCTIONARGS( nil(),  nil())))  => begin
                    (cache, body, NONE(), inInfo, NONE())
                  end

                  (cache, env, body, _)  => begin
                      (cache, elabExp, prop) = Static.elabExp(cache, env, exp, impl, performVectorization, pre, inInfo)
                      ty = Types.getPropType(prop)
                      (elabExp, ty) = makeTupleFromMetaTuple(elabExp, ty)
                      (body, elabExp, info) = elabResultExp2(! Flags.isSet(Flags.PATTERNM_MOVE_LAST_EXP), body, elabExp, inInfo)
                    (cache, body, SOME(elabExp), info, SOME(ty))
                  end
                end
              end
          (outCache, outBody, resExp, resultInfo, resType)
        end

        function elabPatternGuard(inCache::FCore.Cache, inEnv::FCore.Graph, patternGuard::Option{<:Absyn.Exp}, impl::Bool, performVectorization::Bool, pre::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, Option{DAE.Exp}}
              local outPatternGuard::Option{DAE.Exp}
              local outCache::FCore.Cache

              (outCache, outPatternGuard) = begin
                  local exp::Absyn.Exp
                  local elabExp::DAE.Exp
                  local prop::DAE.Properties
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local info::SourceInfo
                  local str::String
                @matchcontinue (inCache, inEnv, patternGuard, impl, performVectorization, pre, inInfo) begin
                  (cache, _, NONE(), _, _, _, _)  => begin
                    (cache, NONE())
                  end

                  (cache, env, SOME(exp), _, _, _, info)  => begin
                      (cache, elabExp, prop) = Static.elabExp(cache, env, exp, impl, performVectorization, pre, info)
                      (elabExp, _) = Types.matchType(elabExp, Types.getPropType(prop), DAE.T_BOOL_DEFAULT, true)
                    (cache, SOME(elabExp))
                  end

                  (cache, env, SOME(exp), _, _, _, info)  => begin
                      (_, _, prop) = Static.elabExp(cache, env, exp, impl, performVectorization, pre, info)
                      str = Types.unparseType(Types.getPropType(prop))
                      Error.addSourceMessage(Error.GUARD_EXPRESSION_TYPE_MISMATCH, list(str), info)
                    fail()
                  end
                end
              end
          (outCache, outPatternGuard)
        end

         #= (cr1,...,crn) = exp; then (cr1,...,crn); => then exp;
            cr = exp; then cr; => then exp;

            Is recursive, and will remove all such assignments, i.e.:
             doStuff(); a = 1; b = a; c = b; then c;
           Becomes:
             doStuff(); then c;

          This phase needs to be performed if we want to be able to discover places to
          optimize for tail recursion.
           =#
        function elabResultExp2(skipPhase::Bool, body::List{<:DAE.Statement}, elabExp::DAE.Exp, info::SourceInfo) ::Tuple{List{DAE.Statement}, DAE.Exp, SourceInfo}
              local outInfo::SourceInfo
              local outExp::DAE.Exp
              local outBody::List{DAE.Statement}

              (outBody, outExp, outInfo) = begin
                  local elabCr1::DAE.Exp
                  local elabCr2::DAE.Exp
                  local elabCrs1::List{DAE.Exp}
                  local elabCrs2::List{DAE.Exp}
                  local b::List{DAE.Statement}
                  local e::DAE.Exp
                  local i::SourceInfo
                @matchcontinue (skipPhase, body, elabExp, info) begin
                  (true, b, e, i)  => begin
                    (b, e, i)
                  end

                  (_, b, elabCr2 && DAE.CREF(__), _)  => begin
                      @match (DAE.STMT_ASSIGN(exp1 = elabCr1, exp = e, source = DAE.SOURCE(info = i)), b) = ListUtil.splitLast(b)
                      @match true = Expression.expEqual(elabCr1, elabCr2)
                      (b, e, i) = elabResultExp2(false, b, e, i)
                    (b, e, i)
                  end

                  (_, b, DAE.TUPLE(elabCrs2), _)  => begin
                      @match (DAE.STMT_TUPLE_ASSIGN(expExpLst = elabCrs1, exp = e, source = DAE.SOURCE(info = i)), b) = ListUtil.splitLast(b)
                      ListUtil.threadMapAllValue(elabCrs1, elabCrs2, Expression.expEqual, true)
                      (b, e, i) = elabResultExp2(false, b, e, i)
                    (b, e, i)
                  end

                  _  => begin
                      (body, elabExp, info)
                  end
                end
              end
          (outBody, outExp, outInfo)
        end

        function fixCaseReturnTypes(icases::List{<:DAE.MatchCase}, iexps::List{<:DAE.Exp}, itys::List{<:DAE.Type}, info::SourceInfo) ::Tuple{List{DAE.MatchCase}, DAE.Type}
              local ty::DAE.Type
              local outCases::List{DAE.MatchCase}

              (outCases, ty) = begin
                  local str::String
                  local cases::List{DAE.MatchCase}
                  local exps::List{DAE.Exp}
                  local tys::List{DAE.Type}
                  local tysboxed::List{DAE.Type}
                @matchcontinue (icases, iexps, itys, info) begin
                  (cases,  nil(),  nil(), _)  => begin
                    (cases, DAE.T_NORETCALL_DEFAULT)
                  end

                  (cases, exps, tys, _)  => begin
                      ty = ListUtil.reduce(ListUtil.map(tys, Types.boxIfUnboxedType), Types.superType)
                      ty = Types.superType(ty, ty)
                      ty = Types.unboxedType(ty)
                      ty = Types.makeRegularTupleFromMetaTupleOnTrue(Types.allTuple(tys), ty)
                      ty = Types.getUniontypeIfMetarecordReplaceAllSubtypes(ty)
                      (exps, _) = Types.matchTypes(exps, tys, ty, true)
                      cases = fixCaseReturnTypes2(cases, exps, info)
                    (cases, ty)
                  end

                  (cases, exps, tys, _)  => begin
                      ty = ListUtil.reduce(tys, Types.superType)
                      ty = Types.superType(ty, ty)
                      ty = Types.unboxedType(ty)
                      ty = Types.makeRegularTupleFromMetaTupleOnTrue(Types.allTuple(tys), ty)
                      ty = Types.getUniontypeIfMetarecordReplaceAllSubtypes(ty)
                      (exps, _) = Types.matchTypes(exps, tys, ty, true)
                      cases = fixCaseReturnTypes2(cases, exps, info)
                    (cases, ty)
                  end

                  _  => begin
                        tys = ListUtil.unionOnTrue(itys, nil, Types.equivtypes)
                        str = stringAppendList(ListUtil.map1r(ListUtil.map(tys, Types.unparseType), stringAppend, "\\n  "))
                        Error.addSourceMessage(Error.META_MATCHEXP_RESULT_TYPES, list(str), info)
                      fail()
                  end
                end
              end
               #=  2 different cases, one boxed and one unboxed to handle everything
               =#
          (outCases, ty)
        end

        function fixCaseReturnTypes2(inCases::List{<:DAE.MatchCase}, inExps::List{<:DAE.Exp}, inInfo::SourceInfo) ::List{DAE.MatchCase}
              local outCases::List{DAE.MatchCase}

              outCases = begin
                  local patterns::List{DAE.Pattern}
                  local decls::List{DAE.Element}
                  local body::List{DAE.Statement}
                  local patternGuard::Option{DAE.Exp}
                  local exp::DAE.Exp
                  local case_::DAE.MatchCase
                  local jump::ModelicaInteger
                  local resultInfo::SourceInfo
                  local info2::SourceInfo
                  local cases::List{DAE.MatchCase}
                  local exps::List{DAE.Exp}
                  local info::SourceInfo
                @matchcontinue (inCases, inExps, inInfo) begin
                  ( nil(),  nil(), _)  => begin
                    nil
                  end

                  (DAE.CASE(patterns, patternGuard, decls, body, SOME(_), resultInfo, jump, info2) <| cases, exp <| exps, info)  => begin
                      cases = fixCaseReturnTypes2(cases, exps, info)
                    _cons(DAE.CASE(patterns, patternGuard, decls, body, SOME(exp), resultInfo, jump, info2), cases)
                  end

                  (case_ && DAE.CASE(result = NONE()) <| cases, exps, info)  => begin
                      cases = fixCaseReturnTypes2(cases, exps, info)
                    _cons(case_, cases)
                  end

                  _  => begin
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list("Patternm.fixCaseReturnTypes2 failed"), inInfo)
                      fail()
                  end
                end
              end
          outCases
        end

        function traverseConstantPatternsHelper(inExp::DAE.Exp, inT::T, func::FuncExpType)  where {T}
              local outT::T = inT
              local outExp::DAE.Exp

              outExp = begin
                  local cases::List{DAE.MatchCase}
                  local cases2::List{DAE.MatchCase}
                  local case_::DAE.MatchCase
                  local patterns::List{DAE.Pattern}
                @match inExp begin
                  outExp && DAE.MATCHEXPRESSION(cases = cases)  => begin
                      cases2 = nil
                      for c in cases
                        case_ = c
                        case_ = begin
                          @match case_ begin
                            DAE.CASE(__)  => begin
                                (patterns, outT) = traversePatternList(case_.patterns, (func) -> traverseConstantPatternsHelper2(func = func), outT)
                                if ! valueEq(case_.patterns, patterns)
                                  case_.patterns = patterns
                                end
                              case_
                            end
                          end
                        end
                        cases2 = _cons(case_, cases2)
                      end
                      cases2 = Dangerous.listReverseInPlace(cases2)
                      if ! valueEq(cases, cases2)
                        outExp.cases = cases2
                      end
                      (outExp, outT) = func(outExp, outT)
                    outExp
                  end

                  _  => begin
                        (outExp, outT) = func(inExp, outT)
                      outExp
                  end
                end
              end
          (outExp, outT)
        end

        function traverseConstantPatternsHelper2(inPattern::DAE.Pattern, inExtra::T, func::FuncExpType)  where {T}
              local extra::T = inExtra
              local outPattern::DAE.Pattern

              outPattern = begin
                  local exp::DAE.Exp
                @match inPattern begin
                  outPattern && DAE.PAT_CONSTANT(__)  => begin
                      (exp, extra) = func(outPattern.exp, extra)
                      if ! referenceEq(outPattern.exp, exp)
                        outPattern.exp = exp
                      end
                    outPattern
                  end

                  _  => begin
                      inPattern
                  end
                end
              end
          (outPattern, extra)
        end

        function filterEmptyPattern(tpl::Tuple{<:DAE.Pattern, String, DAE.Type}) ::Bool
              local outB::Bool

              outB = begin
                @match tpl begin
                  (DAE.PAT_WILD(__), _, _)  => begin
                    false
                  end

                  _  => begin
                      true
                  end
                end
              end
          outB
        end

         #= Adds local declarations to the environment and returns the DAE =#
        function addLocalDecls(inCache::FCore.Cache, inEnv::FCore.Graph, els::List{<:Absyn.ElementItem}, scopeName::String, impl::Bool, info::SourceInfo) ::Tuple{FCore.Cache, Option{Tuple{FCore.Graph, DAE.DAElist, AvlSetString.Tree}}}
              local res::Option{Tuple{FCore.Graph, DAE.DAElist, AvlSetString.Tree}}
              local outCache::FCore.Cache

              (outCache, res) = begin
                  local ld::List{Absyn.ElementItem}
                  local ld2::List{SCode.Element}
                  local ld3::List{SCode.Element}
                  local ld4::List{SCode.Element}
                  local ld_mod::List{Tuple{SCode.Element, DAE.Mod}}
                  local dae1::DAE.DAElist
                  local env2::FCore.Graph
                  local dummyFunc::ClassInf.SMNode
                  local str::String
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local b::Bool
                  local declsTree::AvlSetString.Tree
                  local names::List{String}
                @matchcontinue (inCache, inEnv, els, scopeName, impl, info) begin
                  (cache, env,  nil(), _, _, _)  => begin
                      declsTree = AvlSetString.new()
                    (cache, SOME((env, DAE.emptyDae, declsTree)))
                  end

                  (cache, env, ld, _, _, _)  => begin
                      env2 = FGraphUtil.openScope(env, SCode.NOT_ENCAPSULATED(), scopeName, NONE())
                      ld2 = AbsynToSCode.translateEitemlist(ld, SCode.PROTECTED())
                      @match true = ListUtil.applyAndFold1(ld2, boolAnd, SCodeUtil.isComponentWithDirection, Absyn.BIDIR(), true)
                      (cache, b) = ListUtil.fold1(ld2, checkLocalShadowing, env, (cache, false))
                      ld2 = if b
                            nil
                          else
                            ld2
                          end
                      ld_mod = InstUtil.addNomod(ld2)
                      dummyFunc = ClassInf.FUNCTION(Absyn.IDENT("dummieFunc"), false)
                      (cache, env2, _) = InstUtil.addComponentsToEnv(cache, env2, InnerOuterTypes.emptyInstHierarchy, DAE.NOMOD(), Prefix.NOPRE(), dummyFunc, ld_mod, impl)
                      (cache, env2, _, _, dae1, _, _, _, _, _) = Inst.instElementList(cache, env2, InnerOuterTypes.emptyInstHierarchy, UnitAbsyn.noStore, DAE.NOMOD(), Prefix.NOPRE(), dummyFunc, ld_mod, nil, impl, InstTypes.INNER_CALL(), ConnectionGraph.EMPTY, DAE.emptySet, true)
                      names = ListUtil.map(ld2, SCodeUtil.elementName)
                      declsTree = AvlSetString.addList(AvlSetString.new(), names)
                      res = if b
                            NONE()
                          else
                            SOME((env2, dae1, declsTree))
                          end
                    (cache, res)
                  end

                  (cache, _, ld, _, _, _)  => begin
                      ld2 = AbsynToSCode.translateEitemlist(ld, SCode.PROTECTED())
                      @match (@match _cons(_, _) = ld2) = ListUtil.filterOnTrue(ld2, SCodeUtil.isNotComponent)
                      str = stringDelimitList(ListUtil.map1(ld2, SCodeDump.unparseElementStr, SCodeDump.defaultOptions), ", ")
                      Error.addSourceMessage(Error.META_INVALID_LOCAL_ELEMENT, list(str), info)
                    (cache, NONE())
                  end

                  (cache, _, ld, _, _, _)  => begin
                      ld2 = AbsynToSCode.translateEitemlist(ld, SCode.PROTECTED())
                      ld3 = ListUtil.select1(ld2, SCodeUtil.isComponentWithDirection, Absyn.INPUT())
                      ld4 = ListUtil.select1(ld2, SCodeUtil.isComponentWithDirection, Absyn.OUTPUT())
                      @match (@match _cons(_, _) = ld2) = listAppend(ld3, ld4)
                      str = stringDelimitList(ListUtil.map1(ld2, SCodeDump.unparseElementStr, SCodeDump.defaultOptions), ", ")
                      Error.addSourceMessage(Error.META_INVALID_LOCAL_ELEMENT, list(str), info)
                    (cache, NONE())
                  end

                  _  => begin
                        Error.addSourceMessage(Error.INTERNAL_ERROR, list("Patternm.addLocalDecls failed"), info)
                      (inCache, NONE())
                  end
                end
              end
               #=  Tranform declarations such as Real x,y; to Real x; Real y;
               =#
               #=  Filter out the components (just to be sure)
               =#
               #=  Transform the element list into a list of element,NOMOD
               =#
               #=  Tranform declarations such as Real x,y; to Real x; Real y;
               =#
               #=  Filter out the components (just to be sure)
               =#
               #=  I don't care that this is slow; it's just for error message generation
               =#
          (outCache, res)
        end

        function checkLocalShadowing(elt::SCode.Element, env::FCore.Graph, inTpl::Tuple{<:FCore.Cache, Bool}) ::Tuple{FCore.Cache, Bool}
              local outTpl::Tuple{FCore.Cache, Bool} = inTpl

              local name::String
              local cache::FCore.Cache
              local b::Bool
              local info::SourceInfo
              local var::SCode.Variability

              @match SCode.COMPONENT(name = name, info = info) = elt
              (cache, _) = inTpl
              try
                @match (cache, DAE.ATTR(variability = var), _, _, _, _, _, _, _) = Lookup.lookupVarInternalIdent(cache, env, name)
                b = begin
                  @match var begin
                    SCode.CONST(__)  => begin
                      true
                    end

                    _  => begin
                        false
                    end
                  end
                end
              catch
                b = true
              end
               #=  Allow shadowing constants. Should be safe since they become values pretty much straight away.
               =#
              if ! b
                Error.addSourceMessage(Error.MATCH_SHADOWING, list(name), info)
                outTpl = (cache, true)
              end
          outTpl
        end

        function resultExps(inCases::List{<:DAE.MatchCase}) ::List{DAE.Exp}
              local exps::List{DAE.Exp}

              exps = begin
                  local exp::DAE.Exp
                  local cases::List{DAE.MatchCase}
                @match inCases begin
                   nil()  => begin
                    nil
                  end

                  DAE.CASE(result = SOME(exp)) <| cases  => begin
                      exps = resultExps(cases)
                    _cons(exp, exps)
                  end

                  _ <| cases  => begin
                    resultExps(cases)
                  end
                end
              end
          exps
        end

         #= Returns true if all patterns in the list are wildcards =#
        function allPatternsWild(ipats::List{<:DAE.Pattern}) ::Bool
              local b::Bool

              b = begin
                  local pats::List{DAE.Pattern}
                @match ipats begin
                   nil()  => begin
                    true
                  end

                  DAE.PAT_WILD(__) <| pats  => begin
                    allPatternsWild(pats)
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Returns true if all patterns in the list are wildcards or as-bindings =#
        function allPatternsAlwaysMatch(ipats::List{<:DAE.Pattern}) ::Bool
              local b::Bool

              b = begin
                  local pat::DAE.Pattern
                  local pats::List{DAE.Pattern}
                @match ipats begin
                   nil()  => begin
                    true
                  end

                  DAE.PAT_WILD(__) <| pats  => begin
                    allPatternsAlwaysMatch(pats)
                  end

                  DAE.PAT_AS(pat = pat) <| pats  => begin
                    allPatternsAlwaysMatch(_cons(pat, pats))
                  end

                  DAE.PAT_AS_FUNC_PTR(pat = pat) <| pats  => begin
                    allPatternsAlwaysMatch(_cons(pat, pats))
                  end

                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Accessor function for DAE.Case =#
        function getCasePatterns(case_::DAE.MatchCase) ::List{DAE.Pattern}
              local pats::List{DAE.Pattern}

              @match DAE.CASE(patterns = pats) = case_
          pats
        end

         #= Sets the patterns field in a DAE.Case =#
        function setCasePatterns(case1::DAE.MatchCase, pats::List{<:DAE.Pattern}) ::DAE.MatchCase
              local case2::DAE.MatchCase

              case2 = begin
                  local localDecls::List{DAE.Element}
                  local body::List{DAE.Statement}
                  local patternGuard::Option{DAE.Exp}
                  local result::Option{DAE.Exp}
                  local jump::ModelicaInteger
                  local resultInfo::SourceInfo
                  local info::SourceInfo
                @match (case1, pats) begin
                  (DAE.CASE(_, patternGuard, localDecls, body, result, resultInfo, jump, info), _)  => begin
                    DAE.CASE(pats, patternGuard, localDecls, body, result, resultInfo, jump, info)
                  end
                end
              end
          case2
        end

         #= Get the constructor index of a uniontype record based on its index in the uniontype =#
        function getValueCtor(ix::ModelicaInteger) ::ModelicaInteger
              local ctor::ModelicaInteger

              ctor = ix + 3
          ctor
        end

        function sortPatternsByComplexity(inPatterns::List{<:DAE.Pattern}) ::List{Tuple{DAE.Pattern, ModelicaInteger}}
              local outPatterns::List{Tuple{DAE.Pattern, ModelicaInteger}}

              outPatterns = ListUtil.toListWithPositions(inPatterns)
              outPatterns = ListUtil.sort(outPatterns, sortPatternsByComplexityWork)
          outPatterns
        end

        function sortPatternsByComplexityWork(tpl1::Tuple{<:DAE.Pattern, ModelicaInteger}, tpl2::Tuple{<:DAE.Pattern, ModelicaInteger}) ::Bool
              local greater::Bool

              local pat1::DAE.Pattern
              local pat2::DAE.Pattern
              local i1::ModelicaInteger
              local i2::ModelicaInteger
              local c1::ModelicaInteger
              local c2::ModelicaInteger

              (pat1, i1) = tpl1
              (pat2, i2) = tpl2
              (_, c1) = traversePattern(pat1, patternComplexity, 0)
              (_, c2) = traversePattern(pat2, patternComplexity, 0)
               #=  If both complexities are equal, keep the original ordering
               =#
               #=  If c1 is 0, and c2 is not 0 we move the left pattern to the end.
               =#
               #=  Else we move the cheaper pattern to the beginning
               =#
              greater = if c1 == c2
                    i1 > i2
                  else
                    if c2 == 0
                          false
                        else
                          if c1 == 0
                                true
                              else
                                c1 > c2
                              end
                        end
                  end
          greater
        end

        function patternComplexity(inPat::DAE.Pattern, inComplexity::ModelicaInteger) ::Tuple{DAE.Pattern, ModelicaInteger}
              local i::ModelicaInteger = inComplexity
              local outPat::DAE.Pattern = inPat

              i = begin
                  local p::DAE.Pattern
                  local exp::DAE.Exp
                @match inPat begin
                  DAE.PAT_CONSTANT(exp = exp)  => begin
                      (_, i) = Expression.traverseExpBottomUp(exp, constantComplexity, i)
                    i
                  end

                  DAE.PAT_CONS(__)  => begin
                    i + 5
                  end

                  DAE.PAT_CALL(knownSingleton = false)  => begin
                    i + 5
                  end

                  DAE.PAT_SOME(__)  => begin
                    i + 5
                  end

                  _  => begin
                      i
                  end
                end
              end
          (outPat, i)
        end

        function constantComplexity(inExp::DAE.Exp, ii::ModelicaInteger) ::Tuple{DAE.Exp, ModelicaInteger}
              local oi::ModelicaInteger
              local outExp::DAE.Exp

              (outExp, oi) = begin
                  local e::DAE.Exp
                  local str::String
                  local i::ModelicaInteger
                @match (inExp, ii) begin
                  (e && DAE.SCONST(str), i)  => begin
                    (e, i + 5 + stringLength(str))
                  end

                  (e && DAE.ICONST(_), i)  => begin
                    (e, i + 1)
                  end

                  (e && DAE.BCONST(_), i)  => begin
                    (e, i + 1)
                  end

                  (e && DAE.RCONST(_), i)  => begin
                    (e, i + 2)
                  end

                  (e, i)  => begin
                    (e, i + 5)
                  end
                end
              end
               #=  lists and such; add a little something in addition to its members....
               =#
          (outExp, oi)
        end

        function addEnvKnownAsBindings(inPat::DAE.Pattern, inEnv::FCore.Graph) ::Tuple{DAE.Pattern, FCore.Graph}
              local env::FCore.Graph = inEnv
              local pat::DAE.Pattern = inPat

              env = begin
                @match pat begin
                  DAE.PAT_AS(__)  => begin
                    addEnvKnownAsBindings2(pat, env, findFirstNonAsPattern(pat.pat))
                  end

                  _  => begin
                      env
                  end
                end
              end
          (pat, env)
        end

        function addEnvKnownAsBindings2(inPat::DAE.Pattern, inEnv::FCore.Graph, firstPattern::DAE.Pattern) ::FCore.Graph
              local env::FCore.Graph = inEnv

              env = begin
                  local name::Absyn.Path
                  local path::Absyn.Path
                  local id::String
                  local scope::String
                  local ty::DAE.Type
                  local pat::DAE.Pattern
                  local fields::List{DAE.Var}
                  local index::ModelicaInteger
                  local knownSingleton::Bool
                  local attr::DAE.Attributes
                  local typeVars::List{DAE.Type}
                @match (inPat, firstPattern) begin
                  (DAE.PAT_AS(id = id, attr = attr), DAE.PAT_CALL(index = index, typeVars = typeVars, fields = fields, knownSingleton = knownSingleton, name = name))  => begin
                      path = AbsynUtil.stripLast(name)
                      ty = DAE.T_METARECORD(name, path, typeVars, index, fields, knownSingleton)
                      env = FGraphUtil.mkComponentNode(env, DAE.TYPES_VAR(id, attr, ty, DAE.UNBOUND(), NONE()), SCode.COMPONENT(id, SCode.defaultPrefixes, SCode.defaultVarAttr, Absyn.TPATH(name, NONE()), SCode.NOMOD(), SCode.noComment, NONE(), AbsynUtil.dummyInfo), DAE.NOMOD(), FCore.VAR_DAE(), FCore.emptyGraph)
                    env
                  end

                  _  => begin
                      env
                  end
                end
              end
          env
        end

        function findFirstNonAsPattern(inPattern::DAE.Pattern) ::DAE.Pattern
              local outPattern::DAE.Pattern

              outPattern = begin
                @match inPattern begin
                  DAE.PAT_AS(pat = outPattern)  => begin
                    findFirstNonAsPattern(outPattern)
                  end

                  _  => begin
                      inPattern
                  end
                end
              end
          outPattern
        end

        function getInputAsBinding(inExp::Absyn.Exp) ::Tuple{Absyn.Exp, List{String}, List{String}}
              local aliasesAndCrefs::List{String}
              local aliases::List{String}
              local exp::Absyn.Exp

              (exp, aliases, aliasesAndCrefs) = begin
                  local id::String
                @match inExp begin
                  Absyn.CREF(componentRef = Absyn.CREF_IDENT(id,  nil()))  => begin
                    (inExp, nil, list(id))
                  end

                  Absyn.AS(id, exp)  => begin
                      (exp, aliases, aliasesAndCrefs) = getInputAsBinding(exp)
                    (exp, _cons(id, aliases), _cons(id, aliasesAndCrefs))
                  end

                  _  => begin
                      (inExp, nil, nil)
                  end
                end
              end
          (exp, aliases, aliasesAndCrefs)
        end

        function addPatternAliasesList(inPatterns::List{<:DAE.Pattern}, inAliases::List{<:List{<:String}}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{List{DAE.Pattern}, FCore.Cache}
              local outCache::FCore.Cache = inCache
              local outPatterns::List{DAE.Pattern} = nil

              local aliases::List{String}
              local rest_aliases::List{List{String}} = inAliases

              for pat in inPatterns
                @match _cons(aliases, rest_aliases) = rest_aliases
                (pat, outCache) = addPatternAliases(pat, aliases, outCache, inEnv)
                outPatterns = _cons(pat, outPatterns)
              end
              outPatterns = listReverse(outPatterns)
          (outPatterns, outCache)
        end

        function addPatternAliases(inPattern::DAE.Pattern, inAliases::List{<:String}, inCache::FCore.Cache, inEnv::FCore.Graph) ::Tuple{DAE.Pattern, FCore.Cache}
              local outCache::FCore.Cache = inCache
              local pat::DAE.Pattern = inPattern

              local attr::DAE.Attributes

              for alias in inAliases
                @match (outCache, DAE.TYPES_VAR(attributes = attr), _, _, _, _) = Lookup.lookupIdent(outCache, inEnv, alias)
                pat = DAE.PAT_AS(alias, NONE(), attr, pat)
              end
          (pat, outCache)
        end

        function addAliasesToEnv(inEnv::FCore.Graph, inTypes::List{<:DAE.Type}, inAliases::List{<:List{<:String}}, info::SourceInfo) ::FCore.Graph
              local outEnv::FCore.Graph

              outEnv = begin
                  local tys::List{DAE.Type}
                  local aliases::List{List{String}}
                  local rest::List{String}
                  local id::String
                  local env::FCore.Graph
                  local ty::DAE.Type
                  local attr::DAE.Attributes
                @match (inEnv, inTypes, inAliases, info) begin
                  (_,  nil(),  nil(), _)  => begin
                    inEnv
                  end

                  (_, _ <| tys,  nil() <| aliases, _)  => begin
                    addAliasesToEnv(inEnv, tys, aliases, info)
                  end

                  (env, ty <| _, id <| rest <| aliases, _)  => begin
                      attr = DAE.dummyAttrInput
                      env = FGraphUtil.mkComponentNode(env, DAE.TYPES_VAR(id, attr, ty, DAE.UNBOUND(), NONE()), SCode.COMPONENT(id, SCode.defaultPrefixes, SCode.defaultVarAttr, Absyn.TPATH(Absyn.IDENT("dummy"), NONE()), SCode.NOMOD(), SCode.noComment, NONE(), info), DAE.NOMOD(), FCore.VAR_DAE(), FCore.emptyGraph)
                    addAliasesToEnv(env, inTypes, _cons(rest, aliases), info)
                  end
                end
              end
          outEnv
        end

        function statementListFindDeadStoreRemoveEmptyStatements(inBody::List{<:DAE.Statement}, localsTree::AvlSetString.Tree, inUseTree::AvlSetString.Tree) ::Tuple{List{DAE.Statement}, AvlSetString.Tree}
              local useTree::AvlSetString.Tree
              local body::List{DAE.Statement}

              (body, useTree) = ListUtil.map1Fold(listReverse(inBody), statementFindDeadStore, localsTree, inUseTree)
              body = ListUtil.select(body, isNotDummyStatement)
              body = listReverse(body)
          (body, useTree)
        end

        function statementFindDeadStore(inStatement::DAE.Statement, localsTree::AvlSetString.Tree, inUseTree::AvlSetString.Tree) ::Tuple{DAE.Statement, AvlSetString.Tree}
              local useTree::AvlSetString.Tree
              local outStatement::DAE.Statement

              (outStatement, useTree) = begin
                  local elseTree::AvlSetString.Tree
                  local body::List{DAE.Statement}
                  local cr::DAE.ComponentRef
                  local exp::DAE.Exp
                  local lhs::DAE.Exp
                  local cond::DAE.Exp
                  local msg::DAE.Exp
                  local level::DAE.Exp
                  local exps::List{DAE.Exp}
                  local else_::DAE.Else
                  local ty::DAE.Type
                  local info::SourceInfo
                  local b::Bool
                  local id::String
                  local index::ModelicaInteger
                  local source::DAE.ElementSource
                @match inStatement begin
                  DAE.STMT_ASSIGN(type_ = ty, exp1 = lhs, exp = exp, source = source && DAE.SOURCE(info = info))  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, inUseTree)
                      lhs = Expression.traverseExpBottomUp(lhs, checkDefUse, (localsTree, useTree, info))
                      outStatement = Algorithm.makeAssignmentNoTypeCheck(ty, lhs, exp, source)
                    (outStatement, useTree)
                  end

                  DAE.STMT_TUPLE_ASSIGN(type_ = ty, expExpLst = exps, exp = exp, source = source && DAE.SOURCE(info = info))  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, inUseTree)
                      @match (DAE.TUPLE(exps), _) = Expression.traverseExpBottomUp(DAE.TUPLE(exps), checkDefUse, (localsTree, useTree, info))
                      outStatement = Algorithm.makeTupleAssignmentNoTypeCheck(ty, exps, exp, source)
                    (outStatement, useTree)
                  end

                  DAE.STMT_ASSIGN_ARR(type_ = ty, lhs = lhs, exp = exp, source = source && DAE.SOURCE(info = info))  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, inUseTree)
                      lhs = Expression.traverseExpBottomUp(lhs, checkDefUse, (localsTree, useTree, info))
                      outStatement = Algorithm.makeArrayAssignmentNoTypeCheck(ty, lhs, exp, source)
                    (outStatement, useTree)
                  end

                  DAE.STMT_IF(exp = exp, statementLst = body, else_ = else_, source = source)  => begin
                      (else_, elseTree) = elseFindDeadStore(else_, localsTree, inUseTree)
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, inUseTree)
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, useTree)
                      useTree = AvlSetString.join(useTree, elseTree)
                    (DAE.STMT_IF(exp, body, else_, source), useTree)
                  end

                  DAE.STMT_FOR(ty, b, id, index, exp, body, source)  => begin
                      ErrorExt.setCheckpoint(getInstanceName())
                      (_, useTree) = ListUtil.map1Fold(body, statementFindDeadStore, localsTree, inUseTree)
                      ErrorExt.rollBack(getInstanceName())
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, useTree)
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, useTree)
                      useTree = AvlSetString.join(useTree, inUseTree)
                    (DAE.STMT_FOR(ty, b, id, index, exp, body, source), useTree)
                  end

                  DAE.STMT_WHILE(exp = exp, statementLst = body, source = source)  => begin
                      ErrorExt.setCheckpoint(getInstanceName())
                      (_, useTree) = ListUtil.map1Fold(body, statementFindDeadStore, localsTree, inUseTree)
                      ErrorExt.rollBack(getInstanceName())
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, useTree)
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, useTree)
                      useTree = AvlSetString.join(useTree, inUseTree)
                    (DAE.STMT_WHILE(exp, body, source), useTree)
                  end

                  DAE.STMT_PARFOR(__)  => begin
                    fail()
                  end

                  DAE.STMT_ASSERT(cond = cond, msg = msg, level = level)  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(cond, useLocalCref, inUseTree)
                      (_, useTree) = Expression.traverseExpBottomUp(msg, useLocalCref, useTree)
                      (_, useTree) = Expression.traverseExpBottomUp(level, useLocalCref, useTree)
                    (inStatement, useTree)
                  end

                  DAE.STMT_TERMINATE(msg = exp)  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, AvlSetString.new())
                    (inStatement, useTree)
                  end

                  DAE.STMT_WHEN(__)  => begin
                    fail()
                  end

                  DAE.STMT_REINIT(__)  => begin
                    fail()
                  end

                  DAE.STMT_NORETCALL(exp = DAE.CALL(path = Absyn.IDENT("fail")))  => begin
                    (inStatement, AvlSetString.new())
                  end

                  DAE.STMT_RETURN(__)  => begin
                    (inStatement, AvlSetString.new())
                  end

                  DAE.STMT_NORETCALL(exp = exp)  => begin
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, inUseTree)
                    (inStatement, useTree)
                  end

                  DAE.STMT_BREAK(__)  => begin
                    (inStatement, inUseTree)
                  end

                  DAE.STMT_CONTINUE(__)  => begin
                    (inStatement, inUseTree)
                  end

                  DAE.STMT_ARRAY_INIT(__)  => begin
                    (inStatement, inUseTree)
                  end

                  DAE.STMT_FAILURE(body = body, source = source)  => begin
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, inUseTree)
                    (DAE.STMT_FAILURE(body, source), useTree)
                  end
                end
              end
               #=  Loops repeat, so check for usage in the whole loop before removing any dead stores.
               =#
               #=  TODO: We should remove ident from the use-tree in case of shadowing... But our avlTree cannot delete
               =#
               #=  Loops repeat, so check for usage in the whole loop before removing any dead stores.
               =#
               #=  The loop might not be entered just like if. The following should not remove all previous uses:
               =#
               #=  while false loop
               =#
               #=    return;
               =#
               #=  end while;
               =#
               #=  No PARFOR in MetaModelica
               =#
               #=  Reset the tree; we do not execute anything after this
               =#
               #=  No when or reinit in functions
               =#
               #=  There is no use after this one, so we can reset the tree
               =#
          (outStatement, useTree)
        end

        function elseFindDeadStore(inElse::DAE.Else, localsTree::AvlSetString.Tree, inUseTree::AvlSetString.Tree) ::Tuple{DAE.Else, AvlSetString.Tree}
              local useTree::AvlSetString.Tree
              local outElse::DAE.Else

              (outElse, useTree) = begin
                  local exp::DAE.Exp
                  local body::List{DAE.Statement}
                  local else_::DAE.Else
                  local elseTree::AvlSetString.Tree
                @match (inElse, localsTree, inUseTree) begin
                  (DAE.NOELSE(__), _, _)  => begin
                    (inElse, inUseTree)
                  end

                  (DAE.ELSEIF(exp, body, else_), _, _)  => begin
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, inUseTree)
                      (_, useTree) = Expression.traverseExpBottomUp(exp, useLocalCref, useTree)
                      (else_, elseTree) = elseFindDeadStore(else_, localsTree, inUseTree)
                      useTree = AvlSetString.join(useTree, elseTree)
                      else_ = DAE.ELSEIF(exp, body, else_)
                    (else_, useTree)
                  end

                  (DAE.ELSE(body), _, _)  => begin
                      (body, useTree) = statementListFindDeadStoreRemoveEmptyStatements(body, localsTree, inUseTree)
                      else_ = DAE.ELSE(body)
                    (else_, useTree)
                  end
                end
              end
          (outElse, useTree)
        end

        function isNotDummyStatement(statement::DAE.Statement) ::Bool
              local b::Bool

              b = Algorithm.isNotDummyStatement(statement)
              Error.assertionOrAddSourceMessage(b || ! Flags.isSet(Flags.PATTERNM_ALL_INFO), Error.META_DEAD_CODE, list("Statement optimised away"), ElementSource.getElementSourceFileInfo(Algorithm.getStatementSource(statement)))
          b
        end

        function makeTupleFromMetaTuple(inExp::DAE.Exp, inType::DAE.Type) ::Tuple{DAE.Exp, DAE.Type}
              local ty::DAE.Type
              local exp::DAE.Exp

              (exp, ty) = begin
                  local exps::List{DAE.Exp}
                  local tys::List{DAE.Type}
                  local tys2::List{DAE.Type}
                  local source::List{Absyn.Path}
                @match (inExp, inType) begin
                  (DAE.META_TUPLE(exps), DAE.T_METATUPLE(types = tys))  => begin
                      tys2 = ListUtil.map(tys, Types.unboxedType)
                      (exps, tys2) = Types.matchTypeTuple(exps, tys, tys2, false)
                    (DAE.TUPLE(exps), DAE.T_TUPLE(tys2, NONE()))
                  end

                  _  => begin
                      (inExp, inType)
                  end
                end
              end
          (exp, ty)
        end

         #= Converts an expression to a list of patterns. If the expression is a tuple
           then the contents of the tuple are returned, otherwise the expression itself
           is returned as a list. =#
        function convertExpToPatterns(inExp::Absyn.Exp) ::List{Absyn.Exp}
              local outInputs::List{Absyn.Exp}

              outInputs = begin
                @match inExp begin
                  Absyn.TUPLE(__)  => begin
                    inExp.expressions
                  end

                  _  => begin
                      list(inExp)
                  end
                end
              end
          outInputs
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

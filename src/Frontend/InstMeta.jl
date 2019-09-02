  module InstMeta 


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
        import ClassInf
        import DAE
        import FCore
        import SCode

        import Flags
        import Lookup
        import SCodeUtil
        import Types

        function fixUniontype(inCache::FCore.Cache, inEnv::FCore.Graph, inState::ClassInf.State, inClassDef::SCode.ClassDef) ::Tuple{FCore.Cache, Option{DAE.Type}} 
              local outType::Option{DAE.Type}
              local cache::FCore.Cache = inCache

              outType = begin
                  local b::Bool
                  local p::Absyn.Path
                  local p2::Absyn.Path
                  local paths::List{Absyn.Path}
                  local typeVarsTypes::List{DAE.Type}
                  local names::List{String}
                  local typeVars::List{String}
                  local singletonType::DAE.EvaluateSingletonType
                  local c::SCode.Element
                  local env_1::FCore.Graph
                @match (inState, inClassDef) begin
                  (ClassInf.META_UNIONTYPE(typeVars = typeVars), SCode.PARTS(__))  => begin
                      p = AbsynUtil.makeFullyQualified(inState.path)
                      names = SCodeUtil.elementNames(list(e for e in inClassDef.elementLst if begin
                         @match e begin
                           SCode.CLASS(restriction = SCode.R_METARECORD(__))  => begin
                             true
                           end
                           
                           _  => begin
                               false
                           end
                         end
                       end))
                      paths = list(AbsynUtil.suffixPath(p, n) for n in names)
                      b = listLength(paths) == 1
                      if b
                        p2 = listGet(paths, 1)
                        singletonType = DAE.EVAL_SINGLETON_TYPE_FUNCTION((arrayCreate(1, (cache, inEnv, p2, NONE()))) -> fixUniontype2(arr = arrayCreate(1, (cache, inEnv, p2, NONE()))))
                      else
                        singletonType = DAE.NOT_SINGLETON()
                      end
                      typeVarsTypes = list(DAE.T_METAPOLYMORPHIC(tv) for tv in typeVars)
                    SOME(DAE.T_METAUNIONTYPE(paths, typeVarsTypes, b, singletonType, p))
                  end
                  
                  _  => begin
                      NONE()
                  end
                end
              end
          (cache, outType)
        end

        function fixUniontype2(arr::Array{<:Tuple{<:FCore.Cache, FCore.Graph, Absyn.Path, Option{<:DAE.Type}}}) ::DAE.Type 
              local singletonType::DAE.Type

              local cache::FCore.Cache
              local env::FCore.Graph
              local p::Absyn.Path
              local ot::Option{DAE.Type}

              (cache, env, p, ot) = arrayGet(arr, 1)
              if isNone(ot)
                (_, singletonType) = Lookup.lookupType(cache, env, p, SOME(sourceInfo()))
                arrayUpdate(arr, 1, (cache, env, p, SOME(singletonType)))
              else
                @match SOME(singletonType) = ot
              end
          singletonType
        end

         #= Checks that an array type is valid. =#
        function checkArrayType(inType::DAE.Type)  
              local el_ty::DAE.Type

              el_ty = Types.arrayElementType(inType)
              @match false = ! Types.isString(el_ty) && Types.isBoxedType(el_ty) || Flags.isSet(Flags.RML)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
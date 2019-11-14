  module LookupUtil


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

        import Absyn

        import AbsynUtil

        import DAE

        import FCore

        import SCode

        import Util

        import CrefForHashTable

        import Config

        import Flags

        import FGraphUtil

        import FNode

        import Prefix

        import SCodeUtil

        import Static

        import UnitAbsyn

        import SCodeDump

        import ErrorExt

        import ValuesUtil

        import Values


        #= returns true if the frame is a for-loop scope or a valueblock scope.
       This is indicated by the name of the frame. =#
       function frameIsImplAddedScope(f::FCore.Node) ::Bool
             local b::Bool

             b = begin
                 local oname::FCore.Name
               @match f begin
                 FCore.N(name = oname)  => begin
                   FCore.isImplicitScope(oname)
                 end

                 _  => begin
                     false
                 end
               end
             end
         b
       end

         #= Looks up a cref and returns SOME(true) if it references an iterator,
           SOME(false) if it references an element in the current scope, and NONE() if
           the name couldn't be found in the current scope at all. =#
        function isIterator(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::DAE.ComponentRef) ::Tuple{Option{Bool}, FCore.Cache}
              local outCache::FCore.Cache
              local outIsIterator::Option{Bool}

              (outIsIterator, outCache) = begin
                  local id::String
                  local cache::FCore.Cache
                  local env::FCore.Graph
                  local ht::FCore.Children
                  local res::Option{Bool}
                  local ic::Option{DAE.Const}
                  local ref::FCore.MMRef
                  local b::Bool
                   #=  Look in the current scope.
                   =#
                @matchcontinue (inCache, inEnv, inCref) begin
                  (cache, FCore.G(scope = ref <| _), _)  => begin
                      ht = FNode.children(FNode.fromRef(ref))
                       #=  Only look up the first part of the cref, we're only interested in if
                       =#
                       #=  it exists and if it's an iterator or not.
                       =#
                      id = CrefForHashTable.crefFirstIdent(inCref)
                      @match (DAE.TYPES_VAR(constOfForIteratorRange = ic), _, _, _, _) = lookupVar2(ht, id, inEnv)
                      b = isSome(ic)
                    (SOME(b), cache)
                  end

                  (cache, FCore.G(scope = ref <| _), _)  => begin
                       #=  If not found, look in the next scope only if the current scope is implicit.
                       =#
                      @match true = frameIsImplAddedScope(FNode.fromRef(ref))
                      (env, _) = FGraphUtil.stripLastScopeRef(inEnv)
                      (res, cache) = isIterator(cache, env, inCref)
                    (res, cache)
                  end

                  _  => begin
                      (NONE(), inCache)
                  end
                end
              end
          (outIsIterator, outCache)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

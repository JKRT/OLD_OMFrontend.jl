  module BackendInterface 


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

        import DAE

        import FCore

        import Prefix

        import Values

        import CevalScript
        import RewriteRules
        import StaticScript

        function cevalInteractiveFunctions(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inMsg::Absyn.Msg, inNumIter::ModelicaInteger) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = CevalScript.cevalInteractiveFunctions(inCache, inEnv, inExp, inMsg, inNumIter)
          (outCache, outValue)
        end

        function cevalCallFunction(inCache::FCore.Cache, inEnv::FCore.Graph, inExp::DAE.Exp, inValues::List{<:Values.Value}, inImplInst::Bool, inMsg::Absyn.Msg, inNumIter::ModelicaInteger = 1) ::Tuple{FCore.Cache, Values.Value} 
              local outValue::Values.Value
              local outCache::FCore.Cache

              (outCache, outValue) = CevalScript.cevalCallFunction(inCache, inEnv, inExp, inValues, inImplInst, inMsg, inNumIter)
          (outCache, outValue)
        end

         #= Note: elabCall_InteractiveFunction is set in the error buffer; the called function should pop it =#
        function elabCallInteractive(inCache::FCore.Cache, inEnv::FCore.Graph, inCref::Absyn.ComponentRef, inExps::List{<:Absyn.Exp}, inNamedArgs::List{<:Absyn.NamedArg}, inImplInst::Bool, inPrefix::Prefix.PrefixType, inInfo::SourceInfo) ::Tuple{FCore.Cache, DAE.Exp, DAE.Properties} 
              local outProperties::DAE.Properties
              local outExp::DAE.Exp
              local outCache::FCore.Cache

              (outCache, outExp, outProperties) = StaticScript.elabCallInteractive(inCache, inEnv, inCref, inExps, inNamedArgs, inImplInst, inPrefix, inInfo)
          (outCache, outExp, outProperties)
        end

        function noRewriteRulesFrontEnd() ::Bool 
              local noRules::Bool

              noRules = RewriteRules.noRewriteRulesFrontEnd()
          noRules
        end

        function rewriteFrontEnd(inExp::Absyn.Exp) ::Tuple{Absyn.Exp, Bool} 
              local isChanged::Bool
              local outExp::Absyn.Exp

              (outExp, isChanged) = RewriteRules.rewriteFrontEnd(inExp)
          (outExp, isChanged)
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
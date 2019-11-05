  module InstDAE 


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

        import ClassInf

        import DAE

        import FCore

        import FGraph

        import InnerOuter

        import SCode

        import ComponentReference

        import Config

        import DAEUtil

        import Debug

        import ElementSource

        import Error

        import Flags

        import InstBinding

        import InstUtil

        import ListUtil
        import SCodeUtil

        import Types

        import DAEDump

        import System

        import Util

        Ident = DAE.Ident  #= an identifier =#

        InstanceHierarchy = InnerOuter.InstHierarchy  #= an instance hierarchy =#

        InstDims = List 

         #= Given a global component name, a type, and a set of attributes, this function declares a component for the DAE result.
          Altough this function returns a list of DAE.Element, only one component is actually declared.
          The functions daeDeclare2 and daeDeclare3 below are helper functions that perform parts of the task.
          Note: Currently, this function can only declare scalar variables, i.e. the element type of an array type is used. To indicate that the variable
          is an array, the InstDims attribute is used. This will need to be redesigned in the futurue, when array variables should not be flattened out in the frontend. =#
        function daeDeclare(inCache::FCore.Cache, inParentEnv::FCore.Graph, inClassEnv::FCore.Graph, inComponentRef::DAE.ComponentRef, inState::ClassInf.SMNode, inType::DAE.Type, inAttributes::SCode.Attributes, visibility::SCode.Visibility, inBinding::Option{<:DAE.Exp}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inStartValue::DAE.StartValue, inVarAttr::Option{<:DAE.VariableAttributes}, inComment::Option{<:SCode.Comment}, io::Absyn.InnerOuter, finalPrefix::SCode.Final, source::DAE.ElementSource #= the origin of the element =#, declareComplexVars::Bool #= if true, declare variables for complex variables, e.g. record vars in functions =#) ::DAE.DAElist 
              local outDae::DAE.DAElist

              outDae = begin
                  local ct1::DAE.ConnectorType
                  local dae::DAE.DAElist
                  local vn::DAE.ComponentRef
                  local daeParallelism::DAE.VarParallelism
                  local ci_state::ClassInf.SMNode
                  local ty::DAE.Type
                  local ct::SCode.ConnectorType
                  local vis::SCode.Visibility
                  local var::SCode.Variability
                  local prl::SCode.Parallelism
                  local dir::Absyn.Direction
                  local e::Option{DAE.Exp}
                  local start::Option{DAE.Exp}
                  local inst_dims::InstDims
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local info::SourceInfo
                  local vk::DAE.VarKind
                  local vd::DAE.VarDirection
                  local vv::DAE.VarVisibility
                @matchcontinue (inCache, inParentEnv, inClassEnv, inComponentRef, inState, inType, inAttributes, visibility, inBinding, inInstDims, inStartValue, inVarAttr, inComment, io, finalPrefix, source, declareComplexVars) begin
                  (_, _, _, vn, ci_state, ty, SCode.ATTR(connectorType = ct, parallelism = prl, variability = var, direction = dir), vis, e, inst_dims, start, dae_var_attr, comment, _, _, _, _)  => begin
                      @match DAE.SOURCE(info, _, _, _, _, _, _) = source
                      ct1 = DAEUtil.toConnectorType(ct, ci_state)
                      daeParallelism = DAEUtil.toDaeParallelism(vn, prl, ci_state, info)
                      vk = InstUtil.makeDaeVariability(var)
                      vd = InstUtil.makeDaeDirection(dir)
                      vv = InstUtil.makeDaeProt(vis)
                      dae_var_attr = DAEUtil.setFinalAttr(dae_var_attr, SCodeUtil.finalBool(finalPrefix))
                      dae = daeDeclare2(vn, ty, ct1, vk, vd, daeParallelism, vv, e, inst_dims, start, dae_var_attr, comment, io, source, declareComplexVars)
                      showDAE(inCache, inParentEnv, inClassEnv, inState, dae)
                    dae
                  end
                  
                  _  => begin
                        @match true = Flags.isSet(Flags.FAILTRACE)
                        Debug.trace("- Inst.daeDeclare failed\\n")
                      fail()
                  end
                end
              end
          outDae
        end

        function showDAE(inCache::FCore.Cache, inParentEnv::FCore.Graph, inClassEnv::FCore.Graph, inState::ClassInf.SMNode, inDAE::DAE.DAElist)  
              _ = begin
                  local str::String
                  local sstr::String
                  local comp::DAE.Element
                  local dae::DAE.DAElist
                  local els::List{DAE.Element}
                @matchcontinue (inCache, inParentEnv, inClassEnv, inState, inDAE) begin
                  (_, _, _, _, _)  => begin
                      @match false = Flags.isSet(Flags.SHOW_DAE_GENERATION)
                    ()
                  end
                  
                  (_, _, _, _, _)  => begin
                      els = DAEUtil.daeElements(inDAE)
                      sstr = ClassInf.printStateStr(inState)
                      sstr = "'" + sstr + "'"
                      comp = DAE.COMP(sstr, els, DAE.emptyElementSource, NONE())
                      dae = DAE.DAE_LIST(list(comp))
                      str = if System.getPartialInstantiation()
                            " partial"
                          else
                            " full"
                          end
                      print("DAE: parent: " + FGraph.getGraphNameStr(inParentEnv) + " class: " + FGraph.getGraphNameStr(inClassEnv) + " state: " + sstr + str + "\\n" + DAEDump.dumpStr(dae, DAE.AvlTreePathFunction.Tree.EMPTY()) + "\\n")
                    ()
                  end
                  
                  (_, _, _, _, _)  => begin
                      str = if System.getPartialInstantiation()
                            " partial"
                          else
                            " full"
                          end
                      print("DAE: " + ClassInf.printStateStr(inState) + str + " - could not print\\n")
                    ()
                  end
                  
                  _  => begin
                      ()
                  end
                end
              end
        end

         #= Helper function to daeDeclare. =#
        function daeDeclare2(inComponentRef::DAE.ComponentRef, inType::DAE.Type, inConnectorType::DAE.ConnectorType, inVarKind::DAE.VarKind, inVarDirection::DAE.VarDirection, inParallelism::DAE.VarParallelism, protection::DAE.VarVisibility, inExpExpOption::Option{<:DAE.Exp}, inInstDims::List{Any #= <:List{<:DAE.Dimension} =#}, inStartValue::DAE.StartValue, inAttr::Option{<:DAE.VariableAttributes}, inComment::Option{<:SCode.Comment}, io::Absyn.InnerOuter, source::DAE.ElementSource #= the origin of the element =#, declareComplexVars::Bool) ::DAE.DAElist 
              local outDAe::DAE.DAElist

              outDAe = begin
                  local vn::DAE.ComponentRef
                  local c::DAE.ComponentRef
                  local ct::DAE.ConnectorType
                  local kind::DAE.VarKind
                  local dir::DAE.VarDirection
                  local daePrl::DAE.VarParallelism
                  local e::Option{DAE.Exp}
                  local start::Option{DAE.Exp}
                  local inst_dims::InstDims
                  local dae_var_attr::Option{DAE.VariableAttributes}
                  local comment::Option{SCode.Comment}
                  local l::List{String}
                  local dae::DAE.DAElist
                  local ci::ClassInf.SMNode
                  local dim::ModelicaInteger
                  local s::String
                  local ty::DAE.Type
                  local tp::DAE.Type
                  local prot::DAE.VarVisibility
                  local finst_dims::List{DAE.Dimension}
                  local path::Absyn.Path
                  local tty::DAE.Type
                  local info::SourceInfo
                @matchcontinue (inComponentRef, inType, inConnectorType, inVarKind, inVarDirection, inParallelism, protection, inExpExpOption, inInstDims, inStartValue, inAttr, inComment, io, source, declareComplexVars) begin
                  (vn, DAE.T_INTEGER(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, DAE.T_INTEGER_DEFAULT, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, DAE.T_REAL(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, DAE.T_REAL_DEFAULT, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, DAE.T_BOOL(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, DAE.T_BOOL_DEFAULT, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, DAE.T_CLOCK(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, DAE.T_CLOCK_DEFAULT, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, DAE.T_STRING(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, DAE.T_STRING_DEFAULT, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (_, DAE.T_ENUMERATION(index = SOME(_)), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                    DAE.emptyDae
                  end
                  
                  (vn, ty && DAE.T_ENUMERATION(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, ty, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, ty && DAE.T_COMPLEX(complexClassType = ClassInf.EXTERNAL_OBJ(_)), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, ty, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, DAE.T_SUBTYPE_BASIC(complexType = tp), ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, _, _, _)  => begin
                      (_, dae_var_attr) = InstBinding.instDaeVariableAttributes(FCoreUtil.emptyCache(), FGraph.empty(), DAE.NOMOD(), tp, nil)
                      dae = daeDeclare2(vn, tp, ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, io, source, declareComplexVars)
                    dae
                  end
                  
                  (vn, DAE.T_ARRAY(dims = DAE.DIM_INTEGER(__) <|  nil(), ty = tp), ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, _, _, _)  => begin
                      dae = daeDeclare2(vn, tp, ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, io, source, declareComplexVars)
                    dae
                  end
                  
                  (vn, DAE.T_ARRAY(ty = tp), ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, _, _, _)  => begin
                      @match false = Config.splitArrays()
                      dae = daeDeclare2(vn, tp, ct, kind, dir, daePrl, prot, e, inst_dims, start, dae_var_attr, comment, io, source, declareComplexVars)
                    dae
                  end
                  
                  (vn, DAE.T_ARRAY(dims = DAE.DIM_UNKNOWN(__) <|  nil()), _, _, _, _, _, _, _, _, _, _, _, _, _)  => begin
                      @match true = Config.splitArrays()
                      s = ComponentReference.printComponentRefStr(vn)
                      info = ElementSource.getElementSourceFileInfo(source)
                      Error.addSourceMessage(Error.DIMENSION_NOT_KNOWN, list(s), info)
                    fail()
                  end
                  
                  (vn, ty && DAE.T_COMPLEX(complexClassType = ClassInf.RECORD(_)), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, true)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, ty, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, tty && DAE.T_FUNCTION(__), ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      finst_dims = ListUtil.flatten(inst_dims)
                      path = ComponentReference.crefToPath(vn)
                      tty.path = path
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, tty, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  (vn, ty, ct, kind, dir, daePrl, prot, e, inst_dims, _, dae_var_attr, comment, _, _, _)  => begin
                      @match true = Config.acceptMetaModelicaGrammar()
                      @match true = Types.isBoxedType(ty)
                      finst_dims = ListUtil.flatten(inst_dims)
                    DAE.DAE_LIST(list(DAE.VAR(vn, kind, dir, daePrl, prot, ty, e, finst_dims, ct, source, dae_var_attr, comment, io)))
                  end
                  
                  _  => begin
                      DAE.emptyDae
                  end
                end
              end
               #=  BTH
               =#
               #=  We should not declare each enumeration value of an enumeration when instantiating,
               =#
               #=  e.g Myenum my !=> constant EnumType my.enum1,... {DAE.VAR(vn, kind, dir, DAE.ENUM, e, inst_dims)}
               =#
               #=  instantiation of complex type extending from basic type
               =#
               #=  complex type that is ExternalObject
               =#
               #=  instantiation of complex type extending from basic type
               =#
               #=  array that extends basic type
               =#
               #=  Arrays with unknown dimension are allowed if not expanded
               =#
               #=  if arrays are expanded and dimension is unknown, report an error
               =#
               #=  Complex/Record components, only if declareComplexVars is true
               =#
               #=  MetaModelica extensions
               =#
               #=  MetaModelica extension
               =#
               #= /*----------------------------*/ =#
          outDAe
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
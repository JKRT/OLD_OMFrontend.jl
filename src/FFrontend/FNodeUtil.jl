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

module FNodeUtil
#= anything that is not top, class or a component is an implicit scope! =#
using MetaModelica
using ExportAll

@importDBG FCore
@importDBG SCode
@importDBG SCodeUtil

FunctionRefIs = Function
Filter = Function
FunctionRefIs = Function
Apply = Function

Name = FCore.Name
Names = FCore.Names
Id = FCore.Id
Seq = FCore.Seq
Next = FCore.Next
Node = FCore.Node
Data = FCore.Data
Kind = FCore.Kind
MMRef = FCore.MMRef
Refs = FCore.Refs
import FCore.RefTree
@importDBG FCoreUtil
Children = FCore.Children
Parents = FCore.Parents
Scope = FCore.Scope
ImportTable = FCore.ImportTable
Graph = FCore.Graph
Extra = FCore.Extra
Visited = FCore.Visited
Import = FCore.Import

function isImplicitScope(inNode::Node) ::Bool
  local b::Bool

  b = begin
    @match inNode begin
      FCore.N(data = FCore.TOP(__))  => begin
        false
      end

      FCore.N(data = FCore.CL(__))  => begin
        false
      end

      FCore.N(data = FCore.CO(__))  => begin
        false
      end

      FCore.N(data = FCore.CC(__))  => begin
        false
      end

      FCore.N(data = FCore.FS(__))  => begin
        false
      end

      FCore.N(data = FCore.MS(__))  => begin
        false
      end

      FCore.N(data = FCore.VR(__))  => begin
        false
      end

      _  => begin
        true
      end
    end
  end
  b
end

#= anything that is not a class or a component is an implicit scope! =#
function isRefImplicitScope(inRef::MMRef) ::Bool
  local b::Bool

  b = isImplicitScope(fromRef(inRef))
  b
end

function isReference(inNode::Node) ::Bool
  local b::Bool

  b = begin
    @match inNode begin
      FCore.N(data = FCore.REF(__))  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  b
end

function isUserDefined(inNode::Node) ::Bool
  local b::Bool

  b = begin
    local p::MMRef
    @match inNode begin
      FCore.N(data = FCore.CL(kind = FCore.USERDEFINED(__)))  => begin
        true
      end

      FCore.N(data = FCore.CO(kind = FCore.USERDEFINED(__)))  => begin
        true
      end

      _ where (hasParents(inNode))  => begin
        @match _cons(p, _) = parents(inNode)
        b = isRefUserDefined(p)
        b
      end

      _  => begin
        false
      end
    end
  end
  #=  any parent is userdefined?
  =#
  b
end

function isTop(inNode::Node) ::Bool
  local b::Bool

  b = begin
    @match inNode begin
      FCore.N(data = FCore.TOP(__))  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  b
end

function isExtends(inNode::Node) ::Bool
  local b::Bool

  b = begin
    @match inNode begin
      FCore.N(data = FCore.EX(__))  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  b
end

function isDerived(inNode::Node) ::Bool
  local b::Bool

  b = begin
    local e::SCode.Element
    @match inNode begin
      FCore.N(data = FCore.CL(e = e))  => begin
        SCodeUtil.isDerivedClass(e)
      end

      _  => begin
        false
      end
    end
  end
  b
end

function isClass(inNode::Node) ::Bool
  local b::Bool

  b = begin
    @match inNode begin
      FCore.N(data = FCore.CL(__))  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  b
end

@exportAll

end #=End of FNodeUtil=#

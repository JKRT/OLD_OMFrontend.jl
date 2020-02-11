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

module FCore

using MetaModelica
#= ExportAll is not good practice but it makes it so that we do not have to write export after each functixon :( =#
using ExportAll
  #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#
import Setfield

@UniontypeDecl ImportTable
@UniontypeDecl Node
@UniontypeDecl ModScope
@UniontypeDecl Data
@UniontypeDecl Kind
@UniontypeDecl Status
@UniontypeDecl Visit
@UniontypeDecl Visited
@UniontypeDecl VAvlTree
@UniontypeDecl VAvlTreeValue
@UniontypeDecl Extra
@UniontypeDecl Graph
@UniontypeDecl Top
@UniontypeDecl Cache
@UniontypeDecl ScopeType

  #The question is can we just use Ref? I think so. Add Compatabilty for MetaModelica.jl for now...
  MMRef = Array  #= array of 1 =#

#=Redef of standard types in this file=#
const Name = String  #= an identifier is just a string =#
const Names = List  #= list of names =#
println("FCore Hello1")

module RefTree
  using MetaModelica
  using ExportAll
  import BaseAvlTree
  import BaseAvlSet
  import FCore.Name
  import FCore.MMRef
  import FCore.Node
  using BaseAvlTree
  Key = String
  Value = MMRef

function get(tree, key::Key)::MMRef
    local value::Value
    local k::Key
    k = begin
        @match tree begin
            NODE(__)  => begin
                tree.key
            end
            LEAF(__)  => begin
                tree.key
            end
        end
    end
    value = begin
        @match (keyCompare(key, k), tree) begin
            (0, LEAF(__))  => begin
                tree.value
            end

            (0, NODE(__))  => begin
                tree.value
            end

            (1, NODE(__))  => begin
                get(tree.right, key)
            end

            (-1, NODE(__))  => begin
                get(tree.left, key)
            end
        end
    end
    value
end

  function BaseAvlTree.keyStr(s)::String
    s
  end

  function BaseAvlTree.keyCompare(key1::String, key2::String)
    stringCompare(key1, key2)
  end

  function BaseAvlTree.valueStr(inValue)::String
    local s::String
    @match Node.N(name = s) = arrayGet(inValue, 1)
    s
  end

  @exportAll()
end

@importDBG Absyn
const Import = Absyn.Import
const Id = ModelicaInteger
const Seq = ModelicaInteger
const Next = Seq
const Refs = List
const Parents = Refs
const Scope = Refs
const Children = RefTree.Tree

@importDBG AbsynUtil
@importDBG AvlSetCR
@importDBG DAE
@importDBG Mutable
using Mutable: MutableType
@importDBG SCode
@importDBG Prefix
@importDBG Config

@Uniontype ImportTable begin
  @Record IMPORT_TABLE begin

    #=  Imports should not be inherited, but removing them from the node
    =#
    #=  when doing lookup through extends causes problems for the lookup later
    =#
    #=  on, because for example components may have types that depends on
    =#
    #=  imports.  The hidden flag allows the lookup to 'hide' the imports
    =#
    #=  temporarily, without actually removing them.
    =#
    hidden #= If true means that the imports are hidden. =#::Bool
    qualifiedImports::List{Import}
    unqualifiedImports::List{Import}
  end
end

const emptyScope = nil #= empty scope =#::Scope
const emptyImportTable = IMPORT_TABLE(false, nil, nil)::ImportTable


  @Uniontype Node begin
    @Record N begin

      name #= node name, class/component/extends name, etc. see also *NodeName in above =#::Name
      id #= Unique node id =#::Id
      parents #= A node can have several parents depending on the context =#::Parents
      children #= List of uniquely named classes and variables =#::Children
      data #= More data for this node, Class, Var, etc =#::Data
    end
  end

#= Used to know where a modifier came from, for error reporting. =#
@Uniontype ModScope begin
  @Record MS_COMPONENT begin

    name::String
  end

  @Record MS_EXTENDS begin

    path::Absyn.Path
  end

  @Record MS_DERIVED begin

    path::Absyn.Path
  end

  @Record MS_CLASS_EXTENDS begin

    name::String
  end

  @Record MS_CONSTRAINEDBY begin

    path::Absyn.Path
  end
end

@Uniontype Data begin
  @Record TOP begin

  end

  @Record IT begin

    i #= instantiated component =#::DAE.Var
  end

  @Record IM begin

    i #= imports =#::ImportTable
  end

  @Record CL begin
    e::SCode.Element
    pre::Prefix.PrefixType
    mod #= modification =#::DAE.Mod
    kind #= usedefined, builtin, basic type =#::Kind
    status #= if it is untyped, typed or fully instantiated (dae) =#::Status
  end

  @Record CO begin

    e::SCode.Element
    mod #= modification =#::DAE.Mod
    kind #= usedefined, builtin, basic type =#::Kind
    status #= if it is untyped, typed or fully instantiated (dae) =#::Status
  end

  @Record EX begin

    e::SCode.Element
    mod #= modification =#::DAE.Mod
  end

  @Record DU begin

    els::List{SCode.Element}
  end

  @Record FT begin

    tys #= list since several types with the same name can exist in the same scope (overloading) =#::List{DAE.Type}
  end

  @Record AL begin

    name #= al or ial (initial) =#::Name
    a::List{SCode.AlgorithmSection}
  end

  @Record EQ begin

    name #= eq or ieq (initial) =#::Name
    e::List{SCode.Equation}
  end

  @Record OT begin

    constrainLst::List{SCode.ConstraintSection}
    clsAttrs::List{Absyn.NamedArg}
  end

  @Record ED begin

    ed::SCode.ExternalDecl
  end

  @Record FS begin

    fis::Absyn.ForIterators
  end

  @Record FI begin

    fi::Absyn.ForIterator
  end

  @Record MS begin

    e::Absyn.Exp
  end

  @Record MO begin

    m::SCode.Mod
  end

  @Record EXP begin

    name #= what is the expression for =#::String
    e::Absyn.Exp
  end

  @Record CR begin

    r::Absyn.ComponentRef
  end

  @Record DIMS begin

    name #= what are the dimensions for, type or component =#::String
    dims::Absyn.ArrayDim
  end

  @Record CC begin

    cc::SCode.ConstrainClass
  end

  @Record REF begin

    target::Scope
  end

  @Record ND begin

    scopeType::Option{ScopeType}
  end

  @Record VR begin

    source::Scope
    p::Prefix.PrefixType
    m::DAE.Mod
    scopeType::Option{ScopeType}
  end

  @Record ASSERT begin

    message::String
  end

  @Record STATUS begin

    isInstantiating::Bool
  end
end


@Uniontype Kind begin
  @Record USERDEFINED begin

  end

  @Record BUILTIN begin

  end

  @Record BASIC_TYPE begin

  end
end

#= Used to distinguish between different phases of the instantiation of a component
A component is first added to environment untyped. It can thereafter be instantiated to get its type
and finally instantiated to produce the DAE. These three states are indicated by this datatype. =#
@Uniontype Status begin
  @Record VAR_UNTYPED begin

  end

  @Record VAR_TYPED begin

  end

  @Record VAR_DAE begin

  end

  @Record VAR_DELETED begin

  end

  @Record CLS_UNTYPED begin

  end

  @Record CLS_PARTIAL begin

  end

  @Record CLS_FULL begin

  end

  @Record CLS_INSTANCE begin

    instanceOf::String
  end
end

#=  ************************ FVisit structures *************************** =#

#= Visit Node Info =#
@Uniontype Visit begin
  @Record VN begin

    ref #= which node it is =#::MMRef
    seq #= order in which was visited =#::Seq
  end
end

#= Visited structure is an AvlTree Id <-> Visit =#
@Uniontype Visited begin
  @Record V begin

    tree::VAvlTree
    next #= the next visit node id =#::Next
  end
end

VAvlKey = Id

VAvlValue = Visit

#= The binary tree data structure for visited =#
@Uniontype VAvlTree begin
  @Record VAVLTREENODE begin

    value #= Value =#::Option{VAvlTreeValue}
    height #= heigth of tree, used for balancing =#::ModelicaInteger
    left #= left subtree =#::Option{VAvlTree}
    right #= right subtree =#::Option{VAvlTree}
  end
end

#= Each node in the binary tree can have a value associated with it. =#
@Uniontype VAvlTreeValue begin
  @Record VAVLTREEVALUE begin

    key #= Key =#::VAvlKey
    value #= Value =#::VAvlValue
  end
end

const emptyVAvlTree = VAVLTREENODE(NONE(), 0, NONE(), NONE())::VAvlTree
#=  ************************ FGraph structures *************************** =#

#= propagate more info into env if needed =#
@Uniontype Extra begin
  @Record EXTRA begin

    topModel::Absyn.Path
  end
end

#= graph =#
@Uniontype Graph begin
  @Record G begin
    top #= the top node =#::Top
    scope #= current scope =#::Scope
  end
  @Record EG begin
    name::Name
  end
end

const emptyGraph = EG("empty")

@Uniontype Top begin
  @Record GTOP begin
    graph::Array{Graph}
    name #= name of the graph =#::Name
    node #= the top node =#::MMRef
    extra #= extra information =#::Extra
  end
end

const dummyTopModel = Absyn.IDENT("EMPTY")::Absyn.Path
const dummyExtra = EXTRA(dummyTopModel)::Extra
const recordConstructorSuffix = "recordconstructor"::String
const forScopeName = "for loop scope" #= a unique scope used in for equations =#::String
const forIterScopeName = "foriter loop scope" #= a unique scope used in for iterators =#::String
const parForScopeName = "pafor loop scope" #= a unique scope used in parfor loops =#::String
const parForIterScopeName = "parforiter loop scope" #= a unique scope used in parfor iterators =#::String
const matchScopeName = "match scope" #= a unique scope used by match expressions =#::String
const caseScopeName = "case scope" #= a unique scope used by match expressions; to be removed when local decls are deprecated =#::String
const patternTypeScope = "pattern type scope" #= a scope for specializing pattern types =#::String
const implicitScopeNames = list(forScopeName, forIterScopeName, parForScopeName, parForIterScopeName, matchScopeName, caseScopeName, patternTypeScope)::List
const firstId = 0::Id

#=  ************************ Cache structures *************************** =#

StructuralParameters = Tuple
# test = DAE.FunctionTree

@Uniontype Cache begin
  @Record CACHE begin

    initialGraph #= and the initial environment =#::Option{Graph}
    functions #= set of Option<DAE.Function>; NONE() means instantiation started; SOME() means it's finished =#::MutableType #= {DAE.FunctionTree} =#
    evaluatedParams #= ht of prefixed crefs and a stack of evaluated but not yet prefix crefs =#::StructuralParameters
    modelName #= name of the model being instantiated =#::Absyn.Path
  end

  @Record NO_CACHE begin

  end
end

@Uniontype ScopeType begin
  @Record FUNCTION_SCOPE begin

  end

  @Record CLASS_SCOPE begin

  end

  @Record PARALLEL_SCOPE begin

  end
end

function isImplicitScope(inName::Name) ::Bool
  local isImplicit::Bool

  isImplicit = begin
    local id::Name
    @matchcontinue inName begin
      id  => begin
        stringGet(id, 1) == 36
      end

      _  => begin
        false
      end
    end
  end
  #=  \"$\"
  =#
  isImplicit
end

#= Returns true if the status indicates a deleted conditional component,
otherwise false. =#
function isDeletedComp(status::Status) ::Bool
  local isDeleted::Bool

  isDeleted = begin
    @match status begin
      VAR_DELETED(__)  => begin
        true
      end

      _  => begin
        false
      end
    end
  end
  isDeleted
end

#= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
@exportAll()
end

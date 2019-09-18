  module NFInstTypes 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl Element 
    @UniontypeDecl Class 
    @UniontypeDecl Function 
    @UniontypeDecl Dimension 
    @UniontypeDecl Binding 
    @UniontypeDecl Component 
    @UniontypeDecl Condition 
    @UniontypeDecl ParamType 
    @UniontypeDecl Modifier 
    @UniontypeDecl ConstrainingClass 
    @UniontypeDecl Prefixes 
    @UniontypeDecl VarArgs 
    @UniontypeDecl DaePrefixes 
    @UniontypeDecl Equation 
    @UniontypeDecl Statement 
    @UniontypeDecl FunctionSlot 
    @UniontypeDecl EntryOrigin 
    @UniontypeDecl Entry 
    @UniontypeDecl ScopeType 
    @UniontypeDecl Frame 
    @UniontypeDecl AvlTree 
    @UniontypeDecl AvlTreeValue 
    
    Env = List

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
         #= public import NFConnect2;
         =#

        import DAE

        import NFInstPrefix

        import SCode

        Prefix = NFInstPrefix.Prefix 

         @Uniontype Element begin
              @Record ELEMENT begin

                       component::Component
                       cls::Class
              end

              @Record CONDITIONAL_ELEMENT begin

                       component::Component
              end

              @Record EXTENDED_ELEMENTS begin

                       baseClass::Absyn.Path
                       cls::Class
                       ty::DAE.Type
              end
         end

         @Uniontype Class begin
              @Record COMPLEX_CLASS begin

                       name::Absyn.Path
                       components::List{Element}
                       equations::List{Equation}
                       initialEquations::List{Equation}
                       algorithms::List{List{Statement}}
                       initialAlgorithms::List{List{Statement}}
              end

              @Record BASIC_TYPE begin

                       name::Absyn.Path
              end
         end

         @Uniontype Function begin
              @Record FUNCTION begin

                       path::Absyn.Path
                       inputs::List{Element}
                       outputs::List{Element}
                       locals::List{Element}
                       algorithms #= TODO: Add default bindings =#::List{Statement}
              end

              @Record RECORD_CONSTRUCTOR begin

                       path::Absyn.Path
                       recType::DAE.Type
                       inputs #= componets of the original record which CAN be modified =#::List{Element}
                       locals #= componets of the original record which CAN NOT be modified (protected, final, constant WITH binding) =#::List{Element}
                       algorithms #= TODO: Add default bindings =#::List{Statement}
              end
         end

         @Uniontype Dimension begin
              @Record UNTYPED_DIMENSION begin

                       dimension::DAE.Dimension
                       isProcessing::Bool
              end

              @Record TYPED_DIMENSION begin

                       dimension::DAE.Dimension
              end
         end

         @Uniontype Binding begin
              @Record UNBOUND begin

              end

              @Record RAW_BINDING begin

                       bindingExp::Absyn.Exp
                       env::Env
                       propagatedDims #= See NFSCodeMod.propagateMod. =#::ModelicaInteger
                       info::SourceInfo
              end

              @Record UNTYPED_BINDING begin

                       bindingExp::DAE.Exp
                       isProcessing::Bool
                       propagatedDims #= See NFSCodeMod.propagateMod. =#::ModelicaInteger
                       info::SourceInfo
              end

              @Record TYPED_BINDING begin

                       bindingExp::DAE.Exp
                       bindingType::DAE.Type
                       propagatedDims #= See NFSCodeMod.propagateMod. =#::ModelicaInteger
                       info::SourceInfo
              end
         end

         @Uniontype Component begin
              @Record UNTYPED_COMPONENT begin

                       name::Absyn.Path
                       baseType::DAE.Type
                       dimensions::Array{Dimension}
                       prefixes::Prefixes
                       paramType::ParamType
                       binding::Binding
                       info::SourceInfo
              end

              @Record TYPED_COMPONENT begin

                       name::Absyn.Path
                       ty::DAE.Type
                       parent::Option{Component}
                       #= NO_COMPONENT?
                       =#
                       prefixes::DaePrefixes
                       binding::Binding
                       info::SourceInfo
              end

              @Record CONDITIONAL_COMPONENT begin

                       name::Absyn.Path
                       condition::DAE.Exp
                       element::SCode.Element
                       modifier::Modifier
                       prefixes::Prefixes
                       env::Env
                       prefix::Prefix
                       info::SourceInfo
              end

              @Record DELETED_COMPONENT begin

                       name::Absyn.Path
              end

              @Record OUTER_COMPONENT begin

                       name::Absyn.Path
                       innerName::Option{Absyn.Path}
              end

              @Record COMPONENT_ALIAS begin

                       componentName::Absyn.Path
              end
         end

         @Uniontype Condition begin
              @Record SINGLE_CONDITION begin

                       condition::Bool
              end

              @Record ARRAY_CONDITION begin

                       conditions::List{Condition}
              end
         end

         @Uniontype ParamType begin
              @Record NON_PARAM begin

              end

              @Record NON_STRUCT_PARAM begin

              end

              @Record STRUCT_PARAM begin

              end
         end

         @Uniontype Modifier begin
              @Record MODIFIER begin

                       name::String
                       finalPrefix::SCode.Final
                       eachPrefix::SCode.Each
                       binding::Binding
                       subModifiers::List{Modifier}
                       info::SourceInfo
              end

              @Record REDECLARE begin

                       finalPrefix::SCode.Final
                       eachPrefix::SCode.Each
                       element::SCode.Element
                       env::Env
                       mod::Modifier
                       constrainingClass::Option{ConstrainingClass}
              end

              @Record NOMOD begin

              end
         end

         @Uniontype ConstrainingClass begin
              @Record CONSTRAINING_CLASS begin

                       classPath::Absyn.Path
                       mod::Modifier
              end
         end

         @Uniontype Prefixes begin
              @Record NO_PREFIXES begin

              end

              @Record PREFIXES begin

                       visibility::SCode.Visibility
                       variability::SCode.Variability
                       finalPrefix::SCode.Final
                       innerOuter::Absyn.InnerOuter
                       direction::Tuple{Absyn.Direction, SourceInfo}
                       connectorType::Tuple{SCode.ConnectorType, SourceInfo}
                       varArgs::VarArgs
              end
         end

         const DEFAULT_PROTECTED_PREFIXES = PREFIXES(SCode.PROTECTED(), SCode.VAR(), SCode.NOT_FINAL(), Absyn.NOT_INNER_OUTER(), (Absyn.BIDIR(), AbsynUtil.dummyInfo), (SCode.POTENTIAL(), Absyn.dummyInfo), NO_VARARG())::Prefixes

         const DEFAULT_INPUT_PREFIXES = PREFIXES(SCode.PUBLIC(), SCode.VAR(), SCode.NOT_FINAL(), Absyn.NOT_INNER_OUTER(), (Absyn.INPUT(), AbsynUtil.dummyInfo), (SCode.POTENTIAL(), Absyn.dummyInfo), NO_VARARG())::Prefixes

         @Uniontype VarArgs begin
              @Record NO_VARARG begin

              end

              @Record IS_VARARG begin

              end
         end

         @Uniontype DaePrefixes begin
              @Record NO_DAE_PREFIXES begin

              end

              @Record DAE_PREFIXES begin

                       visibility::DAE.VarVisibility
                       variability::DAE.VarKind
                       finalPrefix::SCode.Final
                       innerOuter::Absyn.InnerOuter
                       direction::DAE.VarDirection
                       connectorType::DAE.ConnectorType
              end
         end

         const DEFAULT_CONST_DAE_PREFIXES = DAE_PREFIXES(DAE.PUBLIC(), DAE.CONST(), SCode.NOT_FINAL(), Absyn.NOT_INNER_OUTER(), DAE.BIDIR(), DAE.NON_CONNECTOR())::DaePrefixes

         @Uniontype Equation begin
              @Record EQUALITY_EQUATION begin

                       lhs #= The left hand side expression. =#::DAE.Exp
                       rhs #= The right hand side expression. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record CONNECT_EQUATION begin

                       lhs #= The left hand side component. =#::DAE.ComponentRef
                       #= NFConnect2.Face lhsFace \"The face of the lhs component, inside or outside.\";
                       =#
                       lhsType #= The type of the lhs component. =#::DAE.Type
                       rhs #= The right hand side component. =#::DAE.ComponentRef
                       #= NFConnect2.Face rhsFace \"The face of the rhs component, inside or outside.\";
                       =#
                       rhsType #= The type of the rhs component. =#::DAE.Type
                       prefix::Prefix
                       info::SourceInfo
              end

              @Record FOR_EQUATION begin

                       name #= The name of the iterator variable. =#::String
                       index #= The index of the iterator variable. =#::ModelicaInteger
                       indexType #= The type of the index/iterator variable. =#::DAE.Type
                       range #= The range expression to loop over. =#::Option{DAE.Exp}
                       body #= The body of the for loop. =#::List{Equation}
                       info::SourceInfo
              end

              @Record IF_EQUATION begin

                       branches #= List of branches, where each branch is a tuple of a condition and a body. =#::List{Tuple{DAE.Exp, List{Equation}}}
                       info::SourceInfo
              end

              @Record WHEN_EQUATION begin

                       branches #= List of branches, where each branch is a tuple of a condition and a body. =#::List{Tuple{DAE.Exp, List{Equation}}}
                       info::SourceInfo
              end

              @Record ASSERT_EQUATION begin

                       condition #= The assert condition. =#::DAE.Exp
                       message #= The message to display if the assert fails. =#::DAE.Exp
                       level #= Error or warning =#::DAE.Exp
                       info::SourceInfo
              end

              @Record TERMINATE_EQUATION begin

                       message #= The message to display if the terminate triggers. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record REINIT_EQUATION begin

                       cref #= The variable to reinitialize. =#::DAE.ComponentRef
                       reinitExp #= The new value of the variable. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record NORETCALL_EQUATION begin

                       exp::DAE.Exp
                       info::SourceInfo
              end
         end

         @Uniontype Statement begin
              @Record ASSIGN_STMT begin

                       lhs #= The asignee =#::DAE.Exp
                       rhs #= The expression =#::DAE.Exp
                       info::SourceInfo
              end

              @Record FUNCTION_ARRAY_INIT begin

                       name::String
                       ty::DAE.Type
                       info::SourceInfo
              end

              @Record FOR_STMT begin

                       name #= The name of the iterator variable. =#::String
                       index #= The index of the scope of the iterator variable. =#::ModelicaInteger
                       indexType #= The type of the index/iterator variable. =#::DAE.Type
                       range #= The range expression to loop over. =#::Option{DAE.Exp}
                       body #= The body of the for loop. =#::List{Statement}
                       info::SourceInfo
              end

              @Record IF_STMT begin

                       branches #= List of branches, where each branch is a tuple of a condition and a body. =#::List{Tuple{DAE.Exp, List{Statement}}}
                       info::SourceInfo
              end

              @Record WHEN_STMT begin

                       branches #= List of branches, where each branch is a tuple of a condition and a body. =#::List{Tuple{DAE.Exp, List{Statement}}}
                       info::SourceInfo
              end

              @Record ASSERT_STMT begin

                       condition #= The assert condition. =#::DAE.Exp
                       message #= The message to display if the assert fails. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record TERMINATE_STMT begin

                       message #= The message to display if the terminate triggers. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record REINIT_STMT begin

                       cref #= The variable to reinitialize. =#::DAE.ComponentRef
                       reinitExp #= The new value of the variable. =#::DAE.Exp
                       info::SourceInfo
              end

              @Record NORETCALL_STMT begin

                       exp::DAE.Exp
                       info::SourceInfo
              end

              @Record WHILE_STMT begin

                       exp::DAE.Exp
                       statementLst::List{Statement}
                       info::SourceInfo
              end

              @Record RETURN_STMT begin

                       info::SourceInfo
              end

              @Record BREAK_STMT begin

                       info::SourceInfo
              end

              @Record FAILURE_STMT begin

                       body::List{Statement}
                       info::SourceInfo
              end
         end

         @Uniontype FunctionSlot begin
              @Record SLOT begin

                       name::String
                       arg::Option{DAE.Exp}
                       defaultValue::Option{DAE.Exp}
              end
         end

         @Uniontype EntryOrigin begin
              @Record LOCAL_ORIGIN begin

              end

              @Record BUILTIN_ORIGIN begin

              end

              @Record INHERITED_ORIGIN begin

                       baseClass #= The path of the baseclass the entry was inherited from. =#::Absyn.Path
                       info #= The info of the extends clause. =#::SourceInfo
                       origin #= The origins of the element in the baseclass. =#::List{EntryOrigin}
                       originEnv #= The environment the entry was inherited from. =#::Env
                       index #= Index used to identify the extends clause for optimization. =#::ModelicaInteger
              end

              @Record REDECLARED_ORIGIN begin

                       replacedEntry #= The replaced entry. =#::Entry
                       originEnv #= The environment the replacement came from. =#::Env
              end

              @Record IMPORTED_ORIGIN begin

                       imp::Absyn.Import
                       info::SourceInfo
                       originEnv #= The environment the entry was imported from. =#::Env
              end
         end

         @Uniontype Entry begin
              @Record ENTRY begin

                       name::String
                       element::SCode.Element
                       mod::Modifier
                       origins::List{EntryOrigin}
              end
         end

         @Uniontype ScopeType begin
              @Record BUILTIN_SCOPE begin

              end

              @Record TOP_SCOPE begin

              end

              @Record NORMAL_SCOPE begin

                       isEncapsulated::Bool
              end

              @Record IMPLICIT_SCOPE begin

                       iterIndex::ModelicaInteger
              end
         end

         @Uniontype Frame begin
              @Record FRAME begin

                       name::Option{String}
                       prefix::Option{Prefix}
                       scopeType::ScopeType
                       entries::AvlTree
              end
         end

        AvlKey = String 

        AvlValue = Entry 

          #= The binary tree data structure =#
         @Uniontype AvlTree begin
              @Record AVLTREENODE begin

                       value #= Value =#::Option{AvlTreeValue}
                       height #= height of tree, used for balancing =#::ModelicaInteger
                       left #= left subtree =#::Option{AvlTree}
                       right #= right subtree =#::Option{AvlTree}
              end
         end

          #= Each node in the binary tree can have a value associated with it. =#
         @Uniontype AvlTreeValue begin
              @Record AVLTREEVALUE begin

                       key #= Key =#::AvlKey
                       value #= Value =#::AvlValue
              end
         end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
  module ClassInf 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    @UniontypeDecl State 
    @UniontypeDecl Event 

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

        import SCode

        import Absyn

        import Config

        import Debug

        import Error

        import Flags

        import Print

        import SCodeDump

          #= - Machine states, the string contains the classname. =#
         @Uniontype State begin
              @Record UNKNOWN begin

                       path::Absyn.Path
              end

              @Record OPTIMIZATION begin

                       path::Absyn.Path
              end

              @Record MODEL begin

                       path::Absyn.Path
              end

              @Record RECORD begin

                       path::Absyn.Path
              end

              @Record BLOCK begin

                       path::Absyn.Path
              end

              @Record CONNECTOR begin

                       path::Absyn.Path
                       isExpandable::Bool
              end

              @Record TYPE begin

                       path::Absyn.Path
              end

              @Record PACKAGE begin

                       path::Absyn.Path
              end

              @Record FUNCTION begin

                       path::Absyn.Path
                       isImpure::Bool
              end

              @Record ENUMERATION begin

                       path::Absyn.Path
              end

              @Record HAS_RESTRICTIONS begin

                       path::Absyn.Path
                       hasEquations::Bool
                       hasAlgorithms::Bool
                       hasConstraints::Bool
              end

              @Record TYPE_INTEGER begin

                       path::Absyn.Path
              end

              @Record TYPE_REAL begin

                       path::Absyn.Path
              end

              @Record TYPE_STRING begin

                       path::Absyn.Path
              end

              @Record TYPE_BOOL begin

                       path::Absyn.Path
              end

               #=  BTH
               =#

              @Record TYPE_CLOCK begin

                       path::Absyn.Path
              end

              @Record TYPE_ENUM begin

                       path::Absyn.Path
              end

              @Record EXTERNAL_OBJ begin

                       path::Absyn.Path
              end

               #= /* MetaModelica extension */ =#

              @Record META_TUPLE begin

                       path::Absyn.Path
              end

              @Record META_LIST begin

                       path::Absyn.Path
              end

              @Record META_OPTION begin

                       path::Absyn.Path
              end

              @Record META_RECORD begin

                       path::Absyn.Path
              end

              @Record META_UNIONTYPE begin

                       path::Absyn.Path
                       typeVars::List{String}
              end

              @Record META_ARRAY begin

                       path::Absyn.Path
              end

              @Record META_POLYMORPHIC begin

                       path::Absyn.Path
              end

               #= /*---------------------*/ =#
         end

          #= - Events =#
         @Uniontype Event begin
              @Record FOUND_EQUATION begin

              end

              @Record FOUND_ALGORITHM begin

              end

              @Record FOUND_CONSTRAINT begin

              end

              @Record FOUND_EXT_DECL begin

              end

              @Record NEWDEF begin

              end

              @Record FOUND_COMPONENT begin

                       name #= name of the component =#::String
              end
         end

         #= - Printing

          Some functions for printing error and debug information about the
          state machine.

          The code is excluded from the report.
         =#
        function printStateStr(inState::State) ::String 
              local outString::String

              outString = begin
                  local p::Absyn.Path
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                @match inState begin
                  UNKNOWN(__)  => begin
                    "unknown"
                  end
                  
                  OPTIMIZATION(__)  => begin
                    "optimization"
                  end
                  
                  MODEL(__)  => begin
                    "model"
                  end
                  
                  RECORD(__)  => begin
                    "record"
                  end
                  
                  BLOCK(__)  => begin
                    "block"
                  end
                  
                  CONNECTOR(__)  => begin
                    "connector"
                  end
                  
                  TYPE(__)  => begin
                    "type"
                  end
                  
                  PACKAGE(__)  => begin
                    "package"
                  end
                  
                  FUNCTION(isImpure = true)  => begin
                    "impure function"
                  end
                  
                  FUNCTION(__)  => begin
                    "function"
                  end
                  
                  TYPE_INTEGER(__)  => begin
                    "Integer"
                  end
                  
                  TYPE_REAL(__)  => begin
                    "Real"
                  end
                  
                  TYPE_STRING(__)  => begin
                    "String"
                  end
                  
                  TYPE_BOOL(__)  => begin
                    "Boolean"
                  end
                  
                  TYPE_CLOCK(__)  => begin
                    "Clock"
                  end
                  
                  HAS_RESTRICTIONS(hasEquations = false, hasAlgorithms = false, hasConstraints = false)  => begin
                    "new def"
                  end
                  
                  HAS_RESTRICTIONS(hasEquations = b1, hasAlgorithms = b2)  => begin
                    "has" + (if b1
                          " equations"
                        else
                          ""
                        end) + (if b2
                          " algorithms"
                        else
                          ""
                        end) + (if b1
                          " constraints"
                        else
                          ""
                        end)
                  end
                  
                  EXTERNAL_OBJ(__)  => begin
                    "ExternalObject"
                  end
                  
                  META_TUPLE(__)  => begin
                    "tuple"
                  end
                  
                  META_LIST(__)  => begin
                    "list"
                  end
                  
                  META_OPTION(__)  => begin
                    "Option"
                  end
                  
                  META_RECORD(__)  => begin
                    "meta_record"
                  end
                  
                  META_POLYMORPHIC(__)  => begin
                    "polymorphic"
                  end
                  
                  META_ARRAY(__)  => begin
                    "meta_array"
                  end
                  
                  META_UNIONTYPE(__)  => begin
                    "uniontype"
                  end
                  
                  _  => begin
                      "#printStateStr failed#"
                  end
                end
              end
               #=  BTH
               =#
          outString
        end

        function printState(inState::State)  
              _ = begin
                  local p::Absyn.Path
                @match inState begin
                  UNKNOWN(path = p)  => begin
                      Print.printBuf("UNKNOWN ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  OPTIMIZATION(path = p)  => begin
                      Print.printBuf("OPTIMIZATION ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  MODEL(path = p)  => begin
                      Print.printBuf("MODEL ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  RECORD(path = p)  => begin
                      Print.printBuf("RECORD ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  BLOCK(path = p)  => begin
                      Print.printBuf("BLOCK ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  CONNECTOR(path = p)  => begin
                      Print.printBuf("CONNECTOR ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE(path = p)  => begin
                      Print.printBuf("TYPE ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  PACKAGE(path = p)  => begin
                      Print.printBuf("PACKAGE ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  FUNCTION(path = p, isImpure = true)  => begin
                      Print.printBuf("IMPURE FUNCTION ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  FUNCTION(path = p)  => begin
                      Print.printBuf("FUNCTION ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE_INTEGER(path = p)  => begin
                      Print.printBuf("TYPE_INTEGER ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE_REAL(path = p)  => begin
                      Print.printBuf("TYPE_REAL ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE_STRING(path = p)  => begin
                      Print.printBuf("TYPE_STRING ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE_BOOL(path = p)  => begin
                      Print.printBuf("TYPE_BOOL ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  TYPE_CLOCK(path = p)  => begin
                      Print.printBuf("TYPE_CLOCK ")
                      Print.printBuf(AbsynUtil.pathString(p))
                    ()
                  end
                  
                  HAS_RESTRICTIONS(path = p)  => begin
                      Print.printBuf("HAS_RESTRICTIONS ")
                      Print.printBuf(AbsynUtil.pathString(p))
                      Print.printBuf(printStateStr(inState))
                    ()
                  end
                end
              end
               #=  BTH
               =#
        end

         #= Returns the classname of the state. =#
        function getStateName(inState::State) ::Absyn.Path 
              local outPath::Absyn.Path

              outPath = begin
                  local p::Absyn.Path
                @match inState begin
                  UNKNOWN(path = p)  => begin
                    p
                  end
                  
                  OPTIMIZATION(path = p)  => begin
                    p
                  end
                  
                  MODEL(path = p)  => begin
                    p
                  end
                  
                  RECORD(path = p)  => begin
                    p
                  end
                  
                  BLOCK(path = p)  => begin
                    p
                  end
                  
                  CONNECTOR(path = p)  => begin
                    p
                  end
                  
                  TYPE(path = p)  => begin
                    p
                  end
                  
                  PACKAGE(path = p)  => begin
                    p
                  end
                  
                  FUNCTION(path = p)  => begin
                    p
                  end
                  
                  ENUMERATION(path = p)  => begin
                    p
                  end
                  
                  HAS_RESTRICTIONS(path = p)  => begin
                    p
                  end
                  
                  TYPE_INTEGER(path = p)  => begin
                    p
                  end
                  
                  TYPE_REAL(path = p)  => begin
                    p
                  end
                  
                  TYPE_STRING(path = p)  => begin
                    p
                  end
                  
                  TYPE_BOOL(path = p)  => begin
                    p
                  end
                  
                  TYPE_CLOCK(path = p)  => begin
                    p
                  end
                  
                  TYPE_ENUM(path = p)  => begin
                    p
                  end
                  
                  EXTERNAL_OBJ(p)  => begin
                    p
                  end
                  
                  META_TUPLE(p)  => begin
                    p
                  end
                  
                  META_LIST(p)  => begin
                    p
                  end
                  
                  META_OPTION(p)  => begin
                    p
                  end
                  
                  META_RECORD(p)  => begin
                    p
                  end
                  
                  META_UNIONTYPE(p)  => begin
                    p
                  end
                  
                  META_ARRAY(p)  => begin
                    p
                  end
                  
                  META_POLYMORPHIC(p)  => begin
                    p
                  end
                  
                  _  => begin
                      Absyn.IDENT("#getStateName failed#")
                  end
                end
              end
               #=  BTH
               =#
          outPath
        end

        function printEventStr(inEvent::Event) ::String 
              local str::String

              str = begin
                  local name::String
                @match inEvent begin
                  FOUND_EQUATION(__)  => begin
                    "equation"
                  end
                  
                  FOUND_CONSTRAINT(__)  => begin
                    "constraint"
                  end
                  
                  NEWDEF(__)  => begin
                    "new definition"
                  end
                  
                  FOUND_COMPONENT(name)  => begin
                    "component " + name
                  end
                  
                  FOUND_EXT_DECL(__)  => begin
                    "external function declaration"
                  end
                  
                  _  => begin
                      "Unknown event"
                  end
                end
              end
          str
        end

         #= 
          This is the state machine initialization function. =#
        function start(inRestriction::SCode.Restriction, inPath::Absyn.Path) ::State 
              local outState::State

              outState = start_dispatch(inRestriction, AbsynUtil.makeFullyQualified(inPath))
          outState
        end

         #=  Transitions
         =#

         #= 
          This is the state machine initialization function. =#
        function start_dispatch(inRestriction::SCode.Restriction, inPath::Absyn.Path) ::State 
              local outState::State

              outState = begin
                  local p::Absyn.Path
                  local isExpandable::Bool
                  local isImpure::Bool
                @match (inRestriction, inPath) begin
                  (SCode.R_CLASS(__), p)  => begin
                    UNKNOWN(p)
                  end
                  
                  (SCode.R_OPTIMIZATION(__), p)  => begin
                    OPTIMIZATION(p)
                  end
                  
                  (SCode.R_MODEL(__), p)  => begin
                    MODEL(p)
                  end
                  
                  (SCode.R_RECORD(_), p)  => begin
                    RECORD(p)
                  end
                  
                  (SCode.R_BLOCK(__), p)  => begin
                    BLOCK(p)
                  end
                  
                  (SCode.R_CONNECTOR(isExpandable), p)  => begin
                    CONNECTOR(p, isExpandable)
                  end
                  
                  (SCode.R_TYPE(__), p)  => begin
                    TYPE(p)
                  end
                  
                  (SCode.R_PACKAGE(__), p)  => begin
                    PACKAGE(p)
                  end
                  
                  (SCode.R_FUNCTION(SCode.FR_NORMAL_FUNCTION(isImpure)), p)  => begin
                    FUNCTION(p, isImpure)
                  end
                  
                  (SCode.R_FUNCTION(SCode.FR_EXTERNAL_FUNCTION(isImpure)), p)  => begin
                    FUNCTION(p, isImpure)
                  end
                  
                  (SCode.R_FUNCTION(_), p)  => begin
                    FUNCTION(p, false)
                  end
                  
                  (SCode.R_OPERATOR(__), p)  => begin
                    FUNCTION(p, false)
                  end
                  
                  (SCode.R_ENUMERATION(__), p)  => begin
                    ENUMERATION(p)
                  end
                  
                  (SCode.R_PREDEFINED_INTEGER(__), p)  => begin
                    TYPE_INTEGER(p)
                  end
                  
                  (SCode.R_PREDEFINED_REAL(__), p)  => begin
                    TYPE_REAL(p)
                  end
                  
                  (SCode.R_PREDEFINED_STRING(__), p)  => begin
                    TYPE_STRING(p)
                  end
                  
                  (SCode.R_PREDEFINED_BOOLEAN(__), p)  => begin
                    TYPE_BOOL(p)
                  end
                  
                  (SCode.R_PREDEFINED_CLOCK(__), p)  => begin
                      @match true = Config.synchronousFeaturesAllowed()
                    TYPE_CLOCK(p)
                  end
                  
                  (SCode.R_PREDEFINED_ENUMERATION(__), p)  => begin
                    TYPE_ENUM(p)
                  end
                  
                  (SCode.R_UNIONTYPE(__), p)  => begin
                    META_UNIONTYPE(p, inRestriction.typeVars)
                  end
                  
                  (SCode.R_METARECORD(__), p)  => begin
                    META_RECORD(p)
                  end
                end
              end
               #=  BTH
               =#
               #= /* Meta Modelica extensions */ =#
          outState
        end

         #= 
          This is the state machine transition function.  It describes the
          transitions between states at different events.
         =#
        function trans(inState::State, inEvent::Event) ::State 
              local outState::State

              outState = begin
                  local p::Absyn.Path
                  local st::State
                  local ev::Event
                  local isExpandable::Bool
                  local b::Bool
                  local b1::Bool
                  local b2::Bool
                  local b3::Bool
                  local isImpure::Bool
                  local s::String
                  local msg::List{String}
                @match (inState, inEvent) begin
                  (UNKNOWN(path = p), NEWDEF(__))  => begin
                    HAS_RESTRICTIONS(p, false, false, false)
                  end
                  
                  (OPTIMIZATION(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (MODEL(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (RECORD(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (BLOCK(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (CONNECTOR(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE(path = p), NEWDEF(__))  => begin
                    TYPE(p)
                  end
                  
                  (PACKAGE(path = p), NEWDEF(__))  => begin
                    PACKAGE(p)
                  end
                  
                  (FUNCTION(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (ENUMERATION(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_INTEGER(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_REAL(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_STRING(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_BOOL(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_CLOCK(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (TYPE_ENUM(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (META_UNIONTYPE(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (META_RECORD(__), NEWDEF(__))  => begin
                    inState
                  end
                  
                  (UNKNOWN(path = p), FOUND_COMPONENT(__))  => begin
                    HAS_RESTRICTIONS(p, false, false, false)
                  end
                  
                  (OPTIMIZATION(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (MODEL(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (RECORD(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (BLOCK(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (CONNECTOR(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE(path = p), FOUND_COMPONENT(name = s))  => begin
                      if ! isBasicTypeComponentName(s)
                        Error.addMessage(Error.TYPE_NOT_FROM_PREDEFINED, list(AbsynUtil.pathString(p)))
                        fail()
                      end
                    TYPE(p)
                  end
                  
                  (PACKAGE(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (FUNCTION(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (ENUMERATION(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (HAS_RESTRICTIONS(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_INTEGER(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_REAL(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_STRING(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_BOOL(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_CLOCK(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (TYPE_ENUM(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (META_RECORD(__), FOUND_COMPONENT(__))  => begin
                    inState
                  end
                  
                  (UNKNOWN(path = p), FOUND_EQUATION(__))  => begin
                    HAS_RESTRICTIONS(p, true, false, false)
                  end
                  
                  (OPTIMIZATION(__), FOUND_EQUATION(__))  => begin
                    inState
                  end
                  
                  (OPTIMIZATION(__), FOUND_CONSTRAINT(__))  => begin
                    inState
                  end
                  
                  (OPTIMIZATION(__), FOUND_ALGORITHM(__))  => begin
                    inState
                  end
                  
                  (MODEL(__), FOUND_EQUATION(__))  => begin
                    inState
                  end
                  
                  (BLOCK(__), FOUND_EQUATION(__))  => begin
                    inState
                  end
                  
                  (MODEL(__), FOUND_ALGORITHM(__))  => begin
                    inState
                  end
                  
                  (BLOCK(__), FOUND_ALGORITHM(__))  => begin
                    inState
                  end
                  
                  (FUNCTION(__), FOUND_ALGORITHM(__))  => begin
                    inState
                  end
                  
                  (HAS_RESTRICTIONS(path = p, hasAlgorithms = b2, hasConstraints = b3), FOUND_EQUATION(__))  => begin
                    HAS_RESTRICTIONS(p, true, b2, b3)
                  end
                  
                  (HAS_RESTRICTIONS(path = p, hasEquations = b1, hasAlgorithms = b2), FOUND_CONSTRAINT(__))  => begin
                    HAS_RESTRICTIONS(p, b1, b2, true)
                  end
                  
                  (HAS_RESTRICTIONS(path = p, hasEquations = b1, hasConstraints = b3), FOUND_ALGORITHM(__))  => begin
                    HAS_RESTRICTIONS(p, b1, true, b3)
                  end
                  
                  (FUNCTION(__), FOUND_EXT_DECL(__))  => begin
                    inState
                  end
                  
                  (_, FOUND_EXT_DECL(__))  => begin
                    fail()
                  end
                  
                  (_, FOUND_EQUATION(__))  => begin
                    fail()
                  end
                  
                  (_, FOUND_CONSTRAINT(__))  => begin
                    fail()
                  end
                  
                  (st, ev)  => begin
                      @match true = Flags.isSet(Flags.FAILTRACE)
                      Debug.traceln("- ClassInf.trans failed: " + printStateStr(st) + ", " + printEventStr(ev))
                    fail()
                  end
                end
              end
               #= /* adrpo 2009-05-15: type Orientation can contain equalityConstraint function! */ =#
               #= case (TYPE(path = p),FOUND_COMPONENT()) then TYPE(p);
               =#
               #=  Added 2009-08-19. sjoelund
               =#
               #= /* Event `FOUND_EQUATION\\' */ =#
          outState
        end

         #= 
          This is the validity function which determines if a state is valid
          according to one of the restrictions.  This means, that if a class
          definition is to be used as, say, a connector, the state of the
          state machine is checked against the `SCode.R_CONNECTOR\\'
          restriction using this function to find out if it is an error to
          use this class definition as a connector.
         =#
        function valid(inState::State, inRestriction::SCode.Restriction)  
              _ = begin
                  local p::Absyn.Path
                @match (inState, inRestriction) begin
                  (UNKNOWN(__), _)  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(__), SCode.R_CLASS(__))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(__), SCode.R_MODEL(__))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(__), SCode.R_OPTIMIZATION(__))  => begin
                    ()
                  end
                  
                  (MODEL(__), SCode.R_MODEL(__))  => begin
                    ()
                  end
                  
                  (RECORD(__), SCode.R_RECORD(_))  => begin
                    ()
                  end
                  
                  (RECORD(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(hasEquations = false, hasConstraints = false, hasAlgorithms = false), SCode.R_RECORD(_))  => begin
                    ()
                  end
                  
                  (BLOCK(__), SCode.R_BLOCK(__))  => begin
                    ()
                  end
                  
                  (MODEL(__), SCode.R_MODEL(__))  => begin
                    ()
                  end
                  
                  (CONNECTOR(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (CONNECTOR(isExpandable = false), SCode.R_CONNECTOR(false))  => begin
                    ()
                  end
                  
                  (CONNECTOR(isExpandable = true), SCode.R_CONNECTOR(true))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(hasEquations = false, hasConstraints = false, hasAlgorithms = false), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_INTEGER(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_REAL(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_STRING(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_BOOL(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_CLOCK(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE_ENUM(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (ENUMERATION(__), SCode.R_CONNECTOR(_))  => begin
                    ()
                  end
                  
                  (TYPE(__), SCode.R_CONNECTOR(__))  => begin
                    ()
                  end
                  
                  (TYPE(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_INTEGER(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_REAL(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_STRING(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_BOOL(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_CLOCK(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (TYPE_ENUM(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (ENUMERATION(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (PACKAGE(__), SCode.R_PACKAGE(__))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(hasEquations = false, hasConstraints = false, hasAlgorithms = false), SCode.R_PACKAGE(__))  => begin
                    ()
                  end
                  
                  (FUNCTION(__), SCode.R_FUNCTION(_))  => begin
                    ()
                  end
                  
                  (HAS_RESTRICTIONS(hasEquations = false, hasConstraints = false), SCode.R_FUNCTION(_))  => begin
                    ()
                  end
                  
                  (META_TUPLE(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (META_LIST(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (META_OPTION(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (META_RECORD(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (META_ARRAY(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                  
                  (META_UNIONTYPE(__), SCode.R_TYPE(__))  => begin
                    ()
                  end
                end
              end
               #=  BTH
               =#
               #=  used in Modelica.Electrical.Digital where we have an enum as a connector
               =#
               #=  used in Modelica.Electrical.Digital where we have an enum as a connector
               =#
               #=  Note: Only allowed in some cases (outputs, etc). Happens when the base class is type T extends Real; end T;
               =#
               #=  BTH
               =#
        end

         #= This function has the same semantical meaning as the function
          `valid\\'.  However, it prints an error message when it fails. =#
        function assertValid(inState::State, inRestriction::SCode.Restriction, info::SourceInfo)  
              _ = begin
                  local st::State
                  local re::SCode.Restriction
                  local str1::String
                  local str2::String
                  local str3::String
                @matchcontinue (inState, inRestriction, info) begin
                  (st, re, _)  => begin
                      valid(st, re)
                    ()
                  end
                  
                  (st, re, _)  => begin
                      str1 = AbsynUtil.pathString(getStateName(st))
                      str2 = printStateStr(st)
                      str3 = SCodeDump.restrictionStringPP(re)
                      Error.addSourceMessage(Error.RESTRICTION_VIOLATION, list(str1, str2, str3), info)
                    fail()
                  end
                end
              end
        end

         #= This function has the same semantical meaning as the function
          `trans\\'.  However, it prints an error message when it fails. =#
        function assertTrans(inState::State, event::Event, info::SourceInfo) ::State 
              local outState::State

              outState = begin
                  local st::State
                  local str1::String
                  local str2::String
                  local str3::String
                @matchcontinue (inState, event, info) begin
                  (st, _, _)  => begin
                    trans(st, event)
                  end
                  
                  (st, _, _)  => begin
                      str1 = AbsynUtil.pathString(getStateName(st))
                      str2 = printStateStr(st)
                      str3 = printEventStr(event)
                      Error.addSourceMessage(Error.TRANS_VIOLATION, list(str1, str2, str3), info)
                    fail()
                  end
                end
              end
          outState
        end

         #= 
          Finds a State in the list that matches the state given as first argument.
          NOTE: Currently not used anywhere.
         =#
        function matchingState(inState::State, inStateLst::List{<:State}) ::Bool 
              local outBoolean::Bool

              outBoolean = begin
                  local rest::List{State}
                  local res::Bool
                @match (inState, inStateLst) begin
                  (_,  nil())  => begin
                    false
                  end
                  
                  (UNKNOWN(__), UNKNOWN(__) <| _)  => begin
                    true
                  end
                  
                  (MODEL(__), MODEL(__) <| _)  => begin
                    true
                  end
                  
                  (RECORD(__), RECORD(__) <| _)  => begin
                    true
                  end
                  
                  (BLOCK(__), BLOCK(__) <| _)  => begin
                    true
                  end
                  
                  (CONNECTOR(__), CONNECTOR(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE(__), TYPE(__) <| _)  => begin
                    true
                  end
                  
                  (PACKAGE(__), PACKAGE(__) <| _)  => begin
                    true
                  end
                  
                  (FUNCTION(__), FUNCTION(__) <| _)  => begin
                    true
                  end
                  
                  (ENUMERATION(__), ENUMERATION(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_INTEGER(__), TYPE_INTEGER(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_REAL(__), TYPE_REAL(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_STRING(__), TYPE_STRING(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_BOOL(__), TYPE_BOOL(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_CLOCK(__), TYPE_CLOCK(__) <| _)  => begin
                    true
                  end
                  
                  (TYPE_ENUM(__), TYPE_ENUM(__) <| _)  => begin
                    true
                  end
                  
                  (_, _ <| rest)  => begin
                      res = matchingState(inState, rest)
                    res
                  end
                end
              end
               #=  BTH
               =#
          outBoolean
        end

         #= returns true if state is FUNCTION. =#
        function isFunction(inState::State) ::Bool 
              local b::Bool

              b = begin
                @match inState begin
                  FUNCTION(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= Fails for states that are not FUNCTION or RECORD. =#
        function isFunctionOrRecord(inState::State) ::Bool 
              local b::Bool

              b = begin
                @match inState begin
                  FUNCTION(__)  => begin
                    true
                  end
                  
                  RECORD(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          b
        end

         #= 
          Fails for states that are not CONNECTOR.
         =#
        function isConnector(inState::State)  
              _ = begin
                @match inState begin
                  CONNECTOR(__)  => begin
                    ()
                  end
                end
              end
        end

         const basicTypeMods = list("quantity", "unit", "displayUnit", "min", "max", "start", "fixed", "nominal", "stateSelect", "uncertain", "distribution")::List
         #=  extension for uncertainties
         =#
         #=  extension for uncertainties
         =#

         #= Returns true if the name can be a component of a builtin type =#
        function isBasicTypeComponentName(name::String) ::Bool 
              local res::Bool

              res = listMember(name, basicTypeMods)
          res
        end

        function isTypeOrRecord(inState::State) ::Bool 
              local outIsTypeOrRecord::Bool

              outIsTypeOrRecord = begin
                @match inState begin
                  TYPE(__)  => begin
                    true
                  end
                  
                  RECORD(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsTypeOrRecord
        end

        function isRecord(inState::State) ::Bool 
              local outIsRecord::Bool

              outIsRecord = begin
                @match inState begin
                  RECORD(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsRecord
        end

        function isMetaRecord(inState::State) ::Bool 
              local outIsRecord::Bool

              outIsRecord = begin
                @match inState begin
                  META_RECORD(__)  => begin
                    true
                  end
                  
                  _  => begin
                      false
                  end
                end
              end
          outIsRecord
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
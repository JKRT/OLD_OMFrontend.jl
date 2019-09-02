  module SCodeSimplify 


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

        import SCode

         #= transforms scode to scode simplified =#
        function simplifyProgram(inSCodeProgram::SCode.Program) ::SCode.Program 
              local outSCodeProgram::SCode.Program

              outSCodeProgram = begin
                  local c::SCode.Element
                  local el::SCode.Element
                  local rest::SCode.Program
                  local acc::SCode.Program
                   #=  handle empty
                   =#
                @match inSCodeProgram begin
                   nil()  => begin
                    nil
                  end
                  
                  el <| rest  => begin
                      c = simplifyClass(el)
                      acc = simplifyProgram(rest)
                    _cons(c, acc)
                  end
                end
              end
               #=  handle something
               =#
          outSCodeProgram
        end

         #= simplifies a class. =#
        function simplifyClass(inClass::SCode.Element) ::SCode.Element 
              local outClass::SCode.Element

              outClass = begin
                  local cDef::SCode.ClassDef
                  local ncDef::SCode.ClassDef
                  local info::SourceInfo
                  local n::SCode.Ident
                  local pref::SCode.Prefixes
                  local ecpf::SCode.Encapsulated
                  local ppf::SCode.Partial
                  local res::SCode.Restriction
                  local cmt::SCode.Comment
                @match inClass begin
                  SCode.CLASS(n, pref, ecpf, ppf, res, cDef, cmt, info)  => begin
                      ncDef = simplifyClassDef(cDef)
                    SCode.CLASS(n, pref, ecpf, ppf, res, ncDef, cmt, info)
                  end
                end
              end
          outClass
        end

         #= simplifies a classdef. =#
        function simplifyClassDef(inClassDef::SCode.ClassDef) ::SCode.ClassDef 
              local outClassDef::SCode.ClassDef

              outClassDef = begin
                  local baseClassName::SCode.Ident
                  local els::List{SCode.Element}
                  local ne::List{SCode.Equation} #= the list of equations =#
                  local ie::List{SCode.Equation} #= the list of initial equations =#
                  local na::List{SCode.AlgorithmSection} #= the list of algorithms =#
                  local ia::List{SCode.AlgorithmSection} #= the list of initial algorithms =#
                  local nc::List{SCode.ConstraintSection} #= the list of constraints for optimization =#
                  local clats::List{Absyn.NamedArg} #= class attributes. currently for optimica extensions =#
                  local ed::Option{SCode.ExternalDecl} #= used by external functions =#
                  local al::List{SCode.Annotation} #= the list of annotations found in between class elements, equations and algorithms =#
                  local c::Option{SCode.Comment} #= the class comment =#
                  local cDef::SCode.ClassDef
                  local mod::SCode.Mod
                  local attr::SCode.Attributes
                  local cmt::Option{SCode.Comment}
                  local typeSpec::Absyn.TypeSpec
                   #=  handle parts
                   =#
                @match inClassDef begin
                  SCode.PARTS(els, ne, ie, na, ia, nc, clats, ed)  => begin
                      els = simplifyElements(els)
                    SCode.PARTS(els, ne, ie, na, ia, nc, clats, ed)
                  end
                  
                  SCode.CLASS_EXTENDS(baseClassName, mod, cDef)  => begin
                      cDef = simplifyClassDef(cDef)
                    SCode.CLASS_EXTENDS(baseClassName, mod, cDef)
                  end
                  
                  SCode.DERIVED(_, _, _)  => begin
                    inClassDef
                  end
                  
                  SCode.ENUMERATION(__)  => begin
                    inClassDef
                  end
                  
                  SCode.OVERLOAD(__)  => begin
                    inClassDef
                  end
                  
                  SCode.PDER(__)  => begin
                    inClassDef
                  end
                end
              end
               #=  handle class extends
               =#
               #=  handle derived!
               =#
               #=  handle enumeration, just return the same
               =#
               #=  handle overload
               =#
               #=  handle pder
               =#
          outClassDef
        end

         #= simplify elements =#
        function simplifyElements(inElements::List{<:SCode.Element}) ::List{SCode.Element} 
              local outElements::List{SCode.Element}

              outElements = begin
                  local el::SCode.Element
                  local el2::SCode.Element
                  local rest::List{SCode.Element}
                  local els::List{SCode.Element}
                  local bcp::Absyn.Path
                   #=  handle classes without elements!
                   =#
                @matchcontinue inElements begin
                   nil()  => begin
                    nil
                  end
                  
                  SCode.EXTENDS(baseClassPath = bcp) <| rest  => begin
                      @match true = AbsynUtil.pathContains(bcp, Absyn.IDENT("Icons"))
                      els = simplifyElements(rest)
                    els
                  end
                  
                  el && SCode.CLASS(__) <| rest  => begin
                      el2 = simplifyClass(el)
                      els = simplifyElements(rest)
                    _cons(el2, els)
                  end
                  
                  el <| rest  => begin
                      els = simplifyElements(rest)
                    _cons(el, els)
                  end
                end
              end
               #=  handle extends Modelica.Icons.*
               =#
               #=  remove Modelica.Icons -> not working yet because of Modelica.Mechanics.MultiBody.Types uses it !/
               =#
               #= case (SCode.CLASS(name = \"Icons\", restriction = SCode.R_PACKAGE())::rest)
               =#
               #=   equation
               =#
               #=     els = simplifyElements(rest);
               =#
               #=   then
               =#
               #=     els;
               =#
               #=  handle classes
               =#
               #=  handle rest
               =#
          outElements
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
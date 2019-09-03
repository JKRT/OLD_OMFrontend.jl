# OMCompiler.jl
A translation of the OpenModelica Compiler frontend into Julia. Stay tuned people

WIP!

This package is currently work in progress and may or may not be functioning until there is an official release.

# Requirements 

* Julia 1.1.1 

* All external dependencies for the OpenModelica Compiler (OMC) 

# Dependencies 

As of this writing we currently depend on the following packages

* MetaModelica.jl

* Absyn.jl

* SCode.jl

* DoubleEnded.jl

* ImmutableList.jl

* The standard library. That is available here: https://github.com/JKRT/Modelica-Standard-Library-AST
(Currently, just a constant which represents the Modelica Compilers internal representation (Absyn.jl) of the Standard Library)

* Parser currently defined in OMCompiler

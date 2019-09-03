# OMCompiler.jl
A translation of the OpenModelica Compiler frontend into Julia. Stay tuned people

WIP!

# Requirements 

* Julia 1.1.1 

* All external depdencies for the omc (If you would like to use a parser)

# Dependencies 

* MetaModelica.jl

* Absyn.jl

* SCode.jl

* DoubleEnded.jl

* The standard library. That is available here: https://github.com/JKRT/Modelica-Standard-Library-AST
(Currently just a constant which represents the Modelica Compilers internal representation (Absyn.jl) of the Standard Library)

* Parser currently defined in OMCompiler

#= Note run from this folder=#
JIT_STACK_START_SIZE = 32768
JIT_STACK_MAX_SIZE = 1048576
Base.PCRE.JIT_STACK[] = ccall((:pcre2_jit_stack_create_8, Base.PCRE.PCRE_LIB), Ptr{Cvoid},
                              (Cint, Cint, Ptr{Cvoid}),
                              JIT_STACK_START_SIZE, JIT_STACK_MAX_SIZE, C_NULL)
ccall((:pcre2_jit_stack_assign_8, Base.PCRE.PCRE_LIB), Cvoid,
      (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}), Base.PCRE.MATCH_CONTEXT[], C_NULL, Base.PCRE.JIT_STACK[])

#=TODO make it call the parserscript from OpenModelica home=#
push!(LOAD_PATH, "../Util/")
push!(LOAD_PATH, "../Frontend/")
println(LOAD_PATH)
# include("./Absyn.jl")
# include("./AbsynUtil.jl")
# include("./List.jl")
#include("./SCode.jl")
include("../Util/AbsynToSCode.jl")
#include("./SCodeUtil.jl")
using Absyn
using MetaModelica

t  = PARTS(list(), list(), list(PUBLIC(list(ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("x", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("start"), SOME(CLASSMOD(list(), EQMOD(INTEGER(1::ModelicaInteger), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 16, 2, 19)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 10, 2, 19))), NOMOD()))), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 3, 2, 20), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), PARAM(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("a", list(), SOME(CLASSMOD(list(), EQMOD(INTEGER(1::ModelicaInteger), SOURCEINFO("/home/johti1b/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 3, 20, 3, 23))))), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 3, 3, 3, 23), NONE())))), EQUATIONS(list(EQUATIONITEM(EQ_EQUALS(CALL(CREF_IDENT("der", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("x", list()))), list())), UNARY(UMINUS(), BINARY(CREF(CREF_IDENT("a", list())), MUL(), CREF(CREF_IDENT("x", list()))))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 5, 3, 5, 19))))), list(), NONE())

HelloWorld = PROGRAM(list(CLASS("HelloWorld", false, false ,false, R_CLASS(), PARTS(list(), list(), list(PUBLIC(list(ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("x", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("start"), SOME(CLASSMOD(list(), EQMOD(INTEGER(1::ModelicaInteger), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 16, 2, 19)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 10, 2, 19))), NOMOD()))), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 2, 3, 2, 20), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), PARAM(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("a", list(), SOME(CLASSMOD(list(), EQMOD(INTEGER(1::ModelicaInteger), SOURCEINFO("/home/johti1b/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 3, 20, 3, 23))))), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 3, 3, 3, 23), NONE())))), EQUATIONS(list(EQUATIONITEM(EQ_EQUALS(CALL(CREF_IDENT("der", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("x", list()))), list())), UNARY(UMINUS(), BINARY(CREF(CREF_IDENT("a", list())), MUL(), CREF(CREF_IDENT("x", list()))))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 5, 3, 5, 19))))), list(), NONE()), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/HelloWorld.mo", false, 1, 1, 6, 15))), TOP())

AbsynToSCode.translateAbsyn2SCode(HelloWorld)

#= Try the bouncing ball =#
BouncingBall = PROGRAM(list(CLASS("BouncingBall", false, false ,false, R_MODEL(), PARTS(list(), list(), list(PUBLIC(list(ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), PARAM(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("e", list(), SOME(CLASSMOD(list(), EQMOD(REAL("0.7"), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 2, 19, 2, 24))))), NONE(), SOME(COMMENT(SOME("coefficient of restitution"), NONE()))))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 2, 3, 2, 52), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), PARAM(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("g", list(), SOME(CLASSMOD(list(), EQMOD(REAL("9.81"), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 3, 19, 3, 25))))), NONE(), SOME(COMMENT(SOME("gravity acceleration"), NONE()))))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 3, 3, 3, 47), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("h", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("fixed"), SOME(CLASSMOD(list(), EQMOD(BOOL(true), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 4, 15, 4, 20)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 4, 10, 4, 20)), MODIFICATION(false, NON_EACH(), IDENT("start"), SOME(CLASSMOD(list(), EQMOD(INTEGER(1::ModelicaInteger), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 4, 27, 4, 29)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 4, 22, 4, 29))), NOMOD()))), NONE(), SOME(COMMENT(SOME("height of ball"), NONE()))))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 4, 3, 4, 47), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("v", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("fixed"), SOME(CLASSMOD(list(), EQMOD(BOOL(true), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 5, 15, 5, 20)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 5, 10, 5, 20))), NOMOD()))), NONE(), SOME(COMMENT(SOME("velocity of ball"), NONE()))))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 5, 3, 5, 40), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Boolean"), NONE()), list(COMPONENTITEM(COMPONENT("flying", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("fixed"), SOME(CLASSMOD(list(), EQMOD(BOOL(true), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 6, 23, 6, 28)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 6, 18, 6, 28)), MODIFICATION(false, NON_EACH(), IDENT("start"), SOME(CLASSMOD(list(), EQMOD(BOOL(true), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 6, 35, 6, 40)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 6, 30, 6, 40))), NOMOD()))), NONE(), SOME(COMMENT(SOME("true, if ball is flying"), NONE()))))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 6, 3, 6, 67), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Boolean"), NONE()), list(COMPONENTITEM(COMPONENT("impact", list(), NONE()), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 7, 3, 7, 17), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Real"), NONE()), list(COMPONENTITEM(COMPONENT("v_new", list(), SOME(CLASSMOD(list(MODIFICATION(false, NON_EACH(), IDENT("fixed"), SOME(CLASSMOD(list(), EQMOD(BOOL(true), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 8, 19, 8, 24)))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 8, 14, 8, 24))), NOMOD()))), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 8, 3, 8, 25), NONE())), ELEMENTITEM(ELEMENT(false, NONE(), NOT_INNER_OUTER(), COMPONENTS(ATTR(false, false, NON_PARALLEL(), VAR(), BIDIR(), NONFIELD(), list()), TPATH(IDENT("Integer"), NONE()), list(COMPONENTITEM(COMPONENT("foo", list(), NONE()), NONE(), NONE()))), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 9, 3, 9, 14), NONE())))), EQUATIONS(list(EQUATIONITEM(EQ_EQUALS(CREF(CREF_IDENT("impact", list())), RELATION(CREF(CREF_IDENT("h", list())), LESSEQ(), REAL("0.0"))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 12, 3, 12, 20)), EQUATIONITEM(EQ_EQUALS(CREF(CREF_IDENT("foo", list())), IFEXP(CREF(CREF_IDENT("impact", list())), INTEGER(1::ModelicaInteger), INTEGER(2::ModelicaInteger), list())), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 13, 3, 13, 32)), EQUATIONITEM(EQ_EQUALS(CALL(CREF_IDENT("der", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("v", list()))), list())), IFEXP(CREF(CREF_IDENT("flying", list())), UNARY(UMINUS(), CREF(CREF_IDENT("g", list()))), INTEGER(0::ModelicaInteger), list())), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 14, 3, 14, 36)), EQUATIONITEM(EQ_EQUALS(CALL(CREF_IDENT("der", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("h", list()))), list())), CREF(CREF_IDENT("v", list()))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 15, 3, 15, 13)), EQUATIONITEM(EQ_WHEN_E(ARRAY(list(LBINARY(RELATION(CREF(CREF_IDENT("h", list())), LESSEQ(), REAL("0.0")), AND(), RELATION(CREF(CREF_IDENT("v", list())), LESSEQ(), REAL("0.0"))), CREF(CREF_IDENT("impact", list())))), list(EQUATIONITEM(EQ_EQUALS(CREF(CREF_IDENT("v_new", list())), IFEXP(CALL(CREF_IDENT("edge", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("impact", list()))), list())), UNARY(UMINUS(), BINARY(CREF(CREF_IDENT("e", list())), MUL(), CALL(CREF_IDENT("pre", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("v", list()))), list())))), INTEGER(0::ModelicaInteger), list())), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 18, 5, 18, 50)), EQUATIONITEM(EQ_EQUALS(CREF(CREF_IDENT("flying", list())), RELATION(CREF(CREF_IDENT("v_new", list())), GREATER(), INTEGER(0::ModelicaInteger))), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 19, 5, 19, 23)), EQUATIONITEM(EQ_NORETCALL(CREF_IDENT("reinit", list()), FUNCTIONARGS(list(CREF(CREF_IDENT("v", list())), CREF(CREF_IDENT("v_new", list()))), list())), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 20, 5, 20, 21))),list()), NONE(), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 17, 3, 21, 11))))), list(), NONE()), SOURCEINFO("/home/johti17/OpenModelica/OMCompiler/Examples/BouncingBall.mo", false, 1, 1, 23, 17))), TOP())
@time a = AbsynToSCode.translateAbsyn2SCode(BouncingBall)
@time AbsynToSCode.translateAbsyn2SCode(BouncingBall)
using Modelica_Standard_Library_AST
 using BenchmarkTools
using Profile
 P = Modelica_Standard_Library_AST.Program
using BenchmarkTools
@time AbsynToSCode.translateAbsyn2SCode(P)
@time AbsynToSCode.translateAbsyn2SCode(P)
println("Goodbye")
#println("Goodbye")
#include("./Util.jl")
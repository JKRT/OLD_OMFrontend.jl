  module Autoconf 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

         const haveBStatic = true::Bool
         const bstatic = if haveBStatic
               "-Wl,-Bstatic"
             else
               ""
             end::String
         const bdynamic = if haveBStatic
               "-Wl,-Bdynamic"
             else
               ""
             end::String
         const configureCommandLine = "Configured 2019-08-18 17:33:36 using arguments:  '--disable-option-checking' '--prefix=/home/johti17/OpenModelica/build' 'CC=clang' 'CXX=clang++-9' '-with-cppruntime' '--without-omc' '--without-omlibrary' '--without-hwloc' '--with-ombuilddir=/home/johti17/OpenModelica/build' '--cache-file=/dev/null' '--srcdir=.'"::String
         const os = "linux"::String
         const make = "make"::String
         const exeExt = ""::String
         const dllExt = ".so"::String
         const ldflags_runtime = " -Wl,--no-as-needed -Wl,--disable-new-dtags -lOpenModelicaRuntimeC  -llapack -lblas   -lm -lomcgc -lpthread -rdynamic"::String
         const ldflags_runtime_sim = " -Wl,--no-as-needed -Wl,--disable-new-dtags -lSimulationRuntimeC  -llapack -lblas   -lm -lomcgc -lpthread -rdynamic -Wl,--no-undefined"::String
         const ldflags_runtime_fmu = " -Wl,--no-as-needed -Wl,--disable-new-dtags  -llapack -lblas   -lm -lpthread -rdynamic -Wl,--no-undefined"::String
         const platform = "Unix"::String
         const pathDelimiter = "/"::String
         const groupDelimiter = ":"::String
         const corbaLibs = ""::String
         const hwloc = if 0 == 1
               "-lhwloc"
             else
               ""
             end::String
         const systemLibs = list("-lomcruntime", "-lexpat", "-lsqlite3", "-llpsolve55", corbaLibs, "-lomcgc", hwloc)::List
         const triple = "x86_64-linux-gnu"::String

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
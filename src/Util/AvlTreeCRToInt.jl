  module AvlTreeCRToInt 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import BaseAvlTree
        import DAE

        import ComponentReference

        extends BaseAvlTree
        Key = DAE.ComponentRef 
        Value = ModelicaInteger 







    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
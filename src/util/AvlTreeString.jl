  module AvlTreeString 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import BaseAvlTree
        extends BaseAvlTree
        Key = String 
        Value = ModelicaInteger 







    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
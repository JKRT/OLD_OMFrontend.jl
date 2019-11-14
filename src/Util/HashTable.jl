
module HashTable


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    FuncHashCref = Function
    FuncCrefEqual = Function
    FuncCrefStr = Function
    FuncExpStr = Function

#= /* HashTable instance specific code */ =#

        import BaseHashTable

        import DAE

        import CrefForHashTable

        const Key = DAE.ComponentRef

        const Value = ModelicaInteger

        const HashTableCrefFunctionsType = Tuple

        const HashTableType = Tuple

         #=
          Returns an empty HashTable.
          Using the default bucketsize..
         =#
        function emptyHashTable() ::HashTableType
              local hashTable::HashTableType

              hashTable = emptyHashTableSized(BaseHashTable.defaultBucketSize)
          hashTable
        end

         #= Returns an empty HashTable.
         Using the bucketsize size =#
        function emptyHashTableSized(size::ModelicaInteger) ::HashTableType
              local hashTable::HashTableType

              hashTable = BaseHashTable.emptyHashTableWork(size, (CrefForHashTable.hashComponentRefMod, CrefForHashTable.crefEqual, CrefForHashTable.printComponentRefStr, intString))
          hashTable
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end

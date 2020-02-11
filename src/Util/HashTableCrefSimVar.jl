  module HashTableCrefSimVar 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll
    #= Necessary to write declarations for your uniontypes until Julia adds support for mutually recursive types =#

    FuncHashCref = Function
    FuncCrefEqual = Function
    FuncCrefStr = Function
    FuncExpStr = Function

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
         #= /* Below is the instance specific code. For each hashtable the user must define:

        Key       - The key used to uniquely define elements in a hashtable
        Value     - The data to associate with each key
        hashFunc   - A function that maps a key to a positive integer.
        keyEqual   - A comparison function between two keys, returns true if equal.
        */ =#
         #= /* HashTable instance specific code */ =#
        import BaseHashTable
        import DAE
        import SimCodeVar
        import Error.addInternalError
        Key = DAE.ComponentRef 
        Value = SimCodeVar.SimVar 

        import ComponentReference

        HashTableCrefFunctionsType = Tuple 
        HashTable = Tuple 









         #= 
          Returns an empty HashTable.
          Using the default bucketsize..
         =#
        function emptyHashTable() ::HashTable 
              local hashTable::HashTable

              hashTable = emptyHashTableSized(BaseHashTable.defaultBucketSize)
          hashTable
        end

         #= Returns an empty HashTable.
         Using the bucketsize size. =#
        function emptyHashTableSized(size::ModelicaInteger) ::HashTable 
              local hashTable::HashTable

              hashTable = BaseHashTable.emptyHashTableWork(size, (ComponentReference.hashComponentRefMod, ComponentReference.crefEqual, ComponentReference.printComponentRefStr, opaqueStr))
          hashTable
        end

        function opaqueStr(var::SimCodeVar.SimVar) ::String 
              local str::String

              str = "#SimVar(index=" + StringFunction(var.index) + ",name=" + ComponentReference.printComponentRefStr(var.name) + ")#"
          str
        end

         #= adds SimVar to hash table inHT and returns extended hash table =#
        function addSimVarToHashTable(simvarIn::SimCodeVar.SimVar, inHT::HashTable) ::HashTable 
              local outHT::HashTable

              outHT = begin
                  local cr::DAE.ComponentRef
                  local acr::DAE.ComponentRef
                  local sv::SimCodeVar.SimVar
                @matchcontinue (simvarIn, inHT) begin
                  (sv && SimCodeVar.SIMVAR(name = cr, arrayCref = NONE()), _)  => begin
                      outHT = BaseHashTable.add((cr, sv), inHT)
                    outHT
                  end
                  
                  (sv && SimCodeVar.SIMVAR(name = cr, arrayCref = SOME(acr)), _)  => begin
                      outHT = BaseHashTable.add((acr, sv), inHT)
                      outHT = BaseHashTable.add((cr, sv), outHT)
                    outHT
                  end
                  
                  _  => begin
                        Error.addInternalError("function addSimVarToHashTable failed", sourceInfo())
                      fail()
                  end
                end
              end
               #= print(\"addSimVarToHashTable: handling variable '\" + ComponentReference.printComponentRefStr(cr) + \"'\\n\");
               =#
               #=  add the whole array crefs to the hashtable, too
               =#
               #= print(\"addSimVarToHashTable: handling array variable '\" + ComponentReference.printComponentRefStr(cr) + \"'\\n\");
               =#
          outHT
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end
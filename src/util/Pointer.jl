    #= Creating shared (sometimes mutable) objects.

   This uniontype contains routines for creating and updating objects,
   similar to array<> structures. Use this uniontype over the Mutable
   package if you need to be able to create constants that are just
   pointers to static, immutable data. Use the Mutable uniontype if you
   do not need to create constants (that package has lower overhead
   since it does no extra checks). =#
   @Uniontype Pointer begin
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

        function create(data::T) ::Pointer{T} 
              local ptr::Pointer{T}

            #= TODO: Defined in the runtime =#
          ptr
        end

        function createImmutable(data::T) ::Pointer{T} 
              local ptr::Pointer{T}

            #= TODO: Defined in the runtime =#
          ptr
        end

        function update(mutable::Pointer{<:T}, data::T)  
            #= TODO: Defined in the runtime =#
        end

        function access(mutable::Pointer{<:T}) ::T 
              local data::T

            #= TODO: Defined in the runtime =#
          data
        end
   end
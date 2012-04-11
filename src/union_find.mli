(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2012 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)
 
module type Elem = 
  sig
    type t 
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type UF = 
    sig 
      type e
      type t

(* expected size *)
      val create : int -> t
      val add : t -> e -> unit
      val find : t -> e -> e 
      val union : t -> e -> e -> unit
    end 

module Make: functor (E : Elem) -> UF with type e = E.t


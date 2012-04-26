(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
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


module type Elem0 =
sig 

  (* The type of an element *)
  type t 

end


(* An element in the priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

  val equal : t -> t -> bool

  (* A flag for membership of an element in each queue *)
  val in_queue : t -> bool

  (* A function setting the membership flag for each queue *)
  val assign_in_queue : bool -> t -> unit

  (* The multiplier for each queue *)
  val mult : int
    
end


module QueueN (Elem0 : Elem0) :
sig
  type elt
  type t
  exception Empty
  val create : int -> (module ElemN with type t = elt) list -> t
  val add_all : t -> elt -> unit
  val is_empty : t -> bool
  val clean : int -> t -> unit
  val remove' : t -> queue list -> elt
  val remove : t -> elt
end

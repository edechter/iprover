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


(* A bare element module with only the type and no operations, those
   are given in a separate module at runtime *)
module type Elem0 =
sig 
  type t 
end


(* An element in a priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

  (* A flag for membership of an element in each queue *)
  val in_queue : t -> bool

  (* A function setting the membership flag for each queue *)
  val assign_in_queue : bool -> t -> unit

  (* The multiplier for each queue *)
  val mult : int
    
end

module QueueN(E : Elem0) : sig

  (* The type of an n-ary priority queue *)
  type t

  (* The type of the elements *)
  type elt = E.t

  (* All queues are empty 

     We should to call [clean] after the queues are empty. *)
  exception Empty 

  (* Create n priority queues containing elements of the same type but
     with different orderings *)
  val create   : int -> (module ElemN with type t = elt) list -> t

  (* The number of elements in the queues *)
  val num_elem : t -> int

  (* Add an element to all queues *)
  val add_all : t -> elt -> unit

  (* Are alle queues empty? *)
  val is_empty : t -> bool

(* if we find that passive queue is empty then we need to clean it: *)
(* (done by PassiveQueue.clean) *)
(* 1. assign in_queue param to false in all clauses in the remaining queue*)
(* 2. release memory and assign new queues *)

  (* Clean queues, that is, recreate the data structures *)
  val clean    : int -> t -> unit
    
  (* Removes the maximal element from some queue *)
  val remove   : t -> elt
    
end




module type Elem2 = sig
  type t
  val compare1  : t -> t -> int
(* is used for checking whether t is in queue1*)
(* assuming it is stored in t as a parameter  *)
  val in_queue1        : t -> bool
  val assign_in_queue1 : bool -> t -> unit
  val mult1     : int
  val compare2  : t -> t -> int
  val mult2     : int
  val in_queue2 : t -> bool
  val assign_in_queue2 : bool -> t -> unit
end




module Queue2(Elem2:Elem2) : sig
  type t
  val create   : int  -> t
  val num_elem : t -> int
  val add      : t -> Elem2.t -> unit
  val is_empty : t -> bool

(* if we find that passive queue is empty then we need to clean it: *)
(* (done by PassiveQueue.clean) *)
(* 1. assign in_queue param to false in all clauses in the remaining queue*)
(* 2. release memory and assign new queues *)

  val clean    : int -> t -> unit
  exception Empty 

(*removes maximal element*)
  val remove   : t -> Elem2.t
end

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

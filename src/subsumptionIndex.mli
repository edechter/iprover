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

(*DEBUG is On can be slow !!!*)

open Lib
(* index is based on feature index of S. Schulz  *)


type clause  = Clause.clause
type literal = Clause.literal

module type Feature =
  sig
    type t
    val compare : t -> t -> int
  (*  val get_feature_list : clause -> t list *)
  end


module type Index = 
  sig
   
  
    type feature

    type index

    val create : unit -> index

  (* we assume that feature list is of the same length for 
     every clause, and if C subsumes D then feature list of  D)
     is greater or equal than feature list of  C*)


 (* we assume that the the clause is in clause db*)
    val add_clause  : feature list -> clause -> index ref -> unit

(* check if the clause is subsumed and 
   returns  Some ((d,unif)) if it is and None otherwise*)
	
    val is_subsumed : 
	feature list -> clause -> index ref -> (clause*Subst.subst) option
	
(* returns list of  all  subsumed clauses by the clause
   and removes them from the index
   [] if no such clauses*)

    val find_subsumed :  feature list -> clause -> index ref -> clause list


(* the same as find_subsumed but also gives subsitution: (subsumed, subst) list*)
    val find_subsumed_subst :   
	index ref -> feature list -> clause -> (clause*Subst.subst) list

    val remove_clause : index ref -> feature list -> clause -> unit 	
(*    val  remove_subsumed : clause -> index -> index *)
    

 end

module type FeatureCom =
  sig
    type t
(* compare position  *)
    val compare_p : t -> t -> int
(* compare the value *)
    val compare_v : t -> t -> int
(*for debug*)
    val to_string : t -> string
  end

module Make(Feature:Feature): (Index with type feature=Feature.t)

module MakeCom(FeatureCom:FeatureCom): (Index with type feature=FeatureCom.t)

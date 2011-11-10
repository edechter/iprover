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
   (* val get_feature_list : clause -> t list *)
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
	
(*    val  remove_subsumed : clause -> index -> index *)
   
 end


module Make(Feature:Feature)  =
  struct
    type feature = Feature.t

    module VIndexM = VectorIndex.Make (Feature)
    type index = (clause list ) VIndexM.index

(* when debug then we store all clauses added to index in
   debug_list and check operations w.r.t. to that list*)

    let  (debug_list : (clause list) ref) = ref [] 
 
    let create () = VIndexM.create ()

(* we have normal and debug versions  *)
    let add_clause_normal feature_list clause index_ref = 
     (* let feature_list =  Feature.get_feature_list clause in *)             
      let elem_ref = VIndexM.add feature_list index_ref in
	match !elem_ref with 
	|Elem(elem) -> 
	    if not (List.exists (Clause.equal clause) elem) 
	    then 
	      elem_ref:=Elem(clause::elem);
	    Clause.set_bool_param 
	      true Clause.in_subsumption_index clause
	|Empty_Elem -> elem_ref:= Elem([clause])

  let add_clause_debug feature_list clause index_ref =
    add_clause_normal feature_list clause index_ref;
    debug_list:= clause::!debug_list

    let is_subsumed_normal feature_list clause index_ref = 
     (* let feature_list = Feature.get_feature_list clause in *)
      let is_subsumed_by d = 
	try
	  let unif = Unif.subsumes d clause in 
	  Some ((d,unif))
	with   
	  Unif.Subsumtion_failed -> None
      in 
      VIndexM.findf_leq (list_findf is_subsumed_by) feature_list index_ref

  let is_subsumed_debug feature_list clause index_ref = 
    match (is_subsumed_normal feature_list clause index_ref) 
    with 
    |Some(x) -> Some(x)
    |None -> 
	let f d =	
	  try
	    let unif = Unif.subsumes d clause in 
	    Some ((d,unif))
	  with   
	    Unif.Subsumtion_failed -> None
	in
	(match (list_findf f !debug_list) with 
	|Some(_) -> failwith "subsumptionIndex is_subsumed_debug: NOT Complete!!!" 
	|None -> None
	)


(* from the list of clauses returnes (list of subsumed, the rest)  *)
    let rec get_subsumed clause = function 
      |h::tl ->  
	  (try (* if needed can get unif here*)
	    let _ = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed clause tl in 
	    (h::rest_subsumed, rest)
	  with 
	    Unif.Subsumtion_failed -> 
              let (rest_subsumed, rest) = get_subsumed clause tl in 
	      (rest_subsumed, h::rest)
	  )
      |[] -> ([],[])

    let find_subsumed_normal feature_list clause index_ref = 
      (* let feature_list = Feature.get_feature_list clause in *)
      let f elem_ref = 
	match !elem_ref with
	|Elem(clause_list) -> 
            let (subsumed,rest) = get_subsumed clause clause_list in 
	    (out_str_debug 
	       (	
		 "Subsumer: "
		 ^(Clause.to_string clause)^"\n"
		 ^"Clauses in Leaf: "
		 ^(Clause.clause_list_to_string clause_list)^"\n"
		 ^"Subsumed: "
		 ^(Clause.clause_list_to_string subsumed)^"\n")); 
	    (if rest = [] 
	    then (*Here is the error!!!*)
	     ( VIndexM.remove feature_list index_ref;
	       out_str_debug "Remove empty leaf from VIndexM \n")
	    else 
	      (if (subsumed != []) then
		(out_str_debug 
		  ("Old clause list"
		   ^(Clause.clause_list_to_string clause_list)^"\n"
		   ^"New clause list "
		   ^(Clause.clause_list_to_string rest)^"\n");
		 elem_ref:= Elem(rest)
		)
	      )
	    );	  
	    subsumed
	|Empty_Elem -> [] 
      in
      VIndexM.findf_all_geq f feature_list index_ref

    let find_subsumed_debug feature_list clause index_ref = 
      let subsumed_from_index = 
	find_subsumed_normal feature_list clause index_ref in
      let (subsumed_debug,rest_debug) = get_subsumed clause !debug_list in
(*debug*)
      if subsumed_from_index != [] 
      then 
	out_str_debug 
	  ("find_subsumed_debug: "
	   ^(Clause.to_string clause)
	   ^"Subsumes from index "
	   ^(Clause.clause_list_to_string subsumed_from_index)^"\n"
	   ^"Subsumes from debug_list"
	   ^(Clause.clause_list_to_string subsumed_debug)^"\n"
	   ^"Debug_list: "
	   ^(Clause.clause_list_to_string !debug_list)^"\n");
      if (List.length subsumed_from_index) != (List.length subsumed_debug)    
      then	      
	 failwith "subsumptionIndex find_subsumed_debug: Not Complete !!!"
      else 
	(debug_list := rest_debug;
	 subsumed_from_index)

(***********change debug / normal versions****************)
let add_clause    = add_clause_debug
let is_subsumed   = is_subsumed_debug 
let find_subsumed = find_subsumed_debug	
  
  end

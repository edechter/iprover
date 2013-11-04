(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006 -2012 Konstantin Korovin and The University of Manchester.
   This file is part of iProver - a theorem prover for first - order logic.

   iProver is free software: you can redistribute it and / or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver. If not, see < http:// www.gnu.org / licenses />. *)
(*----------------------------------------------------------------------[C]-*)

(*DEBUG is On can be slow !!!*)

open Lib
(* index is based on feature index of S. Schulz  *)

type clause = Clause.clause
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
	   every clause, and if C subsumes D then feature list of D)
	   is greater or equal than feature list of C *)
	
	(* we assume that the the clause is in clause db*)
    val add_clause : feature list -> clause -> index ref -> unit
	
	(* check if the clause is subsumed and
	   returns Some ((d, unif)) if it is and None otherwise *)
	
    val is_subsumed :
	feature list -> clause -> index ref -> (clause * Subst.subst) option
	    
	    (* returns list of all subsumed clauses by the clause
	       and removes them from the index
	       [] if no such clauses *)
	    
    val find_subsumed : feature list -> clause -> index ref -> clause list
	
    val find_subsumed_subst :
	index ref -> feature list -> clause -> (clause * Subst.subst) list
	    
    val remove_clause : index ref -> feature list -> clause -> unit

(*    val  remove_subsumed : clause -> index -> index *)

  end

(*-----------Based on Compressed index see vectorIndex Compressed---------------*)

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

module MakeCom(FeatureCom: FeatureCom) =
  struct
    (* There are three versions of main functions: normal, list and debug *)
    (* the list and debug versions are used for debugging *)
    (* to switch between versions uncomment corresponding functions at the end *)
    
    type feature = FeatureCom.t
	  
    module VIndexM = VectorIndex.MakeCom (FeatureCom)
    type index = (clause list ) VIndexM.index
	  
	  (* when debug then we store all clauses added to index in
	     debug_list and check operations w.r.t. to that list *)
	  
    let (debug_list : (clause list) ref) = ref []
	
    let create () = VIndexM.create ()
	
    let to_string_feat_list l =
      list_to_string FeatureCom.to_string l ";"
	
	(* we have normal and debug versions  *)
    let add_clause_normal feature_list clause index_ref =
      (* let feature_list =  Feature.get_feature_list clause in *)
      let elem_ref = VIndexM.add feature_list index_ref in
      match !elem_ref with
      | Elem(elem) ->
	  if not (List.exists (Clause.equal clause) elem)
	  then
	    elem_ref:= Elem(clause:: elem);
	  (*Clause.set_bool_param
	    true Clause.in_subsumption_index clause
	   *)
	  Clause.set_ps_in_subsumption_index true clause
      | Empty_Elem -> elem_ref:= Elem([clause])
	    
    let add_clause_list clause =
      debug_list:= clause::!debug_list
			     
    let add_clause_debug feature_list clause index_ref =
      (* out_str ("Add clause: "
	 ^(Clause.to_string clause)
	 ^"  "^(to_string_feat_list feature_list)^"\n");*)
      add_clause_normal feature_list clause index_ref;
      add_clause_list clause
	
	(*--------------Forward Subsumption-------------------*)
	
    let is_subsumed_normal feature_list clause index_ref =
      (* let feature_list = Feature.get_feature_list clause in *)
      
      let is_subsumed_by d =
	if not (Clause.get_is_dead d)
	then
	  try
	    let unif = Unif.subsumes d clause in
	    Some ((d, unif))
	  with
	    Unif.Subsumtion_failed ->
	      (
	       (* out_str ("Clause to subume: "
		  ^(Clause.to_string clause)^" "
		  ^(to_string_feat_list feature_list)^"\n");
		  out_str ("Failed by: "^(Clause.to_string d)^"\n");*)
	       None)
	else None
      in
      VIndexM.findf_leq (list_findf is_subsumed_by) feature_list index_ref
	
	(* List version *)
    let is_subsumed_list clause =
      let f d =
	if not (Clause.get_is_dead d)
	then
	  try
	    let unif = Unif.subsumes d clause in
	    Some ((d, unif))
	  with
	    Unif.Subsumtion_failed -> None
	else None
      in
      (match (list_findf f !debug_list) with
      | Some(x) -> Some(x)
	    
      | None -> None
      )
	
	(* Debug version *)
    let is_subsumed_debug feature_list clause index_ref =
      match (is_subsumed_normal feature_list clause index_ref) with
      | Some(x) -> Some(x)
      | None ->
	  (
	   match (is_subsumed_list clause) with
	   | Some((d, unif)) ->
	       out_str ("\n Clause: "^(Clause.to_string clause)
			^" "^(to_string_feat_list feature_list)^"\n"
			^" Subsumed by "^(Clause.to_string d)^"\n"
			^"but not by a clause in index\n");
	       failwith "is_subsumed_debug: subsumed by list but not by index"
	   | None -> None
	  )
	    
	    (*-----------Backward Subsumption-------------------*)
	    (*
	      let eliminate_dead clauses =
	      List.filter
	      (fun c -> not (Clause.get_bool_param Clause.is_dead c))
	     *)
	    
	    (* out_str ("\n Clause: "^(Clause.to_string clause)
	       ^" "^(to_string_feat_list feature_list)^"\n"
	       ^" Subsumed by "^(Clause.to_string cl)^"\n");*)
	    
	    (* from the list of clauses returnes (list of subsumed, the rest)  *)
    let rec get_subsumed clause = function
      | h:: tl ->
	  (try (* if needed can get unif here*)
	    let _ = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed clause tl in
	    (h:: rest_subsumed, rest)
	  with
	    Unif.Subsumtion_failed ->
	      let (rest_subsumed, rest) = get_subsumed clause tl in
	      (rest_subsumed, h:: rest)
	  )
      |[] -> ([],[])
	    
    let find_subsumed_normal feature_list clause index_ref =
      (* let feature_list = Feature.get_feature_list clause in *)
      (*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref =
	match !elem_ref with
	| Elem(clause_list) ->
	    let (subsumed, rest) = get_subsumed clause clause_list in
	    List.iter
	      (Clause.set_ps_in_subsumption_index false) subsumed;
	    (* (out_str
	       (
	       "Subsumer: "
	       ^(Clause.to_string clause)^"\n"
	       ^"Clauses in Leaf: "
	       ^(Clause.clause_list_to_string clause_list)^"\n"
	       ^"Subsumed: "
	       ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	    (if rest = []
	    then (*Here is the error!!!*)
	      (VIndexM.remove (List.rev followed_key_list) index_ref
		 (* out_str ("Remove empty leaf from VIndexM \n"
		    ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n" ) *)
	      )
	    else
	      (elem_ref:= Elem(rest))(* (if (subsumed != []) then
					(out_str
					("Old clause list"
					^(Clause.clause_list_to_string clause_list)^"\n"
					^"New clause list "
					^(Clause.clause_list_to_string rest)^"\n");
					elem_ref:= Elem(rest))
					)	*)
	    );
	    subsumed
	| Empty_Elem -> []
      in
      VIndexM.findf_all_geq f feature_list index_ref
	
	(*-----List version------------------*)
    let find_subsumed_list clause =
      let (subsumed, rest) = get_subsumed clause !debug_list in
      debug_list:= rest;
      subsumed
	
	(*-----Debug version------------------*)
    let find_subsumed_debug feature_list clause index_ref =
      let subsumed_from_index =
	find_subsumed_normal feature_list clause index_ref in
      let (subsumed_debug, rest_debug) = get_subsumed clause !debug_list in
      (*debug*)
      (* if subsumed_from_index != []
	 then
	 out_str
	 ("find_subsumed_debug: "
	 ^(Clause.to_string clause)
	 ^"Subsumes from index "
	 ^(Clause.clause_list_to_string subsumed_from_index)^"\n"
	 ^"Subsumes from debug_list"
	 ^(Clause.clause_list_to_string subsumed_debug)^"\n"
	 ^"Debug_list: "
	 ^(Clause.clause_list_to_string !debug_list)^"\n");*)
      
      if (List.length subsumed_from_index) != (List.length subsumed_debug)
      then
	(out_str
	   ("\n Subsumed in debug: "^"\n"
	    ^"By Clause "^(Clause.to_string clause)
	    ^"  "^(to_string_feat_list feature_list)^"\n"
	    ^(list_to_string Clause.to_string subsumed_debug "\n")^"\n" );
	 failwith "subsumptionIndex find_subsumed_debug: Not Complete !!!")
      else
	(debug_list := rest_debug;
	 subsumed_from_index)
	  
	  (*-----------Backward Subsumption Resolution-------------------*)
	  
	  (* like get_subsumed but also returns substitutions *)
let rec get_subsumed_subst clause = function
  | h:: tl ->
      (try (* if needed can get unif here*)
	let subs = Unif.subsumes clause h in
	let (rest_subsumed, rest) = get_subsumed_subst clause tl in
	(((h, subs):: rest_subsumed), rest)
      with
	Unif.Subsumtion_failed ->
	  let (rest_subsumed, rest) = get_subsumed_subst clause tl in
	  (rest_subsumed, h:: rest)
      )
  |[] -> ([],[])
	
	(* output: ((subsumed,subst) list *)
	(* we need substitution for subs. resolution *)
let find_subsumed_subst index_ref feature_list clause =
  (* let feature_list = Feature.get_feature_list clause in *)
  (*      let all_subsumed = ref []in*)
  let f followed_key_list elem_ref =
    match !elem_ref with
    | Elem(clause_list) ->
	let (subsumed, rest) = get_subsumed_subst clause clause_list in
	(* (out_str
	   (
	   "Subsumer: "
	   ^(Clause.to_string clause)^"\n"
	   ^"Clauses in Leaf: "
	   ^(Clause.clause_list_to_string clause_list)^"\n"
	   ^"Subsumed: "
	   ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	List.iter
	  (fun (c, _) ->
	    (Clause.set_ps_in_subsumption_index false c)) subsumed;
	(if rest = []
	then
	  (VIndexM.remove (List.rev followed_key_list) index_ref
	     (* out_str ("Remove empty leaf from VIndexM \n"
		^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n" ) *)
	  )
	else
	  (elem_ref:= Elem(rest)
	  )(* (if (subsumed != []) then
	      (out_str
	      ("Old clause list"
	      ^(Clause.clause_list_to_string clause_list)^"\n"
	      ^"New clause list "
	      ^(Clause.clause_list_to_string rest)^"\n");
	      elem_ref:= Elem(rest))
	      )	*)
	);
	subsumed
    | Empty_Elem -> []
  in
  VIndexM.findf_all_geq f feature_list index_ref
    
    (*-----List version------------------*)
let find_subsumed_list_subst clause =
  let (subsumed, rest) = get_subsumed_subst clause !debug_list in
  debug_list:= rest;
  subsumed
    
    (*-----Debug version------------------*)
let find_subsumed_subst_debug index_ref feature_list clause =
  let subsumed_from_index =
    find_subsumed_subst index_ref feature_list clause in
  let (subsumed_debug, rest_debug) = get_subsumed_subst clause !debug_list in
  (*debug*)
  (* if subsumed_from_index != []
     then
     out_str
     ("find_subsumed_debug: "
     ^(Clause.to_string clause)
     ^"Subsumes from index "
     ^(Clause.clause_list_to_string subsumed_from_index)^"\n"
     ^"Subsumes from debug_list"
     ^(Clause.clause_list_to_string subsumed_debug)^"\n"
     ^"Debug_list: "
     ^(Clause.clause_list_to_string !debug_list)^"\n");*)
  
  if (List.length subsumed_from_index) != (List.length subsumed_debug)
  then
    (let subsumed_debug_cl_list =
      List.map (fun (c, _) -> c) subsumed_debug in
    out_str
      ("\n Subsumed in debug: "^"\n"
       ^"By Clause "^(Clause.to_string clause)
       ^"  "^(to_string_feat_list feature_list)^"\n"
       ^(list_to_string Clause.to_string subsumed_debug_cl_list "\n")^"\n" );
    failwith "subsumptionIndex find_subsumed_subst_debug: Not Complete !!!")
  else
    (debug_list := rest_debug;
     subsumed_from_index)
      
      (*------Removes clause from index--------------*)
let remove_clause index_ref feature_list clause =
  Clause.set_ps_in_subsumption_index false clause;
  let elem_ref = (VIndexM.find feature_list !index_ref) in
  match !elem_ref with
  | Elem(clause_list) ->
      let new_list =
	List.filter (fun c -> not (clause == c)) clause_list in
      if new_list = []
      then
	(VIndexM.remove feature_list index_ref)
      else
	(elem_ref:= Elem(new_list))
  | Empty_Elem -> VIndexM.remove feature_list index_ref
	
	(*---- List version ---------------*)
	
let remove_clause_list clause =
  debug_list := (List.filter (fun c -> not (clause == c)) (!debug_list))
      
      (*---- Debug version ---------------*)
let remove_clause_debug index_ref feature_list clause =
  remove_clause index_ref feature_list clause;
  remove_clause_list clause
    
    (*-------------change list/debug/normal versions--------------------*)
    
    (*
      let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption List!!!!!!!!!!!!!!\n"
      
      let add_clause _feature_list clause _index_ref = add_clause_list clause
      let is_subsumed _feature_list clause _index_ref = is_subsumed_list clause
      let find_subsumed _feature_list clause _index_ref = find_subsumed_list clause
      let find_subsumed_subst _ _ clause = find_subsumed_list_subst clause
      let remove_clause _ _ clause = remove_clause_list clause
     *)
    
    (*
      let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption Debug!!!!!!!!!!!!!!\n"
      
      let add_clause = add_clause_debug
      let is_subsumed = is_subsumed_debug
      let find_subsumed = find_subsumed_debug
      let find_subsumed_subst = find_subsumed_subst_debug
      let remove_clause = remove_clause_debug
     *)
    
let add_clause = add_clause_normal
let is_subsumed = is_subsumed_normal
let find_subsumed = find_subsumed_normal
    
end

(*--------------Currently Not Used, Replaced by Compressed version Above-------*)

(*--------------Based on Uncompressed Feature Index-------------------------*)
(* all functions defined exactly as in the compressed index *)
(*but here we use uncompressed module, (with the same interface as compressed) *)

module Make(Feature: Feature) =
  struct
    type feature = Feature.t
	  
    module VIndexM = VectorIndex.Make (Feature)
    type index = (clause list ) VIndexM.index
	  
	  (* when debug then we store all clauses added to index in
	     debug_list and check operations w.r.t. to that list *)
	  
    let (debug_list : (clause list) ref) = ref []
	
    let create () = VIndexM.create ()
	
	(* we have normal and debug versions  *)
    let add_clause_normal feature_list clause index_ref =
      (* let feature_list =  Feature.get_feature_list clause in *)
      let elem_ref = VIndexM.add feature_list index_ref in
      match !elem_ref with
      | Elem(elem) ->
	  if not (List.exists (Clause.equal clause) elem)
	  then
	    elem_ref:= Elem(clause:: elem);
	  Clause.set_ps_in_subsumption_index true clause
      | Empty_Elem -> elem_ref:= Elem([clause])
	    
    let add_clause_debug feature_list clause index_ref =
      add_clause_normal feature_list clause index_ref;
      debug_list:= clause::!debug_list
			     
			     (*--------------Forward Subsumption-------------------*)
			     
    let is_subsumed_normal feature_list clause index_ref =
      (* let feature_list = Feature.get_feature_list clause in *)
      
      let is_subsumed_by d =
	if not (Clause.get_is_dead d)
	then
	  try
	    (* out_str ("Trying subs: "^(Clause.to_string clause)^" by "
	       ^(Clause.to_string d)^"\n");*)
	    let unif = Unif.subsumes d clause in
	    Some ((d, unif))
	  with
	    Unif.Subsumtion_failed ->
	      (
	       (* out_str ("Clause to subume: "
		  ^(Clause.to_string clause)^" "
		  ^(to_string_feat_list feature_list)^"\n");
		  out_str ("Failed by: "^(Clause.to_string d)^"\n");*)
	       None)
	else None
      in
      VIndexM.findf_leq (list_findf is_subsumed_by) feature_list index_ref
	
	(* List version *)
    let is_subsumed_list clause =
      let f d =
	if not (Clause.get_is_dead d)
	then
	  try
	    let unif = Unif.subsumes d clause in
	    Some ((d, unif))
	  with
	    Unif.Subsumtion_failed -> None
	else None
      in
      (match (list_findf f !debug_list) with
      | Some(x) -> Some(x)
	    
      | None -> None
      )
	
	(* Debug version *)
    let is_subsumed_debug feature_list clause index_ref =
      match (is_subsumed_normal feature_list clause index_ref) with
      | Some(x) -> Some(x)
      | None ->
	  (
	   match (is_subsumed_list clause) with
	   | Some((d, unif)) ->
	       out_str ("\n Clause: "^(Clause.to_string clause)^"\n"
			^" Subsumed by "^(Clause.to_string d)^"\n"
			^"but not by a clause in index\n");
	       failwith "is_subsumed_debug: subsumed by list but not by index"
	   | None -> None
	  )
	    
	    (*-----------Backward Subsumption-------------------*)
	    (*
	      let eliminate_dead clauses =
	      List.filter
	      (fun c -> not (Clause.get_bool_param Clause.is_dead c))
	     *)
	    
	    (* out_str ("\n Clause: "^(Clause.to_string clause)
	       ^" "^(to_string_feat_list feature_list)^"\n"
	       ^" Subsumed by "^(Clause.to_string cl)^"\n");*)
	    
	    (* from the list of clauses returnes (list of subsumed, the rest)  *)
    let rec get_subsumed clause = function
      | h:: tl ->
	  (try (* if needed can get unif here*)
	    let _ = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed clause tl in
	    (h:: rest_subsumed, rest)
	  with
	    Unif.Subsumtion_failed ->
	      let (rest_subsumed, rest) = get_subsumed clause tl in
	      (rest_subsumed, h:: rest)
	  )
      |[] -> ([],[])
	    
    let find_subsumed_normal feature_list clause index_ref =
      (* let feature_list = Feature.get_feature_list clause in *)
      (*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref =
	match !elem_ref with
	| Elem(clause_list) ->
	    let (subsumed, rest) = get_subsumed clause clause_list in
	    List.iter
	      (Clause.set_ps_in_subsumption_index false) subsumed;
	    (* (out_str
	       (
	       "Subsumer: "
	       ^(Clause.to_string clause)^"\n"
	       ^"Clauses in Leaf: "
	       ^(Clause.clause_list_to_string clause_list)^"\n"
	       ^"Subsumed: "
	       ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	    (if rest = []
	    then (*Here is the error!!!*)
	      (VIndexM.remove (List.rev followed_key_list) index_ref
		 (* out_str ("Remove empty leaf from VIndexM \n"
		    ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n" ) *)
	      )
	    else
	      (elem_ref:= Elem(rest))(* (if (subsumed != []) then
					(out_str
					("Old clause list"
					^(Clause.clause_list_to_string clause_list)^"\n"
					^"New clause list "
					^(Clause.clause_list_to_string rest)^"\n");
					elem_ref:= Elem(rest))
					)	*)
	    );
	    subsumed
	| Empty_Elem -> []
      in
      VIndexM.findf_all_geq f feature_list index_ref
	
	(*-----List version------------------*)
    let find_subsumed_list clause =
      let (subsumed, rest) = get_subsumed clause !debug_list in
      debug_list:= rest;
      subsumed
	
	(*-----Debug version------------------*)
    let find_subsumed_debug feature_list clause index_ref =
      let subsumed_from_index =
	find_subsumed_normal feature_list clause index_ref in
      let (subsumed_debug, rest_debug) = get_subsumed clause !debug_list in
      (*debug*)
      (* if subsumed_from_index != []
	 then
	 out_str
	 ("find_subsumed_debug: "
	 ^(Clause.to_string clause)
	 ^"Subsumes from index "
	 ^(Clause.clause_list_to_string subsumed_from_index)^"\n"
	 ^"Subsumes from debug_list"
	 ^(Clause.clause_list_to_string subsumed_debug)^"\n"
	 ^"Debug_list: "
	 ^(Clause.clause_list_to_string !debug_list)^"\n");*)
      
      if (List.length subsumed_from_index) != (List.length subsumed_debug)
      then
	(out_str
	   ("\n Subsumed in debug: "^"\n"
	    ^"By Clause "^(Clause.to_string clause)^"\n"
	    ^(list_to_string Clause.to_string subsumed_debug "\n")^"\n" );
	 failwith "subsumptionIndex find_subsumed_debug: Not Complete !!!")
      else
	(debug_list := rest_debug;
	 subsumed_from_index)
	  
	  (*-----------Backward Subsumption Resolution-------------------*)
	  
	  (* like get_subsumed but also returns substitutions *)
    let rec get_subsumed_subst clause = function
      | h:: tl ->
	  (try (* if needed can get unif here*)
	    let subs = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed_subst clause tl in
	    (((h, subs):: rest_subsumed), rest)
	  with
	    Unif.Subsumtion_failed ->
	      let (rest_subsumed, rest) = get_subsumed_subst clause tl in
	      (rest_subsumed, h:: rest)
	  )
      |[] -> ([],[])
	    
	    (* output: ((subsumed,subst) list *)
	    (* we need substitution for subs. resolution *)
    let find_subsumed_subst index_ref feature_list clause =
      (* let feature_list = Feature.get_feature_list clause in *)
      (*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref =
	match !elem_ref with
	| Elem(clause_list) ->
	    let (subsumed, rest) = get_subsumed_subst clause clause_list in
	    (* (out_str
	       (
	       "Subsumer: "
	       ^(Clause.to_string clause)^"\n"
	       ^"Clauses in Leaf: "
	       ^(Clause.clause_list_to_string clause_list)^"\n"
	       ^"Subsumed: "
	       ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	    List.iter
	      (fun (c, _) ->
		(Clause.set_ps_in_subsumption_index false c)) subsumed;
	    (if rest = []
	    then
	      (VIndexM.remove (List.rev followed_key_list) index_ref
		 (* out_str ("Remove empty leaf from VIndexM \n"
		    ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n" ) *)
	      )
	    else
	      (elem_ref:= Elem(rest)
	      )(* (if (subsumed != []) then
		  (out_str
		  ("Old clause list"
		  ^(Clause.clause_list_to_string clause_list)^"\n"
		  ^"New clause list "
		  ^(Clause.clause_list_to_string rest)^"\n");
		  elem_ref:= Elem(rest))
		  )	*)
	    );
	    subsumed
	| Empty_Elem -> []
      in
      VIndexM.findf_all_geq f feature_list index_ref
	
	(*-----List version------------------*)
    let find_subsumed_list_subst clause =
      let (subsumed, rest) = get_subsumed_subst clause !debug_list in
      debug_list:= rest;
      subsumed
	
	(*-----Debug version------------------*)
    let find_subsumed_subst_debug index_ref feature_list clause =
      let subsumed_from_index =
	find_subsumed_subst index_ref feature_list clause in
      let (subsumed_debug, rest_debug) = get_subsumed_subst clause !debug_list in
      (*debug*)
      (* if subsumed_from_index != []
	 then
	 out_str
	 ("find_subsumed_debug: "
	 ^(Clause.to_string clause)
	 ^"Subsumes from index "
	 ^(Clause.clause_list_to_string subsumed_from_index)^"\n"
	 ^"Subsumes from debug_list"
	 ^(Clause.clause_list_to_string subsumed_debug)^"\n"
	 ^"Debug_list: "
	 ^(Clause.clause_list_to_string !debug_list)^"\n");*)
      
      if (List.length subsumed_from_index) != (List.length subsumed_debug)
      then
	(let subsumed_debug_cl_list =
	  List.map (fun (c, _) -> c) subsumed_debug in
	out_str
	  ("\n Subsumed in debug: "^"\n"
	   ^"By Clause "^(Clause.to_string clause)^"\n"
	   ^(list_to_string Clause.to_string subsumed_debug_cl_list "\n")^"\n" );
	failwith "subsumptionIndex find_subsumed_subst_debug: Not Complete !!!")
      else
	(debug_list := rest_debug;
	 subsumed_from_index)
	  
	  (*------Removes clause from index--------------*)
    let remove_clause index_ref feature_list clause =
      Clause.set_ps_in_subsumption_index false clause;
      let elem_ref = (VIndexM.find feature_list !index_ref) in
      match !elem_ref with
      | Elem(clause_list) ->
	  let new_list =
	    List.filter (fun c -> not (clause == c)) clause_list in
	  if new_list = []
	  then
	    (VIndexM.remove feature_list index_ref)
	  else
	    (elem_ref:= Elem(new_list))
      | Empty_Elem -> VIndexM.remove feature_list index_ref
	    
	    (*---- List version ---------------*)
	    
    let remove_clause_list clause =
      debug_list := (List.filter (fun c -> not (clause == c)) (!debug_list))
	  
	  (*---- Debug version ---------------*)
    let remove_clause_debug index_ref feature_list clause =
      remove_clause index_ref feature_list clause;
      remove_clause_list clause
	
	(*-------------change debug/list/normal versions--------------------*)
	
	(*
	  let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption List!!!!!!!!!!!!!!\n"
	  
	  let add_clause _feature_list clause _index_ref = add_clause_list clause
	  let is_subsumed _feature_list clause _index_ref = is_subsumed_list clause
	  let find_subsumed _feature_list clause _index_ref = find_subsumed_list clause
	  let find_subsumed_subst _ _ clause = find_subsumed_list_subst clause
	  let remove_clause _ _ clause = remove_clause_list clause
	 *)
	
    let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption Debug!!!!!!!!!!!!!!\n"
	
    let add_clause = add_clause_debug
    let is_subsumed = is_subsumed_debug
    let find_subsumed = find_subsumed_debug
    let find_subsumed_subst = find_subsumed_subst_debug
    let remove_clause = remove_clause_debug
	
	(*
	  let add_clause = add_clause_normal
	  let is_subsumed = is_subsumed_normal
	  let find_subsumed = find_subsumed_normal
	 *)
  end





(*---------------------------------------------------------------------------*)
(* concrete implementation of compressed features; based on this concrete subsumtion index is defined using MakeCF *)
(* trasnferred from discount.ml *)
(*---------------------------------------------------------------------------*)

(*--------------Generalised feature index--------*)

(* symbol hierchy: *)
(* first is position of the  hierarchy level, second is the value:*)
(* 1 (or number of ) if the clause contains a symbol from   *)
(* the corresponding hierarchy level and 0 otherwise *)
(* symbol information SymbF: *)
(* first is the symbol group, second is depth, *)
(* third is the number  of occurences of symbs of this group at this depth *)
(* the lex. combination of group and depth is a generalised position *)
(* these positions are greater than any of HierchF positions  *)
(* this should be also reflected in the compare function in the feature module below*)
type feature = 
  |HierF of int * int 
  |SymF of int * int * int

let feature_to_string = function
  |HierF (pos,v) -> 
      ("H("^(string_of_int pos)^","^(string_of_int v)^")")
  |SymF (sym_gr, depth, v) ->  
      ("SymF("^(string_of_int sym_gr)^","^(string_of_int depth)
       ^","^(string_of_int v)^")")


let feature_list_to_string flist = 
  list_to_string feature_to_string flist ";"

(*--------------Group Hierachy for the feature index--------*)
(* we build a compressed feature index where *) 
(* all minimal values are compressed:    *)
(* compressed feature vector is a list of pairs (p,v) where p is a  position *)
(* with a non-zero value v in the original vector index *)
(* p can be a "generalised position" as in SymF, the pairs (sym_gr,depth) *)
(* are generalised positions (ordered lex.), *)
(* these positions can be seen as an ordinal positions  *)


(*-------Symbol groups------------------*)
(* main features are based on occurrences of symbols, all symbols *)
(* are partitioned into symbol groups (when are added into SymbolDB), *)
(* the number of groups is Symbol.max_num_of_sym_groups *)
(* in order for the signature to be extendable (and the feature vector flexible)*)
(* we do not change the number of groups *)

(*--------Symbol Hierarchy---------------*)
(* in order to maximize sharing we build a signature group hierarchy:       *)
(* 1 level: all symbols are partitioned into two groups,                    *)
(* at the next level each subgroup is partitioned again into two subgroups  *)
(* the first k bits of the binary representation of a group  encodes        *)
(* the subgroup of the k-th level of the group hierarchy  it belongs to;    *)
(* the first k bits  also correspond                                        *)
(* to the (group hierarchy) index in the feature vector                     *)

let group_hierarchy_depth = 3

(* k >= 1 *)
let rec bit_k_ones k = 
  if k > 0
  then
    succ ((bit_k_ones (pred k)) lsl 1)
  else 0

(* high n mask is assumed to be n 1's  *)
let get_first_n_bits high_n_mask k = 
  high_n_mask land k

let create_bit_high_mask_array k  = 
  let a = Array.make k 0 in 
  for i = 0 to k-1 do a.(i) <- bit_k_ones (succ i) done;
  a


let bit_high_mask_array = create_bit_high_mask_array (group_hierarchy_depth+1)

(* we use a global array (group_array) to represent (part of) the feature vector *)
(* corresponding to the symbol information of the considered clause *)
(* group array is cleaned each time get_sym_group_compressed_features is called *)
(* (it could be replaced with a local hash table) *)
(* in the group array, places are reserved for the subgroup info *)
(* e.g. if a group number i is in binary 101....then the symbol is in subgroups *)
(*  1,10, 101, ..., the corresponding indexes in the group array are *)
(* shit(1)+1, shif(2) +1,shift(3) + 5 where shift corresponds to the index where *)
(* the hierarchy begins in the array, shift(i) = (\sum_{k=1}^{k} 2^k)-1 *)
(* and numbers are just truncated i bits of the symbol_group; *)
(* the boolean 0,1,  can be easily changed to the number of symbols*)
(* in the corresponding subgroup *)



let group_array_size = bit_k_ones (group_hierarchy_depth+1)


let group_array = Array.make group_array_size 0 

let clear_group_array () = Array.fill group_array 0 group_array_size 0

let group_array_to_list ()= 
  let current_list  = ref [] in
  (* not to reverse the list we traverse the array in desc. order *)
  for i = (group_array_size-1) downto 0
  do
    if not (group_array.(i) = 0) then
      current_list:= (HierF(i,group_array.(i)))::(!current_list)
  done;
  !current_list


(* symbol info stored first in a map *)
(* key is sym_group * depth *)
module SymFKey = 
  struct 
    type t = int * int 
    let compare = pair_compare_lex compare compare 
  end

module SymFM = Map.Make (SymFKey)

(* makes an ordered list from the map*)
let symb_info_db_to_list symb_info_db = 
  let f (sym_group,depth) val_ref rest =
    (SymF(sym_group,depth, !val_ref))::rest 
  in
  SymFM.fold f symb_info_db []

let get_sym_group_compressed_features clause= 
  clear_group_array ();
  let lits = Clause.get_literals clause in
  let symb_info_db = ref SymFM.empty in
  let f_t lit =   
    let is_neg = ref false in
    (if (Term.is_neg_lit lit) 
    then is_neg:=true 
    else is_neg:=false);      
    let f_sym depth sym = 
      if (Symbol.symb_neg == sym) || (Symbol.symb_typed_equality == sym)
      then () (* do not take into account equality or neg symbol *)
      else 
	(let sym_group = Symbol.get_group sym in
(*first fill group hierarchy*)	
	for i = 1 to group_hierarchy_depth 
	do
	  let i_ones = bit_high_mask_array.(i-1) in
	  let shift = i_ones - 1 in
	  let index = shift +(get_first_n_bits i_ones sym_group) in
(*	   out_str ("Index: "^(string_of_int index)^"\n");*)
	  group_array.(index)<-1
	      (*     (out_str ("sym_groups_start: "^(string_of_int sym_groups_start)
		     ^" i: "^(string_of_int i)
		     ^" shift: "^(string_of_int shift)
		     ^" index: "^(string_of_int index))
		     )*)
	done;
	(*now fill sym groups values*)

	let signed_depth = 
	  if (!is_neg) then -depth else depth in
	(try 	
	  let v_ref = SymFM.find (sym_group,signed_depth) !symb_info_db in 
	  v_ref:= !v_ref+1
	with 
	  Not_found -> 
	    symb_info_db:= SymFM.add (sym_group,signed_depth) (ref 1) !symb_info_db
	) 
	)
    in
    Term.iter_sym_depth f_sym  lit     
  in
  List.iter f_t lits;
  let symb_info_list = symb_info_db_to_list !symb_info_db in
  (group_array_to_list ())@(List.rev symb_info_list)
			      

let get_feature_list clause = 
  let feats = get_sym_group_compressed_features  clause  in
(*  out_str ("Clause: "^(Clause.to_string clause)^" "
    ^(feature_list_to_string feats)^"\n");*)
  feats




module FeatureCom = 
  struct 
    type t = feature
(* compare position  *)
    let compare_p f1 f2 = 
      match (f1,f2) with 
      |(HierF(h1,_),HierF(h2,_)) -> compare h1 h2
      |(SymF(g1,d1,_),SymF(g2,d2,_)) -> 
	  pair_compare_lex compare compare (g1,d1) (g2,d2)
(* SymF comes after HierF and therefore its positions are bigger *)
      |(HierF _, SymF _) -> -1
      |(SymF _, HierF _) -> 1

(* compare the value *)
    let compare_v f1 f2 = 
      match (f1,f2) with 
      |(HierF(_,v1),HierF(_,v2))   -> compare v1 v2
      |(SymF(_,_,v1),SymF(_,_,v2)) -> compare v1 v2
      |(HierF _, SymF _) -> -1
      |(SymF _, HierF _) -> 1


    let to_string  = feature_to_string
  end


(* concrete implementation of a subsumtion index with fixed compressed features as defined above *)
module SCFVIndex = 
  struct
    include MakeCom(FeatureCom)
    let get_feature_list = get_feature_list 
  end
    
    




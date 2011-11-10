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

   val find_subsumed_subst :   
	index ref -> feature list -> clause -> (clause*Subst.subst) list

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


module MakeCom(FeatureCom:FeatureCom)  =
  struct
(* There are three versions of main functions: normal, list and debug *)
(* the list and debug versions are used for debugging *)
(* to switch between versions uncomment corresponding functions at the end *)

    type feature = FeatureCom.t

    module VIndexM = VectorIndex.MakeCom (FeatureCom)
    type index = (clause list ) VIndexM.index

(* when debug then we store all clauses added to index in
   debug_list and check operations w.r.t. to that list*)

    let  (debug_list : (clause list) ref) = ref [] 
 
    let create () = VIndexM.create ()

    let to_string_feat_list l = 
      list_to_string FeatureCom.to_string l ";"

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



    let add_clause_list clause   =
      debug_list:= clause::!debug_list

    let add_clause_debug feature_list clause index_ref =
      (*out_str ("Add clause: "
	       ^(Clause.to_string clause)
	       ^"  "^(to_string_feat_list feature_list)^"\n");*)
      add_clause_normal feature_list clause index_ref;
      add_clause_list clause

(*--------------Forward Subsumption-------------------*)	  
	
    let is_subsumed_normal feature_list clause index_ref = 
     (* let feature_list = Feature.get_feature_list clause in *)
    
      let is_subsumed_by d = 
	if  not (Clause.get_bool_param Clause.is_dead d)
	then
	  try
	  let unif = Unif.subsumes d clause in 
	  Some ((d,unif))
	  with   
	  Unif.Subsumtion_failed -> 
	    (
	     (*out_str ("Clause to subume: "
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
	if  not (Clause.get_bool_param Clause.is_dead d)
	then
	  try
	    let unif = Unif.subsumes d clause in 
	    Some ((d,unif))
	  with   
	    Unif.Subsumtion_failed -> None
	else None
      in
      (match (list_findf f !debug_list) with 
      |Some(x) -> Some(x)
	    
      |None -> None
      )
    
(* Debug version *)	
    let is_subsumed_debug feature_list clause index_ref = 
      match (is_subsumed_normal feature_list clause index_ref) with 
      |Some(x) -> Some(x)
      |None -> 
	  (
	   match (is_subsumed_list clause) with 	  
           |Some((d,unif)) -> 
	       out_str ("\n Clause: "^(Clause.to_string clause)
			^" "^(to_string_feat_list feature_list)^"\n"
			^" Subsumed by "^(Clause.to_string d)^"\n"
			^"but not by a clause in index\n");
               failwith "is_subsumed_debug: subsumed by list but not by index"
	   |None -> None
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
(*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref = 
	match !elem_ref with
	|Elem(clause_list) -> 
            let (subsumed,rest) = get_subsumed clause clause_list in 
	    List.iter 	      
	      (Clause.set_bool_param false Clause.in_subsumption_index) subsumed;
	    (*(out_str
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
		(*out_str ("Remove empty leaf from VIndexM \n"
	          ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n"  ) *)
	      )
	    else 
	      (elem_ref:=Elem(rest))(* (if (subsumed != []) then
		  (out_str
		   ("Old clause list"
		   ^(Clause.clause_list_to_string clause_list)^"\n"
		   ^"New clause list "
		    ^(Clause.clause_list_to_string rest)^"\n");
		   elem_ref:= Elem(rest))
		   )	*)	
            );	  
	     subsumed
	|Empty_Elem -> [] 
      in
      VIndexM.findf_all_geq f feature_list index_ref
    


(*-----List version------------------*)
    let find_subsumed_list clause =
     let  (subsumed,rest) = get_subsumed clause !debug_list  in
     debug_list:= rest;
     subsumed

(*-----Debug version------------------*)
    let find_subsumed_debug feature_list clause index_ref = 
      let subsumed_from_index = 
	find_subsumed_normal feature_list clause index_ref in
      let (subsumed_debug,rest_debug) = get_subsumed clause !debug_list in
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
      |h::tl ->  
	  (try (* if needed can get unif here*)
	    let subs = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed_subst clause tl in 
	    (((h,subs)::rest_subsumed), rest)
	  with 
	    Unif.Subsumtion_failed -> 
              let (rest_subsumed, rest) = get_subsumed_subst clause tl in 
	      (rest_subsumed, h::rest)
	  )
      |[] -> ([],[])

(* output: ((subsumed,subst) list *)
(* we need substitution for subs. resolution *)
let find_subsumed_subst index_ref feature_list clause  = 
      (* let feature_list = Feature.get_feature_list clause in *)
(*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref = 
	match !elem_ref with
	|Elem(clause_list) -> 
            let (subsumed,rest) = get_subsumed_subst clause clause_list in 
	    (*(out_str
	       (	
		 "Subsumer: "
		 ^(Clause.to_string clause)^"\n"
		 ^"Clauses in Leaf: "
		 ^(Clause.clause_list_to_string clause_list)^"\n"
		 ^"Subsumed: "
		 ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	    List.iter 
	      (fun (c,_) ->
		(Clause.set_bool_param false Clause.in_subsumption_index c)) subsumed;
	    (if rest = [] 
	    then 
	      (VIndexM.remove (List.rev followed_key_list) index_ref
		(*out_str ("Remove empty leaf from VIndexM \n"
	          ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n"  ) *)
	      )
	    else 
	      (elem_ref:=Elem(rest)
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
	|Empty_Elem -> []
      in
      VIndexM.findf_all_geq f feature_list index_ref



(*-----List version------------------*)
    let find_subsumed_list_subst clause =
      let  (subsumed,rest) = get_subsumed_subst clause !debug_list  in
      debug_list:= rest;
      subsumed

(*-----Debug version------------------*)
    let find_subsumed_subst_debug index_ref feature_list clause  = 
      let subsumed_from_index = 
	find_subsumed_subst index_ref feature_list clause  in
      let (subsumed_debug,rest_debug) = get_subsumed_subst clause !debug_list in
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
	  List.map (fun (c,_) -> c) subsumed_debug in
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
  Clause.set_bool_param false Clause.in_subsumption_index clause; 
  let elem_ref = (VIndexM.find feature_list !index_ref) in
  match !elem_ref with 
  |Elem(clause_list) -> 
      let new_list = 
	List.filter (fun c-> not (clause==c)) clause_list in      
      if new_list = [] 
      then 
	(VIndexM.remove feature_list index_ref)
      else 
	(elem_ref:=Elem(new_list))
  |Empty_Elem -> VIndexM.remove feature_list index_ref
    


(*---- List version ---------------*)

let remove_clause_list clause = 
  debug_list := (List.filter (fun c-> not (clause==c)) (!debug_list))

(*---- Debug version ---------------*)
let remove_clause_debug index_ref feature_list clause =
  remove_clause index_ref feature_list clause;
  remove_clause_list clause

(*-------------change list/debug/normal versions--------------------*)

(*
let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption List!!!!!!!!!!!!!!\n"

let add_clause    _feature_list clause _index_ref   = add_clause_list    clause
let is_subsumed   _feature_list clause _index_ref   = is_subsumed_list   clause
let find_subsumed _feature_list clause _index_ref   = find_subsumed_list clause
let find_subsumed_subst _ _ clause = find_subsumed_list_subst clause
let remove_clause   _ _ clause   =  remove_clause_list clause
*)

(*
let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption Debug!!!!!!!!!!!!!!\n"

let add_clause    = add_clause_debug
let is_subsumed   = is_subsumed_debug 
let find_subsumed = find_subsumed_debug	
let find_subsumed_subst = find_subsumed_subst_debug	
let remove_clause       =  remove_clause_debug
*)


    let add_clause    = add_clause_normal
    let is_subsumed   = is_subsumed_normal 
    let find_subsumed = find_subsumed_normal	

 end



(*--------------Currently Not Used, Replaced by Compressed version Above-------*)

(*--------------Based on Uncompressed Feature Index-------------------------*)
(* all functions defined exactly as in the compressed index *)
(*but here we use uncompressed module, (with the same interface as compressed) *)

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



(*--------------Forward Subsumption-------------------*)	  
	
    let is_subsumed_normal feature_list clause index_ref = 
     (* let feature_list = Feature.get_feature_list clause in *)
    
      let is_subsumed_by d = 
	if  not (Clause.get_bool_param Clause.is_dead d)
	then
	  try
	  let unif = Unif.subsumes d clause in 
	  Some ((d,unif))
	  with   
	  Unif.Subsumtion_failed -> 
	    (
	     (*out_str ("Clause to subume: "
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
	if  not (Clause.get_bool_param Clause.is_dead d)
	then
	  try
	    let unif = Unif.subsumes d clause in 
	    Some ((d,unif))
	  with   
	    Unif.Subsumtion_failed -> None
	else None
      in
      (match (list_findf f !debug_list) with 
      |Some(x) -> Some(x)
	    
      |None -> None
      )
    
(* Debug version *)	
    let is_subsumed_debug feature_list clause index_ref = 
      match (is_subsumed_normal feature_list clause index_ref) with 
      |Some(x) -> Some(x)
      |None -> 
	  (
	   match (is_subsumed_list clause) with 	  
           |Some((d,unif)) -> 
	       out_str ("\n Clause: "^(Clause.to_string clause)^"\n"
			^" Subsumed by "^(Clause.to_string d)^"\n"
			^"but not by a clause in index\n");
               failwith "is_subsumed_debug: subsumed by list but not by index"
	   |None -> None
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
(*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref = 
	match !elem_ref with
	|Elem(clause_list) -> 
            let (subsumed,rest) = get_subsumed clause clause_list in 
	    List.iter 	      
	      (Clause.set_bool_param false Clause.in_subsumption_index) subsumed;
	    (*(out_str
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
		(*out_str ("Remove empty leaf from VIndexM \n"
	          ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n"  ) *)
	      )
	    else 
	      (elem_ref:=Elem(rest))(* (if (subsumed != []) then
		  (out_str
		   ("Old clause list"
		   ^(Clause.clause_list_to_string clause_list)^"\n"
		   ^"New clause list "
		    ^(Clause.clause_list_to_string rest)^"\n");
		   elem_ref:= Elem(rest))
		   )	*)	
            );	  
	     subsumed
	|Empty_Elem -> [] 
      in
      VIndexM.findf_all_geq f feature_list index_ref
    


(*-----List version------------------*)
    let find_subsumed_list clause =
     let  (subsumed,rest) = get_subsumed clause !debug_list  in
     debug_list:= rest;
     subsumed

(*-----Debug version------------------*)
    let find_subsumed_debug feature_list clause index_ref = 
      let subsumed_from_index = 
	find_subsumed_normal feature_list clause index_ref in
      let (subsumed_debug,rest_debug) = get_subsumed clause !debug_list in
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
      |h::tl ->  
	  (try (* if needed can get unif here*)
	    let subs = Unif.subsumes clause h in
	    let (rest_subsumed, rest) = get_subsumed_subst clause tl in 
	    (((h,subs)::rest_subsumed), rest)
	  with 
	    Unif.Subsumtion_failed -> 
              let (rest_subsumed, rest) = get_subsumed_subst clause tl in 
	      (rest_subsumed, h::rest)
	  )
      |[] -> ([],[])

(* output: ((subsumed,subst) list *)
(* we need substitution for subs. resolution *)
let find_subsumed_subst index_ref feature_list clause  = 
      (* let feature_list = Feature.get_feature_list clause in *)
(*      let all_subsumed = ref []in*)
      let f followed_key_list elem_ref = 
	match !elem_ref with
	|Elem(clause_list) -> 
            let (subsumed,rest) = get_subsumed_subst clause clause_list in 
	    (*(out_str
	       (	
		 "Subsumer: "
		 ^(Clause.to_string clause)^"\n"
		 ^"Clauses in Leaf: "
		 ^(Clause.clause_list_to_string clause_list)^"\n"
		 ^"Subsumed: "
		 ^(Clause.clause_list_to_string subsumed)^"\n"));*)
	    List.iter 
	      (fun (c,_) ->
		(Clause.set_bool_param false Clause.in_subsumption_index c)) subsumed;
	    (if rest = [] 
	    then 
	      (VIndexM.remove (List.rev followed_key_list) index_ref
		(*out_str ("Remove empty leaf from VIndexM \n"
	          ^"removed path: "^(to_string_feat_list (List.rev followed_key_list))^"\n"  ) *)
	      )
	    else 
	      (elem_ref:=Elem(rest)
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
	|Empty_Elem -> []
      in
      VIndexM.findf_all_geq f feature_list index_ref



(*-----List version------------------*)
    let find_subsumed_list_subst clause =
      let  (subsumed,rest) = get_subsumed_subst clause !debug_list  in
      debug_list:= rest;
      subsumed

(*-----Debug version------------------*)
    let find_subsumed_subst_debug index_ref feature_list clause  = 
      let subsumed_from_index = 
	find_subsumed_subst index_ref feature_list clause  in
      let (subsumed_debug,rest_debug) = get_subsumed_subst clause !debug_list in
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
	  List.map (fun (c,_) -> c) subsumed_debug in
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
  Clause.set_bool_param false Clause.in_subsumption_index clause; 
  let elem_ref = (VIndexM.find feature_list !index_ref) in
  match !elem_ref with 
  |Elem(clause_list) -> 
      let new_list = 
	List.filter (fun c-> not (clause==c)) clause_list in      
      if new_list = [] 
      then 
	(VIndexM.remove feature_list index_ref)
      else 
	(elem_ref:=Elem(new_list))
  |Empty_Elem -> VIndexM.remove feature_list index_ref
    


(*---- List version ---------------*)

let remove_clause_list clause = 
  debug_list := (List.filter (fun c-> not (clause==c)) (!debug_list))

(*---- Debug version ---------------*)
let remove_clause_debug index_ref feature_list clause =
  remove_clause index_ref feature_list clause;
  remove_clause_list clause

(*-------------change debug/list/normal versions--------------------*)

(*
let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption List!!!!!!!!!!!!!!\n"

let add_clause    _feature_list clause _index_ref   = add_clause_list    clause
let is_subsumed   _feature_list clause _index_ref   = is_subsumed_list   clause
let find_subsumed _feature_list clause _index_ref   = find_subsumed_list clause
let find_subsumed_subst _ _ clause = find_subsumed_list_subst clause
let remove_clause   _ _ clause   =  remove_clause_list clause
*)


let () = out_str "\n !!!!!!!!!!!!!!!!!!Subsumption Debug!!!!!!!!!!!!!!\n"

let add_clause    = add_clause_debug
let is_subsumed   = is_subsumed_debug 
let find_subsumed = find_subsumed_debug	
let find_subsumed_subst = find_subsumed_subst_debug	
let remove_clause       =  remove_clause_debug


(*
    let add_clause    = add_clause_normal
    let is_subsumed   = is_subsumed_normal 
    let find_subsumed = find_subsumed_normal	
*)
end

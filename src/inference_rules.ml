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



open Lib
open Options
open Statistics

type clause  = Clause.clause
type term    = Term.term
type literal = Clause.literal
type term_db = TermDB.termDB
type clause_db = ClauseAssignDB.clauseDB
(*
type  statistics = 
    {num_of_dismatch_blockings : int;
     num_of_non_proper_inst    : int }
*)


(*
let num_of_dismatch_blockings = ref 0 
let num_of_non_proper_inst = ref 0
let num_of_duplicates = ref 0
*)


(*----------------Subset Subs. used in subsumption resolution ----------*)

(* we assume that to_subs_clause has defined length *)
(* and by_clause does not, but all lits a are in    *)

let rec strict_subset_subsume_lits by_lits to_lits = 
  match by_lits with 
  |h::tl -> 
     if  (List.exists (function l -> h == l) to_lits) 
     then strict_subset_subsume_lits tl to_lits
     else false
  |[] -> true 

let strict_subset_subsume by_clause to_clause = 
  let by_lits = Clause.get_literals by_clause in
  if (List.length by_lits) < (Clause.length to_clause)
  then 
    (let to_lits = Clause.get_literals to_clause in
    strict_subset_subsume_lits by_lits to_lits)
  else
    false

exception Main_subsumed_by of clause
(* literals l1 l2 are in c1 and c2 *)
let resolution c1 l1 compl_l1 c_list2 l2 term_db_ref = 
(*  let compl_l1 = Term.compl_lit l1 in*)
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let new_litlist1 = 
    Clause.find_all (fun lit -> not(l1 == lit)) c1 
    in 
  let f rest c2 = 
    check_disc_time_limit ();
    let new_litlist2 = 
      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
    let conclusion = Clause.normalise_blitlist_list 
	term_db_ref mgu [(1,new_litlist1);(2,new_litlist2)] in
    (* Clause.assign_resolution_history conclusion [c1;c2] [l1;l2]; *)
    Clause.assign_tstp_source_resolution conclusion [c1;c2] [l1;l2];
    Clause.assign_when_born [c1] [c2] conclusion;
    let min_conj_dist = Clause.get_min_conjecture_distance [c1;c2] in
    Clause.assign_conjecture_distance (min_conj_dist+1) conclusion;  
    (if !current_options.res_forward_subs_resolution 
    then
      if (strict_subset_subsume conclusion c1)
      then 
	(Clause.set_bool_param true Clause.is_dead c1;
	 Clause.set_bool_param true Clause.res_simplifying conclusion;
	 raise (Main_subsumed_by conclusion))
      else ()
    else ()      
    );
    (if !current_options.res_backward_subs_resolution
    then
      if (strict_subset_subsume conclusion c2)
      then 
	(Clause.set_bool_param true Clause.res_simplifying conclusion;
	 Clause.set_bool_param true Clause.is_dead c2)
      else ()
    else ());      
    conclusion::rest  in 
  List.fold_left f [] c_list2     


(* --------As resolution only in the conclusion we put only clauses which subsume*)
(* -----side clauses ---------*)
let subs_resolution c1 l1 compl_l1 c_list2 l2 term_db_ref = 
(*  let compl_l1 = Term.compl_lit l1 in*)
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let new_litlist1 = 
    Clause.find_all (fun lit -> not(l1 == lit)) c1 
    in 
  let f rest c2 = 
    let new_litlist2 = 
      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
    let conclusion = Clause.normalise_blitlist_list 
	term_db_ref mgu [(1,new_litlist1);(2,new_litlist2)] in
    (* Clause.assign_resolution_history conclusion [c1;c2] [l1;l2]; *)
    Clause.assign_tstp_source_resolution conclusion [c1;c2] [l1;l2];
    Clause.assign_when_born [c1] [c2] conclusion;
    let min_conj_dist = Clause.get_min_conjecture_distance [c1;c2] in
    Clause.assign_conjecture_distance (min_conj_dist+1) conclusion;
    (if !current_options.res_forward_subs_resolution  
    then
      if (strict_subset_subsume conclusion c1)
      then 
	(Clause.set_bool_param true Clause.is_dead c1;
	 Clause.set_bool_param true Clause.res_simplifying conclusion;
	 raise (Main_subsumed_by conclusion))
      else ()
    else ()      
    );
    let subsuming_clauses = 
      if !current_options.res_forward_subs_resolution
      then
	if (strict_subset_subsume conclusion c2)
	then 
	  (Clause.set_bool_param true Clause.is_dead c2;
	   Clause.set_bool_param true Clause.res_simplifying conclusion;
	   [conclusion])
	else []
      else []
    in      
    subsuming_clauses@rest  in 
  List.fold_left f [] c_list2     




(* factors and removes all  repeated l1's in the clause *)
let factoring c l1 l2 term_db_ref =
  if l1==l2 then 
   let new_litlist = 
      l1::(Clause.find_all (fun lit -> not(l1 == lit)) c) in
    let conclusion = Clause.create new_litlist in
    Clause.inherit_conj_dist c conclusion;
    (* Clause.assign_factoring_history conclusion c [l1;l2]; *)
    Clause.assign_tstp_source_factoring conclusion c [l1;l2];
    conclusion
  else    
    let mgu =  Unif.unify_bterms (1,l1) (1,l2) in
    let new_litlist = 
      Clause.find_all (fun lit -> not(l1 == lit)) c
    in 
    let conclusion = Clause.normalise_b_litlist term_db_ref mgu (1,new_litlist) in
    Clause.inherit_conj_dist c conclusion;
    Clause.assign_when_born [c] [] conclusion;
    (* Clause.assign_factoring_history conclusion c [l1;l2]; *)
    Clause.assign_tstp_source_factoring conclusion c [l1;l2];
    conclusion



(* could be more efficient but messier

(* literals l1 l2 are already CUT  from  c1 and c2 *)
   
   let resolution  c1 l1 c2 l2 term_db_ref = 
   let compl_l1 = Term.compl_lit l1 in
   let mgu = Unif.unify_bterms (1,l1) (2,l2) in
   Clause.normalise_bclause_list  
   term_db_ref mgu [(1,c1);(2,c2)]

(* literals l1 l2 are already CUT from  c *)

let factoring c l1 l2 term_db_ref =
  let mgu =  Unif.unify_bterms (1,l1) (1,l2) in
  Clause.normalise_bclause (1,c) mgu term_db_ref

*)


(*----------VERSION WITHOUT DISM VEC INDEX ---------*)
(*--new version: constr checked on normalized substitutions****)


(*

let is_not_redundant_inst_norm subst_norm clause =
(*   out_str_debug 
    ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
    begin
      try
	let dismatching = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
       ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
       ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
	if (Dismatching.check_constr_norm_list subst_norm dismatching)
      (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
	then
    ( (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
      let new_constr = Dismatching.create_constr_norm subst_norm in
      Clause.assign_dismatching 
	(Dismatching.add_constr dismatching new_constr) clause;
      	(*(Dismatching.add_constr_feature_list dismatching new_constr);*)
      true)
	else
	  ((*out_str_debug "Constr. is NOT Satisfied \n";*)
       incr_int_stat 1 inst_num_of_dismatching_blockings;
	   false) 
      with Clause.Dismatching_undef -> 
	(let new_dismatching =
	  (Dismatching.create_constr_list ()) in
	(* let new_dismatching =
	   (Dismatching.create_constr_feature_list ()) in*)
	let new_constr = Dismatching.create_constr_norm subst_norm in
	Clause.assign_dismatching 
      (Dismatching.add_constr new_dismatching new_constr) clause;
  (* (Dismatching.add_constr_feature_list new_dismatching new_constr);   
   Clause.assign_dismatching new_dismatching clause;*)
  (*out_str_debug "Constr. is empty\n";*)
	true)
    end
(*out_str_debug "Constr. is empty";*)  
(*  else false*)


*)



(*
let is_not_redundant_dism constr clause =
(*   out_str_debug 
     ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
   begin
      try
	let constr_set = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
      ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
      ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
	if (Dismatching.check_constr_set constr_set constr)
	    (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
	then
	  (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
	  true 
	else 
	  (incr_int_stat 1 inst_num_of_dismatching_blockings;
	   false)
      with 
	Clause.Dismatching_undef -> 
	  true
    end


let add_dism_constr constr clause = 
   begin
      let constr_set =
	try
	  Clause.get_dismatching clause 
	with 
	  Clause.Dismatching_undef -> 
	    (Dismatching.create_constr_set ())
      in
      Clause.assign_dismatching 
	(Dismatching.add_constr constr_set constr) clause
   end
    
*)

(*
let is_not_redundant_inst_norm subst_norm clause =
  if (not !current_options.inst_dismatching) && (not !current_options.sat_out_model)
  then true
  else
    let constr = Dismatching.create_constr subst_norm in
    if (is_not_redundant_dism constr clause) 
    then 
      (add_dism_constr constr clause;
       true 
      )
    else 
      false
      
*)
    

let get_dismatching_create cl = 
  try
    Clause.get_dismatching cl 
  with 
    Clause.Dismatching_undef -> 
      (Dismatching.create_constr_set ())


let add_to_dism_constr subst_norm clause = 
  let old_constr_set = get_dismatching_create clause in
  let new_constr_set = Dismatching.add_constr old_constr_set subst_norm in
  Clause.assign_dismatching new_constr_set clause



let is_not_redundant_inst_norm subst_norm clause =
  let start_time = Unix.gettimeofday () in
  let res =
(* if not !current_options.sat_out_model=Model_None then we need to creat dismatching constriants     *)
(* for the model representation, they are checked only when !current_options.inst_dismatching is true *)
    if (not !current_options.inst_dismatching) && (!current_options.sat_out_model=Model_None)
    then true
    else
    begin     
      let old_constr_set = get_dismatching_create clause in
      if (!current_options.inst_dismatching) 
      then      
	try 
	  let new_constr_set = Dismatching.check_and_add old_constr_set subst_norm in
	  Clause.assign_dismatching new_constr_set clause;
	  true
	with
	  Dismatching.Constr_Not_Sat ->
	    (incr_int_stat 1 inst_num_of_dismatching_blockings;
	     false)
      else (* !current_options.sat_out_model=true and !current_options.inst_dismatching = false *)
	(* We need to add constriant for model representation, but do not check it *)
	let new_constr_set = Dismatching.add_constr old_constr_set subst_norm in
	Clause.assign_dismatching new_constr_set clause;
	true
    end
  in
  let end_time   = Unix.gettimeofday () in 
  let run_time = (end_time -. start_time) in
  add_float_stat run_time Statistics.inst_dismatching_checking_time;
  res
    

let dismatching_string clause =   
  try 
   "["^(Dismatching.to_string_constr_set (Clause.get_dismatching clause))^"]"
  with
    Clause.Dismatching_undef -> "[]"


exception Main_concl_redundant

(* assume that we already added clause to db *)

let assign_param_clause parent parents_side conj_dist clause = 
(*  Clause.assign_when_born ((Clause.when_born parent)+1) clause;*)
  Clause.assign_when_born [parent] parents_side clause;
  Clause.assign_activity ((Clause.get_activity parent)+1) parent;
  Clause.add_child parent clause;
  Clause.assign_conjecture_distance conj_dist clause;
  (* Clause.assign_instantiation_history clause parent parents_side *)
  Clause.assign_tstp_source_instantiation clause parent parents_side 
    

  
(*---------------------------------------------------------------------------*)  
(*------instantiation first check duplicates then dismatching constraints----*)


let instantiation_norm_dc 
    term_db_ref clause_db_ref c1 l1 compl_l1 c_list2 l2  =
(* if mgu is proper of c1 and the conclusion is redundant then all inference *)
(* is redundant; similar *)
(* if mgu is proper of list2 and *)
(*  all instanses of list2 are redundant then the ineference is redundant  *)
(* we use  list2_concl_redundant is false if at least one concl in list2  *)
(* is not redundant  *)
(* we can not *)
(* put conl of c1 in to ClauseAssignDB immediately, but only at the end  *)
  let list2_concl_redundant = ref true in

(*  out_str "Unif before\n";*)
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
(*  out_str "Unif after\n";*)
(*debug*)
(*  out_str ("Main Clause:"^(Clause.to_string c1)^"\n"
             	   ^"Constr: "^(dismatching_string c1)^"\n" 
		   ^"Sel Lit: "^(Term.to_string l1)^"\n"
		   ^"Conj Dist: "^(string_of_int (Clause.get_conjecture_distance c1))^"\n"); 
*)
(*  let conjecture_distance_c1 = (Clause.get_conjecture_distance c1) in  *)
  let min_conj_dist = Clause.get_min_conjecture_distance (c1::c_list2) in
  let main_old_dismatching_c1 = get_dismatching_create c1
  in
(*  out_str ("Min Conj Dist: "^(string_of_int min_conj_dist)^"\n");*)
(*  inference is not needed for eq_ax with input_under_eq = false  *) 
  try    
  let conc1 = 
       if (SubstBound.is_proper_instantiator mgu 1) 
	then  
	  let (inst_clause,subst_norm) = 
	    (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 c1)
	  in
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then 
          (
(* adding dism. constraint is essential for correct model representation!*)
	   add_to_dism_constr subst_norm c1;   
           incr_int_stat 1 inst_num_of_duplicates;
(*          out_str_debug ("Clause is already In DB: "
            ^(Clause.to_string inst_clause)^"\n");*)
             raise Main_concl_redundant)
	  else
	    if (is_not_redundant_inst_norm subst_norm c1) 
(*(is_not_redundant_feature subst_norm c1)*)
             then 
(*	       let added_clause = 
		(ClauseAssignDB.add_ref inst_clause clause_db_ref) in
	      let new_conj_dist = min_conj_dist +1
		  (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) in
	      assign_param_clause c1 new_conj_dist  added_clause;
	      [added_clause] *)

              Some ((inst_clause, subst_norm))
	    else 
	      (raise Main_concl_redundant)
	else
	 (
	  incr_int_stat 1 inst_num_of_non_proper_insts;
(*       out_str_debug ("Non-proper Inst Main\n");*)
	  None)
    in    
    let conc2 =
(* if l1 in .inst_in_unif_index then all instantiations with the side clauses *)
(* are already beeing made since all inference between active are made        *)
      if ((not (Term.get_fun_bool_param Term.inst_in_unif_index l1))&& 
	  (SubstBound.is_proper_instantiator mgu 2)) 
      then    
	let f rest clause =
(*debug*)
(*	out_str_debug  ("Side Clause:"^(Clause.to_string clause)^"\n"
			^"Constr: "^(dismatching_string clause)^"\n" 
   			^"Sel Lit: "^(Term.to_string l2)^"\n");*)
	  let (inst_clause,subst_norm) = 
	    Clause.apply_bsubst_norm_subst term_db_ref mgu 2 clause 
	  in
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then 
	    (
(* adding dism. constraint is essential for correct model representation!*)
	     add_to_dism_constr subst_norm clause;   
	     incr_int_stat 1 inst_num_of_duplicates;

(*	     out_str_debug ("Side Clause is already In DB, prop inst: \n"
			    ^"Old:-----------------------\n "
			    ^(Clause.to_string clause)^"\n"
                            ^(Clause.to_string inst_clause)^"\n"
			    );
*)
(*debug*)   
(*	     let in_db  = ClauseAssignDB.find inst_clause !clause_db_ref in
	     out_str (" Inst Clause in Active: "
		      ^(string_of_bool (Clause.get_bool_param Clause.in_active in_db ))
		      ^ " In pass_q1: "
 		      ^(string_of_bool (Clause.get_bool_param Clause.inst_pass_queue1 in_db ))
		      ^ " In pass_q2: "
		      ^(string_of_bool (Clause.get_bool_param Clause.inst_pass_queue2 in_db ))
		      ^" Is dead: "
		      ^(string_of_bool (Clause.get_bool_param Clause.is_dead in_db ))^"\n"^"---------------------------\n");

	     (if (in_db == c1) then 
	       list2_concl_redundant := false);
*)
		rest)
	  else
	    if (is_not_redundant_inst_norm subst_norm clause)
(*(is_not_redundant_feature subst_norm clause)*)
	    then 
	      (list2_concl_redundant := false;
	       let added_clause = 
	      ClauseAssignDB.add_ref inst_clause clause_db_ref in
	   (* let new_conj_dist = 
	      ( ((Clause.get_conjecture_distance clause) + 
		  conjecture_distance_c1) lsr 2)+1 in*)
	      let new_conj_dist = (Clause.get_min_conjecture_distance [clause;c1])+1 in
	      assign_param_clause clause [c1] new_conj_dist added_clause;
	      added_clause::rest)
	  else 
	    (
(* should be removed*)
(*	     list2_concl_redundant := false;*)
(*	     out_str_debug ("Dismatching \n");*)
	     rest)	  
      in
      List.fold_left f [] c_list2
    else
      (
       incr_int_stat 1 inst_num_of_non_proper_insts;
       list2_concl_redundant := false;
(* debug*)   
(*       (if (Term.get_fun_bool_param Term.inst_in_unif_index l1) 
       then 	 
	 try  
	   let ind_elem = DiscrTreeM.find sel_lit !unif_ind_debug in ()
	 with
	   Not_found -> 
	     out_str ("Side is Not in Unif Index: "^(Term.to_string l1)^"\n")
       else
	 () (* out_str_debug ("Non-proper Inst Side\n")*)
       );*)
       [])
    in 
(*   let concl_list = conc1@conc2*)
  let concl_list = 
    if  (!list2_concl_redundant) 
     then
      (
   (*    out_str "Side Conclusions are all redundant !\n "; *)
       Clause.assign_dismatching main_old_dismatching_c1 c1;
       [])
      else 
      (match conc1 with 
      |Some ((conc1_cl, conc1_subst_norm)) ->
        (* note that here conc1_subst_norm is always proper *)
	    (if (ClauseAssignDB.mem conc1_cl !clause_db_ref)
            then 
            ((*out_str "inference_rules: conc1 inst is conc2 inst\n";*)
(* adding dism. constraint is essential for correct model representation!*)
	     add_to_dism_constr  conc1_subst_norm c1;   
	     incr_int_stat 1 inst_num_of_duplicates;
             conc2)
            else   
              ( let added_conc1 = 
	      (ClauseAssignDB.add_ref conc1_cl clause_db_ref) in
	      let new_conj_dist = min_conj_dist +1
		  (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) in
	      assign_param_clause c1 c_list2 new_conj_dist  added_conc1;
       	      added_conc1::conc2)
            ) 
           (* in this case conc1 is empty*)
	|None -> conc2
	)

    in
(*   out_str
      ("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
       ^"------------------------------------------------\n");
*)
    concl_list
  with 
    Main_concl_redundant -> 
(*      out_str_debug 
	(" ---------Main_concl_redundant ----------\n");*)
      []	      

(*-------------------------------------------------------------------*)
(* instantiation first check dismatching constraints then duplicates *)

let instantiation_norm_cd term_db_ref clause_db_ref c1 l1 compl_l1 c_list2 l2 =
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
(*debug*)
  (*out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
		  ^"Constr: "^(dismatching_string c1)^"\n" 
        	  ^"Sel Lit: "^(Term.to_string l1)^"\n");  *)
(*  let conjecture_distance_c1 = (Clause.get_conjecture_distance c1) in*)
  let min_conj_dist = Clause.get_min_conjecture_distance (c1::c_list2) in
 try 
    let conc1 = 
      if (SubstBound.is_proper_instantiator mgu 1) 
      then  
	let (inst_clause,subst_norm) = 
	  (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 c1)
	in
	if (is_not_redundant_inst_norm subst_norm c1)
	then 
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then 
	    (
	     incr_int_stat 1 inst_num_of_duplicates;
	     (*out_str_debug ("Clause is already In DB: "
	       ^(Clause.to_string inst_clause)^"\n");*)
	     raise Main_concl_redundant)
	  else
	    let added_clause = 
	      ClauseAssignDB.add_ref inst_clause clause_db_ref in
	    let new_conj_dist = min_conj_dist +1
            (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) in
	    assign_param_clause c1 c_list2 new_conj_dist  added_clause;	    
	    [added_clause]	 
	else 
	  (
	   raise Main_concl_redundant)
      else
	(
	 incr_int_stat 1 inst_num_of_non_proper_insts;
	 (*out_str_debug ("Non-proper Inst Main\n");*)
	 [])
    in    
    let conc2 =
    if (SubstBound.is_proper_instantiator mgu 2) then    
      let f rest clause =
(*debug*)
	(*out_str_debug  ("Side Clause:"^(Clause.to_string clause)^"\n"
			^"Constr: "^(dismatching_string clause)^"\n" 
			^"Sel Lit: "^(Term.to_string l2)^"\n"); *)
	let (inst_clause,subst_norm) = 
	  Clause.apply_bsubst_norm_subst term_db_ref mgu 2 clause 
	in
	if (is_not_redundant_inst_norm subst_norm clause)
	then 
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then (
	    incr_int_stat 1 inst_num_of_duplicates;
		(* out_str_debug ("Clause is already In DB: "
		   ^(Clause.to_string inst_clause)^"\n");*)
		rest)
	  else
	    let added_clause = 
	      ClauseAssignDB.add_ref inst_clause clause_db_ref in
	    let new_conj_dist = (Clause.get_min_conjecture_distance [clause;c1])+1 in
	    assign_param_clause clause [c1] new_conj_dist added_clause;
	    added_clause::rest	
	else 
	  (
	   rest)	  
      in
      List.fold_left f [] c_list2
    else
      (
       incr_int_stat 1 inst_num_of_non_proper_insts;
       (*out_str_debug ("Non-proper Inst Side\n");*)
       [])
    in 
    let concl_list = conc1@conc2 in
    (*out_str_debug 
      ("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
      ^"------------------------------------------------\n");*)
    concl_list
  with 
    Main_concl_redundant -> 
(*      out_str_debug 
	(" ---------Main_concl_redundant ----------\n");*)
      []	      
	


let instantiation_norm = 
  instantiation_norm_dc
(* instantiation first check dismatching constraints then duplicates *)
(* instantiation_norm_cd *)


(*--------Resolution with dismatching on unit clauses-----------*)
(*only for hyper resolution with Horn clauses*)

let resolution_dismatch  
    dismatch_flag forward_subs_resolution_flag  backward_subs_resolution_flag 
    c1 l1 compl_l1 c_list2 l2 term_db_ref = 
(*  let compl_l1 = Term.compl_lit l1 in*)

(* out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
		  ^"Constr: "^(dismatching_string c1)^"\n" 
        	  ^"Sel Lit: "^(Term.to_string l1)^"\n");  *)

  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in   
  let (inst_clause,subst_norm) = 
    (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 c1)
  in
  if (not dismatch_flag) || 
     ((Clause.length c1) <= 1) ||
    (is_not_redundant_inst_norm subst_norm c1) 
  then    
    begin
      let new_litlist1 = 
	Clause.find_all (fun lit -> not(l1 == lit)) c1 
      in
      let f rest c2 = 
(*	out_str_debug ("Side Clause:"^(Clause.to_string c2)^"\n"
		       ^"Constr: "^(dismatching_string c2)^"\n" 
        	       ^"Sel Lit: "^(Term.to_string l2)^"\n");  
*)
	let (inst_clause2,subst_norm2) = 
	  (Clause.apply_bsubst_norm_subst term_db_ref mgu 2 c2)
	in  
	if (not dismatch_flag) || (Clause.length c2) <=1 ||
	(is_not_redundant_inst_norm subst_norm2 c2) 
	then
	  begin
	    let new_litlist2 = 
	      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
	    let conclusion = Clause.normalise_blitlist_list 
		term_db_ref mgu [(1,new_litlist1);(2,new_litlist2)] in
	    (if forward_subs_resolution_flag 
	    then
	      if (strict_subset_subsume conclusion c1)
	      then 
		(Clause.set_bool_param true Clause.is_dead c1;
		 raise (Main_subsumed_by conclusion))
	      else ()
	    else ()      
	    );
	    (if backward_subs_resolution_flag 
	    then
	      if (strict_subset_subsume conclusion c2)
	      then 
		(Clause.set_bool_param true Clause.is_dead c2)
	      else ()
	    else ());      
	    (* Clause.assign_resolution_history conclusion [c1;c2] [l1;l2]; *)
	    Clause.assign_tstp_source_resolution conclusion [c1;c2] [l1;l2];
	    Clause.assign_when_born [c1] [c2] conclusion;
	    conclusion::rest
	  end  
	else (* dismatch flag and c2 is redundant *)
	  (
	 (*  out_str "Dismatch unsat for Side Clause\n";*)
	   rest)	
      in 
      List.fold_left f [] c_list2 
    end    
  else (* dismatch flag and c1 is redundant *)
    (
	  (* out_str "Dismatch unsat for Main Clause\n";*)
     [])




(*------------------Commented--------------------------*)
(*


(*------------- Instantiation ------------------*)

(* Works but slow....*)
(*
(*--------------Feature Index Version--------------------*)
let is_not_redundant_feature subst_norm clause =
(*   out_str_debug 
    ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
  begin
   try
    let dismatching = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
       ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
       ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
    if (Dismatching.check_constr_feature_list subst_norm dismatching)
      (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
    then
    ( (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
      let new_constr =  Dismatching.create_constr_norm subst_norm in
      Dismatching.add_constr_feature_list dismatching new_constr;
  (*    Clause.assign_dismatching 
	( ) clause;*)
      	(*(Dismatching.add_constr_feature_list dismatching new_constr);*)
      true)
    else
      ((*out_str_debug "Constr. is NOT Satisfied \n";*)
  incr_int_stat 1 inst_num_of_dismatching_blockings;
       false) 
  with Clause.Dismatching_undef -> 
  (let new_dismatching =
      (Dismatching.create_constr_feature_list ()) in
  (* let new_dismatching =
     (Dismatching.create_constr_feature_list ()) in*)
   let new_constr = Dismatching.create_constr_norm subst_norm in
   Dismatching.add_constr_feature_list new_dismatching new_constr; 
   Clause.assign_dismatching new_dismatching clause;
  (* (Dismatching.add_constr_feature_list new_dismatching new_constr);   
   Clause.assign_dismatching new_dismatching clause;*)
  (*out_str_debug "Constr. is empty\n";*)
    true)
  end
*)


(****************old version, not correct*********)
(*
let is_not_redundant_inst bound bsubst clause = 
(*  if (SubstBound.is_proper_instantiator bsubst bound)     *)
(*  then proper inst checked first because applies to many clauses with the same lit*)
(*  out_str_debug  "\n-------Constr Check-------\n";*)
  try
    let dismatching = Clause.get_dismatching clause in
    out_str_debug (
    "Inst Clause: "^(Clause.to_string clause)
    ^"  Bound: "^(string_of_int bound)^"\n"      
    ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
    ^"Subs_to_check: "^(SubstBound.to_string bsubst)^"\n"); 
    if (Dismatching.check_constr_list bound bsubst dismatching)
    then
      (out_str_debug "Constr. is Satisfied \n";
       true)
    else 
      (out_str_debug "Constr. is NOT Satisfied \n";
       false) 
  with Clause.Dismatching_undef -> 
    (*out_str_debug "Constr. is empty";*) true 
(*  else false*)

(* instantiates adding dismatching constr to the parent--clause *)
let instantiate_clause term_db_ref bound bsubst clause =
  let concl_clause = Clause.apply_bsubst term_db_ref bsubst (bound,clause) in
  let new_constr = Dismatching.create_constr term_db_ref bound  bsubst in
  try    
    let dismatching = Clause.get_dismatching clause in
    Clause.assign_dismatching (Dismatching.add_constr dismatching new_constr) clause;
    concl_clause
  with 
    Clause.Dismatching_undef -> 
      let empty_dism = Dismatching.create_constr_list () in
      let new_dism = Dismatching.add_constr empty_dism new_constr in
      Clause.assign_dismatching new_dism clause;
      concl_clause

(* {num_of_dismatch_blockings = ref 0;*)
(*     num_of_non_proper_inst = ref 0}*)

let instantiation term_db_ref c1 l1 compl_l1 c_list2 l2 =
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let conc1 = 
    if (SubstBound.is_proper_instantiator mgu 1) 
    then  
      if (is_not_redundant_inst 1 mgu c1)
      then 
	[(instantiate_clause term_db_ref 1 mgu c1)]
      else 
	(
	 [])
    else
      (
       incr_int_stat 1 inst_num_of_non_proper_insts;
       [])
  in    
  let conc2 =
    if (SubstBound.is_proper_instantiator mgu 2) then    
      let f rest clause = 
	if (is_not_redundant_inst 2 mgu clause)
	then 
	  (instantiate_clause term_db_ref 2 mgu clause)::rest
	else 
	  (
	   rest)
      in
      List.fold_left f [] c_list2
    else
      (
       incr_int_stat 1 inst_num_of_non_proper_insts;
       [])
  in conc1@conc2

*)
(*******************old version end*************)



(*
(************** Eq Axioms Special treatment ******************)
(* yet doesnot work..... see fof_eq_reduced_19May_bugs_all.txt for ex.*)
(* instantiation first check duplicates then dismatching constraints*)
let instantiation_norm_dc dismatch_switch term_db_ref clause_db_ref c1 l1 compl_l1 c_list2 l2 =
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
(*debug*)
(*  out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
		  ^"Constr: "^(dismatching_string c1)^"\n" 
		  ^"Sel Lit: "^(Term.to_string l1)^"\n"
		 ^"Conj Dist: "^(string_of_int (Clause.get_conjecture_distance c1))^"\n"); *)
  let conjecture_distance_c1 = (Clause.get_conjecture_distance c1) in    
  let min_conj_dist = Clause.get_min_conjecture_distance (c1::c_list2) in
  let c1_is_eq = Clause.get_bool_param Clause.eq_axiom c1 in
  let c1_is_input_under_eq = Clause.get_bool_param Clause.input_under_eq c1 in
  let c_list2_has_eq = 
    (List.exists (Clause.get_bool_param Clause.eq_axiom) c_list2) in
  let c_list2_has_input_under_eq = 
    (List.exists (Clause.get_bool_param Clause.input_under_eq) c_list2) in
  let c_list2_all_eq_ax = 
    (List.for_all (Clause.get_bool_param Clause.eq_axiom) c_list2) in

  (* inference is not needed for eq_ax with input_under_eq = false *) 
  try    
    let conc1 = 
      if ((c1_is_eq & (not c_list2_has_input_under_eq)) 
	|| ((not c1_is_input_under_eq ) & (c_list2_all_eq_ax)))
      then raise Main_concl_redundant
      else
	if (SubstBound.is_proper_instantiator mgu 1) 
	then  
	  let (inst_clause,subst_norm) = 
	    (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 c1)
	  in
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then 
	    (
             incr_int_stat 1 inst_num_of_duplicates;

(*	   out_str_debug ("Clause is already In DB: "
  ^(Clause.to_string inst_clause)^"\n");*)
(*debug*) 
	     let cl_in_db = ClauseAssignDB.find inst_clause !clause_db_ref in
	     (if (((not (Clause.get_bool_param Clause.input_under_eq cl_in_db))
		 & c1_is_input_under_eq)
		|| 
		  ((not (Clause.get_bool_param Clause.eq_axiom cl_in_db))
		     & c1_is_eq)) 
	     then 
	       out_str "\n Inf_Rules: Cluase in DB weaker than not added!\n"
	     else());
(*end debug*)
 	     raise Main_concl_redundant)
	  else
	    if  (is_not_redundant_inst_norm subst_norm c1)
	    then 
	      let added_clause = 
		(ClauseAssignDB.add_ref inst_clause clause_db_ref) in
	      let new_conj_dist = min_conj_dist +1
		  (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) in
	      assign_param_clause c1 new_conj_dist  added_clause;
	      (if (c1_is_eq || (c1_is_input_under_eq & c_list2_has_eq))
	      then 
		(Clause.set_bool_param true Clause.input_under_eq added_clause;
		 Clause.inherit_bool_param Clause.eq_axiom c1 added_clause)    
	      else  ()); (* by default added_clause has false param*)		
	      [added_clause]
	    else 
	      (
	       raise Main_concl_redundant)
	else
	  (
  incr_int_stat 1 inst_num_of_non_proper_insts;

(*       out_str_debug ("Non-proper Inst Main\n");*)
	 [])
    in    
    let conc2 =
    if ((not (Term.get_fun_bool_param Term.inst_in_unif_index l1))& 
      (SubstBound.is_proper_instantiator mgu 2)) then    
      let f rest clause =
(*debug*)
(*	out_str_debug  ("Side Clause:"^(Clause.to_string clause)^"\n"
			^"Constr: "^(dismatching_string clause)^"\n" 
   			^"Sel Lit: "^(Term.to_string l2)^"\n");*)
	let clause_is_eq =  (Clause.get_bool_param Clause.eq_axiom clause) in
	if (clause_is_eq & (not c1_is_input_under_eq)) 
	then rest 
	else
	  let (inst_clause,subst_norm) = 
	    Clause.apply_bsubst_norm_subst term_db_ref mgu 2 clause 
	  in
	  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
	  then (
                incr_int_stat 1 inst_num_of_duplicates;
(*	      out_str_debug ("Clause is already In DB: "
  ^(Clause.to_string inst_clause)^"\n");*)
(*debug*)
		let cl_in_db = ClauseAssignDB.find inst_clause !clause_db_ref in
		(if (((not (Clause.get_bool_param Clause.input_under_eq cl_in_db))
		       &
		     (Clause.get_bool_param Clause.input_under_eq clause))
		   || 
		     ((not (Clause.get_bool_param Clause.eq_axiom cl_in_db))
			& (Clause.get_bool_param Clause.eq_axiom clause )))
	     then 
	       out_str "\n Inf_Rules: Cluase in DB weaker than not added!\n"
	     else());
(*end debug*)
		rest)
	  else
	    if  (is_not_redundant_inst_norm subst_norm clause)
	    then 
	      (let added_clause = 
	      ClauseAssignDB.add_ref inst_clause clause_db_ref in
	   (* let new_conj_dist = 
	      ( ((Clause.get_conjecture_distance clause) + 
		  conjecture_distance_c1) lsr 2)+1 in*)
	      let new_conj_dist = (Clause.get_min_conjecture_distance [clause;c1])+1 in
	      assign_param_clause clause new_conj_dist added_clause;
	      (if 
		(
		 (clause_is_eq (*&
		  (c1_is_eq || c1_is_input_under_eq)*))
	       ||
		 ((Clause.get_bool_param Clause.input_under_eq clause) &
		  c1_is_eq))
	      then 
		(Clause.set_bool_param true Clause.input_under_eq added_clause;
		 Clause.inherit_bool_param Clause.eq_axiom clause added_clause)    
	      else  ());
	      added_clause::rest)
	  else 
	    (

(*	     out_str_debug ("Dismatching \n");*)
	     rest)	  
      in
      List.fold_left f [] c_list2
    else
      (
      incr_int_stat 1 inst_num_of_non_proper_insts;
(* debug*)   
     (*  (if (Term.get_fun_bool_param Term.inst_in_unif_index l1) 
       then 	 
	 out_str ("Side is In Unif Index: "^(Term.to_string l1)^"\n")
       else
	 out_str_debug ("Non-proper Inst Side\n")
       );*)
       [])
    in 
    let concl_list = conc1@conc2 in
(*   out_str_debug 
      ("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
      ^"------------------------------------------------\n");*)
    concl_list
  with 
    Main_concl_redundant -> 
(*      out_str_debug 
	(" ---------Main_concl_redundant ----------\n");*)
      []	      


(*------------- End Eq Axioms Special treatment comment----------------*)
*)



*)


(*------------------End Commented--------------------------*)

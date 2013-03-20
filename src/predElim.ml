open Lib
open Options
open Statistics

(* contributors: Moshe Emmer, Ilan Tchernowitz *)


type clause = Clause.clause
(* type literal = Clause.literal *)
(* type var = Var.var *)
(* type lit = Term.literal *)

(*type symbol = Symbol.symbol 

module Key = 
  struct
    type t      = symbol
    let equal   = (==)  
    let hash    = get_fast_key 
    let compare = compare_fast_key
  end
*)
module SymbMap = Symbol.Map

module Set = Clause.Set

module type Feature =
sig
        type t
        val compare : t -> t -> int
(* val get_feature_list : clause -> t list *)
end

module SubsumptionIndexM = SubsumptionIndex.SCFVIndex

let get_feature_list cl = SubsumptionIndexM.get_feature_list cl

let subsumption_index_ref = ref (SubsumptionIndexM.create ())

let term_db_ref = Parser_types.term_db_ref

let clause_db_ref = ref (ClauseAssignDB.create_name "predElim_DB")
let () = assign_fun_stat 
    (fun () -> ClauseAssignDB.size !clause_db_ref) res_num_of_clauses

let ss_r_index_ref = ref (SubsetSubsume.create ())
let ss_f_index_ref = ref (SubsetSubsume.create ())


exception Eliminated
exception Empty_Clause of clause

(* Get Var Count: *)
(* 1) Generate mapping between var and the number of its containing clauses *)
(* 2) Generate mapping between var and the number of containing clauses with more than one instantiation *)

(* Main loop *)
(* Find all clauses that hold the variable in positive polarity *)
(* Find all clauses that hold the variable in negative polarity *)
(* Find resolution and apply on N P *)


(*-------------------------------------------------------*)
(*----------------- Predicate mapping -------------------*)
type pos_neg_cl_lists =
	{ pos_cl_list   : clause list;
          neg_cl_list   : clause list;
	  multi_occ_cnt : int }


let rec add_clause_pred_map cl pred_map =
	let f curr_pred_map lit =
		let atom = Term.get_atom lit in
		let is_neg = Term.is_neg_lit lit in
		let pred_symb = Term.get_top_symb atom in
		let pred_list = Clause.find_all (fun l_pred -> ((Term.get_top_symb (Term.get_atom l_pred)) == pred_symb)) cl in
		let curr_occ = List.length pred_list in
		let curr_cnt = 
			if (curr_occ > 1) then
				1
			else
			    	0;
		in
		try
			let old_pos_neg = SymbMap.find pred_symb curr_pred_map in
			let new_pos_neg =
				if is_neg then
					{ old_pos_neg with
						neg_cl_list = cl:: (old_pos_neg.neg_cl_list);
						multi_occ_cnt = old_pos_neg.multi_occ_cnt + curr_cnt
					}
				else
					{ old_pos_neg with
						pos_cl_list = cl:: (old_pos_neg.pos_cl_list);
						multi_occ_cnt = old_pos_neg.multi_occ_cnt + curr_cnt
					}
			in
			SymbMap.add pred_symb new_pos_neg curr_pred_map
		with
			Not_found ->
				let new_pos_neg =
					if is_neg then
						{ pos_cl_list = [];
						  neg_cl_list = [cl];
						  multi_occ_cnt = curr_cnt;	  
						}
					else
						{ pos_cl_list = [cl];
						  neg_cl_list = [];
						  multi_occ_cnt = curr_cnt;
						}
				in
				SymbMap.add pred_symb new_pos_neg curr_pred_map
	in
	let lit_list = Clause.get_literals cl in
	List.fold_left f pred_map lit_list

let rec remove_clause_pred_map pred_map cl =
	let f curr_pred_map lit =
		let atom = Term.get_atom lit in
		let is_neg = Term.is_neg_lit lit in
		let pred_symb = Term.get_top_symb atom in
		let pred_list = Clause.find_all (fun l_pred -> ((Term.get_top_symb (Term.get_atom l_pred)) == pred_symb)) cl in
		let curr_occ = List.length pred_list in
		let curr_cnt = 
			if (curr_occ > 1) then
				1
			else
			    	0;
		in
		let same_clause c2 = Clause.equal cl c2 in
		try
			let old_pos_neg = SymbMap.find pred_symb curr_pred_map in
			let new_pos_neg =
				if is_neg then
					{ old_pos_neg with
						neg_cl_list = snd (List.partition same_clause old_pos_neg.neg_cl_list);
						multi_occ_cnt = old_pos_neg.multi_occ_cnt - curr_cnt
					}
				else
					{ old_pos_neg with
						pos_cl_list = snd (List.partition same_clause old_pos_neg.pos_cl_list);
						multi_occ_cnt = old_pos_neg.multi_occ_cnt - curr_cnt
					}
			in
			SymbMap.add pred_symb new_pos_neg curr_pred_map
		with
			Not_found ->
				SymbMap.empty
	in
	let lit_list = Clause.get_literals cl in
	List.fold_left f pred_map lit_list

let rec create_pred_map_cl_list clause_set pred_map_ref =
	Set.fold add_clause_pred_map clause_set !pred_map_ref


(*-------------------------------------------------------*)
(*------------------ Simplifications --------------------*)

(*------- Tautology deletion -------*)
(* ref: discount.ml *)
let rec coml_in_list lit_list =
  match lit_list with 
  |l::tl ->   
      let exists = List.exists (Term.is_complementary l) tl in
      if exists then exists
      else coml_in_list tl 
  |[] -> false

let is_tautology cl = 
  let lit_list = Clause.get_literals cl in
  coml_in_list lit_list

let check_empty_clause cl = 
  if (Clause.is_empty_clause cl) 
  then
    raise (Empty_Clause cl)
  else ()


(*------- Subsumption -------*)
let is_subset_subsumed cl index_ref = 
  try 
    let by_clause = SubsetSubsume.is_subsumed cl  !(index_ref) in
    Clause.set_bool_param true Clause.res_simplifying by_clause;
    true
  with 
    Not_found ->
      false

(*-------------------------------------------------------*)
(*---------------- Forward Simplification ---------------*)
let simplify_forward cl index_ref pred_map_ref = 
  if (is_tautology cl) 
  then 
    ((*out_str_debug 
       ("Simplified tautology: "
        ^(Clause.to_string cl));*)        
      incr_int_stat 1  res_tautology_del;
      remove_clause_pred_map !pred_map_ref cl;
     raise Eliminated)
  else
    if (is_subset_subsumed cl index_ref) 
    then
      ((* out_str
         ("Subset_subsumed: "
          ^(Clause.to_string cl)); *)
        incr_int_stat 1 res_forward_subset_subsumed;
	remove_clause_pred_map !pred_map_ref cl;
       raise Eliminated)
    else
      if !current_options.res_prop_simpl_new
      then     
        (                  
               Prop_solver_exchange.add_clause_to_solver cl;
               let new_cl = Prop_solver_exchange.prop_subsumption cl in 
               if (not (new_cl == cl))             
               then
                 (
                  check_empty_clause new_cl;
                  if (is_subset_subsumed new_cl index_ref) 
                  then
                    (incr_int_stat 1 res_forward_subset_subsumed;
		     remove_clause_pred_map !pred_map_ref cl;
                     raise Eliminated)
                  else 
		     ( 
		       let predMap = add_clause_pred_map new_cl !pred_map_ref in
		       new_cl
		     )
                 )
               else
		(
		 let predMap = add_clause_pred_map cl !pred_map_ref in
                 cl
		)
        )
      else
	(
          let predMap = add_clause_pred_map cl !pred_map_ref in
	  cl
	)
	

(*-------------------------------------------------------*)
(*---------------- Backward Simplification ---------------*)
let eliminate_clause index_ref pred_map_ref cl = 
  Clause.set_bool_param 
    true Clause.is_dead cl;
(* *)  
  (if (Clause.get_bool_param  Clause.in_subset_subsumption_index cl) 
  then 
    (
      index_ref := SubsetSubsume.remove cl !index_ref;
      let predMap = remove_clause_pred_map !pred_map_ref cl in
      ()
    )
  );
(* *)
  (if (Clause.get_bool_param  Clause.in_subsumption_index cl) 
  then 
   (
    SubsumptionIndexM.remove_clause 
      subsumption_index_ref (get_feature_list cl) cl;
     let predMap = remove_clause_pred_map !pred_map_ref cl in
     ()
    )
  )

let simplify_backward main_clause index_ref pred_map_ref = 
  try 
    let subsumed_clauses = SubsetSubsume.find_subsumed main_clause !index_ref in
(*    out_str (
    "Backward SubsetSubsumed: "
    ^(Clause.clause_list_to_string subsumed_clauses)
    ^"   By: "^(Clause.to_string main_clause));*)
(* we can eliminate backward subsumed clauses since *)
(* we first forward subsume a given clause *)
(* and therefore subsumptions are proper here *)
      List.iter (eliminate_clause index_ref pred_map_ref) subsumed_clauses;
   
    incr_int_stat (List.length subsumed_clauses) res_backward_subset_subsumed;
    (if not (subsumed_clauses = []) 
    then 
      ((*out_str ("Is simpl"^(Clause.to_string main_clause)^"\n"); *)
       Clause.set_bool_param true Clause.res_simplifying main_clause)
    else ());
    index_ref :=  SubsetSubsume.remove_subsumed main_clause !index_ref;
  with 
    SubsetSubsume.No_subsumed -> ()

(*-------------------------------------------------------*)
(*------------------ Resolution -------------------------*)

let resolution c1 l1 compl_l1 c_list2 term_db_ref index_ref pred_map_ref = 
  let new_litlist1 = 
    Clause.find_all (fun lit -> not(l1 == lit)) c1 
  in 
  let f rest c2 = 
	try
    let l2_list = Clause.find_all 
		(fun lit -> (Term.get_top_symb (Term.get_atom lit) == Term.get_top_symb (Term.get_atom compl_l1))) c2 in
    let l2 = List.hd l2_list in
    let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
    let new_litlist2 = 
      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
    let conclusion = 
                (*Clause.create (new_litlist1@new_litlist2) in *)
		Clause.create (Clause.normalise_blitlist_list 
              term_db_ref mgu [(1,new_litlist1);(2,new_litlist2)]) in
    (* Q: what is the purpose of the function below? *)
    Clause.assign_tstp_source_resolution conclusion [c1;c2] [l1;compl_l1];
    (* Q: when are we using "when_born" and "conjecture_distance" of a clause? *)
    let min_conj_dist = Clause.get_min_conjecture_distance [c1;c2] in
    Clause.assign_conjecture_distance (min_conj_dist+1) conclusion; 
     
    (* forward simplification wrt F *)
    
	   let r_to_add = simplify_forward conclusion index_ref pred_map_ref in 
	    r_to_add::rest; 
    with
		| Unif.Unification_failed -> rest
	  | Eliminated -> rest 
		in
		
     List.fold_left f [] c_list2     


(*-------------------------------------------------------*)
(*--------------- Main predElim function ----------------*)

let predElim_fun clause_list =
	let clause_set = Clause.clause_list_to_set clause_list in 
	let entry = ref false in
	let pred_map_ref = ref (SymbMap.empty) in
	let predMap = create_pred_map_cl_list clause_set pred_map_ref in
	(* let predList = Map.bindings predMap in *)
	let predList = SymbMap.fold (fun key _val rest -> (key::rest)) predMap [] in
	try
	(*	while (not !entry) do *)
		    let f rest pred =
		    	let pred_info = SymbMap.find pred predMap in 
		    	if (pred_info.multi_occ_cnt == 0) then
			    let posClauses = pred_info.pos_cl_list in
			    let negClauses = pred_info.neg_cl_list in
			    let not_in_pos_neg cl =
				 not (List.exists (fun cl_eq -> (cl == cl_eq)) (posClauses@negClauses))
			    in
			    let restClauses = List.filter not_in_pos_neg clause_list in
			    (* build resolution resolvents *)
			    if (((List.length posClauses) == 0) || ((List.length negClauses) == 0)) then
				rest
			    else 
			    let r rest pos_cl =
			    	let curr_lit_list = Clause.find_all (fun l_pred -> ((Term.get_top_symb (Term.get_atom l_pred)) == pred)) pos_cl in
				(* a checker for curr_lit_list length *)
				let curr_lit_list_length = List.length curr_lit_list in
				match (curr_lit_list_length > 1) with
				| true -> failwith "predElim failed on multi-occurence predicate" 
				| false ->
					let curr_lit = List.hd curr_lit_list in
			    		let compl_curr_lit = Term.compl_lit curr_lit in 
			    		let r_to_add = resolution pos_cl curr_lit compl_curr_lit negClauses term_db_ref ss_f_index_ref pred_map_ref in
					(r_to_add@rest)
			    in
			    let res = List.fold_left r [] posClauses in
			    let remove_clause_local cl = let dummy = remove_clause_pred_map !pred_map_ref cl in () in
			    let removed_pos_clauses = List.iter remove_clause_local posClauses in
			    let removed_neg_clauses = List.iter remove_clause_local negClauses in 
			    (* forward simplification of each clause in R wrt R*)
			    let r_fwd rest cl =
			    	try
			    		let cl_new = simplify_forward cl ss_r_index_ref pred_map_ref in
					cl_new::rest;
				with
					Eliminated -> rest
			    in
			    let res_fwd_simplified = List.fold_left r_fwd [] res in
			    (* backward simplification of R wrt each clause in R*)
			    let r_back cl =
			    	simplify_backward cl ss_r_index_ref pred_map_ref
			    in
			    let for_backward_simplification = List.iter r_back res_fwd_simplified in
			    let r_clean rest cl = 
			    	if (Clause.get_bool_param Clause.is_dead cl) then
				    (rest)
				else
				    (cl::rest)
			    in
			    let r_to_return = List.fold_left r_clean [] res_fwd_simplified in
			    r_to_return@restClauses
			else 
			    rest;
			(*should it be true??*)
			(*let conclusion = Clause.create [] in
			conclusion::rest in*)
			in
		     List.fold_left f [] predList
		(* done *)
	with 
		Not_found ->
			(* out_str  ("Could not run\n") *)
		  failwith ("Could not run\n")


let predElim clause_list =
	out_str "\n\n Before pred elim: \n\n";
	out_str "\n\n Length of clause list before: ";
	print_int (List.length clause_list); 
	out_str "\n\n";
	out_str (Clause.clause_list_to_string clause_list);
	let new_clause_list = predElim_fun clause_list in 
	out_str "\n\n After pred elim: \n\n";
	out_str (Clause.clause_list_to_string new_clause_list); 
	out_str "\n\n Length of clause list after: ";
	print_int (List.length new_clause_list);
	out_str "\n\n";
	new_clause_list

	
 
	

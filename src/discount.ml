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

open Lib
open Options
open Statistics
open Logic_interface

(* exception Unsatisfiable *)

type all_clauses = context

exception Satisfiable of all_clauses

exception DontKnow
(* in order to get the proof we need to pass the empty clause *)
(* exception Empty_Clause of clause*)

module type InputM =
sig
	val inst_module_name : string
	(* we assume that input clauses are normalised with terms in *)
	(* Parsed_input_to_db.term_db_ref *)
	(* clauses are copied, but terms are not some paremters of terms such as *)
	(* inst_in_unif_index can be changed *)
	(* one should run clear_all () which also clears term parameters *)
	val input_clauses : clause list
end

module Make (InputM: InputM) =
struct
	let inst_module_name = InputM.inst_module_name
	let input_clauses = InputM.input_clauses
	
	let _ = clear_res_stat ()
	
	let compressed_subsumtion_index_flag = ref true
	
	(*let init_clause_list_ref = Parsed_input_to_db.clause_list_ref*)
	
	(* all clauses put into this context *)
	
	(* *)
	let res_context_create () = (context_create 21701) (* 21701 medium large prime number *)
	
	let context = ref (res_context_create ())
	
	let res_context_reset () = context := res_context_create ()
	
	let () = assign_fun_stat
			(fun () -> context_size !context) res_num_of_clauses
	
	(* susbetsubsumption index*)
	let ss_index_ref = ref (SubsetSubsume.create ())
	
	exception Eliminated
	exception Given_clause_is_dead
	exception Passive_Empty
	
	(* in order for orphan elimination to be correct: *)
	(* 1. all simplifying clauses should have res_simplifying set to true *)
	(* 2. dead clauses should be removed from all indexies and clauseDB *)
	(* the clause can become dead beacause of the orphan elimination but later *)
	(* can be derived in a non-redundant way (and needed for completeness) *)
	(* and therefore should be regenrated *)
	
	let check_empty_clause clause =
		if (Clause.is_empty_clause clause)
		then
			raise (Empty_Clause clause)
		else ()
	
	let add_active_to_exchange clause =
		match !current_options.res_to_prop_solver with
		| Res_to_Solver_Active ->
				Prop_solver_exchange.add_clause_to_solver clause
		| _ -> ()
	
	(*let dismatching_flag = ref false*)
	
	(*--------------Simple Passive------------*)
	
	let passive_sim = Queue.create ()
	
	let remove_from_sim_passive () =
		try
			let clause = Queue.pop passive_sim in
			Clause.set_ps_in_sim_passive false clause;
			incr_int_stat (-1) res_num_in_passive_sim;
			clause
		with
			Queue.Empty -> raise Passive_Empty
	
	let add_to_sim_passive clause =
		check_empty_clause clause;
		if (Clause.get_is_dead clause)
		then ()
		else
			(
				Queue.push clause passive_sim;
				Clause.set_ps_in_sim_passive true clause;
				incr_int_stat 1 res_num_in_passive_sim;
				(*add_passive_to_exchange clause*)
			)
	
	(*
	let passive_sim = Stack.create ()
	
	let remove_from_sim_passive () =
	try
	let clause = Stack.pop passive_sim in
	Clause.set_bool_param false Clause.res_in_sim_passive clause;
	clause
	with
	Stack.Empty -> raise Passive_Empty
	
	let add_to_sim_passive clause =
	check_empty_clause clause;
	if (Clause.get_bool_param Clause.is_dead clause)
	then ()
	else
	(
	Stack.push clause passive_sim;
	Clause.set_bool_param true Clause.res_in_sim_passive clause;
	num_in_passive_sim:=!num_in_passive_sim +1;
	(*add_passive_to_exchange clause*)
	)
	
	*)
	
	(*----------------Priority Passive----------------*)
	(*---------------Imperative Queues----------------*)
	
	(* total comparison  for clauses!----*)
	(* Heap.ImperativeEq does not work yet..... *)
	
	module Elem =
	struct
		type t = clause
		
		let compare1 = (Clause.cl_cmp_type_list_to_lex_fun
					!current_options.res_pass_queue1)
		let in_queue1 = Clause.get_ps_pass_queue1
		let assign_in_queue1 b c =
			Clause.set_ps_pass_queue1 b c
		let mult1 = !current_options.res_pass_queue1_mult
		
		let compare2 = (Clause.cl_cmp_type_list_to_lex_fun
					!current_options.res_pass_queue2)
		let in_queue2 = Clause.get_ps_pass_queue2
		let assign_in_queue2 b c =
			Clause.set_ps_pass_queue2 b c
		let mult2 = !current_options.res_pass_queue2_mult
		
	end
	
	let init_capacity_priority = 10001
	
	module PassiveQueue = Priority_queues.Queue2(Elem)
	
	let passive_queue_ref = ref (PassiveQueue.create init_capacity_priority)
	
	let () = assign_fun_stat
			(fun () -> PassiveQueue.num_elem !passive_queue_ref) res_num_in_passive
	
	(* if we find that passive queue is empty then we need to clean it: *)
	(* (done by PassiveQueue.clean) *)
	(* 1. assign in_queue param to false in all clauses in the remaining queue*)
	(* 2. release memory and assign new queues *)
	
	let clean_passive () =
		PassiveQueue.clean init_capacity_priority !passive_queue_ref
	(*  passive_queue_ref:=(PassiveQueue.create init_capacity_priority*)
	
	(*exception Passive_Empty *)
	let rec remove_from_pr_passive () =
		try
			let clause = PassiveQueue.remove !passive_queue_ref in
			if ((Clause.get_ps_in_active clause) ||
				(Clause.get_is_dead clause))
			then
				(remove_from_pr_passive ())
			else
				clause
		with PassiveQueue.Empty ->
				(clean_passive ();
					raise Passive_Empty)
	
	let add_to_pr_passive clause =
		check_empty_clause clause;
		if (not (Clause.get_is_dead clause))
		then
			PassiveQueue.add !passive_queue_ref clause
		else ()
	
	(*---------------- Global remove and add to passive----------------*)
	
	let remove_from_passive () =
		if !current_options.res_passive_queue_flag then
			remove_from_pr_passive ()
		else
			remove_from_sim_passive ()
	
	let add_to_passive clause =
		if !current_options.res_passive_queue_flag then
			add_to_pr_passive clause
		else
			add_to_sim_passive clause
	
	(*----------- Subsumption index based on compressed features ------------------------*)
	
	module SubsumptionIndexM = SubsumptionIndex.SCFVIndex
	
	let get_feature_list clause = SubsumptionIndexM.get_feature_list clause
	
	let subsumption_index_ref = ref (SubsumptionIndexM.create ())
	
	let add_to_subsumption_index feature_list clause =
		(*  let feature_list = (get_feature_list clause) in*)
		(*  let com_feature_list = compress_feature_list feature_list in*)
		SubsumptionIndexM.add_clause feature_list clause subsumption_index_ref
	
	(*-------------------- tautology delition--------------------*)
	
	let rec coml_in_list lit_list =
		match lit_list with
		| l:: tl ->
				let exists = List.exists (Term.is_complementary l) tl in
				if exists then exists
				else coml_in_list tl
		|[] -> false
	
	let is_tautology clause =
		let lit_list = Clause.get_literals clause in
		coml_in_list lit_list
	
	(*-----------------Unification Index------------------------------------*)
	
	module DTParam =
	struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end
	module DiscrTreeM = DiscrTree.Make(DTParam)
	
	type unif_index_elem = (lit * (clause list)) list
	let (unif_index_ref : (unif_index_elem DiscrTreeM.index) ref )
	= ref (DiscrTreeM.create ())
	
	(*-------------------------------------*)
	let eliminate_from_unif_index main_clause =
		Clause.set_ps_in_unif_index
			false main_clause ;
		let selected_literals =
			(try (Clause.get_res_sel_lits main_clause)
			with Clause.Res_sel_lits_undef ->
					failwith
						"eliminate_from_unif_index: sel lit should be def. here \n ")
		(*selection_fun main_clause *)
		in
		(* out_str_debug
		("Trying to elim from Unif index:"
		^(Clause.to_string main_clause)
		^" Literals: "
		^(Term.term_list_to_string selected_literals)^"\n");
		*)
		let elim_lit sel_lit =
			
			let ind_elem = DiscrTreeM.find sel_lit !unif_index_ref
			(* failwith "discount:  eliminate_from_unif_index lit is in unif_index"     *)
			in
			( match !ind_elem with
				| Elem(old) ->
						( (* old = [[L1,[C_1,.., Cn]],[L2,[C'_1,.., C'n']],..]
							old_clause_list = [C_1,.., Cn] corr to sel_lit *)
							try
								let old_clause_list = List.assq sel_lit old in
								(* out_str_debug
								("Elem From Unif index old_cl_list:"
								^(Clause.clause_list_to_string old_clause_list)^"\n"); *)
								let old_with_removed = List.remove_assq sel_lit old in
								
								(*remove main_clause*)
								let new_clause_list =
									List.find_all (fun cl -> not(cl == main_clause)) old_clause_list in
								(* out_str_debug
								("Elem From Unif index new_cl_list:"
								^(Clause.clause_list_to_string new_clause_list)^"\n"); *)
								if new_clause_list = []
								then
									if old_with_removed = []
									then
										(DiscrTreeM.remove_term_path sel_lit unif_index_ref
											(*; out_str_debug
											("Elim unif Removed term path"
											^(Term.to_string sel_lit)^"\n") *))
									else
										(ind_elem := Elem(old_with_removed)
											(*; out_str_debug
											("Elim unif: Old_with_removed") *))
								else
									(ind_elem :=
										Elem((sel_lit, new_clause_list):: old_with_removed)
										(*; out_str_debug
										("Elim unif: Old_with_removed") *) )
							with
								Not_found -> ()
						)
				| Empty_Elem ->
						failwith "discount: eliminate_from_unif_index \
				unif index should not contain Empty_Elem"
			) in
		try
			List.iter elim_lit selected_literals;
		with
			Not_found -> ()
	
	(* old, not suitable for orphan elimination *)
	(* Commented *)
	(* eliminates clause from all indexes *)
	(*   but not from ss_index and not from subsumtion index*)
	(*
	let eliminate_clause clause =
	Clause.set_bool_param
	true Clause.is_dead clause;
	if (Clause.get_bool_param Clause.in_active clause)
	then
	(eliminate_from_unif_index clause;
	incr_int_stat (-1) res_num_in_active;
	Clause.set_bool_param false Clause.in_active clause)
	else ()(*;*)
	(* if (Clause.get_bool_param Clause.in_clause_db clause)
	then
	clause_db_ref:= ClauseAssignDB.remove clause !clause_db_ref
	else ()
	*)
	*)
	
	(*let _=out_str "\n Eliminate in Discount Commented\n"*)
	
	let eliminate_clause clause =
		Clause.assign_is_dead true clause;
		(if (Clause.get_ps_in_active clause)
			then
				(eliminate_from_unif_index clause;
					incr_int_stat (-1) res_num_in_active;
					Clause.set_ps_in_active false clause)
			else ()
		);
		(* *)
		(if (Clause.get_ps_in_subset_subsumption_index clause)
			then
				(ss_index_ref := SubsetSubsume.remove clause !ss_index_ref
				)
		);
		(* *)
		(if (Clause.get_ps_in_subsumption_index clause)
			then
				SubsumptionIndexM.remove_clause
					subsumption_index_ref (get_feature_list clause) clause
		);
		((* out_str ("Eliminated clause: "^(Clause.to_string clause)^"\n");*)
			context_remove !context clause
		)
	
	(*-----------------------Simplify Light---------------------*)
	
	(*---------Add to ss_index--------*)
	let add_to_ss_index clause =
		(* try *)
		ss_index_ref := SubsetSubsume.add_clause clause !(ss_index_ref);
		Clause.set_ps_in_subset_subsumption_index true clause
	(* with
	_ ->
	failwith
	"discount add_to_ss_index: should be checked on subsest subs before adding " *)
	
	(*-------------*)
	
	let is_subset_subsumed clause =
		try
			let by_clause = SubsetSubsume.is_subsumed clause !(ss_index_ref) in
			Clause.set_ps_simplifying true by_clause;
			true
		with
			Not_found ->
				false
	
	(* since the clause is not in the db we do not need to mark it as dead *)
	let simplify_light_forward_new clause =
		if (is_tautology clause)
		then
			((* out_str_debug
				("Simplified tautology: "
				^(Clause.to_string clause));*)
				incr_int_stat 1 res_tautology_del;
				raise Eliminated)
		else
		if (is_subset_subsumed clause)
		then
			((* out_str
				("Subset_subsumed: "
				^(Clause.to_string clause)); *)
				incr_int_stat 1 res_forward_subset_subsumed;
				raise Eliminated)
		else
		if !current_options.res_prop_simpl_new
		then
			(
				Prop_solver_exchange.add_clause_to_solver clause;
				let new_clause = Prop_solver_exchange.prop_subsumption clause in
				if (not (new_clause == clause))
				then
					(
						check_empty_clause new_clause;
						if (is_subset_subsumed new_clause)
						then
							(incr_int_stat 1 res_forward_subset_subsumed;
								raise Eliminated)
						else new_clause
					)
				else
					clause
			)
		else
			clause
	
	let simplify_light_backward_new main_clause =
		try
			let subsumed_clauses = SubsetSubsume.find_subsumed main_clause !ss_index_ref in
			(* out_str (
			"Backward SubsetSubsumed: "
			^(Clause.clause_list_to_string subsumed_clauses)
			^"   By: "^(Clause.to_string main_clause));*)
			(* we can eliminate backward subsumed clauses since *)
			(* we first forward subsume given clause *)
			(* and therefore subsumtions are proper here *)
			List.iter eliminate_clause subsumed_clauses;
			
			incr_int_stat (List.length subsumed_clauses) res_backward_subset_subsumed;
			(if not (subsumed_clauses = [])
				then
					((*out_str ("Is simpl"^(Clause.to_string main_clause)^"\n"); *)
						Clause.set_ps_simplifying true main_clause)
				else ());
			ss_index_ref := SubsetSubsume.remove_subsumed main_clause !ss_index_ref;
		with
			SubsetSubsume.No_subsumed -> ()
	
	(*---------------------Add new clauses to Passive------------------*)
	
	(*let _= out_str "!!!!!!!!!Full Simplification of New clauses!!!!!!!"*)
	
	(* preprocess_new_clause lightly simplifies and *)
	(* adds to ss_index and porop. solver  *)
	(* can raise Unsatisfiable, Eliminated *)
	
	let preprocess_new_clause clause =
		check_empty_clause clause;
		if (not (Clause.get_is_dead clause))
		then
			(
				(* (if (!current_options.res_prop_simpl_new
				|| !current_options.res_prop_simpl_given
				|| !current_options. !add_passive_to_exchange_flag) *)
				(match !current_options.res_to_prop_solver with
					| Res_to_Solver_Passive ->
							Prop_solver_exchange.add_clause_to_solver clause
					| _ -> ());
				let main_clause = simplify_light_forward_new clause in
				(*	let clause_ls = simplify_light_forward_new clause in
				let (_feat_list, main_clause) = all_simplifications clause_ls in *)
				(if (*!add_passive_to_exchange_flag &&*) (not (main_clause == clause))
					then
						(match !current_options.res_to_prop_solver with
							| Res_to_Solver_Passive ->
									Prop_solver_exchange.add_clause_to_solver clause
							| _ -> ())
				);
				simplify_light_backward_new main_clause;
				let added_clause = context_add !context main_clause in
				(*	Clause.assign_when_born (get_val_stat res_num_of_loops) added_clause;*)
				(* Clause.assign_conjecture_distance
				(Clause.get_min_conjecture_distance [added_clause; main_clause])
				added_clause;	*)
				add_to_ss_index added_clause;
				added_clause
			)
		else
			raise Eliminated
	
	let add_new_clause_to_passive clause =
		try
		(*    out_str ("Before Prep Clause: "^(Clause.to_string clause)^"\n");*)
			let added_clause = preprocess_new_clause clause in
			(*    out_str ("Added Clause: "^(Clause.to_string added_clause)^"\n");*)
			add_to_passive added_clause
		
		(*	passive_queue_ref :=
		PassiveQueue.add added_clause !(passive_queue_ref);
		Clause.set_bool_param true Clause.in_passive added_clause;*)
		(* one might also add to full subsumption index*)
		with
			Eliminated -> ()
	
	(*
	let add_inst_exchange_clause_to_passive clause =
	let old_exch_flag = !add_passive_to_exchange_flag in
	add_passive_to_exchange_flag := false;
	add_new_clause_to_passive clause;
	add_passive_to_exchange_flag := old_exch_flag
	*)
	
	let add_conclusion_to_passive given_clause clause =
		add_new_clause_to_passive clause;
		(* give_clause can be simplifed by add_new_clause_to_passive *)
		if (Clause.get_is_dead given_clause)
		then
			(* we abort all further
			inferences with the given clause,
			later we can add to eliminate also all other conclusions
			with this clause but not this one!,
			also in general after backward subsumption we can eliminate
			all children of the subsumed clause provided that we add
			the clause which subsumes to the clause set *)
			( (*out_str ("\nSubset subs Resol."^(Clause.to_string given_clause)^"\n"); *)
				raise Given_clause_is_dead)
		else ()
	
	(*-----------Forward subsumption resolution---------------*)
	(*
	let get_compl_db lit =
	let compl_lit = Term.compl_lit lit in
	(* need to add new term to DB, if positive then it is a subterm of lit *)
	(* and threfore already in TermDB *)
	if (Term.is_neg_lit compl_lit) then
	TermDB.add_ref compl_lit term_db_ref
	else
	compl_lit
	*)
	
	(* returns new list of lits which is obtained by all possible cuts*)
	(* we also keep subsumed by list to add to history later *)
	
	let rec forward_subs_res_list subs_by_list_ref tried_lits rest =
		match rest with
		| h:: tl ->
				let compl_h = add_compl_lit h in
				let tstp_source = Clause.tstp_source_tmp in (* replace later with lit_list*)
				let clause_to_try = create_clause tstp_source (tried_lits@(compl_h:: tl)) in
				let feature_list = get_feature_list clause_to_try in
				(* out_str ("clause_to_try: "^(Clause.to_string clause_to_try)^" "
				^(feature_list_to_string feature_list)^"\n");*)
				(match
					(SubsumptionIndexM.is_subsumed
							feature_list clause_to_try subsumption_index_ref)
					with
					| Some((by_cl, _subst)) ->
							(incr_int_stat 1 res_forward_subsumption_resolution;
								subs_by_list_ref:= by_cl:: (!subs_by_list_ref);
								(*	   out_str ("Subsumed: "^(Clause.to_string clause_to_try)^"\n");*)
								forward_subs_res_list subs_by_list_ref tried_lits tl)
					(* we do not need to retry tried lits after elimination of a literal *)
					(*	   forward_subs_res_list subs_by_list_ref [] (tried_lits@tl))*)
					| None ->
							forward_subs_res_list subs_by_list_ref (tried_lits@[h]) tl
				)
		|[] -> tried_lits
	
	(* can rise Unsatisfiable, Eliminated*)
	let forward_subs_res clause =
		(*  out_str ("Try: "^(Clause.to_string clause)^"\n");*)
		let lits = get_lits clause in
		let subs_by_list_ref = ref [] in
		let new_lits = forward_subs_res_list subs_by_list_ref [] lits in
		if not (!subs_by_list_ref = [])
		then
			(
				let tstp_source = Clause.tstp_source_forward_subsumption_resolution clause (!subs_by_list_ref) in
				let new_clause = create_clause tstp_source new_lits in
				clause_register_subsumed_by ~by: (new_clause) clause;
				(* Clause.inherit_param_modif clause new_clause;
				Clause.set_bool_param true Clause.res_simplifying new_clause;*)
				(* Clause.assign_forward_subsumption_resolution_history
				new_clause clause (!subs_by_list_ref); *)
				(* Clause.assign_tstp_source_forward_subsumption_resolution
				new_clause clause (!subs_by_list_ref); *)
				(* out_str ("Elim: "^(Clause.to_string clause)^"\n");
				out_str ("New: "^(Clause.to_string new_clause)^"\n");
				out_str ("By: "^(Clause.clause_list_to_string !subs_by_list_ref)^"\n");*)
				eliminate_clause clause;
				preprocess_new_clause new_clause
			)
		else
			clause
	
	(*------------Forward Subsumption--------------------*)
	
	let forward_subs_feature feature_list clause =
		(* do not need light simplifications since light backward *)
		match
		(SubsumptionIndexM.is_subsumed
				feature_list clause subsumption_index_ref)
		with
		| Some((by_cl, _subst)) ->
				(
					incr_int_stat 1 res_forward_subsumed;
					clause_register_subsumed_by ~by: by_cl clause;
					(*  Clause.set_bool_param true Clause.res_simplifying by_cl;*)
					(* we can eliminate since subs. is proper since light simplifications *)
					eliminate_clause clause;
					(*debug*)
					(* out_str ("Subs by unit cl: "^(string_of_int (Clause.length by_cl))^"\n");*)
					(*end debug*)
					(*       out_str ("Is subsumed: "^(Clause.to_string clause)^"\n");*)
					raise Given_clause_is_dead )
		| None -> clause
	
	(*
	let forward_subs_full clause =
	let feature_list = (get_feature_list clause) in
	forward_subs_feature feature_list clause
	*)
	
	(* do subsumption only by clauses of length smaller or equal to a given length *)
	(* we assume that the first feature is always length! *)
	let forward_subs_by_length length feature_list clause =
		let new_feature_list =
			match feature_list with
			| _:: rest -> length:: rest
			| _ -> failwith "Discount: get_feature_for_unit_subs "
		in
		forward_subs_feature new_feature_list clause
	
	(*---------------*)
	let simplify_forward feature_list clause =
		let prop_simplified =
			if !current_options.res_prop_simpl_given
			then
				(* in case clause is not in solver add it *)
				(
					Prop_solver_exchange.add_clause_to_solver clause;
					let new_clause = Prop_solver_exchange.prop_subsumption clause in
					(*     Clause.inherit_param_modif clause new_clause;*)
					if (not (new_clause == clause))
					then
						(eliminate_clause clause;
							preprocess_new_clause new_clause
						)
					else clause
				)
			else clause
		in
		let forward_subs =
			match !current_options.res_forward_subs
			with
			| Subs_Full ->
					forward_subs_feature feature_list prop_simplified
			| Subs_By_Length (length) -> failwith "Uncomment"
			
			(* uncomment later, compress subs. test *)
			(*
			forward_subs_by_length length feature_list prop_simplified
			*)
			| Subs_Subset -> prop_simplified
		in
		if !current_options.res_forward_subs_resolution
		then forward_subs_res forward_subs
		else forward_subs
	
	(*------------Backward Subsumption Resolution--------------------*)
	
	let rec remove_lit lit lits =
		List.filter (fun x -> not (x == lit)) lits
	
	let apply_lit_cut given_clause subsumed_subst_list lit =
		let f subsumed_and_new_clause_list (subsumed, subst) =
			incr_int_stat 1 res_backward_subsumption_resolution;
			let lits = get_lits subsumed in
			let lit_to_cut = Subst.apply_subst_term term_db_ref subst lit in
			let new_lits = remove_lit lit_to_cut lits in
			let tstp_source = Clause.tstp_source_backward_subsumption_resolution [given_clause; subsumed] in
			let new_clause = create_clause tstp_source new_lits in
			clause_register_subsumed_by ~by: new_clause subsumed;
			eliminate_clause subsumed;
			(* Clause.inherit_param_modif subsumed new_clause;*)
			
			(* out_str ("Back_subsed: "^(Clause.to_string subsumed)
			^" Lit to cut: "^(Term.to_string lit_to_cut)
			^"\nNew clause: "^(Clause.to_string new_clause));*)
			(subsumed, new_clause):: subsumed_and_new_clause_list
		in
		List.fold_left f [] subsumed_subst_list
	
	(*(subsumed_list, new_clauses_list)*)
	
	let rec backward_subs_res_list given_clause tried_lits rest =
		match rest with
		| h:: tl ->
				let compl_h = add_compl_lit h in
				let tstp_source = Clause.tstp_source_tmp in (* replace later with lit_list*)
				let clause_to_try = create_clause tstp_source (tried_lits@(compl_h:: tl)) in
				let feature_list = get_feature_list clause_to_try in
				(*      out_str ("backward clause_to_try: "^(Clause.to_string clause_to_try)^"\n");*)
				let subsumed_subst_list =
					(SubsumptionIndexM.find_subsumed_subst
							subsumption_index_ref feature_list clause_to_try) in
				let add_subsumed_and_new_clause_list =
					apply_lit_cut given_clause subsumed_subst_list compl_h in
				let rest_subsumed_and_new_clause_list =
					backward_subs_res_list given_clause (tried_lits@[h]) tl in
				add_subsumed_and_new_clause_list@rest_subsumed_and_new_clause_list
		| [] -> []
	
	let backward_subs_res given_clause =
		let lits = get_lits given_clause in
		let subsumed_and_new_clause_list = backward_subs_res_list given_clause [] lits in
		let f (_subsumed, new_clause) =
			(* (* Clause.assign_backward_subsumption_resolution_history
			new_clause [clause; subsumed]; *)
			Clause.assign_tstp_source_backward_subsumption_resolution
			new_clause [clause; subsumed];
			Clause.set_bool_param true Clause.res_simplifying new_clause;
			eliminate_clause subsumed;*)
			add_new_clause_to_passive new_clause
		in
		List.iter f subsumed_and_new_clause_list
	
	(*debug*)
	(* if not (subsumed_list = []) then
	( out_str ("\n Back subsumed by: "^(Clause.to_string clause)^"\n");
	List.iter (fun c -> out_str ("Eliminated: "^(Clause.to_tptp c)^"\n"))
	subsumed_list;
	List.iter (fun c -> out_str ("New clauses: "^(Clause.to_tptp c)^"\n"))
	new_clauses)
	else ()
	*)
	
	(*------------Backward Subsumption--------------------*)
	
	let backward_subs_full feature_list clause =
		let b_subsumed_list =
			(SubsumptionIndexM.find_subsumed
					feature_list clause subsumption_index_ref) in
		if b_subsumed_list != []
		then
			(
				List.iter (fun subsumed ->
								clause_register_subsumed_by ~by: clause subsumed;
								eliminate_clause subsumed
					) b_subsumed_list;
				incr_int_stat (List.length b_subsumed_list) res_backward_subsumed
			)
		else ()
	
	let backward_subs_by_length length feature_list clause =
		if ((Clause.length clause) <= length)
		then
			backward_subs_full feature_list clause
		else ()
	
	let simplify_backward feature_list clause =
		(match !current_options.res_backward_subs with
			| Subs_Full -> backward_subs_full feature_list clause
			| Subs_By_Length (length) -> backward_subs_by_length length feature_list clause
			| Subs_Subset -> ()
		);
		if !current_options.res_backward_subs_resolution
		then
			backward_subs_res clause
		else ()
	
	(*-----Orphan Elimination---------------*)
	(* we need to try orphan elimination only if *)
	(* at leas one clause is backward susbumed  *)
	let some_are_backward_subsumed () =
		if
		(get_val_stat res_backward_subset_subsumed) > 0 or
		(get_val_stat res_backward_subsumed) > 0 or
		(get_val_stat res_backward_subsumption_resolution) > 0
		then true
		else false
	
	let orphan_elimination clause =
		if !current_options.res_orphan_elimination
		then
			if (some_are_backward_subsumed ())
			then
				(let orphan_list = Clause.get_orphans clause in
					List.iter
						(fun c ->
									if (not (Clause.get_ps_simplifying c)) &&
									(not (Clause.get_is_dead c))
									then
										(eliminate_clause c;
											(*    out_str ("Orph: "^(Clause.to_string c)^"\n");*)
											incr_int_stat 1 res_orphan_elimination)
									else ()
						) orphan_list;
					if (Clause.get_is_dead clause)
					then raise Eliminated else()
				)
			else ()
		else ()
	
	(*---------------------General Simplify---------------------*)
	
	let all_simplifications clause =
		orphan_elimination clause;
		(* feature_list is quite expensive therefore need to pass it as param*)
		let feature_list = get_feature_list clause in
		(*  out_str ("simpl: "^(Clause.to_string clause)^"\n");*)
		let simplified_clause = simplify_forward feature_list clause in
		check_empty_clause clause;
		check_disc_time_limit ();
		let new_feature_list =
			if (simplified_clause == clause) then
				feature_list
			else
				get_feature_list simplified_clause
		in
		simplify_backward new_feature_list simplified_clause;
		check_disc_time_limit ();
		if (Clause.get_is_dead simplified_clause)
		then
			raise Eliminated
		else
			(new_feature_list, simplified_clause)
	
	(*----------------------all factorings-----------------------*)
	let rec all_factorings' main_clause sel_lit rest_sel_lits =
		match rest_sel_lits with
		| l:: tl ->
				(try
					let conclusion =
						Inference_rules.factoring main_clause sel_lit l term_db_ref in
					add_conclusion_to_passive main_clause conclusion;
					(* out_str_debug ("\n Factoring: "^(Clause.to_string main_clause)
					^" conclusion: "^(Clause.to_string conclusion));*)
					all_factorings' main_clause sel_lit tl
				with Unif.Unification_failed -> ()
				)
		|[] -> ()
	
	let rec all_factorings_lits main_clause selected_literals =
		match selected_literals with
		| l:: tl ->
				all_factorings' main_clause l tl;
				all_factorings_lits main_clause tl
		|[] -> ()
	
	let all_factorings main_clause =
		let selected_literals =
			(try (Clause.get_res_sel_lits main_clause)
			with Clause.Res_sel_lits_undef ->
					failwith
						"all_factorings: sel lit should be def. here \n ")
		in all_factorings_lits main_clause selected_literals
	
	(*-------------------------all resolutions-----------------------*)
	
	(* eliminates dead clauses from the clause_list and returns the rest*)
	let rec remove_if_dead_from_active stat_entry clause_list =
		match clause_list with
		| c:: tl ->
				if (Clause.get_is_dead c)
				then
					(
						incr_int_stat 1 stat_entry;
						eliminate_clause c;
						(*	 out_str ("Backward Subsumed: "^(Clause.to_string c)^"\n");*)
						remove_if_dead_from_active stat_entry tl)
				else
					c:: (remove_if_dead_from_active stat_entry tl)
		|[]-> []
	
	let all_resolutions main_clause selected_literals =
		(* out_str ("res: main"^(Clause.to_string main_clause)^"\n"); *)
		try
			(let for_all_sel_lit sel_lit =
					let compl_sel_lit = Term.compl_lit sel_lit in
					let unif_candidates =
						DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
					let for_all_candidates (lit, clause_list) =
						(try
					(*		out_str ("res_try: "^(Clause.to_string main_clause)
									^(Clause.clause_list_to_string clause_list));
          *)
							let new_clause_list =
								remove_if_dead_from_active res_backward_subsumption_resolution clause_list
							in
							let conclusion_list =
								Inference_rules.resolution
									main_clause sel_lit compl_sel_lit new_clause_list lit term_db_ref in
							
							(*
							let conclusion_list =
							Inference_rules.resolution_dismatch (!dismatching_flag)
							(!forward_subs_resolution_flag) (!backward_subs_resolution_flag)
							main_clause sel_lit compl_sel_lit new_clause_list lit term_db_ref in
							*)
						(*	
							out_str
								("resolution: "^(Clause.to_string main_clause)
									^"["^(Clause.clause_list_to_string new_clause_list)^"]"
									^"conclusion: "
									^"["^(Clause.clause_list_to_string conclusion_list)^"]");
					*)
							(if !current_options.res_backward_subs_resolution
								then
									let _ =
										remove_if_dead_from_active res_backward_subsumption_resolution new_clause_list
									in ()
								else ());
							List.iter (add_conclusion_to_passive main_clause) conclusion_list
						with Unif.Unification_failed -> ()
						) in
					List.iter for_all_candidates unif_candidates in
				List.iter for_all_sel_lit selected_literals
			)
		with
			Inference_rules.Main_subsumed_by (by_conclusion) ->
				(
					incr_int_stat 1 res_forward_subsumption_resolution;
					add_conclusion_to_passive main_clause by_conclusion)
	
	(* add to unif index *)
	
	let add_to_unif_index main_clause selected_literals =
	(*	out_str ("adding to unif_index: "^(Clause.to_string main_clause)^" lits: "^(Term.term_list_to_string selected_literals)^"\n"); *)
		let add_lit sel_lit =
			let ind_elem = DiscrTreeM.add_term_path sel_lit unif_index_ref in
			(match !ind_elem with
				| Elem(old) ->
						(try
							let old_clause_list = List.assq sel_lit old in
							let old_with_removed = List.remove_assq sel_lit old in
							ind_elem :=
							Elem((sel_lit, (main_clause:: old_clause_list)):: old_with_removed)
						with Not_found -> ind_elem := Elem((sel_lit,[main_clause]):: old)
						)
				| Empty_Elem ->
						ind_elem := Elem([(sel_lit,[main_clause])])
			)
		in
		List.iter add_lit selected_literals;
		Clause.set_ps_in_unif_index true main_clause
	
	(* add_to_subsumption_index *)
	(*add later !!!*)
	
	(*--------------------Discount Loop-------------------------*)
	
	let rec discount_loop_body () =
		incr_int_stat 1 res_num_of_loops;
		try
		(* let clause = PassiveQueue.maximum !(passive_queue_ref) in
		passive_queue_ref := PassiveQueue.remove !(passive_queue_ref);*)
			let clause = remove_from_passive () in
			(*   out_str ("removed form passive"^(Clause.to_string clause)^"\n");*)
			if ((Clause.get_is_dead clause) ||
				(Clause.get_ps_in_active clause))
			then () (* (out_str ("is dead or in active"^(Clause.to_string clause)^"\n");) *)
			else
				(try
					let (feature_list, given_clause) = all_simplifications clause in
					(* Clause.set_bool_param false Clause.in_passive given_clause; *)
					let selected_literals = Selection.res_lit_sel given_clause in
					(*
					out_str ("given_clause: "^(Clause.to_string given_clause)
					^"selected lit: "
					^(Term.term_list_to_string selected_literals)^"\n");
					out_str ("Born: "^( string_of_int (Clause.get_ps_when_born given_clause))^"\n");
					*)
					
					(*debug*)
					(* (if (Clause.length given_clause) <=1 then
					out_str_debug ("given unit clause: "
					^(Clause.to_string given_clause)^"\n"));*)
					all_factorings given_clause;
					all_resolutions given_clause selected_literals;
					add_to_unif_index given_clause selected_literals;
					Clause.set_ps_in_active true given_clause;
					incr_int_stat 1 res_num_in_active;
					(* alternatively one can add all newly generated to subsumption also  *)
					add_to_subsumption_index feature_list given_clause;
					add_active_to_exchange given_clause;
				(* out_str
				("\n In Active: "^(Clause.to_string given_clause)) *)
				(* else () *)
				with
				| Eliminated -> ()
				| Given_clause_is_dead -> ()
				(*out_str_debug "\n Given_clause_is_dead \n"*)
				)
		with
			Passive_Empty -> 
				((* out_str ("Satisfiable context 2 \n\n");
		  	context_iter !context (fun c -> out_str ((Clause.to_string c)^"\n"));
				*) 
				raise (Satisfiable !context)
	       )
	(*-------------------- Adaptive selection ---------------------*)
	
	(*--------------------Old without subs resol.-----------------------------*)
	(*
	let resolution_change_sel main_clause =
	let success = ref false in
	try
	(
	while (not !success) do
	let current_select_lits =
	(try (Clause.get_res_sel_lits main_clause)
	with Clause.Res_sel_lits_undef ->
	failwith "resolution_change_sel: sel lit should be def. here \n ")
	in
	(* out_str_debug ("Main Clause: "^(Clause.to_string main_clause)
	^"Selected lit: "
	^(Term.term_list_to_string current_select_lits)^"\n"); *)
	if (not (Clause.get_bool_param Clause.res_sel_max main_clause))
	then
	(* then only one lit is sel and it is neg*)
	let sel_lit =
	(match current_select_lits with
	| h::[] -> h
	| _ -> failwith "resolution_change_sel: more than one lit sel \n ")
	in
	let compl_sel_lit = Term.compl_lit sel_lit in
	let unif_candidates =
	DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
	if (unif_candidates = [])
	then
	(success:= true)
	else
	(let _ = Selection.change_sel main_clause in ();
	res_num_change_sel:=!res_num_change_sel +1)
	else
	( (* selection is final: maximal, can be several lits*)
	success:= true;
	let for_all_sel_lit sel_lit =
	let compl_sel_lit = Term.compl_lit sel_lit in
	let unif_candidates =
	DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
	let for_all_candidates (lit, clause_list) =
	let prune_clause_list rest clause =
	if (not (Clause.get_bool_param Clause.res_sel_max clause))
	then
	(
	(* out_str_debug ("Removed from Active: "
	^(Clause.to_string clause)
	^"Selected lit: "
	^(Term.term_list_to_string
	(Clause.get_res_sel_lits clause) )^"\n"); *)
	eliminate_from_unif_index clause;
	Clause.set_bool_param false Clause.in_active clause;
	incr_int_stat (-1) res_num_in_active;
	res_num_moves_active:=!res_num_moves_active +1;
	let _ = Selection.change_sel clause in ();
	res_num_change_sel:=!res_num_change_sel +1;
	(* out_str_debug ("New sel: "
	^(Term.term_list_to_string
	(Clause.get_res_sel_lits clause))^"\n"); *)
	add_to_passive clause;
	rest)
	else
	clause:: rest
	in
	let side_clause_list =
	List.fold_left prune_clause_list [] clause_list
	in
	(try
	let conclusion_list =
	Inference_rules.resolution
	!forward_subs_resolution_flag !backward_subs_resolution_flag
	main_clause sel_lit compl_sel_lit side_clause_list lit term_db_ref
	in
	(if !backward_subs_resolution_flag
	then
	let _ = remove_if_dead_from_active
	num_backward_subs_resolution side_clause_list
	in ()
	else ()
	);
	List.iter (add_conclusion_to_passive main_clause) conclusion_list
	with Unif.Unification_failed -> ()
	) in
	List.iter for_all_candidates unif_candidates in
	List.iter for_all_sel_lit current_select_lits
	)
	
	done
	)
	with
	Inference_rules.Main_subsumed_by (by_conclusion) ->
	(num_forward_subs_resolution := !num_forward_subs_resolution +1;
	add_conclusion_to_passive main_clause by_conclusion)
	
	*)
	
	(*--------------Commented---------------------------------*)
	(*
	(*-------------New with subs. resol.------------------------------*)
	let resolution_change_sel main_clause =
	let success = ref false in
	try
	(
	while (not !success) do
	let current_select_lits =
	(try (Clause.get_res_sel_lits main_clause)
	with Clause.Res_sel_lits_undef ->
	failwith "resolution_change_sel: sel lit should be def. here \n ")
	in
	(* out_str_debug ("Main Clause: "^(Clause.to_string main_clause)
	^"Selected lit: "
	^(Term.term_list_to_string current_select_lits)^"\n"); *)
	if (not (Clause.get_bool_param Clause.res_sel_max main_clause))
	then
	(* then only one lit is sel and it is neg*)
	let sel_lit =
	(match current_select_lits with
	| h::[] -> h
	| _ -> failwith "resolution_change_sel: more than one lit sel \n ")
	in
	let compl_sel_lit = Term.compl_lit sel_lit in
	let unif_candidates =
	DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
	(* subsumption resolution is proper now *)
	(*--*) if ((not !current_options.res_forward_subs_resolution)
	&& (not !current_options.res_backward_subs_resolution))
	then
	(*---*)
	(if ( unif_candidates = [])
	then
	(success:= true)
	else
	(let _ = Selection.change_sel main_clause in ();
	incr_int_stat 1 res_num_sel_changes)
	)
	(*---*) else
	(* subsumption resolution part! *)
	let for_all_candidates rest (lit, clause_list) =
	(try
	let clause_list_before =
	remove_if_dead_from_active
	res_backward_subsumption_resolution clause_list
	in
	let subsuming_list =
	Inference_rules.subs_resolution
	main_clause sel_lit compl_sel_lit clause_list_before lit term_db_ref
	in
	List.iter (add_conclusion_to_passive main_clause) subsuming_list;
	let clause_list_after =
	if !current_options.res_backward_subs_resolution
	then
	remove_if_dead_from_active
	res_backward_subsumption_resolution clause_list_before
	else
	clause_list_before
	in
	clause_list_after@rest
	with
	Unif.Unification_failed -> rest
	)
	in
	
	let all_clause_list =
	List.fold_left for_all_candidates [] unif_candidates in
	if (all_clause_list = [])
	then
	(success:= true)
	else
	(let _ = Selection.change_sel main_clause in ();
	incr_int_stat 1 res_num_sel_changes)
	(*----- *)
	else
	( (* selection is final: maximal, can be several lits*)
	success:= true;
	let for_all_sel_lit sel_lit =
	let compl_sel_lit = Term.compl_lit sel_lit in
	let unif_candidates =
	DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
	let for_all_candidates (lit, clause_list) =
	let prune_clause_list rest clause =
	if (not (Clause.get_bool_param Clause.res_sel_max clause))
	then
	(
	(* out_str ("Removed from Active: "
	^(Clause.to_string clause)
	^"Selected lit: "
	^(Term.term_list_to_string
	(Clause.get_res_sel_lits clause) )^"\n"); *)
	eliminate_from_unif_index clause;
	Clause.set_bool_param false Clause.in_active clause;
	incr_int_stat (-1) res_num_in_active;
	incr_int_stat 1 res_moves_from_active_to_pass;
	let _ = Selection.change_sel clause in ();
	incr_int_stat 1 res_num_sel_changes;
	
	(* out_str_debug ("New sel: "
	^(Term.term_list_to_string
	(Clause.get_res_sel_lits clause))^"\n"); *)
	add_to_passive clause;
	rest)
	else
	clause:: rest
	in
	let side_clause_list =
	List.fold_left prune_clause_list [] clause_list
	in
	(try
	let conclusion_list =
	Inference_rules.resolution
	main_clause sel_lit compl_sel_lit side_clause_list lit term_db_ref
	in
	((if !current_options.res_backward_subs_resolution
	then
	(let _ = remove_if_dead_from_active
	res_backward_subsumption_resolution
	side_clause_list
	in ())
	else ()
	);
	(*debug*)
	(* let f cl =
	if (Clause.is_ground cl)
	then
	out_str ((Clause.to_string cl)^"\n")
	else ()
	in
	List.iter f conclusion_list;
	*)
	(*debug end*)
	List.iter (add_conclusion_to_passive main_clause) conclusion_list
	)
	with Unif.Unification_failed -> ()
	)
	in
	List.iter for_all_candidates unif_candidates in
	List.iter for_all_sel_lit current_select_lits
	)
	done
	)
	with
	Inference_rules.Main_subsumed_by (by_conclusion) ->
	(
	incr_int_stat 1 res_forward_subsumption_resolution;
	add_conclusion_to_passive main_clause by_conclusion)
	
	*)
	
	(*--------------end Commented---------------------------------*)
	
	let resolution_change_sel main_clause =
		let success = ref false in
		try
			(
				while (not !success) do
					let current_select_lits =
						(try (Clause.get_res_sel_lits main_clause)
						with Clause.Res_sel_lits_undef ->
								failwith "resolution_change_sel: sel lit should be def. here \n ")
					in
					(* out_str_debug ("Main Clause: "^(Clause.to_string main_clause)
					^"Selected lit: "
					^(Term.term_list_to_string current_select_lits)^"\n"); *)
					if (not (Clause.get_ps_sel_max main_clause))
					then
						(* then only one lit is sel and it is neg*)
						let sel_lit =
							(match current_select_lits with
								| h::[] -> h
								| _ -> failwith "resolution_change_sel: more than one lit sel \n ")
						in
						let compl_sel_lit = Term.compl_lit sel_lit in
						let unif_candidates =
							DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
						(* subsumption resolution is proper now *)
						(*---*) if ((not !current_options.res_forward_subs_resolution)
							&& (not !current_options.res_backward_subs_resolution))
						then
							(*---*)
							(if ( unif_candidates = [])
								then
									(success:= true)
								else
									(let _ = Selection.change_sel main_clause in ();
										incr_int_stat 1 res_num_sel_changes)
							)
						(*---*) else
							(* subsumption resolution part! *)
							let for_all_candidates rest (lit, clause_list) =
								(try
									let clause_list_before =
										remove_if_dead_from_active
											res_backward_subsumption_resolution clause_list
									in
									let subsuming_list =
										Inference_rules.subs_resolution
											main_clause sel_lit compl_sel_lit clause_list_before lit term_db_ref
									in
									List.iter (add_conclusion_to_passive main_clause) subsuming_list;
									let clause_list_after =
										if !current_options.res_backward_subs_resolution
										then
											remove_if_dead_from_active
												res_backward_subsumption_resolution clause_list_before
										else
											clause_list_before
									in
									clause_list_after@rest
								with
									Unif.Unification_failed -> rest
								)
							in
							
							let all_clause_list =
								List.fold_left for_all_candidates [] unif_candidates in
							if (all_clause_list = [])
							then
								(success:= true)
							else
								(let _ = Selection.change_sel main_clause in ();
									incr_int_stat 1 res_num_sel_changes)
					(*----- *)
					else
						( (* selection is final: maximal, can be several lits*)
							success:= true;
							let for_all_sel_lit sel_lit =
								let compl_sel_lit = Term.compl_lit sel_lit in
								let unif_candidates =
									DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
								let for_all_candidates (lit, clause_list) =
									let prune_clause_list rest clause =
										if (not (Clause.get_ps_sel_max clause))
										then
											(
												(* out_str ("Removed from Active: "
												^(Clause.to_string clause)
												^"Selected lit: "
												^(Term.term_list_to_string
												(Clause.get_res_sel_lits clause) )^"\n"); *)
												eliminate_from_unif_index clause;
												Clause.set_ps_in_active false clause;
												incr_int_stat (-1) res_num_in_active;
												incr_int_stat 1 res_moves_from_active_to_pass;
												let _ = Selection.change_sel clause in ();
												incr_int_stat 1 res_num_sel_changes;
												
												(* out_str_debug ("New sel: "
												^(Term.term_list_to_string
												(Clause.get_res_sel_lits clause))^"\n"); *)
												add_to_passive clause;
												rest)
										else
											clause:: rest
									in
									let side_clause_list =
										List.fold_left prune_clause_list [] clause_list
									in
									(try
										let conclusion_list =
											Inference_rules.resolution
												main_clause sel_lit compl_sel_lit side_clause_list lit term_db_ref
										in
										((if !current_options.res_backward_subs_resolution
												then
													(let _ = remove_if_dead_from_active
																res_backward_subsumption_resolution
																side_clause_list
														in ())
												else ()
											);
											(*debug*)
											(* let f cl =
											if (Clause.is_ground cl)
											then
											out_str ((Clause.to_string cl)^"\n")
											else ()
											in
											List.iter f conclusion_list;
											*)
											(*debug end*)
											List.iter (add_conclusion_to_passive main_clause) conclusion_list
										)
									with Unif.Unification_failed -> ()
									)
								in
								List.iter for_all_candidates unif_candidates in
							List.iter for_all_sel_lit current_select_lits
						)
				done
			)
		with
			Inference_rules.Main_subsumed_by (by_conclusion) ->
				(
					incr_int_stat 1 res_forward_subsumption_resolution;
					add_conclusion_to_passive main_clause by_conclusion)
	
	(*-----------------------Adaptive Selection Loop Body----------------------*)
	
	let rec discount_change_sel_loop_body () =
		incr_int_stat 1 res_num_of_loops;
		try
		(* let clause = PassiveQueue.maximum !(passive_queue_ref) in
		passive_queue_ref := PassiveQueue.remove !(passive_queue_ref);*)
			let clause = remove_from_passive () in
		(*	out_str ("Discount: removed form passive: "^(Clause.to_string clause)^"\n"); *)
			
			if ((Clause.get_is_dead clause) ||
				(Clause.get_ps_in_active clause))
			then ()  (* (out_str ("is dead or in active"^(Clause.to_string clause)^"\n");) *)
			else
				(
					let clause_for_inferences =
						(if (not (Clause.res_sel_is_def clause))
							then (* clause is "new" *)
							(
								let (feature_list, given_clause) = all_simplifications clause in
								let _ = Selection.change_sel given_clause in
								(* alternatively one can add all newly generated to subsumption also  *)
								add_to_subsumption_index feature_list given_clause;
								(* exchange with instantiation*)
								add_active_to_exchange given_clause;
								given_clause
							)
							else clause)							
					in
					(
					(*	out_str ("Clause for inf: "^(Clause.to_string clause_for_inferences)^"\n"); *)
						resolution_change_sel clause_for_inferences;
						if (Clause.get_ps_sel_max clause_for_inferences)
						then (* we need factoring only with max selected *)
						all_factorings clause_for_inferences
						else());
					let selected_lits =
						(try (Clause.get_res_sel_lits clause_for_inferences)
						with Clause.Res_sel_lits_undef ->
								failwith
									"discount_change_sel_loop_body: sel lit should be def. here \n ")
					in
					add_to_unif_index clause_for_inferences selected_lits;
					Clause.set_ps_in_active true clause_for_inferences;
					incr_int_stat 1 res_num_in_active;
					
				(*	out_str ("given_clause: "^(Clause.to_string clause_for_inferences)
							^" selected lit: "
							^(Term.term_list_to_string selected_lits));
				*)
				)
		
		(* out_str_debug
		("\n In Active: "^(Clause.to_string given_clause)) *)
		(* else () *)
		
		with
		
		| Eliminated -> ()
		| Given_clause_is_dead -> ()
		(* out_str "\n Given_clause_is_dead \n" *)
		
		| Passive_Empty -> 
			(
			 (* out_str ("Satisfiable context\n\n");
			context_iter !context (fun c -> out_str ((Clause.to_string c)^"\n")); 
			*)
			raise (Satisfiable !context)
    	)
		
	(* replaced by discount_loop_exchange
	let discount_loop () =
	while true do
	(match !current_options.res_sel_fun with
	| Res_Adaptive ->
	discount_change_sel_loop_body ()
	| _ ->
	discount_loop_body ()
	)
	done
	*)
	
	(*let init_discount input_clauses = *)
	
	(* Old
	
	(* for combination with e.g. instantiation *)
	(* if we add eq. axioms than we need to use this*)
	let init_discount_input_clauses input_clauses =
	(* need to copy clauses if combine with instantiation *)
	let renew_clauses_in_init clause =
	let new_clause = Clause.create (Clause.get_literals clause) in
	(Clause.inherit_param_modif clause new_clause;
	Clause.inherit_bool_param Clause.in_prop_solver clause new_clause;
	Clause.inherit_history clause new_clause;
	new_clause)
	in
	let new_input = (List.map renew_clauses_in_init input_clauses) in
	let add_clause clause =
	add_new_clause_to_passive clause
	in
	List.iter add_clause new_input
	(*debug*)
	(* let tmp_cl = Clause.create ([Parsed_input_to_db.bot_term]) in
	add_clause tmp_cl;
	let f cl = out_str "\nbot term is finalised!\n" in
	Gc.finalise f tmp_cl *)
	*)
	
	let init_discount () =
	(*	out_str "\n init_discount\n"; *)
		
		let add_input_to_passive clause =
	
		  let copied_clause = Clause.copy_clause clause in
	  	 let new_clause = context_add !context copied_clause in
			
			(* when_born is 0 *)
		(*	Clause.clear_proof_search_param new_clause; *)
			(* replace with replacing dead with implied *)
			Clause.assign_is_dead false new_clause;
			Clause.assign_ps_when_born 0 new_clause;
			(* out_str ("\n Added: "^(Clause.to_string new_clause)^"\n"); *)
			add_new_clause_to_passive new_clause
		in
		List.iter add_input_to_passive input_clauses
	
	let _ = init_discount ()
	
	(* for combination with e.g. instantiation, runs disount loop once *)
	(* and returns new clauses in exchanege  *)
	(* can raise Satisfiable, Unsatisfiable *)
	let discount_loop_exchange () =
		(match !current_options.res_lit_sel with
			| Res_Adaptive ->
					discount_change_sel_loop_body ();
			| _ ->
					discount_loop_body ()
		);
		check_disc_time_limit ()
	
	(*------------*)
	(*
	let start_discount input_clauses =
	init_discount_input_clauses input_clauses;
	(* ClauseAssignDB.iter add_caluse !init_clause_db_ref; *)
	(* out_str_debug "initial clauses are added to passive \n";*)
	discount_loop_exchange ()
	
	*)
	
	(* unassigns all structures related to discount and runs GC.full_major*)
	let clear_all () =
		
		(* a trick to keep old value of functional statistics*)
		(* like number of clauses and number in passive*)
		
		let num_in_passive = (get_val_stat_fun res_num_in_passive) in
		assign_fun_stat
			(fun () -> num_in_passive)
			res_num_in_passive;
		
		let num_of_clauses = (get_val_stat_fun res_num_of_clauses) in
		assign_fun_stat
			(fun () -> num_of_clauses)
			res_num_of_clauses;
		
		(* init_clause_list_ref :=  [];*)
		(* out_str "Memory Before discount Gc\n";
		Gc.print_stat stdout;*)
		
		clean_passive ();
		ss_index_ref := (SubsetSubsume.create ());
		subsumption_index_ref := (SubsumptionIndexM.create ());
		unif_index_ref := (DiscrTreeM.create ());
		
	  context_iter !context Clause.clear_clause; 

		res_context_reset ();
	(* Memory is cleared separately by Lib.clear_mem ()*)
	
	(*;
	out_str "\n--------------------\n";
	Gc.print_stat stdout;
	out_str "Memory After discount Gc\n" *)
	(*; Gc.compact ()*)
	
	(*-----------------End--------------------------*)
end

(* -------------------Commented--------------*)
(*
(* various debug tests*)

(*matching test*)
let iter_all_pairs_of_trems f =
let g term =
TermDB.iter (f term) !term_db_ref in
TermDB.iter g !term_db_ref

let try_matching t1 t2 =
try
let subst = Unif.matches t1 t2 in
out_str_debug
((Term.to_string t1)
^"Matches "
^(Term.to_string t2)^"\n"
^"  with subst: "^(Subst.to_string subst)^"\n" )
with
Unif.Matching_failed ->
out_str_debug
((Term.to_string t1)
^" NOT Matches "
^(Term.to_string t2)^"\n")

let try_matching_all () =
iter_all_pairs_of_trems try_matching;
out_str_debug "Matching finished \n"

(**subsumption test*)
let iter_all_pairs_of_clauses f =
let f' cl =
ClauseAssignDB.iter (f cl) !clause_db_ref in
ClauseAssignDB.iter f' !clause_db_ref

let try_subsumption c1 c2 =
try
let subst = Unif.subsumes c1 c2 in
out_str_debug
((Clause.to_string c1)
^"Subsumes "
^(Clause.to_string c2)^"\n"
^"  with subst: "^(Subst.to_string subst)^"\n" )
with
Unif.Subsumtion_failed ->
out_str_debug
((Clause.to_string c1)
^" NOT Subsumes "
^(Clause.to_string c2)^"\n")

let try_subsumption_all () =
out_str_debug "start adding init cl to passive\n";
let num_of_symb = SymbolDB.size !symbol_db_ref in
let add_clause clause =
out_str_debug ("Adding init cl to passive: "^(Clause.to_string clause)^"\n");
add_new_clause_to_passive clause;
SubsumptionIndexM.add_clause
(get_feature_list clause) clause subsumption_index_ref
in
List.iter add_clause !init_clause_list_ref;
out_str_debug "initial clauses are added to passive and subsumtion index\n";
ClauseAssignDB.iter
(fun c -> out_str_debug ("Clause in db: "^(Clause.to_string c)^"\n"))
!clause_db_ref ;
iter_all_pairs_of_clauses try_subsumption
(* uncomment for index subsumption
let try_forward_subs clause =
( match
(SubsumptionIndexM.is_subsumed
(get_feature_list clause) clause subsumption_index_ref)
with
| Some((subsumer, subst)) ->
out_str_debug
("Clause"^(Clause.to_string clause)^" is subsumed by "
^(Clause.to_string subsumer)^"\n")
| None ->
out_str_debug
("Clause"^(Clause.to_string clause)^" can not be subsumed \n")
) in
ClauseAssignDB.iter try_forward_subs !clause_db_ref
*)

*)    (* End Comment for tests*)

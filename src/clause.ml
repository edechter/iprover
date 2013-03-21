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
open Hashcons
open Options
module VSet = Var.VSet

type var = Var.var
type bound_var = Var.bound_var
type term = Term.term
type bound_term = Term.bound_term
type term_db = TermDB.termDB
type term_db_ref = term_db ref
type subst = Subst.subst
type bound = int
type bound_subst = SubstBound.bound_subst
type symbol = Symbol.symbol
(*type dismatching = Dismatching.constr_list_feature *)
type dismatching = Dismatching.constr_set

module SymSet = Symbol.Set
type sym_set = Symbol.sym_set

type literal = Term.literal
type literal_list = literal list
type b_litlist = literal_list bind
type lit = literal
type lits = lit list

exception Term_compare_greater
exception Term_compare_less


let clause_counter = ref 0 
let incr_clause_counter () =  (clause_counter := !clause_counter+1)


(* all boolean param of a clause stored in a bit vector (should be in 0-30 range)*)
(* position of the param in the vector *)
(*------------Clause bool param----------------*)
type clause_bool_param = int

(*-------Basic clause bool Param-----*)
(* auto parameters set automatically when clause is created from lits*)
(* user parameters are set by the user *)
let bc_ground = 0   (* auto *)
let bc_horn = 1     (* auto *)
let bc_epr = 2      (* auto *)
let bc_eq_axiom = 3 (* user *)

(* input_under_eq  is true if a clause is (i) is a eq axiom or (ii) input   *)
(* or (iii) obtained from input by some number of inferences with eq axioms *)
(* so it is false for a cluase  obtained by an inference with two clauses   *)
(* which are both non equality *)
(* not used at the moment; may be in the future                             *)
(* let bc_input_under_eq = 4 *)

let bc_has_eq_lit = 4    (* auto *)
let bc_has_conj_symb = 5 (* auto *) (* basd on Term.has_conj_symb *)
let bc_has_non_prolific_conj_symb = 6 (* auto *)

let bc_has_bound_constant = 7 (* auto *)
let bc_has_next_state = 8 (* auto *)
let bc_has_reachable_state = 9 (* auto *)
(*let bc_large_ax_considered = 10 (* auto *) not used at the moment *)
let bc_is_negated_conjecture = 11 (* user *) (* TODO: change in the rest of the code! *)

(*----------clause context bool paramters-----------*)

(* context paramters are set outside of reasoning processes *)

let ccp_is_dead = 0  (* user *)
(* ccp_is_dead true the the clause is replaced in a context and replaced by other clauses *)
(* invariant: set of (not ccp_is_dead) clauses imply the set of all clauses in the context *)
let cpp_in_prop_solver = 1 (* user *)

let ccp_in_unsat_core = 2 (* user *)

 (* clause was in unsat core in the last proof search run *)
(* used in bmc1 *)
(*--------proof search bool params --------------------------*)
(*--------common params for most proof search will be prefixed by ps--*)

(*-------- param common for other  ------------*)

(*let inst_is_dead = 0 *)
let ps_in_active = 1
let ps_in_unif_index = 2
let ps_in_subset_subsumption_index = 3
let ps_in_subsumption_index = 4
(*let inst_in_prop_solver = 5 *)
let ps_in_sim_passive = 5
let ps_pass_queue1 = 6
let ps_pass_queue2 = 7
let ps_pass_queue3 = 8

(*-----------Res bool parm----------*)
let ps_sel_max = 9

(* if used in simplifications then simplifying is true                            *)
(* used in orphan elimination since we can eliminate only non-simplifying cluases *)
let ps_simplifying = 10

(*----no specific for inst bool param ----*)

(*--------End Bool param------------------*)

(*-----------------*)
(* 1) basic clauses are difined by thier literals and all basic_clauses are globally shared                      *)
(* 2) basic_clauses are used only to define (context) clauses   and should not be used outside of this module *)
(* 3) a (context) clause is an extension of a basic clause with extra paramters including tstp source for proofs and  *)
(*    paramteres used in a process such proof search in inst/res/etc or preprocessing *)
(* 4) context clauses are indexed by basic clauses (so there is no two clauses with the same basic_clause in a contex) *)
(*    but clauses can have different parametes in different contexts  *)
(* 5) for proof reconstruction we are using one propositional solver so if a clauses was added to a uc_solver *)
(*    then later a clause with the same basic clause is never added  *)
(*    this may result in proof mixing contexts but should not be a problem *)
(* 6) in a clause context parameters can be reassigned inplace without switching clause to a new context *)
(*    thus sequantially the same context can be used for any number of inst/res cycles  *)
(*    we need to copy a clause to another context only if simultaniously the same basic clause is used in more than one place *)

type basic_clause =
	basic_clause_node hash_consed
and
basic_clause_node =
	{
		lits : literal_list;
		mutable bc_bool_param : Bit_vec.bit_vec;
		mutable length : int;	(* number of all symbols in literals *)
		mutable num_of_symb : int;
		mutable num_of_var : int;
		mutable min_defined_symb : int param; (* minimal defined symbols *)
		mutable max_atom_input_occur : symbol param;
	}

type sel_place = int


(*------------------------------------------------------------------------------*)
(* in a given context there is at most one clause with the same by basic_clause *)
(* we can create any number of the same contexts: Inst/Res/Empty                *)
(* the same basic clause can have different proofs in different contexts        *)
(* proofs can havecontext dependand usage e.g.  deleting all parents of a simplified clause in a context may not be applicable in another context) *)

(* clause_with_context = clause *)
type clause =
	{
		basic_clause : basic_clause;
		mutable fast_key : int;    (* unique id  based on clause_counter *)
(*  mutable context_id : int; *)  (* clause is identified by context_id and fast_id *)
		mutable tstp_source : tstp_source param;
		
(* replaced_by invariants : *)
(* 1) in a context we can replace all clauses by replaced_by obtaining an equisat set of clauses *)
(* 2) there is no cycles when following replaced_by *)	
		mutable replaced_by : replaced_by param;

		mutable prop_solver_id : int option; (* prop_solver_id is used in uc_solver for djoining special literls for unsat cores/proof recontruction*)
		mutable conjecture_distance : int; (* can be changed when tstp_source is reassigned *)
		mutable proof_search_param : proof_search_param;  (* we can reassign clause paramters within the same context *)
		mutable ccp_bool_param : Bit_vec.bit_vec;
	}

(* clause parameters can contain clauses themselves like inst_children *)
and proof_search_param =
	{
		(* shared paramtes *)
		mutable ps_bool_param : Bit_vec.bit_vec;
	  mutable ps_when_born : int param;
		mutable ps_children : clause list;

   (* inst params *)
		mutable inst_sel_lit : (term * sel_place) param;
		mutable inst_dismatching : dismatching param;
		mutable inst_activity : int;

	(* res params *)	
 	 mutable res_sel_lits : literal_list param;
	}


and replaced_by = 
	(* when clause got replaced we record the clauses which is got replaced by *)
	(* assumption are: 1) orginal cluase logically follows from the simplifed_by cluases *)
	(* in particular we can replace the original clause by replaced_by clauses *)
	(* there is no cyclic simplification depdendences; we can recover the leaf replacing clauses*)
	(*  which are not replaced *)
	| RB_subsumption of clause
	| RB_sub_typing of clause
	| RB_splitting of clause list  


(*-------tstp_source-----------*)
(*
and axiom =
	| Eq_Axiom
	| Distinct_Axiom
	| Less_Axiom
	| Range_Axiom
	| BMC1_Axiom
*)
and tstp_internal_source =
	| TSTP_definition
	| TSTP_assumption

and tstp_theory_bmc1 =
	| TSTP_bmc1_path_axiom of int
	| TSTP_bmc1_reachable_state_axiom of int
	| TSTP_bmc1_reachable_state_conj_axiom of int
	| TSTP_bmc1_reachable_state_on_bound_axiom of int
	| TSTP_bmc1_reachable_sk_replacement of int * clause  (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)
	| TSTP_bmc1_only_bound_reachable_state_axiom of int
	| TSTP_bmc1_clock_axiom of int * Symbol.symbol * (int list)
	| TSTP_bmc1_instantiated_clause of int * clause

and tstp_theory =
	| TSTP_equality
	| TSTP_distinct
	| TSTP_domain 
	| TSTP_bmc1 of tstp_theory_bmc1
	| TSTP_less
	| TSTP_range

and tstp_external_source =
	| TSTP_file_source of string * string
	| TSTP_theory of tstp_theory

and tstp_inference_rule =
	| Instantiation of clause list (* side clauses *)
	| Resolution of literal list
	| Factoring of literal list
	| Global_subsumption of int
	| Forward_subsumption_resolution
	| Backward_subsumption_resolution
	| Splitting of symbol list
	| Grounding of (var * term) list
	| Non_eq_to_eq
	| Subtyping
	| Flattening

and tstp_inference_record =
	tstp_inference_rule * clause list

and tstp_source =
	| TSTP_external_source of tstp_external_source
	| TSTP_internal_source of tstp_internal_source
	| TSTP_inference_record of tstp_inference_record

(*--------------Consing hash tables--------------------------*)


(* basic clause hash table *)
(* Key for consing table *)
module BClause_Node_Key =
struct
	type t = basic_clause_node
	let equal c1 c2 =
		try
			List.for_all2 (==) c1.lits c2.lits
		with
			Invalid_argument _ -> false
	let hash c = hash_list Term.hash c.lits
	(* alternative equal *)
	(*	let compare =
	list_compare_lex Term.compare cl1.literals cl2.literals
	let equal c1 c2 =
	if (compare c1 c2) =0
	then true
	else false
	
	*)
end

module BClause_Htbl = Hashcons.Make(BClause_Node_Key)

(*---------------------------------------------*)
(* clause db which contains all basic clauses *)

let basic_clause_db = BClause_Htbl.create 50821  (* a midium size prime *)
let add_bc_node bc_node = BClause_Htbl.hashcons basic_clause_db bc_node

(*---------------------------*)


(*-----------------------------------------*)

type bound_clause = clause Lib.bind

type bound_bclause = basic_clause Lib.bind

let get_bclause c =
	c.basic_clause

let get_bc = get_bclause (* shorthand *)

(* fast_key is unique for each generated clause  *)
let get_fast_key c = c.fast_key

(* lits_fast_key is the basic_clause rather than basic_clause.tag since if we use tag basic clause may be removed *)
(* by weak table since no refernce will be held *)
(*  unique for each literal list *)


let get_lits_fast_key c = c.basic_clause
let get_lits_hash c = c.basic_clause
let lits_compere c1 c2 = Pervasives.compare c1.tag c2.tag
let lits_equal c1 c2 =  c1.basic_clause == c2.basic_clause
 
(* let get_context_id c = c.context_id *)
	
(*-----------------------------------------*)
let compare_basic_clause c1 c2 =
	Pervasives.compare c1.tag c2.tag

let equal_basic_clause = (==)

(*
let compare_clause c1 c2 =
	pair_compare_lex
		Pervasives.compare
		Pervasives.compare
		((get_fast_key c1), (get_context_id c1))
		((get_fast_key c2), (get_context_id c2))
*)

let compare_clause c1 c2 =
	Pervasives.compare (get_fast_key c1) (get_fast_key c2)

let equal_clause = (==)

let equal = equal_clause

let compare = compare_clause 

let compare_lits c1 c2 = compare_basic_clause (get_bc c1) (get_bc c2)

let equal_lits c1 c2 =  equal_basic_clause (get_bc c1) (get_bc c2) 


(*---------- filling Bool params of a basic clause ----------------------------*)

let set_bool_param_bc value param bclause =
	bclause.node.bc_bool_param <- Bit_vec.set value param bclause.node.bc_bool_param

let get_bool_param_bc param bclause =
	Bit_vec.get param bclause.node.bc_bool_param

(*----------*)
let is_ground_lits lits =
	let is_not_ground lit = not (Term.is_ground lit) in
	not (List.exists is_not_ground lits)

let is_ground_bc c = (get_bool_param_bc bc_ground c)

(*----------*)
let is_horn_lits lits =
	let num_pos = ref 0 in
	let rec is_horn_check' lits =
		match lits with
		| h :: tl ->
				if not (Term.is_neg_lit h)
				then
					if !num_pos >= 1
					then false
					else
						(num_pos := !num_pos +1;
							is_horn_check' tl
						)
				else
					is_horn_check' tl
		|[] -> true
	in
	is_horn_check' lits

let is_horn_bc c = (get_bool_param_bc bc_horn c)

(*-----------*)

let is_epr_lits lits =
	let is_not_epr lit = not (Term.is_epr_lit lit) in
	not (List.exists is_not_epr lits)

let is_epr_bc c = (get_bool_param_bc bc_epr c)

(*----------*)
let has_eq_lit_lits lits =
	(List.exists Term.is_eq_lit lits)

let has_eq_lit c = (get_bool_param_bc bc_has_eq_lit c)

(*--------from term params to lits param-------------------------*)

let exists_lit_with_true_bool_param term_bool_param lits =
	List.exists (Term.get_fun_bool_param term_bool_param) lits

let has_conj_symb_lits lits =
	exists_lit_with_true_bool_param Term.has_conj_symb lits

let has_non_prolific_conj_symb_lits lits =
	exists_lit_with_true_bool_param Term.has_non_prolific_conj_symb lits

let has_bound_constant_lits lits =
	exists_lit_with_true_bool_param Term.has_bound_constant lits

let has_next_state_lits lits =
	List.exists Term.is_next_state_lit lits

let has_reachable_state_lits lits =
	List.exists Term.is_reachable_state_lit lits

(*----------------------------------*)
  
  
(*----------------------------------*)
let length_lits lits = List.length lits

let num_of_symb_lits lits =
	let f rest term = rest + (Term.get_num_of_symb term) in
	List.fold_left f 0 lits

let num_of_var_lits lits =
	let f rest term = rest + (Term.get_num_of_var term) in
	List.fold_left f 0 lits

let max_atom_input_occur_lits lits =
	let get_symb lit =
		let atom = Term.get_atom lit in
		match atom with
		| Term.Fun(symb, _, _) -> symb
		| _ -> failwith "assign_max_atom_input_occur should not be var"
	in
	let cmp lit1 lit2 =
		let symb1 = get_symb lit1 in
		let symb2 = get_symb lit2 in
		Pervasives.compare
			(Symbol.get_num_input_occur symb1) (Symbol.get_num_input_occur symb2) in
	let max_atom_input_occur = get_symb (list_find_max_element cmp lits) in
	max_atom_input_occur

(* defined depth -> circuit_depth *)
let min_defined_symb_lits lits =
	let cmp_lit l1 l2 =
		let d1 = Symbol.get_defined_depth (Term.lit_get_top_symb l1) in
		let d2 = Symbol.get_defined_depth (Term.lit_get_top_symb l2) in
		match (d1, d2) with
		| (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
		
		(* changed to the opposite since spliting symbols by vapi become big!
		(* Undef is greater then Def *)
		| (Undef, Def _) -> 1
		| (Def _, Undef) -> -1
		*)
		| (Undef, Def _) -> -1
		| (Def _, Undef) -> 1
		| (Undef, Undef) -> 0
	in
	let min_lit = list_find_min_element cmp_lit lits in
	let min_d = Symbol.get_defined_depth (Term.lit_get_top_symb min_lit) in
	min_d

(*--------------------------------------------------------------*)
type 'a bool_param_fill_list = (('a -> bool) * int) list

(* obj is an argument of the fill_list, can be anythig usually lit_lits *)

let fill_bool_params fill_list obj bit_vector =
	List.fold_left (fun curr_bv (curr_fun, bv_param) -> Bit_vec.set (curr_fun obj) bv_param curr_bv) bit_vector fill_list

(* auto fill bit-vector params should be added here *)
let auto_bool_param_fill_list =
	[
	(is_ground_lits, bc_ground);
	(is_horn_lits, bc_horn);
	(is_epr_lits, bc_epr);
	(has_eq_lit_lits, bc_has_eq_lit);
	(has_conj_symb_lits, bc_has_conj_symb);
	(has_non_prolific_conj_symb_lits, bc_has_non_prolific_conj_symb);
	(has_bound_constant_lits, bc_has_bound_constant);
	(has_next_state_lits, bc_has_next_state);
	(has_reachable_state_lits, bc_has_reachable_state);
	(*  (is_negated_conjecture_lits, bc_is_negated_conjecture);		*) (* not auto but user fill*)
	]

(* can be dangerous since options are redefined after schedules take place; but clauses added during parsing*)
(* can make definite exclusion list when we do not use cicuit topology
let defined_symb_enabled_check () =
!current_options.bmc1_incremental || !current_options.schedule = Options.verification_epr
*)

(* us to check whether the clause is in the *)
let template_bc_node lits =
	{
		lits = lits;
		bc_bool_param = Bit_vec.false_vec;
		length = 0;
		num_of_symb = 0; 	(* number of all symbols in literals *)
		num_of_var = 0;
		max_atom_input_occur = Undef; 	(* minial defined symbols *)
		min_defined_symb = Undef;
	}

(* auto fill non bit-vector params should be added here *)
let fill_bc_auto_params bc_node =
	let auto_bool_param = fill_bool_params auto_bool_param_fill_list bc_node.lits Bit_vec.false_vec in
	let lits = bc_node.lits in
	bc_node.bc_bool_param <- auto_bool_param;
	bc_node.length <- length_lits lits;
	bc_node.num_of_symb <- num_of_symb_lits lits;
	bc_node.num_of_var <- num_of_var_lits lits;
	bc_node.max_atom_input_occur <- Def(max_atom_input_occur_lits lits);
	bc_node.min_defined_symb <- min_defined_symb_lits lits

let create_basic_clause lits =
	let template_bc_node = template_bc_node lits in
	let added_bc = add_bc_node template_bc_node in
	let new_bc =
		(if (added_bc.node == template_bc_node) (* there was no copy in clause cons *)
			then
				(
					fill_bc_auto_params added_bc.node;
					added_bc
				)
			else (* there was a bc clause with these lits; so we just return it*)
			added_bc
		)
	in
	new_bc

(*
let is_negated_conjecture clause =
clause.conjecture_distance = conjecture_int
*)

(*---------------end basic clause-----------------------*)



(*------------------*)

let get_lits c = c.basic_clause.node.lits 
let get_literals = get_lits	
		
let compare_lits c1 c2 =
	list_compare_lex Term.compare (get_lits c1) (get_lits c2)

let is_empty_clause c =
	if (get_lits c) = [] then true
	else false


(*------------output: to stream/string to_tptp is later due to dependences on getting parameters------------*)

let to_stream s clause =
	s.stream_add_char '{';
	(list_to_stream s Term.to_stream (get_lits clause) ";");
	s.stream_add_char '}'

let out = to_stream stdout_stream

let to_string =
	to_string_fun_from_to_stream_fun 100 to_stream

let clause_list_to_stream s c_list =
	list_to_stream s to_stream c_list "\n"

let out_clause_list = clause_list_to_stream stdout_stream

let clause_list_to_string =
	to_string_fun_from_to_stream_fun 300 clause_list_to_stream

(*
let to_string clause =
"{"^(list_to_string Term.to_string clause.literals ";")^"}" (*^"\n"*)
*)

(*-------------------------------*)
exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

let assign_prop_solver_id c id =
	match c.prop_solver_id with
	| None -> c.prop_solver_id <- Some (id)
	| Some _ -> raise Clause_prop_solver_id_is_def

let get_prop_solver_id clause = clause.prop_solver_id

(*-------------------------------*)

(*
let assign_tstp_source tstp_source c =
	c.node.tstp_source <- tstp_source

let get_tstp_source c =	c.node.tstp_source


*)



(*-----------------------------------------*)
(*
let axiom_to_string axiom =
	match axiom with
	| Eq_Axiom -> "Equality Axiom"
	| Distinct_Axiom -> "Distinct Axiom"
	| Less_Axiom -> "Less Axiom"
	| Range_Axiom -> "Range Axiom"
	| BMC1_Axiom -> "BMC1 Axiom"
*)
(*
let pp_axiom ppf = function
	| Eq_Axiom -> Format.fprintf ppf "Equality Axiom"
	| Distinct_Axiom -> Format.fprintf ppf "Distinct Axiom"
	| Less_Axiom -> Format.fprintf ppf "Less Axiom"
	| Range_Axiom -> Format.fprintf ppf "Range Axiom"
	| BMC1_Axiom -> Format.fprintf ppf "BMC1 Axiom"
*)

(*----------------------------*)
let get_node c = c.node

let get_bc c = c.basic_clause
	
let get_bc_node c = c.basic_clause.node

let equal_bc c1 c2 = (get_bc c1) == (get_bc c2)

(* 
let compare_in_context c1 c2 = Pervasives.compare c1.tag c2.tag

let compare_globally c1 c2 = 
	pair_compare_lex
		Pervasives.compare
		Pervasives.compare
    (c1.tag, c1.node.context_id)
		(c2.tag, c2.node.context_id)

let compare = compare_globally	

(* clauses with the same literals but in different contexts are not equal*)
let equal = (==)

(* clauses with the same literals are equal_bc *)
let equal_bc c1 c2 = (get_bc c1) == (get_bc c2)
*)


(*--------------------*)
let memq lit clause = List.memq lit (get_lits clause)
let exists p clause = List.exists p (get_lits clause)
let find p clause = List.find p (get_lits clause)
let fold f a clause = List.fold_left f a (get_lits clause)
let find_all f clause = List.find_all f (get_lits clause)
let partition f clause = List.partition f (get_lits clause)
let iter f clause = List.iter f (get_lits clause)


				
(*----------------------------------------------------*)


(*---------------------------------------------------------*)
let bc_set_bool_param value param clause =
	let bc = get_bc_node clause in
	bc.bc_bool_param <- Bit_vec.set value param bc.bc_bool_param

let bc_get_bool_param param clause =
	Bit_vec.get param (get_bc_node clause).bc_bool_param

(*------------- *)
let ccp_get_bool_param param clause = 
	Bit_vec.get param clause.ccp_bool_param

let ccp_set_bool_param value param clause =
	clause.ccp_bool_param <- Bit_vec.set value param clause.ccp_bool_param


(*--------clause bc params get/assign -------------*)

let is_negated_conjecture c = 
	bc_get_bool_param bc_is_negated_conjecture c 

let is_ground c =
	bc_get_bool_param bc_ground c

let is_horn c =
	bc_get_bool_param bc_horn c
	
let is_epr c =
	bc_get_bool_param bc_epr c
	
let is_eq_axiom c = 
	bc_get_bool_param bc_eq_axiom c

let assign_is_eq_axiom value c = (* user *) (* assign only for user parameters *)
 set_bool_param_bc value bc_eq_axiom (get_bc c)
																														
let has_eq_lit c =
  bc_get_bool_param bc_has_eq_lit c

let has_conj_symb c =
	bc_get_bool_param bc_has_conj_symb c
	
let has_non_prolific_conj_symb c = 
	bc_get_bool_param bc_has_non_prolific_conj_symb c
		
let has_bound_constant c = 
	bc_get_bool_param bc_has_bound_constant c

let has_next_state c = 
	bc_get_bool_param bc_has_next_state c
		
let has_reachable_state c = 
	bc_get_bool_param bc_has_reachable_state c 
	
let num_of_symb c =
	let bc_node = get_bc_node c in
	bc_node.num_of_symb
	
let num_of_var c =
	let bc_node = get_bc_node c in
	bc_node.num_of_var
	
let length c =
	let bc_node = get_bc_node c in
	bc_node.length	
	
(* int param *)	
let get_max_atom_input_occur c = 
	let bc_node = get_bc_node c in
	bc_node.max_atom_input_occur

(* symb param*)	
let	get_min_defined_symb c =
	let bc_node = get_bc_node c in
	bc_node.min_defined_symb

	
(*------clause params get/assign------*)


let assign_tstp_source c tstp_source =
	match c.tstp_source with
	| Def _ -> raise (Failure "Clause source already assigned")
	| Undef -> c.tstp_source <- Def(tstp_source)

let get_tstp_source c =	
	match c.tstp_source with 
	| Def (tstp_source) -> tstp_source 
	| Undef -> failwith ("tstp_source is not defined for clause: "^(to_string c))

(*let get_context_id c = c.node.context_id*)

(*
let assign_context_id id c = 
	c.context_id <- id
*)

let get_replaced_by c = 
	c.replaced_by
	
let assign_replaced_by sby c = 
		c.replaced_by <- sby
		
let get_conjecture_distance c = 
		c.conjecture_distance

let assign_conjecture_distance d c = 
  c.conjecture_distance <- d

let inherit_conj_dist from_c to_c =
	to_c.conjecture_distance <- from_c.conjecture_distance




(*------ccp bool params get/assign-------*)
let get_is_dead c = 
	ccp_get_bool_param ccp_is_dead c
	
let assign_is_dead b c = 
	ccp_set_bool_param b ccp_is_dead c 

let in_unsat_core c = 
	ccp_get_bool_param ccp_in_unsat_core c

let assign_in_unsat_core b c = 
  ccp_set_bool_param b ccp_in_unsat_core c

let in_prop_solver c = 
	 ccp_get_bool_param cpp_in_prop_solver c

let assign_in_prop_solver b c = 
	ccp_set_bool_param b cpp_in_prop_solver c



(*-----proof search params-------*)

(*--------------------------------*)

let create_ps_param () =
	{
		ps_bool_param = Bit_vec.false_vec;
	  ps_when_born = Undef;
	  ps_children = [];

   (* inst params *)
		inst_sel_lit = Undef;
		inst_dismatching = Undef;
		inst_activity = 0;

	(* res params *)	
 	 res_sel_lits = Undef;
}


(*----------------*)
		
let get_proof_search_param c = 	c.proof_search_param
let get_ps_param = get_proof_search_param

let clear_proof_search_param c = c.proof_search_param <- (create_ps_param ())
			
let get_ps_bv_param c =  	 
	let ps_param = get_ps_param c in 
  ps_param.ps_bool_param
	 
let get_ps_bool_param param c = 
	let bv = get_ps_bv_param c in
	Bit_vec.get param bv


		
let set_ps_bool_param value param c = 
	let ps_param = get_ps_param c in 
	 ps_param.ps_bool_param <- Bit_vec.set value param ps_param.ps_bool_param
	
	
(*---res non-boolean param--*)	
let get_ps_when_born c =
	let ps_param = get_ps_param c in
	match ps_param.ps_when_born with
	| Def(n) -> n
	| Undef ->
			(
				let fail_str = "Clause: res_when_born is undef for "^(to_string c) in
				failwith fail_str
			)
let assign_ps_when_born i c =
	let ps_param = get_ps_param c in
	ps_param.ps_when_born <- Def(i) 
			
let res_assign_sel_lits sel_lits clause =
	let ps_param = get_ps_param clause in
	ps_param.res_sel_lits <- Def(sel_lits)

let res_sel_is_def clause =
 let ps_param = get_ps_param clause in
	match ps_param.res_sel_lits with
	| Def(_) -> true
	| Undef -> false
	
exception Res_sel_lits_undef
let get_res_sel_lits clause =
	let ps_param = get_ps_param clause in
	match ps_param.res_sel_lits with
	| Def(sel_lits) -> sel_lits
	| Undef -> raise Res_sel_lits_undef
 


let get_ps_in_active c = get_ps_bool_param ps_in_active c
let set_ps_in_active v c = set_ps_bool_param v ps_in_active c

let get_ps_in_unif_index c = get_ps_bool_param ps_in_unif_index c
let set_ps_in_unif_index v c = set_ps_bool_param v ps_in_unif_index c

let get_ps_in_subset_subsumption_index c = get_ps_bool_param ps_in_subset_subsumption_index c
let set_ps_in_subset_subsumption_index v c = set_ps_bool_param v ps_in_subset_subsumption_index c

let get_ps_in_subsumption_index c = get_ps_bool_param ps_in_subsumption_index c
let set_ps_in_subsumption_index v c = set_ps_bool_param v ps_in_subsumption_index c

let get_ps_in_sim_passive c = get_ps_bool_param ps_in_sim_passive c
let set_ps_in_sim_passive v c = set_ps_bool_param v ps_in_sim_passive c

let get_ps_pass_queue1 c = get_ps_bool_param ps_pass_queue1 c
let set_ps_pass_queue1 v c = set_ps_bool_param v ps_pass_queue1 c

let get_ps_pass_queue2 c = get_ps_bool_param ps_pass_queue2 c
let set_ps_pass_queue2 v c = set_ps_bool_param v ps_pass_queue2 c

let get_ps_pass_queue3 c = get_ps_bool_param ps_pass_queue3 c
let set_ps_pass_queue3 v c = set_ps_bool_param v ps_pass_queue3 c

let get_ps_sel_max c = get_ps_bool_param ps_sel_max c
let set_ps_sel_max v c = set_ps_bool_param v ps_sel_max c

let get_ps_simplifying c = get_ps_bool_param ps_simplifying c
let set_ps_simplifying v c = set_ps_bool_param v ps_simplifying c



(*
let get_ c = ps_get_bool_param  c
let set_ v c = ps_set_bool_param v c
*)

(*

let get_ c = inst_get_bool_param  c
let set_ v c = inst_set_bool_param v c

let inst_in_active = 1
let inst_in_unif_index = 2
let inst_in_subset_subsumption_index = 3
let inst_in_subsumption_index = 4
 (* let inst_in_prop_solver = 5 *)
let inst_in_sim_passive = 6

let inst_pass_queue1 = 7
let inst_pass_queue2 = 8
let inst_pass_queue3 = 9
*)

(*
let get_inst_in_active c = inst_get_bool_param inst_in_active c
let set_inst_in_active v c = inst_set_bool_param v inst_in_active c

let get_inst_in_unif_index c = inst_get_bool_param inst_in_unif_index c
let set_inst_in_unif_index v c = inst_set_bool_param v inst_in_unif_index c

let get_inst_in_subset_subsumption_index c = inst_get_bool_param inst_in_subset_subsumption_index c
let set_inst_in_subset_subsumption_index v c = inst_set_bool_param v inst_in_subset_subsumption_index c

let get_inst_in_subsumption_index c = inst_get_bool_param inst_in_subsumption_index c
let set_inst_in_subsumption_index v c = inst_set_bool_param v inst_in_subsumption_index c

let get_inst_in_sim_passive c = inst_get_bool_param inst_in_sim_passive c
let set_inst_in_sim_passive v c = inst_set_bool_param v inst_in_sim_passive c

let get_inst_pass_queue1 c = inst_get_bool_param inst_pass_queue1 c
let set_inst_pass_queue1 v c = inst_set_bool_param v inst_pass_queue1 c

let get_inst_pass_queue2 c = inst_get_bool_param inst_pass_queue2 c
let set_inst_pass_queue2 v c = inst_set_bool_param v inst_pass_queue2 c

let get_ c = inst_get_bool_param  c
let set_ v c = inst_set_bool_param v c

let get_inst_pass_queue3 c = inst_get_bool_param inst_pass_queue3 c
let set_inst_pass_queue3 v c = inst_set_bool_param v inst_pass_queue3 c
*)

(*----inst non-boolean params -----------*)

exception Sel_lit_not_in_cluase
let rec inst_find_sel_place sel_lit lit_list =
	match lit_list with
	| h:: tl ->
			if (h == sel_lit) then 0
			else 1 + (inst_find_sel_place sel_lit tl)
	|[] -> raise Sel_lit_not_in_cluase

let inst_assign_sel_lit sel_lit clause =
	let sel_place = inst_find_sel_place sel_lit (get_lits clause) in
	let ps_param = get_ps_param clause in
	(* Format.eprintf
	"Selecting literal %s in clause (%d) %s@."
	(Term.to_string sel_lit)
	(match clause.fast_key with
	| Def key -> key
	| Undef -> -1)
	(to_string clause); *)
	ps_param.inst_sel_lit <- Def((sel_lit, sel_place))

let inst_assign_dismatching dismatching clause =
	let ps_param = get_ps_param clause in
	ps_param.inst_dismatching <- Def(dismatching)


exception Inst_sel_lit_undef
let inst_get_sel_lit clause =
	let ps_param = get_ps_param clause in
		match ps_param.inst_sel_lit with
	| Def((sel_lit, _)) -> sel_lit
	| Undef -> raise Inst_sel_lit_undef

(* should be changed dependeing on the tstp_source
exception Parent_undef
let get_parent clause =
	clause.parent
*)
	
(* match clause.parent with
| Def(p) -> p
| Undef -> raise Parent_undef *)

let inst_compare_sel_place c1 c2 =
	let c1_ps_param = get_ps_param c1 in
	let c2_ps_param = get_ps_param c2 in
	match (c1_ps_param.inst_sel_lit, c2_ps_param.inst_sel_lit) with
	| (Def((_, sp1)), Def((_, sp2)))
	-> Pervasives.compare sp1 sp2
	| _ -> raise Inst_sel_lit_undef

exception Dismatching_undef
let get_inst_dismatching clause =
	let ps_param = get_ps_param clause in
	match ps_param.inst_dismatching with
	| Def(dismatching) -> dismatching
	| Undef -> raise Dismatching_undef

let add_ps_child clause ~child =
	let ps_param = get_ps_param clause in
	ps_param.ps_children <- child:: (ps_param.ps_children)

let get_ps_children clause = 
	let ps_param = get_ps_param clause in
	ps_param.ps_children
	

let inst_get_activity clause = 
	let ps_param = get_ps_param clause in
	ps_param.inst_activity

let inst_assign_activity act clause = 
	let ps_param = get_ps_param clause in
	ps_param.inst_activity <- act

(*-------inst/res when born assignments--*)

(* assigns when the clause born based on when the clauses in the premise where born *)
(*                                    *)
(* if the the prem1 and prem2 is [] then zero is assined (e.g. imput clauses) *)
(* we assign when_born when 1) conclusion of an inference was generated       *)
(* 2) clause is replaced and 3) splitting 4)model transformation/equation axiom  *)
(* 5) it is an imput clause                                                   *)
(* in the case 1) we calculate when born of the conclusion as  *)
(* when_born=max(min(pem1),min(prem2)) + 1                     *)
(* case 4),5) we use assign_when_born prem1 [] [] clause       *)
(* is case 2),3) we use inherit  inherit_param_modif           *)

(* aux: if list is empty then 0 else max element*)


let list_find_max_element_zero comp l =
	try
		list_find_max_element comp l
	with Not_found -> 0

let ps_when_born_concl prem1 prem2 clause =
	let born_list1 = List.map get_ps_when_born prem1 in
	let born_list2 = List.map get_ps_when_born prem2 in
	let inv_compare = compose_sign false Pervasives.compare in
	(* finds min element *)
	let min_prem1 = list_find_max_element_zero inv_compare born_list1 in
	let min_prem2 = list_find_max_element_zero inv_compare born_list2 in
	let max_born = list_find_max_element Pervasives.compare [min_prem1; min_prem2] in
	let when_cl_born = max_born + 1 in
	when_cl_born

let assign_ps_when_born_concl ~prem1 ~prem2 ~c =
	let ps_param = get_ps_param c in
	ps_param.ps_when_born <- Def(ps_when_born_concl prem1 prem2 c)
	


(*--------------pp printing ------------------------------------*)
(* Print the name of a clause

Clauses are named [c_n], where [n] is the identifier (fast_key) of
the clause. If the identifier is undefined, the clause is named
[c_tmp].
*)
let pp_clause_name ppf clause = 
	Format.fprintf ppf "c_%d" (*(get_context_id clause)*) (get_fast_key clause)

let pp_clause_with_id ppf clause =
	Format.fprintf
		ppf
		"(%d) {%a}"
		(*(get_context_id clause)*)
		(get_fast_key clause)
		(pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause ppf clause =
	Format.fprintf
		ppf
		"@[<h>{%a}@]"
		(pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause_min_depth ppf clause =
	pp_clause ppf clause;
	let s = clause.basic_clause.node.min_defined_symb in
	(* let d = Symbol.get_defined_depth
	(Term.lit_get_top_symb s) in
	*)
	(*  out_str *)
	Format.fprintf
		ppf "@[<h> depth: %s @]" (param_to_string string_of_int s)

let rec pp_literals_tptp ppf = function
	
	| [] -> ()
	
	| [l] -> Format.fprintf ppf "@[<h>%a@]" Term.pp_term_tptp l
	
	| l :: tl ->
			pp_literals_tptp ppf [l];
			Format.fprintf ppf "@ | ";
			pp_literals_tptp ppf tl

(* Output clause in TPTP format *)
let pp_clause_literals_tptp ppf clause =
	
	(* Print empty clause *)
	if (is_empty_clause clause) 
	then
			Format.fprintf ppf "@[<h>( %a )@]" Symbol.pp_symbol Symbol.symb_false
	else
	(* Print non-empty clause as disjunction of literals *)
			Format.fprintf
				ppf
				"@[<hv>( %a )@]"
				pp_literals_tptp
				(get_lits clause)

(* Output clause in TPTP format *)
let pp_clause_tptp ppf clause =
	Format.fprintf
		ppf
		"cnf(c_%d,%s,(%a))."
	 (* (get_context_id clause) *) (get_fast_key clause)
		(if (is_negated_conjecture clause)
			then "negated_conjecture"
			else "plain")
		(pp_any_list Term.pp_term_tptp " | ") (get_lits clause)
		
(* Output list of clauses in TPTP format, skipping equality axioms *)
let rec pp_clause_list_tptp ppf = function
	
	| [] -> ()
	
	(* Skip equality axioms *)
	(*  | { history = Def (Axiom Eq_Axiom) } :: tl ->      *)
	| c:: tl when 
	  (get_tstp_source c) = TSTP_external_source (TSTP_theory TSTP_equality)-> 
			pp_clause_list_tptp ppf tl
	
	(* Clause at last position in list *)
	| [c] -> pp_clause_tptp ppf c
	
	(* Clause at middle position in list *)
	| c :: tl ->
			pp_clause_tptp ppf c;
			Format.pp_print_newline ppf ();
			pp_clause_list_tptp ppf tl

(*----tptp output without pp-----*)
let tptp_to_stream s clause =
	begin
		s.stream_add_str "cnf(";
		s.stream_add_str ("id_"^(string_of_int  (get_fast_key clause)));
		s.stream_add_char ',';
		(if (is_negated_conjecture clause)
			then
				s.stream_add_str "negated_conjecture"
			else
				s.stream_add_str "plain"
		);
		s.stream_add_char ',';
		s.stream_add_char '(';
		list_to_stream s Term.to_stream (get_lits clause) "|";
		s.stream_add_str "))."
	end

let out_tptp = tptp_to_stream stdout_stream

let to_tptp =
	to_string_fun_from_to_stream_fun 30 tptp_to_stream

let clause_list_tptp_to_stream s c_list =
	list_to_stream s tptp_to_stream c_list "\n"

let out_clause_list_tptp = clause_list_tptp_to_stream stdout_stream

let clause_list_to_tptp =
	to_string_fun_from_to_stream_fun 300 clause_list_tptp_to_stream

	
(*----------*)
let rec add_var_set vset cl =
	List.fold_left Term.add_var_set vset (get_lits cl)

let get_var_list cl =
	let vset = add_var_set (VSet.empty) cl in
	VSet.elements vset


(*
let inherit_history from_c to_c =
to_c.history <- from_c.history
*)

	

(*--------------------------------------*)

let fold_sym f a clause =
	List.fold_left (Term.fold_sym f) a (get_lits clause)

let iter_sym f clause =
	List.iter (Term.iter_sym f) (get_lits clause)



(*-------------------------------------------------------------------------------------------*)
(*------------------------- Normalising binded lit_lists /clauses ---------------------------*)
(*-------------------------------------------------------------------------------------------*)

(* changed from *)
(* apply_bsubst term_db_ref bsubst bclause *)

let apply_bsubst term_db_ref bsubst bound lits =
	let bterm_list = propagate_binding_to_list (bound, lits) in
	let new_lit_list =
		SubstBound.apply_bsubst_btlist term_db_ref bsubst bterm_list in
	new_lit_list

let apply_bsubst_norm_subst term_db_ref bsubst bound lits =
	let bterm_list = propagate_binding_to_list (bound, lits) in
	let (new_term_list, norm_subst) =
		SubstBound.apply_bsubst_btlist_norm_subst
			term_db_ref bsubst bound bterm_list in
	((new_term_list), norm_subst)
	
(*
let apply_bsubst_norm_subst term_db_ref bsubst bound clause =
	let bterm_list = propagate_binding_to_list (bound, clause.literals) in
	let (new_term_list, norm_subst) =
		SubstBound.apply_bsubst_btlist_norm_subst
			term_db_ref bsubst bound bterm_list in
	((create_parent clause new_term_list), norm_subst)
(*  (create_parent clause new_term_list,norm_subst)*)
*)


(* term_compare' returns cequal
if the skeletons of terms the same or raises an exception above *)

let rec term_compare' t s =
	match (t, s) with
	| (Term.Fun(t_sym, t_args, _), Term.Fun(s_sym, s_args, _)) ->
			let cmp = Symbol.compare t_sym s_sym in
			if cmp = cequal then
				Term.arg_fold_left2
					(fun result t' s' -> term_compare' t' s') cequal t_args s_args
			else
			if cmp > cequal then raise Term_compare_greater
			else raise Term_compare_less
	| (Term.Var(_, _), Term.Fun(_, _, _)) -> raise Term_compare_greater
	| (Term.Fun(_, _, _), Term.Var(_, _)) -> raise Term_compare_less
	| (Term.Var(_, _), Term.Var(_, _)) -> cequal

(*term_compare used to normalise clauses for better sharing and all...*)

let term_compare t s =
	try term_compare' t s
	with
	| Term_compare_greater -> cequal +1
	| Term_compare_less -> cequal -1

(*
let bound_term_compare ((_, t) : bound_term) ((_, s) : bound_term) =
term_compare t s
*)

let norm_bterm_wrt_subst bound_t bound_subst =
	match bound_t with
	| (b_t, Term.Var(t_v, _)) ->
			(
				try (SubstBound.find_norm (b_t, t_v) bound_subst)
				with Not_found -> bound_t
			)
	| _ -> bound_t

let cmp_bmc1_atom_fun () = Term.lit_cmp_type_list_to_lex_fun
		[
		(*	Lit_next_state false;*)
		Lit_range true;
		Lit_less true;
		(* Lit_clock true;
		Lit_eq false *)]


let rec bterm_subst_compare' bound_t bound_s bound_subst =
	let norm_bt = norm_bterm_wrt_subst bound_t bound_subst and
	norm_bs = norm_bterm_wrt_subst bound_s bound_subst in
	let (b_t, t) = norm_bt and
	(b_s, s) = norm_bs in
	match (t, s) with
	| (Term.Fun(t_sym, t_args, _), Term.Fun(s_sym, s_args, _)) ->
			let cmp = Symbol.compare t_sym s_sym in
			if cmp = cequal then
				Term.arg_fold_left2
					(fun result t' s' -> bterm_subst_compare' (b_t, t') (b_s, s') bound_subst)
					cequal t_args s_args
			else
			if cmp > cequal then raise Term_compare_greater
			else raise Term_compare_less
	| _ -> term_compare' t s

let bterm_subst_compare bound_t bound_s bound_subst =
	let b_atom_t = apply_to_bounded Term.get_atom bound_t in
	let b_atom_s = apply_to_bounded Term.get_atom bound_s in
	
	let (bt, atom_t) = b_atom_t in
	let (bs, atom_s) = b_atom_s in
	let pre_comp_fun =
		if (val_of_override !current_options.bmc1_incremental)
		then
			cmp_bmc1_atom_fun ()
		else
			Term.lit_cmp_type_to_fun (Lit_eq(false))
	
	in
	let	pre_comp = pre_comp_fun atom_t atom_s in
	
	if pre_comp = 0
	then
		
		(
			try bterm_subst_compare' b_atom_t b_atom_s bound_subst
			with
			| Term_compare_greater -> cequal +1
			| Term_compare_less -> cequal -1
		)
	
	else
		- pre_comp (* "-" since List.sort sorts in ascending order *)

type var_param = var param

module VarTableM = Var.VHashtbl

let rec normalise_term_var' var_table (max_var_ref : var ref) term =
	match term with
	| Term.Fun(sym, args, _) ->
			let new_args =
				Term.arg_map_left (normalise_term_var' var_table max_var_ref) args in
			Term.create_fun_term_args sym new_args
	| Term.Var(v, _) ->
			try
				let new_v = VarTableM.find var_table v in
				Term.create_var_term new_v
			with
				Not_found ->
					let old_max_var = !max_var_ref in
					VarTableM.add var_table v old_max_var;
					(*  env_ref := (v,old_max_var)::(!env_ref);*)
					max_var_ref := Var.get_next_var old_max_var;
					Term.create_var_term old_max_var
					
					
let normalise_bterm_list term_db_ref bsubst bterm_list =
	let bterm_compare bt bs = bterm_subst_compare bt bs bsubst in
	let sorted_list = List.sort bterm_compare bterm_list in
	let renaming_env = SubstBound.init_renaming_env () in
	let rename_bterm_var rest bterm =
		(SubstBound.apply_bsubst_bterm' term_db_ref renaming_env bsubst bterm):: rest in
	let rev_new_term_list = List.fold_left rename_bterm_var [] sorted_list in
	List.rev rev_new_term_list

(* normilse v1 with reordering for better renaming of vars, *)

(* normalise v2  simply removes duplicate lits  *)

let normalise_b_litlist_v1 term_db_ref bsubst b_litlist =
	let list_blit = propagate_binding_to_list b_litlist in
	let new_lit_list = normalise_bterm_list term_db_ref bsubst list_blit in
	(* removes duplicates fast but not perfect based on the fact
	that literals are preordered *)
	let removed_duplicates = list_remove_duplicates new_lit_list in
	(* create removed_duplicates*)
	removed_duplicates

(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)
let normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list =
	let blit_list_list =
		List.map propagate_binding_to_list blitlist_list in
	let list_blit = List.flatten blit_list_list in
	let new_lit_list = normalise_bterm_list term_db_ref bsubst list_blit in
	(* removes duplicates fast but not perfect based on the fact
	that literals are preordered *)
	let removed_duplicates = list_remove_duplicates new_lit_list in
	(* create removed_duplicates *)
	removed_duplicates

(* complicated version *)
let normalise_bclause_v1 term_db_ref bsubst (b, clause) =
	normalise_b_litlist_v1 term_db_ref bsubst (b, (get_lits clause))

let normalise_bclause_list_v1 term_db_ref bsubst bclause_list =
	let blitlist_list =
		List.map
			(fun (b_c, clause) ->
						(b_c, (get_lits clause))) bclause_list in
	normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list

(* simpler version v2*)
(**)

let normalise_b_litlist_v2' term_db_ref bsubst blit_list =
	let blits = propagate_binding_to_list blit_list in
	list_remove_duplicates (SubstBound.apply_bsubst_btlist term_db_ref bsubst blits)

let normalise_b_litlist_v2 term_db_ref bsubst blit_list =
	(* create (normalise_b_litlist_v2' term_db_ref bsubst blit_list)*)
	(normalise_b_litlist_v2' term_db_ref bsubst blit_list)

(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)
let normalise_blitlist_list_v2 term_db_ref bsubst blitlist_list =
			List.concat
				(List.map
						(fun blit_list -> normalise_b_litlist_v2' term_db_ref bsubst blit_list)
						blitlist_list
				)

(* normilse v1 is with reordering for better renaming of vars, *)
(* normalise v2 is simply removes duplicate lits  *)

let normalise_b_litlist = normalise_b_litlist_v1
let normalise_blitlist_list = normalise_blitlist_list_v1

(*
let normalise_b_litlist = normalise_b_litlist_v2
let normalise_blitlist_list = normalise_blitlist_list_v2
*)

(*
let normalise_bclause term_db_ref bsubst bclause =
	let (b_c, clause) = bclause in
	let bterm_list = propagate_binding_to_list (b_c, (get_lits clause)) in
	let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
	create new_term_list
*)

(*
let normalise_bclause_list term_db_ref bsubst bclause_list =
	let bterm_list_list =
		List.map
			(fun (b_c, clause) ->
						propagate_binding_to_list (b_c, (get_lits clause))) bclause_list in
	let bterm_list = List.flatten bterm_list_list in
	let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
	create new_term_list
*)
(* for uniformity ise normalise_bclause with empty substitution *)

let normalise_lit_list term_db_ref lit_list =
	normalise_blitlist_list term_db_ref (SubstBound.create ()) [(1, lit_list)]

(*
let create_normalise term_db_ref context tstp_source proof_search_param lit_list = 
  let normalised_lit_list = normalise_lit_list term_db_ref lit_list in 
	create_clause context tstp_source proof_search_param normalised_lit_list
*)

(*----------------conjecture distance------------------------------------*)
(* a very big number *)
let max_conjecture_dist = 1 lsl 28
let conjecture_int = 0

let get_min_conjecture_distance_clist c_list =
	let f current_min c =
		let d = (get_conjecture_distance c) in
		(if d < current_min then d
			else current_min)
	in List.fold_left f max_conjecture_dist c_list


let get_parents tstp_source =
	match tstp_source with
	| TSTP_inference_record
	(tstp_inference_rule, main_parents) ->
			let side_parents =
				begin
					match tstp_inference_rule with
					| Instantiation side_parents -> side_parents
					| Resolution _ -> []
					| Factoring _ -> []
					| Global_subsumption _ -> []
					| Forward_subsumption_resolution -> []
					| Backward_subsumption_resolution -> []
					| Splitting _ ->[]
					| Grounding _ -> []
					| Non_eq_to_eq -> []
					| Subtyping  ->[]
					| Flattening ->[]
				end
			in main_parents@side_parents
	| _ ->	[] (* other tstp_sources*)

(* we assume that the check if the clause is a conjecture is done before*)
(* applying get_conjecture_distance_tstp_source *)
(* this is min distance of the parents, so we would need to increase before assigning to the clause *)

let get_conjecture_distance_tstp_source tstp_source = 
	let parents = get_parents tstp_source in 
	get_min_conjecture_distance_clist parents


(**-------- create clause ----------------------------*)

let new_clause ~is_negated_conjecture tstp_source bc = 
	 let conjecture_distance = 
		if is_negated_conjecture
		then 0
		else
	  	(get_conjecture_distance_tstp_source tstp_source)+1
		in 	
		let fast_key = !clause_counter in
		incr_clause_counter ();
		let ps_param = create_ps_param () in
		let new_clause = 
	 {
		basic_clause = bc;
		fast_key = fast_key; (* auto assigned when added to context *)
(*	context_id = 0; *)(* auto assigned when added to context *)
		tstp_source = Def(tstp_source);
		replaced_by = Undef;
		prop_solver_id = None;
		conjecture_distance = conjecture_distance;
		proof_search_param = ps_param;
		ccp_bool_param = Bit_vec.false_vec
		}
	  in
	 bc_set_bool_param is_negated_conjecture bc_is_negated_conjecture new_clause;
	 new_clause
   
(*	
let fill_clause_param is_conjecture tstp_source ps_param c =
	 c.tstp_source <- Def(tstp_source);
	 c.proof_search_param <- ps_param;
		c.conjecture_distance <- 
		
	 (* No auto bool context params *)
	 (* TODO: conjecture_distance from the rest of the code to here*)
	*)
	

let create_clause_opts ~is_negated_conjecture term_db_ref tstp_source lits =
	let bc = create_basic_clause (normalise_lit_list term_db_ref lits) in
	new_clause ~is_negated_conjecture tstp_source bc

(*---------------*)		
(* by default all literals in clauses are normalised *)
(* assume clause is not a negated conjecture *)

let create_clause term_db_ref tstp_source lits =
 create_clause_opts ~is_negated_conjecture:false term_db_ref tstp_source lits

(* assume clause is a negate_conjecture *)
let create_neg_conjecture term_db_ref tstp_source lits = 
	create_clause_opts ~is_negated_conjecture:true term_db_ref tstp_source lits

(* clause without normalising lits *)
let create_clause_raw tstp_source lits = 
	let bc = create_basic_clause lits in
	new_clause ~is_negated_conjecture:false tstp_source bc
	
	

(*--------------Compare two clauses-------------------*)

(* f_perv returns a value that can be compared by Pervasives.compare; ususally int or bool *)
let cmp f_perv c1 c2 = Pervasives.compare (f_perv c1) (f_perv c2)

let cmp_num_var c1 c2 = cmp num_of_var c1 c2

let cmp_num_symb c1 c2 = cmp num_of_symb c1 c2
	
let cmp_num_lits c1 c2 = cmp length c1 c2

let cmp_age c1 c2 =
	let (when_born1, when_born2) =
		((get_ps_when_born c1), (get_ps_when_born c2))
	in	
	- (Pervasives.compare (when_born1) (when_born2))

let cmp_ground c1 c2 = cmp is_ground c1 c2

let cmp_horn c1 c2 = cmp is_horn c1 c2

let cmp_epr c1 c2 = cmp is_epr c1 c2

let cmp_in_unsat_core c1 c2 = cmp in_unsat_core c1 c2

let cmp_has_eq_lit c1 c2 = cmp has_eq_lit c1 c2

let cmp_has_conj_symb c1 c2 = cmp has_conj_symb c1 c2

let cmp_has_bound_constant c1 c2 = cmp has_bound_constant c1 c2

let cmp_has_next_state c1 c2 = cmp has_next_state c1 c2

let cmp_has_reachable_state c1 c2 = cmp has_reachable_state c1 c2

let cmp_has_non_prolific_conj_symb c1 c2 = cmp has_non_prolific_conj_symb c1 c2

let cmp_conjecture_distance c1 c2 = cmp get_conjecture_distance c1 c2
	

let cmp_max_atom_input_occur c1 c2 =
	let d1 = get_max_atom_input_occur c1 in
	let d2 = get_max_atom_input_occur c2 in
	match (d1, d2) with
	| (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
	(* Undef is greater then Def *)
	| (Undef, Def _) -> -1
	| (Def _, Undef) -> 1
	| (Undef, Undef) -> 0

let cmp_min_defined_symb c1 c2 =
	let d1 = get_min_defined_symb c1 in
	let d2 = get_min_defined_symb c2 in
	match (d1, d2) with
	| (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
	(* Undef is greater then Def *)
	| (Undef, Def _) -> -1
	| (Def _, Undef) -> 1
	| (Undef, Undef) -> 0

let cl_cmp_type_to_fun t =
	match t with
	| Options.Cl_Age b -> compose_sign b cmp_age
	| Options.Cl_Num_of_Var b -> compose_sign b cmp_num_var
	| Options.Cl_Num_of_Symb b -> compose_sign b cmp_num_symb
	| Options.Cl_Num_of_Lits b -> compose_sign b cmp_num_lits
	| Options.Cl_Ground b -> compose_sign b cmp_ground
	| Options.Cl_Conj_Dist b -> compose_sign b cmp_conjecture_distance
	| Options.Cl_Has_Conj_Symb b -> compose_sign b cmp_has_conj_symb
	| Options.Cl_has_bound_constant b -> compose_sign b cmp_has_bound_constant
	| Options.Cl_has_next_state b -> compose_sign b cmp_has_next_state
	| Options.Cl_has_reachable_state b -> compose_sign b cmp_has_reachable_state
	| Options.Cl_Has_Non_Prolific_Conj_Symb b -> compose_sign b cmp_has_non_prolific_conj_symb
	| Options.Cl_Max_Atom_Input_Occur b -> compose_sign b cmp_max_atom_input_occur
	| Options.Cl_Horn b -> compose_sign b cmp_horn
	| Options.Cl_EPR b -> compose_sign b cmp_epr
	| Options.Cl_in_unsat_core b -> compose_sign b cmp_in_unsat_core
	| Options.Cl_Has_Eq_Lit b -> compose_sign b cmp_has_eq_lit
	| Options.Cl_min_defined_symb b -> compose_sign b cmp_min_defined_symb

let cl_cmp_type_list_to_lex_fun l =
	lex_combination ((List.map cl_cmp_type_to_fun l)@[(compose_12 (~-) compare)])

(*------------------------------------------*)
exception Literal_not_found

let rec cut_literal_from_list literal list =
	match list with
	| h:: tl ->
			if h == literal then tl
			else h:: (cut_literal_from_list literal tl)
	|[] -> raise Literal_not_found


(*
let cut_literal literal lit_list =
*)



(* ------------ TSTP source  ----------------------- *)


(*  *)
(*
let assign_tstp_source clause source =
	
	match clause.tstp_source with
	
	(* Fail if source already defined *)
	| Def _ -> raise (Failure "Clause source already assigned")
	
	(* Only if source undefined *)
	| Undef -> clause.tstp_source <- Def source
*)

(* Clause is generated in an instantiation inference *)
let tstp_source_instantiation parent parents_side =	
  (TSTP_inference_record ((Instantiation parents_side), [parent]))

(* Clause is generated in a resolution inference *)
let tstp_source_resolution parents upon_literals =	
		(TSTP_inference_record ((Resolution upon_literals), parents))

(* Clause is generated in a factoring inference *)
let tstp_source_factoring parent upon_literals =
		(TSTP_inference_record ((Factoring upon_literals), [parent]))

let tstp_source_subtyping parent =
		(TSTP_inference_record ((Subtyping), [parent]))

(* Clause is in input *)
let tstp_source_input file name =
		(TSTP_external_source (TSTP_file_source (file, name)))

(* Clause is generated in a global propositional subsumption *)
let tstp_source_global_subsumption max_clause_id parent =
		(TSTP_inference_record (Global_subsumption max_clause_id, [parent]))

(* Clause is generated in a translation to purely equational problem *)
let tstp_source_non_eq_to_eq parent =
		(TSTP_inference_record (Non_eq_to_eq,[parent]))

(* Clause is generated in a forward subsumption resolution *)
let tstp_source_forward_subsumption_resolution main_parent parents =
		(TSTP_inference_record
			(Forward_subsumption_resolution, (main_parent :: parents)))

(* Clause is generated in a backward subsumption resolution *)
let tstp_source_backward_subsumption_resolution parents =
		(TSTP_inference_record (Backward_subsumption_resolution, parents))

(* Clause is generated in splitting *)
let tstp_source_split symbols parent =
		(TSTP_inference_record (Splitting symbols, [parent]))

let tstp_source_flattening parent =
		(TSTP_inference_record (Flattening, [parent]))

(* Clause is generated in grounding *)
let tstp_source_grounding grounding parent =
		(TSTP_inference_record (Grounding grounding, [parent]))

(* Clause is a theory axiom *)
let tstp_source_theory_axiom theory =
		(TSTP_external_source (TSTP_theory theory))

(* Clause is an equality axiom *)
let tstp_source_axiom_equality =
	tstp_source_theory_axiom TSTP_equality

(* Clause is a distinct axiom *)
let tstp_source_axiom_distinct =
	tstp_source_theory_axiom TSTP_distinct

(* Clause is a domain axiom used in finite models *)
let tstp_source_axiom_domain =
	tstp_source_theory_axiom TSTP_domain

(* Clause is an less axiom *)
let tstp_source_axiom_less =
	tstp_source_theory_axiom TSTP_less

(* Clause is an range axiom *)
let tstp_source_axiom_range =
	tstp_source_theory_axiom TSTP_range

(* Clause is an bmc1 axiom *)
let tstp_source_axiom_bmc1 bmc1_axiom =
	tstp_source_theory_axiom (TSTP_bmc1 bmc1_axiom)

(* Clause is generated in grounding *)
let tstp_source_assumption =
	 (TSTP_internal_source TSTP_assumption)

(* term definitions in finite_models *)
let tstp_source_definition =
	 (TSTP_internal_source TSTP_definition)

(*---------------- end TSTP --------------------------*)


(*-----------------*)
module KeyContext = 
	struct
		  type t = basic_clause (* key *)
			let hash bc = bc.tag
			let equal bc1 bc2 = (bc1 == bc2) 
  end
	 
module Context = Hashtbl.Make(KeyContext)

type context = clause Context.t

(* cc -- context*)

(* creates context with an inital size *)
let context_create size = Context.create size 

let context_reset cc = Context.reset cc (* empties context*) 		

let context_add cc c = 
	let bc = (get_bc c) in
	try (Context.find cc bc) 
	with 
	| Not_found -> 
		(Context.add cc bc c;
		c
		)
let context_add_ignore cc c = 
	ignore (context_add cc c) 
		
let context_add_list cc c_list = 
		List.iter (context_add_ignore cc) c_list 
		
let context_remove cc c = Context.remove cc (get_bc c)

let context_mem cc c = Context.mem cc (get_bc c)

let context_mem_lits cc lits = Context.mem cc (create_basic_clause lits)


let context_find cc c = Context.find cc (get_bc c)

let context_find_lits cc lits = Context.find cc (create_basic_clause lits)

let context_iter cc f = Context.iter (fun _ c -> f c) cc
let context_fold cc f a = Context.fold (fun _ c a -> (f c a)) cc a  
let context_size cc = Context.length cc

(** copy_context from_cxt to_contxt; if a clause in to_context it will remain and not replaced by from_cxt; *)
(** from_cxt remains unchanged;  clauses are not renewed but added so changing paramtes in to_cxt will affect on from_cxt *)
(* use context_reset which clears and resizes to the initial size *)

let context_add_context from_cxt to_cxt =
	let f c = 
		 ignore (context_add to_cxt c)
		in
	context_iter from_cxt f

(*
*)
	
(* returns clause list with which c was replaced *)	
let get_replaced_by_clauses c =
 match c.replaced_by  
 with
	| Def(RB_subsumption by_clause) -> [by_clause]
	| Def(RB_sub_typing by_clause) -> [by_clause]
	| Def(RB_splitting by_clause_list) -> by_clause_list
	| Undef -> []
	 
(* add assert of non-cyclicity check *)		
let get_replaced_by_rec clause_list = 
	let rec f to_process rep_by = 
	match to_process with 
	|h::tl -> 
		(let h_rep_by = (get_replaced_by_clauses h) in
		 f tl (h_rep_by@rep_by)
	  )
	|	[] -> rep_by	    	 
 in
  f clause_list	[]
	
	
(* replaces dead clauses with replaced *)
let context_replace_by cc =
 let f c = 
	
	 let rep_by = get_replaced_by_rec [c] in
	 if (rep_by = [])
	 then ()
	 else 
		(context_remove cc c;
	   context_add_list cc rep_by 
		)		
	in	
	context_iter cc f
	
	
	
(* a diferent version prossible to merge from smaller to larger
let merge_context from_cxt to_contxt = 

		let (smaller_cxt,larger_cxt) = 
		if (context_size from_cxt) < (context_size to_cxt)
		then 
			(from_cxt, to_cxt) 
		else 
			(to_cxt, from_cxt)
	in (* move from smaller to bigger cxt*)
	let f c = 
		 if (context_mem larger_cxt c) 
		 then ()
		 else 
*)

						
(*
(* cc -- context*)
let cc_create size name = Context.create_name size name
let cc_mem cc bc = Context.mem cc bc
let cc_find cc bc = Context.find cc bc
let cc_size cc = Context.size cc

(* in cc_fold f: bc -> c -> 'a -> 'a *)
let cc_fold f cc a = Context.fold f cc a

(* in cc_iter f: bc -> c -> unit *)
let cc_iter f cc = Context.iter f cc
let cc_add cc clause = 
  Context.add clause db_ref

(* should be copyed since add_ref is different....*)
let cc_add context elem =
      let cc_ref = ref context in
      let _ = cc_add_ref cc_ref elem in
      !cc_ref


let cc_remove context clause = 
  let new_context = Context.remove clause context in
  Clause.set_bool_param false Clause.in_clause_db clause;
  new_db

let cc_get_name = ClauseDBM.get_name

let to_stream s clause_db = 
  ClauseDBM.to_stream s Clause.to_stream ",\n" clause_db

let out = to_stream stdout_stream

let to_string clause_db = 
  ClauseDBM.to_string Clause.to_stream ",\n" clause_db
*)
		 
(*
let normalise term_db_ref clause =
	normalise_bclause term_db_ref (SubstBound.create ()) (1, clause)
*)

										
(*----Orphan Search Not Finished--------------*)

let get_non_simplifying_parents clause =
	match clause.tstp_source with
	| Def (TSTP_inference_record ((Resolution upon_literals), parents)) ->
			parents
	
	| Def (TSTP_inference_record ((Factoring upon_literals), parents)) ->
			parents
	
	| _ -> []

(* we collect all oprphans in a branch to a dead parent *)
(* if we meet a simplifying clause then we stop and do not include this branch*)
let rec get_orphans clause =
	if (get_is_dead clause)
	then [clause]
	else
	if (get_ps_simplifying clause)
	then []
	else
		let parents = get_non_simplifying_parents clause in
		let parent_result =
			List.fold_left (fun rest curr -> ((get_orphans curr)@rest)) [] parents in
		if not (parent_result = [])
		then
			(clause:: parent_result)
		else []

(*-----assume clause is of the from [pred(sK)] where sK is a state skolem fun---*)
let get_skolem_bound_clause clause =
	match (get_literals clause) with
	|[Term.Fun(symb, args, _)] ->
			if (Symbol.is_a_state_pred_symb symb)
			then
				(match (Term.arg_to_list args)
					with
					|[term] ->
							if (Term.is_skolem_const term)
							then Some term
							else None
					| _ -> None
				)
			else None
	| _ -> None


let replace_subterm termdb_ref subterm byterm lits =
	normalise_lit_list
		termdb_ref
				(List.map (Term.replace subterm byterm) lits)

																														
(*------------ clause signature --------------------*)																																																												(*------------------*)
type clause_signature =
	{
		(*sig_fun_pred contains all functions and predicate symbols *)
		(* occurring in the set of clauses except eq_types which are in sig_eq_types *)
		mutable sig_fun_preds : sym_set;
		mutable sig_eq_types : sym_set;
	}

let create_clause_sig () =
	{
		sig_fun_preds = SymSet.empty;
		sig_eq_types = SymSet.empty;
	}

let rec extend_clause_sig_term csig t =
	match t with
	| Term.Fun(symb, args, _) ->
			let relevant_args =
				if (symb == Symbol.symb_typed_equality)
				then
					(
						let (eq_type, t1, t2) =
							get_triple_from_list (Term.arg_to_list args) in
						let eq_type_sym = Term.get_top_symb eq_type in
						csig.sig_eq_types <- SymSet.add eq_type_sym csig.sig_eq_types;
						
						Term.list_to_arg [t1; t2]
					)
				else
					(
						csig.sig_fun_preds <- SymSet.add symb csig.sig_fun_preds;
						args
					)
			in
			Term.arg_iter (extend_clause_sig_term csig) relevant_args
	| Term.Var _ -> ()

let extend_clause_sig_lit csig lit =
	extend_clause_sig_term csig (Term.get_atom lit)

let extend_clause_sig_cl csig clause =
	iter (extend_clause_sig_lit csig) clause

let extend_clause_list_signature csig clause_list =
	List.iter (extend_clause_sig_cl csig) clause_list

let clause_list_signature clause_list =
	let cl_sig = create_clause_sig () in
	extend_clause_list_signature cl_sig clause_list;
	cl_sig
																														


(*-------------- Hash/Map/Set -------------------------*)

module Key = 
	struct
  type t = clause
	let equal = (==)
	let hash c =  (get_fast_key c) 
(*	let hash c = hash_sum (get_fast_key c) (get_context_id c)*)
	let compare = compare
	end

module Map = Map.Make(Key)

module Set = Set.Make(Key)
type clause_set = Set.t

module Hashtbl = Hashtbl.Make(Key)

let clause_list_to_set clause_list =
	List.fold_left (fun set cl -> Set.add cl set) Set.empty clause_list


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

exception Term_compare_greater
exception Term_compare_less



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

let ccp_is_dead_in_context = 0  (* user *)
(* ccp_is_dead_in_context true the the clause is simplified in a context and replaced by other clauses *)
(* invariant: set of (not ccp_is_dead_in_context) clauses imply the set of all clauses in the context *)

let ccp_in_unsat_core = 1 (* user *)
 (* clause was in unsat core in the last proof search run *)
(* used in bmc1 *)

(*--------Inst bool param------------*)

let inst_is_dead = 0
let inst_in_active = 1
let inst_in_unif_index = 2
let inst_in_subset_subsumption_index = 3
let inst_in_subsumption_index = 4
let inst_in_prop_solver = 5
let inst_in_sim_passive = 6

let inst_pass_queue1 = 7
let inst_pass_queue2 = 8
let inst_pass_queue3 = 9
let bc_in_last_unsat_core = 10 (* could be changed *)

(*-----------Res bool parm----------*)
let res_sel_max = 0
let res_pass_queue1 = 1
let res_pass_queue2 = 2
let res_in_sim_passive = 3

(* if used in simplifications then simplifying is true                            *)
(* used in orphan elimination since we can eliminate only non-simplifying cluases *)
let res_simplifying = 4

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
	clause_node hash_consed
and clause_node =
	{
		basic_clause : basic_clause;
		mutable context_id : int;       (* clause is identified by context_id and basic_clause.tag *)
		mutable tstp_source : tstp_source param;
		mutable simplified_by : simplified_by param;
		mutable prop_solver_id : int param; (* prop_solver_id is used in uc_solver for djoining special literls for unsat cores/proof recontruction*)
		mutable conjecture_distance : int; (* can be changed when tstp_source is reassigned *)
		mutable proof_search_param : proof_search_param;  (* we can reassign clause paramters within the same context *)
		mutable ccp_bool_param : Bit_vec.bit_vec;
	}

(* clause parameters can contain clauses themselves like inst_children *)
and inst_param =
	{
		mutable inst_bool_param : Bit_vec.bit_vec;
		mutable inst_sel_lit : (term * sel_place) param;
		mutable inst_dismatching : dismatching param;
		mutable inst_when_born : int param;
		mutable inst_children : clause list;
		mutable inst_activity : int;
	}

and res_param =
	{
		mutable res_bool_param : Bit_vec.bit_vec;
		mutable res_sel_lits : literal_list param;
		mutable res_when_born : int param;
	}

(* clause parameters can change from context to context but basic_clause will remain the same*)
and proof_search_param =
	| Inst_param of inst_param
	| Res_param of res_param
	| Empty_param

and simplified_by =             
	(* when clause got simplified we record the clauses which is got simplified by *)
	(* assumption are: 1) orginal cluase logically follows from the simplifed_by cluases *)
	(* in particular we can replace the original clause by simplified_by clauses *)
	(* there is no cyclic simplification depdendences; we can recover the leaf simplifyig clauses which are not simplified *)
	| Simp_by_subsumption of clause
	| Simp_by_global_subsumption of clause
(* in future: demodulation, others *)

(*-------tstp_source-----------*)

and axiom =
	| Eq_Axiom
	| Distinct_Axiom
	| Less_Axiom
	| Range_Axiom
	| BMC1_Axiom

and tstp_internal_source =
	| TSTP_definition
	| TSTP_assumption
	| TSTP_non_eq_to_eq

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
module Clause_Node_Key =
struct
	type t = clause_node
	(* assume that we already *)
	let equal c1 c2 = c1.basic_clause == c2.basic_clause
	let hash c = c.basic_clause.tag (* use tag in place of hash *)
end

module Clause_Cons = Hashcons.Make(Clause_Node_Key)

(* clauses are normally created within a context such as resolution/instantiation etc *)

type clause_context =
	{
		cc_cons : Clause_Cons.t;
		cc_id : int;
		cc_name : string;
	}

let clause_context_counter = ref 0 (* all clause contexts will have a unique id *)

(* redo with Maps *)
let clause_context_list = ref []

let create_clause_context name size =
	let cc =
		{ 
			cc_cons = Clause_Cons.create 11353; (* medium size prime number *)
			cc_id = !clause_context_counter;
			cc_name = name
		}
	in
	clause_context_counter:= !clause_context_counter +1;
	clause_context_list := cc::!clause_context_list;
	cc

let add_clause_node context clause_node = Clause_Cons.hashcons context.cc_cons clause_node

(*-----------------------------------------*)

type bound_clause = clause Lib.bind

type bound_bclause = basic_clause Lib.bind

let get_bclause c =
	c.basic_clause

(*-----------------------------------------*)
let compare_basic_clause c1 c2 =
	Pervasives.compare c1.tag c2.tag

let equal_basic_clause = (==)

let compare_clause c1 c2 =
	pair_compare_lex
		Pervasives.compare
		Pervasives.compare
		(c1.tag, c1.node.context_id)
		(c2.tag, c2.node.context_id)

let equal_clause = (==)

let equal = equal_clause

let compare = compare_clause 

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

(*---------------clause params -------------------------*)

let create_inst_param () =
	{
		inst_bool_param = Bit_vec.false_vec;
		inst_sel_lit = Undef;
		inst_dismatching = Undef;
		inst_when_born = Undef;
		inst_children = [];
		inst_activity = 0;
	}

let create_res_param () =
	{
		res_bool_param = Bit_vec.false_vec;
		res_sel_lits = Undef;
		res_when_born = Undef;
	}


(*
{
		basic_clause : basic_clause;
		context_id : int;       (* clause is identified by context_id and basic_clause.tag *)
		mutable tstp_source : tstp_source param;
		mutable simplified_by : simplified_by param;
		mutable prop_solver_id : int param; (* prop_solver_id is used in uc_solver for djoining special literls for unsat cores/proof recontruction*)
		mutable conjecture_distance : int; (* can be changed when tstp_source is reassigned *)
		mutable proof_search_param : proof_search_param;  (* we can reassign clause paramters within the same context *)
		mutable clause_context_param : Bit_vec.bit_vec;
	}
*)

(* a very big number *)
let max_conjecture_dist = 1 lsl 28
let conjecture_int = 0

(* us to check whether the clause is in the *)
let template_clause_node bc =
	{
		basic_clause = bc;
		context_id = 0;
		tstp_source = Undef;
		simplified_by = Undef;
		prop_solver_id = Undef;
		conjecture_distance = max_conjecture_dist;
		proof_search_param = Empty_param;
		ccp_bool_param = Bit_vec.false_vec
		}

let fill_clause_param context tstp_source ps_param c = 
	 c.context_id <- context.cc_id;
	 c.tstp_source <- tstp_source;
	 c.proof_search_param <- ps_param
	 (* No auto bool context params *)
	 (* TODO: conjecture_distance from the rest of the code to here*)
	
	
let create_clause_param context tstp_source ps_param lits =
	let bc = create_basic_clause lits in
	let template_clause_node = template_clause_node bc in
	let added_clause = add_clause_node context template_clause_node in
	let new_clause =
		(if (added_clause.node == template_clause_node) (* there was no copy in clause cons *)
			then
				(
					fill_clause_param context tstp_source ps_param added_clause.node;
					added_clause
				)
			else (* there was a bc clause with these lits; so we just return it*)
			added_clause
		)
	in
	new_clause
		
(* literals are not normalised *)
	
let create_clause_res context tstp_source lits =
	let res_param = Res_param (create_res_param ()) in (* max_conjecture_dist calculate *)
	create_clause_param context tstp_source res_param lits

let create_clause_inst context tstp_source lits =
	let inst_param = Inst_param (create_inst_param ()) in
	create_clause_param context tstp_source inst_param lits

let create_clause_no_param context tstp_source lits =
	create_clause_param context tstp_source Empty_param lits

(*------------------*)

let get_lits c = c.node.basic_clause.node.lits 
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

(*----------------*)
let get_proof_search_param c = c.node.proof_search_param
	
	
let get_inst_param c = 
	 match (get_proof_search_param c) with 
		Inst_param p -> p 
	|_-> failwith "Inst_param is not defined" 

let inst_get_bool_param c = 
	let inst_param = get_inst_param c in 
	inst_param.inst_bool_param
	 
let get_res_param c = 
	 match (get_proof_search_param c) with 
		Res_param p -> p 
	|_-> failwith "Res_param is not defined" 
				  	
						
let res_get_bool_param c = 
	let res_param = get_res_param c in 
	res_param.res_bool_param

	
(*-------------------------------*)
exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

let assign_prop_solver_id c id =
	match c.node.prop_solver_id with
	| Undef -> c.node.prop_solver_id <- Def (id)
	| Def _ -> raise Clause_prop_solver_id_is_def

let get_prop_solver_id clause = clause.node.prop_solver_id

(*-------------------------------*)

(*
let assign_tstp_source tstp_source c =
	c.node.tstp_source <- tstp_source

let get_tstp_source c =	c.node.tstp_source


*)



(*-----------------------------------------*)
let axiom_to_string axiom =
	match axiom with
	| Eq_Axiom -> "Equality Axiom"
	| Distinct_Axiom -> "Distinct Axiom"
	| Less_Axiom -> "Less Axiom"
	| Range_Axiom -> "Range Axiom"
	| BMC1_Axiom -> "BMC1 Axiom"

let pp_axiom ppf = function
	| Eq_Axiom -> Format.fprintf ppf "Equality Axiom"
	| Distinct_Axiom -> Format.fprintf ppf "Distinct Axiom"
	| Less_Axiom -> Format.fprintf ppf "Less Axiom"
	| Range_Axiom -> Format.fprintf ppf "Range Axiom"
	| BMC1_Axiom -> Format.fprintf ppf "BMC1 Axiom"

(*----------------------------*)
let get_node c = c.node

let get_bc c = c.node.basic_clause
	
let get_bc_node c = c.node.basic_clause.node

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

let ccp_get_bool_param param clause = 
	Bit_vec.get param clause.ccp_bool_param

let ccp_set_bool_param value param clause =
	clause.ccp_bool_param <- Bit_vec.set value param clause.ccp_bool_param

let inst_get_bool_param param clause =
	let inst_param = get_inst_param clause in
	Bit_vec.get param inst_param.inst_bool_param

let inst_set_bool_param value param clause =
	let inst_param = get_inst_param clause in
	inst_param.inst_bool_param <- Bit_vec.set value param inst_param.inst_bool_param

let res_get_bool_param param clause =
	let res_param = get_res_param clause in
	Bit_vec.get param res_param.res_bool_param

let res_set_bool_param value param clause =
	let res_param = get_res_param clause in
	res_param.res_bool_param <- Bit_vec.set value param res_param.res_bool_param

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
	bc_get_bool_param bc_has_non_prolific_conj_symb  c
		
let has_bound_constant c = 
	bc_get_bool_param  bc_has_bound_constant c

let has_next_state c = 
	bc_get_bool_param bc_has_next_state  c
		
let has_reachable_state c = 
	bc_get_bool_param bc_has_reachable_state  c			

	
let num_of_symb c =
	let bc_node =  get_bc_node c in
	bc_node.num_of_symb
	
let num_of_var c =
	let bc_node =  get_bc_node c in
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
	match c.node.tstp_source with
	| Def _ -> raise (Failure "Clause source already assigned")
	| Undef -> 	c.node.tstp_source <- Def(tstp_source)

let get_tstp_source c =	c.node.tstp_source

let get_context_id c = c.node.context_id

let assign_context_id id c = 
	c.node.context_id <- id

let get_simplified_by c = 
	c.node.simplified_by
	
let assign_simplied_by sby c = 
		c.node.simplified_by <- sby
		
let get_conjecture_distance c = 
		c.node.conjecture_distance

let assign_conjecture_distance d c = 
  c.node.conjecture_distance <- d

let inherit_conj_dist from_c to_c =
	to_c.node.conjecture_distance <- from_c.node.conjecture_distance


let get_min_conjecture_distance_clist c_list =
	let f current_min c =
		let d = (get_conjecture_distance c) in
		(if d < current_min then d
			else current_min)
	in List.fold_left f max_conjecture_dist c_list



(*------ccp bool params get/assign-------*)
let is_dead_in_context c = 
	Bit_vec.get ccp_is_dead_in_context c.node.ccp_bool_param
	
let assign_is_dead_in_context b c = 
		Bit_vec.set b ccp_is_dead_in_context c.node.ccp_bool_param

let in_unsat_core c = 
	Bit_vec.get ccp_in_unsat_core c.node.ccp_bool_param

let assign_in_unsat_core b c = 
	Bit_vec.set b ccp_in_unsat_core c.node.ccp_bool_param

(*-----proof_search param get/assign---------*)

let assign_empty_ints_param c =
	c.node.proof_search_param <- Inst_param(create_inst_param ()) 

let assign_empty_res_param c =
	c.node.proof_search_param <- Res_param(create_res_param ()) 

let assign_empty_param c =
  c.node.proof_search_param <- Empty_param
	
(*-------res param get/assign-*)
	
let res_when_born c =
	let res_param = get_res_param c in
	match res_param.res_when_born with
	| Def(n) -> n
	| Undef ->
			(
				let fail_str = "Clause: res_when_born is undef for "^(to_string c) in
				failwith fail_str
			)
		
let res_assigns_sel_lits sel_lits clause =
	let res_param = get_res_param clause in
	res_param.res_sel_lits <- Def(sel_lits)

let res_sel_is_def clause =
 let res_param = get_res_param clause in
	match res_param.res_sel_lits with
	| Def(_) -> true
	| Undef -> false
	
exception Res_sel_lits_undef
let get_res_sel_lits clause =
	let res_param = get_res_param clause in
	match res_param.res_sel_lits with
	| Def(sel_lits) -> sel_lits
	| Undef -> raise Res_sel_lits_undef

(*----------inst param get/set------------------------*)

let inst_when_born c =
	let inst_param = get_inst_param c in
	match inst_param.inst_when_born with
	| Def(n) -> n
	| Undef ->
			(
				let fail_str = "Clause: res_when_born is undef for "^(to_string c) in
				failwith fail_str
			)
	
exception Sel_lit_not_in_cluase
let rec inst_find_sel_place sel_lit lit_list =
	match lit_list with
	| h:: tl ->
			if (h == sel_lit) then 0
			else 1 + (inst_find_sel_place sel_lit tl)
	|[] -> raise Sel_lit_not_in_cluase

let inst_assign_sel_lit sel_lit clause =
	let sel_place = inst_find_sel_place sel_lit (get_lits clause) in
	let inst_param = get_inst_param clause in
	(* Format.eprintf
	"Selecting literal %s in clause (%d) %s@."
	(Term.to_string sel_lit)
	(match clause.fast_key with
	| Def key -> key
	| Undef -> -1)
	(to_string clause); *)
	inst_param.inst_sel_lit <- Def((sel_lit, sel_place))

let inst_assign_dismatching dismatching clause =
	let inst_param = get_inst_param clause in
		inst_param.inst_dismatching <- Def(dismatching)


exception Inst_sel_lit_undef
let inst_get_sel_lit clause =
	let inst_param = get_inst_param clause in
		match inst_param.inst_sel_lit with
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

let res_compare_sel_place c1 c2 =
	let c1_inst_param = get_inst_param c1 in
	let c2_inst_param = get_inst_param c2 in
	match (c1_inst_param.inst_sel_lit, c2_inst_param.inst_sel_lit) with
	| (Def((_, sp1)), Def((_, sp2)))
	-> Pervasives.compare sp1 sp2
	| _ -> raise Inst_sel_lit_undef

exception Dismatching_undef
let get_inst_dismatching clause =
	let inst_param = get_inst_param clause in
	match inst_param.inst_dismatching with
	| Def(dismatching) -> dismatching
	| Undef -> raise Dismatching_undef

let inst_add_child clause child =
	let inst_param = get_inst_param clause in
	inst_param.inst_children <- child:: (inst_param.inst_children)

let inst_get_children clause = 
	let inst_param = get_inst_param clause in
	inst_param.inst_children
	

let inst_get_activity clause = 
	let inst_param = get_inst_param clause in
	inst_param.inst_activity

let inst_assign_activity act clause = 
	let inst_param = get_inst_param clause in
	inst_param.inst_activity <- act

(*-------inst/res when born assignments--*)

(* assigns when the clause born based on when the clauses in the premise where born *)
(*                                    *)
(* if the the prem1 and prem2 is [] then zero is assined (e.g. imput clauses) *)
(* we assign when_born when 1) conclusion of an inference was generated       *)
(* 2) clause is simplified and 3) splitting 4)model transformation/equation axiom  *)
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


let inst_when_born_concl prem1 prem2 clause =
	let born_list1 = List.map inst_when_born prem1 in
	let born_list2 = List.map inst_when_born prem2 in
	let inv_compare = compose_sign false Pervasives.compare in
	(* finds min element *)
	let min_prem1 = list_find_max_element_zero inv_compare born_list1 in
	let min_prem2 = list_find_max_element_zero inv_compare born_list2 in
	let max_born = list_find_max_element Pervasives.compare [min_prem1; min_prem2] in
	let when_cl_born = max_born + 1 in
	when_cl_born

let inst_assign_when_born prem1 prem2 c =
	let inst_param = get_inst_param c in
	inst_param.inst_when_born <- Def(inst_when_born_concl prem1 prem2 c)
	
let res_when_born_concl prem1 prem2 clause =
	let born_list1 = List.map res_when_born prem1 in
	let born_list2 = List.map res_when_born prem2 in
	let inv_compare = compose_sign false Pervasives.compare in
	(* finds min element *)
	let min_prem1 = list_find_max_element_zero inv_compare born_list1 in
	let min_prem2 = list_find_max_element_zero inv_compare born_list2 in
	let max_born = list_find_max_element Pervasives.compare [min_prem1; min_prem2] in
	let when_cl_born = max_born + 1 in
	when_cl_born	
	
let res_assign_when_born prem1 prem2 c =
	let res_param = get_res_param c in
	res_param.res_when_born <- Def(res_when_born_concl prem1 prem2 c)



(*--------------pp printing ------------------------------------*)
(* Print the name of a clause

Clauses are named [c_n], where [n] is the identifier (fast_key) of
the clause. If the identifier is undefined, the clause is named
[c_tmp].
*)
let pp_clause_name ppf clause = 
	Format.fprintf ppf "c_%d_%d" (get_context_id clause) clause.tag

let pp_clause_with_id ppf clause =
	Format.fprintf
		ppf
		"(%d_%d) {%a}"
		(get_context_id clause)
		clause.tag
		(pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause ppf clause =
	Format.fprintf
		ppf
		"@[<h>{%a}@]"
		(pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause_min_depth ppf clause =
	pp_clause ppf clause;
	let s = clause.node.basic_clause.node.min_defined_symb in
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
		"cnf(c_%d_%d,%s,(%a))."
	  (get_context_id clause) clause.tag
		(if (is_negated_conjecture clause)
			then "negated_conjecture"
			else "plain")
		(pp_any_list Term.pp_term_tptp " | ") (get_lits clause)
		
(* Output list of clauses in TPTP format, skipping equality axioms *)
let rec pp_clause_list_tptp ppf = function
	
	| [] -> ()
	
	(* Skip equality axioms *)
	(*  | { history = Def (Axiom Eq_Axiom) } :: tl ->      *)
	| c::tl when 
	  (get_tstp_source c) = Def (TSTP_external_source (TSTP_theory TSTP_equality)) -> 
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
		s.stream_add_str ("id_"^(string_of_int (get_context_id clause))^"_"^(string_of_int clause.tag));
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



(*--------------Compare two clauses-------------------*)

(* f_perv returns a value that can be compared by Pervasives.compare; ususally int or bool *)
let cmp f_perv c1 c2 = Pervasives.compare (f_perv c1) (f_perv c2)

let cmp_num_var c1 c2 = cmp num_of_var c1 c2

let cmp_num_symb c1 c2 = cmp num_of_symb c1 c2
	
let cmp_num_lits c1 c2 = cmp length c1 c2

let cmp_age c1 c2 =
	let (when_born1,when_born2) =
	(match ((get_proof_search_param c1), (get_proof_search_param c2)) with 
	| (Inst_param(inst_param1), Inst_param(inst_param2)) ->
		 (inst_param1.inst_when_born, inst_param2.inst_when_born)
  | (Res_param(inst_param1), Res_param(inst_param2)) ->
		 (inst_param1.res_when_born, inst_param2.res_when_born)
	| _-> failwith (" cmp_age: when born is either not defined or not compatible in "^(to_string c1)^" "^(to_string c2)) 
	)
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



(* ------------ TSTP source get/assign ----------------------- *)


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
let assign_tstp_source_instantiation clause parent parents_side =	
	assign_tstp_source		
	clause
  (TSTP_inference_record ((Instantiation parents_side), [parent]))

(* Clause is generated in a resolution inference *)
let assign_tstp_source_resolution clause parents upon_literals =	
	assign_tstp_source
		clause
		(TSTP_inference_record ((Resolution upon_literals), parents))

(* Clause is generated in a factoring inference *)
let assign_tstp_source_factoring clause parent upon_literals =
	
	assign_tstp_source
		clause
		(TSTP_inference_record ((Factoring upon_literals), [parent]))

let assign_tstp_source_subtyping clause parent =
	assign_tstp_source
		clause
		(TSTP_inference_record ((Subtyping), [parent]))

(* Clause is in input *)
let assign_tstp_source_input clause file name =
	
	assign_tstp_source
		clause
		(TSTP_external_source (TSTP_file_source (file, name)))

(* Clause is generated in a global propositional subsumption *)
let assign_tstp_source_global_subsumption max_clause_id clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Global_subsumption max_clause_id, [parent]))

(* Clause is generated in a translation to purely equational problem *)
let assign_tstp_source_non_eq_to_eq clause parent =
	
	assign_tstp_source
		clause
		(TSTP_internal_source TSTP_non_eq_to_eq)

(* Clause is generated in a forward subsumption resolution *)
let assign_tstp_source_forward_subsumption_resolution clause main_parent parents =
	
	assign_tstp_source
		clause
		(TSTP_inference_record
			(Forward_subsumption_resolution, (main_parent :: parents)))

(* Clause is generated in a backward subsumption resolution *)
let assign_tstp_source_backward_subsumption_resolution clause parents =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Backward_subsumption_resolution, parents))

(* Clause is generated in splitting *)
let assign_tstp_source_split symbols clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Splitting symbols, [parent]))

let assign_tstp_source_flattening clause parent =
	assign_tstp_source
		clause
		(TSTP_inference_record (Flattening, [parent]))

(* Clause is generated in grounding *)
let assign_tstp_source_grounding grounding clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Grounding grounding, [parent]))

(* Clause is a theory axiom *)
let assign_tstp_source_theory_axiom clause theory =
	
	assign_tstp_source
		clause
		(TSTP_external_source (TSTP_theory theory))

(* Clause is an equality axiom *)
let assign_tstp_source_axiom_equality clause =
	assign_tstp_source_theory_axiom clause TSTP_equality

(* Clause is a distinct axiom *)
let assign_tstp_source_axiom_distinct clause =
	assign_tstp_source_theory_axiom clause TSTP_distinct

(* Clause is an less axiom *)
let assign_tstp_source_axiom_less clause =
	assign_tstp_source_theory_axiom clause TSTP_less

(* Clause is an range axiom *)
let assign_tstp_source_axiom_range clause =
	assign_tstp_source_theory_axiom clause TSTP_range

(* Clause is an bmc1 axiom *)
let assign_tstp_source_axiom_bmc1 bmc1_axiom clause =
	assign_tstp_source_theory_axiom clause (TSTP_bmc1 bmc1_axiom)

(* Clause is generated in grounding *)
let assign_tstp_source_assumption clause =
	assign_tstp_source clause (TSTP_internal_source TSTP_assumption)

(*---------------- end TSTP assignments --------------------------*)

(*-------------- Hash/Map/Set -------------------------*)

module Key = 
	struct
  type t = clause
	let equal = (==)
	let hash c = hash_sum c.tag (get_context_id c)
	let compare = compare
	end

module Map = Map.Make(Key)

module Set = Set.Make(Key)
type clause_set = Set.t

module Hashtbl = Hashtbl.Make(Key)

let clause_list_to_set clause_list =
	List.fold_left (fun set cl -> Set.add cl set) Set.empty clause_list


(*------ Normalising binded lit_lists /clauses ----------*)

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

let create_normalised term_db_ref context tstp_source lit_list = 
............

		 
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
	if (get_bool_param is_dead clause)
	then [clause]
	else
	if (get_bool_param res_simplifying clause)
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

let replace_subterm termdb_ref subterm byterm cluase =
	normalise
		termdb_ref
		(create
			
				(List.map (Term.replace subterm byterm) (get_literals cluase)))
																														

(*---------------------OLD--------------------------------*)
type clause =
	{
		literals : literal_list;
		mutable fast_key : int param;
		mutable db_id : int param;
		mutable prop_solver_id : int option;
		mutable bool_param : Bit_vec.bit_vec;
		mutable inst_sel_lit : (term * sel_place) param;
		mutable res_sel_lits : literal_list param;
		mutable dismatching : dismatching param;
		mutable length : int param;
		(* number of all symbols in literals *)
		mutable num_of_symb : int param;
		mutable num_of_var : int param;
		mutable when_born : int param;
		mutable tstp_source : tstp_source param;
		mutable parent : clause param;
		mutable children : clause list;
		mutable activity : int;
		mutable conjecture_distance : int;
		mutable max_atom_input_occur : int;
		(* minial defined symbols *)
		mutable min_defined_symb : int param;
	}

(*
and history =
| Input
| Instantiation of clause * (clause list)
| Resolution of (clause list) * (literal list)
| Factoring of clause * (literal list)
(* simplified from cluase*)
| Global_Subsumption of clause
| Forward_Subsumption_Resolution of clause * (clause list)
| Backward_Subsumption_Resolution of clause list
| Non_eq_to_eq of clause
| Axiom of axiom
| Split of clause

*)

(*---------------------------------*)
(*---------End bool params-------------*)

(*---------------------------------------------------------*)

(*  |Simplified of clause *)

type bound_clause = clause Lib.bind

exception Term_compare_greater
exception Term_compare_less

(* a very big number *)
let max_conjecture_dist = 1 lsl 28
let conjecture_int = 0

let is_negated_conjecture clause =
	clause.conjecture_distance = conjecture_int

let create term_list =
	{
		literals = term_list;
		fast_key = Undef;
		db_id = Undef;
		prop_solver_id = None;
		inst_sel_lit = Undef;
		res_sel_lits = Undef;
		dismatching = Undef;
		bool_param = Bit_vec.false_vec;
		length = Undef;
		num_of_symb = Undef;
		num_of_var = Undef;
		when_born = Undef;
		tstp_source = Undef;
		parent = Undef;
		children = [];
		activity = 0;
		conjecture_distance = max_conjecture_dist;
		max_atom_input_occur =0;
		min_defined_symb = Undef;
	}

let create_parent parent term_list =
	{
		literals = term_list;
		fast_key = Undef;
		db_id = Undef;
		prop_solver_id = None;
		inst_sel_lit = Undef;
		res_sel_lits = Undef;
		dismatching = Undef;
		bool_param = Bit_vec.false_vec;
		length = Undef;
		num_of_symb = Undef;
		num_of_var = Undef;
		when_born = Undef;
		tstp_source = Undef;
		parent = Def(parent);
		children = [];
		activity = 0;
		conjecture_distance = max_conjecture_dist;
		max_atom_input_occur =0;
		min_defined_symb = Undef;
	}

exception Clause_fast_key_is_def

let assign_fast_key clause (fkey : int) =
	match clause.db_id, clause.fast_key with
	
	(* Assign fast key if undefined or if clause database is undefined *)
	| Undef, _
	| _, Undef -> clause.fast_key <- Def(fkey)
	
	(* Raise exception if both fast key and clause database are defined *)
	| _ -> raise Clause_fast_key_is_def

exception Clause_db_id_is_def

let assign_db_id = function
	
	(* Raise exception when db_id is already defined *)
	| { db_id = Def _ } ->
			(function _ -> raise Clause_db_id_is_def)
	
	(* Set db_id to defined value *)
	| clause ->
			(function db_id -> clause.db_id <- Def(db_id))

(* Identifier for next clause that is not in a clause database *)
let clause_next_tmp_fast_key = ref 1

let assign_temp_key = function
	
	(* Only if fast key and database are not defined *)
	| { db_id = Undef; fast_key = Undef } as clause ->
	
	(* Assign a fast key in an undefined clause database *)
			clause.fast_key <- Def !clause_next_tmp_fast_key;
			clause.db_id <- Undef;
			
			(* Increment identifier for next clause without a fast key *)
			clause_next_tmp_fast_key := succ !clause_next_tmp_fast_key;
	
	(* Fail if fast key is defined *)
	| _ -> raise Clause_fast_key_is_def

exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

let assign_prop_solver_id = function
	| { prop_solver_id = None } as clause ->
			(function id -> clause.prop_solver_id <- Some id)
	
	| { prop_solver_id = Some a } ->
			(function _ -> raise Clause_prop_solver_id_is_def)

let get_prop_solver_id { prop_solver_id = id } = id

let compare_literals c1 c2 =
	list_compare_lex Term.compare c1.literals c2.literals

let compare_key cl1 cl2 =
	list_compare_lex Term.compare cl1.literals cl2.literals

exception Clause_fast_key_undef

let get_fast_key cl =
	match cl.fast_key with
	| Def(key) -> key
	| _ -> raise Clause_fast_key_undef

let compare_fast_key cl1 cl2 =
	(compare (get_fast_key cl1) (get_fast_key cl2))

let compare = compare_fast_key

let equal c1 c2 =
	if (compare c1 c2) =0 then true
	else false

let memq literal clause = List.memq literal clause.literals
let exists p clause = List.exists p clause.literals
let find p clause = List.find p clause.literals
let fold f a clause = List.fold_left f a clause.literals
let find_all f clause = List.find_all f clause.literals
let partition f clause = List.partition f clause.literals
let iter f clause = List.iter f clause.literals

let get_literals clause = clause.literals


(* switching  parameters of clauses*)

let set_bool_param value param clause =
	clause.bool_param <- Bit_vec.set value param clause.bool_param

let get_bool_param param clause =
	Bit_vec.get param clause.bool_param

let inherit_bool_param param from_c to_c =
	set_bool_param
		(get_bool_param param from_c) param to_c

let inherit_bool_param_all from_c to_c =
	to_c.bool_param <- from_c.bool_param


let inherit_conj_dist from_c to_c =
	to_c.conjecture_distance <- from_c.conjecture_distance

let inherit_when_born from_c to_c =
	to_c.when_born <- from_c.when_born

(* inherit relevant parameters for clauses obtained by modification: *)
(* it can be simplified by prop_subsumption or obtained by splitting *)
let inherit_param_modif from_c to_c =
	inherit_conj_dist from_c to_c;
	inherit_bool_param eq_axiom from_c to_c;
	inherit_when_born from_c to_c;
	inherit_bool_param input_under_eq from_c to_c
(* match to_c.history with
| Undef -> to_c.history <- Def (Simplified from_c)
| _ -> ()
*)

let inherit_tstp_source from_c to_c =
	to_c.tstp_source <- from_c.tstp_source

let copy_clause_proper c =
	let new_c = create c.literals in
	inherit_conj_dist c new_c;
	inherit_bool_param eq_axiom c new_c;
	inherit_bool_param input_under_eq c new_c;
	inherit_bool_param in_prop_solver c new_c;
	inherit_bool_param in_unsat_core c new_c;
	inherit_bool_param large_ax_considered c new_c;
	new_c.prop_solver_id <- c.prop_solver_id;
	new_c.tstp_source <- c.tstp_source;
	new_c.conjecture_distance <- c.conjecture_distance;
	new_c.max_atom_input_occur <- c.max_atom_input_occur;
	new_c.min_defined_symb <- c.min_defined_symb;
	new_c

(*	in progress*)
(*
let clause_reset c =
(* does not work ex.: ALG+016 *)
c.fast_key <- Undef;
c.db_id <- Undef;
(*	prop_solver_id = None;*)
c.inst_sel_lit <- Undef;
c.res_sel_lits <- Undef;
c.dismatching <- Undef;
let in_unsat_core_old = get_bool_param in_unsat_core c in
c.bool_param <- Bit_vec.false_vec;
set_bool_param in_unsat_core_old in_unsat_core c
*)

let copy_clause c =
	copy_clause_proper c

(*
clause_reset c;
c
*)

(* length = Undef;
num_of_symb = Undef;
num_of_var = Undef;
when_born = Undef;
tstp_source = Undef;
parent = Def(parent);
children = [];
activity = 0;

conjecture_distance = max_conjecture_dist;
max_atom_input_occur =0;
min_defined_symb = Undef;
*)

(*
let copy_clause c =
{ c with literals = c.literals }

let copy_clause_undef_fast_key c =
{ c with fast_key = Undef }
*)

(*------------To stream/string-------------------------------*)

let to_stream s clause =
	s.stream_add_char '{';
	(list_to_stream s Term.to_stream clause.literals ";");
	s.stream_add_char '}'

(* Print the name of a clause

Clauses are named [c_n], where [n] is the identifier (fast_key) of
the clause. If the identifier is undefined, the clause is named
[c_tmp].
*)
let rec pp_clause_name ppf = function
	
	(* Clause has a fast key, but is not in a clause database *)
	| { fast_key = Def n; db_id = Undef } ->
	
	(* Print clause name outside of a clause database *)
			Format.fprintf ppf "c_x_%d" n
	
	(* Clause has a fast key and is in a numbered clause database *)
	| { fast_key = Def n; db_id = Def d } ->
	
	(* Print clause name with identifier of clause database *)
			Format.fprintf ppf "c_%d_%d" d n
	
	(* Clause does not have a fast key *)
	| { fast_key = Undef } as clause ->
	
	(* Assign a temporary key for clause *)
			assign_temp_key clause;
			
			(* Print name of clause *)
			pp_clause_name ppf clause

let pp_clause_with_id ppf clause =
	Format.fprintf
		ppf
		"(%d) {%a}"
		(match clause.fast_key with Def k -> k | Undef -> -1)
		(pp_any_list Term.pp_term ";") clause.literals

let pp_clause ppf clause =
	Format.fprintf
		ppf
		"@[<h>{%a}@]"
		(pp_any_list Term.pp_term ";") clause.literals

let pp_clause_min_depth ppf clause =
	pp_clause ppf clause;
	let s = clause.min_defined_symb in
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
let pp_clause_literals_tptp ppf = function
	
	(* Print empty clause *)
	| clause when clause.literals = [] ->
			Format.fprintf ppf "@[<h>( %a )@]" Symbol.pp_symbol Symbol.symb_false
	
	(* Print non-empty clause as disjunction of literals *)
	| clause ->
			Format.fprintf
				ppf
				"@[<hv>( %a )@]"
				pp_literals_tptp
				clause.literals

(* Output clause in TPTP format *)
let pp_clause_tptp ppf clause =
	Format.fprintf
		ppf
		"cnf(%s,%s,(%a))."
		(match clause.fast_key with
			| Def k -> Format.sprintf "id_%d" k
			| Undef -> "tmp")
		(if (is_negated_conjecture clause)
			then "negated_conjecture"
			else "plain")
		(pp_any_list Term.pp_term_tptp " | ") clause.literals

(* Output list of clauses in TPTP format, skipping equality axioms *)
let rec pp_clause_list_tptp ppf = function
	
	| [] -> ()
	
	(* Skip equality axioms *)
	(*  | { history = Def (Axiom Eq_Axiom) } :: tl ->      *)
	| { tstp_source = Def (TSTP_external_source (TSTP_theory TSTP_equality)) } :: tl ->
			pp_clause_list_tptp ppf tl
	
	(* Clause at last position in list *)
	| [c] -> pp_clause_tptp ppf c
	
	(* Clause at middle position in list *)
	| c :: tl ->
			pp_clause_tptp ppf c;
			Format.pp_print_newline ppf ();
			pp_clause_list_tptp ppf tl

let out = to_stream stdout_stream

let to_string =
	to_string_fun_from_to_stream_fun 100 to_stream

(*
let to_string clause =
"{"^(list_to_string Term.to_string clause.literals ";")^"}" (*^"\n"*)
*)

let tptp_to_stream s clause =
	begin
		s.stream_add_str "cnf(";
		s.stream_add_str "id_";
		(match clause.fast_key with
			| Def(key) ->
					s.stream_add_str (string_of_int key)
			| Undef ->
					s.stream_add_str "tmp"
		);
		s.stream_add_char ',';
		(if (is_negated_conjecture clause)
			then
				s.stream_add_str "negated_conjecture"
			else
				s.stream_add_str "plain"
		);
		s.stream_add_char ',';
		s.stream_add_char '(';
		list_to_stream s Term.to_stream clause.literals "|";
		s.stream_add_str "))."
	end

let out_tptp = tptp_to_stream stdout_stream

let to_tptp =
	to_string_fun_from_to_stream_fun 30 tptp_to_stream

(*
"cnf("^id_str^","^clause_type^","
^"("^(list_to_string Term.to_string clause.literals "|")^")"^")."
*)

(*

let to_tptp clause =
let id_str =
let pref_id = "id_" in
match clause.fast_key with
| Def(key) -> pref_id^(string_of_int key)
| Undef -> pref_id^"tmp"
in
let clause_type = "plain" in
"cnf("^id_str^","^clause_type^","
^"("^(list_to_string Term.to_string clause.literals "|")^")"^")."

*)

let clause_list_to_stream s c_list =
	list_to_stream s to_stream c_list "\n"

let out_clause_list = clause_list_to_stream stdout_stream

let clause_list_to_string =
	to_string_fun_from_to_stream_fun 300 clause_list_to_stream

let clause_list_tptp_to_stream s c_list =
	list_to_stream s tptp_to_stream c_list "\n"

let out_clause_list_tptp = clause_list_tptp_to_stream stdout_stream

let clause_list_to_tptp =
	to_string_fun_from_to_stream_fun 300 clause_list_tptp_to_stream


(*
let clause_list_to_string c_list =
list_to_string to_string c_list "\n"

let clause_list_to_tptp c_list =
list_to_string to_tptp c_list "\n"
*)

(*----------*)
(*!! is ground is used before it is put in a clauseDB!!*)

let is_ground c =
	if (get_bool_param in_clause_db c)
	then
		(get_bool_param ground c)
	else
		(let is_not_ground lit = not (Term.is_ground lit) in
			if (exists is_not_ground c)
			then false
			else true)

(*----------*)
let is_horn_check c =
	let num_pos = ref 0 in
	let rec is_horn_check' lits =
		match lits with
		| h :: tl ->
				if not (Term.is_neg_lit h)
				then
					if !num_pos >=1
					then false
					else
						(num_pos := !num_pos +1;
							is_horn_check' tl
						)
				else
					is_horn_check' tl
		|[] -> true
	in
	is_horn_check' (c.literals)

let is_horn c =
	if (get_bool_param in_clause_db c)
	then
		(get_bool_param horn c)
	else
		is_horn_check c

(*---------- check if clause is epr class-----*)

let is_epr c =
	if (get_bool_param in_clause_db c)
	then
		(get_bool_param epr c)
	else
		(let is_not_epr lit = not (Term.is_epr_lit lit) in
			if (exists is_not_epr c) then false
			else true)

(*----------*)
let has_eq_lit c =
	if (get_bool_param in_clause_db c)
	then
		(get_bool_param has_eq_lit_param c)
	else
	if (exists Term.is_eq_lit c) then true
	else false

(*----------*)
let rec add_var_set vset cl =
	List.fold_left Term.add_var_set vset (get_literals cl)

let get_var_list cl =
	let vset = add_var_set (VSet.empty) cl in
	VSet.elements vset

(*
let inherit_history from_c to_c =
to_c.history <- from_c.history
*)

let num_of_symb clause =
	match clause.num_of_symb with
	| Def(n) -> n
	| Undef -> failwith "Clause: num_of_symb is undef"

let num_of_var clause =
	match clause.num_of_var with
	| Def(n) -> n
	| Undef -> failwith "Clause: num_of_var is undef"

let length clause =
	match clause.length with
	| Def(n) -> n
	| Undef -> failwith "Clause: length is undef"

let when_born clause =
	match clause.when_born with
	| Def(n) -> n
	| Undef ->
			(
				let fail_str = "Clause: when_born is undef for "^(to_string clause) in
				failwith fail_str
			)

let assign_max_atom_input_occur c =
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
	let max_symb = get_symb (list_find_max_element cmp c.literals) in
	c.max_atom_input_occur <- (Symbol.get_num_input_occur max_symb)

let get_max_atom_input_occur c = c.max_atom_input_occur

let assign_conjecture_distance int c =
	if (int >= max_conjecture_dist)
	then c.conjecture_distance <- max_conjecture_dist
	else c.conjecture_distance <- int

let get_conjecture_distance c =
	c.conjecture_distance

let get_min_conjecture_distance c_list =
	let f current_min c =
		let d = (get_conjecture_distance c) in
		(if d < current_min then d
			else current_min)
	in List.fold_left f max_conjecture_dist c_list

let cmp_conjecture_distance c1 c2 =
	(Pervasives.compare c1.conjecture_distance c2.conjecture_distance)

(*------------------*)
let get_num_of_symb clause =
	let f rest term = rest + (Term.get_num_of_symb term) in
	List.fold_left f 0 clause.literals

let get_num_of_var clause =
	let f rest term = rest + (Term.get_num_of_var term) in
	List.fold_left f 0 clause.literals

let assign_num_of_symb clause =
	clause.num_of_symb <- Def(get_num_of_symb clause)

let assign_num_of_var clause =
	clause.num_of_var <- Def(get_num_of_var clause)

let assign_length clause =
	clause.length <- Def(List.length clause.literals)

let assign_term_bool_param_clause_param term_bool_param clause_bool_param clause =
	set_bool_param
		(List.exists (Term.get_fun_bool_param term_bool_param) clause.literals)
		clause_bool_param clause

let assign_has_conj_symb clause =
	assign_term_bool_param_clause_param Term.has_conj_symb has_conj_symb clause

let assign_has_non_prolific_conj_symb clause =
	assign_term_bool_param_clause_param Term.has_non_prolific_conj_symb has_non_prolific_conj_symb clause

let assign_has_bound_constant clause =
	assign_term_bool_param_clause_param Term.has_bound_constant has_bound_constant clause

let assign_has_next_state clause =
	set_bool_param (List.exists Term.is_next_state_lit clause.literals) has_next_state
		clause

let assign_has_reachable_state clause =
	set_bool_param (List.exists Term.is_reachable_state_lit clause.literals) has_reachable_state clause

(*
let assign_has_conj_symb clause =
set_bool_param
(List.exists (Term.get_fun_bool_param Term.has_conj_symb) clause.literals)
has_conj_symb clause

let assign_has_non_prolific_conj_symb clause =
set_bool_param
(List.exists (Term.get_fun_bool_param Term.has_non_prolific_conj_symb) clause.literals)
has_non_prolific_conj_symb clause
*)

let assign_min_defined_symb c =
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
	let lit_list = get_literals c in
	let min_lit = list_find_min_element cmp_lit lit_list in
	let min_d = Symbol.get_defined_depth (Term.lit_get_top_symb min_lit) in
	c.min_defined_symb <- min_d

let get_min_defined_symb c =
	c.min_defined_symb

let assign_ground c =
	set_bool_param (is_ground c) ground c

let assign_epr c =
	set_bool_param (is_epr c) epr c

let assign_horn c =
	set_bool_param (is_horn c) horn c

let assign_has_eq c =
	set_bool_param (has_eq_lit c) has_eq_lit_param c


let assign_res_sel_lits sel_lits clause =
	clause.res_sel_lits <- Def(sel_lits)

let res_sel_is_def clause =
	match clause.res_sel_lits with
	| Def(_) -> true
	| Undef -> false

exception Sel_lit_not_in_cluase
let rec find_sel_place sel_lit lit_list =
	match lit_list with
	| h:: tl ->
			if (h == sel_lit) then 0
			else 1 + (find_sel_place sel_lit tl)
	|[] -> raise Sel_lit_not_in_cluase

let assign_inst_sel_lit sel_lit clause =
	let sel_place = find_sel_place sel_lit clause.literals in
	(* Format.eprintf
	"Selecting literal %s in clause (%d) %s@."
	(Term.to_string sel_lit)
	(match clause.fast_key with
	| Def key -> key
	| Undef -> -1)
	(to_string clause); *)
	clause.inst_sel_lit <- Def((sel_lit, sel_place))

let assign_dismatching dismatching clause =
	clause.dismatching <- Def(dismatching)

exception Res_sel_lits_undef
let get_res_sel_lits clause =
	match clause.res_sel_lits with
	| Def(sel_lits) -> sel_lits
	| Undef -> raise Res_sel_lits_undef

exception Inst_sel_lit_undef
let get_inst_sel_lit clause =
	match clause.inst_sel_lit with
	| Def((sel_lit, _)) -> sel_lit
	| Undef -> raise Inst_sel_lit_undef

exception Parent_undef
let get_parent clause =
	clause.parent
(* match clause.parent with
| Def(p) -> p
| Undef -> raise Parent_undef *)

let compare_sel_place cl1 cl2 =
	match (cl1.inst_sel_lit, cl2.inst_sel_lit) with
	| (Def((_, sp1)), Def((_, sp2)))
	-> Pervasives.compare sp1 sp2
	| _ -> raise Inst_sel_lit_undef

exception Dismatching_undef
let get_dismatching clause =
	match clause.dismatching with
	| Def(dismatching) -> dismatching
	| Undef -> raise Dismatching_undef

let assign_all_for_clause_db clause =
	assign_num_of_symb clause;
	assign_num_of_var clause;
	assign_length clause;
	assign_has_conj_symb clause;
	assign_has_non_prolific_conj_symb clause;
	assign_has_bound_constant clause;
	assign_has_next_state clause;
	assign_has_reachable_state clause;
	assign_max_atom_input_occur clause;
	assign_ground clause;
	assign_epr clause;
	assign_horn clause;
	assign_has_eq clause;
	assign_min_defined_symb clause;
	(* "set_bool_param true in_clause_db clause" should be last! *)
	set_bool_param true in_clause_db clause



let fold_sym f a clause =
	List.fold_left (Term.fold_sym f) a clause.literals

let iter_sym f clause =
	List.iter (Term.iter_sym f) clause.literals

let add_child clause child =
	clause.children <- child:: (clause.children)

let get_children clause = clause.children

let get_activity clause = clause.activity
let assign_activity act clause = clause.activity <- act

(*******************)

(*
let assign_when_born when_born clause =
clause.when_born <- Def(when_born)
(* match clause.when_born with
| Undef -> clause.when_born <- Def(when_born)
| _ -> failwith "clause: clause when_born is already assigned"
*)
*)

(* assigns when the clause born based on when the clauses in the premise where born *)
(*                                    *)
(* if the the prem1 and prem2 is [] then zero is assined (e.g. imput clauses) *)
(* we assign when_born when 1) conclusion of an inference was generated       *)
(* 2) clause is simplified and 3) splitting 4)model transformation/equation axiom  *)
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

let assign_when_born prem1 prem2 clause =
	let born_list1 = List.map when_born prem1 in
	let born_list2 = List.map when_born prem2 in
	let inv_compare = compose_sign false Pervasives.compare in
	(* finds min element *)
	let min_prem1 = list_find_max_element_zero inv_compare born_list1 in
	let min_prem2 = list_find_max_element_zero inv_compare born_list2 in
	let max_born = list_find_max_element Pervasives.compare [min_prem1; min_prem2] in
	let when_cl_born = max_born + 1 in
	clause.when_born <- Def(when_cl_born)



(* match clause.when_born with
| Undef -> clause.when_born <- Def(when_born)
| _ -> failwith "clause: clause when_born is already assigned"
*)

(* ********************************************************************** *)

let get_tstp_source = function
	| { tstp_source = Def s } -> s
	| { tstp_source = Undef } -> raise (Failure "Clause source not defined")

(* Assign source of clause, fail if source not undefined *)
let assign_tstp_source clause source =
	
	match clause.tstp_source with
	
	(* Fail if source already defined *)
	| Def _ -> raise (Failure "Clause source already assigned")
	
	(* Only if source undefined *)
	| Undef -> clause.tstp_source <- Def source

(* Clause is generated in an instantiation inference *)
let assign_tstp_source_instantiation clause parent parents_side =
	
	assign_tstp_source
		clause
		(TSTP_inference_record ((Instantiation parents_side), [parent]))

(* Clause is generated in a resolution inference *)
let assign_tstp_source_resolution clause parents upon_literals =
	
	assign_tstp_source
		clause
		(TSTP_inference_record ((Resolution upon_literals), parents))

(* Clause is generated in a factoring inference *)
let assign_tstp_source_factoring clause parent upon_literals =
	
	assign_tstp_source
		clause
		(TSTP_inference_record ((Factoring upon_literals), [parent]))

let assign_tstp_source_subtyping clause parent =
	assign_tstp_source
		clause
		(TSTP_inference_record ((Subtyping), [parent]))

(* Clause is in input *)
let assign_tstp_source_input clause file name =
	
	assign_tstp_source
		clause
		(TSTP_external_source (TSTP_file_source (file, name)))

(* Clause is generated in a global propositional subsumption *)
let assign_tstp_source_global_subsumption max_clause_id clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Global_subsumption max_clause_id, [parent]))

(* Clause is generated in a translation to purely equational problem *)
let assign_tstp_source_non_eq_to_eq clause parent =
	
	assign_tstp_source
		clause
		(TSTP_internal_source TSTP_non_eq_to_eq)

(* Clause is generated in a forward subsumption resolution *)
let assign_tstp_source_forward_subsumption_resolution clause main_parent parents =
	
	assign_tstp_source
		clause
		(TSTP_inference_record
			(Forward_subsumption_resolution, (main_parent :: parents)))

(* Clause is generated in a backward subsumption resolution *)
let assign_tstp_source_backward_subsumption_resolution clause parents =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Backward_subsumption_resolution, parents))

(* Clause is generated in splitting *)
let assign_tstp_source_split symbols clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Splitting symbols, [parent]))

let assign_tstp_source_flattening clause parent =
	assign_tstp_source
		clause
		(TSTP_inference_record (Flattening, [parent]))

(* Clause is generated in grounding *)
let assign_tstp_source_grounding grounding clause parent =
	
	assign_tstp_source
		clause
		(TSTP_inference_record (Grounding grounding, [parent]))

(* Clause is a theory axiom *)
let assign_tstp_source_theory_axiom clause theory =
	
	assign_tstp_source
		clause
		(TSTP_external_source (TSTP_theory theory))

(* Clause is an equality axiom *)
let assign_tstp_source_axiom_equality clause =
	assign_tstp_source_theory_axiom clause TSTP_equality

(* Clause is a distinct axiom *)
let assign_tstp_source_axiom_distinct clause =
	assign_tstp_source_theory_axiom clause TSTP_distinct

(* Clause is an less axiom *)
let assign_tstp_source_axiom_less clause =
	assign_tstp_source_theory_axiom clause TSTP_less

(* Clause is an range axiom *)
let assign_tstp_source_axiom_range clause =
	assign_tstp_source_theory_axiom clause TSTP_range

(* Clause is an bmc1 axiom *)
let assign_tstp_source_axiom_bmc1 bmc1_axiom clause =
	assign_tstp_source_theory_axiom clause (TSTP_bmc1 bmc1_axiom)

(* Clause is generated in grounding *)
let assign_tstp_source_assumption clause =
	assign_tstp_source clause (TSTP_internal_source TSTP_assumption)

(* history assignments *)
(*
let assign_instantiation_history clause parent parents_side =
match clause.history with
| Undef -> clause.history <- Def (Instantiation (parent, parents_side))
| Def _ -> failwith "clause: history  is already assigned"

let assign_resolution_history clause parents upon_literals =
match clause.history with
| Undef -> clause.history <- Def(Resolution(parents, upon_literals))
| _ -> failwith "clause: history  is already assigned"

let assign_factoring_history clause parent upon_literals =
match clause.history with
| Undef -> clause.history <- Def(Factoring(parent, upon_literals))
| _ -> failwith "clause: history  is already assigned"

let assign_input_history clause =
match clause.history with
| Undef -> clause.history <- Def(Input)
| _ -> failwith "clause: history  is already assigned"

let assign_global_subsumption_history clause parent =
match clause.history with
| Undef -> clause.history <- Def(Global_Subsumption(parent))
| _ -> failwith "clause: history  is already assigned"

let assign_non_eq_to_eq_history clause parent =
match clause.history with
| Undef -> clause.history <- Def(Non_eq_to_eq(parent))
| _ -> failwith "clause: history  is already assigned"

let assign_forward_subsumption_resolution_history clause main_parent parents =
match clause.history with
| Undef -> clause.history <- Def(Forward_Subsumption_Resolution(main_parent, parents))
| _ -> failwith "clause: history  is already assigned"

let assign_backward_subsumption_resolution_history clause parents =
match clause.history with
| Undef -> clause.history <- Def(Backward_Subsumption_Resolution(parents))
| _ -> failwith "clause: history  is already assigned"

let assign_axiom_history axiom clause =
clause.history <- Def(Axiom (axiom))

let assign_axiom_history_cl_list axiom cl_list =
List.iter (assign_axiom_history axiom) cl_list

let assign_split_history concl parent =
concl.history <- Def(Split(parent))

*)

module Key =
struct
	type t = clause
	
	let rec hash = function
		
		(* Use key if defined *)
		| { fast_key = Def k } -> k
		
		(* Assign key and hash otherwise *)
		| _ as clause ->
		
		(* Assign temporary key to clause and use this key *)
				assign_temp_key clause; hash clause
	
	let rec compare = function
		
		(* First clause is in a database with fast key assigned *)
		| { db_id = Def d1; fast_key = Def k1 } ->
		
				(
					
					function
					
					(* Second clause is in a database with fast key assigned *)
					| { db_id = Def d2; fast_key = Def k2 } ->
					
					(* Compare databases and keys lexicographically *)
							pair_compare_lex
								Pervasives.compare
								Pervasives.compare
								(d1, k1)
								(d2, k2)
					
					(* Second clause is in a database without a fast key *)
					| { db_id = Def d2; fast_key = Undef } ->
					
					(* Clauses in a database must have a fast key *)
							raise Clause_fast_key_undef
					
					(* Second clause is not in a database *)
					| { db_id = Undef } ->
					
					(* Clauses in a database are greater *)
							1
					
				)
		
		(* First clause is in a database without a fast key *)
		| { db_id = Def d1; fast_key = Undef } ->
		
		(* Clauses in a database must have a fast key *)
				raise Clause_fast_key_undef
		
		(* First clause is not in a database, but has temporary key *)
		| { db_id = Undef; fast_key = Def k1 } as c1 ->
		
				(
					
					function
					
					(* Second clause is in a database with fast key assigned *)
					| { db_id = Def _; fast_key = Def _ } ->
					
					(* Clauses in a database are greater *)
					-1
					
					(* Second clause is in a database without a fast key *)
					| { db_id = Def _; fast_key = Undef } ->
					
					(* Clauses in a database must have a fast key *)
							raise Clause_fast_key_undef
					
					(* Second clause is not in a database but has a temporary key *)
					| { db_id = Undef; fast_key = Def k2 } ->
					
					(* Compare temporary fast keys *)
							Pervasives.compare k1 k2
					
					(* Second clause is not in a database and has no temporary key *)
					| { db_id = Undef; fast_key = Undef } as c2 ->
					
					(* Assign temporary key to clause and compare again *)
							assign_temp_key c2; compare c1 c2
					
				)
		
		(* First clause is not in a database and has no temporary key *)
		| { db_id = Undef; fast_key = Undef } as c1 ->
		
				function c2 ->
				
				(* Assign temporary key to clause and compare again *)
						assign_temp_key c1; compare c1 c2
	
	let equal c1 c2 = (compare c1 c2) = 0
	
end

module Map = Map.Make(Key)

module Set = Set.Make(Key)
type clause_set = Set.t

module Hashtbl = Hashtbl.Make(Key)

let clause_list_to_set clause_list =
	List.fold_left (fun set cl -> Set.add cl set) Set.empty clause_list

(*

let rec get_history_parents' visited accum = function

(* No more clause histories to recurse *)
| [] -> accum

(* Clause already seen *)
| (clause :: tl) when ClauseHashtbl.mem visited clause ->

(* Skip clause *)
get_history_parents' visited accum tl

(* Undefined parents *)
| ({ history = Undef } as clause) :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Add clause as leaf *)
get_history_parents'
visited
(clause :: accum)
tl

(* Clause after instantiation *)
| { history = Def (Instantiation (parent, parents_side)) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parents of premises *)
get_history_parents'
visited
accum
((parent :: parents_side) @ tl)

(* Clause after resolution *)
| { history = Def (Resolution (parents, upon_literals)) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parents of premises *)
get_history_parents'
visited
accum
(parents @ tl)

(* Clause after factoring *)
| { history = Def (Factoring (parent, upon_literals)) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parent of premise *)
get_history_parents'
visited
accum
(parent :: tl)

(* Input clause *)
| { history = Def Input } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Add clause as leaf *)
get_history_parents'
visited
(clause :: accum)
tl

(* Clause after global subsumption *)
| { history = Def (Global_Subsumption parent) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parent of premise *)
get_history_parents'
visited
accum
(parent ::
((Prop_solver_exchange.justify_prop_subsumption parent clause) @ tl))

(* Clause after tranformation to pure equational clause *)
| { history = Def (Non_eq_to_eq parent) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parent of premise *)
get_history_parents'
visited
accum
(parent :: tl)

(* Clause after forward subsumption resolution *)
| { history = Def (Forward_Subsumption_Resolution (main_parent, parents)) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parents of premises *)
get_history_parents'
visited
accum
(parents @ tl)

(* Clause after backward subsumption resolution *)
| { history = Def (Backward_Subsumption_Resolution parents) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parents of premises *)
get_history_parents'
visited
accum
(parents @ tl)

(* Clause is an axiom *)
| { history = Def (Axiom _) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Add clause as leaf *)
get_history_parents'
visited
(clause :: accum)
tl

(* Clause after splitting *)
| { history = Def (Split parent) } as clause :: tl ->

(* Remeber clause *)
ClauseHashtbl.add visited clause ();

(* Recurse to get parent of premise *)
get_history_parents'
visited
accum
(parent :: tl)

let clause_get_history_parents clause =
get_history_parents' (ClauseHashtbl.create 101) [] [clause]

let clause_list_get_history_parents clause_list =
get_history_parents' (ClauseHashtbl.create 101) [] clause_list

*)

(*****)
(*let add_to_prop_solver solver prop_var_db ground_term clause = *)

(******)

(* Compare two clauses *)
let cmp_num_var c1 c2 =
	(Pervasives.compare (num_of_var c1) (num_of_var c2))

let cmp_num_symb c1 c2 =
	(Pervasives.compare (num_of_symb c1) (num_of_symb c2))

let cmp_num_lits c1 c2 =
	(Pervasives.compare (length c1) (length c2))

let cmp_age c1 c2 =
	- (Pervasives.compare (when_born c1) (when_born c2))

let cmp_ground c1 c2 =
	Pervasives.compare (is_ground c1) (is_ground c2)

let cmp_horn c1 c2 =
	Pervasives.compare (is_horn c1) (is_horn c2)

let cmp_epr c1 c2 =
	Pervasives.compare (is_epr c1) (is_epr c2)

let cmp_bool_param param c1 c2 =
	Pervasives.compare (get_bool_param param c1) (get_bool_param param c2)

let cmp_in_unsat_core c1 c2 =
	cmp_bool_param in_unsat_core c1 c2

let cmp_has_eq_lit c1 c2 =
	Pervasives.compare (has_eq_lit c1) (has_eq_lit c2)

let cmp_has_conj_symb c1 c2 =
	cmp_bool_param has_conj_symb c1 c2

let cmp_has_bound_constant c1 c2 =
	cmp_bool_param has_bound_constant c1 c2

let cmp_has_next_state c1 c2 =
	cmp_bool_param has_next_state c1 c2

let cmp_has_reachable_state c1 c2 =
	cmp_bool_param has_reachable_state c1 c2

let cmp_has_non_prolific_conj_symb c1 c2 =
	cmp_bool_param has_non_prolific_conj_symb c1 c2

let cmp_max_atom_input_occur c1 c2 =
	Pervasives.compare c1.max_atom_input_occur c2.max_atom_input_occur

let cmp_min_defined_symb c1 c2 =
	let d1 = c1.min_defined_symb in
	let d2 = c2.min_defined_symb in
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



exception Literal_not_found

let rec cut_literal_from_list literal list =
	match list with
	| h:: tl ->
			if h == literal then tl
			else h:: (cut_literal_from_list literal tl)
	|[] -> raise Literal_not_found

let cut_literal literal clause =
	create (cut_literal_from_list literal clause.literals)

let is_empty_clause clause =
	if clause.literals = [] then true
	else false

(* let is_eq_clause clause =
List.exists Term.is_eq_lit clause.literals
*)

let apply_bsubst term_db_ref bsubst bclause =
	let (b_c, clause) = bclause in
	let bterm_list = propagate_binding_to_list (b_c, clause.literals) in
	let new_term_list =
		SubstBound.apply_bsubst_btlist term_db_ref bsubst bterm_list in
	create new_term_list

let apply_bsubst_norm_subst term_db_ref bsubst bound clause =
	let bterm_list = propagate_binding_to_list (bound, clause.literals) in
	let (new_term_list, norm_subst) =
		SubstBound.apply_bsubst_btlist_norm_subst
			term_db_ref bsubst bound bterm_list in
	((create_parent clause new_term_list), norm_subst)
(*  (create_parent clause new_term_list,norm_subst)*)

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

(*
| Lit_Ground of bool
| Lit_Num_of_Var of bool
| Lit_Num_of_Symb of bool
| Lit_Split of bool
| Lit_has_conj_symb of bool
| Lit_has_bound_constant of bool
| Lit_next_state of bool
| Lit_reachable_state of bool
(*  | Lit_reachable_state            of bool *)
| Lit_has_non_prolific_conj_symb of bool
| Lit_eq of bool
| Lit_clock of bool
| Lit_less of bool
| Lit_range of bool
*)

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

(* done *)

(*
let normalise_lit_list term_db_ref lit_list =
let sorted_list = List.sort term_compare lit_list in
let var_ref = ref (Var.get_first_var ()) in
let var_table_initsize = 16 in
let var_table = VarTableM.create(var_table_initsize) in
let new_list =
list_map_left
(fun term' ->
TermDB.add_ref (normalise_term_var' var_table var_ref term') term_db_ref)
sorted_list in
let removed_duplicates = list_remove_duplicates new_list in
removed_duplicates
*)

(* works but slow*)
(*
type var_eq = var * var

(*association list*)
type var_eq_list = var_eq list

let rec normalise_term_var'
(env_ref : var_eq_list ref) (max_var_ref : var ref) term =
match term with
| Term.Fun(sym, args, _) ->
let new_args =
Term.arg_map_left (normalise_term_var' env_ref max_var_ref) args in
Term.create_fun_term_args sym new_args
| Term.Var(v, _) ->
try
let new_v = List.assoc v !env_ref in
Term.create_var_term new_v
with
Not_found ->
let old_max_var = !max_var_ref in
env_ref := (v, old_max_var):: (!env_ref);
max_var_ref := Var.get_next_var old_max_var;
Term.create_var_term old_max_var

(*
let normalise_clause_var env_map clause =
*)

(* works but slow*)
let normalise_lit_list term_db_ref lit_list =
let sorted_list = List.sort term_compare lit_list in
let var_ref = ref (Var.get_first_var ()) in
let env_ref = ref [] in
let new_list =
list_map_left
(fun term' ->
TermDB.add_ref (normalise_term_var' env_ref var_ref term') term_db_ref)
sorted_list in
let removed_duplicates = list_remove_duplicates new_list in
removed_duplicates

*)

(*
let normalise term_db_ref clause =
create (normalise_lit_list term_db_ref clause.literals)
*)

(*

type bvar_list = bound_var list
type bvar_eq = bound_var * var
type bvar_eq_list = bvar_eq list

(* rename_bterm_var' changes : add renaming : mapping
from bvar (-- the leafs of the subst.) to new_vars;
max_var is the maximal used variable *)

(* futuer: reoreder lits: max num of vars first, then system preds ?*)
let rec rename_bterm_var' (renaming_ref : bvar_eq_list ref)
(mapped_bvars_ref : bvar_list ref)
(max_var_ref : var ref) bsubst bterm =
let (b_t, term) = bterm in
match term with
| Term.Fun(sym, args, _) ->
Term.arg_iter
(fun term' ->
rename_bterm_var' renaming_ref mapped_bvars_ref
max_var_ref bsubst (b_t, term')
) args

| Term.Var(v, _) ->
let b_v = (b_t, v) in
if not (List.mem b_v !mapped_bvars_ref)
then
try
let new_bterm = SubstBound.find b_v bsubst in
mapped_bvars_ref := b_v::!mapped_bvars_ref;
rename_bterm_var' renaming_ref mapped_bvars_ref
max_var_ref bsubst new_bterm
with
Not_found ->
let old_max_var = !max_var_ref in
renaming_ref := (b_v, old_max_var):: (!renaming_ref);
mapped_bvars_ref := b_v::!mapped_bvars_ref;
max_var_ref := Var.get_next_var old_max_var
else ()

(* start var will be changed to the  var next after the last var*)
(*
let rename_bterm_var (start_var_ref : var ref) bsubst bterm =
let renaming_ref = ref [] and	mapped_bvars_ref = ref [] in
rename_bterm_var' renaming_ref mapped_bvars_ref start_var_ref bsubst bterm
*)

type termDB = TermDB.termDB

exception Add_term_to_db_renaiming_is_incomplete

(* returns new term *)
let rec add_bterm_to_db (term_db_ref : termDB ref)
(renaming : bvar_eq_list) bsubst bterm =
let (b_t, term) = bterm in
match term with
| Term.Fun(sym, args, _) ->
let new_args =
Term.arg_map_left
(fun term' ->
(add_bterm_to_db term_db_ref renaming bsubst (b_t, term'))
) args in
let new_term = Term.create_fun_term_args sym new_args in
TermDB.add_ref new_term term_db_ref
| Term.Var(v, _) ->
let b_v = (b_t, v) in
try
let new_bterm = SubstBound.find b_v bsubst in
add_bterm_to_db term_db_ref renaming bsubst new_bterm
with
Not_found ->
try
let new_var = List.assoc b_v renaming in
let new_term = Term.create_var_term new_var in
TermDB.add_ref new_term term_db_ref
with
Not_found -> raise Add_term_to_db_renaiming_is_incomplete

(*
let rec apply_sub_and_normalise_var' bound_term_list term_db =
*)

(*returns a clause with terms in db*)
let normalise_bterm_list term_db_ref bsubst bterm_list =
let bterm_compare bt bs = bterm_subst_compare bt bs bsubst in
let sorted_list = List.sort bterm_compare bterm_list in
let start_var_ref = ref (Var.get_first_var ()) and
renaming_ref = ref [] and
mapped_bvars_ref = ref [] in
let rename_bterm_var bterm =
rename_bterm_var' renaming_ref mapped_bvars_ref start_var_ref bsubst bterm in
(*change to iter*)
let () = List.iter rename_bterm_var sorted_list in
let add_bterm_to_db' bterm' =
add_bterm_to_db term_db_ref !renaming_ref bsubst bterm' in
list_map_left add_bterm_to_db' sorted_list
*)

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
	normalise_b_litlist_v1 term_db_ref bsubst (b, clause.literals)

let normalise_bclause_list_v1 term_db_ref bsubst bclause_list =
	let blitlist_list =
		List.map
			(fun (b_c, clause) ->
						(b_c, clause.literals)) bclause_list in
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
	create(
			List.concat
				(List.map
						(fun blit_list -> normalise_b_litlist_v2' term_db_ref bsubst blit_list)
						blitlist_list
				)
		)

(* normilse v1 is with reordering for better renaming of vars, *)
(* normalise v2 is simply removes duplicate lits  *)

let normalise_b_litlist = normalise_b_litlist_v1
let normalise_blitlist_list = normalise_blitlist_list_v1

(*
let normalise_b_litlist = normalise_b_litlist_v2
let normalise_blitlist_list = normalise_blitlist_list_v2
*)

let normalise_bclause term_db_ref bsubst bclause =
	let (b_c, clause) = bclause in
	let bterm_list = propagate_binding_to_list (b_c, clause.literals) in
	let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
	create new_term_list

let normalise_bclause_list term_db_ref bsubst bclause_list =
	let bterm_list_list =
		List.map
			(fun (b_c, clause) ->
						propagate_binding_to_list (b_c, clause.literals)) bclause_list in
	let bterm_list = List.flatten bterm_list_list in
	let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
	create new_term_list

(* for uniformity ise normalise_bclause with empty substitution *)

let normalise_lit_list term_db_ref lit_list =
	normalise_blitlist_list term_db_ref (SubstBound.create ()) [(1, lit_list)]

let normalise term_db_ref clause =
	normalise_bclause term_db_ref (SubstBound.create ()) (1, clause)

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
	if (get_bool_param is_dead clause)
	then [clause]
	else
	if (get_bool_param res_simplifying clause)
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

let replace_subterm termdb_ref subterm byterm cluase =
	normalise
		termdb_ref
		(create
			
				(List.map (Term.replace subterm byterm) (get_literals cluase)))

(* done *)
(*

let get_non_simplifying_parents clause =
match clause.history with
| Def(history) ->
(match history with
| Resolution(parents, _upon_literals) -> parents
| Factoring(parent, _upon_literals) -> [parent]
| Input -> []
| _ -> []
)
| Undef -> []

(* we collect all oprphans in a branch to a dead parent *)
(* if we meet a simplifying clause then we stop and do not include this branch*)
let rec get_orphans clause =
if (get_bool_param is_dead clause)
then [clause]
else
if (get_bool_param res_simplifying clause)
then []
else
let parents = get_non_simplifying_parents clause in
let parent_result =
List.fold_left (fun rest curr -> ((get_orphans curr)@rest)) [] parents in
if not (parent_result = [])
then
(clause:: parent_result)
else []

*)

(* root on the top! *)
let dash_str = "--------------------------------------------------\n"

(*
let rec to_stream_history s clause =
match clause.history with
| Def(history) ->
begin
match history with
| Instantiation(parent, parents_side) ->
s.stream_add_str "Instantiation:\n";
s.stream_add_str "concl:  ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
to_stream s parent;
s.stream_add_str "]\n";
s.stream_add_str "side: [";
clause_list_to_stream s parents_side;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
parents_str s [parent];
parents_str s parents_side
| Resolution(parents, upon_literals) ->
s.stream_add_str "Resolution:\n";
s.stream_add_str "concl:  ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
clause_list_to_stream s parents;
s.stream_add_str "]\n";
s.stream_add_str "upon: [";
Term.term_list_to_stream s upon_literals;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
parents_str s parents
| Factoring(parent, upon_literals) ->
s.stream_add_str "Factoring:\n";
s.stream_add_str "concl:  ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
to_stream s parent;
s.stream_add_str "]\n";
s.stream_add_str "upon: [";
Term.term_list_to_stream s upon_literals;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
to_stream_history s parent
| Input ->
s.stream_add_str "Input clause:\n";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str dash_str;

| Global_Subsumption(parent) ->
s.stream_add_str "Global Subsumption:\n";
s.stream_add_str "concl: ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
to_stream s parent;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
to_stream_history s parent

| Non_eq_to_eq(parent) ->
s.stream_add_str "Non Eq to Eq:\n";
s.stream_add_str "concl: ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
to_stream s parent;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
to_stream_history s parent

| Forward_Subsumption_Resolution(main_parent, parents) ->
s.stream_add_str "Forward Subsumption Resolution:\n";
s.stream_add_str "concl:  ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: main: [";
to_stream s main_parent;
s.stream_add_str "]\n";
s.stream_add_str "prem: side: [";
clause_list_to_stream s parents;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
to_stream_history s main_parent;
parents_str s parents

| Backward_Subsumption_Resolution(parents) ->
s.stream_add_str "Backward Subsumption Resolution\n";
s.stream_add_str "concl:  ";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "prem: [";
clause_list_to_stream s parents;
s.stream_add_str "]\n";
s.stream_add_str dash_str;
parents_str s parents

| Axiom(axiom) ->
s.stream_add_str ((axiom_to_string axiom)^"\n");
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str dash_str;

| Split(parent) ->
s.stream_add_str "Split \n";
to_stream s clause;
s.stream_add_str "\n";
s.stream_add_str "From \n";
s.stream_add_str dash_str;
to_stream_history s parent

(* | Simplified parent ->
"Simplification\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)
*)
end
| Undef ->
(
s.stream_add_str "Undef history \n";
to_stream s clause;
s.stream_add_str "\n";

(* out_str ("history is not defined for"(to_string clause)^"\n");

failwith "clasue: to_string_history: history is not defined")
*)
)
and
parents_str s parents =
(List.iter
(fun p_clause -> (to_stream_history s p_clause))
parents)

let rec pp_clause_history ppf = function

| { history = Undef } as clause ->
Format.fprintf
ppf
"Undef history @\n%a@\n%s"
pp_clause
clause
dash_str

| { history = Def (Instantiation (parent, parents_side)) } as clause ->

Format.fprintf
ppf
"Instantiation:@\nconcl:  %a@\nprem: %a@\nside: [%a]@\n%s"
pp_clause clause
pp_clause parent
(pp_any_list pp_clause ",") parents_side
dash_str;

pp_clause_history ppf parent;
pp_clause_list_history ppf parents_side

| { history = Def (Resolution (parents, upon_literals)) } as clause ->

Format.fprintf
ppf
"Resolution:@\nconcl:  %a@\nprem: [%a]@\nupon: [%a]@\n%s"
pp_clause clause
(pp_any_list pp_clause ",") parents
(pp_any_list Term.pp_term ", ") upon_literals
dash_str;

pp_clause_list_history ppf parents

| { history = Def (Factoring (parent, upon_literals)) } as clause ->

Format.fprintf
ppf
"Factoring:@\nconcl:  %a@\nprem: [%a]@\nupon: [%a]@\n%s"
pp_clause clause
pp_clause parent
(pp_any_list Term.pp_term ", ") upon_literals
dash_str;

pp_clause_history ppf parent

| { history = Def Input } as clause ->

Format.fprintf
ppf
"Input clause:@\n%a@\n%s"
pp_clause clause
dash_str

| { history = Def (Global_Subsumption parent) } as clause ->

Format.fprintf
ppf
"Global Subsumption:@\nconcl: %a@\nprem: [%a]@\n%s"
pp_clause clause
pp_clause parent
dash_str;

pp_clause_history ppf parent

| { history = Def (Non_eq_to_eq parent) } as clause ->

Format.fprintf
ppf
"Non Eq to Eq:@\nconcl: %a@\nprem: [%a]@\n%s"
pp_clause clause
pp_clause parent
dash_str;

pp_clause_history ppf parent

| { history = Def (Forward_Subsumption_Resolution (main_parent, parents)) } as clause ->

Format.fprintf
ppf
"Forward Subsumption Resolution:@\nconcl:  %a@\nprem: main: [%a]@\nprem: side: [%a]@\n%s"
pp_clause clause
pp_clause main_parent
(pp_any_list pp_clause ",") parents
dash_str;

pp_clause_list_history ppf parents

| { history = Def (Backward_Subsumption_Resolution parents) } as clause ->

Format.fprintf
ppf
"Backward Subsumption Resolution@\nconcl:  %a@\nprem: [%a]@\n%s"
pp_clause clause
(pp_any_list pp_clause ",") parents
dash_str;

pp_clause_list_history ppf parents

| { history = Def (Axiom axiom) } as clause ->

Format.fprintf
ppf
"%a@\n%a@\n%s"
pp_axiom axiom
pp_clause clause
dash_str;

| { history = Def (Split parent) } as clause ->

Format.fprintf
ppf
"Split@\n%a@\nFrom@\n%s"
pp_clause clause
dash_str;

pp_clause_history ppf parent

and pp_clause_list_history ppf clauses =
List.iter (pp_clause_history ppf) clauses

let out_history = to_stream_history stdout_stream

*)

(*------------------*)
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

(*
let rec to_string_history clause =
match clause.history with
| Def(history) ->
(match history with
| Resolution(parents, upon_literals) ->
("Resolution:\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(clause_list_to_string parents)^"]\n"
^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n"
^"--------------------------------------------------\n"
^(parents_str parents))
| Factoring(parent, upon_literals) ->
"Factoring:\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)
| Input ->
"Input clause:\n"
^(to_string clause)^"\n"
^"---------------------------------------------------\n"

| Global_Subsumption(parent) ->
"Global Subsumption:\n"
^"concl: "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)

| Non_eq_to_eq(parent) ->
"Non Eq to Eq:\n"
^"concl: "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)

| Forward_Subsumption_Resolution(main_parent, parents) ->
("Forward Subsumption Resolution:\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: main:"^"["^(to_string main_parent)^"]\n"
^"prem: side:"^"["^(clause_list_to_string parents)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history main_parent)
^(parents_str parents))

| Backward_Subsumption_Resolution(parents) ->
("Backward Subsumption Resolution\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(clause_list_to_string parents)^"]\n"
^"--------------------------------------------------\n"
^(parents_str parents))

(* | Simplified parent ->
"Simplification\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)
*)
)
| Undef ->
(out_str ("history is not defined for"^(to_string clause)^"\n");
failwith "clasue: to_string_history: history is not defined")
and
parents_str parents =
(List.fold_left
(fun rest p_clause -> rest^(to_string_history p_clause))
"" parents)

*)

(*----------Commented--------------------*)
(*

(* root on the top!
path_str it a string of numbers corresponding to
the path of the clause in the proof tree *)
(*
let rec to_string_history path_str clause =
match clause.history with
| Def(history) ->
(match history with
| Resolution(parents, upon_literals) ->
let str_this_inf =
("Resolution----------------------------------------\n"
^"concl:  "^path_str^(to_string clause)^"\n"
^"prem: "^"["^(clause_list_to_string parents)^"]\n"
^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n"
^"--------------------------------------------------\n") in
let str_parents =
(List.fold_left
(fun rest p_clause -> rest^(to_string_history p_clause))
"" parents) in
str_this_inf^str_parents
| Factoring(parent, upon_literals) ->
"Factoring----------------------------------------\n"
^"concl:  "^(to_string clause)^"\n"
^"prem: "^"["^(to_string parent)^"]\n"
^"upon:"^"["^(Term.term_list_to_string upon_literals)^"]\n"
^"--------------------------------------------------\n"
^(to_string_history parent)
| Input ->
"Input clause----------------------------------------\n"
^(to_string clause)^"\n"
^"---------------------------------------------------\n"
)
| Undef -> failwith "clasue: to_string_history: history is not defined"
*)

*)
(*----------Commented--------------------*)

(*
let to_string clause =
"{"^(list_to_string Term.to_string clause.literals ";")^"}"
^"-num of sym-"^(string_of_int (get_num_of_sym clause))
*)

(* tmp*)





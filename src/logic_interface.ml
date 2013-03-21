(* to generate interface *)
(* ocamlc -I obj/ -i src/logic_interface.ml > src/logic_interface.mli *)
open Lib

type var    = Var.var
type symbol = Symbol.symbol
type stype = Symbol.stype
type term = Term.term
type args = Term.args
type lit = Term.term
type literal = lit
type clause = Clause.clause
type tstp_source = Clause.tstp_source
type context = Clause.context
type proof_search_param = Clause.proof_search_param

let symbol_db_ref = Parser_types.symbol_db_ref
let term_db_ref = Parser_types.term_db_ref
let context = Parser_types.context

(* first when term_db_ref is a parameter *)

(*----------------- symbols ---------------------------------*)

(*let creat_const_symb symb_name ~symb_type =*)
let create_symbol symbol_name symbol_stype =
	SymbolDB.add_ref
			(Symbol.create_from_str_type symbol_name symbol_stype)
			symbol_db_ref
	

(*---------------terms/lits----------------------------------*)
let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let add_fun_term_args symb args = 
  TermDB.add_ref (Term.create_fun_term_args symb args) term_db_ref

let add_var_term var = 
  TermDB.add_ref (Term.create_var_term var) term_db_ref
					
let add_typed_equality_term stype_term t s =
	let args = [stype_term; t; s] in
	add_fun_term Symbol.symb_typed_equality args

let add_typed_equality_term_sym eq_type_sym t s =
	let eq_type_term = (add_fun_term eq_type_sym []) in
	add_typed_equality_term eq_type_term t s


let add_neg_atom atom =
	let args = [atom] in
	add_fun_term Symbol.symb_neg args

let add_compl_lit lit = 
	TermDB.add_ref (Term.compl_lit lit) term_db_ref 
	
(*
let dis_equality t s =
	neg_atom (equality_term t s)
*)

let add_typed_dis_equality stype t s =
	add_neg_atom (add_typed_equality_term stype t s)

(* used for model output *)
let add_term_algebra_eq_term args = 
    let ta_eq_type_term = (add_fun_term Symbol.symb_term_algebra_type []) in
	 add_fun_term Symbol.symb_typed_equality  (ta_eq_type_term::args)

(*--------clause---------------*)	

let create_clause tstp_source proof_search_param lits = 
	let norm_lits = Clause.normalise_lit_list term_db_ref lits in
	Clause.create_clause term_db_ref tstp_source proof_search_param norm_lits	

let create_clause_context context tstp_source proof_search_param lits =
	let clause = create_clause tstp_source proof_search_param lits in
	Clause.context_add context clause


let create_clause_res tstp_source lits =
  create_clause
  	  tstp_source (Clause.Res_param(Clause.create_res_param ()))  lits	

let create_clause_inst tstp_source lits =
  create_clause
  	 tstp_source (Clause.Inst_param(Clause.create_inst_param ()))  lits	
  
let create_clause_empty_param tstp_source lits =
  create_clause
     tstp_source (Clause.Empty_param)  lits	

let get_lits c = Clause.get_lits c

let clause_register_subsumed_by ~by c = 
   Clause.assign_is_dead true c;
	 Clause.set_ps_simplifying true by;
   Clause.assign_simplied_by (Def(Clause.Simp_by_subsumption by)) c
	
let normalise_blitlist_list blitlist_list = 
	Clause.normalise_blitlist_list term_db_ref blitlist_list 		

(*---------- context ----------------*)				
let context_create = Clause.context_create
let context_add  = Clause.context_add
let context_remove = Clause.context_remove  
let context_mem = Clause.context_mem 
let context_reset = Clause.context_reset 
let context_find = Clause.context_find
let context_iter = Clause.context_iter 
let context_fold = Clause.context_fold 
let context_size = Clause.context_size

(* context_add_context from_cxt to_cxt *)
let context_add_context = Clause.context_add_context
 
(** replaces dead with simplified_by *)
let context_replace_dead = Clause.context_replace_dead 	
		


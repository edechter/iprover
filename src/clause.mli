(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2012 Konstantin Korovin and The University of Manchester. 
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

type var           = Var.var
type literal       = Term.literal
type term          = Term.term
type symbol        = Symbol.symbol
type literal_list  = literal list
type term_db       = TermDB.termDB
type subst         = Subst.subst
type bound         = int
type bound_subst   = SubstBound.bound_subst
type clause
type bound_clause = clause Lib.bind


type sym_set = Symbol.sym_set

module ClauseHashtbl : Hashtbl.S with type key = clause

type tstp_internal_source = 
  | TSTP_definition 
  | TSTP_assumption
  | TSTP_non_eq_to_eq

type tstp_theory_bmc1 = 
  | TSTP_bmc1_path_axiom of int 
  | TSTP_bmc1_reachable_state_axiom of int 
  | TSTP_bmc1_reachable_state_conj_axiom of int 
  | TSTP_bmc1_reachable_state_on_bound_axiom of int
	| TSTP_bmc1_reachable_sk_replacement of int * clause  (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)
  | TSTP_bmc1_only_bound_reachable_state_axiom of int 
	| TSTP_bmc1_clock_axiom of int * Symbol.symbol * (int list)
  | TSTP_bmc1_instantiated_clause of int * clause

type tstp_theory =
  | TSTP_equality
  | TSTP_distinct
  | TSTP_bmc1 of tstp_theory_bmc1
  | TSTP_less
  | TSTP_range

type tstp_external_source =
  | TSTP_file_source of string * string
  | TSTP_theory of tstp_theory

type tstp_inference_rule =
  | Instantiation of clause list
  | Resolution of literal list
  | Factoring of literal list
  | Global_subsumption of int
  | Forward_subsumption_resolution 
  | Backward_subsumption_resolution
  | Splitting of symbol list
  | Grounding of (Var.var * Term.term) list
  | Subtyping
	| Flattening

type tstp_inference_record = 
    tstp_inference_rule * clause list 

type tstp_source = 
  | TSTP_external_source of tstp_external_source
  | TSTP_internal_source of tstp_internal_source
  | TSTP_inference_record of tstp_inference_record

type axiom = 
  |Eq_Axiom 
  |Distinct_Axiom 
  |Less_Axiom 
  |Range_Axiom 
  |BMC1_Axiom 
 

(* all boolean param are set false and other Undef*)
val create         : literal_list -> clause
val create_parent  : clause -> literal_list -> clause

(* boolean parameters of te clause*)
type clause_bool_param 

val is_dead                      : clause_bool_param 
val in_clause_db                 : clause_bool_param
val in_active                    : clause_bool_param
val in_unif_index                : clause_bool_param
val in_subset_subsumption_index  : clause_bool_param
val in_subsumption_index         : clause_bool_param
val in_prop_solver               : clause_bool_param
val inst_in_sim_passive          : clause_bool_param 
val inst_pass_queue1             : clause_bool_param 
val inst_pass_queue2             : clause_bool_param 
val inst_pass_queue3             : clause_bool_param 
val res_pass_queue1              : clause_bool_param 
val res_pass_queue2              : clause_bool_param 
val res_in_sim_passive           : clause_bool_param 
val res_sel_max                  : clause_bool_param 
val eq_axiom                     : clause_bool_param 
val input_under_eq               : clause_bool_param 
val has_conj_symb                : clause_bool_param 
val has_bound_constant           : clause_bool_param  
val has_next_state               : clause_bool_param  
val has_reachable_state          : clause_bool_param  
val has_non_prolific_conj_symb   : clause_bool_param 
val in_unsat_core                : clause_bool_param 
val large_ax_considered          : clause_bool_param  



 (* if used in simplifications then simplifying is true *)
(* used in orphan elimination since we can eliminate only non-simplifying clauses *)
val res_simplifying                  : clause_bool_param 

(* creates a new copy of the clause with the same parameters,*) 
(* terms are not re-created *)
val copy_clause  : clause -> clause
val copy_clause_undef_fast_key  : clause -> clause

val set_bool_param : bool ->  clause_bool_param -> clause -> unit
val get_bool_param : clause_bool_param -> clause -> bool 
(* inherit_bool_param param from_c to_c *)
val inherit_bool_param     :  clause_bool_param -> clause -> clause -> unit
(* inherit_bool_param_all  from_c to_c *)
val inherit_bool_param_all :  clause -> clause -> unit

(* inherit relevant parameters for clauses obtained by modification: *)
(* it can be simplified by prop_subsumption or obtained by splitting *)
(*let inherit_param_modif from_c to_c = *)

val inherit_param_modif : clause -> clause -> unit 

(* fist form, second to*)
(* val inherit_history : clause -> clause -> unit *)
val inherit_tstp_source : clause -> clause -> unit

val num_of_symb                 : clause -> int 
val num_of_var                  : clause -> int 

val length                      : clause -> int 

(* can be used in e.g. resolution loops for calculating age*)
val when_born                   : clause -> int

(* adds all vars of the clause to the set *)
val add_var_set : Var.VSet.t -> clause -> Var.VSet.t

val get_var_list: clause -> var list 

(*-------------------assignments------------------*)

(* assigns when the clause born based on when the clauses in the premise where born *)
(* when_born=max(min(pem1),min(prem2)) + 1                            *)
(* if the the prem1 and prem2 is [] then zero is assined (e.g. imput clauses) *)

val assign_when_born         : clause list ->clause list -> clause -> unit


val assign_res_sel_lits          : literal_list -> clause -> unit

val assign_inst_sel_lit          : literal -> clause -> unit

(* conjecture distance *)

(* big int  *)
val max_conjecture_dist : int

(* all input conjectures 0 *)
val conjecture_int      : int

val is_negated_conjecture : clause -> bool

(* inherit_conj_dist from_c to_c*)
val inherit_conj_dist : clause -> clause -> unit
val get_min_conjecture_distance  : clause list -> int

(* assign max {int,max_conjecture_dist}*)
val assign_conjecture_distance   : int -> clause -> unit
val cmp_conjecture_distance      : clause -> clause -> int
val get_conjecture_distance      : clause -> int
val cmp_has_conj_symb                : clause -> clause -> int
val cmp_has_non_prolific_conj_symb   : clause -> clause -> int

exception Res_sel_lits_undef
val get_res_sel_lits             : clause -> literal_list
val res_sel_is_def               : clause -> bool

exception Inst_sel_lit_undef
val get_inst_sel_lit            : clause -> literal

val get_parent                  : clause -> clause Lib.param

(*
val clause_get_history_parents : clause -> clause list 

val clause_list_get_history_parents : clause list -> clause list 
*)

(* comapares places of two clauses, is used to compare that   *)
(* sel literal in parent corresponds to sel lit in child      *)
(* do not renormalise parents and children!*)
val compare_sel_place           : clause -> clause -> int


type dismatching = Dismatching.constr_set

(*type dismatching = Dismatching.constr_list_feature*)

val assign_dismatching : dismatching -> clause -> unit

exception Dismatching_undef
val get_dismatching : clause -> dismatching

val get_tstp_source : clause -> tstp_source 

	
(** Clause is generated in an instantiation inference *)
val assign_tstp_source_instantiation : clause -> clause -> clause list -> unit


(** Clause is generated in a resolution inference *)
val assign_tstp_source_resolution : clause -> clause list -> literal list -> unit 

(** Clause is generated in a factoring inference *)
val assign_tstp_source_factoring : clause -> clause -> literal list -> unit


(** Clause is in input *)
val assign_tstp_source_input : clause -> string -> string -> unit


(** Clause is generated in a global propositional subsumption *)
val assign_tstp_source_global_subsumption : int -> clause -> clause -> unit


(** Clause is generated in a translation to purely equational problem *)
val assign_tstp_source_non_eq_to_eq : clause -> clause -> unit


(** Clause is generated in a forward subsumption resolution *)
val assign_tstp_source_forward_subsumption_resolution : clause -> clause -> clause list -> unit


(** Clause is generated in a backward subsumption resolution *)
val assign_tstp_source_backward_subsumption_resolution : clause -> clause list -> unit


(** Clause is generated in splitting with split symbols introduced *)
val assign_tstp_source_split : symbol list -> clause -> clause -> unit 

(** assign_tstp_source_flattening clause parent *)
val assign_tstp_source_flattening : clause -> clause -> unit 


(** Clause is generated in grounding with variable substitutions *)
val assign_tstp_source_grounding : (Var.var * Term.term) list -> clause -> clause -> unit 

val assign_tstp_source_subtyping : clause -> clause -> unit 


(** Clause is an equality axiom *)
val assign_tstp_source_axiom_equality : clause -> unit

(** Clause is a distinct axiom *)
val assign_tstp_source_axiom_distinct : clause -> unit

(** Clause is an less axiom *)
val assign_tstp_source_axiom_less : clause -> unit

(** Clause is an range axiom *)
val assign_tstp_source_axiom_range : clause -> unit

(** Clause is an bmc1 axiom *)
val assign_tstp_source_axiom_bmc1 : tstp_theory_bmc1 -> clause -> unit

(** Clause is an assumption *)
val assign_tstp_source_assumption : clause -> unit


(*
val assign_instantiation_history : clause -> clause -> clause list -> unit

(* history when this clause is obtined by resolution from parents upon_literals*)
(* first arg is the conclusion, sencod arg are parents *) 
val assign_resolution_history : clause -> clause list -> literal list -> unit 

(* history when this clause is obtined by factoring from parent upon_literals*)

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_factoring_history : clause -> clause -> literal list -> unit

val assign_input_history : clause -> unit

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_global_subsumption_history : clause -> clause -> unit

(* first arg is the conclusion, sencod arg is the parent *) 
val assign_non_eq_to_eq_history : clause -> clause -> unit

(* the first arg is the conclusion, the sencod arg is the main parent *)
(* and the third is the list of side parents*) 
val assign_forward_subsumption_resolution_history : clause -> clause -> clause list -> unit

val assign_backward_subsumption_resolution_history : clause -> clause list -> unit

val assign_axiom_history : axiom -> clause -> unit
val assign_axiom_history_cl_list : axiom -> clause list -> unit

(* first arg is the resulting clause second arg is the parent *)
val assign_split_history : clause -> clause -> unit
*)

(* first is parent second is child*)
val add_child : clause -> clause -> unit
val get_children : clause -> clause list

val get_orphans : clause -> clause list

val get_activity : clause -> int
val assign_activity : int -> clause -> unit 


(******)

val assign_all_for_clause_db : clause -> unit

exception Clause_fast_key_is_def

(* only to be used in clauseDB where the fast_key is assigned*)
val assign_fast_key : clause -> int -> unit

(* If a clause has a fast_key, then the db_id is set to a unique
   identifier of the clause database it was added to. This is
   necessary to get unique clause names. *)
exception Clause_db_id_is_def
val assign_db_id : clause -> int -> unit


exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

val assign_prop_solver_id : clause -> int -> unit

val get_prop_solver_id : clause -> int option



(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. clauseDB is build; 
   before that use compare_key the same for equal*)  

val compare  : clause -> clause -> int 
val equal    : clause -> clause -> bool             

(* 
  compare_key impl. as structural equality used for clauseDB 
  we assume that literals in clause are in termDB *)

val compare_key           : clause -> clause -> int
val compare_fast_key      : clause -> clause -> int


(* physical membership  *)
val memq    : literal -> clause -> bool

val exists      : (literal -> bool) -> clause -> bool
val find        : (literal -> bool) -> clause -> literal
val fold        : ('a -> literal -> 'a) -> 'a -> clause -> 'a 
val find_all    : (literal -> bool) -> clause -> literal_list
val partition   : (literal -> bool) -> clause -> literal_list * literal_list
val iter        : (literal -> unit) -> clause -> unit

val get_literals : clause -> literal_list

val is_empty_clause : clause -> bool

(*val is_eq_clause    : clause -> bool*)

val is_ground          : clause -> bool
val is_epr             : clause -> bool
val is_horn            : clause -> bool
val has_eq_lit         : clause -> bool

val get_min_defined_symb : clause -> int param

(*Comapre two clauses*)
val cmp_num_var  : clause -> clause -> int
val cmp_num_symb : clause -> clause -> int
val cmp_num_lits : clause -> clause -> int
val cmp_age      : clause -> clause -> int
val cmp_ground   : clause -> clause -> int
val cmp_in_unsat_core : clause -> clause -> int


val assign_has_conj_symb              : clause -> unit
val assign_has_non_prolific_conj_symb : clause -> unit


val cl_cmp_type_list_to_lex_fun : 
    Options.cl_cmp_type list -> (clause -> clause -> int) 

(* folds f on all symbols in the clause *)
val fold_sym : ('a -> symbol -> 'a) -> 'a -> clause -> 'a 

val iter_sym : (symbol-> unit) -> clause -> unit

(* returns clause without cut literal, 
  literal should be physically equal to literal in clause, 
  raises Literal_not_found otherwise 
 *)

(*  should use get_literals
val cut_literal : literal -> clause -> clause *)

val apply_bsubst : term_db ref -> bound_subst -> bound_clause -> clause 

val apply_bsubst_norm_subst :  
    term_db ref -> bound_subst -> bound -> clause -> clause * subst

(* during normalisations below obtained literals are added to term_db*)
val normalise_lit_list :  term_db ref -> literal_list ->literal_list
val normalise :  term_db ref -> clause -> clause

type b_litlist = literal_list Lib.bind

val normalise_b_litlist : 
    term_db ref -> bound_subst -> b_litlist -> literal_list 

val normalise_blitlist_list :
    term_db ref -> bound_subst -> (b_litlist list) -> literal_list 

 

(*
val normalise_bclause : 
    bound_clause -> bound_subst -> term_db ref -> clause

val normalise_bclause_list : 
    bound_clause list -> bound_subst -> term_db ref -> clause
*)


val to_stream                  : 'a string_stream -> clause -> unit
val out                        : clause -> unit

(** Print the name of a clause

   Clauses are named [c_n], where [n] is the identifier (fast_key) of
   the clause. If the identifier is undefined, the clause is named
   [c_tmp].
*)
val pp_clause_name : Format.formatter -> clause -> unit


val pp_clause : Format.formatter -> clause -> unit
val pp_clause_literals_tptp : Format.formatter -> clause -> unit
val pp_clause_tptp : Format.formatter -> clause -> unit
val pp_clause_list_tptp : Format.formatter -> clause list -> unit

val pp_clause_min_depth : Format.formatter -> clause -> unit

val tptp_to_stream             : 'a string_stream -> clause -> unit
val out_tptp                   : clause -> unit

val clause_list_to_stream      : 'a string_stream -> clause list -> unit
val out_clause_list            : clause list -> unit

val clause_list_tptp_to_stream : 'a string_stream -> clause list -> unit
val out_clause_list_tptp       : clause list -> unit

val to_string : clause -> string
val to_tptp   : clause -> string 
val clause_list_to_string : clause list -> string
val clause_list_to_tptp   : clause list -> string

(* val to_stream_history : 'a string_stream -> clause -> unit *)

(* val pp_clause_history : Format.formatter -> clause -> unit *)


(* val out_history       : clause -> unit *)



(*--------------------------*)
type clause_signature = {
  mutable sig_fun_preds : sym_set;
  mutable sig_eq_types  : sym_set;
}

val create_clause_sig : unit -> clause_signature

(* main fun  *)
val clause_list_signature : clause list -> clause_signature

val extend_clause_sig_term : clause_signature -> Term.term -> unit
val extend_clause_sig_lit  : clause_signature -> Term.term -> unit
val extend_clause_sig_cl   : clause_signature -> clause -> unit
val extend_clause_list_signature : clause_signature -> clause list -> unit


(*-----assume clause is of the from [pred(sK)] where sK is a state skolem fun---*)
val get_skolem_bound_clause : clause -> Term.term option

(*val replace_subterm : term_db ref -> subterm:term ->  byterm:term -> clause -> clause*)

val replace_subterm : term_db ref -> term ->  term -> clause -> clause

open Lib

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
type dismatching = Dismatching.constr_set
type literal = Term.literal
type lit = literal
type lits = lit list
type literal_list = literal list
type b_litlist = literal_list Lib.bind

exception Term_compare_greater
exception Term_compare_less

(* type basic_clause *)

type sel_place = int

type clause
and proof_search_param
and replaced_by =
	| RB_subsumption of clause
	| RB_sub_typing of clause
	| RB_splitting of clause list
  | RB_tautology_elim
	| RB_orphan_elim of clause (* is not used  for replacements *)

(*and axiom = Eq_Axiom | Distinct_Axiom | Less_Axiom | Range_Axiom | BMC1_Axiom*)
and tstp_internal_source =
		TSTP_definition
	| TSTP_assumption
	| TSTP_tmp
and tstp_theory_bmc1 =
		TSTP_bmc1_path_axiom of int
	| TSTP_bmc1_reachable_state_axiom of int
	| TSTP_bmc1_reachable_state_conj_axiom of int
	| TSTP_bmc1_reachable_state_on_bound_axiom of int
(*	|  TSTP_bmc1_reachable_sk_replacement of int * clause *)
	| TSTP_bmc1_only_bound_reachable_state_axiom of int
	| TSTP_bmc1_clock_axiom of int * Symbol.symbol * int list
(*	| TSTP_bmc1_instantiated_clause of int * clause *)
and tstp_theory =
		TSTP_equality
	| TSTP_distinct
	| TSTP_domain
	| TSTP_bmc1 of tstp_theory_bmc1
	| TSTP_less
	| TSTP_range
and tstp_external_source =
		TSTP_file_source of string * string
	| TSTP_theory of tstp_theory
and tstp_inference_rule =
		Instantiation of clause list
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
	| Eq_res_simp
  | TSTP_bmc1_instantiated_clause of int 
  | TSTP_bmc1_reachable_sk_replacement of int (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)

and tstp_inference_record = tstp_inference_rule * clause list
and tstp_source =
		TSTP_external_source of tstp_external_source
	| TSTP_internal_source of tstp_internal_source
	| TSTP_inference_record of tstp_inference_record

type bound_clause = clause Lib.bind
(*type bound_bclause = basic_clause Lib.bind *)

(* val get_bclause : clause -> basic_clause *)

(*type lits_fast_key*)

val get_fast_key : clause -> int
(*
val compare_lits : clause -> clause -> int
val equal_lits : clause -> clause -> bool
*)

(*
val get_lits_fast_key : clause -> basic_clause
val get_lits_hash : clause -> basic_clause
val lits_compare : lits_fast_key -> lits_fast_key -> int
val lits_equal : clause -> clause -> bool
*)
(*
val get_context_id : clause -> int
*)
(*
val compare_basic_clause :
'a Hashcons.hash_consed -> 'b Hashcons.hash_consed -> int

val equal_basic_clause : 'a -> 'a -> bool
*)

(*val compare_clause : clause -> clause -> int*)

val equal_clause : clause -> clause -> bool
val equal : clause -> clause -> bool
val compare : clause -> clause -> int

(* val set_bool_param_bc :
bool -> int -> basic_clause_node Hashcons.hash_consed -> unit
*)

(*val get_bool_param_bc : int -> basic_clause_node Hashcons.hash_consed -> bool*)

(* *)
(*
val is_ground_lits : Term.term list -> bool
val is_ground_bc : basic_clause_node Hashcons.hash_consed -> bool
val is_horn_lits : Term.literal list -> bool
val is_horn_bc : basic_clause_node Hashcons.hash_consed -> bool
val is_epr_lits : Term.term list -> bool
val is_epr_bc : basic_clause_node Hashcons.hash_consed -> bool
val has_eq_lit_lits : Term.literal list -> bool

val exists_lit_with_true_bool_param :
Term.fun_term_bool_param -> Term.term list -> bool

val has_conj_symb_lits : Term.term list -> bool
val has_non_prolific_conj_symb_lits : Term.term list -> bool
val has_bound_constant_lits : Term.term list -> bool
val has_next_state_lits : Term.term list -> bool
val has_reachable_state_lits : Term.term list -> bool
val length_lits : 'a list -> int
val num_of_symb_lits : Term.term list -> int
val num_of_var_lits : Term.term list -> int

val max_atom_input_occur_lits : Term.literal list -> Term.symbol
val min_defined_symb_lits : Term.term list -> int Lib.param
type 'a bool_param_fill_list = (('a -> bool) * int) list
val fill_bool_params :
(('a -> bool) * int) list -> 'a -> Bit_vec.bit_vec -> Bit_vec.bit_vec
val auto_bool_param_fill_list : ((Term.literal list -> bool) * int) list
val template_bc_node : literal_list -> basic_clause_node
val fill_bc_auto_params : basic_clause_node -> unit

val create_basic_clause :
literal_list -> BClause_Htbl.key Hashcons.hash_consed
*)

(**)
(* val max_conjecture_dist : int
val conjecture_int : int
*)

(*
module KeyContext :
sig
type t = basic_clause
type e = clause
val hash : 'a Hashcons.hash_consed -> int
val equal : 'a Hashcons.hash_consed -> 'b Hashcons.hash_consed -> bool
val assign_fast_key : clause -> int -> unit
val assign_db_id : clause -> int -> unit
end

module Context :
sig
type key = KeyContext.t
type e = Keyclause
type assign_map = AssignMap.Make(KeyContext).assign_map
val create : int -> string -> assign_map
val get_name : assign_map -> string
val get_map_id : assign_map -> int
val mem : assign_map -> key -> bool
val find : assign_map -> key -> e
val size : assign_map -> int
val fold : (key -> e -> 'a -> 'a) -> assign_map -> 'a -> 'a
val iter : (key -> e -> unit) -> assign_map -> unit
val add : assign_map -> key -> e -> e
val remove : assign_map -> key -> unit
val to_stream :
'a Lib.string_stream ->
('a Lib.string_stream -> e -> unit) -> string -> assign_map -> unit
val out :
(out_channel Lib.string_stream -> e -> unit) ->
string -> assign_map -> unit
val to_string :
(Buffer.t Lib.string_stream -> e -> unit) ->
string -> assign_map -> string
val get_key_counter : assign_map -> int
end
*)

(** a clauses always placed in a context *)

type context

(** create_context size name; size approximate initial size *)
val context_create : int -> context
val context_add : context -> clause -> clause
val context_remove : context -> clause -> unit

val context_mem : context -> clause -> bool

(* literals are not normalised unlike wnen create_clause *)
val context_mem_lits : context -> lits -> bool

(* val context_reset : context -> unit *)
val context_find : context -> clause -> clause

(* literals are not normalised unlike wnen create_clause *)
val context_find_lits : context -> lits -> clause
val context_iter : context -> (clause -> unit) -> unit
val context_fold : context -> (clause -> 'a -> 'a) -> 'a -> 'a
val context_size : context -> int

(* context_add_context from_cxt to_cxt *)
val context_add_context : context -> context -> unit

(** replaces clausews with replaced_by (recusively) *)
(*val context_replace_by : context -> clause -> clause list*)
val context_replace_by_clist :  context -> clause list -> clause list
(*val template_clause : basic_clause -> clause*)

(** creates a clause within a context; use create_neg_conjecture if a clause is a negate conjectue *)
(** literals are normalised, use create_clause_raw for creating with literals as it is *)
val create_clause :
term_db_ref -> tstp_source -> literal_list -> clause

val create_neg_conjecture :
term_db_ref -> tstp_source -> literal_list -> clause

(* clause with literals as it is (non-normalised)*)
val create_clause_raw :
tstp_source -> literal_list -> clause

val copy_clause : clause -> clause

(* clears tstp_source of the clause should not be used after that     *)
(* unless it was recoreded in propositional solver for proof purposes *)

(*val clear_clause : clause -> unit*)

(*-----*)
val get_lits : clause -> literal_list

(** get_literals = get_lits *)
val get_literals : clause -> literal_list

val lits_equal : clause -> clause -> bool	
(*val compare_lits : clause -> clause -> int*)

val is_empty_clause : clause -> bool

(**-------- output ------------*)

val to_stream : 'a Lib.string_stream -> clause -> unit

val out : clause -> unit

val to_string : clause -> string

val clause_list_to_stream : 'a Lib.string_stream -> clause list -> unit

val out_clause_list : clause list -> unit

val clause_list_to_string : clause list -> string

(* val axiom_to_string : axiom -> string *)

val tptp_to_stream : 'a Lib.string_stream -> clause -> unit
val out_tptp : clause -> unit
val to_tptp : clause -> string
val clause_list_tptp_to_stream : 'a Lib.string_stream -> clause list -> unit
val out_clause_list_tptp : clause list -> unit
val clause_list_to_tptp : clause list -> string

(**------pretty priting------------*)
(* val pp_axiom : Format.formatter -> axiom -> unit *)
val pp_clause_name : Format.formatter -> clause -> unit
val pp_clause_with_id : Format.formatter -> clause -> unit
val pp_clause : Format.formatter -> clause -> unit
val pp_clause_min_depth : Format.formatter -> clause -> unit
val pp_literals_tptp : Format.formatter -> Term.term list -> unit
val pp_clause_literals_tptp : Format.formatter -> clause -> unit
val pp_clause_tptp : Format.formatter -> clause -> unit
val pp_clause_list_tptp : Format.formatter -> clause list -> unit

val pp_clause_with_source :

(* function for global justification of global subsumption, default is None, see tstpProof for such function *)
?global_subsumption_justification_fun: (int ->
clause -> clause -> clause list)
option ->
(* default is false *)
?clausify_proof: bool ->
	Format.formatter ->
clause -> unit

val pp_clause_list_with_source :
?global_subsumption_justification_fun: (int ->
clause -> clause -> clause list)
option ->
?clausify_proof: bool ->
	Format.formatter ->
clause list -> unit

(* output of parameters of a clause *)
(*
type clause_fun_type =
		FInt of (clause -> int)
	| FStr of (clause -> string)
	| FFloat of (clause -> float)
	| FBool of (clause -> bool)
	| FTerm of (clause -> term)
	| FTerm_list of (clause -> term list)
	| FSymb of (clause -> symbol)
	| FClause of (clause -> clause)
	| FClause_list of (clause -> clause list)
	| FReplaced_by of (clause -> replaced_by)
*)

type 'a fun_type =
    FInt of ('a -> int)
  | FStr of ('a -> string)
  | FFloat of ('a -> float)
  | FBool of ('a -> bool)
  | FTerm of ('a -> term)
  | FTerm_list of ('a -> term list)
  | FSymb of ('a -> symbol)
  | FClause of ('a -> clause)
  | FClause_list of ('a -> clause list)
  | FReplaced_by of ('a -> replaced_by)

type clause_fun_type = clause fun_type

(* one can output any list of [(paremater_name, fun_type)] *)
(* predefined param_lists are below *)

type param_out_list = (string * clause_fun_type) list

val param_out_list_gen : param_out_list
val param_out_list_bmc1 : param_out_list
val param_out_list_ps : param_out_list
val param_out_list_res : param_out_list
val param_out_list_inst : param_out_list
val param_out_list_all : param_out_list

val pp_clause_params :
param_out_list -> Format.formatter -> clause -> unit

(*-------------------*)

val get_proof_search_param : clause -> proof_search_param

exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

val assign_prop_solver_id : clause -> int -> unit
val get_prop_solver_id : clause -> int option

(* val get_bc : clause -> basic_clause
val get_bc_node : clause -> basic_clause_node
val equal_bc : clause -> clause -> bool
*)

(*------------*)
val memq : literal -> clause -> bool
val exists : (literal -> bool) -> clause -> bool
val find : (literal -> bool) -> clause -> literal
val fold : ('a -> literal -> 'a) -> 'a -> clause -> 'a
val find_all : (literal -> bool) -> clause -> literal list
val partition : (literal -> bool) -> clause -> literal list * literal list
val iter : (literal -> unit) -> clause -> unit

(*
val bc_set_bool_param : bool -> int -> clause -> unit
val bc_get_bool_param : int -> clause -> bool
val ccp_get_bool_param : int -> clause -> bool
val ccp_set_bool_param : bool -> int -> clause -> unit
*)

(** general clause params *)
val is_negated_conjecture : clause -> bool
val is_ground : clause -> bool
val is_horn : clause -> bool
val is_epr : clause -> bool
val is_eq_axiom : clause -> bool
val assign_is_eq_axiom : bool -> clause -> unit
val has_eq_lit : clause -> bool
val has_conj_symb : clause -> bool
val has_non_prolific_conj_symb : clause -> bool
val has_bound_constant : clause -> bool
val has_next_state : clause -> bool
val has_reachable_state : clause -> bool
val num_of_symb : clause -> int
val num_of_var : clause -> int
val length : clause -> int
val get_max_atom_input_occur : clause -> symbol Lib.param
val get_min_defined_symb : clause -> int Lib.param

(** get/assign general clause params *)

val assign_tstp_source : clause -> tstp_source -> unit
val get_tstp_source : clause -> tstp_source

(** non recursive *)
val get_replaced_by : clause -> replaced_by Lib.param

(** recursively until non_replaced clauses *)
(*val get_replaced_by_rec : clause list -> clause list*)

val assign_replaced_by : replaced_by Lib.param -> clause -> unit

val get_conjecture_distance : clause -> int
val assign_conjecture_distance : int -> clause -> unit

val inherit_conj_dist : clause -> clause -> unit
val get_min_conjecture_distance_clist : clause list -> int

val get_is_dead : clause -> bool
val assign_is_dead : bool -> clause -> unit

val in_unsat_core : clause -> bool
val assign_in_unsat_core : bool -> clause -> unit

val in_prop_solver : clause -> bool
val assign_in_prop_solver : bool -> clause -> unit

(* reevaluates has_non_prolific_conj_symb, assuming lits are already reevaluated *)
val reset_has_non_prolific_conj_symb : clause -> unit
val reset_has_conj_symb : clause -> unit

(** proof search bool param*)
val get_ps_in_active : clause -> bool
val set_ps_in_active : bool -> clause -> unit
val get_ps_in_unif_index : clause -> bool
val set_ps_in_unif_index : bool -> clause -> unit
val get_ps_in_subset_subsumption_index : clause -> bool
val set_ps_in_subset_subsumption_index : bool -> clause -> unit
val get_ps_in_subsumption_index : clause -> bool
val set_ps_in_subsumption_index : bool -> clause -> unit
val get_ps_in_sim_passive : clause -> bool
val set_ps_in_sim_passive : bool -> clause -> unit
val get_ps_pass_queue1 : clause -> bool
val set_ps_pass_queue1 : bool -> clause -> unit
val get_ps_pass_queue2 : clause -> bool
val set_ps_pass_queue2 : bool -> clause -> unit
val get_ps_pass_queue3 : clause -> bool
val set_ps_pass_queue3 : bool -> clause -> unit
val get_ps_sel_max : clause -> bool
val set_ps_sel_max : bool -> clause -> unit
val get_ps_simplifying : clause -> bool
val set_ps_simplifying : bool -> clause -> unit

(** proof search non-bool param *)

val clear_proof_search_param : clause -> unit

val get_ps_when_born : clause -> int
val assign_ps_when_born : int -> clause -> unit

val assign_ps_when_born_concl :
prem1: clause list -> prem2: clause list -> c: clause -> unit

val add_ps_child : clause -> child: clause -> unit
val get_ps_children : clause -> clause list

(** res non-bool param *)

exception Res_sel_lits_undef
val res_sel_is_def : clause -> bool
val get_res_sel_lits : clause -> literal_list
val res_assign_sel_lits : literal_list -> clause -> unit

(** inst bool param *)

(** inst non-bool param *)

exception Sel_lit_not_in_cluase
val inst_find_sel_place : 'a -> 'a list -> int
val inst_assign_sel_lit : literal -> clause -> unit
val inst_assign_dismatching : dismatching -> clause -> unit
exception Inst_sel_lit_undef
val inst_get_sel_lit : clause -> term
val inst_compare_sel_place : clause -> clause -> int
exception Dismatching_undef
val get_inst_dismatching : clause -> dismatching
val inst_get_activity : clause -> int
val inst_assign_activity : int -> clause -> unit

(**---- tstp sources -----*)
val tstp_source_instantiation : clause -> clause list -> tstp_source
val tstp_source_resolution : clause list -> literal list -> tstp_source
val tstp_source_factoring : clause -> literal list -> tstp_source
val tstp_source_subtyping : clause -> tstp_source
val tstp_source_input : string -> string -> tstp_source
val tstp_source_global_subsumption : int -> clause -> tstp_source
val tstp_source_non_eq_to_eq : clause -> tstp_source
val tstp_source_forward_subsumption_resolution :
clause -> clause list -> tstp_source
val tstp_source_backward_subsumption_resolution : clause list -> tstp_source
val tstp_source_split : symbol list -> clause -> tstp_source
val tstp_source_flattening : clause -> tstp_source
val tstp_source_grounding : (var * term) list -> clause -> tstp_source
val tstp_source_theory_axiom : tstp_theory -> tstp_source
val tstp_source_axiom_equality : tstp_source
val tstp_source_axiom_distinct : tstp_source
val tstp_source_axiom_domain : tstp_source
val tstp_source_axiom_less : tstp_source
val tstp_source_axiom_range : tstp_source
val tstp_source_axiom_bmc1 : tstp_theory_bmc1 -> tstp_source
val tstp_source_assumption : tstp_source
val tstp_source_definition : tstp_source
val tstp_source_tmp : tstp_source

(*
val tstp_source_instantiation :
clause -> clause list -> unit
val assign_tstp_source_resolution :
clause -> clause list -> literal list -> unit
val assign_tstp_source_factoring : clause -> clause -> literal list -> unit
val assign_tstp_source_subtyping : clause -> clause -> unit
val assign_tstp_source_input : clause -> string -> string -> unit
val assign_tstp_source_global_subsumption : int -> clause -> clause -> unit
val assign_tstp_source_non_eq_to_eq : clause -> 'a -> unit
val assign_tstp_source_forward_subsumption_resolution :
clause -> clause -> clause list -> unit
val assign_tstp_source_backward_subsumption_resolution :
clause -> clause list -> unit
val assign_tstp_source_split : symbol list -> clause -> clause -> unit
val assign_tstp_source_flattening : clause -> clause -> unit
val assign_tstp_source_grounding :
(var * term) list -> clause -> clause -> unit
val assign_tstp_source_theory_axiom : clause -> tstp_theory -> unit
val assign_tstp_source_axiom_equality : clause -> unit
val assign_tstp_source_axiom_distinct : clause -> unit
val assign_tstp_source_axiom_less : clause -> unit
val assign_tstp_source_axiom_range : clause -> unit
val assign_tstp_source_axiom_bmc1 : tstp_theory_bmc1 -> clause -> unit
val assign_tstp_source_assumption : clause -> unit
*)

(**---------*)
val fold_sym : ('a -> Term.symbol -> 'a) -> 'a -> clause -> 'a
val iter_sym : (Term.symbol -> unit) -> clause -> unit

val cut_literal_from_list : term -> term list -> term list

val cmp : ('a -> 'b) -> 'a -> 'a -> int
val cmp_num_var : clause -> clause -> int
val cmp_num_symb : clause -> clause -> int
val cmp_num_lits : clause -> clause -> int
val cmp_age : clause -> clause -> int
val cmp_ground : clause -> clause -> int
val cmp_horn : clause -> clause -> int
val cmp_epr : clause -> clause -> int
val cmp_in_unsat_core : clause -> clause -> int
val cmp_has_eq_lit : clause -> clause -> int
val cmp_has_conj_symb : clause -> clause -> int
val cmp_has_bound_constant : clause -> clause -> int
val cmp_has_next_state : clause -> clause -> int
val cmp_has_reachable_state : clause -> clause -> int
val cmp_has_non_prolific_conj_symb : clause -> clause -> int
val cmp_conjecture_distance : clause -> clause -> int
val cmp_max_atom_input_occur : clause -> clause -> int
val cmp_min_defined_symb : clause -> clause -> int
val cl_cmp_type_to_fun : Options.cl_cmp_type -> clause -> clause -> int
val cl_cmp_type_list_to_lex_fun :
Options.cl_cmp_type list -> clause -> clause -> int
exception Literal_not_found

module Key :
sig
	type t = clause
	val equal : 'a -> 'a -> bool
	val hash : clause -> int
	val compare : clause -> clause -> int
end

module Map :
sig
	type key = Key.t
	type 'a t = 'a Map.Make(Key).t
	val empty : 'a t
	val is_empty : 'a t -> bool
	val mem : key -> 'a t -> bool
	val add : key -> 'a -> 'a t -> 'a t
	val singleton : key -> 'a -> 'a t
	val remove : key -> 'a t -> 'a t
	val merge :
	(key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
	val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
	val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
	val iter : (key -> 'a -> unit) -> 'a t -> unit
	val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
	val for_all : (key -> 'a -> bool) -> 'a t -> bool
	val exists : (key -> 'a -> bool) -> 'a t -> bool
	val filter : (key -> 'a -> bool) -> 'a t -> 'a t
	val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
	val cardinal : 'a t -> int
	val bindings : 'a t -> (key * 'a) list
	val min_binding : 'a t -> key * 'a
	val max_binding : 'a t -> key * 'a
	val choose : 'a t -> key * 'a
	val split : key -> 'a t -> 'a t * 'a option * 'a t
	val find : key -> 'a t -> 'a
	val map : ('a -> 'b) -> 'a t -> 'b t
	val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
end

module Set :
sig
	type elt = Key.t
	type t = Set.Make(Key).t
	val empty : t
	val is_empty : t -> bool
	val mem : elt -> t -> bool
	val add : elt -> t -> t
	val singleton : elt -> t
	val remove : elt -> t -> t
	val union : t -> t -> t
	val inter : t -> t -> t
	val diff : t -> t -> t
	val compare : t -> t -> int
	val equal : t -> t -> bool
	val subset : t -> t -> bool
	val iter : (elt -> unit) -> t -> unit
	val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
	val for_all : (elt -> bool) -> t -> bool
	val exists : (elt -> bool) -> t -> bool
	val filter : (elt -> bool) -> t -> t
	val partition : (elt -> bool) -> t -> t * t
	val cardinal : t -> int
	val elements : t -> elt list
	val min_elt : t -> elt
	val max_elt : t -> elt
	val choose : t -> elt
	val split : elt -> t -> t * bool * t
end

type clause_set = Set.t

module Hashtbl :
sig
	type key = Key.t
	type 'a t = 'a Hashtbl.Make(Key).t
	val create : int -> 'a t
	(*    val clear : 'a t -> unit *)
	(*    val reset : 'a t -> unit *)
	val copy : 'a t -> 'a t
	val add : 'a t -> key -> 'a -> unit
	val remove : 'a t -> key -> unit
	val find : 'a t -> key -> 'a
	val find_all : 'a t -> key -> 'a list
	val replace : 'a t -> key -> 'a -> unit
	val mem : 'a t -> key -> bool
	val iter : (key -> 'a -> unit) -> 'a t -> unit
	val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
	val length : 'a t -> int
(*   val stats : 'a t -> Hashtbl.statistics *)
end

val clause_list_to_set : Set.elt list -> Set.t

val apply_bsubst :
SubstBound.term_db_ref ->
SubstBound.bound_subst -> int -> Term.term list -> SubstBound.term list

val apply_bsubst_norm_subst :
SubstBound.term_db_ref ->
SubstBound.bound_subst ->
SubstBound.bound ->
Term.term list -> SubstBound.term list * SubstBound.subst

(**-----normalisations--------*)

val normalise_b_litlist :
TermDB.termDB ref ->
SubstBound.bound_subst ->
Term.literal list Lib.bind -> SubstBound.term list

val normalise_blitlist_list :
TermDB.termDB ref ->
SubstBound.bound_subst ->
Term.literal list Lib.bind list -> Term.term list

val normalise_lit_list :
TermDB.termDB ref -> Term.literal list -> Term.term list

(*
val create_normalise :
TermDB.termDB ref ->
context ->
tstp_source ->
proof_search_param -> Term.literal list -> clause
*)

(*--------------*)
val get_non_simplifying_parents : clause -> clause list
val get_orphans : clause -> clause list
val get_skolem_bound_clause : clause -> Term.term option

(*--------------*)
val replace_subterm :
TermDB.termDB ref ->
Term.term -> Term.term -> Term.term list -> Term.term list

(**---clause signature ----*)

type sym_set = Symbol.sym_set

type clause_signature = {
	mutable sig_fun_preds : sym_set;
	mutable sig_eq_types : sym_set;
}
val create_clause_sig : unit -> clause_signature
val extend_clause_sig_term : clause_signature -> Term.term -> unit
val extend_clause_sig_lit : clause_signature -> Term.literal -> unit
val extend_clause_sig_cl : clause_signature -> clause -> unit
val extend_clause_list_signature : clause_signature -> clause list -> unit
val clause_list_signature : clause list -> clause_signature

(*-------------*)
val add_var_set : Var.VSet.t -> clause -> Var.VSet.t
val get_var_list : clause -> Var.VSet.elt list


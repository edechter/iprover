(* Logical interface *)
(* shorthands for frequently used functions: building terms, clauses, equiations etc. *)

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

(** db_refs are taken from Parser_types*)
val symbol_db_ref : SymbolDB.symbolDB ref
val term_db_ref : TermDB.termDB ref

(** create_symbol symbol_name symbol_stype *)

val create_symbol : string -> stype -> symbol

(** add_fun_term symb arg_list *)
val add_fun_term : symbol -> term list -> term

(** add_fun_term_args symb args *)
val add_fun_term_args : symbol -> args -> term

(** add_var_term var *)
val add_var_term : var -> term

(** add_neg_atom atom *)
val add_neg_atom : term -> term

(** add_compl_lit lit  *)
val add_compl_lit : term -> term

(**  add_typed_equality_term stype_term t s *)
val add_typed_equality_term :
  term -> term -> term -> term

(** add_typed_equality_term_sym eq_type_sym t s *)
val add_typed_equality_term_sym :
  symbol -> term -> term -> term

(** add_term_algebra_eq_term args *)
val add_term_algebra_eq_term : term list -> term


val add_typed_dis_equality :
  term -> term -> term -> term

(**---------Clause-----------*)
(** create_clause tstp_source proof_search_param lits *)
val create_clause :
  tstp_source -> 
	lit list -> clause

(** create_clause_context: creats and add clause to context/returns old if already exists in the context *)
val create_clause_context :
  context ->
  tstp_source ->
	lit list -> clause
	
	
val get_lits : clause -> lit list
	
val clause_register_subsumed_by : by:clause -> clause -> unit

val normalise_blitlist_list :
  SubstBound.bound_subst ->
  ((lit list) Lib.bind) list -> term list
	
	
(**------------clause context-------------------*)	
(** create_context size name; size approximate initial size *)
val context_create : int -> context
val context_add : context -> clause -> clause
val context_remove : context -> clause -> unit
val context_mem : context -> clause -> bool
val context_reset : context -> unit
val context_find : context -> clause -> clause
val context_iter : context -> (clause -> unit) -> unit
val context_fold : context -> (clause -> 'a -> 'a) -> 'a -> 'a
val context_size : context -> int

(* context_add_context from_cxt to_cxt *)
val context_add_context : context -> context -> unit
(** replaces dead with simplified_by *)
val context_replace_by : context -> unit
	
		

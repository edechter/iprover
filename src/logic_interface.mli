(* Logical interface *)
(* shorthands for frequently used functions: building terms, clauses, equiations etc. *)

open Lib

type var    = Var.var
type symbol = Symbol.symbol
type stype = Symbol.stype
type term = Term.term
type args = Term.args
type lit = term
type lits = lit list
type literal = lit
type clause = Clause.clause
type tstp_source = Clause.tstp_source
type context = Clause.context
type proof_search_param = Clause.proof_search_param

exception Empty_Clause of clause 

type symbol_db_ref = SymbolDB.symbolDB ref
type term_db_ref = TermDB.termDB ref

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
val add_neg_atom_symb : symbol -> term list -> term

(** add_compl_lit lit  *)
val add_compl_lit : term -> term

(**  add_typed_equality_term stype_term t s *)
val add_typed_equality_term :
  term -> term -> term -> term

val add_typed_disequality_term :
  term -> term -> term -> term


(** add_typed_equality_term_sym eq_type_sym t s *)
val add_typed_equality_sym :
  symbol -> term -> term -> term

val add_typed_disequality_sym :
  symbol -> term -> term -> term
	
	
(** add_term_algebra_eq_term args *)
val add_term_algebra_eq_term : term list -> term

(*-----------term views----------*)
(* term_eq_view_type_term decomposes equational term into *)
(* Def(Eq_type_term(equality_type_term, t,s)) or Undef if term is not equality  *)

type eq_view_type_term = Eq_type_term of term * term * term
val term_eq_view_type_term : Term.term -> eq_view_type_term param

(* term_eq_view_type_symb is similar only equality_type_symb in place of  equality_type_term *)
(* should be used with care since we assume that eq type is not a variable here *)	
type eq_view_type_symb = Eq_type_symb of symbol * term * term
val term_eq_view_type_symb : Term.term -> eq_view_type_symb param


(**---------Clause-----------*)


(** create_clause tstp_source proof_search_param lits, can raise  Empty_clause (empty_clause) *)
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

	
(**--- pretty printing clause ----*)		

val pp_clause_with_source :
			(* function for global justification of global subsumption, default is None, see tstpProof for such function *)
  ?global_subsumption_justification_fun:(int ->
                                         clause -> clause -> clause list)
                                        option ->
(* default is false *)																											
  ?clausify_proof:bool -> 
  Format.formatter ->
	clause -> unit

val pp_clause_list_with_source :
  ?global_subsumption_justification_fun:(int ->
                                         clause -> clause -> clause list)
                                        option ->													
  ?clausify_proof:bool -> 
	Format.formatter ->
	clause list -> unit

	
	
(**------------clause context-------------------*)	
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
(** replaces dead with simplified_by *)
val context_replace_by_clist : context -> clause list -> clause list
	
		

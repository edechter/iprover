(* Logical interface *)
(* shorthands for frequently used functions: building terms, clauses, equiations etc. *)

type var    = Var.var
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol
type context = Clause.context
type proof_search_param = Clause.proof_search_param



val add_fun_term : Term.symbol -> Term.term list -> TermDB.term

val add_fun_term_args : Term.symbol -> Term.args -> TermDB.term

val add_var_term : Term.var -> TermDB.term

val create_clause :
  Clause.context ->
  Clause.tstp_source ->
  Clause.proof_search_param -> 
	Term.literal list -> Clause.clause

val add_typed_equality_term :
  Term.term -> Term.term -> Term.term -> TermDB.term

val add_typed_equality_term_sym :
  Term.symbol -> TermDB.term -> TermDB.term -> TermDB.term

val add_term_algebra_eq_term : TermDB.term list -> TermDB.term

val add_neg_atom : Term.term -> TermDB.term

val add_compl_lit : Term.term -> TermDB.term

val add_typed_dis_equality :
  Term.term -> Term.term -> Term.term -> TermDB.term

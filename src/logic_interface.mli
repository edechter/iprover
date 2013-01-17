(* Logical interface *)
(* shorthands for frequently used functions: building terms, clauses, equiations etc. *)


val add_fun_term : Term.symbol -> Term.term list -> TermDB.term

val add_fun_term_args : Term.symbol -> Term.args -> TermDB.term

val add_var_term : Term.var -> TermDB.term

val new_clause : Clause.literal_list -> Clause.clause

val add_typed_equality_term :
  Term.term -> Term.term -> Term.term -> TermDB.term
val add_typed_equality_term_sym :
  Term.symbol -> TermDB.term -> TermDB.term -> TermDB.term

val add_term_algebra_eq_term : TermDB.term list -> TermDB.term

val add_neg_atom : Term.term -> TermDB.term

val add_compl_lit : Term.term -> TermDB.term

val add_typed_dis_equality :
  Term.term -> Term.term -> Term.term -> TermDB.term

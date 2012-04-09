
type clause = Clause.clause

(* side clauses are theory clauses: they are used to block removing needed     *)
(* clauses from the clause set but are not added to the resulting filtered set *)
(* sem_filter_unif clause_list side_clause_list *)

val sem_filter_unif : clause list -> clause list -> clause list

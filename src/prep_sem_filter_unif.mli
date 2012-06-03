
type clause = Clause.clause

(* filtered_clauses  are used for output only *)
type filtered_clauses =
    {

      filtered_in  : clause list;
(* filtered out clauses are used in model representation *)
(* for convenience  clauses get assigned inst_sel_lit which *)
(* are the literals true in the model *)
      filtered_out : clause list 
   }


(* sem_filter_unif clause_list side_clause_list *)
(* side clauses are theory clauses: they are used to block removing needed     *)
(* clauses from the clause set but are not added to the resulting filtered set *)


val sem_filter_unif : clause list -> clause list -> filtered_clauses



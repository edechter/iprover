(* to generate interface *)
(* ocamlc -I obj/ -i src/logic_interface.ml > src/logic_interface.mli *)

let term_db_ref = Parser_types.term_db_ref

(* first when term_db_ref is a parameter *)

let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let add_fun_term_args symb args = 
  TermDB.add_ref (Term.create_fun_term_args symb args) term_db_ref

let add_var_term var = 
  TermDB.add_ref (Term.create_var_term var) term_db_ref
	
let new_clause lits = Clause.normalise term_db_ref (Clause.create lits)

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
	

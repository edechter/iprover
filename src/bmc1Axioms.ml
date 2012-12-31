(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006 -2012 Konstantin Korovin and The University of Manchester.
This file is part of iProver - a theorem prover for first - order logic.

iProver is free software: you can redistribute it and / or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
iProver is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
See the GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with iProver. If not, see < http:// www.gnu.org / licenses />. *)
(*----------------------------------------------------------------------[C]-*)

open Lib
open Options
open Statistics
type clause = Clause.clause

(* The symbol database *)
let symbol_db = Parser_types.symbol_db_ref

(* The term database *)
let term_db = Parser_types.term_db_ref

(* Assumptions for previous bounds *)
let invalid_bound_assumptions = ref []

(* Clauses to be instantiated for each bound *)
let bound_instantiate_axioms = ref []

(* in state preinstantiation strategy separated next state clauses *)
let next_state_clauses = ref []

(* Skolem constants occurring in  [$$reachableState(sK)] clauses *)
let reach_bound_skolem_constants = ref []

(* clauses which contain reach_bound_skolem_constants/ used in state pre-inst *)
let has_reach_bound_skolem_constants = ref []

(********** Symbol names and name patterns **********)

(* Type of addresses *)
let address_type = Symbol.symb_ver_address_type

(* Type of states *)
let state_type = Symbol.symb_ver_state_type

(* Type of bitindexes *)
let bitindex_type = Symbol.symb_ver_bit_index_type

(* Name of path symbol *)
(*let path_symbol_name = "$$nextState"*)

(* Name of reachable state symbol *)
let reachable_state_symbol_name = "$$reachableState"

(* Name of addressDiff symbol *)
let address_diff_symbol_name = "$$addressDiff"

(* Name of addressDiff symbol *)
let address_val_symbol_name = "$$addressVal"

(* Name of address symbol *)
let address_symbol_name = "$$address"

(* Format of symbol for active bound *)
let bound_symbol_format = format_of_string "$$iProver_bound%d"

(* Format of symbol for bitindex *)
let bitindex_symbol_format = format_of_string "bitindex%d"

(* Format of state symbol *)
let state_symbol_format = format_of_string "$$constB%d"

(* Format of constant address term *)
let constant_address_term_format = format_of_string "%s_address_term"

(* Format of transient address term *)
let transient_address_term_format =
	format_of_string "%s_address_term_bound_%d"

(********** Generic functions **********)

(*
(* Get n-th variable recursively *)
let rec var_n' accum = function

(* Terminate and return accumulated variable *)
| 0 -> accum

(* Fail for negaive variable numbers *)
| i when i < 0 -> failwith ("Bmc1Axioms.var_n: variable number must be >= 0")

(* Recurse to get next variable *)
| i -> var_n' (Var.get_next_var accum) (pred i)
*)

(* Get n-th variable *)
let var_n vtype n = Var.create vtype n
(*	var_n' (Var.get_first_var ()) n*)

(* Get n-th variable term *)
let term_xn vtype n =
	TermDB.add_ref
		(Term.create_var_term (var_n vtype n))
		term_db

(* Create term for variable X0 *)
let term_x0 vtype = TermDB.add_ref (term_xn vtype 0) term_db

(* Create term for variable X1 *)
let term_x1 vtype = TermDB.add_ref (term_xn vtype 1) term_db

(* Create term for variable X2 *)
let term_x2 vtype = TermDB.add_ref (term_xn vtype 2) term_db

(* Create typed equation *)
let create_typed_equation stype lhs rhs =
	
	(* Add or retrieve type term from term database *)
	let stype_term =
		TermDB.add_ref
			(Term.create_fun_term stype [])
			term_db
	in
	
	(* Add or retrieve equation from term database *)
	TermDB.add_ref
		(Term.create_fun_term
				Symbol.symb_typed_equality
				[stype_term; lhs; rhs])
		term_db

(* Create term *)
let create_term symbol_name symbol_type =
	
	(* Type of symbol *)
	let symbol_stype = Symbol.create_stype [] symbol_type in
	
	(* Add symbol to symbol database *)
	let symbol =
		SymbolDB.add_ref
			(Symbol.create_from_str_type symbol_name symbol_stype)
			symbol_db
	in
	
	(* Add term to term database *)
	let term =
		TermDB.add_ref
			(Term.create_fun_term symbol [])
			term_db
	in
	
	(* Return creted term *)
	term

(* Create skolem term with parameter *)
let create_skolem_term (symbol_format : ('a -> 'b, 'c, 'd, 'e, 'e, 'b) format6) symbol_type (name_param: 'a) =
	
	(* Name of skolem symbol *)
	let skolem_symbol_name = Format.sprintf symbol_format name_param in
	
	(* Create term *)
	create_term skolem_symbol_name symbol_type

(* Create atom with arguments *)
let create_atom symbol_name arg_types args =
	
	(* Create stype of symbol *)
	let symbol_stype =
		Symbol.create_stype arg_types Symbol.symb_bool_type
	in
	
	(* Add or retrieve symbol from symbol database *)
	let symbol =
		SymbolDB.add_ref
			(Symbol.create_from_str_type symbol_name symbol_stype)
			symbol_db
	in
	
	(* Create atom and add to term database *)
	let atom =
		TermDB.add_ref
			(Term.create_fun_term symbol args)
			term_db
	in
	
	(* Return created atom *)
	atom

let create_atom_symb symb args =
	let atom = TermDB.add_ref
			(Term.create_fun_term symb args)
			term_db
	in
	atom

(* Create complementary literal *)
let create_compl_lit term =
	
	(* Add or retrieve complement from term database *)
	TermDB.add_ref
		(Term.compl_lit term)
		term_db

(********** Creation of terms and atoms **********)

(* Create term for state, i.e. constB{n} *)
let create_state_term n =
	create_skolem_term state_symbol_format state_type n

(* Create atom for active bound, i.e. $$iProver_bound{bound} *)
let create_bound_atom n =
	create_skolem_term bound_symbol_format Symbol.symb_bool_type n

(* Create atoms $$iProver_bound{bound} up to [ubound], in [accum] *)
let rec create_bound_atom_list accum ubound = function
	
	(* Terminate on upper bound and return list in ascending order *)
	| bound when bound >= ubound -> List.rev accum
	
	(* Create atom for bound, add to list and recurse for next bound *)
	| bound ->
	
			create_bound_atom_list
				((create_bound_atom bound) :: accum)
				ubound
				(succ bound)

(* Create term for bitindex, i.e. bitindex{n} *)
let create_bitindex_term n =
	create_skolem_term bitindex_symbol_format bitindex_type n

(* Create atom for bitvector, i.e. b000(X0) *)
let create_bitvector_atom bitvector_symbol_name bitindex_term =
	create_atom
		bitvector_symbol_name
		[ bitindex_type ]
		[ bitindex_term ]

(* Create path atom for two states, i.e. nextState(constB{p}, constB{q}) *)
let create_path_atom state_p state_q =
	(*
	create_atom
	path_symbol_name
	[ state_type; state_type]
	[ state_p; state_q ]
	*)
	create_atom_symb Symbol.symb_ver_next_state [state_p; state_q]

(* Create reachable state atom for given state,
i.e. reachableState(state) *)
let create_reachable_state_atom state =
	(* create_atom
	reachable_state_symbol_name
	[ state_type ]
	[ state ]
	*)
	create_atom_symb Symbol.symb_ver_reachable_state [state]

(* Create addressDiff atom for given arguments *)
let create_address_diff_atom arg1 arg2 arg3 =
	create_atom
		address_diff_symbol_name
		[ address_type; address_type; bitindex_type ]
		[ arg1; arg2; arg3 ]

(* Create addressVal atom for given arguments *)
let create_address_val_atom arg1 arg2 =
	create_atom
		address_val_symbol_name
		[ address_type; bitindex_type ]
		[ arg1; arg2 ]

(* Create sort atom for address, i.e. address(state) *)
let create_address_atom address =
	create_atom
		address_symbol_name
		[ address_type ]
		[ address ]

(********** Path axioms **********)

(* Create path axiom $$nextState(b-1, b) *)
let create_path_axiom b =
	
	(* Create state term for state *)
	let state_term_b = create_state_term b in
	
	(* Create state term for preceding state *)
	let state_term_pred_b = create_state_term (pred b) in
	
	(* Create path axiom for states *)
	let path_atom_b =
		create_path_atom state_term_pred_b state_term_b
	in
	
	(* Create unit clause of atom *)
	let path_axiom_b =
		Clause.normalise
			term_db
			(Clause.create [ path_atom_b ])
	in
	(* Assign clause history as path axiom for bound *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_path_axiom b)
		path_axiom_b;
	
	(* Return path axiom for bound *)
	path_axiom_b

(* Create path axioms for all bounds down to [lbound] *)
let rec create_path_axioms accum lbound = function
	
	(* No more axioms if state is less than lower bound *)
	| b when b <= lbound -> accum
	
	| b ->
	(* Create path axiom for bound *)
			let path_axiom_b = create_path_axiom b in
			
			(* Add path axioms for lesser states *)
			create_path_axioms (path_axiom_b :: accum) lbound (pred b)

let pre_instantiate_next_state_clause state_p state_q clause =
	let lits = Clause.get_literals clause in
	let next_list, rest_lits =
		List.partition Term.is_next_state_lit lits in
	let next_cl_lit =
		match next_list
		with
			[lit] -> lit
		| _ -> failwith "bmc1Axioms: exactly one next atom is expected"
	in
	(* next_cl_lit = ~$$nextState(VarCurr,VarNext) *)
	let next_cl_atom = Term.get_atom next_cl_lit in
	
	(* Create state term for state *)
	let state_term_p = create_state_term state_p in
	
	(* Create state term for preceding state *)
	let state_term_q = create_state_term state_q in
	
	(* nex_gr_atom = $$nextState($$constBq,$$constBp) *)
	let next_gr_atom = create_path_atom state_term_p state_term_q in
	let next_gr_cl =
		Clause.normalise term_db
			(Clause.create [next_gr_atom ])
	in
	(* Assign clause history as path axiom for bound *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_path_axiom state_q)
		next_gr_cl;
	try
		let mgu = Unif.unify_bterms (1, next_gr_atom) (2, next_cl_atom) in
		let resolved =
			Clause.create
				(Clause.normalise_blitlist_list term_db mgu [(2, rest_lits)])
		in
		Clause.assign_tstp_source_resolution
			resolved [clause; next_gr_cl] [next_cl_lit; next_gr_atom];
		resolved
	with
		Unif.Unification_failed ->
			failwith "bmc1Axioms: next_state atoms should be unifyable"

(* pre_instantiate for all bounds down to [lbound] *)
let rec pre_instantiate_next_state_clause_lu accum clause lbound = function
	(* No more axioms if state is less than lower bound *)
	| b when b <= lbound -> accum
	| b ->
			let pre_inst_cl = pre_instantiate_next_state_clause (pred b) b clause in
			pre_instantiate_next_state_clause_lu (pre_inst_cl:: accum) clause lbound (pred b)

let pre_instantiate_all_next_state_clauses lbound ubound =
	List.fold_left
		(fun rest cl ->
					let pre_inst_cls =
						pre_instantiate_next_state_clause_lu [] cl lbound ubound in
					pre_inst_cls@rest
		)
		[] !next_state_clauses

(********** Reachable state axioms (for all states) **********)

(* Create reachable state axiom $$reachableState(b) *)
let create_reachable_state_axiom b =
	
	(* Create state term for state *)
	let state_term_b = create_state_term b in
	
	(* Create reachable state axiom for state *)
	let reachable_state_atom_b =
		create_reachable_state_atom state_term_b
	in
	
	(* Create unit clause of atom *)
	let reachable_state_axiom_b =
		Clause.normalise
			term_db
			(Clause.create [ reachable_state_atom_b ])
	in
	
	(* Assign clause history as reachable state axiom for bound *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_reachable_state_axiom b)
		reachable_state_axiom_b;
	
	(* Return reachable state axiom for bound *)
	reachable_state_axiom_b

(* Create reachable state axioms for all bounds down to [lbound] *)
let rec create_reachable_state_axioms accum lbound = function
	
	(* No more axioms if state is less than lower bound *)
	| b when b < lbound -> accum
	
	| b ->
	
	(* Create reachable state axiom $$reachableState(b) *)
			let reachable_state_axiom_b = create_reachable_state_axiom b in
			
			(* Add reachable state axioms for lesser states *)
			create_reachable_state_axioms
				(reachable_state_axiom_b :: accum) lbound (pred b)

(* Create reachable state literals for all states down to zero *)
let rec create_reachable_state_literals accum = function
	
	| b when b = -1 -> accum
	
	| b ->
	
	(* Create state term for state *)
			let state_term_b = create_state_term b in
			
			(* Create equation X0 = constB{b} *)
			let reachable_state_literal_b =
				create_typed_equation
					state_type
					state_term_b
					(term_x0 state_type)
			in
			
			(* Add literals for lesser states *)
			create_reachable_state_literals
				(reachable_state_literal_b :: accum)
				(pred b)

(* Create reachable state axiom for bound *)
let create_reachable_state_conj_axiom bound =
	
	(* Create head literal in clause, i.e. ~reachableState(X0) *)
	let reachable_state_literal =
		create_compl_lit
			(create_reachable_state_atom (term_x0 state_type))
	in
	
	(* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
	let bound_literal = create_compl_lit (create_bound_atom bound) in
	
	(* Create head of clause,
	i.e. {~$$iProver_bound { b }; ~reachableState(X0)] *)
	let reachable_state_axiom_head =
		[ bound_literal; reachable_state_literal ]
	in
	
	(* Create and add literals for all states less than bound *)
	let reachable_state_literals =
		create_reachable_state_literals reachable_state_axiom_head bound
	in
	
	(* Create axiom *)
	let reachable_state_conj_axiom =
		Clause.normalise term_db (Clause.create reachable_state_literals);
	in
	
	(* Assign clause history as axiom *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_reachable_state_conj_axiom bound)
		reachable_state_conj_axiom;
	
	(* Return created clause *)
	reachable_state_conj_axiom

(***** Reachable state axioms (last state only) **********)

(* Create reachable state axiom ~$$iProver_bound{b} | $$reachableState(b) *)
let create_reachable_state_on_bound_axiom b =
	
	(* Create state term for state *)
	let state_term_b = create_state_term b in
	
	(* Create reachable state axiom for state *)
	let reachable_state_atom_b =
		create_reachable_state_atom state_term_b
	in
	
	(* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
	let bound_literal = create_compl_lit (create_bound_atom b) in
	
	(* Create unit clause of atom *)
	let reachable_state_axiom_b =
		Clause.normalise
			term_db
			(Clause.create [ bound_literal; reachable_state_atom_b ])
	in
	
	(* Assign clause history as axiom *)
	(* Clause.assign_axiom_history Clause.BMC1_Axiom reachable_state_axiom_b; *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)
		reachable_state_axiom_b;
	
	(* Return reachable state axiom for bound *)
	reachable_state_axiom_b

(* Create reachable state axioms for all bounds down to [lbound] *)
let rec create_reachable_state_on_bound_axioms accum lbound = function
	
	(* No more axioms if state is less than lower bound *)
	| b when b < lbound -> accum
	
	| b ->
	
	(* Create reachable state axiom ~$$iProver_bound{b} | $$reachableState(b) *)
			let reachable_state_axiom_b = create_reachable_state_on_bound_axiom b in
			
			(* Add reachable state axioms for lesser states *)
			create_reachable_state_on_bound_axioms
				(reachable_state_axiom_b :: accum)
				lbound
				(pred b)

(* Create clause
~$$iProver_bound { b } | ~$$reachableState(X0) | X0 = constB { b } *)
let create_only_bound_reachable_axiom b =
	
	(* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
	let bound_literal = create_compl_lit (create_bound_atom b) in
	
	(* Create literal ~$$reachableState(X0) *)
	let reachable_state_x0_literal =
		create_compl_lit (create_reachable_state_atom (term_x0 state_type))
	in
	
	(* Create state term for state *)
	let state_term_b = create_state_term b in
	
	(* Create equation X0 = constB{b} *)
	let reachable_state_literal_b =
		create_typed_equation
			state_type
			state_term_b
			(term_x0 state_type)
	in
	
	(* Create clause
	~$$iProver_bound { b } | ~$$reachableState(X0) | X0 = constB { b } *)
	let reachable_state_axiom_b =
		Clause.normalise
			term_db
			(Clause.create
					[ bound_literal;
					reachable_state_x0_literal;
					reachable_state_literal_b ])
	in
	
	(* Assign clause history as axiom *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_only_bound_reachable_state_axiom b)
		reachable_state_axiom_b;
	
	(* Return created clause *)
	reachable_state_axiom_b

(* Create reachable state literals for all states down to zero *)
let rec create_only_bound_reachable_axioms accum lbound = function
	
	(* No more axioms if state is less than lower bound *)
	| b when b < lbound -> accum
	
	| b ->
	
	(* Create clause
	~$$iProver_bound { b } | ~$$reachableState(X0) | X0 = constB { b } *)
			let reachable_state_axiom_b = create_only_bound_reachable_axiom b in
			
			(* Add clauses for lesser states *)
			create_only_bound_reachable_axioms
				(reachable_state_axiom_b :: accum)
				lbound
				(pred b)

(*------- reachable state pre-instantiation vesion -----------*)

(* separte clauses containing $$reachableState *)
(* we assume that all such occurrrences are of the form $$reachableState(sK) *)
(* then sparate clauses containing sK constants; these will be replaced by bounds at each iteration *)

exception Reach_Not_Supported

(* also removes $$reachableState *)

let separate_reach_constants clauses =
	let has_reachable_state clause =
		(List.exists Term.is_reachable_state_lit (Clause.get_literals clause)) in
	
	let (reach_clauses, no_reach_cl) = List.partition has_reachable_state clauses in
	try
		let extract_reach_sk cl =
			(match (Clause.get_skolem_bound_clause cl)
				with
				| Some sK -> sK
				| None -> raise Reach_Not_Supported
			)
		in
		let reach_sk_constants = List.map extract_reach_sk reach_clauses in
		reach_bound_skolem_constants := reach_sk_constants;
		(reach_clauses, no_reach_cl)
	with
		Reach_Not_Supported ->
			failwith
				"bmc1Axioms: reachable clauses are supported only of
the form $$reachableState(sK)"

(*-------------------------*)
let rec pre_inst_reachable_state_axioms accum lbound = function
	| b when b < lbound -> accum
	| b ->
	
	(* Create state term for state constB{b} *)
			let state_term_b = create_state_term b in
			
			(* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
			let bound_literal = create_compl_lit (create_bound_atom b) in
			
			(* Create equation sK = constB{b} *)
			let reachable_state_literal_b sK =
				create_typed_equation
					state_type
					sK
					state_term_b
			
			in
			(* Create clause [sK = constB{b}] *)
			let reachable_state_axiom_b sK =
				let reach_ax =
					Clause.normalise
						term_db
						(Clause.create
								[bound_literal; (reachable_state_literal_b sK)])
				in
				(* Assign clause history as axiom *)
				Clause.assign_tstp_source_axiom_bmc1
					(Clause.TSTP_bmc1_only_bound_reachable_state_axiom b)
					reach_ax;
				reach_ax
			in
			let reach_axioms =
				List.fold_left
					(
						fun rest sK ->
								(reachable_state_axiom_b sK):: rest
					)
					[] !reach_bound_skolem_constants
			in
			pre_inst_reachable_state_axioms
				(reach_axioms@accum) lbound (pred b)

(*------this extra is not used yet---------------------*)

let separate_reachable_state_clauses clauses =
	(* Clause.has_next_state is not assigned at this point so need to explicitely search for next state *)
	
	let (_reach_clauses, no_reach_cl) = separate_reach_constants clauses in
	
	(* assume the size of reach_bound_skolem_constants is small, usually 1 *)
	let has_bound_sk_constant_lit lit =
		(List.exists
				(fun sk -> Term.is_subterm sk lit) !reach_bound_skolem_constants)
	in
	let has_bound_sk_constant_cl cl =
		Clause.exists has_bound_sk_constant_lit cl
	in
	let (has_bound_sk_constant, no_bound_sk_no_reach) =
		List.partition has_bound_sk_constant_cl no_reach_cl
	in
	has_reach_bound_skolem_constants:= has_bound_sk_constant;
	(* debug *)
	(*
	out_str "\n\n----- separated has_bound_sk_constant ---------------\n";
	out_str ((Clause.clause_list_to_tptp has_bound_sk_constant)^"\n\n");
	out_str "\n--------------------\n";
	*)
	(* debug *)
	no_reach_cl

let rec pre_inst_reachable_state_clauses accum lbound = function
	| b when b < lbound -> accum
	| b ->
	(* $$constBb *)
			let state_term_b = create_state_term b in
			
			(* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
			let bound_literal = create_compl_lit (create_bound_atom b)
			in
			let pre_inst_reachable_cl cl sk_term =
				let repl_cl =
					Clause.replace_subterm term_db ~subterm: sk_term ~byterm: state_term_b cl
				in
				let pre_inst_cl =
					Clause.normalise
						term_db
						(Clause.create (bound_literal:: (Clause.get_literals repl_cl)))
				in
				Clause.assign_tstp_source_axiom_bmc1
					(Clause.TSTP_bmc1_only_bound_reachable_state_axiom b)
					pre_inst_cl;
				pre_inst_cl
			in
			let pre_inst_all_sk_consts_cl cl =
				List.fold_left
					(fun rest sk ->
								(
									(pre_inst_reachable_cl cl sk):: rest
								)
					)
					[] !reach_bound_skolem_constants
			in
			let pre_instantiated_all_cl =
				List.fold_left
					(fun rest cl ->
								(
									(pre_inst_all_sk_consts_cl cl)@rest
								)
					)
					[] !has_reach_bound_skolem_constants
			in
			pre_inst_reachable_state_clauses (pre_instantiated_all_cl@accum) lbound (pred b)

(********** Clock pattern **********)

(* Get sign of clock in given state *)
let sign_of_clock_pattern state pattern =
	(List.nth pattern (state mod List.length pattern)) = 1

(* Create axiom for given clock in given state *)
let create_clock_axiom state clock pattern =
	
	(* Create term for state *)
	let state_term = create_state_term state in
	
	(* Create atom for clock *)
	let clock_atom =
		TermDB.add_ref
			(Term.create_fun_term clock [ state_term ])
			term_db
	in
	
	(* Create literal for clock *)
	let clock_literal =
		
		(* Sign of clock in state *)
		if sign_of_clock_pattern state pattern then
			
			(* Clock literal is positive *)
			clock_atom
		
		else
			
			(* Clock literal is negative *)
			create_compl_lit clock_atom
	
	in
	
	(* Create clock axiom *)
	let clock_axiom =
		Clause.normalise term_db (Clause.create [ clock_literal ])
	in
	
	(* Return clock axiom *)
	clock_axiom

(* Create axiom for given clock in given state *)
let create_clock_axioms state clock pattern accum =
	
	(* Create clock axiom *)
	let clock_axiom = create_clock_axiom state clock pattern in
	
	(* Assign clause history as axiom *)
	(* Clause.assign_axiom_history Clause.BMC1_Axiom clock_axiom; *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_clock_axiom (state, clock, pattern))
		clock_axiom;
	
	(* Return clock axiom in accumulator *)
	clock_axiom :: accum

(* Create clock axioms for all clocks in state *)
let create_all_clock_axioms state =
	
	(* Iterate clocks *)
	Symbol.Map.fold
		(create_clock_axioms state)
		!Parser_types.clock_map
		[ ]

(* Create clock axioms for all clock and all states up to bound *)
let rec create_all_clock_axioms_for_states accum bound_i ubound =
	
	(* Reached upper bound? *)
	if bound_i > ubound then
		
		(* Return clock axioms *)
		accum
	
	else
		
		(* Add clock axioms for next states *)
		create_all_clock_axioms_for_states
			((create_all_clock_axioms bound_i) @ accum)
			(succ bound_i)
			ubound

(********** Address axioms (TODO) **********)

(* This is untested and unfinished. Currently, address axioms are
extracted from the problem and instantiated, see below *)

(*

(* Create address domain axioms

~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2 |
address_val(A1, B) | address_val(A2, B)

~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2 |
~address_val(A1, B) | ~address_val(A2, B)

*)
let create_address_domain_axiom () =

(* Common literals of both axioms:

~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2
*)
let axiom_head =
[ create_compl_lit (create_address_atom term_x0);
create_compl_lit (create_address_atom term_x1);
create_compl_lit (create_address_diff_atom term_x0 term_x1 term_x2);
create_typed_equation address_type term_x0 term_x1 ]
in

(* Atom address_val(A1,B) *)
let address_val_1_atom =
create_address_val_atom term_x0 term_x2
in

(* Atom address_val(A2,B) *)
let address_val_2_atom =
create_address_val_atom term_x1 term_x2
in

(* First axiom:

address_val(A1, B) | address_val(A1, B) | { axiom_head }
*)
let address_domain_axiom_1 =
address_val_1_atom ::
address_val_2_atom ::
axiom_head
in

(* Second axiom:

~address_val(A1, B) | ~address_val(A1, B) | { axiom_head }
*)
let address_domain_axiom_2 =
(create_compl_lit address_val_1_atom) ::
(create_compl_lit address_val_2_atom) ::
axiom_head
in

(* Return the two address_domain axioms *)
[ address_domain_axiom_1; address_domain_axiom_2 ]

(* Accumulate atoms addressDiff(A1,A2,bitindex{n}) from n to 0 *)
let rec create_address_diff_disjunction accum = function

(* Terminate after all atoms have been generated *)
| i when i < 0 -> accum

(* Create axiom for current i *)
| i ->

(* Create atom addressDiff(X0,X1,bitindex{i}) *)
let address_diff_disjunct =
create_address_diff_atom term_x0 term_x1 (create_bitindex_term i)
in

(* Recursively create remaining atoms *)
create_address_diff_disjunction
(address_diff_disjunct :: accum)
(pred i)

(* Create address_diff axiom with the maximal bit width of all
addresses:

cnf(address_diff, axiom, addressDiff(A1, A2, bitindex0) | ... |
addressDiff(A1, A2, bitindex { N -1 })).

*)
let create_address_domain_axiom address_max_width =

(* Create literals for axiom *)
let address_domain_axiom_literals =
create_address_diff_disjunction [ ] address_max_width
in

(* Create axiom *)
let address_domain_axiom =
Clause.normalise term_db (Clause.create address_domain_axiom_literals)
in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom address_domain_axiom; *)
Clause.assign_tstp_source_axiom_bmc1 address_domain_axiom;

(* Return axiom *)
address_domain_axiom

(* Return address definition for given constant bit vector b000 as

b000(X0) <=> addressVal(b000_address_term, X0)

clausified to

b000(X0) | ~addressVal(b000_address_term, X0)
~b000(X0) | addressVal(b000_address_term, X0)

and sort axiom

address(b000_address_term)

TODO: optimise clausification, might be sufficient to generate
first clause only in some cases

*)
let create_constant_address_definition accum bitvector_symbol =

(* Get name of bit vector symbol *)
let bitvector_name = Symbol.get_name bitvector_symbol in

(* Create address term for constant bit vector: b000_address_term *)
let address_term =
create_skolem_term constant_address_term_format address_type bitvector_name
in

(* Create atom for address: addressVal(b000_address_term, X0) *)
let address_val_atom =
create_address_val_atom address_term term_x0
in

(* Create atom for bitvector with variable: b000(X0) *)
let bitvector_atom =
create_bitvector_atom bitvector_name term_x0
in

(* Create atom for address term: address(b000_address_term) *)
let address_atom =
create_address_atom address_term
in

(* Create first axiom *)
let constant_address_definition_1 =
Clause.normalise
term_db
(Clause.create
[ create_compl_lit bitvector_atom; address_val_atom ])
in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_1; *)
Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_1;

(* Create second axiom *)
let constant_address_definition_2 =
Clause.normalise
term_db
(Clause.create
[ bitvector_atom; create_compl_lit address_val_atom ])
in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_2; *)
Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_2;

(* Create third axiom *)
let constant_address_definition_3 =
Clause.normalise
term_db
(Clause.create [ address_atom ])
in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_3; *)
Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_3;

(* Return clauses in accumulator *)
constant_address_definition_1 ::
constant_address_definition_2 ::
constant_address_definition_3 ::
accum
*)

(********** Instantiate clauses for bound **********)

(* Is the term or one if its subterms to be instantiated for each bound? *)
let rec is_bound_term = function
	
	(* No instantiation for variables *)
	| Term.Var _ -> false
	
	(* Symbol is a state constant *)
	| Term.Fun (symb, args, _)
	when Symbol.Map.mem symb !Parser_types.state_constant_map ->
	
	(* Only instantiate the state constant for bound 1 *)
			Symbol.Map.find symb !Parser_types.state_constant_map = 1
	
	(* Symbol has a base name *)
	| Term.Fun (symb, args, _)
	when Symbol.Map.mem symb !Parser_types.address_base_name_map ->
	
	(* Get base name of symbol *)
			let base_name =
				Symbol.Map.find symb !Parser_types.address_base_name_map
			in
			
			(
				
				try
				
				(* Only instantiate if base name of symbol has a "1"
				appended? *)
					String.sub
						(Symbol.get_name symb)
						(String.length base_name)
						((String.length (Symbol.get_name symb)) -
							(String.length base_name))
					= "1"
				
				with Invalid_argument _ ->
				
						failwith
							(Format.sprintf
									("Bmc1Axioms.is_bound_term: name of symbol %s " ^^
										"and base name %s do not match")
									(Symbol.get_name symb)
									base_name)
				
			)
	
	(* Check if term has a subterm to be instantiated *)
	| Term.Fun (_, args, _) ->
	
	(* Is one of the subterms a term to be instantiated? *)
			List.exists (fun b -> b) (Term.arg_map_list is_bound_term args)

(* Is the clause to be instantiated at each bound? *)
let is_bound_clause clause =
	List.exists
		(fun b -> b)
		(List.map is_bound_term (Clause.get_literals clause))

(* Instantiate term for current bound *)
let rec bound_instantiate_term bound = function
	
	(* No instantiation for variables *)
	| Term.Var _ as t -> t
	
	(* Symbol is a state constant *)
	| Term.Fun (symb, args, _) as t
	when Symbol.Map.mem symb !Parser_types.state_constant_map ->
	
			if
			
			(* Only replace state constant for bound 1 *)
			Symbol.Map.find symb !Parser_types.state_constant_map = 1
			
			then
				
				(* Replace term with state term for current bound *)
				create_state_term bound
			
			else
				
				(* Keep state constant for bounds other than 1*)
				t
	
	(* Symbol has a base name *)
	| Term.Fun (symb, args, _) as t
	when Symbol.Map.mem symb !Parser_types.address_base_name_map ->
	
	(* Get base name of symbol *)
			let base_name =
				Symbol.Map.find symb !Parser_types.address_base_name_map
			in
			
			if
			
			(
				try
				
				(* Base name of symbol has "1" appended? *)
					String.sub
						(Symbol.get_name symb)
						(String.length base_name)
						((String.length (Symbol.get_name symb)) -
							(String.length base_name))
					= "1"
				
				with Invalid_argument _ ->
				
						failwith
							(Format.sprintf
									("Bmc1Axioms.bound_instantiate_term: name of symbol %s " ^^
										"and base name %s do not match")
									(Symbol.get_name symb)
									base_name)
				
			)
			
			then
				
				(* Append bound to base name *)
				let term_bound_name = base_name ^ (string_of_int bound) in
				
				(* Replace term with term for current bound *)
				create_term term_bound_name address_type
			
			else
				
				(* Keep term for bounds other than 1 *)
				t
	
	(* Instantiate withing functional term *)
	| Term.Fun (symb, args, _) ->
	
	(* Instantiate arguments of term *)
			let args' =
				Term.arg_map_list (bound_instantiate_term bound) args
			in
			
			(* Return term with instantiated arguments *)
			TermDB.add_ref
				(Term.create_fun_term
						symb
						args')
				term_db

(* Instantiate clause for current bound *)
let bound_instantiate_clause bound clause =
	
	(* Get literals of clause *)
	let clause_literals =
		Clause.get_literals clause
	in
	
	(* Instantiate terms in literals for current bound *)
	let clause_literals' =
		List.map (bound_instantiate_term bound) clause_literals
	in
	
	(* Create new clause of instantiated literals *)
	let instantiated_clause =
		Clause.normalise
			term_db
			(Clause.create clause_literals')
	in
	
	(* Assign clause history as axiom *)
	(* Clause.assign_axiom_history Clause.BMC1_Axiom instantiated_clause; *)
	Clause.assign_tstp_source_axiom_bmc1
		(Clause.TSTP_bmc1_instantiated_clause (bound, clause))
		instantiated_clause;
	
	(* Return instantiated clause *)
	instantiated_clause

(* Instantiate clauses for current bound *)
let instantiate_bound_axioms bound clauses =
	
	(* Instantiate each clause *)
	List.map
		(bound_instantiate_clause bound)
		clauses

(* Return two list of clauses, the first containing the clauses to be
instantiated at each bound, the second the clauses valid for each
bound *)
let separate_bound_axioms clauses =
	List.partition is_bound_clause clauses

(* separte clauses containing $$nextState, used in preinstantiation strategy *)
(* first are the nextState clauses *)
let separate_next_state_clauses clauses =
	(* Clause.has_next_state is not assigned at this point so need to explicitely search for next state *)
	
	let has_next_state clause =
		(List.exists Term.is_next_state_lit (Clause.get_literals clause)) in
	List.partition has_next_state clauses

(********** Utility functions **********)

(* Formatter for output, None if uninitialised. Use
get_bmc1_dump_formatter as access function *)
let bmc1_dump_formatter = ref None

(* Return a formatter for writing into the file given in the option
-- bmc1_dump_file *)
let get_bmc1_dump_formatter () =
	
	match !bmc1_dump_formatter with
	
	(* Return formatter if initialised *)
	| Some f -> f
	
	(* Formatter is not initialised *)
	| None ->
	
	(* Filename from options *)
			let dump_filename =
				
				(* Get value of option *)
				match val_of_override !current_options.bmc1_dump_file with
				
				(* Default is stdout *)
				| None -> "-"
				
				(* Use filename if non-default *)
				| Some f -> f
			
			in
			
			(* Formatter of channel of opened file *)
			let new_bmc1_dump_formatter =
				
				try
				
				(* Open formatter writing into file *)
					formatter_of_filename false dump_filename
				
				with
				
				(* Catch errors when opening *)
				| Sys_error _ ->
						failwith
							(Format.sprintf
									"Could not open file %s for output"
									dump_filename)
			
			in
			
			(* Save formatter *)
			bmc1_dump_formatter := Some new_bmc1_dump_formatter;
			
			(* Return formatter *)
			new_bmc1_dump_formatter

(********** Top functions **********)

(* Return clauses with assumptions for given bound *)
let get_bound_assumptions bound =
	
	(* Get atom iProver_bound{n} *)
	let bound_literal = create_bound_atom bound in
	
	(* Return unit clause containing positive bound atom *)
	[ Clause.normalise term_db (Clause.create [ bound_literal ]) ]

(* reachable state pre-instantiation *)

(* First version (currently implemented) *)
(* replace *)
(*  $$reachableState(sK)                                             *)
(* ~$$reachableState(X) -> X = $$constB0 \/..\/X = $$constBn         *)
(* by  replace sK = $$constB0 \/..\/ sK = $$constBn                  *)

(*Second version (not fully implemented)*)

(* 1) find clauses of the type [$$reachbleState(sK)], *)
(*    and collect all such sK constants (usually 1)  *)
(* 2) separate all clauses containing these sK constants *)
(* 3) with each bound replace sK in 2) with the bound term and add to the clauses set *)
(* !!! reachable state pre - instantiation
Does not work at the moment because transitional addresses can occur in
2) then they are not unrolled since the clauses are separated *)

(*let _= out_str "\n!!! Warning: pre_instantiate_next_state_flag add to options!!!\n"*)

(*-----------------------------------------*)
(* Axioms for bound 0 *)
(*-----------------------------------------*)
let init_bound all_clauses =
	
	(* Separate axioms to be instantiated for each bound *)
	let bound_instantiate_axioms_of_clauses, clauses' =
		separate_bound_axioms all_clauses
	in
	let clauses'' =
		if !current_options.bmc1_pre_inst_next_state
		then
			(let cl_next_state, cl_rest = separate_next_state_clauses clauses' in
				next_state_clauses:= cl_next_state;
				cl_rest
			)
		else
			clauses'
	in
	let clauses =
		if !current_options.bmc1_pre_inst_reach_state
		then
			let (reach, no_reach) = separate_reach_constants clauses''
			in
			(*
			out_str "\n\n----- Reach clauses  ---------------\n";
			out_str ((Clause.clause_list_to_tptp reach)^"\n\n");
			out_str "\n--------------------\n";
			*)
			no_reach
		(*      separate_reachable_state_clauses clauses'' *)
		else
			clauses''
	in
	(* Create reachable states axiom for next bound *)
	let reachable_state_axioms =
		if !current_options.bmc1_pre_inst_reach_state  (* add this as a case in match below*)
		then
			begin
				let reach_axs = pre_inst_reachable_state_axioms [] 0 0 in
				(*	pre_inst_reachable_state_clauses [] 0 0 *)
				(*
				out_str "\n\n-----  pre_inst_reachable_state_axioms ---------------\n";
				out_str ((Clause.clause_list_to_tptp reach_axs)^"\n\n");
				out_str "\n--------------------\n";
				*)
				reach_axs
			end
		
		else
			begin
				match val_of_override !current_options.bmc1_axioms with
				
				(* All states are reachable *)
				| BMC1_Axioms_Reachable_All ->
				
				(* Axiom for conjunction of reachable states *)
						(create_reachable_state_conj_axiom 0) ::
						
						(* Axioms for individual reachable states *)
						(create_reachable_state_axioms
								[ ]
								0
								0)
				
				(* Only last state is reachable *)
				| BMC1_Axioms_Reachable_Last ->
				
				(* Only final state is reachable in each bound *)
						(create_reachable_state_on_bound_axioms [] 0 0) @
						
						(* Final state is reachable in next bound *)
						(create_only_bound_reachable_axioms [] 0 0)
			end
	in
	
	(* Create clock axiom *)
	let clock_axioms =
		create_all_clock_axioms_for_states
			[ ]
			0
			0
	in
	
	(* Create literal for current bound, i.e. $$iProver_bound{b_cur} *)
	let bound_literal_0 = create_bound_atom 0 in
	
	(* Return created path axioms and reachable state axiom *)
	let bound_axioms =
		reachable_state_axioms @ clock_axioms
	in
	
	(* Save axioms to be instantiated *)
	bound_instantiate_axioms := bound_instantiate_axioms_of_clauses;
	
	(* Assume assumption literal for next_bound to be true in solver *)
	Prop_solver_exchange.assign_only_norm_solver_assumptions
		[ bound_literal_0 ];
	
	(* Output only in verbose mode *)
	if val_of_override !current_options.bmc1_verbose then
		
		(
			
			(* Output axioms to be instantiated for each bound *)
			Format.printf
				"BMC1 axioms to be instantiated at bounds@.";
			
			List.iter
				(fun c -> Format.printf "%s@\n@." (Clause.to_string c))
				!bound_instantiate_axioms;
			
			(* Output created axioms for bound *)
			Format.printf
				"BMC1 axioms for initial bound 0@.";
			
			List.iter
				(function c -> Format.printf "%s@." (Clause.to_string c))
				bound_axioms;
			
			Format.printf "@."
			
		);
	
	(* Return created axioms for bound *)
	bound_axioms, clauses

(*-------------------------------------------------*)
(* Increment bound from given bound *)
(*-------------------------------------------------*)
let increment_bound cur_bound next_bound simulate =
	
	(*currently only next_bound should be cur_bound + 1 *)
	assert (next_bound - cur_bound = 1);
	(* change grounding of state type to next_bound *)
	
	(*
	let next_bound_state_term = create_state_term next_bound in
	out_str ("state term: "^(Term.to_string next_bound_state_term)^("\n"));
	Prop_solver_exchange.assign_new_grounding Symbol.symb_ver_state_type next_bound_state_term;
	*)
	
	(* Create literals for current bound up to next bound,
	i.e. $$iProver_bound {b_cur },...,$$iProver_bound { b_next - 1 } *)
	let bound_literals_cur_to_next =
		List.map
			create_compl_lit
			(create_bound_atom_list [] next_bound cur_bound)
	in
	
	(* Create literal for next bound, i.e. $$iProver_bound{b_next} *)
	let bound_literal_next = create_bound_atom next_bound in
	
	(* Create path axioms for all states between next bound and current
	bound *)
	let path_axioms =
		if !current_options.bmc1_pre_inst_next_state
		then
			pre_instantiate_all_next_state_clauses cur_bound next_bound
		else
			create_path_axioms [] cur_bound next_bound
	in
	
	(* Create reachable states axiom for next bound *)
	let reachable_state_axioms =
		if !current_options.bmc1_pre_inst_reach_state  (* add this as a case in match below*)
		then
			begin
				let reach_axs = pre_inst_reachable_state_axioms [] (succ cur_bound) next_bound in
				(*
				out_str "\n\n-----  pre_inst_reachable_state_axioms ---------------\n";
				out_str ((Clause.clause_list_to_tptp reach_axs)^"\n\n");
				out_str "\n--------------------\n";
				*)
				reach_axs
				(*	pre_inst_reachable_state_clauses []  (succ cur_bound) next_bound*)
			end
		else
			begin
				match val_of_override !current_options.bmc1_axioms with
				
				(* All states are reachable *)
				| BMC1_Axioms_Reachable_All ->
				
				(* Axiom for conjunction of reachable states *)
						(create_reachable_state_conj_axiom next_bound) ::
						
						(* Axioms for individual reachable states *)
						(create_reachable_state_axioms
								[ ]
								(succ cur_bound)
								next_bound)
				
				(* Only last state is reachable *)
				| BMC1_Axioms_Reachable_Last ->
				
				(* Only final state is reachable in each bound *)
						(create_reachable_state_on_bound_axioms
								[]
								(succ cur_bound)
								next_bound) @
						
						(* Final state is reachable in next bound *)
						(create_only_bound_reachable_axioms
								[]
								(succ cur_bound)
								next_bound)
			end
	in
	
	(* Create clock axioms up to next bound *)
	let clock_axioms =
		create_all_clock_axioms_for_states
			[ ]
			(succ cur_bound)
			next_bound
	in
	
	(* Instantiate axioms for next bound
	
	TODO: iterate all bounds between cur_bound and next_bound if
	increases are in greater steps *)
	let bound_axioms_instantiated =
		instantiate_bound_axioms next_bound !bound_instantiate_axioms
	in
	
	(* Add complementary assumption for current bound *)
	invalid_bound_assumptions :=
	bound_literals_cur_to_next @ !invalid_bound_assumptions;
	
	(* Assume assumption literal for next_bound to be true in solver *)
	if not simulate then
		Prop_solver_exchange.assign_only_norm_solver_assumptions
			(bound_literal_next :: !invalid_bound_assumptions);
	
	(* Return created path axioms and reachable state axiom *)
	let bound_axioms =
		reachable_state_axioms @
		path_axioms @
		clock_axioms @
		bound_axioms_instantiated
	in
	
	(* Output only in verbose mode *)
	if val_of_override !current_options.bmc1_verbose then
		
		(
			
			(* Output created axioms for bound *)
			Format.printf
				"BMC1 axioms for bound %d after bound %d@."
				next_bound
				cur_bound;
			
			List.iter
				(function c -> Format.printf "%s@." (Clause.to_string c))
				bound_axioms;
			
			Format.printf "@."
			
		);
	
	(* Return created axioms for bound *)
	bound_axioms

(* Create axiom for given bound of axioms for previous bound *)
let rec extrapolate_to_bound' bound accum = function
	
	(* Return extrapolated clauses *)
	| [] -> accum
	
	(* Continue with tail of list of clauses *)
	| clause :: tl ->
	
	(* Add extrapolated axiom to accumulator *)
			let accum' =
				
				(* Get source of clause *)
				match Clause.get_tstp_source clause with
				
				(* Clause is a BMC1 path axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_path_axiom b)))
				when b = (pred bound) ->
				
				(* Add path axiom for current bound *)
						(create_path_axiom bound) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_reachable_state_axiom b)))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						(create_reachable_state_axiom bound) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_reachable_state_conj_axiom b)))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						(create_reachable_state_conj_axiom bound) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						(create_reachable_state_on_bound_axiom bound) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_only_bound_reachable_state_axiom b)))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						(create_only_bound_reachable_axiom bound) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_clock_axiom (b, clock, pattern))))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						( create_clock_axiom bound clock pattern) :: accum
				
				(* Clause is a BMC1 reachable state axiom for the previous bound *)
				| Clause.TSTP_external_source
				(Clause.TSTP_theory
				(Clause.TSTP_bmc1
				(Clause.TSTP_bmc1_instantiated_clause (b, clause))))
				when b = (pred bound) ->
				
				(* Add reachable state axiom for current bound *)
						(bound_instantiate_clause bound clause) :: accum
				
				(* Clause is not a BMC1 axiom *)
				| _ -> accum
			
			in
			
			(* Continue with tail of list of clauses *)
			extrapolate_to_bound' bound accum' tl

(* For all axioms that are dependent on the previous bound return a
list of clauses for the given bound. *)
let extrapolate_to_bound bound clauses =
	extrapolate_to_bound' bound [] clauses

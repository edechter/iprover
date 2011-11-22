(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2011 Konstantin Korovin and The University of Manchester. 
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
open Options
open Statistics


(* The symbol database *)
let symbol_db  = Parser_types.symbol_db_ref

(* The term database *)
let term_db = Parser_types.term_db_ref
  
  
(* Assumptions for previous bounds *)
let invalid_bound_assumptions = ref []


(* Clauses to be instantiated for each bound *)
let bound_instantiate_axioms = ref []
  

(********** Symbol names and name patterns **********)  

(* Type of addresses *)
let address_type = Symbol.symb_ver_address_type

(* Type of states *)
let state_type = Symbol.symb_ver_state_type
  
(* Type of bitindexes *)
let bitindex_type = Symbol.symb_ver_bit_index_type
  
(* Name of path symbol *)
let path_symbol_name = "$$nextState"

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


(* Get n-th variable recursively *)
let rec var_n' accum = function
    
  (* Terminate and return accumulated variable *)
  | 0 -> accum
    
  (* Fail for negaive variable numbers *)
  | i when i < 0 -> failwith ("Bmc1Axioms.var_n: variable number must be >= 0")
      
  (* Recurse to get next variable *)
  | i -> var_n' (Var.get_next_var accum) (pred i)


(* Get n-th variable *)
let var_n n = var_n' (Var.get_first_var ()) n


(* Get n-th variable term *)
let term_xn n = 
  TermDB.add_ref 
    (Term.create_var_term (var_n n))
    term_db 
    

(* Create term for variable X0 *)
let term_x0 = TermDB.add_ref (term_xn 0) term_db 


(* Create term for variable X0 *)
let term_x1 = TermDB.add_ref (term_xn 1) term_db 


(* Create term for variable X0 *)
let term_x2 = TermDB.add_ref (term_xn 2) term_db 


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
  create_atom 
    path_symbol_name    
    [ state_type; state_type]
    [ state_p; state_q ]
      

(* Create reachable state atom for given state,
   i.e. reachableState(state) *)
let create_reachable_state_atom state =
  create_atom 
    reachable_state_symbol_name 
    [ state_type ]
    [ state ]


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


(********** Creation of clauses **********)

(* Create path axioms for all bounds down to [lbound] *)
let rec create_path_axioms accum lbound = function 

  (* No more axioms if state is less than lower bound *)
  | b when b <= lbound -> accum 

  | b -> 

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
	
	(* Add path axioms for lesser states *)
	create_path_axioms (path_axiom_b :: accum) lbound (pred b)


(* Create path axioms for all bounds down to [lbound] *)
let rec create_reachable_state_axioms accum lbound = function 

  (* No more axioms if state is less than lower bound *)
  | b when b < lbound -> accum 

  | b -> 

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
	  term_x0
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
      (create_reachable_state_atom term_x0)
  in

  (* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
  let bound_literal = create_compl_lit (create_bound_atom bound) in
    
  (* Create head of clause, 
     i.e. {~$$iProver_bound{b}; ~reachableState(X0)] *)
  let reachable_state_axiom_head =
    [ bound_literal; reachable_state_literal ]
  in

  (* Create and add literals for all states less than bound *)
  let reachable_state_literals = 
    create_reachable_state_literals reachable_state_axiom_head bound 
  in

    (* Create axiom *)
    Clause.normalise term_db (Clause.create reachable_state_literals)


(* Get sign of clock in given state *)
let sign_of_clock_pattern state pattern = 
  (List.nth pattern (state mod List.length pattern)) = 1
      

(* Create axiom for given clock in given state *)
let create_clock_axiom state clock pattern accum =

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

    (* Return clock axiom in accumulator *)
    (Clause.normalise term_db (Clause.create [ clock_literal ])) :: accum



(* Create clock axioms for all clocks in state *)
let create_all_clock_axioms state =

  (* Iterate clocks *)
  Symbol.Map.fold 
    (create_clock_axiom state)
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


(* Create address domain axioms 
   
   ~address(A1) | ~address(A2) | ~addressDiff(A1,A2,B) | A1 = A2 | 
     address_val(A1,B) | address_val(A2,B)

   ~address(A1) | ~address(A2) | ~addressDiff(A1,A2,B) | A1 = A2 | 
     ~address_val(A1,B) | ~address_val(A2,B)

*)
let create_address_domain_axiom () =

  (* Common literals of both axioms: 

     ~address(A1) | ~address(A2) | ~addressDiff(A1,A2,B) | A1 = A2
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
     
     address_val(A1,B) | address_val(A1,B) | {axiom_head} 
  *)
  let address_domain_axiom_1 = 
    address_val_1_atom :: 
      address_val_2_atom :: 
      axiom_head
  in

  (* Second axiom:

     ~address_val(A1,B) | ~address_val(A1,B) | {axiom_head} 
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
   
   cnf(address_diff,axiom,addressDiff(A1,A2,bitindex0) | ... | 
                            addressDiff(A1,A2,bitindex{N-1})).

*)
let create_address_domain_axiom address_max_width = 

  (* Create literals for axiom *)
  let address_domain_axiom_literals =
    create_address_diff_disjunction [ ] address_max_width 
  in
    
    (* Create axiom *)
    Clause.normalise term_db (Clause.create address_domain_axiom_literals)
    



(* Return address definition for given constant bit vector b000 as 
   
   b000(X0) <=> addressVal(b000_address_term,X0) 
   
   clausified to 
   
   b000(X0) | ~addressVal(b000_address_term,X0) 
   ~b000(X0) | addressVal(b000_address_term,X0) 
   
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

    (* Return clauses in accumulator *)
    (Clause.normalise 
      term_db 
      (Clause.create 
	 [ create_compl_lit bitvector_atom; address_val_atom ])) ::
      (Clause.normalise 
	 term_db 
	 (Clause.create 
	    [ bitvector_atom; create_compl_lit address_val_atom ])) ::
      (Clause.normalise 
	 term_db 
	 (Clause.create [ address_atom ])) ::
      accum



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
    Clause.normalise
      term_db
      (Clause.create clause_literals')
      

(* Instantiate clauses for current bound *)
let instantiate_bound_axioms bound clauses = 

  (* Instantiate each clause *)
  List.map
    (bound_instantiate_clause bound)
    clauses


let separate_bound_axioms clauses =

  List.partition is_bound_clause clauses
    
    

(* Axioms for bound 0 *)
let init_bound all_clauses = 

  (* Separate axioms to be instantiated for each bound *)
  let bound_instantiate_axioms_of_clauses, clauses = 
    separate_bound_axioms all_clauses 
  in
    
  (* Create reachable states axiom *)
  let reachable_state_axioms = 
    create_reachable_state_axioms 
      [ ]       
      0
      0
  in
    
  (* Create reachable states axiom *)
  let reachable_state_conj_axiom = 
    create_reachable_state_conj_axiom 0
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
    reachable_state_conj_axiom :: 
      (reachable_state_axioms @ clock_axioms)
  in
    
    (* Save axioms to be instantiated *)
    bound_instantiate_axioms := bound_instantiate_axioms_of_clauses;
    
    (* Assume assumption literal for next_bound to be true in solver *)
    Prop_solver_exchange.assign_only_norm_solver_assumptions 
      [ bound_literal_0 ];
    
    (* Output only in verbose mode *)
    if !current_options.bmc1_verbose then
      
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
      
      
      
(* Increment bound from given bound *)
let increment_bound cur_bound next_bound =

  (* Create path axioms for all states between next bound and current
     bound *)
  let path_axioms =
    create_path_axioms [ ] cur_bound next_bound
  in

  (* Create reachable states axiom for next bound *)
  let reachable_state_axioms = 
    create_reachable_state_axioms 
      [ ]       
      (succ cur_bound)
      next_bound
  in

  (* Create reachable states axiom for next bound *)
  let reachable_state_conj_axiom = 
    create_reachable_state_conj_axiom next_bound
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

  (* Create literal for current bound, i.e. $$iProver_bound{b_cur} *)
  let bound_literal_cur = create_bound_atom cur_bound in

  (* Create literal for next bound, i.e. $$iProver_bound{b_next} *)
  let bound_literal_next = create_bound_atom next_bound in

    (* Add complementary assumption for current bound *)
    invalid_bound_assumptions := 
      (create_compl_lit bound_literal_cur) :: !invalid_bound_assumptions;
    
    (* Assume assumption literal for next_bound to be true in solver *)
    Prop_solver_exchange.assign_only_norm_solver_assumptions 
      (bound_literal_next :: !invalid_bound_assumptions);
    
    (* Return created path axioms and reachable state axiom *)
    let bound_axioms =
      reachable_state_conj_axiom :: 
	(reachable_state_axioms @ 
	   path_axioms @ 
	   clock_axioms @ 
	   bound_axioms_instantiated)
    in
      
      (* Output only in verbose mode *)
      if !current_options.bmc1_verbose then
	
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



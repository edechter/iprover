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
open Printf


(* The symbol database *)
let symbol_db  = Parser_types.symbol_db_ref

(* The term database *)
let term_db = Parser_types.term_db_ref

(* Assumptions for previous bounds *)
let invalid_bound_assumptions = ref []

(* Format of state symbol *)
let state_symbol_format = format_of_string "constB%d" 
  
(* Name of path symbol *)
let path_symbol_name = "nextState"

(* Name of reachable state symbol *)
let reachable_state_symbol_name = "reachableState"

(* Format of symbol for active bound *)
let bound_symbol_format = format_of_string "$$iProver_bound%d"


(* Create term for variable X0 *)
let term_x0 = 
  TermDB.add_ref 
    (Term.create_var_term (Var.get_first_var ()))
    term_db 


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
      

(* Create complementary literal *)
let create_compl_lit term = 
  
  (* Add or retrieve complement from term database *)
  TermDB.add_ref
    (Term.compl_lit term)
    term_db 

      
(* Create term for state, i.e. constB{n} *)
let create_state_term n = 
  
  (* Name of state symbol *)
  let state_symbol_name = Format.sprintf state_symbol_format n in

  (* Type of state symbol *)
  let state_symbol_stype = Symbol.create_stype [] Symbol.symb_ver_state_type in

  (* Add state symbol to symbol database *)
  let state_symbol = 
    SymbolDB.add_ref
      (Symbol.create_from_str_type state_symbol_name state_symbol_stype)
      symbol_db
  in
    
  (* Add state term to term database *)
  let state_term = 
    TermDB.add_ref 
      (Term.create_fun_term state_symbol []) 
      term_db
  in

    (* Return creted state term *)
    state_term


(* Create path atom for two states, i.e. nextState(constB{p}, constB{q}) *)
let create_path_atom state_p state_q =

  (* Type of path symbol *)
  let path_symbol_stype = 
    Symbol.create_stype 
      [Symbol.symb_ver_state_type; Symbol.symb_ver_state_type]
      Symbol.symb_bool_type
  in

  (* Add or retrieve symbol from symbol database *)
  let path_symbol =
    SymbolDB.add_ref
      (Symbol.create_from_str_type path_symbol_name path_symbol_stype)
      symbol_db
  in

  (* Create path atom and add to term database *)
  let path_atom = 
    TermDB.add_ref
      (Term.create_fun_term path_symbol [state_p; state_q])
      term_db
  in

    (* Return created path atom *)
    path_atom
      

(* Create reachable state atom for given state,
   i.e. reachableState(state) *)
let create_reachable_state_atom state =

  (* Type of reachable state symbol *)
  let reachable_state_symbol_stype = 
    Symbol.create_stype 
      [Symbol.symb_ver_state_type]
      Symbol.symb_bool_type
  in
    
  (* Add or retrieve symbol from symbol database *)
  let reachable_state_symbol =
    SymbolDB.add_ref
      (Symbol.create_from_str_type 
	 reachable_state_symbol_name 
	 reachable_state_symbol_stype)
      symbol_db
  in
    
    (* Add or retrieve atom from term database *)
    TermDB.add_ref
      (Term.create_fun_term 
	 reachable_state_symbol 
	 [state])
      term_db


(* Create atom for active bound, i.e. $$iProver_bound{bound} *)
let create_bound_atom bound = 

  (* Type of bound symbol *)
  let bound_symbol_stype = Symbol.create_stype [] Symbol.symb_bool_type in

  (* Add or retrieve symbol from symbol database *)
  let bound_symbol =
    SymbolDB.add_ref 
      (Symbol.create_from_str_type
	 (Format.sprintf bound_symbol_format bound)
	 bound_symbol_stype)
      symbol_db
  in
    
    (* Add or retrieve term from term database *)
    TermDB.add_ref 
      (Term.create_fun_term bound_symbol [])
      term_db
    
  
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
	  (Clause.create [path_atom_b])
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
	  (Clause.create [reachable_state_atom_b])
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
	  Symbol.symb_ver_state_type
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
      (Term.create_fun_term clock [state_term]) 
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
    (Clause.normalise term_db (Clause.create [clock_literal])) :: accum



(* Create clock axioms for all clocks in state *)
let create_all_clock_axioms state =

  (* Iterate clocks *)
  Symbol.Map.fold 
    (create_clock_axiom state)
    !Parser_types.clock_map 
    []

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


(* Axioms for bound 0 *)
let init_bound () = 

  (* Create reachable states axiom *)
  let reachable_state_axioms = 
    create_reachable_state_axioms 
      []       
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
      [] 
      0
      0
  in

  (* Create literal for current bound, i.e. $$iProver_bound{b_cur} *)
  let bound_literal_0 = create_bound_atom 0 in

    (* Assume assumption literal for next_bound to be true in solver *)
    Prop_solver_exchange.assign_only_norm_solver_assumptions 
      [bound_literal_0];
    
    (* Return created path axioms and reachable state axiom *)
    let bound_axioms =
      reachable_state_conj_axiom :: 
	(reachable_state_axioms @ clock_axioms)
    in
      
      (* Output created axioms for bound *)
      Format.printf 
	"BMC1 axioms for initial bound 0@.";
      
      List.iter
	(function c -> Format.printf "%s@." (Clause.to_string c))
	bound_axioms;

      Format.printf "@.";
      
      (* Return created axioms for bound *)
      bound_axioms

  

(* Increment bound from given bound *)
let increment_bound cur_bound next_bound =

  (* Create path axioms for all states between next bound and current
     bound *)
  let path_axioms =
    create_path_axioms [] cur_bound next_bound
  in

  (* Create reachable states axiom for next bound *)
  let reachable_state_axioms = 
    create_reachable_state_axioms 
      []       
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
      [] 
      (succ cur_bound)
      next_bound 
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
	(reachable_state_axioms @ path_axioms @ clock_axioms)
    in
      
      
      (* Output created axioms for bound *)
      Format.printf 
	"BMC1 axioms for bound %d after bound %d@." 
	next_bound 
	cur_bound;
      
      List.iter
	(function c -> Format.printf "%s@." (Clause.to_string c))
	bound_axioms;

      Format.printf "@.";
   
      (* Return created axioms for bound *)
      bound_axioms



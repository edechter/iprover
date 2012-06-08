(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2012 Konstantin Korovin and The University of Manchester. 
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

(* input clauses : unit propagate*)
exception Satisfiable 
exception Unsatisfiable 


module type PropStruct = 
  sig
    type var
    type lit 
    type clause = lit list 
    val is_var  : lit -> bool
    val get_var : lit -> var
    val compare_var : var -> var -> int
    val compare_lit : lit -> lit -> int
  (*  val get_num_lit : clause -> int
    val iter_clause : (lit -> unit) -> clause -> unit
    val find_lit    : (lit -> bool) -> clause -> lit
*)
  end

module type DPLL = 
  sig
(*    type var 
    type lit 
    type clause *)
    type state
    val create_state : unit -> state
    val run_dpll : state -> clause list -> state
  end

module Make(PropStruct:PropStruct) = 
  struct
    type var      =  PropStruct.var
    type lit      =  PropStruct.lit
    type clause   =  PropStruct.clause
	  
    type decision_status = Decision | Implied
    type polarity = Pos | Neg
    type clause_ext = 
	{
	 lit_list : var_ext list;
	 num_of_lit : int;
	 mutable num_of_true_lit  : int;
	 mutable num_of_false_lit : int
       }	 
    and lit_ext = { polarity : polarity; var : var_ext } 
    and var_ext = 
	{
	 var : var;
	 mutable assignment : bool param;
	 mutable is_flipped : bool;
(*	 mutable splitting_priority : int; currently not used*)
	 mutable var_decision_level : int;
	 mutable decision_status : decision_status param;
	 mutable pos_occur : clause_ext list;
	 mutable neg_occur : clause_ext list;
	 mutable implied_vars : var_ext list   
       }

    type state = 
	{
	 mutable var_list : var_ext list;
	 mutable clause_list : clause_ext list;
	 mutable decision_level : int ;          
	 mutable decision_var : var_ext;
	 mutable decision_stack : var_ext Stack.t ;
	 mutable conflict_clause : clause param;
       }

    let is_free var_ext =
      if var_ext.assignment = Undef 
      then true 
      else false 

    let is_sat clause_ext = 
      if clause_ext.num_of_true_lit > 0 
      then true 
      else false 

    let is_unit clause_ext = 
      if ((not (is_sat clause_ext)) && 
	(clause_ext.num_of_lit - clause_ext.num_of_false_lit = 1))
      then true 
      else false
     

    let num_of_unsat_with_var var = 
      let add_unsat rest clause =
	if (is_sat clause) then rest else rest + 1 in 
      match var.assignment with 
      |Undef -> 
	  (List.fold_left add_unsat 0 var.pos_occur) + 
	    (List.fold_left add_unsat 0 var.neg_occur)                 
      |Def(true)  -> (List.fold_left add_unsat 0 var.neg_occur)
      |Def(false) -> (List.fold_left add_unsat 0 var.pos_occur)


    let find_next_split state =    
	let cmp v1 v2 = 
	  compare (num_of_unsat_with_var v1) (num_of_unsat_with_var v2) in      
	let split_var = 
	  try (list_find_max_element_p is_free cmp state.var_list)
	  with 	Not_found -> Satifiable 
	in
	let add_unsat rest clause =
	  if (is_sat clause) then rest else rest + 1 in 
	let pos_unsat = List.fold_left add_unsat 0 var.pos_occur in 
	let neg_unsat = List.fold_left add_unsat 0 var.pos_occur in 
	if (pos_unsat = 0 && neg_unsat = 0 )
	then raise Satisfiable (* since we choose var with max unsat*) 
	else  
	  if pos_unsat > neg_unsat 
	  then (split_var,true)
	  else (split_var,false)

(* later change to backjumping*)

    let backtrack state clause = 
      if 
      raise Backtrack

    let rec deduce state decision_status assignment var = 
      var.var_decision_level <- state.decision_level;
      var.decision_status <- decision_status;
      var.assignment <- Def(assignment);
      let (sat_occur,unsat_occur) = 
	if assignment 
	then (var.pos_occur,var.neg_occur)
	else (var.neg_occur,var.pos_occur)
      in
      let incr_true_lit clause =
	clause.num_of_true_lit <- clause.num_of_true_lit + 1 in
      List.iter incr_true_lit  split_var.neg_occur;
      let incr_false_lit clause =
	clause.num_of_false_lit <- clause.num_of_false_lit + 1; 
	if (is_conflict clause)
	then 
	  (state.conflict_clause <- Def(clause);
	   raise Backtrack)
	else
	  (if (is_unit clause) 
	  then  unit_propagate state clause)	    
      in
      List.iter incr_false_lit var.pos_unsat
    and
        unit_propagate state clause =
      let is_free_lit lit = 
	is_free lit.var in
      let free_lit = List.find is_free_lit clause.lit_list in
      state.decision_var.implied_vars  <- 
	free_lit.var::state.decision_var.implied_vars;
      match free_lit.polarity with 
      |Pos -> deduce state Def(Implied) true  free_lit.var
      |Neg -> deduce state Def(Implied) false free_lit.var
	    


    let dpll_loop state =
      try 
	while true 
	do  
	  let (split_var,assignment) = find_next_split state in	  
	  state.decision_var <- Def(split_var);
	  while true  
	  do
	    try	    
	      deduce state Def(Decision) assignment split_var;	   
	      state.decision_level <- state.decision_level + 1;
	      Stack.push split_var state.decision_stack 
	    with Backtrack -> backtrack state (* state is changed on backtrack*)
	  done
	done
      with 
      |Satisfiable -> state
      |Unsatisfiable -> Unsatisfiable 
	    

(*
  let split_neg state = 
    try 
      let split_var =  find_next_split state in
	if (num_of_unsat_with_var split_var) > 0 
	then
	 (state.decision_level      <- state.decision_level + 1;
  	  split_var.assignment      <- Def(false);
	  split_var.var_decision_level  <- state.decision_level;
	  split_var.decision_status <- Def(Decision);
	  let incr_false_lit clause =
	    clause.num_of_false_lit <- clause.num_of_false_lit + 1; 
	    if (is_unit clause) 
	    then unit_propogate state split_var clause 		
	    else
	      if (is_conflict clause)
	      then 
		(backtrack state var clause; 
		 raise Backtrack)
	  in
	  List.iter incr_false_lit  split_var.pos_occur; 
	  let incr_true_lit clause =
	    clause.num_of_true_lit <- clause.num_of_true_lit + 1 in
	  List.iter incr_true_lit  split_var.neg_occur
	 )
    
	else
	  raise Satisfiable 
      with Not_found -> raise Satisfiable
  *) 
	  
  end
	  

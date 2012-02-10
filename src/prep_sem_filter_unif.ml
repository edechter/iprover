(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2011 The University of Manchester. 
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
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol  

let symbol_db_ref  = Parser_types.symbol_db_ref
let term_db_ref    = Parser_types.term_db_ref


(*-------------------------------*)
type filter_clause = 
    {orig_clause : clause;
(* order literals first in the order of preferred selection *)
(* e.g. negative/positive/ground first     *)

(* if filter_clause is in the watch index then first literal in lits_to_try*)
(* is the next after the watched literal  *)                 
     mutable lits_to_try : lit list; 
   }

module DTParam = 
  struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end 

module DiscrTreeM = DiscrTree.Make(DTParam)  

(* all clauses with the same literal put together, *)
(*   assoc list with == *)

(* we use non-perfect unification index without going into full unification *)
type watch_unif_index_elem = (filter_clause list)

(*
let (unif_index_ref : (unif_index_elem DiscrTreeM.index) ref ) 
    = ref (DiscrTreeM.create ())
 *)

type dummy = Dummy

type filter_state = 
    {
(* intially all clauses unprocessed *)
     mutable unprocessed_fclauses : filter_clause list;

(* clauses that are kept after the filter *)
     mutable filtered_in_clauses : clause list;
     
(*  atom_unif_index contains atoms for which interpretation can not be established *)
     mutable atom_unif_index  : (watch_unif_index_elem DiscrTreeM.index);

(* watch_unif_index: indexes lists of clauses  by watch literals that *)
(* prospectively can be defined true in any extension *)
(* of any model of filtered_in_clauses *)

     mutable watch_unif_index : (watch_unif_index_elem DiscrTreeM.index);
   }

let clause_to_fclause order_lit_fun clause = 
  {
   orig_clause = clause;
   lits_to_try = order_lit_fun (Clause.get_literals clause);
 }


let init_filter_state clause_list order_lit_fun = 
  {
   unprocessed_clauses = 
   List.map (clause_to_filter_clause order_lit_fun) clause_list;

   filtered_in_clauses    = [];

   atom_unif_index     = (DiscrTreeM.create ());
   watch_unif_index    = (DiscrTreeM.create ());
 }

(* lit is unifiable with the element in the index*)
let is_unif unif_index lit =
     (DiscrTreeM.unif_candidates unif_index lit) != []

(* find_watch_lit raise Not_found if no watch_symb found *)  

let rec find_watch_lit filter_state fclause =
  match fclause.lits_to_try with
  |[] -> raise Not_found
  |h::tl -> 
      fclause.lits_to_try <- tl;
      let atom = Term.get_atom h in       
      let compl_h = (Term.compl_lit h) in     
      if 
	(* check that the atom is not unif with  atom_unif_index *)
	(not (is_unif fclause.atom_unif_index atom))
	  &&
	(* check that the complement of the lit  is not unif with  watch_unif_index *)
        (not (is_unif fclause.watch_unif_index compl_h))
      then 
	h
      else
	(
	 find_watch_lit filter_state fclause
	)
	  	
let add_to_watch filter_state watch_lit fclause = 
  let ind_elem = DiscrTreeM.add_term_path watch_lit filter_sate.watch_unif_index in
  (match !ind_elem with 
  |Elem(old) -> 
      (
       ind_elem:= (fclause::old)
      )
  |Empty_Elem   -> 	       
      (
       ind_elem := Elem([fclause])
      )
  )     


let add_filter_in_clause filter_state fclause = 
  let lits = Clause.get_lits fclause.orig_clause in
  let compl_lits = List.map Term.get_compl lits in
  let atoms = List.map Term.get_atom lits in
  (* move fclauses from watched to unprocessed *)
  

  filter_state.filtered_in_clauses<-clause::filter_state.filtered_in_clauses

let rec filter_clauses filter_state = 
  match filter_state.unprocessed_clauses with 
  |[] ->  filter_state.filtered_in_clauses
  |fclause::tl ->
      (try 
	let watch_lit = find_watch_lit filter_state fclause in 
	(add_to_watch filter_state watch_lit fclause)
      with
	Not_found -> 
	  (
	   add_filter_in_clause filter_state fclause;
	  )
      );


(*--junk------------*)

let rec filter_clauses filter_state = 
  match filter_state.unprocessed_clauses with 
  |[] ->  filter_state.filtered_clauses
  |clause::tl ->
      (try 
	let watch_symb = find_watch_symb filter_state clause in 
	add_to_watch filter_state watch_symb clause;
      with
	Not_found -> 
	  (
	   add_preds_to_undef_list filter_state clause;
	   filter_state.filtered_clauses<-clause::filter_state.filtered_clauses;
	   )
      );
      filter_state.unprocessed_clauses <- tl;
      process_undef_preds filter_state
and
    process_undef_preds filter_state =
  match filter_state.undef_pred_queue with 
  |[] -> filter_clauses filter_state
  |symb::tl -> 
      (try
	let watch_clause_list_ref =
	  SymbHash.find filter_state.watch_symbol_table symb in
	filter_state.unprocessed_clauses <- 
	  (!watch_clause_list_ref)@filter_state.unprocessed_clauses;
	SymbHash.remove filter_state.watch_symbol_table symb		      
      with 
	Not_found -> ()
      );
      filter_state.undef_pred_queue <- tl;
      filter_state.undef_pred_set <-
	(SymbSet.add symb filter_state.undef_pred_set);
      process_undef_preds filter_state




(*-----junk *)

   let ind_elem = DiscrTreeM.add_term_path sel_lit unif_index_ref in
    (match !ind_elem with 
    |Elem(old) -> 
	(try
	  let old_clause_list =  List.assq sel_lit old in 
	  let old_with_removed = List.remove_assq sel_lit old in
	  ind_elem := 
	    Elem((sel_lit,(main_clause::old_clause_list))::old_with_removed)
	  with Not_found ->  ind_elem := Elem((sel_lit,[main_clause])::old)
	)	     
    |Empty_Elem   -> 	 
	ind_elem := Elem([(sel_lit,[main_clause])])
    );     



(* dummy *)
let sem_filter_unif clause_list = clause_list

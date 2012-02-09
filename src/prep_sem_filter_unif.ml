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
(* is the watched literal  *)                 
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
     mutable unprocessed_clauses : filter_clause list;

(* clauses that are kept after the filter *)
     mutable filtered_in_clauses : clause list;
     
(*  atom_unif_index contains atoms for which interpretation can not be established *)
     mutable atom_unif_index  : (dummy DiscrTreeM.index);

(* watch_unif_index: indexes lists of clauses  by watch literals that *)
(* prospectively can be defined true in any extension *)
(* of any model of filtered_in_clauses *)

     mutable watch_unif_index : (watch_unif_index_elem DiscrTreeM.index);
   }

let clause_to_filter_clause order_lit_fun clause = 
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

(* dummy *)
let sem_filter_unif clause_list = clause_list

(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
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


type stat_int_entry

type stat_float_entry

type stat_fun_type = unit -> int

type stat_fun_entry 


val assign_int_stat : int  -> stat_int_entry -> unit
val incr_int_stat   : int  -> stat_int_entry ->  unit

val assign_float_stat : float -> stat_float_entry -> unit
val add_float_stat   : float -> stat_float_entry -> unit

val assign_fun_stat : stat_fun_type -> stat_fun_entry -> unit 

val get_val_stat       : stat_int_entry -> int
val get_float_val_stat : stat_float_entry -> float
val get_val_stat_fun   : stat_fun_entry -> int

(* runs function and add running time to stat*)
val run_and_time  :  stat_float_entry -> ('a-> 'b) -> 'a -> 'b

(*--General---*)
val num_of_splits        : stat_int_entry
val num_of_split_atoms   : stat_int_entry 
val forced_gc_time       : stat_int_entry 
val parsing_time         : stat_float_entry 
val num_of_terms         : stat_fun_entry 
val num_of_symbols       : stat_fun_entry 
val num_of_input_clauses : stat_int_entry 
val num_of_input_neg_conjectures : stat_int_entry 


(*----Propositional Solver-----*)
val prop_solver_calls              : stat_fun_entry 
val prop_solver_time               : stat_float_entry 
val prop_fast_solver_calls         : stat_fun_entry 
val prop_fast_solver_time          : stat_float_entry 
val prop_num_of_clauses            : stat_int_entry 
val prop_preprocess_simplified     : stat_int_entry 
val prop_fo_subsumed               : stat_int_entry 

(*----Instantiation------------*)
val inst_num_of_clauses            : stat_fun_entry 
val inst_num_in_passive            : stat_fun_entry 
val inst_num_of_loops              : stat_int_entry 
val inst_num_in_active             : stat_int_entry 
val inst_num_in_unprocessed        : stat_int_entry 
val inst_num_in_simple_passive     : stat_int_entry 
val inst_num_moves_active_passive  : stat_int_entry 
val inst_num_of_learning_restarts  : stat_int_entry 
val inst_max_lit_activity          : stat_int_entry 
val inst_lit_activity_moves        : stat_int_entry 
val inst_num_tautologies           : stat_int_entry 
val inst_num_of_duplicates         : stat_int_entry 
val inst_num_prop_implied          : stat_int_entry 
val inst_num_existing_simplified   : stat_int_entry 
val inst_num_child_elim            : stat_int_entry 
val inst_num_of_dismatching_blockings : stat_int_entry 
val inst_dismatching_checking_time     : stat_float_entry 
val inst_num_of_non_proper_insts   : stat_int_entry 
val inst_num_of_duplicates         : stat_int_entry  
val inst_num_from_inst_to_res      : stat_int_entry 

val clear_inst_stat                : unit -> unit

(*-----Resolution----------*)
val res_num_of_clauses                   : stat_fun_entry 
val res_num_in_passive                   : stat_fun_entry 
val res_num_in_passive_sim               : stat_int_entry 
val res_num_in_active                    : stat_int_entry 
val res_num_of_loops                     : stat_int_entry 
val res_forward_subset_subsumed          : stat_int_entry  
val res_backward_subset_subsumed         : stat_int_entry 
val res_forward_subsumed                 : stat_int_entry 
val res_backward_subsumed                : stat_int_entry 
val res_forward_subsumption_resolution   : stat_int_entry 
val res_backward_subsumption_resolution  : stat_int_entry 
val res_clause_to_clause_subsumption     : stat_int_entry 
val res_orphan_elimination               : stat_int_entry 
val res_tautology_del                    : stat_int_entry 
val res_num_sel_changes                  : stat_int_entry 
val res_moves_from_active_to_pass        : stat_int_entry 

val clear_res_stat                : unit -> unit

(*
val assign_int_stat : int  -> stat_int_entry -> unit
val incr_int_stat   : int  -> stat_int_entry ->  unit
val assign_fun_stat : stat_fun_type -> stat_fun_entry -> unit 
val get_val_stat    : stat_int_entry -> int
*)

(*val  : stat_int_entry *)



val out_stat : unit -> unit

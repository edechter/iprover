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



(*val start_instantiation : unit -> unit*)
open Lib

type clause = Clause.clause
type lit = Term.literal
type term = Term.term


type all_clauses = ClauseAssignDB.clauseDB

(*
type model
val out_model : model -> unit
*)

exception Unsatisfiable
exception Satisfiable of all_clauses
exception DontKnow

val clear_after_inst_is_dead : unit -> unit

module type InputM = 
  sig
    val inst_module_name : string
(* we assume that input clauses are normalised with terms in *)
(* Parsed_input_to_db.term_db_ref *)
(* clauses are copied, but terms are not some paremters of terms such as *)
(* inst_in_unif_index can be changed *)
(* one should run clear_all () which also clears term parameters *)
    val input_clauses    : clause list
  end

module Make (InputM:InputM) : sig
 
(*  val init_instantiation : clause list -> unit*)


(*  let lazy_loop_body solver_counter sover_clause_counter *)
      
  val lazy_loop_body  : int ref -> int ref -> unit 

(* the module is unusable after clear_all *)
  val clear_all : unit -> unit

 (* val learning_restart : clause list -> unit *)
end

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

type solver

(*type var*)

(*
type solver_name  = MiniSat | ZChaff
val current_solver :  solver_name
*)

type lit

type var_id = int

type solver_out = Sat  | Unsat

(* used in unsta_test:  AUnsat unsat under assumptions*)
type fast_solve = FSat | FUnsat | FUnknown

type lit_val    = True | False | Any
type lit_sign   = Pos  | Neg


exception Unsatisfiable
exception Create_lit_error

(* if true creates a simplifiaction solver and if false creates an incemental solver *)

val create_solver            : bool -> solver 

val num_of_solver_calls      : solver -> int
val num_of_fast_solver_calls : solver -> int
val num_of_vars              : solver -> int
val num_of_clauses           : solver -> int

val is_simplification        : solver -> bool

val add_var_solver : solver -> var_id -> unit
(* val create_variable: solver -> var_id -> var *)
val create_lit:  solver -> lit_sign -> var_id ->  lit

val lit_sign: solver -> lit -> bool

val lit_var: solver -> lit -> int

(* can raise Unsatisfiable if the solver state becomes trivialy unsat *)
val add_clause: solver -> lit list -> unit

val solve: solver -> solver_out

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val solve_assumptions: solver -> lit list -> solver_out

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val fast_solve: solver -> lit list -> fast_solve

val lit_val: solver -> lit -> lit_val 

(* to strings *)
val lit_to_string:        solver -> lit -> string
val lit_list_to_string:   solver -> lit list -> string
val solver_out_to_string: solver_out ->string
val lit_val_to_string:    lit_val -> string
val lit_sign_to_string:   lit_sign -> string   

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



type solver

type solver_uc

(*type var*)

(*
type solver_name  = MiniSat | ZChaff
val current_solver :  solver_name
*)

type lit

type lit_uc

type var_id = int

type solver_out = Sat  | Unsat

(* used in unsta_test:  AUnsat unsat under assumptions*)
type fast_solve = FSat | FUnsat | FUnknown

type lit_val    = True | False | Any
type lit_sign   = Pos  | Neg

val sign_to_bool : lit_sign -> bool

val bool_to_sign : bool -> lit_sign

exception Unsatisfiable
exception Create_lit_error

(* if true creates a simplifiaction solver and if false creates an incemental solver *)

val create_solver            : bool -> solver 

val create_solver_uc            : bool -> solver_uc

(* val create_solver_uc            : unit -> solver_uc *)

val num_of_solver_calls      : solver -> int
val num_of_fast_solver_calls : solver -> int
val num_of_vars              : solver -> int
val num_of_clauses           : solver -> int

val is_simplification        : solver -> bool

val add_var_solver : solver -> var_id -> unit
(* val create_variable: solver -> var_id -> var *)

val create_lit : solver -> lit_sign -> var_id ->  lit

val create_lit_uc : solver_uc -> lit_sign -> var_id ->  lit_uc

val lit_sign : solver -> lit -> bool

val lit_var : solver -> lit -> int

val lit_sign_uc : solver_uc -> lit_uc -> bool

val lit_var_uc : solver_uc -> lit_uc -> int

(* can raise Unsatisfiable if the solver state becomes trivialy unsat *)
val add_clause : solver -> lit list -> unit

val add_clause_with_id : solver_uc -> int option -> lit_uc list -> int option

val clauses_with_id : solver_uc -> int

val set_important_lit : solver -> lit -> unit

val solve : ?reset:bool -> solver -> solver_out

val solve_uc : solver_uc -> solver_out 

(* val unsat_core : solver_uc -> int list  *)

val get_conflicts : solver_uc -> int list 

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val solve_assumptions: ?reset:bool -> solver -> lit list -> solver_out

val solve_assumptions_uc : solver_uc -> lit_uc list -> solver_out 

val solve_assumptions_upto_id_uc : solver_uc -> lit_uc list -> int -> solver_out 

(* can raise Unsatisfiable if unsat wihtout assumptions *)
val fast_solve: solver -> lit list -> fast_solve

val lit_val: solver -> lit -> lit_val 

(* to strings *)
val lit_to_string:        solver -> lit -> string
val lit_list_to_string:   solver -> lit list -> string
val solver_out_to_string: solver_out ->string
val lit_val_to_string:    lit_val -> string
val lit_sign_to_string:   lit_sign -> string   

val pp_lit : solver -> Format.formatter -> lit -> unit

val pp_lit_list_dimacs : solver -> Format.formatter -> lit list -> unit

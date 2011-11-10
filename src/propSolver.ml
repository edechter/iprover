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



open Lib
open Statistics

exception Unsatisfiable
exception Create_lit_error

type solver_name   = MiniSat | ZChaff
let current_solver = MiniSat


type solver_out = Sat  | Unsat
(* used in unsta_test:  AUnsat unsat under assumptions*)
type fast_solve = FSat | FUnsat | FUnknown
type lit_val    = True | False | Any
type lit_sign   = Pos  | Neg
type var_id = int

type minisat_lit

type solver_core

type solver = 
  { core : solver_core;
    mutable num_of_solver_calls : int;
    mutable num_of_fast_solver_calls : int;
    mutable num_of_vars : int;
    mutable num_of_clauses : int;
    mutable is_sim         : bool;
  }

type lit = {var: var_id; sign: lit_sign; minisat_val: minisat_lit}

type lit_list = lit list

type minisat_lit_list = minisat_lit list



(* if true creates a simplifiaction solver and if false creates an incremental solver *)

external create_solver_core : bool -> solver_core = "C_create_solver"

external add_var       : solver_core -> var_id -> unit = "C_add_var"

external create_lit_minisat: var_id ->solver_core ->bool->minisat_lit = "C_create_lit"

external add_clause_to_minisat: minisat_lit array -> solver_core ->bool = "C_add_clause"

external solve_minisat: solver_core ->bool = "C_solve"

external solve_assumptions_minisat: solver_core -> minisat_lit array -> int = "C_solve_assumptions"

external fast_solve_minisat: solver_core -> minisat_lit array -> int = "C_fast_solve"

(*external print_array : int list -> unit  = "C_print_array"*)
    
(*external lit_val_minisat: solver -> minisat_lit -> bool -> int = "C_get_lit_val"*)
    
external lit_val_minisat: solver_core -> minisat_lit -> int = "C_get_lit_val"
   
(* only functions allowed... so define explicitly 
external l_False : int = "C_l_False"
external l_True  : int = "C_l_True"
external l_Undef : int = "C_l_Undef"
*)
(* should be the same as in solver.h  ... cannt match int constants, so using  explicit numbers !*)
let l_False = -1 
let l_True  =  1
let l_Undef =  0

let create_solver is_sim = 
  { core                     = create_solver_core is_sim;
    num_of_solver_calls      = 0;
    num_of_fast_solver_calls = 0;
    num_of_vars              = 0;
    num_of_clauses           = 0;
    is_sim                   = is_sim;
   }

let is_simplification solver = 
  solver.is_sim


let num_of_solver_calls solver      = solver.num_of_solver_calls
let num_of_fast_solver_calls solver = solver.num_of_fast_solver_calls
let num_of_vars solver              = solver.num_of_vars
let num_of_clauses solver           = solver.num_of_clauses

let sign_to_bool (sign_in) = 
  match sign_in with 
  |Pos -> true
  |Neg -> false
	
let add_var_solver solver var_id =
  solver.num_of_vars <- solver.num_of_vars +1;
  add_var solver.core var_id
	
let create_lit solver (sign: lit_sign) (var: var_id)   =
  if var <= 0 then raise Create_lit_error 
  else
    (solver.num_of_vars <- solver.num_of_vars +1;
  let sign_bool  = sign_to_bool sign in
  let lit_minisat = create_lit_minisat var solver.core sign_bool in
  {var =var ;  sign = sign; minisat_val = lit_minisat})
    
let get_minisat_lit (minisat_lit :lit) =
  minisat_lit.minisat_val
    
let add_clause solver (lits_in:lit_list)   =
  if lits_in = [] then
    raise Unsatisfiable
  else
    (solver.num_of_clauses <- solver.num_of_clauses;
     let list_of_minisat_lits = List.map get_minisat_lit lits_in  in
     let clause_array = Array.of_list list_of_minisat_lits in
     let out = (add_clause_to_minisat clause_array solver.core) in
     if  out = false
     then raise Unsatisfiable else ()
    )
	
      
let int_to_val int_in = 
  match int_in with 
  |  1    -> True 
  | -1    -> False
  |  0    -> Any
  | _     -> 
      failwith ("MiniSat error:int_to_val  unknown truth value: "^(string_of_int int_in))


(*  cannot mach a int constant ...
  | l_True    -> True 
  | l_False   -> False
  | l_Undef   -> Any
*)
 
(*	
let lit_val solver lit  = 
  int_to_val (lit_val_minisat solver lit.minisat_val (sign_to_bool lit.sign))
  *)  


let lit_val solver lit  = 
  int_to_val (lit_val_minisat solver.core lit.minisat_val) 


let solve solver =
  solver.num_of_solver_calls <- solver.num_of_solver_calls+1;
  let start_time = Unix.gettimeofday () in
  let outcome = solve_minisat solver.core in  
  let end_time = Unix.gettimeofday () in
  add_float_stat (end_time -. start_time) prop_solver_time;
  if outcome = true then Sat else Unsat

let solve_assumptions solver (assumptions : lit_list) =
  solver.num_of_solver_calls <- solver.num_of_solver_calls+1;
  let list_of_minisat_lits = List.map get_minisat_lit assumptions in
  let ass_array = Array.of_list list_of_minisat_lits in
  let start_time = Unix.gettimeofday () in
  let result = solve_assumptions_minisat solver.core ass_array in
  let end_time = Unix.gettimeofday () in
  add_float_stat (end_time -. start_time) prop_solver_time;
  match result with 
  |  1  -> Sat    (* under assumption *) 
  | -1  -> Unsat  (* under assumption *) 
  |  0  -> raise Unsatisfiable (* without assumptions*) 
  |_    -> failwith "MiniSat error: solve_assumptions  unknown truth value"

let fast_solve solver (assumptions : lit_list) =
  solver.num_of_fast_solver_calls <- solver.num_of_fast_solver_calls+1;
  let list_of_minisat_lits = List.map get_minisat_lit assumptions in
  let ass_array = Array.of_list list_of_minisat_lits in 
  let start_time = Unix.gettimeofday () in
  let result = fast_solve_minisat solver.core ass_array in
  let end_time = Unix.gettimeofday () in
  add_float_stat (end_time -. start_time) prop_fast_solver_time;
  match result with 
  | -1  -> FUnsat    (* under assumption *) 
  |  1  -> FUnknown  (* under assumption *) 
  |  0  -> raise Unsatisfiable (* without assumptions*) 
  |_    -> failwith "MiniSat error: solve_assumptions  unknown truth value"
	


let get_var_id lit = lit.var 
    
let lit_sign lit =  lit.sign
    

(* to_strings *)
    
let lit_to_string lit = 
  if lit.sign = Pos then string_of_int lit.var
  else string_of_int (-lit.var)

let lit_list_to_string lit_list = 
  "["^(Lib.list_to_string lit_to_string lit_list ",")^"]"

let solver_out_to_string = function
  |Sat   -> "Satisfiable"
  |Unsat -> "Unsatisfiable"
  


let lit_val_to_string = function 
  |True  -> "True"
  |False -> "False"
  |Any   -> "Any"

let lit_sign_to_string = function
  |Pos  -> "Positive"
  |Neg  -> "Negative"

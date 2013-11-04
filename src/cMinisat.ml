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
open Statistics

exception Unsatisfiable
exception Create_lit_error

type minisat_lit

type solver_core

(* A solver instance *)
type solver = 
    { core : solver_core;
      mutable num_of_solver_calls : int;
      mutable num_of_fast_solver_calls : int;
      mutable num_of_vars : int;
      mutable num_of_clauses : int;
      mutable is_sim         : bool;
    }

(* A literal in a solver instance *)
type literal = {var: int; sign: bool; minisat_val: minisat_lit}

type lit_list = literal list

type minisat_lit_list = minisat_lit list



(* if true creates a simplifiaction solver and if false creates an incremental solver *)

external create_solver_core : bool -> solver_core = "C_create_solver"

(* resets solver but keeps clauses/in some solvers does not do anything *)
(*external solver_reset_core      : solver_core -> unit = "C_solver_reset"*)

external add_var_minisat : solver_core -> int -> unit = "C_add_var"

external create_lit_minisat: int ->solver_core ->bool->minisat_lit = "C_create_lit"

external add_clause_to_minisat: minisat_lit array -> solver_core ->bool = "C_add_clause"

(* the second argument is solver reset, done only in PicoSAT version *)
external solve_minisat: solver_core -> bool ->bool = "C_solve"

(* the third argument is solver reset, done only in PicoSAT version *)
external solve_assumptions_minisat: solver_core -> minisat_lit array -> bool -> int = "C_solve_assumptions"

external fast_solve_minisat: solver_core -> minisat_lit array -> int = "C_fast_solve"

(*external print_array : int list -> unit  = "C_print_array"*)
    
(*external lit_val_minisat: solver -> minisat_lit -> bool -> int = "C_get_lit_val"*)
    
external lit_val_minisat: solver_core -> minisat_lit -> int = "C_get_lit_val"

external important_lit_minisat: solver_core -> minisat_lit -> unit = "C_important_lit"
    
(* only functions allowed... so define explicitly 
   external l_False : int = "C_l_False"
   external l_True  : int = "C_l_True"
   external l_Undef : int = "C_l_Undef"
 *)
(* should be the same as in solver.h  ... cannt match int constants, so using  explicit numbers !*)
let l_False = -1 
let l_True  =  1
let l_Undef =  0

(*  Creates and returns a new solver instance *)
let create_solver is_sim = 
  { core                     = create_solver_core is_sim;
    num_of_solver_calls      = 0;
    num_of_fast_solver_calls = 0;
    num_of_vars              = 0;
    num_of_clauses           = 0;
    is_sim                   = is_sim;
  }

(* Return [true] if the solver was created as a simplification
   solver in {!create_solver} *)
let is_simplification solver = solver.is_sim

(* Return the number of calls to {!solve} of the solver instance *)
let num_of_solver_calls solver = 
  solver.num_of_solver_calls

(* Return the number of calls to {!fast_solve} of the solver instance *)
let num_of_fast_solver_calls solver = 
  solver.num_of_fast_solver_calls

(* Return the number of propositional variables in the solver instance *)
let num_of_vars solver = 
  solver.num_of_vars

(* Return the number of clauses in the solver instance *)
let num_of_clauses solver = 
  solver.num_of_clauses

(* Adds the propositional variable [var_id] to the solver *)	
let add_var solver var_id =
  solver.num_of_vars <- solver.num_of_vars + 1;
  add_var_minisat solver.core var_id
    
(* Create and return a literal of the propositional
   variable [var] with sign [sign] 

   var = 0 is allowed in, but use var + 1 in order to be safe here
 *)
let create_lit solver sign var =
  (* TODO: var = 0 seems to be allowed, but check before changing
     calling code; Not in PicoSAT/Lingeling *)
  if var <= 0 then raise Create_lit_error 
  else
    (solver.num_of_vars <- solver.num_of_vars + 1;
     let lit_minisat = create_lit_minisat var solver.core sign in
     { var = var ;  sign = sign ; minisat_val = lit_minisat })
      
let get_minisat_lit minisat_lit =
  minisat_lit.minisat_val
    
(* Assert the clause given as a list of literals in the solver *)
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
      
      
let int_to_bool_option int_in = 
  match int_in with 
  |  1    -> Some true
  | -1    -> Some false
  |  0    -> None
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


(* Return the truth value of the literal in the current model *)
let model_value solver lit  = 
  int_to_bool_option 
    (lit_val_minisat solver.core lit.minisat_val) 

(* Test the given clause set for satisfiability; reset solver if reset is true *)
let solve ?(reset = false) solver =
  solver.num_of_solver_calls <- solver.num_of_solver_calls+1;
  let outcome = solve_minisat solver.core reset in  
  if outcome = true then true else false

(* Test the given clause set for satisfiability when the given
   literals are to be made true. *)
let solve_assumptions ?(reset = false) solver (assumptions : lit_list) =
  solver.num_of_solver_calls <- solver.num_of_solver_calls+1;
  let list_of_minisat_lits = List.map get_minisat_lit assumptions in
  let ass_array = Array.of_list list_of_minisat_lits in
  let result = solve_assumptions_minisat solver.core ass_array reset in
  match result with 
  |  1  -> true    (* under assumption *) 
  | -1  -> false  (* under assumption *) 
  |  0  -> raise Unsatisfiable (* without assumptions*) 
  |_    -> failwith "MiniSat error: solve_assumptions  unknown truth value"

let fast_solve solver (assumptions : lit_list) =
  solver.num_of_fast_solver_calls <- solver.num_of_fast_solver_calls+1;
  let list_of_minisat_lits = List.map get_minisat_lit assumptions in
  let ass_array = Array.of_list list_of_minisat_lits in 
  let result = fast_solve_minisat solver.core ass_array in
  match result with 
  | -1  -> Some false    (* under assumption *) 
  |  1  -> Some true     (* under assumption *) 
  |  0  -> raise Unsatisfiable (* without assumptions*) 
  |  -2  -> None  (* from C++ MiniSat *) 
  |_    -> failwith "MiniSat error: fast_solve  unknown truth value"
	

let set_important_lit solver lit = 
  important_lit_minisat solver.core lit.minisat_val
    

(* First variable is 0, but here always use var > 0 *)
let lit_var _ lit = lit.var 
    
let lit_sign _ lit = lit.sign
    

(* to_strings *)
    
let literal_to_string _ lit = 
  if lit.sign then string_of_int lit.var
  else string_of_int (-lit.var)

let pp_literal _ ppf lit = 
  Format.fprintf ppf "%s" (literal_to_string () lit)

let literal_list_to_string _ lit_list = 
  "["^(Lib.list_to_string (literal_to_string ()) lit_list ",")^"]"

let pp_literal_list _ ppf list = 
  Format.fprintf ppf "%s" (literal_list_to_string () list)

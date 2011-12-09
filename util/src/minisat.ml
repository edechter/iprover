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

(*
  
  Created: 2011-12-07 Christoph Sticksel

*)

type minisat_solver

type minisat_lit

type lbool = 
  | L_true
  | L_false
  | L_undef

let int_to_lbool = function 
  | 0 -> L_true
  | 1 -> L_false
  | 2 -> L_undef
  | _ -> invalid_arg "int_to_lbool"

let pp_lbool ppf = function 
  | L_true -> Format.fprintf ppf "L_true"
  | L_false -> Format.fprintf ppf "L_false"
  | L_undef -> Format.fprintf ppf "L_undef"

(*
external dummy_unit : unit -> int = "dummy_unit"

external dummy_int_id : int -> int = "dummy_int_id"
*)

external create_solver : unit -> minisat_solver = "minisat_create_solver" 

external add_var : minisat_solver -> int -> unit = "minisat_add_var"

external create_lit : minisat_solver -> int -> bool -> minisat_lit = "minisat_create_lit"

external stat_vars : minisat_solver -> int = "minisat_stat_vars" 

external add_clause : minisat_solver -> minisat_lit list -> bool = "minisat_add_clause"

external lit_to_int : minisat_solver -> minisat_lit -> int = "minisat_lit_to_int"

external solve : minisat_solver ->  bool = "minisat_solve"

external solve_assumptions : minisat_solver -> minisat_lit list -> int = "minisat_solve_assumptions"

external model_value : minisat_solver -> minisat_lit -> int = "minisat_model_value"
external fast_solve : minisat_solver -> minisat_lit list -> int = "minisat_fast_solve"

let main () = 

  let s = create_solver () in

  let p = create_lit s 0 true in

  let q = create_lit s 1 true in

  let r = create_lit s 2 true in

  let p' = create_lit s 0 false in

  let q' = create_lit s 1 false in

  let c1 = add_clause s [p; q; r] in 

  let c2 = add_clause s [p'] in 

  let res1 = solve s in

  let res2 = int_to_lbool (solve_assumptions s []) in

  let res3 = int_to_lbool (solve_assumptions s [q]) in

  let res4 = int_to_lbool (solve_assumptions s [r]) in
  
  let res1' = int_to_lbool (fast_solve s []) in

  let res2' = int_to_lbool (fast_solve s []) in

  let res3' = int_to_lbool (fast_solve s [q]) in

  let res4' = int_to_lbool (fast_solve s [r]) in
  
  let m_p = int_to_lbool (model_value s p) in
  let m_q = int_to_lbool (model_value s q) in
  let m_p' = int_to_lbool (model_value s p') in
  let m_q' = int_to_lbool (model_value s q') in
  let m_r = int_to_lbool (model_value s r) in

  Format.printf
    "res1: %B@\nres2: %a@\nres3: %a@\nres4: %a@\n@."
    res1
    pp_lbool res2
    pp_lbool res3
    pp_lbool res4;

  Format.printf
    "res1': %a@\nres2': %a@\nres3': %a@\nres4': %a@\n@."
    pp_lbool res1'
    pp_lbool res2'
    pp_lbool res3'
    pp_lbool res4';

  Format.printf
    "p: %a@\nq: %a@\np': %a@\nq': %a@\nr: %a@\n@."
    pp_lbool m_p
    pp_lbool m_q
    pp_lbool m_p'
    pp_lbool m_q'
    pp_lbool m_r
;;

(* Call main when called as script *)
main ();;

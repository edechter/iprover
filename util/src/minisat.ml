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

let main () = 

  let s = create_solver () in

  (* let s2 = create_solver () in *)

  let p = create_lit s 1 true in

  Format.printf "Literals: %d@." (lit_to_int s p);

  let q = create_lit s 2 true in

  (* Format.printf "Literals: %d %d@." (lit_to_int s p) (lit_to_int s q); *)

  let p' = create_lit s 1 false in

  (* Format.printf 
    "Literals: %d %d %d@." 
    (lit_to_int s p) 
    (lit_to_int s q)
    (lit_to_int s p'); *)

  let q' = create_lit s 2 false in

(*
  Format.printf 
    "Literals: %d %d %d %d@." 
    (lit_to_int s q') 
    (lit_to_int s p')
    (lit_to_int s p)
    (lit_to_int s q); 
*)

  let c1 = add_clause s [p; q] in 

  let c2 = add_clause s [p'] in 

  let c3 = add_clause s [q'] in 

  let res = solve s in

    Format.printf 
      "variables: %d@\nc1: %B@\nc2: %B@\nc3: %B@\nres: %B@."
      (stat_vars s)
      c1
      c2
      c3
      res;

  Format.printf 
    "Literals: %d %d %d %d@." 
    (lit_to_int s p) 
    (lit_to_int s q)
    (lit_to_int s p')
    (lit_to_int s q')


;;

(* Call main when called as script *)
main ();;

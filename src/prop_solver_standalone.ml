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

type lit = PropSolver.lit


(*- read from stdin -*)
(* create an incremental solver (if true simplification solver is created) *)

let solver     = PropSolver.create_solver false 

type i_lit = int
type clause = int list

(* PropSolver.create_lit solver PropSolver.Pos var_id*)


let sign i_l = 
  if i_l> 0
  then
    PropSolver.Pos
  else
    if i_l=0
    then
      failwith "lit should not be equal to 0"
    else 
      PropSolver.Neg


let add_clause i_c = 
  let lit_list = 
    List.map 
      (fun l ->
	let var_id = abs l in
	PropSolver.add_var_solver solver var_id; 
	PropSolver.create_lit solver (sign l) var_id
      ) i_c  
  in        
  out_str ((PropSolver.lit_list_to_string lit_list)^"\n");
  PropSolver.add_clause solver lit_list

let read_clauses () =
  let current_clause = ref [] in
  let clause_list = ref [] in
  try
    while true do
      let str = read_line () in
      if (String.length str = 0)
      then ()
      else
	(
	 if (str.[0] = 'c' || str.[0] ='p') 
	 then ()
	 else
	   let str_list = Str.split (Str.regexp " ") str in
	   let l_list = List.map (fun s -> int_of_string s) str_list in
	   
	   let rec fill_str list = 
	     match list with 
	     |h::tl -> 
		 if h = 0 
		 then 
		   (
		    assert ((List.length !current_clause) > 0);
		    clause_list := (!current_clause)::(!clause_list);
		    current_clause := [];
		    fill_str tl
		   )
		 else
		   (
		    current_clause:=h::(!current_clause);
		    fill_str tl
		   )
	     |[] -> ()
	   in
	   fill_str l_list
	)
    done;
    !clause_list
  with 
    End_of_file ->      
      (
       if ((List.length !current_clause) > 0)
       then
	 (
	  clause_list := (!current_clause)::(!clause_list);
	  current_clause := [];
	  !clause_list
	 )
       else
	 !clause_list
      )
	   


let () = 
  let c_list = read_clauses () in
  try
    List.iter (fun c -> add_clause c) c_list;
    match  (PropSolver.solve solver) 
    with 
    |PropSolver.Sat   -> out_str "SATISFIABLE"
    |PropSolver.Unsat -> out_str "UNSATISFIABLE"
  with 
    PropSolver.Unsatisfiable -> out_str "UNSATISFIABLE"
	

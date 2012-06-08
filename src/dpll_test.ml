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

let file_name = "/home/korovin/SAT/Blocks/medium.cnf"

let rec strip_comments file = 
  try   
    let next_str = input_line file in 
    if (String.length next_str > 0) 
    then  
      let first_char = String.get next_str 0 in
      if (first_char = 'c') || (first_char = 'p')  
      then   
	strip_comments file
      else
	next_str^" "^(strip_comments file)
    else  
      strip_comments file
  with 
    End_of_file -> " "
  |_-> failwith "strip_comments "

let number_expr = Str.regexp "-?[0-9]+"

let rec str_to_clause_list' part_clause part_list str pos str_length = 
  if (pos < str_length) 
  then
    try 
      let _=Str.search_forward number_expr str pos in
      let next_number = int_of_string (Str.matched_string  str) in
      let next_pos = Str.match_end () in
      if (next_number != 0 )
      then 
	str_to_clause_list' 
	  (next_number::part_clause) part_list str next_pos str_length
      else
	str_to_clause_list' [] (part_clause::part_list) str next_pos str_length
    with
(* we assume that each clause iincluding the last one is ended by 0*)
      Not_found ->  part_list
  else part_list
		
let str_to_clause_list str = 
   str_to_clause_list' [] [] str 0 (String.length str)
 
let read_file file_name =  
  let file = open_in file_name in
  let str = strip_comments file in
  close_in file;
  str_to_clause_list str

(* *)
module PropStruct = 
  struct 
    type var = int 
    type lit = int
    type clause = lit list

    let pos_lit lit = (lit > 0) 
    let get_var lit = 
      if (lit > 0) 
      then lit 
      else -lit
    let compare_var = compare
    let var_to_string = string_of_int 
 end


module DPLLM = Dpll.Make (PropStruct)

let state = DPLLM.create_init_state ()

let run_dpll file_name = 
  let clause_litst = read_file file_name in
  try DPLLM.dpll state clause_litst 
  with 
  | Dpll.Satisfiable -> out_str "Satisfiable"
  | Dpll.Unsatisfiable -> out_str "Unsatisfiable"
 
let () = run_dpll file_name 

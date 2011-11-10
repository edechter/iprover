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

type var = int
type t = var
type bound_var = var Lib.bind

let get_first_var () = 0
let get_next_var var = var + 1 

let compare = compare 
let equal = (=)

let compare_bvar (bv1 : bound_var) (bv2 : bound_var) =  
  Lib.pair_compare_lex compare compare bv1 bv2

let equal_bvar bv1 bv2 = 
   if (compare_bvar bv1 bv2)=cequal then true 
   else false

let hash var = var
let index var = var


let to_stream s var = 
  s.stream_add_char 'X';
  s.stream_add_str (string_of_int var)

let out = to_stream stdout_stream

let to_string =  
  to_string_fun_from_to_stream_fun 5 to_stream

let to_prolog  = to_string

(*let to_string var = "X"^(string_of_int var)*)

(* for uniformity to_string is via buffers *)


(* let fast_key_to_int var = var *)

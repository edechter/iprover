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

type symbol = Symbol.symbol
type stype  = Symbol.stype

let symbol_db_ref  = Parser_types.symbol_db_ref



type pre_new_type = 
    {
     symb : symbol;
(* the number in the list of arguments, 0 is the value type *)
     arg  : int;
     arg_type : stype
   }

(*pre_new_type element of union find*)

module PNTE = 
  struct 
    type t = pre_new_type
    let equal t1 t2 = 
      (t1.symb == t2.symb) 
	&& 
      (t1.arg = t2.arg) 
	&&
      (t1.arg_type == t2.arg_type) 

    let hash t = ((Symbol.get_fast_key t.symb) lsl 5) + t.arg
	
  end
    
module UF_PNT = Union_find.Make(PNTE)



(*let typify_clause clause type_context =  
 
let typify_clause_list clause_list =*)

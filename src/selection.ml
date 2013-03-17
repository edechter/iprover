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
open Options
type term    = Term.term
type clause  = Clause.clause
type literal = Clause.literal

(* don't need it much since in unif index we store (L,clause) *)
let get_sel sel_fun clause =
  try
    Clause.get_res_sel_lits clause
  with Clause.Res_sel_lits_undef ->
    let sel_lits = sel_fun clause in
    Clause.res_assign_sel_lits sel_lits clause;
    sel_lits

let kbo_sel_max' clause = 
  list_get_max_elements_v 
    Orderings.simple_kbo_lit (Clause.get_lits clause)

(*let kbo_sel_max clause = get_sel kbo_sel_max' clause see below*)

let literal_neg_selection_max'  clause = 
(*let lit_neg_sel_max_t clause =*)
 let neg_literals = Clause.find_all Term.is_neg_lit clause in
   let cmp lit1 lit2 = 
     compare (Term.get_num_of_symb lit1) (Term.get_num_of_symb lit2) in
   try  
     let neg_literal  = list_find_max_element cmp neg_literals in
     [neg_literal]
   with 
     Not_found -> (* all lits are positive*)
       list_get_max_elements_v 
	 Orderings.simple_kbo_lit (Clause.get_lits clause)
    
let literal_neg_selection_max  = 
  get_sel literal_neg_selection_max' 

(*let literal_neg_selection_max = literal_neg_selection_max'*)

let literal_neg_selection_min'  clause = 
  let neg_literals = Clause.find_all Term.is_neg_lit clause in
  let cmp lit1 lit2 = 
    compare (Term.get_num_of_symb lit1) (Term.get_num_of_symb lit2) in
    try  
      let neg_literal  = list_find_max_element (fun x y -> - (cmp x y)) neg_literals in
      [neg_literal]
    with 
    Not_found -> (* all lits are positive*)
      list_get_max_elements_v Orderings.simple_kbo_lit (Clause.get_lits clause)
	
let literal_neg_selection_min clause = get_sel literal_neg_selection_min' clause


(* changing selection !*)


(* next_neg_sel moving to the next negative selection   *)
(* chnages the selection and returns the new sel lit *)
(* can raise  No_next_neg *)
(* assume no duplicates of lits in the clause *)
exception No_next_neg
let next_neg_sel clause = 
  let  lits = (Clause.get_lits clause) in
  try 
    let current_sel = 
      (match (Clause.get_res_sel_lits clause) 
      with h::tl -> h
      |_->  failwith "Selection: next_neg_sel selection is not neg")
    in
    let tail_lits = list_skip current_sel lits in
    try 
      let next_sel = List.find Term.is_neg_lit tail_lits in
      (* todo test if next_sel is the last neg and all in the original are*)
      (* neg then it is already max sel*)
      Clause.res_assign_sel_lits [next_sel] clause; 
      [next_sel]
    with 
      Not_found -> raise No_next_neg
  with 
    Clause.Res_sel_lits_undef ->   
      try 
	let next_sel = List.find Term.is_neg_lit lits in
	Clause.res_assign_sel_lits [next_sel] clause; 
	[next_sel]
      with 
	Not_found -> raise No_next_neg
	    

(* sel max kbo but if there is neg in max then selects any such neg*)
let sel_kbo_max clause =
  if (not (Clause.get_res_sel_max clause)) 
  then 
    (Clause.set_res_sel_max true clause;
     let new_sel_lits = 
       list_get_max_elements_v 
	 Orderings.simple_kbo_lit (Clause.get_literals clause)
     in 
     try  
       let neg_sel = List.find Term.is_neg_lit new_sel_lits in
       Clause.res_assign_sel_lits [neg_sel] clause; 
       [neg_sel]
     with
       Not_found -> 
	 (Clause.res_assign_sel_lits new_sel_lits clause;
	  new_sel_lits)
    )
  else
    try 
      Clause.get_res_sel_lits clause 
    with 
      Clause.Res_sel_lits_undef -> 
	failwith "Selection: sel_kbo_max"

(*change_sel changes selection to new and returns new selected literals *)
(*if  selection is already max then raises Max_sel  *)
(*also works when no sel is assigned*)
exception Max_sel	  
let change_sel clause = 
  if (Clause.get_res_sel_max clause) 
  then raise Max_sel
  else
    try 
      next_neg_sel clause
    with 
      No_next_neg -> 
	sel_kbo_max clause


let res_lit_sel_type_to_fun res_lit_sel_type = 
  match res_lit_sel_type with 
  |Res_Adaptive    -> change_sel
  |Res_KBO_Max     -> sel_kbo_max
  |Res_Neg_Sel_Max -> literal_neg_selection_max
  |Res_Neg_Sel_Min -> literal_neg_selection_min


let res_lit_sel clause = 
(* don't need it much since in unif index we store (L,clause) *)
  let sel_fun = res_lit_sel_type_to_fun !current_options.res_lit_sel in
  get_sel sel_fun clause

      

(*-------------------------instantiation selections-----------------------*)


(* lit_selector chooses some literals from clause i.e. true in a model *)
let inst_lit_sel lit_selector clause = 
  let candidate_list = Clause.find_all lit_selector clause in
  let cmp_fun = (Term.lit_cmp_type_list_to_lex_fun 
		   !current_options.inst_lit_sel) in
  list_find_max_element cmp_fun candidate_list

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

type term    = Term.term
type clause  = Clause.clause
type literal = Clause.literal


(* don't need it much since in unif index we store (L,clause) *)
let get_sel sel_fun clause = 
  try 
    Clause.get_res_sel_lits clause 
  with Clause.Res_sel_lits_undef ->   
    let sel_lits = sel_fun clause in
    Clause.assign_res_sel_lits sel_lits clause; 
    sel_lits

let kbo_sel_max' clause = 
  list_get_max_elements_v 
    Orderings.simple_kbo (Clause.get_literals clause)

let kbo_sel_max clause = get_sel kbo_sel_max' clause

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
	 Orderings.simple_kbo (Clause.get_literals clause)
    
let literal_neg_selection_max  = get_sel literal_neg_selection_max' 

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
      list_get_max_elements_v Orderings.simple_kbo (Clause.get_literals clause)
	
let literal_neg_selection_min clause = get_sel literal_neg_selection_min' clause

(********* instantiation selections*****************)

  
let cmp_ground t1 t2 =
  let gt1 = if (Term.is_ground t1) then 1 else 0 in
  let gt2 = if (Term.is_ground t2) then 1 else 0 in
  compare gt1 gt2

let cmp_num_symb t1 t2 =
  compare (Term.get_num_of_symb t1) (Term.get_num_of_symb t2)

let cmp_num_var t1 t2 =
  compare (Term.get_num_of_var t1) (Term.get_num_of_var t2)

(*pos bigger than neg*)
let cmp_sign t1 t2 =
  let nt1 = if (Term.is_neg_lit t1) then 1 else 0 in
  let nt2 = if (Term.is_neg_lit t2) then 1 else 0 in
  -(compare nt1 nt2)


(*
let lit_pos_big_var get_prop_truth clause =
  let lex_compare = 
    lex_combination [cmp_sign;cmp_num_symb;compose_12 (~-) cmp_num_var] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list



let cmp_neg t1 t2 =
  let nt1 = if (Term.is_neg_lit t1) then 1 else 0 in
  let nt2 = if (Term.is_neg_lit t2) then 1 else 0 in
  compare nt1 nt2

let cmp_pos t1 t2 = -(cmp_neg t1 t2)

let cmp_ground t1 t2 =
  let gt1 = if (Term.is_ground t1) then 1 else 0 in
  let gt2 = if (Term.is_ground t2) then 1 else 0 in
  compare gt1 gt2

 
let cmp_size t1 t2 =
  -(compare (Term.get_num_of_sym t1) (Term.get_num_of_sym t2))

let cmp_size t1 t2 =
  -(compare (Term.get_num_of_sym t1) (Term.get_num_of_sym t2))


let cmp_size_big t1 t2 =
  (compare (Term.get_num_of_sym t1) (Term.get_num_of_sym t2))

let cmp_num_var t1 t2 =
  -(compare (Term.get_num_of_var t1) (Term.get_num_of_var t2))



let lit_neg_gr_shallow get_prop_truth clause =
  let lex_compare = lex_combination [cmp_neg; cmp_ground;cmp_size] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_gr_neg_shallow get_prop_truth clause =
  let lex_compare = lex_combination [cmp_ground;cmp_neg;cmp_size] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_var_neg_shallow get_prop_truth clause =
  let lex_compare = lex_combination [cmp_num_var;cmp_neg;cmp_size] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_var_neg_big get_prop_truth clause =
  let lex_compare = lex_combination [cmp_num_var;cmp_neg;cmp_size_big] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_var_big_neg get_prop_truth clause =
  let lex_compare = lex_combination [cmp_num_var;cmp_size_big;cmp_neg] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_var_sh_neg get_prop_truth clause =
  let lex_compare = lex_combination [cmp_num_var;cmp_size;cmp_neg] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_neg_var_sh get_prop_truth clause =
  let lex_compare = lex_combination [cmp_neg;cmp_num_var;cmp_size] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list



let lit_neg_var_big  get_prop_truth clause =
  let lex_compare = lex_combination [cmp_neg;cmp_num_var;cmp_size_big] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_neg_big_var get_prop_truth clause =
  let lex_compare = lex_combination [cmp_neg;cmp_size_big;cmp_num_var] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list


let lit_pos_var_sh get_prop_truth clause =
  let lex_compare = lex_combination [cmp_pos;cmp_num_var;cmp_size] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list


let lit_big_var_neg get_prop_truth clause =
  let lex_compare = lex_combination [cmp_size_big;cmp_num_var;cmp_neg] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_big_neg_var get_prop_truth clause =
  let lex_compare = lex_combination [cmp_size_big;cmp_neg;cmp_num_var] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

let lit_big_pos_var get_prop_truth clause =
  let lex_compare = lex_combination [cmp_size_big;cmp_pos;cmp_num_var] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list


let lit_big_var_pos get_prop_truth clause =
  let lex_compare = lex_combination [cmp_size_big;cmp_num_var;cmp_pos] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list


let lit_pos_var_big get_prop_truth clause =
  let lex_compare = lex_combination [cmp_pos;cmp_num_var;cmp_size_big] in
  let candidate_list = Clause.find_all get_prop_truth clause in
  list_find_max_element lex_compare candidate_list

*)

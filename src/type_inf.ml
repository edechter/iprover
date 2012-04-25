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

type symbol = Symbol.symbol
type stype  = Symbol.stype
type clause = Clause.clause 

let symbol_db_ref  = Parser_types.symbol_db_ref


(* we assume all symbols we are dealing with are put to symbol_db_ref *)

(* we assume that the problem is typed initially, *)
(* (in fof, cnf all types initially are $i type);*)
(* then we 1) sub-type each type with (symbol, arg_ind) arg_ind includes value *)
(* 2) merge sub_types according occurences in args and var linking *)
(* we assume that sub_types of different types are never merged i.e. initially, the problem was correctly typed *)
(* 3) collaps sub_types due to unshielded positive eq: x=t, t=x, x=y *)
(*    we collaps all sub_types of eq_type   (we reinstate original type for any symbol with is type)  overriding sub_typing       *)


type sub_type = 
    {
     sym      : symbol;
(* the number in the list of arguments, 0 is the value type *)
     arg_ind  : int;
     arg_type : symbol
   }

let sub_type_to_str st = 
   (Symbol.to_string st.arg_type)^"_"
  ^(Symbol.to_string st.sym)^"_"
  ^(string_of_int st.arg_ind)

let create_sub_type sym arg_ind arg_type = 
  {
   sym = sym; 
   arg_ind = arg_ind;
   arg_type = arg_type;
 }

(* sub_type element of union find*)

module SubTypeE = 
  struct 
    type t = sub_type

    let equal t1 t2 = 
      (t1.sym == t2.sym) 
	&& 
      (t1.arg_ind = t2.arg_ind) 
	&&
      (t1.arg_type == t2.arg_type) 

    let hash t = ((Symbol.get_fast_key t.sym) lsl 5) + t.arg_ind
	
  end
    
module UF_ST = Union_find.Make(SubTypeE)

module VarTable = Hashtbl.Make (Var)

module SymSet = Set.Make (Symbol)

type context = 
    {
     uf : UF_ST.t;
     
(*types with X=Y, X=t, t=X are collapsed since all arg_subtypes should be merged *)
(* can be relaxed later *)
(* collapsed types implicitly override sub_types *)
     mutable collapsed_types : SymSet.t; 

  }

(* var -> sub_type table linking variables to a choosen sub_type of this var; local to each clause *)
(*needs to be rest with each clause, not very good *)

type vtable =  (sub_type) VarTable.t

let get_sym_types sym =
  match (Symbol.get_stype_args_val sym) with 
  |Def (arg_t, v_t) -> (arg_t, v_t)
  |_-> failwith "get_sym_types: arg_types should be defined"

  
   
(*    top_type : sub_type option; *)
(* f(t_1,t_2) at t_2 we have top_type_top is f_arg_2 *)

(* top_type_opt_term_list = [(Some(top_sub_type),fun_term);(None, pred_term)...]  *)

let rec extend_uf_types context (vtable:vtable) top_sub_type_opt_term_ass_list = 
(* first define a function for processing arguments that we will use several times *)

  let process_args_fun sym args ass_list= 
    let arg_types, _val_type = get_sym_types sym in 
    let arg_list = Term.arg_to_list args in
    let (_,_,add_ass_list) = 	  
      Term.arg_fold_left 
	(fun (arg_ind,arg_types_rest,ass_list_rest) arg -> 
	  match arg_types_rest with 
	  |h::tl -> 	   
	      let arg_sub_type = create_sub_type sym arg_ind h in	
	      ((arg_ind+1),tl, ((Some (arg_sub_type),arg)::ass_list_rest))
	  |[] -> failwith "process_args_fun: should not happen"
	)
	(1,arg_types,[]) 
	args
    in
    let new_ass_list = add_ass_list@ass_list in
    extend_uf_types context vtable new_ass_list
  in
(* aux fun *)
  let get_val_sub_type sym =
    let _arg_types, val_type = get_sym_types sym in 
    let val_sub_type = (create_sub_type sym 0 val_type) in
    val_sub_type
  in

(*----------- main part ---------------*)

  match top_sub_type_opt_term_ass_list with 
  |(Some(top_sub_type), Term.Fun (sym,args,_))::tl_ass ->
(* here we assume that sym is not fun (not pred) since Some *)
      let val_sub_type =  get_val_sub_type sym in
      UF_ST.union context.uf top_sub_type val_sub_type;
      process_args_fun sym args tl_ass
	
  |(Some(top_sub_type), Term.Var(var,args))::tl_ass ->
     ( try 
       let var_sub_type = VarTable.find vtable var in
       UF_ST.union context.uf top_sub_type var_sub_type;
       extend_uf_types context vtable tl_ass
      with 
       Not_found ->
	 (
	  VarTable.add vtable var top_sub_type; 
	  UF_ST.add context.uf top_sub_type;
	  extend_uf_types context vtable tl_ass
	 )
      )
  |(None, lit)::tl_ass ->
(* here we assume that sym is pred/or ~pred since None *)
      let atom = Term.get_atom lit in
(* dealing with equality *)
      if (Term.is_eq_atom atom)  
      then
	match atom with 
	|Term.Fun (_sym, args,_) ->

	    let [type_term_eq; t;s] = Term.arg_to_list args in

	    let eq_v_type = 
	      try
		Term.get_top_symb type_term_eq 
	      with Term.Var_term -> 
		failwith 
		  "equality should not have var as the type argument; proabably equality axioms are added which are not needed here"
	    in
	    if (not (Term.is_neg_lit atom)) (* positive eq *)
	    then
		  begin		      
		    match (t,s) with 
		    |(Term.Fun(sym1,args1,_),Term.Fun(sym2,args2,_)) ->
			(
			 let val_sub_type1 = get_val_sub_type sym1 in
			 let val_sub_type2 = get_val_sub_type sym2 in	
	    		 UF_ST.union context.uf val_sub_type1 val_sub_type2;	
			 process_args_fun sym1 args1 [];
			 process_args_fun sym2 args2 [];
			 extend_uf_types context vtable tl_ass
			)
			    
(* type collaps cases *)
		    |(Term.Var (_v, _),Term.Fun(sym,args,_))
		    |(Term.Fun(sym,args,_),Term.Var (_v, _)) -> 
			(
			 context.collapsed_types <-
			   SymSet.add eq_v_type context.collapsed_types;
			   (* arguments can be still of a different type  *)
			 process_args_fun sym args tl_ass
			)
		    |(Term.Var(_v1,_),Term.Var (_v2, _)) ->  
			(context.collapsed_types <-
			  SymSet.add eq_v_type context.collapsed_types
			)
		  end		  
	    else (* neg equality, as usual pred only in place of top sym is eq_v_type *)	    
      	      (process_args_fun eq_v_type args tl_ass)

		
	|_-> failwith "extend_uf_types: non-eq 2"
      else (* non eq predicate *)
	(match atom with 
	|Term.Fun (sym,args,_) ->
	    (process_args_fun sym args tl_ass)
	|_-> failwith "extend_uf_types: var"
	)

  |[] -> ()


let extend_uf_types_clause context clause = 
  let lits = Clause.get_literals clause in 
  let top_sub_type_opt_term_ass_list = 
    List.map (fun l -> (None,l)) lits 
  in 
  let vtable =  VarTable.create 10 in
  extend_uf_types context vtable top_sub_type_opt_term_ass_list


let extend_uf_types_clause_list context clause_list = 
  List.iter (extend_uf_types_clause context) clause_list



module STypeTable = Hashtbl.Make(SubTypeE)


(* get_subt_nf_to_all_subt returns *) 
(* STypeTable maping sub_type normal form into list of all sub_types it represents *)
(* does not take into account collapsed types *)

let st_nf_to_all_st_table context = 
  let st_table = STypeTable.create (UF_ST.length context.uf) in
  let iter_fun st st_nf = 
    try
      let old_list = STypeTable.find st_table st_nf in
      STypeTable.replace st_table st_nf (st::old_list)
    with 
      Not_found ->
	STypeTable.add st_table st_nf ([st])
  in 
  UF_ST.iter iter_fun context.uf;
  st_table


let sub_type_inf clause_list = 

    let context = 
    {
     uf = UF_ST.create 301;
     collapsed_types =  SymSet.empty; 
   }

  in
    (
     extend_uf_types_clause_list context clause_list;       
     );
  let st_nf_table = st_nf_to_all_st_table context in
(* debug *)
  out_str "Inferred Subtypes:\n\n";
  STypeTable.iter 
    (fun nf st_list -> 
      out_str ("NF: "^(sub_type_to_str nf)^" "
	       ^"["^(list_to_string sub_type_to_str st_list ";")^"]\n\n"
	      )
    ) st_nf_table;

  out_str "\n Collapsed Types:\n\n";
  SymSet.iter 
    (fun sym -> 
      out_str ((Symbol.to_string sym)^", "))  context.collapsed_types

 
(*-------------------Commented below-----------------*)

(*
let rec extend_uf_types context top_type_opt term = 
  match term with 
  |Term.Fun (sym,args,_) ->
      let arg_types, v_type = 
	match (Symbol.get_stype_args_val sym) with 
	|Def (arg_t, v_t) -> (arg_t, v_t)
	|_-> failwith "extend_uf_types: arg_types should be defined"
      in 
      (* extend args *)
      ignore(
      Term.arg_fold_left 
	(fun (arg_ind,arg_types_rest) arg -> 
	  let h::tl = arg_types_rest in 
	  let new_pnt = create_pnt sym arg_ind h in
	  extend_uf_types context (Some new_pnt) arg;
	  ((arg_ind+1),tl) 
	)
	(1,arg_types) 
	args
     );
  
      if (Symbol.is_pred sym) 
      then 
	(
	 if (sym == Symbol.symb_typed_equality) 
	 then 
	   match args with 
	   | [type_eq_; t;s] -> 
	       if !(Term.is_var t) && !(Term.is_var s) 
	       then 
..............
		 extend_uf_types context top_type_opt
..............
	)
      else
	( (* fun symb *)
	 match top_type_opt with 
	 |Some top_type -> 
	     UF_PNT.union context.uf top_type (create_pnt sym 0 v_type);	     
	 | None -> failwith "functions should not be at top"
	)

  |Term.Var (v,_) -> 
   let top_type = 
     match top_type_opt with 
     |Some top_type -> top_type 	    
     |None -> failwith "vars should not be at top" 
   in
   try 
     let v_type = VarTable.find context.vtable v in
     UF_PNT.union context.uf top_type v_type
   with 
     Not_found -> 
       VarTable.add context.vtable v top_type
*)

(*let typify_clause clause type_context =  
 
let typify_clause_list clause_list =*)

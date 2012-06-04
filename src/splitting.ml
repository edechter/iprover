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
type var    = Var.var
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol

let symb_db_ref  = Parser_types.symbol_db_ref
let term_db_ref  = Parser_types.term_db_ref
 

type split_result = 
    { 
      split_list : clause list;
      num_of_splits : int;
      num_of_split_atoms : int;
   }

let get_split_list         result = result.split_list
let get_num_of_splits      result = result.num_of_splits
let get_num_of_split_atoms result = result.num_of_split_atoms 


let empty_result () = 
  { split_list = []; 
    num_of_splits = 0; 
    num_of_split_atoms = 0 }

module LitListKey =
  struct
    type t       = lit list 
    let  compare l1 l2 = list_compare_lex Term.compare l1 l2 
 end

module SplitMap = Map.Make(LitListKey)

type split_map = (lit*lit) SplitMap.t
let create_split_map () = SplitMap.empty
let split_map_ref = ref (create_split_map ())

module VarHashKey = 
  struct
    type t    = var
    let equal = (==)
    let hash  = Var.hash
  end 


module VarHash = Hashtbl.Make(VarHashKey)


type lit_ext = 
    { elit : lit;
      evar_list : var list}

type part_entry =
    { mutable lit_list : lit list;
      mutable var_list : var list
    } 
 
(*we assume no ground in unprocessed *)
type partition = 
    { 
      mutable  current        :  part_entry param;
      mutable  unprocessed    :  lit_ext list;
      mutable  processed      :  (lit list) list
    }


exception All_var_tried
let rec get_next_var_to_check var_tried_hash var_list = 
  match var_list with 
  | v::tl -> 
      if (VarHash.mem var_tried_hash v)
      then get_next_var_to_check var_tried_hash tl
      else 
	(VarHash.add var_tried_hash v v; 
	 v)
  | [] -> raise All_var_tried


(* returns (lits,vars,new_unprocessed) where var occures in lits *)
(* and does not occur in new_unprocessed *)

let get_all_lits_vars var unprocessed = 
  let f rest lit_ext = 
    let (rest_lits,rest_vars,new_unprocessed) = rest in 
    if (List.mem var lit_ext.evar_list)
    then     
      (lit_ext.elit::rest_lits, 
       (List.rev_append lit_ext.evar_list rest_vars),
       new_unprocessed)
    else (rest_lits,rest_vars,lit_ext::new_unprocessed)
  in
  List.fold_left f ([],[],[]) unprocessed

let rec partition_lit_list var_tried_hash partition = 
  match partition.current with 
  |Def(part_entry) -> 
      (try
	(let var = get_next_var_to_check var_tried_hash part_entry.var_list in
	let (all_lits,all_vars,new_unprocessed) 
	  = get_all_lits_vars var partition.unprocessed in
	partition.current<-
	  Def({lit_list = (List.rev_append all_lits part_entry.lit_list);
	       var_list = (List.rev_append all_vars part_entry.var_list)});
	partition.unprocessed<-new_unprocessed;
	partition_lit_list var_tried_hash partition) 
      with 
	All_var_tried -> 
	  ( partition.processed <- (part_entry.lit_list)::(partition.processed);
	    partition.current<-Undef;
	    partition_lit_list var_tried_hash partition)
      )
  |Undef -> 
      match partition.unprocessed with 
      |[] -> partition.processed
      | lit_ext::tl ->
     	(partition.unprocessed<-tl;
	 partition.current <-
	   Def(
	   {lit_list = [lit_ext.elit];
	    var_list = lit_ext.evar_list
	  });
	 partition_lit_list var_tried_hash partition) 
	
(* was *)
(* C_1\/p_1;..C_n\/p_n; ~p_1\/..\/~p_n\/ground_lits *)

(* now *)
(* C_1\/~p_1;..C_n\/~p_n; p_1\/..\/p_n\/ground_lits *)

let ground_split_clause clause =

  let var_tried_hash = VarHash.create 23 in
  let all_lits = Clause.get_literals clause in
  let (ground_lits,non_ground_lits) = List.partition Term.is_ground all_lits in
  let unprocessed = 
    let f lit = {elit = lit; 
		 evar_list = fst (List.split (Term.get_var_list lit))} in
    List.map f non_ground_lits in
  let init_partition = 
    {
     current = Undef;
     unprocessed = unprocessed;
     processed   = [];
   } in
  let split_ground_lits = ref ground_lits in
  let split_clauses     = ref [] in
  let num_of_split_atoms = ref 0 in

  (* Record symbols introduced for splitting *)
  let split_symbols = ref [] in

  let processed = 
    partition_lit_list var_tried_hash init_partition in
  if 
    (
     (not (processed = []) &
      (not ((List.tl processed) = []))) || 
      ( not (processed = []) & not (ground_lits = []) &
	(not ((List.tl ground_lits) = [])))
) 
  then
    let create_split_clause_split_atom lit_list = 
      let norm_list = Clause.normalise_lit_list term_db_ref lit_list in
      (try 
	(let (split_atom,split_neg_atom) = SplitMap.find norm_list !split_map_ref in
	(*split_clauses:= (Clause.create (split_atom::norm_list))::(!split_clauses);*)
	(* split_ground_lits:=split_neg_atom::(!split_ground_lits))*)
      split_ground_lits:=split_atom::(!split_ground_lits))
      with 
	Not_found ->
	  (

	   let new_split_symb = 
	     SymbolDB.create_new_split_symb 
	       symb_db_ref 
	       (Symbol.create_stype [] Symbol.symb_bool_type) 
	   in
	   
	   num_of_split_atoms := !num_of_split_atoms+1;
	   split_symbols := new_split_symb :: !split_symbols;
	   
	   let split_atom = 
	     TermDB.add_ref (Term.create_fun_term new_split_symb []) term_db_ref in
	   let split_neg_atom = 
	     TermDB.add_ref (Term.create_fun_term Symbol.symb_neg [split_atom]) term_db_ref in
	   split_map_ref := 
	     SplitMap.add norm_list (split_atom,split_neg_atom) !split_map_ref;
(*	 split_clauses:= (Clause.create (split_atom::norm_list))::(!split_clauses);
	 split_ground_lits:=split_neg_atom::(!split_ground_lits)
*)
	   let split_clause = (Clause.create (split_neg_atom::norm_list)) in
	   Clause.inherit_param_modif clause split_clause;
	   (* Clause.assign_split_history split_clause clause; *)

	   (* Clause was split with a fresh splitting symbol introduced *)
	   Clause.assign_tstp_source_split 
	     [new_split_symb] 
	     split_clause 
	     clause;

	   split_clauses:= split_clause::(!split_clauses);
	   split_ground_lits:=split_atom::(!split_ground_lits)
	  )
      )
    in
    List.iter create_split_clause_split_atom processed;
    let ground_clause =  Clause.create !split_ground_lits in
    Clause.inherit_param_modif clause ground_clause;
    (* Clause.assign_split_history ground_clause clause; *)

    (* Clause was split with fresh splitting symbols introduced *)
    Clause.assign_tstp_source_split 
      !split_symbols
      ground_clause 
      clause; 

    let split_final_list = ground_clause::(!split_clauses) in
    let result ={
      split_list          = split_final_list;
      num_of_splits       = (List.length !split_clauses);
      num_of_split_atoms  = !num_of_split_atoms;
    }in
    result 
  else 
    let result ={
      split_list          = [clause];
      num_of_splits       = 0;
      num_of_split_atoms  = 0;
    }in
    result 
      

let ground_split_clause_list clause_list = 
  let init_result = empty_result ()in
  let f rest clause = 
(*    out_str ("Clause to Split: "^(Clause.to_string clause)^"\n");*)
    let clause_split_result = 
      ground_split_clause clause in
(*    out_str ("Clauses After Split: \n"
	     ^(Clause.clause_list_to_string clause_split_result.split_list)^"\n");*)
    let result =
      {split_list = List.rev_append clause_split_result.split_list rest.split_list;
       num_of_splits = clause_split_result.num_of_splits + rest.num_of_splits;
       num_of_split_atoms  = 
       clause_split_result.num_of_split_atoms + rest.num_of_split_atoms;
     } in result
  in 
  List.fold_left f init_result clause_list 
  

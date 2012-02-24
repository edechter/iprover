(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2012 The University of Manchester. 
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
open Statistics

type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol  

let symbol_db_ref  = Parser_types.symbol_db_ref
let term_db_ref    = Parser_types.term_db_ref


(*-------------------------------*)
type filter_clause = 
    {orig_clause : clause;
(* order literals first in the order of preferred selection *)
(* e.g. negative/positive/ground first     *)

(* if filter_clause is in the watch index then first literal in lits_to_try*)
(* is the watched literal  *)                 
     mutable lits_to_try : lit list; 
   }

module DTParam = 
  struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end 

module DiscrTreeM = DiscrTree.Make(DTParam)  

(* all clauses with the same literal put together, *)
(*   assoc list with == *)

(* we use non-perfect unification index without going into full unification *)
type watch_unif_index_elem = (filter_clause list)

(*
let (unif_index_ref : (unif_index_elem DiscrTreeM.index) ref ) 
    = ref (DiscrTreeM.create ())
 *)

type dummy = Dummy

type filter_state = 
    {
(* intially all clauses unprocessed *)
     mutable unprocessed_fclauses : filter_clause list;

(* clauses that are kept after the filter *)
     mutable filtered_in_clauses : clause list;
     
(*  atom_unif_index contains atoms for which interpretation can not be established *)
     mutable atom_unif_index  : (watch_unif_index_elem DiscrTreeM.index);

(* watch_unif_index: indexes lists of clauses  by watch literals that *)
(* prospectively can be defined true in any extension *)
(* of any model of filtered_in_clauses *)

     mutable watch_unif_index : (watch_unif_index_elem DiscrTreeM.index);
   }

let clause_to_fclause order_lit_fun clause = 
  {
   orig_clause = clause;
(* order in decreasing order therefore we compose_sign with false *)
   lits_to_try = List.sort (compose_sign false order_lit_fun) (Clause.get_literals clause);
 }


let init_filter_state clause_list order_lit_fun = 
  {
   unprocessed_fclauses = 
   List.map (clause_to_fclause order_lit_fun) clause_list;

   filtered_in_clauses    = [];

   atom_unif_index     = (DiscrTreeM.create ());
   watch_unif_index    = (DiscrTreeM.create ());
 }

(* lit is unifiable with the element in the index*)
let is_unif unif_index lit =
  (DiscrTreeM.unif_cand_exists unif_index lit)



(* find_watch_lit raise Not_found if no watch_symb found *)  

let rec find_watch_lit filter_state fclause =
(*  out_str ("\n Find watch: "^(Clause.to_string fclause.orig_clause)^"\n");*)
  match fclause.lits_to_try with
  |[] -> raise Not_found
  |h::tl -> 
     (* fclause.lits_to_try <- tl;*)

(*      let atom = Term.get_atom h in       *)

      let compl_h = (Term.compl_lit h) in     
(*      
      out_str 
	(
	 " clause: "^(Clause.to_string fclause.orig_clause)
	 ^" to try "^(Term.term_list_to_string fclause.lits_to_try) 
	 ^" Compl_h: "^(Term.to_string compl_h)^" unif watch ind: "
	 ^(string_of_bool (is_unif filter_state.watch_unif_index compl_h))
	 ^" unif cand: "
	 ^(Clause.clause_list_to_string 
	     (List.map (fun fcl -> fcl.orig_clause)
		(DiscrTreeM.unif_candidates 
		   filter_state.watch_unif_index compl_h))^"\n"));
*)
      if 
	(* check that the atom is not unif with  atom_unif_index; now moved up front *)
(*	(not (is_unif filter_state.atom_unif_index atom))
	  &&*)
	(* check that the complement of the lit  is not unif with  watch_unif_index *)
        (not (is_unif filter_state.watch_unif_index compl_h))
      then 
	h
      else
	(
	 fclause.lits_to_try <- tl;
	 find_watch_lit filter_state fclause
	)
	  
let add_to_watch filter_state watch_lit fclause = 
  let ind_ref = ref filter_state.watch_unif_index in
  let ind_elem = DiscrTreeM.add_term_path watch_lit ind_ref in
  filter_state.watch_unif_index <- !ind_ref;
  (match !ind_elem with 
  |Elem(old) -> 
      (
(*       out_str ("\n Added to watch lit: "
		^(Term.to_string watch_lit)^" clause: "
		^(Clause.to_string fclause.orig_clause)^"\n");
*)
       ind_elem:= Elem (fclause::old)
      )
  |Empty_Elem   -> 	       
      (
(*      out_str ("\n Added to watch new lit: "
		^(Term.to_string watch_lit)^" clause: "
		^(Clause.to_string fclause.orig_clause)^"\n");
  *)     
       ind_elem := Elem([fclause])
      )
  )     

let get_watched_list_fclause fclause = 
  (* we assume that fclause is in the  filter_state.watch_unif_index *)
  (* therefore first lit in fclause.list_to_try is watched *)
  match fclause.lits_to_try 
  with
  |h::tl -> (h,tl)
  |[] -> failwith "get_watched_list_fclause: list should not be empty"


(*---------------------------*)
(*move_from_watch_to_unprocessed: assumes that fclause is in filter_state.watch_unif_index *)
let move_from_watch_to_unprocessed filter_state fclause =
 let (w_lit,tl) = get_watched_list_fclause fclause in
(* out_str ("\n Remove from watch:"^(Term.to_string w_lit)^"\n");*)
 (* we assume that all clauses for removal are already collected *)
 let ind_ref = ref filter_state.watch_unif_index in
 (try 
   (DiscrTreeM.remove_term_path w_lit ind_ref;
   filter_state.watch_unif_index <- !ind_ref;
   )
 with (* could be removed when removing other w_lits *)
   DiscrTree.Not_in_discr_tree -> ()
 ); 
(* w_lit does not need to be tried again since *)
(* atom(lit) will be in filter_state.atom_unif_index *)
 fclause.lits_to_try <- tl;
(* add fclause to unprocessed *)
(* out_str ("\n Added to unprocessed: "^(Clause.to_string fclause.orig_clause)^"\n");*)
 filter_state.unprocessed_fclauses <- fclause::(filter_state.unprocessed_fclauses)
			

(*---------------------------*)

let no_watch_found filter_state fclause = 
  let lits = Clause.get_literals fclause.orig_clause in
  let compl_lits = List.map Term.compl_lit lits in
  let atoms = List.map Term.get_atom lits in
  (* move fclauses from watched to unprocessed *)
  let remove_unif_from_watch lit = 
    let fclause_list = 
      DiscrTreeM.unif_candidates filter_state.watch_unif_index lit in 
    List.iter (move_from_watch_to_unprocessed filter_state) fclause_list      
  in
  List.iter remove_unif_from_watch compl_lits;
(* add atoms to filter_state.atom_unif_index *)
  let add_to_atom_unif_index atom = 
    let ind_ref = ref filter_state.atom_unif_index in
    ignore (DiscrTreeM.add_term_path atom ind_ref);
    filter_state.atom_unif_index <- !ind_ref;
  in
  List.iter add_to_atom_unif_index atoms;
  filter_state.filtered_in_clauses <- 
    (fclause.orig_clause)::(filter_state.filtered_in_clauses)

(*---------------------------*)

let rec find_movable_watch filter_state fclause = 
  match fclause.lits_to_try with
  |[] -> raise Not_found
  |h::tl -> 
      let compl_h = (Term.compl_lit h) in     
      let fclause_list = 
	DiscrTreeM.unif_candidates filter_state.watch_unif_index compl_h in 
      (* we cannot move further in this clause *)
      let is_not_movable fc = 
	match fc.lits_to_try with 
	|_h::[] -> true 
	| [] -> true 
	|_-> false
      in
      if (List.exists is_not_movable fclause_list) 
      then
	(fclause.lits_to_try <-tl;
	 find_movable_watch filter_state fclause)
      else
	(h,fclause_list)



let process_given filter_state fclause = 
  let lits_to_try_not_in_unif = 
    List.filter 
      (fun l -> 
	let atom = Term.get_atom l in
	(not (is_unif filter_state.atom_unif_index atom))	
      )  fclause.lits_to_try in
  fclause.lits_to_try <- lits_to_try_not_in_unif;
  let old_lits_to_try  = fclause.lits_to_try in
  (try 
    let watch_lit = find_watch_lit filter_state fclause in 
(*	  out_str ("\n Found watch: "^(Term.to_string watch_lit)^" : "^(Clause.to_string fclause.orig_clause)^"\n");*)
    (add_to_watch filter_state watch_lit fclause)
  with
    Not_found -> 
      (
(*  out_str ("\n Not Found watch: "^(Clause.to_string fclause.orig_clause)^"\n");*)
       fclause.lits_to_try <- old_lits_to_try;
       try 
	let (lit, fclause_list) = (find_movable_watch filter_state fclause) in
(* move_from_watch_to_unprocessed it also moves in lits_to_try by one lit *)
	List.iter (move_from_watch_to_unprocessed filter_state) fclause_list;
	
(* add fclause to unprocessed; do not need to move in lits_to_try *)
	filter_state.unprocessed_fclauses <- 
	  fclause::(filter_state.unprocessed_fclauses)    
       with 
	 Not_found ->
	   (no_watch_found filter_state fclause; )
      )
  )
  

let rec filter_clauses filter_state = 
  match filter_state.unprocessed_fclauses with 
  |[] ->  filter_state.filtered_in_clauses
  |fclause::tl -> 
      begin
	filter_state.unprocessed_fclauses <- tl;	
	process_given filter_state fclause ;
	filter_clauses filter_state    
      end


let neg_order_fun_1 () =  
  Term.lit_cmp_type_list_to_lex_fun 
    [Lit_Sign false; Lit_Ground true]

let neg_order_fun_2 () =  
  Term.lit_cmp_type_list_to_lex_fun 
    [Lit_Sign false;  Lit_Num_of_Symb(true); Lit_Num_of_Var (false)]


let pos_order_fun_1 () = 
  Term.lit_cmp_type_list_to_lex_fun 
    [Lit_Sign true;  Lit_Ground true]

let pos_order_fun_2 () = 
  Term.lit_cmp_type_list_to_lex_fun 
    [Lit_Sign true; Lit_Num_of_Symb(true); Lit_Num_of_Var (false)]





let sem_filter_unif_order order_fun clause_list = 
  let time_before = Unix.gettimeofday () in       	
  let filter_state = init_filter_state clause_list order_fun in

  ignore(filter_clauses filter_state);

  let time_after = Unix.gettimeofday () in 
  add_float_stat (time_after-.time_before) sem_filter_time;
  let num_of_filtered_out =
    (List.length clause_list) - (List.length filter_state.filtered_in_clauses) in
(*  out_str ("Num of : num_of_filtered_out "^(string_of_int num_of_filtered_out));*)
  incr_int_stat num_of_filtered_out num_of_sem_filtered_clauses;
  filter_state.filtered_in_clauses
 
(* when clauses are not in db length is not defined, may change this later *)
let cmp_clause_length c1 c2 = 
  (compare 
     (List.length (Clause.get_literals c1)) 
     (List.length (Clause.get_literals c2)) )

let cmp_clause_length_compl c1 c2 = -cmp_clause_length c1 c2
    


let sem_filter_unif clause_list = 
  match !current_options.prep_sem_filter with
  | Sem_Filter_None -> clause_list
  | Sem_Filter_Pos -> 
      sem_filter_unif_order 
	(pos_order_fun_1 ()) 
	clause_list
  | Sem_Filter_Neg -> sem_filter_unif_order (neg_order_fun_1 ()) clause_list
  | Sem_Filter_Exhaustive 
    -> 
      begin
	let changed = ref true in
	let current_clauses = ref clause_list in
(*	let current_clauses = ref (List.sort cmp_clause_length  clause_list) in*)
	let order_fun_list = [(neg_order_fun_1 ());(pos_order_fun_1 ());(pos_order_fun_2 ());(neg_order_fun_2 ())] in
	while !changed 
	do
	  let num_of_sem_filtered_clauses_before = num_of_sem_filtered_clauses in
	  let f order_fun  = 
	 (*   current_clauses := (List.sort cmp_clause_length  !current_clauses);*)
	    current_clauses := sem_filter_unif_order order_fun !current_clauses;
	  in	  
	  List.iter f order_fun_list;
	  let num_of_sem_filtered_clauses_after = num_of_sem_filtered_clauses in
	  changed := 
	    (num_of_sem_filtered_clauses_before != num_of_sem_filtered_clauses_after)
	done;
	!current_clauses
      end 



(*
(*--junk------------*)




let rec filter_clauses filter_state = 
  match filter_state.unprocessed_clauses with 
  |[] ->  filter_state.filtered_clauses
  |clause::tl ->
      (try 
	let watch_symb = find_watch_symb filter_state clause in 
	add_to_watch filter_state watch_symb clause;
      with
	Not_found -> 
	  (
	   add_preds_to_undef_list filter_state clause;
	   filter_state.filtered_clauses<-clause::filter_state.filtered_clauses;
	   )
      );
      filter_state.unprocessed_clauses <- tl;
      process_undef_preds filter_state
and
    process_undef_preds filter_state =
  match filter_state.undef_pred_queue with 
  |[] -> filter_clauses filter_state
  |symb::tl -> 
      (try
	let watch_clause_list_ref =
	  SymbHash.find filter_state.watch_symbol_table symb in
	filter_state.unprocessed_clauses <- 
	  (!watch_clause_list_ref)@filter_state.unprocessed_clauses;
	SymbHash.remove filter_state.watch_symbol_table symb		      
      with 
	Not_found -> ()
      );
      filter_state.undef_pred_queue <- tl;
      filter_state.undef_pred_set <-
	(SymbSet.add symb filter_state.undef_pred_set);
      process_undef_preds filter_state




(*-----junk *)

   let ind_elem = DiscrTreeM.add_term_path sel_lit unif_index_ref in
    (match !ind_elem with 
    |Elem(old) -> 
	(try
	  let old_clause_list =  List.assq sel_lit old in 
	  let old_with_removed = List.remove_assq sel_lit old in
	  ind_elem := 
	    Elem((sel_lit,(main_clause::old_clause_list))::old_with_removed)
	  with Not_found ->  ind_elem := Elem((sel_lit,[main_clause])::old)
	)	     
    |Empty_Elem   -> 	 
	ind_elem := Elem([(sel_lit,[main_clause])])
    );     


*)

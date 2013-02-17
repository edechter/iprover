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
open Statistics

let proof = false 
    
type clause  = Clause.clause
type lit     = Term.literal
type term    = Term.term
type symbol  = Symbol.symbol  
type tmp     = bool
(*type prop_var = PropSolver.var *)
type prop_lit = PropSolver.lit

(* at the moment model will be represented as the set of all clauses *)
type all_clauses = ClauseAssignDB.clauseDB

(*--------------------------------*)
exception Unsatisfiable

exception Satisfiable of all_clauses

exception DontKnow
(*--------------------------------*)

(*
(*----------------------------------------------------*)
let model_to_stream s model = 
  let f clause = 
    if not (Clause.get_bool_param Clause.in_active clause)
    then ()
    else
      begin
	s.stream_add_str "%---------------\n";
	Clause.to_stream s clause;
	s.stream_add_char ' ';
	Term.to_stream s (Clause.get_inst_sel_lit clause);
	s.stream_add_char '\n';
	(try 	
	  Dismatching.to_stream_constr_set s (Clause.get_dismatching clause);
	  s.stream_add_char '\n';
	with 
	  Clause.Dismatching_undef ->
	    s.stream_add_str "[]\n");
	
      end
  in
  ClauseAssignDB.iter f model;
  s.stream_add_str "\n%---------------End Model--------------\n\n"


let out_model model = 
  model_to_stream stdout_stream model
*)

(*
 
     let dismatching_str = 
	try 
	 Dismatching.constr_list_to_string (Clause.get_dismatching clause)      
	with 
	  Clause.Dismatching_undef ->
	    "[]\n"
      in
      out_str 
	(
	 (Clause.to_string clause)^" "
	 ^(Term.to_string (Clause.get_inst_sel_lit clause))^"\n"
	 ^dismatching_str)
(*	 ^"\n%---------------\n")	 *)
    else
      ()
  in
  out_str "\n%----------------Model-----------------\n\n";
  ClauseAssignDB.iter f model;
  out_str "\n%---------------End Model--------------\n\n"    
*)	



(*----------------------------------------------------*)
module type InputM = 
  sig
    val inst_module_name : string
(* we assume that input clauses are normalised with terms in *)
(* Parsed_input_to_db.term_db_ref *)
(* clauses are copied, but terms are not some paremters of terms such as *)
(* inst_in_unif_index can be changed *)
(* one should run clear_all () which also clears term parameters *)
    val input_clauses    : clause list
  end

module Make (InputM:InputM) = 
  struct
    let inst_module_name = InputM.inst_module_name
    let input_clauses    = InputM.input_clauses

(*inst_clear_all also clears all statistics related to inst. *)
(* we need to preserve learning restarts *)

    let _ =
      let stat_learning_restarts = 
	get_val_stat inst_num_of_learning_restarts 
      in
      clear_inst_stat ();
      assign_int_stat stat_learning_restarts inst_num_of_learning_restarts
      

    let symbol_db_ref  = Parser_types.symbol_db_ref
    let term_db_ref    = Parser_types.term_db_ref

    let clause_db_ref = ref (ClauseAssignDB.create_name "Instantiation_Clauses_DB")
    let ()= assign_fun_stat 
	(fun () -> (ClauseAssignDB.size !clause_db_ref)) inst_num_of_clauses
   
(* 
    let selection_fun = 
    let selection_fun_ref = ref (Selection.inst_lit_sel)    
*)

(* TO DO add this to options *)

(* start applying simplification only after this number of learning resturts*)
(*let start_simpl_after_learn = 0*)
(*let start_prop_simpl_after_learn = 2*)
(*let inst_solver_threshold   = ref 100*)
let inst_solver_threshold   = ref 1
    
(*let init_clause_list_ref = Parsed_input_to_db.clause_list_ref*)

(* simple passive is just a list and *)
(* only is used in the instantiation_exhaustive_loop*)
(*  *)
    
let simple_passive_ref = ref []

(* unprocessed is a list of newly generated clauses *)
(* we cannot put them to passive since some truth val of some var *)
(* can be not defined at this stage *)

let unprocessed_ref    = ref []    



(*------------ unprocessed --------------------*)

let add_clause_to_unprocessed clause = 
  unprocessed_ref:=clause::!unprocessed_ref;
  incr_int_stat 1 inst_num_in_unprocessed
			     
(*-------------- simple passive ---------------*)

exception Passive_Simple_Empty 
let remove_from_simple_passive () = 
  match !simple_passive_ref with 
  | clause::tl -> 
      simple_passive_ref := tl;
      Clause.set_bool_param false Clause.inst_in_sim_passive clause;
      incr_int_stat 1 inst_num_in_simple_passive;
      clause
  |[]     -> raise Passive_Simple_Empty 
	
let add_to_simple_passive clause = 
  simple_passive_ref := clause::!simple_passive_ref;
  incr_int_stat 1 inst_num_in_simple_passive;
  Clause.set_bool_param true Clause.inst_in_sim_passive clause (*;*)
(*  Clause.assign_when_born (get_val_stat inst_num_of_loops) clause*)

(*add new clauses*)    
let add_new_clause_to_sp clause = 
  if (Clause.is_empty_clause clause) 
  then
    ( (* Format.eprintf "Added empty clause to simple passive in instantiation@."; *)
    raise Unsatisfiable)
  else 
    if (not (Clause.get_bool_param Clause.is_dead clause))  
    then 
	  add_to_simple_passive clause 
    else ()


(*-------------------- end simple passive-----------------------------*)


(*--------------------Imperative Passive QUEUES-----------------*)


(* total comparison  for clauses!----*)
(* Heap.ImperativeEq does not work yet..... *)

(* Creating an n-ary priority queue *)

(* A module for the type of elements in the queue *)
module Elem0 = 
struct 
  type t = clause 
end 

(* Create a module for n-ary priority queues of clauses *)
module PassiveQueue = Priority_queues.QueueN(Elem0)

(* TODO: make this generic, that is, modify options to pass an
   aritrary number of priority queues and then create these modules at
   runtime *)

(* Create a Priority_queues.ElemN module *)
let create_elem compare in_queue assign_in_queue mult = 

  (* Create a module from given parameters *)
  let module ElemN = 
      struct
	type t = clause 
	let compare = compare 
	let in_queue = in_queue 
	let assign_in_queue = assign_in_queue 
	let mult = mult 
      end
  in
  
  (* Return module *)
  (module ElemN : Priority_queues.ElemN with type t = clause) 
    

(* Initial capacity of a passive queue *)
let init_capacity_priority = 10001



(* Create a passive queue 

   TODO: make this generic, that is, modify options and clause
   parameters to define an aritrary number of priority queues *)
let create_passive_queue init_capacity =
  (PassiveQueue.create 
     
     (* Initial capacity of each queue *)
     init_capacity
     
     (* A list of ElemN modules *)
     [

       (* First passive queue *)
       create_elem 
	 (fun c1 c2 -> 
	   Clause.cl_cmp_type_list_to_lex_fun
	     (val_of_override !current_options.inst_pass_queue1)
	     c1
	     c2)
	 (fun c -> 
	   Clause.get_bool_param Clause.inst_pass_queue1 c)
	 (fun b c -> 
	   Clause.set_bool_param b Clause.inst_pass_queue1 c)
	 (val_of_override !current_options.inst_pass_queue1_mult);
       
       (* Second passive queue *)
       create_elem 
	 (fun c1 c2 -> 
	   Clause.cl_cmp_type_list_to_lex_fun
	     (val_of_override !current_options.inst_pass_queue2)
	     c1
	     c2)
	 (fun c -> 
	   Clause.get_bool_param Clause.inst_pass_queue2 c)
	 (fun b c -> 
	   Clause.set_bool_param b Clause.inst_pass_queue2 c)
	 (val_of_override !current_options.inst_pass_queue2_mult);
	 
       (* Third passive queue, use mult = 0 to deactivate a queue *)
       create_elem 
	 (fun c1 c2 -> 
	   Clause.cl_cmp_type_list_to_lex_fun
	     (val_of_override !current_options.inst_pass_queue3)
	     c1
	     c2)
	 (fun c -> 
	   Clause.get_bool_param Clause.inst_pass_queue3 c)
	 (fun b c -> 
	   Clause.set_bool_param b Clause.inst_pass_queue3 c)
	 (val_of_override !current_options.inst_pass_queue3_mult)
	 
     ])
    
    

let passive_queue_ref = ref (create_passive_queue init_capacity_priority)
	     

(*
module Elem = 
struct
  type t = clause 

  let compare1  = (Clause.cl_cmp_type_list_to_lex_fun 
		     !current_options.inst_pass_queue1)
  let in_queue1 = Clause.get_bool_param Clause.inst_pass_queue1 
  let assign_in_queue1 b c = 
    Clause.set_bool_param b Clause.inst_pass_queue1 c
  let mult1    = !current_options.inst_pass_queue1_mult

  let compare2  = (Clause.cl_cmp_type_list_to_lex_fun 
		     !current_options.inst_pass_queue2)
  let in_queue2 = Clause.get_bool_param Clause.inst_pass_queue2 
  let assign_in_queue2 b c = 
    Clause.set_bool_param b Clause.inst_pass_queue2 c
  let mult2    = !current_options.inst_pass_queue2_mult

end

let init_capacity_priority = 10001

module  PassiveQueue = Priority_queues.Queue2(Elem)

let passive_queue_ref = ref (PassiveQueue.create init_capacity_priority)

*)


let () = assign_fun_stat 
  (fun () -> PassiveQueue.num_elem !passive_queue_ref) 
  inst_num_in_passive

(* if we find that passive queue is empty then we need to clean it: *)
(* (done by PassiveQueue.clean) *)
(* 1. assign in_queue param to false in all clauses in the remaining queue*)
(* 2. release memory and assign new queues *)

let clean_passive () = 
  PassiveQueue.clean init_capacity_priority !passive_queue_ref
(*  passive_queue_ref:=(PassiveQueue.create init_capacity_priority*)


let add_to_passive clause =    	     
  if(Clause.get_bool_param Clause.is_dead clause)
  then ()
  else
    PassiveQueue.add_all !passive_queue_ref clause

exception Passive_Empty 
let rec remove_from_passive () = 
  try 
    let clause = PassiveQueue.remove !passive_queue_ref in
      if ((Clause.get_bool_param Clause.in_active clause) || 
      (Clause.get_bool_param Clause.is_dead clause)) 
      then 
	(remove_from_passive ())
      else	
	clause
  with PassiveQueue.Empty -> 
    (clean_passive ();
     raise Passive_Empty)


(* change empty clause check  to unprocessed*)
let add_new_clause_to_passive clause = 
  if (Clause.is_empty_clause clause) 
  then
    ( (* Format.eprintf "Added empty clause to passive in instantiation@."; *)
    raise Unsatisfiable)
  else 
    if (not (Clause.get_bool_param Clause.is_dead clause))  
    then 
	  add_to_passive clause 
    else ()

(*--------------------End Imperative Passive QUEUES-----------------*)




(*----------------- unification index -------------------------*)

module DTParam = 
  struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end 
module DiscrTreeM = DiscrTree.Make(DTParam)  

(* all clauses with the same literal put together, *)
(*   assoc list with == *)

type unif_index_elem = (lit*(clause list)) list

let (unif_index_ref : (unif_index_elem DiscrTreeM.index) ref ) 
    = ref (DiscrTreeM.create ())
    
(* add to unif index *)
      
let add_to_unif_index main_clause =
  try
    let sel_lit = Clause.get_inst_sel_lit main_clause in
    Term.set_fun_bool_param true  Term.inst_in_unif_index sel_lit;
    (Clause.set_bool_param true Clause.in_active main_clause); 
(*    out_str ("Add to Unif Index: Clause: "^(Clause.to_string main_clause)); *)
(*    out_str ("Add to Unif  literal:  "^(Term.to_string sel_lit)
	     ^"restarts: "^(string_of_int !num_of_learning_restarts)^"\n"); *)
(* debug check that if add not t then t is not in the index*)
(*    ( if (Term.is_neg_lit sel_lit) 
    then 
      let atom = Term.get_atom sel_lit in
      try 
	let ind_elem = DiscrTreeM.find atom !unif_index_ref in
	out_str ("Compl. Lit is in Unif! Lit: "^(Term.to_string sel_lit)
		 ^" Compl: "^(Term.to_string atom));
      with Not_found -> 
	( 
	  out_str ("Compl. Lit is NOT in Unif! (ok) Lit: "^(Term.to_string sel_lit)
		 ^" Compl: "^(Term.to_string atom));
	)
    else ()
     );*)
(*end debug*)
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
    Clause.set_bool_param true Clause.in_unif_index main_clause
  with
    Clause.Inst_sel_lit_undef -> 
      failwith "add_to_unif_index: clause should have selected literals here"



(*--------------------------------*)

let eliminate_from_unif_index main_clause = 
  try
    let sel_lit = Clause.get_inst_sel_lit main_clause in
 (*   Term.set_fun_bool_param false  Term.in_unif_index sel_lit;*) (*see below*)
(*    out_str ("Remove from Unif cl literal:  "^(Term.to_string sel_lit)
	   ^"restarts: "^(string_of_int !num_of_learning_restarts)^"\n"); *)
(*    out_str
      ("Trying to elim from Unif index:"
      ^(Clause.to_string main_clause)
      ^" Literals: "
      ^(Term.to_string sel_lit)^"\n"); *)

    (try  
      let ind_elem = DiscrTreeM.find sel_lit !unif_index_ref
	(* failwith "discount:  eliminate_from_unif_index lit is in unif_index" *)
      in
      ( match !ind_elem with 
      |Elem(old) ->
	  ( (* old = [(L1,[C_1,..,Cn]),(L2,[C'_1,..,C'n']),..]  
	       old_clause_list = [C_1,..,Cn] corr to sel_lit*)
	    (*  try *) 
	    let old_clause_list  = List.assq sel_lit old in 
            (*  out_str_debug 
		("Elem From Unif index old_cl_list:"
		^(Clause.clause_list_to_string old_clause_list)^"\n"); *)   
	    let old_with_removed = List.remove_assq sel_lit old in
	    
(*remove main_clause*)     
	    let new_clause_list = 
	      List.find_all (fun cl -> not(cl == main_clause)) old_clause_list in
	    (* out_str_debug 
	       ("Elem From Unif index new_cl_list:"
	       ^(Clause.clause_list_to_string new_clause_list)^"\n"); *)
            if new_clause_list = [] 
	    then 
	      (Term.set_fun_bool_param false  Term.inst_in_unif_index sel_lit;
 	       if  old_with_removed = []
	       then
		 (DiscrTreeM.remove_term_path sel_lit unif_index_ref
                    (*; out_str_debug 
		      ("Elim unif Removed term path"
		      ^(Term.to_string sel_lit)^"\n")*))
	      else 
		 (ind_elem := Elem(old_with_removed)
                     (*; out_str_debug 
		       ("Elim unif: Old_with_removed")*))
	      )
	    else 	    
	      (ind_elem := 
		Elem((sel_lit,new_clause_list)::old_with_removed)
		  (*;out_str_debug 
		    ("Elim unif: Old_with_removed")*) )		
		(*with *)
		(*  Not_found -> ()*)
	   )
    | Empty_Elem -> 
	  failwith "instantiation: eliminate_from_unif_index  \
	    unif index should not contain Empty_Elem"  
       )     
    with
      Not_found -> 
	out_str 
      ("\n Warning: eliminate_from_unif_index: the clause in not in the index!\n ")
  ); 
    Clause.set_bool_param  
      false Clause.in_unif_index main_clause 
  with 
    Clause.Inst_sel_lit_undef -> 
      failwith "eliminate_from_unif_index: Clause.Sel_lits_undef "
	

(* eliminates all clauses indexed by lit from unif_index and returns*)
(* the eliminated clause list   *)

let eliminate_lit_from_unif_index lit = 
(*  eliminated literals can be different form lit!!! lit\bot = lit_elim\bot *)
(*  Term.set_fun_bool_param false  Term.in_unif_index lit;*)
(*  out_str ("Remove from Unif literal:  "^(Term.to_string lit)
	   ^"restarts: "^(string_of_int !num_of_learning_restarts)^"\n"); *)

(*    out_str
      ("Trying to elim from Unif index:"
      ^" Literal: "
      ^(Term.to_string lit)^"\n"); *)

  let  ind_elem = DiscrTreeM.remove_term_path_ret lit unif_index_ref in
  match !ind_elem with 
  | Elem(elem) ->
   (* elem = [(L1,[C_1,..,Cn]),(L2,[C'_1,..,C'n']),..] *)  
      (* elem_clause_list = [C_1,..,Cn] corr to sel_lit*)
      let elem_f rest (lit,cl_list) = 
	Term.set_fun_bool_param false  Term.inst_in_unif_index lit;
	let add_cl rest' clause = 
	  (Clause.set_bool_param  
	     false Clause.in_unif_index clause;
	   clause::rest')
	in
	List.fold_left add_cl rest cl_list 
      in 
      List.fold_left elem_f [] elem
  | Empty_Elem -> 
      failwith "instantiation: eliminate_lit_from_unif_index  \
	unif index should not contain Empty_Elem"  


(*---------------end  unification index -------------------*)

(*---------------end simplification--------------------*)
(*
let dismatching_string clause = 
  try 
   "["^(Dismatching.constr_list_to_string (Clause.get_dismatching clause))^"]"
  with
    Clause.Dismatching_undef -> "[]"
*)



let add_to_active clause = 
  if 
    ((not (Clause.get_bool_param Clause.in_active clause)) 
   || 
    (not (Clause.get_bool_param Clause.is_dead clause)))
   then
    (Clause.set_bool_param true Clause.in_active clause;
     add_to_unif_index clause;
    (* out_str ("Add to Active: "^(Clause.to_string clause));*)
    incr_int_stat 1 inst_num_in_active;
    )
  else ()

let remove_from_active clause =
  if (Clause.get_bool_param Clause.in_active clause) 
  then 
    (eliminate_from_unif_index clause;
     Clause.set_bool_param false Clause.in_active clause;
(*     out_str ("\n Remove from Active: "^(Clause.to_string clause));*)
(*     out_str ("Sel lit: "^(Term.to_string (Clause.get_sel_lits)))*)
     incr_int_stat (-1) inst_num_in_active
    )
  else ()

let remove_lit_from_active lit =
(*  out_str ("\n Remove Lit: "^(Term.to_string lit));*)
  let cl_list = eliminate_lit_from_unif_index lit in
  let set_param clause = 
(*    out_str ("\n Remove from Active: "^(Clause.to_string clause));*)
    Clause.set_bool_param false Clause.in_active clause;
    incr_int_stat (-1) inst_num_in_active
(*    out_str ("Removed from Unif: "^(Clause.to_string clause))*)
  in
  List.iter set_param cl_list;
  cl_list



(* simple passive version old*)
let move_from_active_to_sp clause = 
  remove_from_active clause; 
  add_to_simple_passive clause;
  incr_int_stat 1 inst_num_moves_active_passive

let move_from_active_to_passive clause = 
  remove_from_active clause; 
 (* add_clause_to_unprocessed clause;*)
(*  out_str ("move_from_active_to_passive: "^(Clause.to_string clause)^"\n");*)
  ((*if (not (in_passive clause)) then*)
(* should not change when_born ! since it can be age priority queue *)
(* which would destroy integrety of the queue*)
    ((*Clause.assign_when_born !num_of_instantiation_loops clause;*)
     add_to_passive clause)
 (* else num_in_passive := !num_in_passive+1*)
  );  
  incr_int_stat 1 inst_num_moves_active_passive



(*  moves all clauses from univ index which are indexed *)
(* by the same literal *)


let move_lit_from_active_to_passive  lit = 
    let cl_list = remove_lit_from_active lit in
(*    out_str ("Move lit form act to pass: "^(Term.to_string lit)^"\n");*)
    let to_pass clause = 
  
 (*   add_clause_to_unprocessed clause;*)
(*    Clause.assign_when_born (!num_of_instantiation_loops+2) clause;*)
(*debug*)
(*      out_str ("\n Act_to_Pass: "^(Clause.to_string clause)^"\n");*)
(*      let sel_lit = Clause.get_inst_sel_lit clause in
      let var_entry   = get_prop_gr_var_entry sel_lit in
      out_str ("Lit: "^(Term.to_string sel_lit)^"\n"
	       ^"Var entry:"^(var_entry_to_string solver var_entry)^"\n");*)
      ((*if (not (in_passive clause)) then*)
	((*Clause.assign_when_born !num_of_instantiation_loops clause;*)
	(* out_str ("\n Act_to_Pass: "^(Clause.to_string clause)^"\n");*)
	 add_to_passive clause)
      (*else num_in_passive := !num_in_passive+1*)
      );
      incr_int_stat 1 inst_num_moves_active_passive
    in
    List.iter to_pass cl_list

    

(*------------- Simplification -------------------*) 


	    


(*let () = out_str "Debug: child elimination swithced off"*)
let rec eliminate_clause clause = 
(* out_str ("\n Eliminate Clause:"^(Clause.to_string clause)^"\n");*)
  remove_from_active clause;
  Clause.set_bool_param true Clause.is_dead clause;
  incr_int_stat 1 inst_num_child_elim;
  List.iter eliminate_clause (Clause.get_children clause)



exception Simplified_exists

let prop_subsumption clause = 
  let new_clause = Prop_solver_exchange.prop_subsumption clause in
  if new_clause == clause
  then clause 
  else
    begin
      eliminate_clause clause;
      incr_int_stat (-1) inst_num_child_elim;
      try      
	(let _existing_simplified = ClauseAssignDB.find new_clause !clause_db_ref in
	incr_int_stat 1 inst_num_existing_simplified;
(* if the existing simplified clause is not in the input_under_eq then   *)
(* we need to make it input_under_eq, possibly remove from active *)
(* special tratment of eq axioms yet does not work 
   (if (Clause.get_bool_param Clause.input_under_eq existing_simplified)
   then ()
   else 
   (Clause.set_bool_param true Clause.input_under_eq existing_simplified;
	    if (Clause.get_bool_param Clause.in_active existing_simplified) 
   then 
	      (move_from_active_to_passive existing_simplified)
   else ()
	   )
	 );*)
	(* out_str ("Prop Subs Simplifies exists: n "^(Clause.to_string existing_simplified));*)
	raise Simplified_exists
	)
      with 
	Not_found -> (* Simplified is a new clause *)
	  (((*try *)
	   Prop_solver_exchange.add_clause_to_solver new_clause
	 (*with PropImplied -> ()*));
	   Clause.inherit_param_modif clause new_clause;
	  let added_clause = 
	    ClauseAssignDB.add_ref new_clause clause_db_ref in             
	  (*(if (PropSolver.fast_solve solver []) = PropSolver.FUnsat  
	  then raise Unsatisfiable);*)
	  (*add_clause_to_solver solver_sim solver gr_by added_clause;*)

(*	  Clause.assign_when_born (get_val_stat inst_num_of_loops)  added_clause;*)

	  (*inherit some parameters from parent*) 

	 (* out_str ("\n Clause: "^(Clause.to_string clause)^"\n");
	  out_str ("\n Simplified to: "^(Clause.to_string added_clause)^"\n");*)
	  (* add_clause_to_unprocessed added_clause;
	     raise Given_clause_simplified *)
	  added_clause)
    
    end


exception Simplified

(* simple not complete, after prop_subsumption*)
let tautology_elim c = 
  if (Clause.length c = 2)
  then 
    let lits = (Clause.get_literals c) in
    match lits with 
    |[l1;l2] ->
	( 
	 if (Term.is_neg_lit l1) 
	 then 
	   if (l2 == (Term.get_atom l1))
	   then
	     (
	      incr_int_stat 1 inst_num_tautologies;
	    (*  out_str ("Tautology: "^(Clause.to_string c)^"\n");*)
	      raise Simplified)
	   else ()
	 else 
	   if (Term.is_neg_lit l2)
	   then
	     if (l1 == (Term.get_atom l2))
	     then
	       (
		incr_int_stat 1 inst_num_tautologies;
		Clause.set_bool_param true Clause.is_dead c;
(*		out_str ("Tautology: "^(Clause.to_string c)^"\n");*)
		raise Simplified)
	     else ()  
	 )
    |_-> failwith "Tautology_elim: this shouldn't happen"
 

(*exception New_Clause_Simplified *)

let simplify_new clause = 
  let new_clause = 
    if !current_options.inst_prop_sim_new && 
      ((get_val_stat inst_num_of_learning_restarts) >= !current_options.inst_start_prop_sim_after_learn)
    then
      (prop_subsumption clause)
   else clause
  in 
  new_clause 

      
(*let ()=  out_str "Debug: Uncomment simplify_given_clause\n"*)
(* can raise Simplified_exists Simplified*)
let simplify_given_clause clause = 
  tautology_elim clause;
  let new_clause = 
    if !current_options.inst_prop_sim_given && 
      ((get_val_stat inst_num_of_learning_restarts) >= !current_options.inst_start_prop_sim_after_learn)
    then
      (prop_subsumption clause)
    else clause
  in 
  new_clause


(*   
(*let ()=  out_str "Debug: Uncomment in simplify_clause_list\n"*)
let simplify_clause_list clause_list =
  clause_list
(* not needed since propositional learning....*)
(*  let simpl_clause rest clause = 
    if (10 >(Clause.when_born clause))
    then
      try 
	let new_clause = prop_subsumption clause in
	if (new_clause == clause) then   
	  new_clause::rest
	else 
	  (add_clause_to_unprocessed new_clause; 
	   rest)	
      with 
	  Simplified_exists  -> rest
    else 
      clause::rest
  in List.fold_left simpl_clause [] clause_list
*)
  *)


(*----------------------- End Simplification----------------------*)
  

(*-----------------------All_instantiations----------------------*)

let all_instantiations main_clause =
  try
    (*we assume that sel in main_clause is checked before *)
    (*on accordance with solver*)
    let sel_lit_tmp = Clause.get_inst_sel_lit main_clause in
    (try 
      ( (*uncommnet for lit activity!*)
	Prop_solver_exchange.lit_activity_check 
	  move_lit_from_active_to_passive sel_lit_tmp;
       Prop_solver_exchange.increase_lit_activity 1 sel_lit_tmp) 
    with Prop_solver_exchange.Activity_Check ->  
      (Prop_solver_exchange.selection_renew 
	 move_lit_from_active_to_passive Selection.inst_lit_sel main_clause));
    let sel_lit = Clause.get_inst_sel_lit main_clause in
    
(*     out_str_debug ("all_instantiations main clause: "
        ^(Clause.to_string main_clause)^"\n");*)
    let compl_sel_lit = Term.compl_lit sel_lit in
    let unif_candidates = 
      DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
    let for_all_candidates (lit,clause_cand_list) =       
(*      out_str_debug ("inst_try cand_list:"^"Sel_lit: "^(Term.to_string  lit)^"\n"
		     ^(Clause.clause_list_to_string clause_cand_list)^"\n"); *)

(*Simplification tun later on *)
      try( 
(*uncomment for lit activity*)
	Prop_solver_exchange.lit_activity_check move_lit_from_active_to_passive lit;
	let clause_list =  clause_cand_list in

(*	let clause_list = simplify_clause_list  clause_cand_list  in*)
(*      let clause_list = clause_cand_list in*)
      if (clause_list != [])
      then
	try 
	  (
      (* let var_entry     = get_prop_gr_var_entry lit in
	  if (model_accords_solver solver var_entry)
	  then*)
	    (
(* debug*)   
	  (*   (if (Term.get_fun_bool_param Term.in_unif_index sel_lit) 
	     then 	 
	       try  
		 let ind_elem = DiscrTreeM.find sel_lit !unif_index_ref in ()
	       with
		 Not_found -> 
		   out_str ("Side is Not in Unif Index: "^(Term.to_string sel_lit)^"\n")
	     else ());*)
(*end debug*)
(*	     out_str "conclusion_list before\n";*)

	     let conclusion_list = 
	       Inference_rules.instantiation_norm 
		 term_db_ref clause_db_ref main_clause sel_lit compl_sel_lit 
		 clause_list lit in		  
(*	     out_str "conclusion_list after\n";*)
	     Prop_solver_exchange.increase_lit_activity  (List.length  conclusion_list) lit;
             let apply_to_concl clause =  
	    (*try *)


	       try 
		 Prop_solver_exchange.add_clause_to_solver clause;
		 let simplified_clause = simplify_new clause in	 
		 add_clause_to_unprocessed simplified_clause
	       with Simplified_exists -> ()
	  (*  with PropImplied -> ()*)
	      
	    (* with Clause_Simplified -> ()*)	  	  	    
	   in
	   List.iter apply_to_concl conclusion_list    
	  )
	(*else ()*) (*  model_accords_solver will move all clauses to passive!*)
	)
	with Unif.Unification_failed  -> ()       
      else ()
       )     
      with Prop_solver_exchange.Activity_Check ->  ()
    in	    
    List.iter for_all_candidates unif_candidates;
  with
    Clause.Inst_sel_lit_undef -> 
      failwith "all_instantiations: clause should have selected literals here"
  


 
(*-------------- end all_instantiations------------------*)



exception Given_Splitted

(*--------------------------LAZY LOOP BODY-----------------------------*)
(* Moved to Lib *)

(*let solve_num_deb = ref 0 *)
let solve_pass_empty = ref 0

(* let bmc1_bounds = ref [1; 2; 4; 8; 12; 16] *)
(* let bmc1_bounds = ref [4] *)
let bmc1_bounds = ref [] 

  let lazy_loop_body solver_counter sover_clause_counter =
    try  
      (let given_clause = remove_from_passive () in       
       if 
	 ((Clause.get_bool_param Clause.is_dead given_clause) ||
	 (Clause.get_bool_param Clause.in_active given_clause))
       then () 
       else	 
	 ( 
	solver_counter:=!solver_counter+1;  
	if ( !solver_counter > !current_options.inst_solver_per_active || 
	  (get_val_stat inst_num_of_loops) < !inst_solver_threshold ||
(*     solver_per_new_claues *)
	  ((get_val_stat prop_num_of_clauses) > 
	   (!sover_clause_counter + !current_options.inst_solver_per_clauses))
	    )
	  then
	    (  
	       (if ((get_val_stat prop_num_of_clauses) > 
		    (!sover_clause_counter + 
		       !current_options.inst_solver_per_clauses))
	       then      
		 sover_clause_counter:=(get_val_stat prop_num_of_clauses)     
	       );	 
	       solver_counter:=0;
	(*       solve_num_deb:= !solve_num_deb +1;
	       out_str ("Solve not forced "^(string_of_int !solve_num_deb)^"\n");
          *)    
	       if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat) 		 
		   (* || (PropSolver.solve solver_sim) = PropSolver.Unsat)*)
	       then ( (* Format.eprintf "Unsatisfiable after solve call in lazy_loop_body in instantiation@."; *)
		     raise Unsatisfiable)
	       else 	
		 (if !current_options.inst_eager_unprocessed_to_passive then
		   (List.iter add_new_clause_to_passive !unprocessed_ref;
		    unprocessed_ref:=[];
		    assign_int_stat 0 inst_num_in_unprocessed)
		 else ()

		 )
	       
	      )
       );        
	(*if (PropSolver.solve solver) = PropSolver.Unsat 
	then raise Unsatisfiable
	  else*)
       (try  
	 ((*out_str (" Start Simpl Given Clause: \n");*)
(*
	   out_str("\n--------------------------\n");
         out_str("\n Given Clause: "
                 ^(Clause.to_string given_clause)^"\n");
*)
             let simplified_given_clause 
	       = simplify_given_clause  given_clause in
(*
      out_str("\n--------------------------\n");
      out_str ("\n Simpl Given Clause: "
                     ^(Clause.to_string simplified_given_clause)^"\n");
*)										

(*
  (if (not (Clause.is_ground simplified_given_clause))
  then
	     (out_str("\n--------------------------\n");
             out_str ("\n Simpl Non-Gr Given Clause: "
                     ^(Clause.to_string simplified_given_clause)^"\n");)
  else ()
 );
*)

(*
	     out_str ("Min def symb depth: "
		      ^(param_to_string string_of_int 
			  (Clause.get_min_defined_symb simplified_given_clause))^"\n");
			  
*)		  

(*	     out_str("Clause length: "^(string_of_int (Clause.length simplified_given_clause)));*)

(*         out_str ("Is Eq: "
           ^(string_of_bool 
  (Clause.get_bool_param Clause.eq_axiom simplified_given_clause ))
           ^" Is Input_under_eq: "
           ^ (string_of_bool 
(Clause.get_bool_param Clause.input_under_eq simplified_given_clause )));*)

(*	   out_str_debug ("\n Dist: "
			  ^(string_of_int (Clause.get_conjecture_distance simplified_given_clause))^"\n");*)
(* out_str ("Has conj symb: "
	  ^ (string_of_bool
	       (Clause.get_bool_param Clause.has_conj_symb simplified_given_clause ))^"\n");*)

	   (match  !current_options.ground_splitting with
	   |Split_Full->
	     let split_result = 
	       (Splitting.ground_split_clause simplified_given_clause) in
	     if (Splitting.get_num_of_splits split_result)>0 
	     then
	       ((*out_str "Eliminate Cl Splitting";*)
		eliminate_clause simplified_given_clause;
		let splitted_clauses = Splitting.get_split_list split_result in
		let f new_clause = 
		  Clause.assign_when_born 
		    [simplified_given_clause][] new_clause;
		  let added_clause = 
		    ClauseAssignDB.add_ref new_clause clause_db_ref in             
(*		  Clause.assign_when_born 
		    (get_val_stat inst_num_of_loops) added_clause;*)
	
		  Prop_solver_exchange.add_clause_to_solver added_clause;
		  add_clause_to_unprocessed added_clause;
		(*  out_str ("Splitted_clause: "^(Clause.to_string added_clause)^"\n")*)
		in 
		List.iter f splitted_clauses;	    
		incr_int_stat 
		  (Splitting.get_num_of_splits split_result) num_of_splits; 
		incr_int_stat 
		  (Splitting.get_num_of_split_atoms split_result) num_of_split_atoms;
		raise Given_Splitted)
	   |_-> ()
	   );
	     
	

(*     out_str ("\n Given after simpl: "^(Clause.to_string new_clause)^"\n");*)
	     
	       Prop_solver_exchange.selection_renew 
		 move_lit_from_active_to_passive Selection.inst_lit_sel simplified_given_clause;


(*	    lit_activity_check solver new_clause;    *)

	     
(* let new_clause = simplify_given_clause solver_sim solver  clause in *)



	 (*  out_str ("\n Age Given: "
		    ^(string_of_int(!num_of_instantiation_loops - (Clause.when_born new_clause)))); *)

	(* out_str_debug (model_sel_to_string solver); *)
	
(*
	   out_str ("Sel in Given: "^ 
			  (Term.to_string (Clause.get_inst_sel_lit simplified_given_clause)^"\n"));
*)

(*  out_str("Clauses in DB: "^(string_of_int (ClauseAssignDB.size !clause_db_ref))^"\n");*)
(*Debug*)
(*       let lits_consist_model = 
	 Clause.find_all consistent_with_model clause in
       out_str_debug ("Act. Clause: "^(Clause.to_string clause)^"\n");
       out_str_debug ("Cons Lits: \n ");
       let out_consist lit = 
	 out_str_debug ((Term.to_string lit)^("\n"))
       in 
       List.iter out_consist lits_consist_model; 
       out_str_debug ("Sel Lit: "
		      ^(Term.to_string (Clause.get_inst_sel_lit clause))^"\n");	 *)
(*End Debug*)
	     
             all_instantiations  simplified_given_clause;
	   
(*     all_instantiations_sel solver gr_by clause;*)	  
	     add_to_active simplified_given_clause;

(*	     out_str ("\n Add to Active: "
		      ^(Clause.to_string simplified_given_clause)
		      ^"In Active: "
		      ^(string_of_bool (Clause.get_bool_param Clause.in_active 
					  simplified_given_clause))
		      ^"In queu1: "		      
		      ^(string_of_bool (Clause.get_bool_param Clause.inst_pass_queue1 
					  simplified_given_clause))
		      ^"In queu2: "		      
		      ^(string_of_bool (Clause.get_bool_param Clause.inst_pass_queue2 
					  simplified_given_clause))^"\n")	     
  *)    

(*----------Exchange with resolution----------*)
(* do not need now *)
	 (*    (if (!resolution_flag 
		    && 
		  !inst_simp_exchange_flag 
		    &&
		  (not (simplified_given_clause==given_clause))) 
	     then
	       (
		Discount.add_inst_exchange_clause_to_passive
		  (Clause.create (Clause.get_literals simplified_given_clause));
		num_from_inst_exchanged:=!num_from_inst_exchanged+1;
	       )
	     else()
	     )
	       *)
	    )
       with Prop_solver_exchange.Activity_Check ->  
	 add_clause_to_unprocessed given_clause
       )	   
      )	       	
  with	  
  |Passive_Empty -> 
      (	
(*
	      solve_pass_empty:= !solve_pass_empty +1;
	       out_str ("Passive Empty "^(string_of_int !solve_pass_empty)^"\n"
			 
			^" unprocessed "^(string_of_int (List.length !unprocessed_ref))^"\n");
	out_str ((Clause.clause_list_to_string !unprocessed_ref)^"\n");
*)

(* Now we assume that value of prop. literals are always defined *)
(* Even if we have not run the solver on these set of clauses    *)
(* MiniSAT was modified respectively *)
(* if it is not the case uncommment "if" below *)
(*
	if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
	then (raise Unsatisfiable)
	else
 *)
	(
(* old,  if passive and unprocessed are empty we *)
(* don't need that model accords with the solver, *)
(* it still will be a model for active clauses! *)
 (*  try
 	  List.iter add_new_clause_to_passive !unprocessed_ref;
	  unprocessed_ref:=[];
	  num_in_unprocessed:=0;
	  apply_new_model Prop_solver_exchange.solver;
	  num_of_solver_calls := !num_of_solver_calls +1
	      (* out_str_debug (model_sel_to_string ())*)
	with 
	  Sel_Unchanged -> 
	    (if (*!simple_passive_ref =[] *)
		(passive_is_empty ()) &&  (!unprocessed_ref=[])
	    then  (*out_str_debug (model_sel_to_string solver); *)
	      raise Satisfiable
	    else())
  *)

	 if (!unprocessed_ref=[])
	 then  
	   raise (Satisfiable !clause_db_ref) 
	 else
	   (
	    List.iter add_new_clause_to_passive !unprocessed_ref;
	    unprocessed_ref:=[];
	    assign_int_stat 0 inst_num_in_unprocessed
	    )	 
	)
      )
  |Simplified -> ()
  |Simplified_exists  -> ()(*(out_str ("\n Simplified_exists\n "))*)
  |Given_Splitted     -> () (*out_str "Given_Splitted\n"*)

(* Removed: BMC1 only from top-level, not inside the instantiation loop *)
(*

  (* Unsatisfiable and next bound for BMC1 *)
  | PropSolver.Unsatisfiable
  | Unsatisfiable
      when ((List.length !bmc1_bounds) > 1 ) -> 

      (

	(* Add an axiom clause to unprocessed *)
	let add_bound_axioms_to_unprocessed clause = 

	  (* Add clause to database *)
	  let clause' = 	     
	    ClauseAssignDB.add_ref 
	      (Clause.copy_clause clause) 
	      clause_db_ref
	  in             
	    
	    (* Assign age of clause *)
	    Clause.assign_when_born [] [] clause';

	    (* Add clause to solver *)
	    Prop_solver_exchange.add_clause_to_solver clause';
	    
	    (* Add clause to unprocessed set *)
	    add_clause_to_unprocessed clause'
	      
	in
	  
	(* Get current and next bounds *)
	let cur_bound, next_bound, bounds_tail =
	  match !bmc1_bounds with
	    | b :: c :: tl -> b, c, tl
	    | _ -> failwith ("Iprover.main: bmc1_bounds too short")
	in
	  
	  (* Output current bound *)
	  Format.printf 
	    "%s BMC1 bound %d unsatisfiable@\n@."
	    pref_str
	    cur_bound;
	  
	  (* Output statistics *)
	  out_stat ();
	  
	  (* Output next bound *)
	  Format.printf 
	    "%s Incrementing BMC1 bound to %d@\n@."
	    pref_str
	    next_bound;
	  
	  (* Get axioms for next bound *)
	  let next_bound_axioms = 
	    Bmc1Axioms.increment_bound cur_bound next_bound false
	  in
	    
	    (* Symbols in axioms are input symbols *)
	    List.iter  
	      (Clause.iter_sym 
		 (Symbol.assign_is_essential_input true)) 
	      next_bound_axioms;
	    
	    (* Preprocess axioms *)
	    let next_bound_axioms' = 
	      Preprocess.preprocess next_bound_axioms
	    in

	      (* Make all active clauses passive *)
	      Prop_solver_exchange.clear_model_and_move_to_passive
		move_from_active_to_passive;

	      (* Eliminate current bound from list *)
	      bmc1_bounds := next_bound :: bounds_tail;

	      (* Add all axioms to unprocessed *)
	      List.iter 
		add_bound_axioms_to_unprocessed 
		next_bound_axioms'

      )

  (* Unsatisfiable and no more bounds for BMC1 *)
  | PropSolver.Unsatisfiable -> 
      raise Unsatisfiable

*)


(*------------------------ Lazy Loop ---------------------*)

let rec instantiation_lazy_loop () =
  let solver_counter = ref 0 in
  let solver_clause_counter = ref 0 in
  let stat_counter   = ref 0 in
  let bound_iter     = ref 0 in 
  out_str !param_str_ref;
  while true do
(* while !bound_iter < 10000 do*)
(*    (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)
   lazy_loop_body solver_counter solver_clause_counter;
    stat_counter := !stat_counter +1;
    bound_iter:=!bound_iter +1
  done  



(*------------------------Lerning Restart ------------------------*)
(*
let learning_restart input_clauses  = 
  clause_db_ref :=  
    (ClauseAssignDB.create_name 
       ("Instantiation_Clauses_DB"));   
  clean_passive ();
 (* empty unif index *)
  unif_index_ref  :=  (DiscrTreeM.create ());
(* for all terms set in_unif_index to false  *)
(* change later to terms in unif index only *)
 
 let f t = 
    match t with 
    |Term.Fun _ ->  (Term.set_fun_bool_param false  Term.inst_in_unif_index t)
    |_->() 
  in
  TermDB.iter f  !term_db_ref;

(* refresh the model *)

 (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat)
 then raise Unsatisfiable);
 

 Prop_solver_exchange.clear_model ();

 unprocessed_ref := [];    

 assign_int_stat 0 inst_num_in_active;
  (*   out_str("\n Learning Restart\n ");*)
  let add_cl clause =
    let new_clause   =        
       (Clause.normalise term_db_ref  (Clause.create (Clause.get_literals clause)))
    in
(*  let new_clause = Clause.normalise term_db_ref clause in *)
    let added_clause = 
      ClauseAssignDB.add_ref new_clause clause_db_ref in             
    add_clause_to_unprocessed added_clause;
    Clause.inherit_param_modif clause added_clause;
    Clause.inherit_bool_param Clause.in_prop_solver clause added_clause;
    Clause.assign_when_born 0 added_clause;

(*debug*)
(*	 out_str ((Clause.to_string added_clause)^"\n"^
		  (string_of_bool (Clause.get_bool_param Clause.in_prop_solver added_clause))^"\n");*)
 
  in
  List.iter add_cl input_clauses
(* Memory is cleared separately by Lib.clear_mem ()*)

(*  out_str "Major GC \n";*)
 (*  out_str "Major end  \n"*)
   (* out_str_debug ("Learning restart: "^(string_of_int !num_of_restarts)^"\n");*)
   (*      out_statistics ()*)
*)

(*------------------------End Lerning Restart----------------------*)






(*----------------------Start Instantiation--------------------------*)

(*
let init_instantiation  input_clauses = 
  let add_input_to_unprocessed clause = 
    let added_clause = 	     
      (ClauseAssignDB.add_ref  clause clause_db_ref) in             
    Clause.set_bool_param true Clause.input_under_eq added_clause;
(* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
    Clause.set_bool_param true Clause.input_under_eq clause;
    Clause.assign_when_born 0 added_clause;
    add_clause_to_unprocessed added_clause
  in
  List.iter add_input_to_unprocessed input_clauses;
(*  full_loop input_clauses;*)

*)


  
  
let init_instantiation () = 
  let add_input_to_unprocessed clause = 
    try
      let added_clause = 	     
	    ClauseAssignDB.add_ref (Clause.copy_clause clause) clause_db_ref
      in
	(*		out_str ("\n Added: "^(Clause.to_string added_clause)^"\n");*)
      Clause.assign_when_born [] [] added_clause;
      add_clause_to_unprocessed added_clause
    (* Skip duplicate clauses in the input *)
    with Clause.Clause_fast_key_is_def ->
			(
				(* out_str ("Failed: "^(Clause.to_string clause)^"\n"); *)
		 failwith "init_instantiation Clause.Clause_fast_key_is_def")
  in

(*Christph added; not clear why *)
(* commented for now *)
(*
  let input_clauses' =
    
    (* Check list of bounds for incremental BMC *)
    match !bmc1_bounds with 
	
      (* Take initial bound *)
      | b :: tl -> 
	  
	  (* Create clauses for initial bound *)
	  let bmc1_axioms = Bmc1Axioms.increment_bound 0 b false in
(*	  
	  (* Create equality axioms also for symbols in BMC1 axioms *)
	  let eq_axioms = Eq_axioms.axiom_list () in
*)	      
	  (* Preprocess axioms *)
	  let bmc1_and_eq_axioms = 
	    Preprocess.preprocess bmc1_axioms
(*	    Preprocess.preprocess (bmc1_axioms @ eq_axioms) *)
	  in
	    
	    (* Symbols in axioms are input symbols *)
	    List.iter  
	      (Clause.iter_sym 
		 (Symbol.assign_is_essential_input true)) 
	      bmc1_and_eq_axioms;
	    
	    (* Add clause to solver *)
	    List.iter
	      Prop_solver_exchange.add_clause_to_solver 
	      bmc1_and_eq_axioms;

	    (* Add clauses for initial bound *)
	    bmc1_and_eq_axioms @ input_clauses
		  
      (* No bounds given *)
      | [] -> input_clauses
	  
  in

    List.iter add_input_to_unprocessed input_clauses'
*)

  List.iter add_input_to_unprocessed input_clauses
	
(* 
 (*----------debug----------*)
   let out_cl c = 
      out_str ("Clause: "
	       ^(Clause.to_string c)
	       ^" has conj symb: "
	       ^ (string_of_bool (Clause.get_bool_param Clause.has_conj_symb c ))
	       ^" has non-prolific conj symb: "
	       ^(string_of_bool (Clause.get_bool_param Clause.has_non_prolific_conj_symb c ))
 ^" has bound constant: "
	       ^(string_of_bool (Clause.get_bool_param Clause.has_bound_constant c ))

	       ^"\n")
    in
    out_str "\n\n ------------------------------\n\n";
    ClauseAssignDB.iter out_cl !clause_db_ref
  
  (*--------debug-------*)
*)

let _ = init_instantiation ()

(*------------------Clears All---------------------------*)

let clear_all () = 

(* a trick to keep old value of functional statistics*)
(* like number of clauses and number in passive*)

  let num_in_passive = (get_val_stat_fun inst_num_in_passive) in
  assign_fun_stat 
    (fun () -> num_in_passive) 
    inst_num_in_passive;

  let num_of_clauses = (get_val_stat_fun inst_num_of_clauses) in
  assign_fun_stat 
    (fun () -> num_of_clauses) 
    inst_num_of_clauses;

(* clear clause db *)
  clause_db_ref :=  
    (ClauseAssignDB.create_name 
       ("Instantiation_Clauses_DB"));   

(* clear passive_queue *)
  passive_queue_ref:= create_passive_queue 1;
  
 (* empty unif index *)
  unif_index_ref  :=  (DiscrTreeM.create ());
  

  let f t = 
    match t with 
    |Term.Fun _ ->  (Term.set_fun_bool_param false  Term.inst_in_unif_index t)
    |_->() 
  in
  TermDB.iter f  !term_db_ref;
  
(* refresh the model *)

  (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat)
   then ( (* Format.eprintf "Unsatisfiable after solve call in Instantiation.clear_all@."; *)
	raise Unsatisfiable));
  Prop_solver_exchange.clear_model ()



(*---------------End--------------------------------*)
end (* Instantiation.Make *)


let clear_after_inst_is_dead () = 
   let f t = 
    match t with 
    |Term.Fun _ ->  (Term.set_fun_bool_param false  Term.inst_in_unif_index t)
    |_->() 
  in
  TermDB.iter f  !Parser_types.term_db_ref;
  
(* refresh the model *)

   Prop_solver_exchange.clear_model ()



(*--------------Commented Part-----------------------*)

(*
(* it's better to simplify before splitting ... add later*)
let simplify_input init_clause_list_ref = 
(* need to add to solver before simplifying *)
    let add_to_prop_solver clause =
      add_clause_to_solver solver_sim solver grounding_term clause
    in List.iter add_to_prop_solver !init_clause_list_ref;
    let subs clause =
    let  new_clause = prop_subsumption clause in
    if ground_splitting_input || ground_splitting_full
    then
      let split_result = 
	(Splitting.ground_split_clause 
	   symbol_db_ref term_db_ref split_map_ref clause) in      
  num_of_splits  := !num_of_splits + (Splitting.get_num_of_splits split_result);
  Statistics.incr_int_stat (Splitting.get_num_of_splits split_result);
      num_of_split_atoms := 
	!num_of_split_atoms + (Splitting.get_num_of_split_atoms split_result);
      init_clause_list_ref:=Splitting.get_split_list split_result);
*)


(*    
let simplify_input init_clause_list = 
  let simplify_clause rest clause = 
    try 
      (prop_subsumption clause)::rest
    with 
      Simplified_exists 
      -> rest
  in
  List.fold_left simplify_clause [] init_clause_list
*)    


(*
  let start_instantiation ()
  try
(* signals:*)
    let signal_handler signal =
      if 
	(
(*      signal = Sys.sigquit ||*)
(*	signal = Sys.sigvtalrm ||*)
	signal = Sys.sigint  (*||*)
(*	signal = Sys.sigalrm || 	*)
(*	signal = Sys.sigterm || *)
(*	signal = Sys.sigtstp *)
	) 
      then
	(out_stat (); 
	 raise Termination_Signal)     
      else failwith "Unkown Signal"
    in  	  
(*    Sys.set_signal Sys.sigquit (Sys.Signal_handle signal_handler);*)
    Sys.set_signal Sys.sigint (Sys.Signal_handle signal_handler);
(*    Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigkill (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigalrm  (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigterm (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigtstp (Sys.Signal_handle signal_handler);*)



 
  (*  lit_sel_fun_ref:=lit_sel_fun;*)

(*    let grounding_term = get_term_for_grounding  () in*)
(*    let grounding_term = bot_term in*)
(*  out_str_debug ("Term for grounding: "^(Term.to_string grounding_term)^"\n");*)
(*    let solver = PropSolver.create_solver () in*)
(* solver used for simplifications *)
(*    let solver_sim = PropSolver.create_solver () in*)
    let equality_axioms = Eq_axioms.axiom_list () in
    init_clause_list_ref:= equality_axioms@(!init_clause_list_ref);  
    (*(if (Symbol.is_input Symbol.symb_equality) 
    then  resolution_mult:= (!resolution_mult /10));*)


 (*   out_str_debug ("Equality Axioms:\n" 
		   ^(Clause.clause_list_to_string equality_axioms)^"\n"); *)
(*    out_str_debug 
      ("Init Clauses: \n"
       ^(Clause.clause_list_to_string !init_clause_list_ref));    *)
(* it's better to simplify before splitting ... add later*)
(*    simplify_input init_clause_list_ref;*)
  
(*    out_str_debug 
      ("After Split: \n"
       ^(Clause.clause_list_to_string !init_clause_list_ref));*)

(*----------add clause to prop solver------------*)
    List.iter 
      Prop_solver_exchange.add_clause_to_solver !init_clause_list_ref;

    (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat )
(*|| 
    (PropSolver.solve Prop_solver_exchange.solver_sim) = PropSolver.Unsat*)
    then raise Unsatisfiable
    else ());

(*-----------------should assign params before simplifying?------------*)
(*-------should be simplified_init later----------*)

    init_clause_list_ref:= 
      simplify_input !init_clause_list_ref;

    let split_map_ref = ref (Splitting.create_split_map ()) in
    (match !current_options.ground_splitting with
    |Split_Input |Split_Full ->    
	let split_result = 
	(Splitting.ground_split_clause_list !init_clause_list_ref) in
	incr_int_stat 
	  (Splitting.get_num_of_splits split_result) num_of_splits; 
	incr_int_stat 
	  (Splitting.get_num_of_split_atoms split_result) num_of_split_atoms;	
	init_clause_list_ref:=Splitting.get_split_list split_result
    |_-> ()
    );
    
    let add_input_to_unprocessed clause = 
      let added_clause = 	     
	(ClauseAssignDB.add_ref  clause clause_db_ref) in             
      Clause.set_bool_param true Clause.input_under_eq added_clause;
(* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
      Clause.set_bool_param true Clause.input_under_eq clause;
      Clause.assign_when_born 0 added_clause;
      add_clause_to_unprocessed added_clause
    in
    List.iter add_input_to_unprocessed !init_clause_list_ref;
    full_loop ();

(*
    let add_cl_to_solver_and_unprocessed clause =
      (*try 
	let simplified_clause = simplify_new clause in *)
	(try
	  add_clause_to_solver solver_sim solver grounding_term clause;
(* we have normalised clauses before, also normalisation will lose params*) 
(* such as conj_dist *)
(*(Clause.normalise term_db_ref clause)*)
	  let added_clause = 	     
	      (ClauseAssignDB.add_ref  clause clause_db_ref) in             
	  Clause.set_bool_param true Clause.input_under_eq added_clause;
(* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
	  Clause.set_bool_param true Clause.input_under_eq clause;
	  Clause.assign_when_born 0 added_clause;
	  add_clause_to_unprocessed added_clause
	(*out_str_debug ((Clause.to_string added_clause)^"\n")*)
	with PropImplied -> () )
    (*  with New_Clause_Simplified -> ()   *)
    in
    List.iter add_cl_to_solver_and_unprocessed !init_clause_list_ref;
 *)
   
  with
  |Unsatisfiable |PropSolver.Unsatisfiable -> 
      out_str "PROVED (by instnatiation)\n";
      out_stat ()
  |Satisfiable   -> 
      out_str "SATISFIABLE (by instnatiation)\n";  
      out_stat ()	
  |Discount.Unsatisfiable ->

(*      out_str "PROVED (by resolution)\n";*)
      out_stat ()

  |Discount.Satisfiable ->
      out_stat ()

  *)    

 (*out_str (test_sel ())*)


(* 
let start_instantiation () = 
(* get term for grounding*)
  let num_of_symb = SymbolDB.size !symbol_db_ref in
  (if  num_of_symb < !actual_num_of_symb_groups_ref
  then actual_num_of_symb_groups_ref := num_of_symb);  
  partition_symbols !actual_num_of_symb_groups_ref;
    let add_clause clause = 
      add_new_clause_to_passive clause clause
    in
    List.iter add_clause !init_clause_list_ref;
    (* ClauseAssignDB.iter add_caluse !init_clause_db_ref; *)
   (* out_str_debug "initial clauses are added to passive \n";*)
    try  discount_loop () with
    |Unsatisfiable -> 
	out_str "\n PROVED";
   out_statistics ()	  	
    |Satisfiable   -> 
	out_str "\n SATISFIABLE";  
	out_statistics ()

*)

(* tests *)
(*
let test_sel () =  
  let truth_f term = true in
  let sel_lit clause =
    Selection.lit_neg_gr_shallow truth_f clause in
  let to_str rest clause =
    rest^"Clause: "^(Clause.to_string clause)^"\n"
    ^"Sel: "^(Term.to_string (sel_lit clause))^"\n" in
  List.fold_left to_str "" !init_clause_list_ref
*)

(*
end
*)













(************ all_instantiations_sel with the selection: *) 
(************ lit is sel if it has the least  number     *)
(************ of unif. compl lits in unif index          *)
(*
let all_instantiations_sel solver_sim solver gr_by main_clause =
  try 
    let accord lit = 
      let var_entry     = get_prop_gr_var_entry lit in
      change_model_solver solver var_entry in
    Clause.iter accord main_clause; 
    let sel_cand_lits  = 
      Clause.find_all consistent_with_model main_clause in
(* returns list (lit, unif_cand_list_[] ) *) 
    let lits_unif = 
      let get_unif_cand lit = 
	(lit, (DiscrTreeM.unif_candidates !unif_index_ref (Term.compl_lit lit))) in      
      List.map get_unif_cand sel_cand_lits 
    in
    let comp_cand (l1,unif_list1) (l2,unif_list2) = 
      -(compare (List.length unif_list1) (List.length unif_list2)) in
    let (sel_lit,unif_candidates) = 
      Lib.list_find_max_element comp_cand lits_unif in
    Clause.assign_inst_sel_lit sel_lit main_clause;
    ass_if_consistent sel_lit main_clause;
    let compl_sel_lit = Term.compl_lit sel_lit in
(*old part*)
    let for_all_candidates (lit,clause_list) =       
      (*out_str_debug ("inst_try: "^(Clause.to_string main_clause)*)
      (*^(Clause.clause_list_to_string clause_list)); *) 
      try 
	(let var_entry     = get_prop_gr_var_entry lit in
(*	if (model_accords_solver solver var_entry)
	then*)
	  (
	   let conclusion_list = 
	     Inference_rules.instantiation_norm dismatch_switch
	       term_db_ref clause_db_ref main_clause sel_lit compl_sel_lit 
	       clause_list lit in		  
           let apply_to_concl clause =  
	    (*try *)
(* uncomment this if back to  constraint checking then simplified *)
	      (* let simplified_clause = simplify clause in	 *)
	    let simplified_clause = clause in
(* uncomment this if back to  constraint checking then simplified *)
	    (* let added_clause = 
		ClauseAssignDB.add_ref clause clause_db_ref in *)          
	    let added_clause = clause in
	    add_clause_to_solver solver_sim solver gr_by added_clause;
            add_clause_to_unprocessed added_clause
	    (* with Clause_Simplified -> ()*)	  	  	    
	   in
	   List.iter apply_to_concl conclusion_list    
	  )
(*	else ()*) (*  model_accords_solver will move all clauses to passive!*)
	)
      with Unif.Unification_failed  -> ()       
    in	
    List.iter for_all_candidates unif_candidates
  with
    Clause.Inst_sel_lit_undef -> 
      failwith "all_instantiations: clause should have selected literals here"

*)
(************ end all_instantiations ********)

(**************** instantiation_exhaustive_loop *********************)
(* we exhaustivelly apply instantiations util passive is empty *)
(* then apply prop_solver *)
(*    
let rec instantiation_exhaustive_loop solver_sim solver gr_by =
  let stat_counter = ref 0 in
  while true do  
    (*  out_str_debug 
	("instantiation_exhaustive_loop \n "
	^(string_of_int !num_of_instantiation_loops));*)
    num_of_instantiation_loops := !num_of_instantiation_loops + 1;  
    stat_counter := !stat_counter +1;
(* often output of statistic *)
  (*  (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)
    try  
    (*  let clause = remove_from_simple_passive () in*)
      let clause = remove_from_passive () in
      if ((Clause.get_bool_param Clause.is_dead clause) ||
      (Clause.get_bool_param Clause.in_active clause))
      then () 
      else
(* sp for simple passive *)
	(selection_renew solver clause;
	 all_instantiations solver_sim solver gr_by clause;
	 add_to_active clause)	
    with
    |Passive_Empty ->
	(if (PropSolver.solve solver) = PropSolver.Unsat 
	then raise Unsatisfiable
	else 
	  try
 	    List.iter add_new_clause_to_passive !unprocessed_ref;
	    unprocessed_ref:=[];
	    apply_new_model solver;
	    num_of_solver_calls := !num_of_solver_calls +1
	   (* out_str_debug (model_sel_to_string ())*)
	  with 
	    Sel_Unchanged -> 
	      if (passive_is_empty ())
	      then raise Satisfiable
	      else())
    |PropSolver.Unsatisfiable -> raise Unsatisfiable
  done

*)

(**************** instantiation loop with each clause added to passive *)
(******************solver called**************)
(* replace here simple passive to passive*)
(*
let rec instantiation_each_loop solver_per_active solver_sim solver gr_by =
  let stat_counter = ref 0 in
  let solver_counter = ref 0 in
  while true do  
  (*  out_str_debug 
      ("instantiation_exhaustive_loop \n "
      ^(string_of_int !num_of_instantiation_loops));*)
    num_of_instantiation_loops := !num_of_instantiation_loops + 1;  
    stat_counter := !stat_counter +1;
    solver_counter:=!solver_counter+1;
(* often output of statistic *)
  (*  (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)
 
    try  
(* test run solver every loop *)
     (* if (PropSolver.solve solver) = PropSolver.Unsat 
      then raise Unsatisfiable
      else*)       
	(if ((!solver_counter > solver_per_active ) || 
	(passive_is_empty ()))
	then 
	  if (!unprocessed_ref = []) && (passive_is_empty ())
	  then raise Satisfiable
	  else
	    (solver_counter:=0;	 
	   if (PropSolver.solve solver) = PropSolver.Unsat 
	   then raise Unsatisfiable
	   else       
	     (List.iter add_new_clause_to_passive !unprocessed_ref;
	      unprocessed_ref:=[];
	      try
		apply_new_model solver
	      with
		Sel_Unchanged -> 
		  if (passive_is_empty ())
		  then raise Satisfiable
		  else()
	     )	
	  )
	else
	  let clause = remove_from_passive () in       
	if ((Clause.get_bool_param Clause.is_dead clause) ||
	(Clause.get_bool_param Clause.in_active clause))
	then () 
	else	 
	  (selection_renew solver clause;
	   all_instantiations solver_sim solver gr_by clause;
	   add_to_active clause)       
	)
   with	  
    |Passive_Empty -> ()
    |PropSolver.Unsatisfiable -> raise Unsatisfiable
  done
*)
(****************end instantiation_each_loop***************)

(***************instantiation lazy loop***********************)
(*we change model patially and lazily for literals detected having different *)
(* value in the solver vs in the model *)

(*
let rec instantiation_lazy_loop solver_per_active solver gr_by =
  let stat_counter = ref 0 in
  let solver_counter = ref 0 in
  while true do  
  (*  out_str_debug 
      ("instantiation_exhaustive_loop \n "
      ^(string_of_int !num_of_instantiation_loops));*)
    num_of_instantiation_loops := !num_of_instantiation_loops + 1;  
    stat_counter := !stat_counter +1; (* out statistic after some steps*)
    solver_counter:=!solver_counter+1;
(* often output of statistic *)
    (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());
    try  
      (if !solver_counter > solver_per_active  
      then       
	(num_of_solver_calls := !num_of_solver_calls +1;
	 if (PropSolver.solve solver) = PropSolver.Unsat 
	 then raise Unsatisfiable
	 else solver_counter:=0));      
      let clause = remove_from_passive () in       
      if 
	((Clause.get_bool_param Clause.is_dead clause) ||
	(Clause.get_bool_param Clause.in_active clause))
      then () 
      else	 
	((*out_str_debug ("Given Clause: "^(Clause.to_string clause)^"\n");*)
	 selection_renew solver clause;
	(* out_str_debug ("Sel in Given: "^ *)
	(*		(Term.to_string (Clause.get_inst_sel_lit clause)^"\n"));*)
	(* out_str_debug (model_sel_to_string solver); *)
	 all_instantiations solver_sim solver gr_by clause;
	 add_to_active clause)       	
    with	  
  |Passive_Empty -> 
  ( num_of_solver_calls := !num_of_solver_calls +1;
  if (PropSolver.solve solver) = PropSolver.Unsat 
	then raise Unsatisfiable
	else 
  try
  List.iter add_new_clause_to_passive !unprocessed_ref;
	    unprocessed_ref:=[];
             num_in_unprocessed:=0;
	    apply_new_model solver;
	    num_of_solver_calls := !num_of_solver_calls +1
		(* out_str_debug (model_sel_to_string ())*)
	  with 
	    Sel_Unchanged -> 
	      (if (*!simple_passive_ref =[] *)
		!passive_queue_ref = PassQueue.empty
	      then  ((*out_str_debug (model_sel_to_string solver); *)
		     raise Satisfiable)
	      else())
	)	  
    |PropSolver.Unsatisfiable -> raise Unsatisfiable
  done
*)

(*let ()= add_param_str "all_instantiations_sel\n"*)

(*
let return_solver_state solver = 
  let apply_entry var_entry =
    let prop_var = get_prop_var_var_entry var_entry in
    let prop_neg_var = get_prop_neg_var_var_entry var_entry in
    match var_entry.truth_val with	
    |Def(PropSolver.True) -> 	
	let _= PropSolver.solve_assumptions solver [prop_var] in ()
    |Def(PropSolver.False) ->
	let _= PropSolver.solve_assumptions solver [prop_neg_var] in ()
    |_ -> ()
  in
  TableArray.iter apply_entry var_table
*)


(* auxilary *)
(* nonsense
let rec check_same_sel_desc clause desc_clause = 
  if ((Clause.get_bool_param Clause.in_active desc_clause)
	&((Clause.compare_sel_place clause desc_clause) = 0))
  then 
    (out_str ("parent: "^(Clause.to_string desc_clause)
     ^"Sel: "^(Term.to_string (Clause.get_inst_sel_lit desc_clause))^"\n"); 
     true)
  else
    false
    let parent = Clause.get_parent desc_clause in 
    match parent with 
    |Def(p) -> check_same_sel_desc clause p
    |Undef -> false
    
 
let check_parent_same_sel clause = 
  let parent = Clause.get_parent clause in 
  match parent with 
  |Def(p) -> check_same_sel_desc clause p
  |Undef -> false
*)
    

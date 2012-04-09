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
open Statistics
open Options


(* Formatter for output, None if uninitialised. Use
   get_prop_dump_formatter as access function *)
let prop_clauses_dump_formatter = ref None 


(* Return a formatter for writing into the file given in the option
   --dbg_prop_clauses_dump_file *)
let get_prop_clauses_dump_formatter () = 

  match !prop_clauses_dump_formatter with

    (* Return formatter if initialised *)
    | Some f -> f 


    (* Formatter is not initialised *)
    | None -> 
      
      (* Formatter of channel of opened file *)
      let new_prop_clauses_dump_formatter = 
	
	try 
	  
	  (* Open formatter writing into file *)
	  formatter_of_filename 
	    false  
	    !current_options.dbg_dump_prop_clauses_file
	  
	with
	    
	  (* Catch errors when opening *)
	  | Sys_error _ -> 
	    raise (Failure 
	      (Format.sprintf 
		 "Could not open file %s for output"
		 !current_options.dbg_dump_prop_clauses_file))
	      
      in

      (* Save formatter *)
      prop_clauses_dump_formatter := Some new_prop_clauses_dump_formatter;

      (* Return formatter *)
      new_prop_clauses_dump_formatter
  




type prop_lit = PropSolver.lit
type prop_lit_uc = PropSolver.lit_uc

type term       = Term.term
type lit        = Term.literal
type symbol     = Symbol.symbol  
type clause     = Clause.clause

let bot_symb       = Symbol.symb_bot
let bot_term       = Parser_types.bot_term      

(* gr_by can be changed by  init_solver_exchange *)

let gr_by          = ref bot_term

let symbol_db_ref  = Parser_types.symbol_db_ref  
let term_db_ref    = Parser_types.term_db_ref

let init_clause_list_ref = Parser_types.all_current_clauses

(*------------Parameters that can be changed by other modules-----------*)

(*let lit_activity_threshold   = ref 200*)
(*let lit_activity_flag_ref    = ref true*)
let lit_activity_threshold   = ref 500

(*
let set_lit_activity_flag  b  =  
  (lit_activity_flag_ref := b;
   lit_activity_threshold:= 200000000
  )
*)
(*--------------------get term for grounding-----------------------*)  

let get_term_for_grounding () = 
  if !answer_mode_ref then 
    bot_term
  else
    begin
(* first try the  constant with max occurrence, which is in the conjecture*)
      let gr_symb = 
	let f_max_sym s max_sym = 
	  if ((Symbol.is_fun s) &&
	      ((Symbol.get_arity s) = 0) &&
	      (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym)) 
	  then s 
	  else max_sym
	in
    let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
    max_sym 
      in
  (* we need to find the term in term_db corresponding to max_sym*)
  (* for this we just try to add it to term_db *) 
      let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
      gr_by_term
    end    

let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
  (* debug*)
(* out_str ("Term for grounding_new: "^(Term.to_string gr_by_new)^"\n");
  match gr_by_new with 
  |Term.Fun(symb,_,_) ->
      out_str ("Number of occ_new: "^( string_of_int (Symbol.get_num_input_occur symb))^"\n")
  |_->()
*)



(*--------------Init Solvers-----------------------------*)

let solver = PropSolver.create_solver false 

let solver_sim = PropSolver.create_solver true

let solver_uc = PropSolver.create_solver_uc false

(* solver assumptions are used for finite models *)
(* solver assumptions are changed assign_solver_assumptions below*)

(* assumptions for all solvers *)
let solver_assumptions_ref = ref []  

(* Assumptions for unsat core solver *)
let solver_uc_assumptions_ref = ref []  

(* assumptions only for non-simplifying  *)
let only_norm_solver_assumptions_ref = ref []

(* assumptions only for non-simplifying  *)
let only_norm_solver_assumptions_ref = ref []

(* only for non-simplifying*)
let answer_assumptions_ref = ref [] 

let only_sim_solver_assumptions_ref = ref []

let get_solver_assumptions solver = 
  if (PropSolver.is_simplification solver) 
  then 
    ((!only_sim_solver_assumptions_ref)@(!solver_assumptions_ref))
  else 
    ((!only_norm_solver_assumptions_ref)@(!answer_assumptions_ref)@(!solver_assumptions_ref))

(* Return literal assumptions for unsat core solver *)
let get_solver_uc_assumptions () = !solver_uc_assumptions_ref

(* adjoint_preds are added for all simplified claues *)
(* used in finite models *)


let adjoint_preds = ref [] 


(*-------------------------*)


exception AssumptionsInconsistent
let normalise_assumptions assumptions = 
  if assumptions = [] 
  then []
  else
    let cmp l1 l2 = 
      compare (PropSolver.lit_var solver l1) (PropSolver.lit_var solver l2)
    in 
    let sorted_assumptions = List.sort cmp assumptions in
    let rec elim_duplicates_compl rest lit_list = 
      match lit_list with
      | [] -> rest 
      | l::[] -> l::rest
      | l1::l2::tl ->
	  let id1 = (PropSolver.lit_var solver l1) in 
	  let id2 = (PropSolver.lit_var solver l2) in 
	  if id1 = id2 
	  then 
	  let sign1 = (PropSolver.lit_sign solver l1) in 
	  let sign2 = (PropSolver.lit_sign solver l2) in 
	  if sign1 = sign2 
	  then 
	    elim_duplicates_compl rest (l1::tl)
	  else
	    raise AssumptionsInconsistent
	  else
  	    elim_duplicates_compl (l1::rest) (l2::tl)
    in
    elim_duplicates_compl [] sorted_assumptions

let normalise_assumptions_uc assumptions = 
  if assumptions = [] 
  then []
  else
    let cmp l1 l2 = 
      compare 
	(PropSolver.lit_var_uc solver_uc l1) 
	(PropSolver.lit_var_uc solver_uc l2)
    in 
    let sorted_assumptions = List.sort cmp assumptions in
    let rec elim_duplicates_compl rest lit_list = 
      match lit_list with
      | [] -> rest 
      | l::[] -> l::rest
      | l1::l2::tl ->
	  let id1 = (PropSolver.lit_var_uc solver_uc l1) in 
	  let id2 = (PropSolver.lit_var_uc solver_uc l2) in 
	  if id1 = id2 
	  then 
	  let sign1 = (PropSolver.lit_sign_uc solver_uc l1) in 
	  let sign2 = (PropSolver.lit_sign_uc solver_uc l2) in 
	  if sign1 = sign2 
	  then 
	    elim_duplicates_compl rest (l1::tl)
	  else
	    raise AssumptionsInconsistent
	  else
  	    elim_duplicates_compl (l1::rest) (l2::tl)
    in
    elim_duplicates_compl [] sorted_assumptions


(*---------------------*)

let () = assign_fun_stat 
    (fun () ->  
      (PropSolver.num_of_solver_calls solver) +
	(PropSolver.num_of_solver_calls solver_sim))
    prop_solver_calls
    
let () = assign_fun_stat 
    (fun () ->        
      (PropSolver.num_of_fast_solver_calls solver) +
	(PropSolver.num_of_fast_solver_calls solver_sim))
    prop_fast_solver_calls


let solve_num = ref 0 
(*---------------------*)

let solve () = 
  solve_num:= !solve_num +1;
 (* out_str ("Solve num: "^(string_of_int !solve_num));*)
 (* out_str ("Assumptions: "^
	     (PropSolver.lit_list_to_string 
		(get_solver_assumptions solver)) ^ "\n"); *)
  PropSolver.solve_assumptions solver (get_solver_assumptions solver)


let solve_assumptions solver assumptions = 
  try 
    let ass = normalise_assumptions (assumptions@(get_solver_assumptions solver)) in
    PropSolver.solve_assumptions solver ass  
  with 
    AssumptionsInconsistent -> PropSolver.Unsat

let fast_solve solver assumptions = 
   try 
    let ass = normalise_assumptions(assumptions@(get_solver_assumptions solver)) in
    PropSolver.fast_solve solver ass
   with 
     AssumptionsInconsistent -> PropSolver.FUnsat


(* The clauses in the satisfiability solver and their corresponding
   first-order clauses *)
let solver_uc_clauses : (int, Clause.clause) Hashtbl.t = Hashtbl.create 1001


let rec pp_clause_list ppf = function 
  | [] -> ()
  | [c] -> Format.fprintf ppf "%s" (Clause.to_string c)
  | c::tl -> 
    Format.fprintf ppf "%s@\n" (Clause.to_string c); 
    pp_clause_list ppf tl

let rec pp_unsat_core ppf = function 
  | [] -> ()
  | [e] -> Format.fprintf ppf "%d" e
  | e::tl -> Format.fprintf ppf "%d, " e; pp_unsat_core ppf tl


let unsat_core () = 

  let start_time = Unix.gettimeofday () in
  
  match 
    (
      
      try 
	
	(* Run unsat core solver with assumptions *)
	PropSolver.solve_assumptions_uc
	  solver_uc
	  (get_solver_uc_assumptions ())
	  
      (* Catch exception and return normally *)
      with PropSolver.Unsatisfiable -> PropSolver.Unsat
	
    )
      
  with 
      
    (* Should return unsat, but check *)
    | PropSolver.Unsat -> 
      
      (* Get the unsat core as a list of clause ids *)
      let unsat_core_ids = PropSolver.get_conflicts solver_uc in

      let end_time = Unix.gettimeofday () in
      add_float_stat (end_time -. start_time) prop_unsat_core_time;
      
      (* Get first-order clauses from clause ids *)
      let unsat_core_clauses =
	List.fold_left 
	  (fun a c -> 
	    try 
	      (Hashtbl.find solver_uc_clauses c) :: a
	  with Not_found -> 
	    a)
	  []
	  unsat_core_ids
      in
      
      (* Return clauses in unsat core *)
      unsat_core_clauses

    (* Must not return sat when other solver returns unsat *)
    | PropSolver.Sat -> 
       raise (Failure "Unsat core solver returned satisfiable")
      (*failwith "Unsat core solver returned satisfiable"*)

(*------------ propositional interpretation-------------------*)

type var_entry = 
    {var_id              : int param;
     prop_var            : prop_lit param; 
     prop_neg_var        : prop_lit param;
     prop_var_uc         : prop_lit_uc param; 
     prop_neg_var_uc     : prop_lit_uc param;
(* If  truth_val = Def(Any) the we assume that sel_clauses=[] *)
(* So if we select a lit the we should change Def(Any) *)
    mutable truth_val       : PropSolver.lit_val param; 
(* list of clauses for which selection is based on this var *)
     mutable sel_clauses    : (clause list);
(* used only for output of model*)
     mutable ground_term    : lit param;
     mutable in_solver_sim  : bool;
     mutable pos_activity   : int;
     mutable neg_activity   : int;
(* we try to change the lit value if *)
(* activity diff is greater than change_acitivity_limit *)
     mutable change_activity_limit : int; 
   } 


let var_entry_to_string prop_var_entry = 
  let var_solver_val_str =
    match prop_var_entry.prop_var with
    |Def(prop_var) ->
(* need to check if solver was called at all before *)
	(match prop_var_entry.truth_val with
	|Def _ -> 
	    PropSolver.lit_val_to_string (PropSolver.lit_val solver prop_var) 
	|_-> "Never checked with Solver" 
	)
    |_-> " Var is undef "
  in
  "var_id: "^(param_to_string string_of_int prop_var_entry.var_id)
  ^"; current truth_val: "
  ^(param_to_string PropSolver.lit_val_to_string prop_var_entry.truth_val)
  ^"; Solver truth val: "^(var_solver_val_str)
  ^"; \n Ground term: "^(param_to_string Term.to_string prop_var_entry.ground_term)
  ^"; Pos Activity: "^(string_of_int prop_var_entry.pos_activity)
  ^"; Neg Activity: "^(string_of_int prop_var_entry.neg_activity)

let var_entry_sel_to_string prop_var_entry = 
  try
    let clause_list_str =  
      let get_cl_str rest clause = 
	let sel_lit = Clause.get_inst_sel_lit clause in
	let sel_str = "\n Selected:  "^(Term.to_string sel_lit)^"\n" in
	let clause_str = " In clause: "^(Clause.to_string clause) in
	rest^sel_str^clause_str 
      in			       
      List.fold_left get_cl_str "" prop_var_entry.sel_clauses
    in
    (var_entry_to_string prop_var_entry)^clause_list_str
  with
    Clause.Inst_sel_lit_undef -> 
      raise (Failure "var_entry_sel_cl_to_string: Sel_lits_undef")


let empty_var_entry = 
  {
   var_id        = Undef;
   prop_var      = Undef;
   prop_neg_var  = Undef;
   prop_var_uc = Undef;
   prop_neg_var_uc = Undef;
   truth_val     = Undef;
   sel_clauses   = [];
   ground_term   = Undef;
   in_solver_sim = false;
   pos_activity  = 0;
   neg_activity  = 0;
   change_activity_limit  = !lit_activity_threshold
 }

let create_var_entry var_id ground_term = 
(* we also need to create var in solver_sim ....*)
  PropSolver.add_var_solver solver_sim var_id; 
  {
   var_id       = Def(var_id);
   prop_var     = Def(PropSolver.create_lit solver PropSolver.Pos var_id); 
   prop_neg_var = Def(PropSolver.create_lit solver PropSolver.Neg var_id);
   prop_var_uc = Def(PropSolver.create_lit_uc 
		       solver_uc 
		       PropSolver.Pos 
		       (var_id + (PropSolver.clauses_with_id solver_uc))); 
   prop_neg_var_uc = Def(PropSolver.create_lit_uc 
			   solver_uc 
			   PropSolver.Neg 
			   (var_id + (PropSolver.clauses_with_id solver_uc)));
   truth_val    = Undef;
   sel_clauses  = [];
   ground_term  = Def(ground_term);
   in_solver_sim = false;
   pos_activity  = 0;
   neg_activity  = 0;
   change_activity_limit = !lit_activity_threshold
 }


let var_table_initsize = 10001

let var_table = TableArray.create var_table_initsize empty_var_entry

let model_to_string_gen entry_to_str =
  let init_str   = "\n ------------Model-----------\n" in
  let final_str = "\n ----------END Model----------\n" in
  let main_str=
    let get_entry_str rest entry = 
      rest ^ "\n---------------------------------\n"
      ^(entry_to_str entry)^"\n" in
    TableArray.fold_left get_entry_str "" var_table  
  in 
  init_str^main_str^final_str


let model_to_string () =   model_to_string_gen var_entry_to_string

let model_sel_to_string () =  
  model_to_string_gen var_entry_sel_to_string

let clear_model () =  
  TableArray.iter 
    (function var_entry -> 
      var_entry.sel_clauses <- [];
      var_entry.pos_activity <- 0;
      var_entry.neg_activity <- 0;
      var_entry.truth_val <- Undef
    ) var_table


let clear_model_and_move_to_passive move_clause_from_active_to_passive =  
  TableArray.iter 
    (function var_entry -> 
       List.iter move_clause_from_active_to_passive var_entry.sel_clauses;
      var_entry.sel_clauses <- [];
      var_entry.pos_activity <- 0;
      var_entry.neg_activity <- 0;
      var_entry.truth_val <- Undef
    ) var_table


(* Create a new propositional variable that no term is assigned to *)
let get_new_dummy_prop_var () =

  (* Get next key in variable table *)
  let new_key = TableArray.get_next_key var_table in
  
  (* Assign empty entry for new key *)
  TableArray.assign var_table new_key empty_var_entry;
  
  (* Return new key *)
  new_key 


let get_prop_key_assign  atom = 
  try Term.get_prop_key atom
  with Term.Prop_key_undef ->
    (let new_key = TableArray.get_next_key var_table in
(* var_id > 0 *)
    let var_id  = TableArray.key_to_int new_key + 1 in
    let var_entry = create_var_entry var_id atom in
    TableArray.assign var_table new_key var_entry;
    Term.assign_prop_key new_key atom;
    (if (Term.is_ground atom) 
    then  Term.assign_prop_gr_key new_key atom
    else ());
    new_key)
    

(*  a*)
let get_prop_gr_key_assign term = 
  try Term.get_prop_gr_key term
  with Term.Prop_gr_key_undef ->
    let gr_term = 
      try Term.get_grounding term      
      with
	Term.Term_grounding_undef ->
	  let new_gr_t = Subst.grounding term_db_ref !gr_by term in 
	  Term.assign_grounding new_gr_t term;
	  new_gr_t
    in
    try 
      let new_key = Term.get_prop_gr_key gr_term in
      Term.assign_prop_gr_key new_key term;
      new_key
    with Term.Prop_gr_key_undef ->	
      let new_key = TableArray.get_next_key var_table in
(* var_id > 0 *)
      let var_id  = TableArray.key_to_int new_key + 1 in
      let var_entry = create_var_entry var_id gr_term in
      TableArray.assign var_table new_key var_entry;
      Term.assign_prop_gr_key new_key term;
      Term.assign_prop_gr_key new_key gr_term;
      Term.assign_prop_key new_key gr_term;
      new_key

(* adds literal without grounding to propositional solver and to var_table *)
let get_prop_lit_assign lit = 
  let atom = Term.get_atom lit in 
  let atom_prop_key = get_prop_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> raise (Failure "Instantiation get_prop_lit: lit is undefind")
  
(* adds literal without grounding to propositional solver and to var_table *)
let get_prop_lit_uc_assign lit = 
  let atom = Term.get_atom lit in 
  let atom_prop_key = get_prop_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var_uc
    else
     prop_var_entry.prop_var_uc 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> raise (Failure "Instantiation get_prop_lit: lit is undefind")


(*returns prop literal;  assume that prop key is def. *)
let get_prop_lit lit = 
  let atom = Term.get_atom lit in 
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> raise (Failure "Instantiation get_prop_lit: lit is undefind")
  

(*returns complementary prop literal;  assume that prop key is def. *)
    let get_prop_compl_lit lit = 
      let atom = Term.get_atom lit in 
      let atom_prop_key = Term.get_prop_key atom in
      let prop_var_entry = TableArray.get var_table atom_prop_key in
      let def_lit = 
	if (Term.is_neg_lit lit) 
	then      
	  prop_var_entry.prop_var 
	else
	  prop_var_entry.prop_neg_var 
      in
      match def_lit with 
      |Def(lit) -> lit 
      | _ -> raise (Failure "Instantiation get_prop_compl_lit: lit is undefind")
	    

let get_prop_gr_lit lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def(lit) -> lit 
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")


let get_prop_gr_compl_lit lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_var 
    else
      prop_var_entry.prop_neg_var 

  in
  match def_lit with 
  |Def plit -> 
    (* Format.eprintf 
      "Literal %s is %s in simplification solver@." 
      (Term.to_string lit) 
      (PropSolver.lit_to_string solver_sim plit); *)
    plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")


(* adds literal after grounding to propositional solver and to var_table *)
let get_prop_gr_lit_assign lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = get_prop_gr_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var 
    else
     prop_var_entry.prop_var 
  in
  match def_lit with 
  |Def plit -> plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit_assign: lit is undefind")

let get_prop_gr_lit_uc_assign lit =
  let atom = Term.get_atom lit in 
  let atom_prop_gr_key = get_prop_gr_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit = 
    if (Term.is_neg_lit lit) 
    then      
      prop_var_entry.prop_neg_var_uc 
    else
     prop_var_entry.prop_var_uc 
  in
  match def_lit with 
  |Def plit -> plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit_assign: lit is undefind")


let get_prop_gr_var_entry lit = 
  try 
    let atom           = Term.get_atom lit in
    let prop_gr_key    = Term.get_prop_gr_key atom in
    TableArray.get var_table prop_gr_key
  with 
    Term.Prop_gr_key_undef -> raise (Failure (Format.sprintf "get_prop_gr_var_entry : Term.Prop_key_undef for %s@." (Term.to_string lit)))


let get_prop_var_entry lit = 
  try 
    let atom           = Term.get_atom lit in
    let prop_key       = Term.get_prop_key atom in
    TableArray.get var_table prop_key
  with 
    Term.Prop_key_undef -> raise (Failure "get_prop_var_entry : Term.Prop_key_undef")

let get_truth_var_entry var_entry = 
  match var_entry.truth_val with	
  |Def(truth_val) -> truth_val
  |Undef ->   raise (Failure "get_truth_var_entry: truth_val is Undef\n")

let get_prop_var_var_entry var_entry =
  match var_entry.prop_var with	
  |Def(prop_var) -> prop_var
  |Undef ->   raise (Failure "get_prop_var_var_entry: prop_var is Undef\n")

let get_prop_neg_var_var_entry var_entry =
  match var_entry.prop_neg_var with	
  |Def(prop_neg_var) -> prop_neg_var
  |Undef ->   raise (Failure "get_prop_neg_var_var_entry: prop_var is Undef\n")


	

let get_lit_activity lit = 
(*  out_str ("Lit Act !\n"^(Term.to_string lit));*)
  let var_entry = get_prop_gr_var_entry lit in
  if (Term.is_neg_lit lit) 
  then var_entry.neg_activity
  else var_entry.pos_activity

let lit_activity_compare l1 l2 = 
(*  out_str ("Act Compare !\n"^(Term.to_string l1)^(Term.to_string l2));*)
  compare (get_lit_activity l1) (get_lit_activity l2)

(* get truth val of lit after grounding in stored model *)

let get_gr_lit_model_truth_val lit = 
    let var_entry = get_prop_gr_var_entry lit in 
    var_entry.truth_val
  

 (*
let selection_fun get_prop_truth clause = 
  let candidate_list = Clause.find_all get_prop_truth clause in 
  let fun_list = [Term.cmp_ground;(compose_12 (~-)lit_activity_compare); 
		  Term.cmp_sign] 
in
  list_find_max_element (lex_combination fun_list)  candidate_list
 
 
let ()=add_param_str ("Real Selection lex [-act;-num_symb]\n")
*)



(*--------------------*)
let assign_solver_assumptions lit_list = 
  let new_assumptions = 
    normalise_assumptions (List.map get_prop_lit_assign lit_list) 
  in

  let new_assumptions_uc = 
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list) 
  in

   (*
   Format.printf "New solver assumptions: @\n";

   List.iter 
     (fun l -> Format.printf "%s@\n" (Term.to_string l))
     lit_list;
   
   Format.printf "@\n@.";
   *)

 solver_assumptions_ref:= new_assumptions;
 solver_uc_assumptions_ref:= new_assumptions_uc


let assign_only_sim_solver_assumptions lit_list = 
 let new_assum =  normalise_assumptions (List.map get_prop_lit_assign lit_list) in
   (*
   Format.printf "New assumptions for simplification solver: @.";

   List.iter 
     (fun l -> Format.printf "%s@." (Term.to_string l))
     lit_list;
   *)

 only_sim_solver_assumptions_ref:= new_assum

let assign_only_norm_solver_assumptions lit_list = 
  let new_assumptions =  
    normalise_assumptions (List.map get_prop_lit_assign lit_list) 
  in
  let new_assumptions_uc =  
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list) 
  in

   (*
   Format.printf "New assumptions for satisfiability solver: @.";

   List.iter 
     (fun l -> Format.printf "%s@." (Term.to_string l))
     lit_list;
   
   Format.printf "@.";
   *)

   only_norm_solver_assumptions_ref:= new_assumptions;
   solver_uc_assumptions_ref:= new_assumptions_uc

let assign_adjoint_preds preds =
  adjoint_preds:=preds



(*-------------Add clause to solver----------------*)

(*----- Simpifications of Propositional  clauses before adding to SAT -----*)

let prop_norm_order pl1 pl2 = 
  let cmp = 
    (compare (PropSolver.lit_var solver pl1) (PropSolver.lit_var solver pl2)) 
  in
  if cmp = cequal 
  then 
    compare (PropSolver.lit_sign solver pl1) (PropSolver.lit_sign solver pl2) 
  else
    cmp

(* we assume that the list is sorted so lits with the same atoms are together*)
exception PropTaut
let rec prop_remove_dupl_taut plit_list = 
  match plit_list with 
  |h1::h2::tl -> 
      if h1==h2 
      then prop_remove_dupl_taut (h2::tl) 
      else 
	if ((PropSolver.lit_var solver h1) = (PropSolver.lit_var solver h2))
	then 
	  raise PropTaut (* if h1 h2 would have the same sign then h1==h2*)
	else (h1::(prop_remove_dupl_taut (h2::tl)))
  |[h] -> [h]
  |[]  -> []


(* we keep all prop clauses in a trie (after normalisation) *)
 
module PropTrieKey =
  struct
    type t      = PropSolver.lit
    let compare = prop_norm_order 
  end
 
module PropTrieM = Trie_func.Make(PropTrieKey)

let prop_trie_ref = ref (PropTrieM.create ())

let rec prop_lit_list_is_subsumed lit_list  =
  try 
    let _ = (PropTrieM.long_or_in lit_list !prop_trie_ref) in 
    true
  with
    Not_found -> 
      (match lit_list with 
      |l::tl ->  
	  prop_lit_list_is_subsumed tl
      |[] -> false
      )  

let rec pp_prop_lit_list ppf = function 
  | [] -> ()
  | [e] -> Format.fprintf ppf "%a" (PropSolver.pp_lit solver) e
  | e::tl -> 
    Format.fprintf ppf "%a " (PropSolver.pp_lit solver) e; 
    pp_prop_lit_list ppf tl

let rec pp_prop_lit_list_list ppf = function 
  | [] -> ()
  | [e] -> Format.fprintf ppf "%a" pp_prop_lit_list e
  | e::tl -> 
    Format.fprintf ppf "%a@\n" pp_prop_lit_list e; 
    pp_prop_lit_list_list ppf tl

(* to do: in the trie we can not add short list, but this would be useful...*)
let add_to_prop_trie prop_lit_list =
  try
    prop_trie_ref:= PropTrieM.add prop_lit_list prop_lit_list !prop_trie_ref
  with

  (* Discard clause if it subsumes an existing clause *)
  |Trie_func.Trie_add_short_kyelist  -> 

    (* Format.eprintf 
      "Clause %a backward subsumes in propositional trie, skipped@."
      pp_prop_lit_list prop_lit_list; *)
    
    (* Format.eprintf
      "Clauses in trie:@\n%a@."
      pp_prop_lit_list_list
      (PropTrieM.all_elem 
	 (PropTrieM.find_short prop_lit_list !prop_trie_ref)) *)
    ()
      
  (* These won't happen if key has been checked before with
     long_or_in *)
  |Trie_func.Trie_add_leaf_extension -> ()
  |Trie_func.Trie_add_already_in     -> () 


exception PropSubsumed

(* We can return an empty list, this must be caught by the caller and
   must raise exception PropSolver.Unsatisfiable there. This is
   because the unsat core solver must also have the empty clause and
   it must be associated with some first-order clause only the caller
   knows. *)
let simplify_prop_lit_list prop_lit_list = 
  let sorted = List.sort prop_norm_order  prop_lit_list in 
  let new_list = prop_remove_dupl_taut sorted in
  if new_list = [] 
  then 
    ( 

      (* Format.eprintf "Clause simplified to empty clause in simplify_prop_lit_list@."; *)
      
    (* Check this in add_clause_to_solver, because empty clause must
       be added to unsat core solver and mapped to first-oder clause
       there *)
    (* raise PropSolver.Unsatisfiable *)
      []
    )
  else
    if (prop_lit_list_is_subsumed new_list)
    then 
      raise PropSubsumed
    else 
      new_list

(*      prop_lit_list*)

(*
let norm_add_to_prop_solver solver prop_lit_list = 
  try 
    (PropSolver.add_clause solver (normalise_prop_lit_list prop_lit_list);
     num_in_prop_solver:=!num_in_prop_solver+1)
  with 
    PropTaut -> ()
*) 

(*------------------- Answers -----------*)
(* assume ~answer(..)\bot                              *)
(* when unsat minimise set of ~answer(...)\bot and output *)
(* disjunction of corresponding answers, \bot -> X0)  *)
(* Later add more general answers: vars mapped to constants  *)
(* for this we need rewrite normalisation so unifed literals would be the same *)
(* or since there are only one answer literal in a clause, make them first in the clause and rename *)



module PropHashKey = 
  struct
    type t    = PropSolver.lit
    let equal = (=)
    let hash  = PropSolver.lit_var solver
  end 

(* will have several uses*)
module PropHash = Hashtbl.Make(PropHashKey)

(* maps prop assump -> fo assumpt *)

let answer_assumptions_table = ref (PropHash.create 41)

(* we negate the grounding of the answer lit before adding to the ground sovler assumtions *)
(* we use (answer \bot) at the moment *)
let add_answer_assumption answer =
  let answer_bot =  Term.get_grounding answer in
  let gr_compl_answer =  get_prop_gr_compl_lit answer_bot in 
  if (PropHash.mem !answer_assumptions_table gr_compl_answer) 
  then ()
  else
    begin
      PropHash.add !answer_assumptions_table gr_compl_answer answer_bot;
      answer_assumptions_ref:= gr_compl_answer::(!answer_assumptions_ref)
    end

(* we assume that the solver is unsat under answer assumptions and we minimise them*)
let minimise_answers () = 
  let rec min_unsat_subs' needed =     
    match !answer_assumptions_ref with 
    |h::tl -> 
	answer_assumptions_ref := needed@tl;	
	
(* debug *)
(*	out_str "Assumptions: ";
	let f ass = 
	  let answer_atom = PropHash.find !answer_assumptions_table ass in
	  out_str ((Term.to_string answer_atom)^",");
	in
	List.iter f !answer_assumptions_ref;
	out_str "\n";
*)
(* end debug *) 
	begin
	  match (solve ()) with
	  |PropSolver.Unsat -> 
	      (
	       answer_assumptions_ref:=tl;
	       PropHash.remove  !answer_assumptions_table h;
	       min_unsat_subs' needed
	      )
	  |PropSolver.Sat ->
	      (
	       answer_assumptions_ref:=tl;
	       min_unsat_subs' (h::needed)
	      )
	end
    |[] -> needed
  in
  let needed =  min_unsat_subs' [] in 
  answer_assumptions_ref:=needed
      

(* replace bot with X0 in term *)

let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let term_var var = TermDB.add_ref (Term.create_var_term var) term_db_ref

	
let bot_to_var term =
  let x0 =  term_var (Var.get_first_var ()) in
  let rec f t = 
    match t with 
    |Term.Fun(symb,args,_) ->
	if (symb == Symbol.symb_bot) 
	then 
	  x0
	else
	  (let new_args = Term.arg_map f args in
	  add_fun_term symb (Term.arg_to_list new_args)
	  )
    |_-> t
  in
  f term


(* if we two answers answer_1 anser2,.. are unifiable *)
(* then we can remove one of them and apply unif to the rest of lit list *)

(*  let bound_a_list = List.map (fun a -> (1,a)) a_list in*)

let bound_list b list =  List.map (fun a -> (b,a)) list
let unbound_list list = List.map (fun (_,a) -> a) list

let reduce_answer_bl_list bl bound_a_list =
  let rec reduce_answer_bl_list' bl tried rest = 
    match rest with 
    |h::tl -> 
	begin
	  try 
	    let mgu =  Unif.unify_bterms bl h in
	    Some(mgu)
	  with 
	    Unif.Unification_failed ->
	      reduce_answer_bl_list' bl (h::tried) tl	  	      
	end
    |[] -> None
  in
  reduce_answer_bl_list' bl [] bound_a_list


(* very inefficient but should be ok for reducing small disjunctive answers*)
let rec reduce_answer_list a_list =
  let ba_list = bound_list 1 a_list in   
  let rec reduce_answer_list' non_unifable rest =
    match rest with 
    |h::tl ->
	begin 
	  match (reduce_answer_bl_list h tl) with
	  |Some (mgu) -> 
	      let new_a_list = 
		SubstBound.apply_bsubst_btlist term_db_ref mgu	(non_unifable@tl) 
	      in 
	      reduce_answer_list new_a_list
	  |None -> 
	      reduce_answer_list' (h::non_unifable) tl
	    
	end
    |[] -> 
	non_unifable
  in
 reduce_answer_list' [] ba_list 



let get_answer () = 
  minimise_answers ();
  let answer_bot_list =
      PropHash.fold (fun  _ answer_bot rest -> answer_bot::rest) 
      !answer_assumptions_table []
  in
  let answer_list = List.map bot_to_var answer_bot_list in
  let reduced_bound_list = reduce_answer_list answer_list in
  unbound_list reduced_bound_list


let out_answer_stream s = 
  let answer_list =  get_answer () in
  let answer_atom_to_stream stream answer = 
    let args = Term.arg_to_list (Term.get_args answer) in
    stream.stream_add_char '[';
    list_to_stream stream Term.to_stream args ",";
    stream.stream_add_char ']'
  in
  let answer_list_to_stream a_list = 
    if ((List.length a_list) > 1) 
    then
      begin
	s.stream_add_char '(';
	list_to_stream s answer_atom_to_stream a_list "|";
	s.stream_add_char ')';
      end
    else
      begin
	if ((List.length a_list) =1)
	then
	  answer_atom_to_stream s (List.hd a_list)
	else ()
      end
  in
  s.stream_add_str "% SZS answers Tuple [";
  answer_list_to_stream answer_list; 
  s.stream_add_str "]";
  s.stream_add_str " for ";
  list_to_stream s (fun stream string -> stream.stream_add_str string) !current_options.problem_files ",";
  s.stream_add_str "\n"

    
let out_answer () =  out_answer_stream stdout_stream

(*-------End answers----------------------------------*)

(*
(* A clause in the sat solver as a list of literals *)
module PropClause = 
struct
  
  (* An arbitrarily sorted list of propositional literals *)
  type t = PropSolver.lit list 
      
  (* Use equality on lists *)
  let equal = (=)

  (* Use polymorphic hash function on atoms, since no clause in the
     solver contains a literal and its negation *)
  let hash clause = 
    Hashtbl.hash (List.map (PropSolver.lit_var solver) clause)
      
end 
  
(* A hash table over propositional clauses *)
module PropClauseHashtbl = Hashtbl.Make(PropClause)
*)

(*

let add_clause_to_solver_and_solver_uc 
    add_clause_to_solver 
    add_clause_to_solver_uc 
    clause
    prop_clause 
    prop_clause_uc =

  (

    try 
      
      (* Add new clause to solver *)
      add_clause_to_solver prop_clause 
	
    (* Continue on unsatisfiable, we must add clause also to unsat
       core solve, which raises the same exception *)
    with PropSolver.Unsatisfiable ->
      
      (* Format.eprintf 
	"Unsatisfiable with added clause@." *)

      ()

  );
  
  (* Add new clause to unsat core solver and get id  *)
  let clause_id = 
    add_clause_to_solver_with_id prop_clause_uc
  in

  (

    match clause_id with 
	
      (* Clause was discarded in solver *)
      | None -> ()

      (* Clause has an ID in solver *)
      | Some i -> 
	
	(

	  (* Format.eprintf 
	    "Added clause to UC solver as %d:@\n%s@."
	    i
	    (Clause.to_string clause); *)

	  (* Map ID in solver to first-order clause *)
	  Hashtbl.add solver_uc_clauses i clause
	    
	)
  )

  

*)


let rec pp_prop_lit_pair_list ppf = function 
  | [] -> ()
  | [(p, q)] -> 
    Format.fprintf ppf 
      "(%a, %a)" 
      (PropSolver.pp_lit solver) p
      (PropSolver.pp_lit solver) q
  | (p, q)::tl -> 
    Format.fprintf ppf 
      "(%a, %a)" 
      (PropSolver.pp_lit solver) p 
      (PropSolver.pp_lit solver) q; 
    pp_prop_lit_pair_list ppf tl

(* adds both versions of the clauses before and after grounding *)
(* first version is used for simplifications *)
exception PropImplied

let add_clause_to_solver clause =

  (* Skip if clause already in solver *)
  if Clause.get_bool_param Clause.in_prop_solver clause then 

    (
(*
       Format.printf
	"Clause %a is already in solver, skipping@."
	Clause.pp_clause clause 
*)
    )

  else 
    
    (
      (*
       Format.printf
	"Adding clause %a to solver@."
	Clause.pp_clause clause; 
*)

      (* Dump propositional clause *)
      if !current_options.dbg_dump_prop_clauses then
	Format.fprintf 
	  (get_prop_clauses_dump_formatter ())
	  "c First-order clause %a@."
	  Clause.pp_clause clause;
	  
      (* Mark clause as added to the solver *)
      Clause.set_bool_param true Clause.in_prop_solver clause;

      (* Get literals from clause *)
      let lits = Clause.get_literals clause in
      
      (* Map clause literals to grounded propositional literals *)
      let prop_gr_lit_list = 
	List.map get_prop_gr_lit_assign lits 
      in

      (* Dump propositional clause *)
      if !current_options.dbg_dump_prop_clauses then
	Format.fprintf 
	  (get_prop_clauses_dump_formatter ())
	  "c Grounded to clause %a@."
	  (PropSolver.pp_lit_list_dimacs solver) prop_gr_lit_list;
	  
      (* Map clause literals to grounded propositional literals in
	 unsat core solver *)
      let prop_gr_lit_uc_list = 
	List.map get_prop_gr_lit_uc_assign lits 
      in

      (* Make association list of literals in satsisfiability solver to
	 literals in unsat core solver
	 
	 This association list is only needed locally in this function
	 to convert the possibly simplifed propositional clause in the
	 satisfiability solver to a clause in the unsat core solver. *)
      let prop_gr_lit_to_uc = 
	List.combine prop_gr_lit_list prop_gr_lit_uc_list 
      in

      (* Map clause literals to propositional literals grounded by
	 variable *)
      let prop_lit_list = List.map get_prop_lit_assign lits in 

      (* Map clause literals to propositional literals grounded by
	 variable in unsat core solver *)
      let prop_lit_uc_list = 
	List.map get_prop_lit_uc_assign lits 
      in

      (* Make association list of literals in satsisfiability solver to
	 literals in unsat core solver

	 This association list is only needed locally to convert the
	 possibly simplifed propositional clause in the satisfiability
	 solver to a clause in the unsat core solver *)
      let prop_lit_to_uc = 
	List.combine prop_lit_list prop_lit_uc_list 
      in
      
      (* Mark propositional variables as in solver *)
      let f lit = 
	let var_entry = get_prop_var_entry lit in
	var_entry.in_solver_sim <- true in
      List.iter f lits;
      
      (*  Commented *)
      (* Propositional implication  is not compatible with prop_subsumtion:*)
      (* an instance of a subsumed clause can imply an instance of the new clause*)
      (*  let lits_in_solver_sim =
	  let f lit = 
	  let var_entry = get_prop_var_entry lit in
	  var_entry.in_solver_sim in
	  List.find_all f lits in
	  let compl_lit_list = List.map get_prop_compl_lit lits_in_solver_sim in 
	  num_of_fast_solver_calls:=!num_of_fast_solver_calls+1;
	  match (fast_solve solver_sim compl_lit_list)
	  with 
	  | PropSolver.FUnsat -> 
	  ((*num_prop_implied:=!num_prop_implied+1; *)
      (*       out_str ("Prop Implied: "^(Clause.to_string clause)^"\n");*)
	  raise PropImplied)
	  |PropSolver.FSat | PropSolver.FUnknown -> *)
      (* debug*) 
      (*let str = list_to_string PropSolver.lit_to_string prop_gr_lit_list ";" in
	out_str_debug ("Clause: "^(Clause.to_string clause)^"\n"
	^"Prop Clause:"^str^"\n");*)
      (*  debug *)
      (*  out_str ("Old Clause: "^(PropSolver.lit_list_to_string prop_gr_lit_list)^"\n");*)
      (* end Commented*) 

      (

	try 
	  
	  (* Propositionally simplify list of grounded literals *)
	  let simpl_gr_lit_list = 
	    simplify_prop_lit_list prop_gr_lit_list
	  in 
	  
	  (* Catch simplification to empty clause *)
	  if simpl_gr_lit_list = [] then

	    (
	      
	      (* Add empty clause to unsat core solver and get id *)
	      let clause_id = 
		PropSolver.add_clause_with_id solver_uc None []
	      in
	      
	      (
		
		match clause_id with 
		    
		  (* Clause was discarded in solver *)
		  | None -> ()
		    
		  (* Clause has an ID in solver *)
		  | Some i -> 
		    
		    (
		      
		      (* Map ID in solver to first-order clause *)
		      Hashtbl.add solver_uc_clauses i clause;

		      (* Assign ID to clause 

			 Clauses are only added to the solver once,
			 therefore IDs are not reassigned *)
		      Clause.assign_prop_solver_id clause i
			
		    )
	      );
	      
	      (* Raise exception only after empty clause is in unsat
		 core solver *)
	      raise PropSolver.Unsatisfiable
		
	    );

	  (* Map literals in simplified clause in satisfiability solver
	     to literals in unsat core solver
	     
	     Use short association list of grounded literals to
	     grounded literals in unsat core solver to remove the
	     literals eliminated by propositional subsumption from the
	     clause to be added to the unsat core solver *)
	  let simpl_gr_lit_uc_list = 
	    List.map 
	      (function e -> List.assoc e prop_gr_lit_to_uc) 
	      simpl_gr_lit_list 
	  in

	  (* Add simplified clause to unsat core solver and get id
	     
	     Must do this first, since adding a clause to
	     satisfiability solver can be immediately unsatisfiable,
	     but not in unsat core solver *)
	  let clause_id = 
	    PropSolver.add_clause_with_id solver_uc None simpl_gr_lit_uc_list
	  in
	  
	  (

	    match clause_id with 
		
	      (* Clause was discarded in solver *)
	      | None -> ()
		
	      (* Clause has an ID in solver *)
	      | Some i -> 
		
		(
		  
		  (* Map ID in solver to first-order clause *)
		  Hashtbl.add solver_uc_clauses i clause;

		  (* Assign ID to clause 
		     
		     Clauses are only added to the solver once,
		     therefore IDs are not reassigned *)
		  Clause.assign_prop_solver_id clause i
		    
		)
	  );

	  (* Dump propositional clause *)
	  if !current_options.dbg_dump_prop_clauses then
	    Format.fprintf 
	      (get_prop_clauses_dump_formatter ())
	      "c Added with ID %d@\n%a@."
	      (match clause_id with None -> -1 | Some i -> i)
	      (PropSolver.pp_lit_list_dimacs solver) simpl_gr_lit_list;
	  
	  (* Add simplified clause to satisfiability solver
	     
	     Clause must already be in unsat core solver, since this may
	     raise the PropSolver.Unsatisfiable exception *)
	  PropSolver.add_clause solver simpl_gr_lit_list;
	  
	  (* Add simplified clause to simplification solver *)
	  PropSolver.add_clause solver_sim simpl_gr_lit_list;

	  (* Add simplified clause to propositional trie *)
	  add_to_prop_trie simpl_gr_lit_list;
	  
	  (* Increment counter for number of propositional clauses *)
	  incr_int_stat 1 prop_num_of_clauses
	    
	with 
	    
	  (* Clause is a tautology or was propositionally simplified *)
	  | PropTaut
	  | PropSubsumed -> 
	    
	    (* Increment counter for simplified clauses *)
	    incr_int_stat 1 prop_preprocess_simplified
	      
      );
      
      (

	try 
	  
	  (* Propositionally simplify list of literals grounded by variable *)
	  let simpl_lit_list = simplify_prop_lit_list prop_lit_list in 
	  
	  (* Catch simplification to empty clause *)
	  if simpl_lit_list = [] then

	    (
	      
	      (* Add empty clause to unsat core solver and get id *)
	      let clause_id = 
		PropSolver.add_clause_with_id 
		  solver_uc 
		  (Clause.get_prop_solver_id clause)
		  []
	      in
	      
	      (
		
		match clause_id with 
		    
		  (* Clause was discarded in solver *)
		  | None -> ()
		    
		  (* Clause has an ID in solver *)
		  | Some i -> 
		    
		    (
		      
		      (* Map ID in solver to first-order clause *)
		      Hashtbl.add solver_uc_clauses i clause
			
		    )
	      );
	      
	      (* Raise exception only after empty clause is in unsat
		 core solver *)
	      raise PropSolver.Unsatisfiable
		
	    );


	  (* Map literals in simplified clause in simplification solver to
	     literals in unsat core solver
	     
	     Use short association list of literals grounded by variable to
	     literals grounded by variable in unsat core solver to remove
	     the literals eliminated by propositional subsumption from the
	     clause to be added to the unsat core solver *)
	  let simpl_lit_uc_list = 
	    List.map 
	      (function e -> List.assoc e prop_lit_to_uc) 
	      simpl_lit_list 
	  in
	  
	  (* Add simplified clause to unsat core solver and get id  
	     
	     Must do this first, since adding a clause to satisfiability
	     solver can be immediately unsatisfiable, but not in unsat
	     core solver *)
	  let clause_id = 
	    PropSolver.add_clause_with_id 
	      solver_uc 
	      (Clause.get_prop_solver_id clause)
	      simpl_lit_uc_list 
	  in
	  
	   (

	    match clause_id with 
		
	      (* Clause was discarded in solver *)
	      | None -> ()
		
	      (* Clause has an ID in solver *)
	      | Some i -> 
		
		(
		  
		  (* Map ID in solver to first-order clause *)
		  Hashtbl.add solver_uc_clauses i clause;

		  (* Assign ID to clause 
		     
		     Clauses are only added to the solver once,
		     therefore IDs are not reassigned *)
		  (match Clause.get_prop_solver_id clause with
		    | None -> Clause.assign_prop_solver_id clause i
		    | Some _ -> ())
		    
		)
	  );

	  (* Add simplified clause to simplification solver *)
	  PropSolver.add_clause solver_sim simpl_lit_list;
	  
	  (* Add simplified clause to propositional trie *)
	  add_to_prop_trie simpl_lit_list; 
	  
	  (* Increment counter for number of propositional clauses *)
	  incr_int_stat 1 prop_num_of_clauses
	    
	with 
	    
	  (* Clause is a tautology or was propositionally simplified *)
	  | PropTaut 
	  | PropSubsumed -> 
	    
	    (* Increment counter for simplified clauses *)
	    incr_int_stat 1 prop_preprocess_simplified

      );
	    
      (*----- add answer assumtions *)
      
      let add_answer_lit lit = 
	   (* answer lits are assumed to occur only positively*)
	if ((Term.get_top_symb lit) == Symbol.symb_answer)
	then
	  add_answer_assumption lit 
	else ()
      in
      if !answer_mode_ref 
      then 
	List.iter add_answer_lit lits
      else ()
	
	   
    )


(*------------------ end add clause to solver -----------------------*)

(*----------------- change selection -----------------------------*)

let pp_truth_val ppf = function
  | Undef -> Format.fprintf ppf "Undef"
  | Def PropSolver.True -> Format.fprintf ppf "True"
  | Def PropSolver.False -> Format.fprintf ppf "False"
  | Def PropSolver.Any -> Format.fprintf ppf "Any"
  

(* Warning both A and neg A can be consitent with the solver *)
(* (if the solver returns Any) *)
(* after grounding*)
let consistent_with_solver lit = 
  (* Format.eprintf
    "consistent_with_solver %a@."
    Term.pp_term lit; *)
  let var_entry      = get_prop_gr_var_entry lit in
  let prop_var       = get_prop_var_var_entry var_entry in
  let var_truth_val  = PropSolver.lit_val solver prop_var in
  if var_truth_val = PropSolver.Any 
  then 
    ( (*Format.eprintf
       "Literal %s is consistent with solver, since model value is Any@."
       (Term.to_string lit);  *)
     true)
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then
      ( (* Format.eprintf
	 "Literal %s is consistent with solver, since model value is True@."
	 (Term.to_string lit); *)
       true)
    else 
      ( (* Format.eprintf
	 "Literal %s is not consistent with solver, since model value is False@."
	 (Term.to_string lit); *)
       false)

(* without grounding*)
let consistent_with_solver_lit  lit = 
  let var_entry      = get_prop_var_entry lit in
  let prop_var       = get_prop_var_var_entry var_entry in
  let var_truth_val  = PropSolver.lit_val solver prop_var in
  if var_truth_val = PropSolver.Any 
  then true
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then true
    else false

(* after grounding *)
let consistent_with_model lit = 
  let var_entry      = get_prop_gr_var_entry lit in
(*    let var_truth_val  = get_truth_var_entry var_entry in*)
  match var_entry.truth_val with
  |Def(var_truth_val) ->
      if (var_truth_val = PropSolver.Any)
      then  
	((*out_str "consistent_with_model: Any\n "; *)
	  (* Format.eprintf
	    "Literal %s is consistent with model, since model value is Any@."
	    (Term.to_string lit); *)
	  true )
      else
      let is_neg = Term.is_neg_lit lit in    
      if
	((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
	((var_truth_val = PropSolver.False) & is_neg)
      then 
 	((* Format.eprintf
	   "Literal %s is consistent with model, since model value is True@."
	   (Term.to_string lit); *)
	 true)
      else
  	((* Format.eprintf
	   "Literal %s is not consistent with model, since model value is False@."
	   (Term.to_string lit); *)
	 false)
  | Undef -> 
    ((* Format.eprintf
       "Literal %s is consistent with model, since model value is Undef@."
       (Term.to_string lit); *)
     true)



let get_lit_activity lit = 
  let var_entry = get_prop_var_entry lit in
  if (Term.is_neg_lit lit) then 
    var_entry.neg_activity
  else
    var_entry.pos_activity

let activity_condition lit = 
  let activity = get_lit_activity lit in
  ((activity < ((get_val_stat inst_max_lit_activity) lsr 2)) 
 || 
   (activity < !lit_activity_threshold)
)
  

let  consistent_with_model_activity  lit = 
(* remove true later*)
  if  (activity_condition lit)
  then consistent_with_model lit
  else false
      
let  consistent_with_solver_activity lit = 
(* remove true later*)
    if (activity_condition lit)
    then consistent_with_solver lit
    else false



(* without grounding*)
let consistent_with_model_lit lit = 
  let var_entry      = get_prop_var_entry lit in
  let var_truth_val  = get_truth_var_entry var_entry in
  if (var_truth_val = PropSolver.Any)
  then true 
  else
    let is_neg = Term.is_neg_lit lit in    
    if
      ((var_truth_val = PropSolver.True)  & (not is_neg)) ||  
      ((var_truth_val = PropSolver.False) & is_neg)
    then true
    else false
  
    
(* move_lit_from_active_to_passive is a function which is a parameter here *)
(* and is defined in instantiation.ml *)

(* returns true if it can preserve model (solver is run under entry assumption) *)
(* otherwise return false *)

let preserve_model_solver move_lit_from_active_to_passive var_entry =
  let prop_var      = get_prop_var_var_entry var_entry in
  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in
  let new_truth_val = PropSolver.lit_val solver prop_var in
(*  out_str ("Var entry:"^(var_entry_to_string solver var_entry)^"\n");
  out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with 
  |Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any) 
      then 
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(var_entry.truth_val <- Def(new_truth_val);
(*debug check *)
(*	 (if var_entry.sel_clauses !=[] 
	 then out_str "preserve_model_solver: sel_clauses should be empty \n");
*)
	 true)
      else
	if (old_truth_val = new_truth_val) || (new_truth_val = PropSolver.Any)
	then true
	else 
	  (
	    let assumption = 
	      if  old_truth_val = PropSolver.True 
	      then prop_var
	      else prop_neg_var 
	    in	   
	    ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	     match(solve_assumptions solver [assumption]) 
	     with 
	     | PropSolver.Sat -> true
	     | PropSolver.Unsat (*| PropSolver.FUnknown*) ->
		( (*out_str "Prop unsat \n"; *)
		  let new_truth_val = PropSolver.lit_val solver prop_var in
		  var_entry.truth_val <- Def(new_truth_val);
		  let move_cl_from_active_to_passive clause =
		   if  (Clause.get_bool_param Clause.in_active clause) 
 		   then 
		     (let sel_lit = Clause.get_inst_sel_lit clause in
		     (* moves all clauses indexed by sel_lit *)
                    move_lit_from_active_to_passive sel_lit)
                   else ()
		  in
		 List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
		  var_entry.sel_clauses <- [];
 
		(* out_str ("Preserve Model: Unsat: "
			  ^"Assum: "^(PropSolver.lit_to_string  assumption)^"  "
			 ^(var_entry_to_string solver var_entry)^"\n");*)
		   
(*		 (match (solve ())
		 with PropSolver.Unsat -> raise Unsatisfiable
		 |PropSolver.Sat -> ());*)
                 
		 false)
	    ))

  |Undef -> 
      (var_entry.truth_val <- Def(new_truth_val); 
       true)
(*with Not_found -> failwith "Nor_found here"*)


(* if model value is  defferent from solver then chage the model value *)
let change_model_solver  move_lit_from_active_to_passive var_entry =
  let prop_var      = get_prop_var_var_entry var_entry in
(*  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in*)
  let new_truth_val = PropSolver.lit_val solver prop_var in
(*  out_str ("Var enty:"^(var_entry_to_string solver var_entry)^"\n");
  out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with 
  |Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any) 
      then 
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(	 
(*debug*)
	 (* (if var_entry.sel_clauses !=[] 
	 then out_str "change_model_solver: sel_clauses should be empty \n");*)
	 var_entry.truth_val <- Def(new_truth_val)) 	
      else
	if (old_truth_val = new_truth_val) (* || (new_truth_val = PropSolver.Any) *)
	then ()
	else 
	  (
(*	   out_str ("Change_model_solver: "^
		    (var_entry_to_string var_entry)^"\n");*)	  	 
	     var_entry.truth_val <- Def(new_truth_val);
	     let move_cl_from_active_to_passive clause =
	       if  (Clause.get_bool_param Clause.in_active clause) 
	       then 
		 (let sel_lit = Clause.get_inst_sel_lit clause in
	     (*  out_str ("Change_model in Active: "^(Clause.to_string clause)^"\n");*)
	       (* moves all clauses indexed by sel_lit *)
		 move_lit_from_active_to_passive sel_lit
		 )
	       else ()
	     in
	     List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
	     var_entry.sel_clauses <- []
	  )	  

  |Undef -> 
      var_entry.truth_val <- Def(new_truth_val)

(* auxilary function for below, apply only if lit is consitent with the model!*)
       
let ass_if_consistent lit clause= 
  let var_entry = get_prop_gr_var_entry lit in   
  if (get_truth_var_entry var_entry = PropSolver.Any)
  then 
    (
(*debug check *)
(*
      (if var_entry.sel_clauses !=[] 
       then Format.eprintf "ass_if_consistent: sel_clauses should be empty@.");
*)
     var_entry.sel_clauses <- [clause];
     if (Term.is_neg_lit lit)
     then var_entry.truth_val <- Def(PropSolver.False)
     else var_entry.truth_val <- Def(PropSolver.True))
  else    
    var_entry.sel_clauses <- clause::(var_entry.sel_clauses)
(* we assume that the clause is from passive and therefore *)
(* not assigned in to any of var_entry.sel_clauses         *)
(* we try to keep the old selection                        *)
(*
let find_nex_true_lit 
*)

let remove_undef_model clause = 
  (* Format.eprintf 
    "remove_undef_model %a@."
    Clause.pp_clause clause; *)
  let remove_undef_lit lit = 
    (* Format.eprintf 
      "remove_undef_lit %a@."
      Term.pp_term lit; *)
    let var_entry = get_prop_gr_var_entry lit in
    match var_entry.truth_val with 
    |Def(PropSolver.Any)|Undef ->
        (* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(let prop_var  = get_prop_var_var_entry var_entry in
	let new_truth_val = PropSolver.lit_val solver prop_var in
	(* Format.eprintf 
	  "Changing model for atom %s from %a to %a@."
	  (Term.to_string (Term.get_atom lit))
	  pp_truth_val var_entry.truth_val
	  pp_truth_val (Def new_truth_val); *)
	var_entry.truth_val <- Def(new_truth_val))
    | _ -> ()
      (* Format.eprintf 
	"Keeping model for atom %s as %a@."
	(Term.to_string (Term.get_atom lit))
	pp_truth_val var_entry.truth_val *)
  in 
  Clause.iter remove_undef_lit clause
	


exception Sel_Changed  
exception Solver_Sel
let rec selection_renew_model move_lit_from_active_to_passive selection_fun clause =  

  (* Format.eprintf 
    "selection_renew_model for clause %s@."
    (Clause.to_string clause); *)

(*  out_str (" selection_renew clause:  "^(Clause.to_string clause)^"\n");*)
(*
  let accord lit = 
    let var_entry     = get_prop_gr_var_entry lit in
   let _= model_accords_solver solver var_entry in () in
  Clause.iter accord clause;          *)
(* do not try, it will cycle!
  let preserve_mod lit = 
    let var_entry = get_prop_gr_var_entry lit in
    let _= preserve_model_solver move_lit_from_active_to_passive solver var_entry in () in
  Clause.iter preserve_mod clause; *)
  try
    let sel_lit       = Clause.get_inst_sel_lit clause in    
    let sel_var_entry = get_prop_gr_var_entry sel_lit in
    if 
      (consistent_with_model sel_lit)
    then     
      if 
	(preserve_model_solver move_lit_from_active_to_passive sel_var_entry)
      then 
	((* Format.eprintf "Selection is consistent and can be preserved@."; *)
	 ass_if_consistent sel_lit clause)
      else    
	((* Format.eprintf "Selection is consistent but cannot be preserved@."; *)
	 raise Sel_Changed)
    else 
      ((* Format.eprintf "Selection is not consistent@."; *)
       raise Sel_Changed)
  with
      Sel_Changed | Clause.Inst_sel_lit_undef ->
	(
	 try 	   
	  (  
	     remove_undef_model clause;
	   (*  out_str ("----------------------------\n");
	     out_str ("Try consist with Model:");
	     let out_entry lit = 
	       let var_entry     = get_prop_gr_var_entry lit in
	       out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			^(var_entry_to_string var_entry)^"\n"
			^"Consist_with_Model: "
			^(string_of_bool (consistent_with_model lit))^"\n");
	     in Clause.iter out_entry clause; *)

	     let model_sel_lit = 
	       selection_fun consistent_with_model_activity clause in
(*	     let model_sel_lit = 
	       selection_fun consistent_with_model clause in *)
(*             out_str ("Consist_model: "^(Term.to_string model_sel_lit)^"\n");*)
	     let model_sel_var_entry  = get_prop_gr_var_entry model_sel_lit in
	       if  (preserve_model_solver move_lit_from_active_to_passive model_sel_var_entry) then 
		 ((*change_model_solver model_sel_var_entry;*)
		  Clause.assign_inst_sel_lit model_sel_lit clause;
		  ass_if_consistent model_sel_lit clause;
(*		  out_str ("preserve model:  "^
			   (var_entry_to_string model_sel_var_entry)^"\n");
		  out_str ("----------------------------\n")*)
		 )
	       else 
(* optional change_model*)
		 ( 
		  change_model_solver move_lit_from_active_to_passive model_sel_var_entry;
		  raise Solver_Sel)
	   )    
	 with Not_found | Solver_Sel  ->	   
	   try (
(*debug*)
(*	     out_str ("----------------------------\n");
	     out_str ("No consist with Model:");
	     let out_entry lit = 
	       let var_entry     = get_prop_gr_var_entry lit in
	       out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			^(var_entry_to_string  var_entry)^"\n"
                        ^"Consist_with_Model: "
                        ^(string_of_bool (consistent_with_model lit))^"\n");
	     in Clause.iter out_entry clause;*)

	     let solver_sel_lit = 
	       selection_fun consistent_with_solver_activity clause in	  
	     let solver_sel_var_entry  = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
      (*     out_str "Change here \n";*)
(*	     out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
		     ^"Sel_lit entry: "
		     ^(var_entry_to_string  solver_sel_var_entry));*)
	     Clause.assign_inst_sel_lit solver_sel_lit clause; 
	     ass_if_consistent solver_sel_lit clause
(*	     out_str ("----------------------------\n");*)
	   )
	   with Not_found -> 
	     ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	      match (solve ()) with 
	     |PropSolver.Unsat -> 
	       ( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_model@."; *)
		raise PropSolver.Unsatisfiable)
	     |PropSolver.Sat   ->

		   let new_solver_sel_lit = 
		     try 
		     selection_fun consistent_with_solver clause 
		     with 
		       Not_found -> 
			 ( out_str ("\n Selection is not found for clause: "
				    ^(Clause.to_tptp clause)^"\n");
			   raise (Failure "selection_renew_model"))

		   in	  
		   let new_solver_sel_var_entry  = 
		     get_prop_gr_var_entry new_solver_sel_lit in
(*		 out_str "\n Change here!!!!\n";*)
		   change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
(*		 out_str ("Solver select:"^
			  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
			  ^"Sel_lit entry: "
			  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
		   Clause.assign_inst_sel_lit new_solver_sel_lit clause; 
		   ass_if_consistent new_solver_sel_lit clause
		
	     )
	)

(*
exception Sel_Unchanged
let apply_new_model solver = 
  let sel_is_changed = ref false in
  let change_entry var_entry =
    let prop_var = get_prop_var_var_entry var_entry in
    match var_entry.truth_val with	
    |Def(_) -> 	
  if (change_model_solver move_lit_from_active_to_passive var_entry) 
	then ()
	else sel_is_changed:=true
    |Undef ->
	(    (* sel_is_changed:=true; *)
	     let new_truth_val = PropSolver.lit_val solver prop_var in
	     var_entry.truth_val <- Def(new_truth_val)
	    )
  in
  TableArray.iter change_entry var_table;  
  if !sel_is_changed then ()
  else 
    raise Sel_Unchanged
  *)    
      
(*----------------- end change selection -----------------------------*)

(*let solver_calls_renew = ref 0*)

let rec selection_renew_solver move_lit_from_active_to_passive selection_fun clause =  
  try
    (
	     let solver_sel_lit = 
(*	       selection_fun consistent_with_solver_activity clause in	 *)
       selection_fun consistent_with_solver clause in	 
	     let solver_sel_var_entry  = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
      (*     out_str "Change here \n";*)
(*	     out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
		     ^"Sel_lit entry: "
		     ^(var_entry_to_string  solver_sel_var_entry));*)
	     Clause.assign_inst_sel_lit solver_sel_lit clause; 
	     ass_if_consistent solver_sel_lit clause
(*	     out_str ("----------------------------\n");*)
	   )
	   with Not_found -> 
	     ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	 (*     solver_calls_renew:= !solver_calls_renew +1;
	      out_str ("solver_calls renew "^(string_of_int !solver_calls_renew));*)
	      match (solve ()) with 
	     |PropSolver.Unsat -> 
	       ( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_solver@."; *)
		raise PropSolver.Unsatisfiable)
	     |PropSolver.Sat   ->
		 let new_solver_sel_lit = 
		   try
		     selection_fun consistent_with_solver clause 
		   with Not_found ->
		     raise (Failure (Format.sprintf "No selection possible for %s@." (Clause.to_string clause)))
		 in	  
		 let new_solver_sel_var_entry  = 
		   get_prop_gr_var_entry new_solver_sel_lit in
(*		 out_str "\n Change here!!!!\n";*)
		 change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
(*		 out_str ("Solver select:"^
			  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
			  ^"Sel_lit entry: "
			  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
		 Clause.assign_inst_sel_lit new_solver_sel_lit clause; 
		 ass_if_consistent new_solver_sel_lit clause
	     )
	


(*let _ = out_str "\n\n !!!selection_renew_main later switch to  selection_renew_tmp!!!\n\n "
*)


let selection_renew x =  
   match !current_options.inst_sel_renew with
    |Inst_SR_Solver ->
	selection_renew_solver x
    |Inst_SR_Model ->
	selection_renew_model x
 
(*------------Instantiation Lit Activity -----------------------------*)

exception Activity_Check
exception Activity_Undef
let lit_activity_check move_lit_from_active_to_passive lit = 
  if (not !current_options.inst_lit_activity_flag) 
  then ()
  else
    begin 
      try 
	let var_entry = get_prop_gr_var_entry lit in
	let model_truth_val = 
	  match var_entry.truth_val with 
	  |Def(PropSolver.True) -> true 
	  |Def(PropSolver.False) -> false
	  |_ -> raise Activity_Undef 
	in
	if ((model_truth_val = false)
(*	  && (var_entry.neg_activity > 
	     (var_entry.pos_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
	  && (var_entry.neg_activity > var_entry.pos_activity + var_entry.change_activity_limit) 
       )
    then
      (match (solve_assumptions solver [(get_prop_var_var_entry var_entry)])
       with 
       |PropSolver.Unsat -> 
	   (var_entry.change_activity_limit <-  1000000; (*any big number*)
            (*match (PropSolver.solve solver)
	   with PropSolver.Unsat -> raise Unsatisfiable
	   |PropSolver.Sat -> ()*) )
       |PropSolver.Sat   -> (
	   incr_int_stat 1 inst_lit_activity_moves;
			     var_entry.pos_activity <- 0;
			     var_entry.neg_activity <- 0;
			     var_entry.change_activity_limit <- 
			       (2*var_entry.change_activity_limit);
(*			     out_str ("Act Lit: "^(Term.to_string lit)^"\n"
				      ^"Before Change: "
				      ^(var_entry_to_string solver var_entry)^"\n");
*)
			     change_model_solver move_lit_from_active_to_passive var_entry;
			     
(*			     out_str ("After Chnage: "
				      ^(var_entry_to_string solver var_entry)^"\n");
*)
			     raise Activity_Check)
      )
    else 
      if ((model_truth_val = true)
	   (* && (var_entry.pos_activity > (var_entry.neg_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
	    && (var_entry.pos_activity > (var_entry.neg_activity + var_entry.change_activity_limit))
)
      then
	( 
	  match (solve_assumptions solver [(get_prop_neg_var_var_entry var_entry)])
	 with 
	 |PropSolver.Unsat -> 
	     (var_entry.change_activity_limit <-  1000000; (*any big number*)
             (*match (PropSolver.solve solver)
	     with PropSolver.Unsat -> raise Unsatisfiable
	     |PropSolver.Sat -> ()*)) 
(* (out_str ("Act_Check Unsat with assumption: "
				    ^(PropSolver.lit_to_string 
				    (get_prop_neg_var_var_entry var_entry))^"\n"))*)
	 |PropSolver.Sat   -> (
	   incr_int_stat 1 inst_lit_activity_moves;
			       var_entry.neg_activity <- 0;
			       var_entry.pos_activity <- 0;
			       var_entry.change_activity_limit <- 
				 (2*var_entry.change_activity_limit);
(*			       out_str ("Act Lit: "^(Term.to_string lit)^"\n"
					^"Before Change: "
					^(var_entry_to_string solver var_entry)^"\n");
 *) 
			       change_model_solver move_lit_from_active_to_passive var_entry;
(*			       
			       out_str ("After Chnage: "
					^(var_entry_to_string solver var_entry)^"\n");
*)
			       raise Activity_Check)
	)
      else ()
      with Activity_Undef -> ()
    end


let increase_lit_activity i lit = 
  try 
    let var_entry = get_prop_gr_var_entry lit in 
    let model_truth_val = 
      match var_entry.truth_val with 
      |Def(PropSolver.True) -> true 
      |Def(PropSolver.False) -> false
      |_ -> raise Activity_Undef 
    in
    if (model_truth_val = false) 
    then 
      (var_entry.neg_activity <- var_entry.neg_activity+i;
       if var_entry.neg_activity > (get_val_stat  inst_max_lit_activity)
       then (assign_int_stat var_entry.neg_activity inst_max_lit_activity
	     (*out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		      ^(var_entry_to_string  var_entry))*)
	    )
      )
    else 
      (var_entry.pos_activity <- var_entry.pos_activity+i;
       if var_entry.pos_activity > (get_val_stat  inst_max_lit_activity)
       then (assign_int_stat var_entry.pos_activity inst_max_lit_activity
	    (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		      ^(var_entry_to_string var_entry))*)
	    )
      )
  with Activity_Undef -> ()
     

(*
let  lit_activity_check =  lit_activity_check_main



let  lit_activity_check _ _ = ()
let _ = out_str "\n\n !!! lit_activity_check -> lit_activity_check_main !!!"
*)

(*------------End Instantiation Lit Activity -----------------------------*)


(*-----------Propositional Subsumtion--------------------------------*)

type add_lit = 
    {
     slit            : lit;
     sprop_lit       : PropSolver.lit;
     sprop_compl_lit : PropSolver.lit;
     mutable slabel  : bool
   }

exception Subsum_all_tried 
let rec first_non_tried rest list_add_lit =
  match list_add_lit with
  | h::tl -> 
      if (not h.slabel) 
      then (h,(rest@tl))
      else (first_non_tried (h::rest) tl)
  |[] -> raise Subsum_all_tried

let rec prop_subs_lits list_add_lit =
  try
    let (lit, to_test_add_lits) = first_non_tried [] list_add_lit in
    lit.slabel<-true;
    let to_test_prop_lits = 
      List.map (function add_lit -> add_lit.sprop_compl_lit) to_test_add_lits
    in      
    match (fast_solve solver_sim to_test_prop_lits) with
    |PropSolver.FUnsat -> 
	(
	 incr_int_stat 1 prop_fo_subsumed;
	 (* out_str("\n Solver_Sim Unsat under:\n");
	    out_str ((list_to_string PropSolver.lit_to_string to_test_prop_lits ";")
		   ^"\n");*)
	 prop_subs_lits to_test_add_lits)
    |PropSolver.FSat | PropSolver.FUnknown ->
(*    |PropSolver.Sat ->*)
	prop_subs_lits  list_add_lit
  with 
    Subsum_all_tried -> list_add_lit
  



(*let () = out_str "\n\n !!!Uncomment  prop_subsumption \n\n !!!"*)

(* We need first to filter adjoint predicate! *)
(* otherwise the same clause will be generated: c\/p  *)
(* by first cutting p and then adding it *)
(* this will result that the old clause will be declared dead *)
(* but new one will not be added since the old one is in the db *)

let filter_adjoint_pred lit_list = 
  let filter_pred list pred = List.filter (fun l -> not (l==pred)) list in
  List.fold_left filter_pred lit_list !adjoint_preds
  

let prop_subsumption clause = 
  let lits = filter_adjoint_pred (Clause.get_literals clause) in
  let list_add_lit = 
    let f lit = 
      {slit = lit; 
       sprop_lit = (get_prop_lit lit); 
       sprop_compl_lit = (get_prop_compl_lit lit); 
       slabel = false }
    in 
    List.map f lits in
  let new_add_lits = prop_subs_lits list_add_lit in
  if (List.length new_add_lits) < (List.length list_add_lit)
  then      
(*out_str "Eliminate Prop Subs\n";*)
      if (new_add_lits = []) 
      then 
	( (* Format.eprintf "Clause simplified to empty clause in prop_subsumption@."; *)
	 raise PropSolver.Unsatisfiable)
      else
	(let new_clause   = 
	  Clause.normalise term_db_ref 
	    (Clause.create 
	       ((List.map 
		   (function add_lit -> add_lit.slit) new_add_lits)@(!adjoint_preds))) 
	in
	  (* out_str ("Old Clause: "^(Clause.to_string clause)^"\n");  *)
	    Clause.inherit_param_modif clause new_clause;
	    Clause.assign_global_subsumption_history new_clause clause;
            Clause.set_bool_param true Clause.res_simplifying new_clause;
	    add_clause_to_solver new_clause;
	   
(*	    out_str ("New Clause: "^(Clause.to_string new_clause)^"\n");*)
	    new_clause )
  else clause (*raise Non_simplifiable*)






(*----------------Commented-----------------------*)
(*

(*--------------------get term for grounding-----------------------*)  

(* with the conjecture having a priority, not very good results

let get_term_for_grounding () = 
(* first try the  constant with max occurrence, which is in the conjecture*)
  let f_max_conj_sym s max_conj_sym = 
    if (
      (Symbol.get_bool_param Symbol.is_conj_symb s) &&
      ((Symbol.get_type s) = Symbol.Fun) &&
      ((Symbol.get_arity s) = 0) &&
      (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_conj_sym)) 
    then s 
    else max_conj_sym
  in
  let max_conj_sym = SymbolDB.fold f_max_conj_sym !symbol_db_ref bot_symb in
  let gr_symb = 
    if (max_conj_sym == bot_symb) then  
      let f_max_sym s max_sym = 
	if (((Symbol.get_type s) = Symbol.Fun) &&
	    ((Symbol.get_arity s) = 0) &&
	    (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym)) 
	then s 
	else max_sym
      in
      let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
      max_sym 
    else 
      max_conj_sym
  in
  (* we need to find the term in term_db corresponding to max_sym*)
  (* for this we just try to add it to term_db *) 
  let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
  gr_by_term
    
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
  (* debug*)
(* out_str ("Term for grounding_new: "^(Term.to_string gr_by_new)^"\n");
  match gr_by_new with 
  |Term.Fun(symb,_,_) ->
      out_str ("Number of occ_new: "^( string_of_int (Symbol.get_num_input_occur symb))^"\n")
  |_->()
*)

*)


(*--------------------get term for grounding-----------------------*)  
(* works but now much simpler version *)
(*

let get_term_for_grounding () = 
  let size = (SymbolDB.size !symbol_db_ref)+1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term = 
    match term with 
    |Term.Fun(symb,args,_) ->
(*      if (Term.is_empty_args args) then *)
	if (Term.is_constant term) then
	  (let index = (Symbol.get_fast_key symb)  in 
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
	  Array.set occur_array index ((Array.get occur_array index)+1);
	  Array.set const_term_array index term;
	  )
	else	
      Term.arg_iter fill_term  args
    |Term.Var _ -> ()
  in	  
  let fill_clause clause = 
    List.iter fill_term (Clause.get_literals clause) in
  let () =  List.iter fill_clause !init_clause_list_ref in
  let index_max =
    let max = ref 0 in
    let index = ref 0 in
    Array.iteri  
      (fun c_index c_max -> 
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
	if c_max >= !max 
	then 
	  (max := c_max; index:=c_index)
	else ()
      ) occur_array;
    !index 
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term
    
  
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)
*)



(*--------------------get term for grounding-----------------------*)  
(* works but now much simpler version *)

let get_term_for_grounding () = 
  let size = (SymbolDB.size !symbol_db_ref)+1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term = 
    match term with 
    |Term.Fun(symb,args,_) ->
(*      if (Term.is_empty_args args) then *)
	if (Term.is_constant term) then
	  (let index = (Symbol.get_fast_key symb)  in 
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
	  Array.set occur_array index ((Array.get occur_array index)+1);
	  Array.set const_term_array index term;
	  )
	else	
      Term.arg_iter fill_term  args
    |Term.Var _ -> ()
  in	  
  let fill_clause clause = 
    List.iter fill_term (Clause.get_literals clause) in
  let () =  List.iter fill_clause !init_clause_list_ref in
  let index_max =
    let max = ref 0 in
    let index = ref 0 in
    Array.iteri  
      (fun c_index c_max -> 
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
	if c_max >= !max 
	then 
	  (max := c_max; index:=c_index)
	else ()
      ) occur_array;
    !index 
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term
    
  
let init_solver_exchange () = 
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)




exception Given_clause_simplified 
(* is weaker than prop_subsumption *)

let prop_subs_resolution solver_sim solver gr_by clause = 
(*  out_str ("\n Given Clause: "^(Clause.to_string clause)^"\n");*)
  let is_simplified = ref false in
(*  let lits = Clause.get_lits clause in*)
  let resolve rest lit = 
    if (consistent_with_solver_lit solver lit) then lit::rest
    else
      (let prop_lit = get_prop_lit lit in
(*      let prop_compl_lit = get_prop_compl_lit solver lit in*)
      let result = (solve_assumptions solver_sim [prop_lit]) in
      match result with 
      |PropSolver.Unsat -> 
	  (* out_str "Unsat Assmpt \n ";*)
  ( is_simplified:= true; 
   incr_int_stat 1 porp_fo_subsumed;
	  rest)
      |PropSolver.Sat -> lit::rest
      ) 
    in 			      
  let new_lit_list = Clause.fold resolve [] clause in 
  if !is_simplified then 
    ( (*out_str "Given Simplified! \n";*)
      eliminate_clause clause;
      if (new_lit_list = []) 
      then raise Unsatisfiable 
      else
	(let new_clause   = Clause.create new_lit_list in
	if (not (ClauseAssignDB.mem new_clause !clause_db_ref))
	then
	  (let added_clause = 
	    ClauseAssignDB.add_ref new_clause clause_db_ref in             
	  (*add_clause_to_solver solver_sim solver gr_by added_clause;*)
	  Clause.assign_when_born !num_of_instantiation_loops  added_clause;
(*	out_str ("\n Clause: "^(Clause.to_string clause)^"\n");
  out_str ("\n Simplified to: "^(Clause.to_string added_clause)^"\n");*)
	 (* add_clause_to_unprocessed added_clause;*)
	  added_clause)
	else
	  raise Given_clause_simplified 
	(*added_clause*))      
     )
  else () (*clause*)
*)

(*----------------End Commented-----------------------*)

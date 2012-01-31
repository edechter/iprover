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
open Options
open Statistics
open Printf



type clause = Clause.clause 

let symbol_db_ref = Parser_types.symbol_db_ref


(*----------------- see libs.ml for iProver version number ---------------*)
(*let ()= out_str "\n---------------- iProver v0.7 --------------------\n"*)


let ()= out_str(options_to_str !current_options)




(*let time_before = Unix.gettimeofday () in       	
  Gc.full_major ();
  let time_after = Unix.gettimeofday () in       
  incr_int_stat (int_of_float  (time_after-.time_before)) forced_gc_time  
*)




(*------------------Signals:-----------------*)

exception Time_out_real
exception Time_out_virtual

let set_sys_signals () = 
  let signal_handler signal =
    if (signal = Sys.sigint || signal = Sys.sigterm || signal = Sys.sigquit) 
    then raise Termination_Signal
    else 
      if (signal = Sys.sigalrm) 
      then raise Time_out_real
      else 
	if (signal = Sys.sigvtalrm)
	then raise Time_out_virtual
	else failwith "Unknown Signal"
  in  	  
  Sys.set_signal Sys.sigint     (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigterm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigquit    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigalrm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigvtalrm  (Sys.Signal_handle signal_handler)

let set_time_out () = 
  (if  input_options.time_out_real > 0. 
  then 
    (
    ignore 
      (Unix.setitimer Unix.ITIMER_REAL
      {
       Unix.it_interval = 0.;
       Unix.it_value  = !current_options.time_out_real;
     })
    )
  else 
    if input_options.time_out_real = 0. 
    then raise Time_out_real
    else () (* if negative then unlimited *)
  );
  (if input_options.time_out_virtual > 0. 
  then
    ignore  
      (Unix.setitimer Unix.ITIMER_VIRTUAL
	 {
	  Unix.it_interval = 0.;
	  Unix.it_value  = input_options.time_out_virtual;
	})
  
  else 
    if !current_options.time_out_virtual = 0. 
      then raise Time_out_virtual
    else () (* if negative then unlimited *)
  )
    

(*---------------Probelm Properties---------------------*)

type problem_props = 
    {
     mutable epr  : bool;
     mutable horn : bool;
     mutable has_eq : bool;     
   }

let empty_problem_props () = 
  {
   epr    = true;
   horn   = true; 
   has_eq = false;
 }

(*
let val_distance = 40

let opt_val_to_str opt_val = 
  let (opt_name,val_str') = opt_val in
  let val_str = 
    if val_str' = "" then "\"\"" else val_str' in
  (space_padding_str val_distance opt_name)^val_str

let opt_val_list_to_str l = 
  String.concat "\n" (List.map opt_val_to_str l)

*)

let problem_props_to_string props = 
  let props_list = 
    [
     ("EPR",   string_of_bool props.epr);
     ("Horn",  string_of_bool props.horn);
     ("Has equality",string_of_bool props.has_eq)
   ]
  in
  Options.opt_val_list_to_str props_list

let get_problem_props clause_list = 
  let props = empty_problem_props () in
  let f cl = 
    (if props.epr then 
      props.epr <- Clause.is_epr cl
    else ()
    );
    (if props.horn then 
      props.horn <- Clause.is_horn cl
    else ()
    );
    (if not props.has_eq then 
      props.has_eq <- Clause.has_eq_lit cl
    else ());
(*debug*)
  (*  (if not (Clause.is_horn cl) then
      (out_str "\nNon_horn\n"; 
       flush stdout;
       out_str (Clause.to_tptp cl))
    else ()
    );*)
(*debug*)
    in
  List.iter f clause_list;
  props

let input_problem_props = ref (empty_problem_props ())



(*-------------Symbol type check--------------------------*)
(* check if there is only on symbol name for each type  *)


module NameSymMap = Map.Make(String)

(* table from symb numbes to list of symbols with the same name *)

type symb_name_table = (((Symbol.symbol list) ref) NameSymMap.t)

let create_name_symb_table () =
  let f symb symb_table =
    if not (Symbol.is_input symb)  
    then symb_table
    else
      (
       let symb_name = (Symbol.get_name symb) in
       try 
	 let symb_list_ref = NameSymMap.find symb_name symb_table in
	 symb_list_ref:= symb::(!symb_list_ref);
	 symb_table
       with 
	 Not_found -> 
	   NameSymMap.add symb_name (ref [symb]) symb_table
      )
  in
  SymbolDB.fold f !symbol_db_ref NameSymMap.empty

let check_symb_name_table snt = 
  let ok = ref true in
  let f sname symb_list_ref = 
    if ((List.length !symb_list_ref) > 1)
    then 
      (
       ok:=false;
       out_str (pref_str^("Type Check Faild on ")^(sname)^"\n");
       List.iter (fun symb -> 
	 Symbol.to_stream_full stdout_stream symb;
	 out_str "\n")
	 !symb_list_ref
      )
    else ()
  in
  NameSymMap.iter f snt;
  (if !ok
  then ()
  else 
    failwith "Type Check Faild, see help on option --symbol_type_check"
  )    

       
let symb_type_check () = 
  let snt = create_name_symb_table () in
  check_symb_name_table snt


(*--------Schedule Time Checks--------------------------*)

type time = float param

let sched_time_limit = ref Undef
let sched_start_time = ref Undef

let init_sched_time time_limit = 
  sched_time_limit:= time_limit;
  sched_start_time:= Def((Unix.gettimeofday ()))

(* can raise Sched_Time_Out (full_loop_counter)*)
(* full_loop_counter is the number of  iterations of the full_loop before *)
(* the time out, this can be used to determinise the run of the iProver *)
(* so one can reconstruct exactly the same behaviour *)
(* (the current schedule behaviour is dependent on time and therefore *)
(* on the environment but can be recostructed independent of time *)
(* based on full_loop_counter)*)
exception Sched_Time_Out of int 
let check_sched_time full_loop_counter = 
  match !sched_time_limit with 
  |Undef -> ()
  |Def time_limit  -> 
      (match !sched_start_time with 
      |Undef -> () 
      |Def start_time ->
	  if ((Unix.gettimeofday ()) -. start_time ) > time_limit 
	  then 
	    (
	     raise (Sched_Time_Out full_loop_counter))
	  else ()
      )

let time_to_string time = 
  match time with  
  |Def(float) -> string_of_float float
  |Undef -> "Unbounded"

(*
let switching_off_discount () = 
  out_str (pref_str^"Switching off resolution: loop timeout \n");
  !current_options.resolution_flag <- false;
  Discount.clear_all();
  clear_memory ()
*)


(*----------------------Full Loop--------------------------------------*) 

type prover_functions = {
  mutable  inst_lazy_loop_body     : (int ref -> int ref -> unit) param;      
  mutable  inst_clear_all          : (unit -> unit) param;
  mutable  res_discount_loop_exchange : (unit -> unit) param;
  mutable  res_clear_all           : (unit -> unit) param
  }

  

let apply_fun f_d args=
  match f_d with     
  |Def (f) -> f args
  |Undef -> failwith "iprover: Function is not defined"

let apply_fun_if_def f_d args=
  match f_d with     
  |Def (f) -> f args
  |Undef -> ()

let clear_all_provers prover_functions = 
  apply_fun_if_def prover_functions.inst_clear_all ();
  apply_fun_if_def prover_functions.res_clear_all ()


let full_loop prover_functions_ref input_clauses =  
(*  let current_input_clauses = ref input_clauses in
(* debug *)
  out_str ("\n Input Clauses: "
	   ^(string_of_int (List.length !current_input_clauses))^"\n");
(* debug *)
*)
  let solver_counter        = ref 0 in
  let solver_clause_counter = ref 0 in
  let learning_bound        = ref !current_options.inst_learning_start in 
  let learning_counter      = ref 0 in
  let resolution_counter    = ref 0 in
  let instantiation_counter = ref 0 in
  let full_loop_counter     = ref 0 in 
  while true do
    ( check_sched_time (!full_loop_counter);
      full_loop_counter:= !full_loop_counter+1;
      if (!current_options.resolution_flag && 
	  (!resolution_counter < !current_options.comb_res_mult)) 
      then
	( 
	resolution_counter:= !resolution_counter + 1;
	(*num_resolution_loops := !num_resolution_loops+1;*)
	(try
	  assign_discount_time_limit (!current_options.res_time_limit);
	  assign_discount_start_time ();
	  apply_fun !prover_functions_ref.res_discount_loop_exchange
	    ();
	with Timeout ->
	  if (!current_options.instantiation_flag) then 
	    ( out_str (pref_str^"Switching off resolution: loop timeout \n");
	      !current_options.resolution_flag <- false;
	      apply_fun !prover_functions_ref.res_clear_all ();
	      prover_functions_ref:= 
		{!prover_functions_ref with 
		 res_discount_loop_exchange = Undef;
		 res_clear_all	            = Undef};
	      clear_memory ()
	     )   
(* switching_off_discount ()*)
	  else failwith "Inst is off and Resolution is TimeOut: see --res_time_limit"
	);	
(*       out_str ("Resolution flag: "^(string_of_bool !resolution_flag)^"\n");*)

(*       let f clause = 
	 if (not (ClauseAssignDB.mem clause !clause_db_ref))
	 then ( clause)
	 else ()
	 in*)
       (*List.iter 
	  (Prop_solver_exchange.add_clause_to_solver gr_by) exchange_clauses;*)
(*       out_str ("\n Exchange Clauses: "
		^(Clause.clause_list_to_string exchange_clauses)^"\n")*)
      )
    else (* end of resolution part *)
      (
      if  !current_options.instantiation_flag && 
	(!instantiation_counter < !current_options.comb_inst_mult) 
      then 
	(instantiation_counter := !instantiation_counter + 1;	  
	 if ((not !current_options.inst_learning_loop_flag) ||
	     (!learning_counter < !learning_bound))
	 then 
	   (
	    learning_counter:=!learning_counter+1;
	    incr_int_stat 1 inst_num_of_loops;	
	    apply_fun !prover_functions_ref.inst_lazy_loop_body  
	      solver_counter solver_clause_counter;
	   )	     
	 else
      (* learning: !current_options.inst_learning_loop_flag & !learning_counter >= !learning_bound *)	  	   
	   ((* Format.eprintf "Learning restart in instantiation@."; *)
	     learning_bound:=!learning_bound * !current_options.inst_learning_factor;
	      learning_counter:=0;
	      incr_int_stat 1  inst_num_of_learning_restarts;
	      apply_fun !prover_functions_ref.inst_clear_all ();
(* simplify current_input_clauses with the new solver state *)
(* when simpl. given and new are switched off *)	      
(* not very good?  *)
(*		let simplify_clause rest clause = 
		  (Prop_solver_exchange.prop_subsumption clause)::rest
		in
		current_input_clauses := List.fold_left 
		    simplify_clause []  !current_input_clauses;
*)
(* debug *)
(*
		out_str ("\n New Input Length: "
                ^(string_of_int (List.length !current_input_clauses))^"\n");
*)
(*		out_str "\nNon Horn Clauses:\n";
		List.iter 
		  (fun c -> 
		    if (not (Clause.is_horn c)) 
		    then
		      out_str (Clause.to_string c)
		    else()) 
		  !current_input_clauses;

*)
(* end debug *)
		let module InstInput = 
		  struct 
		    let inst_module_name = 
		      ("Inst Restart "
		       ^(string_of_int (get_val_stat inst_num_of_learning_restarts)))
			
(*		    let input_clauses = !current_input_clauses		  *)
		    let input_clauses = input_clauses		
		end in 
		let module InstM = Instantiation.Make (InstInput) in
		prover_functions_ref:= 
		{ !prover_functions_ref with 
		  inst_lazy_loop_body     = Def(InstM.lazy_loop_body);
		  inst_clear_all          = Def(InstM.clear_all)};
(*	      prover_functions.inst_learning_restart input_clauses;*)
	      clear_memory ()
	     )
	)	    
      else (* instantiation_counter > instantiation_mult *)
	(resolution_counter:= 0;
	 instantiation_counter:=0    
	)
      
      )
     )
  done



(*------------Create Provers-------------------------*)

let create_provers inst_name res_name input_clauses = 
  let prover_functions =  {
    inst_lazy_loop_body        = Undef;
    inst_clear_all             = Undef;
    res_discount_loop_exchange = Undef;
    res_clear_all	           = Undef 
  } in
  (if !current_options.instantiation_flag 
  then 
    let module InstInput = 
      struct 
	let inst_module_name = inst_name
	let input_clauses = input_clauses
      end in 
    let module InstM = Instantiation.Make (InstInput) in
    prover_functions.inst_lazy_loop_body <- Def(InstM.lazy_loop_body); 
    prover_functions.inst_clear_all      <- Def(InstM.clear_all);
  else ()
  );
  (if !current_options.resolution_flag 
  then
    let module ResInput = 
      struct 
	let inst_module_name = res_name
	let input_clauses = input_clauses
      end in 
    let module ResM = Discount.Make (ResInput) in
    prover_functions.res_discount_loop_exchange <- Def(ResM.discount_loop_exchange);
    prover_functions.res_clear_all	        <- Def(ResM.clear_all) 
  else()
  );
  prover_functions



(*---------------Finite Models-------------------------------*)

(* if there is no equality then we start with a model with the size = *)
(* to the number of constants, we aslo do not add disequalities and *)
(* use unit domain axioms *)

let get_num_of_input_constants () = 
  let f s i  =
    if (Symbol.is_constant s) && (Symbol.get_num_input_occur s) >0   
    then 
      i+1
    else i
  in 
  SymbolDB.fold f !symbol_db_ref 0

(*
let _= out_str "\n\n!!! no_input_eq  Commented !!!\n\n"
*)

let no_input_eq () =  
  false
(*  (Symbol.get_num_input_occur Symbol.symb_equality) = 0 *)
  

let finite_models clauses = 
  !current_options.resolution_flag <- false;
  let model_bound = 500 in
  out_str (pref_str^"Finite Models:\n");
  let prep_clauses = Preprocess.preprocess clauses in
  Finite_models.flat_signature ();
  let init_clauses = (Finite_models.flat_clause_list prep_clauses) in
  out_str (pref_str^"lit_activity_flag true\n");
(*  Prop_solver_exchange.set_lit_activity_flag false;*)
  List.iter 
    Prop_solver_exchange.add_clause_to_solver init_clauses;
  (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
  then raise PropSolver.Unsatisfiable);
  let dom_const_list = ref [] in
  let domain_preds   = ref [] in

  let model_size = ref
    (if no_input_eq () 
    then 
      (out_str (pref_str^"No Equality\n");
       let num_const = get_num_of_input_constants () in
       if num_const > 0 
       then num_const
       else 1
      )
(* there is equality we start with the size 1 *)
    else 1
    )
  in
(*  let model_size = ref 20 in
  out_str (pref_str^"Overwritting the model size to:"
	   ^(string_of_int !model_size)^"\n");*)
  for i = 1 to !model_size 
  do
    let new_dom_const = 
      Finite_models.add_domain_constant i in
    dom_const_list := (!dom_const_list)@[new_dom_const]
  done;
  while !model_size < model_bound
  do
    try 
      out_str (pref_str^"Trying models of size: "
	       ^(string_of_int !model_size)^"\n");
      let dis_eq_axioms =
	if no_input_eq () 
	then []
	else
	  Finite_models.dis_eq_axioms_list !dom_const_list 
      in
      let new_dom_pred = Finite_models.add_domain_pred !model_size in      
      let domain_axioms = 
	if no_input_eq () 
	then 
	  Finite_models.domain_axioms_unit new_dom_pred !dom_const_list 
	else
	  Finite_models.domain_axioms_triangular new_dom_pred !dom_const_list 
      in
      let axioms  = domain_axioms@dis_eq_axioms in
      let clauses = axioms@init_clauses in
    (*  out_str ("\n-----------------------------\n"
     ^(Clause.clause_list_to_tptp clauses)^"\n");
    *)
      List.iter 
	Prop_solver_exchange.add_clause_to_solver axioms;
      let neg_domain_pred =  
	TermDB.add_ref 
	  (Term.create_fun_term Symbol.symb_neg [new_dom_pred]) 
	  Parser_types.term_db_ref in     
      Prop_solver_exchange.assign_solver_assumptions (neg_domain_pred::!domain_preds);

(* new_dom_pred is added for all simplified claues *)
      Prop_solver_exchange.assign_adjoint_preds  [new_dom_pred];
	(*(neg_domain_pred::(!domain_preds));*)
      domain_preds := new_dom_pred::!domain_preds;
      let prover_functions_ref = 
	ref (create_provers "Inst" "Res" clauses) in
      full_loop prover_functions_ref clauses	
    with 
    |Discount.Unsatisfiable 
    |Instantiation.Unsatisfiable  |PropSolver.Unsatisfiable  
      -> (Instantiation.clear_after_inst_is_dead (); 
	  model_size:=!model_size+1;
	  let new_dom_const = 
	    Finite_models.add_domain_constant !model_size in
	  dom_const_list := (!dom_const_list)@[new_dom_const])
  done;
  out_str ("Model Bound exceeded: "^(string_of_int model_bound)^"\n")


(*------Prolific Symbols change for large theories----------------*)

(* If prolific_symb_bound is changed in current_options *)
(* then we need to recalculate which terms/clauses contain prolific symbols *)
let rec change_prolific_symb_input input_clauses =
  let rec change_prolific_symb_term t =  
    match t with 
    |Term.Fun (symb, args, info)->
	Term.arg_iter change_prolific_symb_term args;
	Term.assign_has_non_prolific_conj_symb t
    |Term.Var _ -> ()    
      in
  let change_prolific_symb_clause c =
    Clause.iter change_prolific_symb_term c;
    Clause.assign_has_non_prolific_conj_symb c
      in
  List.iter change_prolific_symb_clause input_clauses
 
(*--------------------*)

let assign_is_essential_input_symb c_list = 
 List.iter  (Clause.iter_sym (Symbol.assign_is_essential_input true)) c_list


(*--------------Schedule-----------------------------*)

(* Current bound for BMC1 *)
let bmc1_cur_bound = ref 0

(* Assign statistics for current bound being processed *)
let () = assign_fun_stat 
  (fun () -> (!bmc1_cur_bound)) bmc1_current_bound


type schedule = (named_options * time) list 

(* setting hard time limit is problematic since the SAT solver can be interrupted*)
exception Schedule_Terminated
let rec schedule_run input_clauses finite_model_clauses schedule = 

  match schedule with 
  | (named_options,time_limit) ::tl ->
      if (named_options.options.sat_mode && named_options.options.sat_finite_models)
      then 
	((* current_options:= named_options.options; *)
	  set_new_current_options named_options.options;
	  init_sched_time time_limit;
	  finite_models finite_model_clauses)
      else
	begin
(* Moved down to output the actual options 
	  print_string ((s_pref_str ())^named_options.options_name
			^" Time Limit: "^(time_to_string time_limit)^"\n"^
			(options_to_str named_options.options)^"\n\n"
			^(s_pref_str ())^"Proving...");
	  flush stdout;
*)
	  (if not (!current_options.prolific_symb_bound = 
		   named_options.options.prolific_symb_bound) 
	  then change_prolific_symb_input input_clauses);
	  (* current_options:= named_options.options; *)
	  set_new_current_options named_options.options;
	  print_string ((s_pref_str ())^named_options.options_name
			^" Time Limit: "^(time_to_string time_limit)^"\n"^
			(options_to_str !current_options)^"\n\n"
			^(s_pref_str ())^"Proving...");
	  flush stdout;
(* debug *) 
	(*     !current_options.out_options <- Out_All_Opt;
	       out_str ("\n current options: "^(options_to_str !current_options)^"\n");
       *)
	  init_sched_time time_limit;
	  let prover_functions_ref = 
	    ref (create_provers "Inst Sched" "Res Sched" input_clauses) in
	  (try 
	    full_loop prover_functions_ref input_clauses
	  with 
	    Sched_Time_Out(full_loop_counter) ->
	      (out_str ("Time Out after: "
			^(string_of_int full_loop_counter)
		   ^" full_loop iterations\n");
	       clear_all_provers !prover_functions_ref;
	       clear_memory ();
	       schedule_run input_clauses finite_model_clauses tl)
(* One should be careful here,                     *)
(* since if Inst.  Satisfiable the model is passed *)
(* and resolution empty clause, proof  is passed, clearing provers should not *)
(* destroy models/proofs (at the moment it does not) *)
	  |x -> 
	      (clear_all_provers !prover_functions_ref; 
	  raise x)

	  )
	end
  | [] -> raise Schedule_Terminated

(*------------------Large Theories--------------------------------*)

   
let is_large_theory () = 
  (get_val_stat num_of_input_clauses) > !current_options.lt_threshold

(* For large theories, *)
(* we first omit eq axioms and if without them is Sat. then add eq axioms*)

let eq_axioms_are_omitted = ref false

let omit_eq_axioms () =
  !current_options.large_theory_mode &&
  (Symbol.is_essential_input Symbol.symb_equality) &&
  (is_large_theory ()) && 
  (get_val_stat num_of_input_neg_conjectures > 0) &&
  (not (List.exists 
	  Clause.has_eq_lit !Parser_types.neg_conjectures))&&
  (not !current_options.sat_mode) 
 

    
let schedule_to_many_axioms_schedule schedule = 
  if (is_large_theory ())
      && (get_val_stat num_of_input_neg_conjectures > 0)
  then
    (out_str (pref_str^"Large theory \n");
     let f (opt,time) = ((Options.named_opt_to_many_axioms_named_opt1 opt),time)
     in List.map f schedule
    )
  else
    schedule

let strip_conj_schedule schedule = 
  if (get_val_stat num_of_input_neg_conjectures = 0)
  then 
    let f (opt,time) = ((Options.strip_conj_named_opt opt),time)
    in List.map f schedule
  else schedule
      

(*returns (list_no_last,last)  *)
let get_last_elm_list list = 
  let rec get_last_elm_list' rest list =
    match list with 
    |h::[] -> ((List.rev rest), h)
    |h::tl -> get_last_elm_list' (h::rest) tl
    |[] -> failwith " iprover.ml: get_last_elm_list list is empty"
  in
  get_last_elm_list' [] list


let schedule_no_learinig_restarts schedule = 
  let f (opt,time) = 
    let new_opt = 
      {opt with 
       options = {opt.options with 
		  inst_learning_start            = 30000000
		}
     } in (new_opt,time) 
  in  List.map f schedule

let schedule_no_learinig_restarts_between schedule = 
  let (rest, last) = get_last_elm_list schedule in
  let new_rest = schedule_no_learinig_restarts rest in
  new_rest@[last]

(* for now a schedule is defined manualy here and not in the options *)
let init_schedule1 () = 
  let time1 = Def(10.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(10.) in 
  let option3 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]

let init_schedule2 () = 
  let time1 = Def(10.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_4 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]


let init_schedule3 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]

let init_schedule3_1 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1_1 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_2_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_3_1 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option_last,time_last)]


(* like option 1 but with shorter times *)
let init_schedule4 () = 
  let time1 = Def(15.) in 
  let option1 = named_option_1 () in 
  (*let time2 = Def(10.) in 
  let option2 = named_option_2 () in 
  let time3 = Def(10.) in 
    let option3 = named_option_3 () in *)
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(*(option2,time2);(option3,time3);*)(option_last,time_last)]


let init_schedule5 () = 
  let time1 = Def(25.) in
  let option1 = input_named_options in 
  let time2 = Def(15.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let init_schedule5_no_res_last () = 
  let time1 = Def(10.) in
  let option1 = input_named_options in 
  let time2 = Def(10.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(10.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(10.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = 
    {options_name = input_named_options.options_name^" \"--resolution_flag false\"";
     options      = {input_named_options.options with resolution_flag = false}}
  in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]




let init_schedule5_1 () = 
  let time1 = Def(25.) in
  let option1 = input_named_options in 
  let time2 = Def(15.) in 
  let option2 = named_option_1_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2_1 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3_1 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let init_schedule5_2 () = 
  let time1 = Def(25.) in
  let option1 = named_option_1_2 () in 
  let time2 = Def(15.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = named_option_1_2 () in 
  [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let init_schedule5_inst_first () =
  let time0 = Def(10.) in
  let option0 = 
    {options_name = input_named_options.options_name^" \"--resolution_flag false\"";
     options      = {input_named_options.options with resolution_flag = false}} in
  let time1 = Def(25.) in
  let option1 = input_named_options in 
  let time2 = Def(15.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(15.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(15.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = input_named_options in 
  [(option0,time0);(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


(*
let init_schedule () = 
  out_str (pref_str^"Schedule 1 is on \n");
  init_schedule1 ()   
*)
(*
let init_schedule () = 
  out_str (pref_str^"Many Axioms, Schedule 1 is on \n");
  schedule_to_many_axioms_schedule (init_schedule1 ())
*)


(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule3 ()))
      )
  else 
    (out_str (pref_str^"Schedule 3 is on, no restarts between \n");
     schedule_no_learinig_restarts_between  (init_schedule3 ()))

*)

(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule3 ()))
      )
  else 
    (out_str (pref_str^"Schedule 3 is on \n");
    (init_schedule3 ()))
*)

(*
let init_schedule () = 
  if num_of_input_clauses > !current_options.axioms_threshold
  then
    (  out_str (pref_str^"Schedule 1 is on, Many Axioms, no restarts \n");
       schedule_to_many_axioms_schedule (schedule_no_learinig_restarts  (init_schedule1 ()))
      )
  else 
    (out_str (pref_str^"Schedule 1 is on \n");
    (init_schedule1 ()))
*)


let sat_schedule () = 
  out_str (pref_str^"Schedule Sat is on\n");
  let time1 = Def(30.) in
  let option1 = (named_opt_sat_mode_off input_named_options) in 
  let time2 = Def(10.) in 
  let option2 = named_option_1 () in 
  let time3 = Def(10.) in 
  let option3 = named_option_2 () in 
  let time4 = Def(10.) in 
  let option4 = named_option_3 () in 
  let time_last = Undef in 
  let option_last = named_option_finite_models() in 
  strip_conj_schedule [(option1,time1);(option2,time2);(option3,time3);(option4,time4);(option_last,time_last)]


let epr_non_horn_schedule () = 
  out_str (pref_str^"Schedule EPR non Horn is on\n");
  let time1 = Def(10.) in
  let option1 = 
    {options_name = input_named_options.options_name^" \"--resolution_flag false\"";
     options      = {input_named_options.options with resolution_flag = false}} in

  let time_last = Undef in
  let option_last = named_option_epr_non_horn  () in
  [(option1,time1); (option_last,time_last)]



(*let _ = out_str "\n Schedule 5 was the best before\n"*)


(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5 ()))
*)

(*let _ = out_str "\n now init_schedule5_no_res_last, change later!\n "*)

let dynamic_sched_5 () =
  if (!input_problem_props.epr && (not !input_problem_props.horn))
  then 
    strip_conj_schedule (schedule_to_many_axioms_schedule 
			   (epr_non_horn_schedule ()))
			 (*  [((named_option_epr_non_horn  ()),Undef)])    *)
  else
    if (!input_problem_props.epr && !input_problem_props.horn) 
    then
      strip_conj_schedule (schedule_to_many_axioms_schedule 
			     [((named_option_epr_horn  ()),Undef)])
    else
      (out_str (pref_str^"Schedule dynamic 5 is on \n");
(*
       strip_conj_schedule  
	 (schedule_to_many_axioms_schedule (init_schedule5 ()))
*)
(*
       strip_conj_schedule  
	 (schedule_to_many_axioms_schedule (init_schedule5_no_res_last ()))
*)

	strip_conj_schedule  
	 (schedule_to_many_axioms_schedule (init_schedule5_inst_first ()))
	 
      )

	
let default_schedule () =  
  dynamic_sched_5 () 


let verification_epr_schedule () = 
  let time_last = Undef in 
  let option_last = named_option_verification_epr () in 
  strip_conj_schedule [(option_last,time_last)]
  

let verification_epr_schedule_tables () = 
  let time_last = Undef in 
  let option_last = named_option_verification_epr_tables () in 
  strip_conj_schedule [(option_last,time_last)]


(* !!!FINISH!!!*)
let out_res_model all_clauses = 
()  

(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5 ()))
*)
(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5_2 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5_2 ()))
*)

(*
let init_schedule () =  
  out_str (pref_str^"Schedule 5_1 is on \n");
  strip_conj_schedule  
    (schedule_to_many_axioms_schedule (init_schedule5_1 ()))
*)




(*------Main Function----------*)

(*
let szs_pref = "\n\nSZS' status "

(* "PROVED\n" *)
let proved_str ()   =
  if  (get_val_stat num_of_input_neg_conjectures > 0) 
  then
    szs_pref^"Theorem\n"
  else
    szs_pref^"Unsatisfiable\n"

(*"SATISFIABLE\n"*)
let satisfiable_str () = 
  if  (get_val_stat num_of_input_neg_conjectures > 0) 
  then
    szs_pref^"CounterSatisfiable\n"
  else
    szs_pref^"Satisfiable\n"  
*)


let szs_pref = "\n\n% SZS status "

(* "PROVED\n" *)
let proved_str ()   =
  if  ((get_some !ParseFiles.input_problem_type) = ParseFiles.FOF &&
       (get_val_stat num_of_input_neg_conjectures > 0))
  then
    szs_pref^"Theorem\n"
  else
    szs_pref^"Unsatisfiable\n"

(*"SATISFIABLE\n"*)
let satisfiable_str () = 
  if ((get_some !ParseFiles.input_problem_type) = ParseFiles.FOF &&
      (get_val_stat num_of_input_neg_conjectures > 0))
  then
    szs_pref^"CounterSatisfiable\n"
  else
    szs_pref^"Satisfiable\n"  


let unknown_str  ()   = szs_pref^"Unknown\n"

(* these clauses are used for *)
(*let clauses_for_sat_ref = ref [] *)

(* clauses used for finite model finding need not contain eq axioms *)




let rec main clauses finite_model_clauses = 
(* when Sat and eq ax are omitted we need to add them and start again *)
  let when_eq_ax_ommitted () =
    assert !eq_axioms_are_omitted;      
    out_str ("\n"^pref_str^("Adding Equality Axioms\n"));
    if !current_options.brand_transform then 
      main (Eq_axioms.eq_axioms_flatting clauses) finite_model_clauses
    else
      let equality_axioms = Eq_axioms.axiom_list () in
      List.iter 
	Prop_solver_exchange.add_clause_to_solver equality_axioms;
      eq_axioms_are_omitted:=false;
      let perp_eq_axs = Preprocess.preprocess equality_axioms in  
      main (perp_eq_axs@clauses) finite_model_clauses
  in
  let sched_run sched = schedule_run clauses finite_model_clauses sched in
  if (not !current_options.instantiation_flag) 
      && (not !current_options.resolution_flag)
  then
    failwith "No solver is selected: see --instantiation_flag, --resolution_flag"
  else
    try    
      match !current_options.schedule with 
      |Schedule_default           -> 
	  sched_run (default_schedule ())
      |Schedule_verification_epr  -> 
	  sched_run (verification_epr_schedule ())
      |Schedule_verification_epr_tables  -> 
	  sched_run (verification_epr_schedule_tables ())
      |Schedule_none              ->
	  if (!current_options.sat_mode && !current_options.sat_finite_models)
	  then
(* we use input clauses rather than clauses + eq axioms*)
	    finite_models finite_model_clauses
	  else
(* usual mode *)
	    let prover_functions_ref = 
	      ref (create_provers "Inst" "Res" clauses) in
	      full_loop prover_functions_ref clauses
		    
      | Schedule_sat -> 
	  sched_run (sat_schedule ())
		      
    (*  

	(if !current_options.schedule then 
	(
	let schedule = 
	if !current_options.sat_mode 
	then 
	sat_schedule () 
	else 
	init_schedule ()
	in
    (*	 let schedule = init_schedule () in*)
	 schedule_run clauses schedule 
	)
      else
	(
	 if (!current_options.sat_mode && !current_options.sat_finite_models)
	 then
(*we use input clauses rather than clauses + eq axioms*)
	   finite_models !Parsed_input_to_db.input_clauses_ref
	 else
(* usual mode *)
	   let prover_functions_ref = 
	     ref (create_provers "Inst" "Res" clauses) in
	   full_loop prover_functions_ref clauses
	)
      )
*)
(* end was commented *)


    with 
    |Discount.Satisfiable all_clauses
      -> 
	if !eq_axioms_are_omitted 
	then 	  
	  when_eq_ax_ommitted ()
	else	
	  (
	      out_str (satisfiable_str ());  

	    (* Do not output statistics in BMC1 mode with
	       --bmc1_out_stat none *)
	    if (not !current_options.bmc1_incremental) || 
	      (not (val_of_override !current_options.bmc1_out_stat = 
		  BMC1_Out_Stat_None)) then
	      out_stat ();	   

	    if (not (!current_options.sat_out_model = Model_None))
	    then
	      out_res_model all_clauses
	    else ()
	  )
    |
	Instantiation.Satisfiable all_clauses 
      ->
      if !eq_axioms_are_omitted 
      then 	  
	when_eq_ax_ommitted ()
      else	
	(out_str (satisfiable_str ());  

	    (* Do not output statistics in BMC1 mode with
	       --bmc1_out_stat none *)
	 if (not !current_options.bmc1_incremental) || 
	   (not (val_of_override !current_options.bmc1_out_stat = 
	       BMC1_Out_Stat_None)) then
	   out_stat ();	   

	 if (not (!current_options.sat_out_model = Model_None))
	 then
	   Model_inst.out_model (Model_inst.build_model all_clauses)
	 else ()
	)

    (* Incremental BMC1 solving: unsatisfiable when there are higher
       bounds left to check *)
    | (Discount.Unsatisfiable as e)
    | (Instantiation.Unsatisfiable as e)
    | (PropSolver.Unsatisfiable as e)
    | ((Discount.Empty_Clause _) as e)
	when !current_options.bmc1_incremental -> 
	
	(

(*	  
	  (match e with 
	    | Discount.Unsatisfiable -> 
	      Format.eprintf "Unsatisfiable in resolution@."
	    | Instantiation.Unsatisfiable ->
	      Format.eprintf "Unsatisfiable in instantiation@."
	    | PropSolver.Unsatisfiable ->
	      Format.eprintf "Unsatisfiable in propositional solver@."
	    | Discount.Empty_Clause _ ->
	      Format.eprintf "Unsatisfiable with empty clause in resolution@."
	    | _ -> ()
	  );
*)
	  
	  (* Get clauses in unsatisfiable core *)
	  let unsat_core_clauses = 
	    (try 
	       Prop_solver_exchange.unsat_core () 
	     with Invalid_argument _ -> []);
	  in

	  (* Print unsat core *)
	  Format.printf 
	    "@\nUnsat core has size %d@\n%a@." 
	    (List.length unsat_core_clauses)
	    (pp_any_list Clause.pp_clause "\n") unsat_core_clauses;

	  (* Don't do this: very long output 
	  (* Print histories of clauses in unsat core *)
	  Format.printf "@\nClause histories:@\n@.";
	  List.iter
	    (Format.printf "@\n%a@\n@." Clause.pp_clause_history)
	    unsat_core_clauses;
	  *)

	  (* Assign size of unsat core in statistics *)
	  assign_int_stat 
	    (List.length unsat_core_clauses) 
	    bmc1_unsat_core_size;

	  let start_time = Unix.gettimeofday () in

	  (* Get parent clauses of unsat core clauses *)
	  let unsat_core_parents = 
	    Clause.clause_list_get_history_parents unsat_core_clauses
	  in
(*
	    List.fold_left 
	      (fun a c -> 
		List.fold_left 
		  (fun a' c' -> if List.memq c' a' then a' else (c' :: a'))
		  a
		  (Clause.get_history_parents c))
	      []
	      unsat_core_clauses
	  in
*)

	  let end_time = Unix.gettimeofday () in
	  
	    if 
	      
	      (* Verbose output for BMC1?*)
	      val_of_override !current_options.bmc1_verbose 

	    then 
	      
	      (

		Format.printf 
		  "Time for finding parents of unsat core clauses: %.3f@\n@."
		  (end_time -. start_time);
		
		(* Print parents of unsat core *)
		Format.printf 
		  "@\nUnsat core parents has size %d@\n%a@." 
		  (List.length unsat_core_parents)
		  (pp_any_list Clause.pp_clause "\n") unsat_core_parents

	      )
		
	    else

	      (

		(* Print parents of unsat core *)
		Format.printf 
		  "@\nUnsat core parents has size %d@\n@." 
		  (List.length unsat_core_parents)

	      );

	  (* Increment bound by one
	     
	     TODO: option for arbitrary bound increments *)
	  let cur_bound, next_bound =
	    !bmc1_cur_bound, succ !bmc1_cur_bound
	  in

	  (* Get value of maximal bound *)
	  let max_bound = 
	    val_of_override !current_options.bmc1_max_bound
	  in

	    (* Output current bound *)
	    Format.printf 
	      "@.@\n%s BMC1 bound %d %s after %.3fs@\n@."
	      pref_str
	      cur_bound
	      ("UNSAT")
	      (truncate_n 3 (Unix.gettimeofday () -. iprover_start_time));
	    
	    (* Assign last solved bound in statistics *)
	    assign_int_stat !bmc1_cur_bound bmc1_last_solved_bound;
	    
	    if 
	      
	      (* Next bound is beyond maximal bound? *)
	      next_bound > max_bound && 
		
		(* No maximal bound for -1 *)
		max_bound >= 0 
		
	    then
	      
	      (
		
		(* Output unsatisfiable result for last bound *)
		out_str (proved_str ());
		
	      );
	    
	    (
	      
	      (* When to output statistics? *)
	      match val_of_override !current_options.bmc1_out_stat with
		  
		(* Output statistics after each bound *)
		| BMC1_Out_Stat_Full -> out_stat ()

		(* Output statistics after last bound *)
		| BMC1_Out_Stat_Last 
		    when next_bound > max_bound -> out_stat ()

		(* Do not output statistics for bounds before last *)
		| BMC1_Out_Stat_Last -> ()

		(* Never output statistics *)
		| BMC1_Out_Stat_None -> ()

	    );
	    
	    if 
	      
	      (* Next bound is beyond maximal bound? *)
	      next_bound > max_bound && 
		
		(* No maximal bound for -1 *)
		max_bound >= 0 
		
	    then

	      (

		(* Silently terminate *)
		raise Exit
		  
	      );
	    
	    (* Output next bound *)
	    Format.printf 
	      "%s Incrementing BMC1 bound to %d@\n@."
	      pref_str
	      next_bound;
	    
	    (* Clear properties of terms before running again *)
	    Instantiation.clear_after_inst_is_dead (); 
	    
	    (* Add axioms for next bound *)
	    let next_bound_axioms = 
	      Bmc1Axioms.increment_bound cur_bound next_bound
	    in

	      (* Symbols in axioms are input symbols *)
	      assign_is_essential_input_symb next_bound_axioms;

	      (* Add axioms to solver *)
	      List.iter 
		Prop_solver_exchange.add_clause_to_solver 
		next_bound_axioms;

	      (* Preprocess axioms *)
	      let next_bound_axioms' = 
		Preprocess.preprocess next_bound_axioms
	      in

	      (* Clauses in unsatisfiable core to be added to next
		 bound *)
	      let unsat_core_clauses' = 

		if 

		  (* Add clauses from unsatisfiable core to next bound *)
		  val_of_override !current_options.bmc1_add_unsat_core 

		then

		  (

		    (* Flag clauses as in unsat core *)
		    List.iter 
		      (Clause.set_bool_param true Clause.in_unsat_core)
		      unsat_core_parents;

(*
		    List.iter 
		      (Clause.set_bool_param true Clause.in_unsat_core)
		      unsat_core_clauses;
*)

		    (* Preprocess clauses *)
		    Preprocess.preprocess unsat_core_clauses

		  )
		    
		else

		  (* Do not add clauses from unsatisfiable core *)
		  []

	      in

	      (* Save next bound as current *)
	      bmc1_cur_bound := next_bound;
	      
	      (* Input clauses for next bound *)
	      let all_clauses = 
		next_bound_axioms' @ unsat_core_clauses' @ clauses
	      in

	      if 
		
		(* Dump clauses to TPTP format? *)
		val_of_override !current_options.bmc1_dump_tptp 

	      then

		Format.printf "%a@." 
		  (pp_any_list Clause.pp_clause_tptp "@\n@.") all_clauses;

	      (* Run again for next bound *)
	      main 
		all_clauses
		finite_model_clauses
	      
	)

(*-------- Reachability depth for father_of relation (Intel) -----------*)

module SymbMap = Symbol.Map
module SymbReachRel = 
  struct 
    type t = Symbol.symbol 
    let compare = Symbol.compare 
    let reach_rel symb =       
      let reach_symb_names = 
	try 
	  SymbMap.find symb !(Parser_types.father_of_map)
	with 
	  Not_found -> []
      in
      let reach_symb_list = 
	let f rest symb_name = 
	  try 
	    let symb = SymbolDB.find 
		(Symbol.create_template_key_symb symb_name) !symbol_db_ref in
	    (symb::rest)
	  with 
	    Not_found -> 
	      rest
	in 
	List.fold_left f [] reach_symb_names 
      in
      reach_symb_list
  end

module SymbReach = MakeReach(SymbReachRel)
module SymbReachMap =  SymbReach.ReachMap


let symbol_reach conj_list = 
  let get_preds_clause clause =
    Clause.fold 
      (fun rest lit ->  
	let pred = Term.lit_get_top_symb lit in 
	if (Symbol.get_bool_param Symbol.is_defined_symb_input pred) 
	then (pred::rest)
	else rest
      ) [] clause in
  let conj_pred_list = 
   List.fold_left (fun rest clause -> ((get_preds_clause clause)@rest)) [] conj_list
  in
  let reach_map = SymbReach.compute_reachability conj_pred_list in
  SymbReachMap.iter 
    (fun symb depth -> 
      Symbol.assign_defined_depth depth symb) reach_map;
  reach_map

let out_symb_reach_map srm =
(* get into list and order by priority *)
 let symb_depth_list = 
   SymbReachMap.fold (fun symb depth rest -> ((symb,depth)::rest)) srm []
 in
 let sorted_symb_depth_list = 
   List.sort (fun (_,d1) (_,d2) -> compare d1 d2) symb_depth_list in

   (* Output only in verbose mode *)
   if val_of_override !current_options.bmc1_verbose then 
     List.iter 
       (fun (symb,depth) -> 
	  out_str ((Symbol.to_string symb)^": "^(string_of_int depth))) 
       sorted_symb_depth_list  
       

(*------------------------------------------------*)

(*----------------Top Function--------------------*)

(*--run_iprover: initialises, ----------------*)
(*--parses and then runs main on the prepocessed clauses------*)

let run_iprover () =

  (try
(*---------Set System Signals--------------------*)
    set_sys_signals ();
    set_time_out ();
 

(*---------------Parse the input-------------*)    
 
(*----debug----*)
  (*  mem_test ParseFiles.parse 3; *)
(*    let test_fun () = 
      Parser_types.init ();
      ParseFiles.parse ();
    in
    mem_test test_fun 5; 
*)
(*--Uncomment-------*)
 
    assign_float_stat (get_time_fun 3 ParseFiles.parse) parsing_time;

    (if !current_options.clausify_out
    then  
      (
       let clause_list = Parser_types.get_clauses_without_extra_axioms () in
       let (epr, non_epr) = List.partition Clause.is_epr clause_list in       
       out_str  ("% "^pref_str^"Clauses after clausification:\n\n");
       out_str  ("% "^pref_str^"EPR clauses:\n\n");
       Clause.out_clause_list_tptp epr;
       out_str  ("\n\n"^"% "^pref_str^"non-EPR clauses:\n\n");
       Clause.out_clause_list_tptp non_epr;     
       out_str "\n\n";
       exit(0);
      )
    else ()
    );

   
(*-----------check types of symbols---------------*)
    (if !current_options.symbol_type_check 
    then 
      symb_type_check () 
    else ()
    );

(*---- We need to Calculate has_conj_symb/has_non_prolific_conj_symb ----------*)
(* not very good but should work *)

    let change_conj_symb_input () =  
      let rec change_conj_symb_term is_conj t = 
	match t with 
	|Term.Fun (symb, args, info)->
(* if it is conjecture and symbol is plain (non-theory, neg, quant, etc) *)
(*	    let stype = (Symbol.get_type symb) in                        *)
	    (if (is_conj  
                   && 
		 ((Symbol.is_fun symb) or (Symbol.is_pred symb))
               (* && 
		 ((Symbol.get_property symb) = Symbol.Undef_Prop)*))
	    then 
	      Symbol.set_bool_param 
		true Symbol.is_conj_symb symb
	    else()
	    );
	    Term.arg_iter (change_conj_symb_term is_conj) args;
	    Term.assign_has_conj_symb t;
	    Term.assign_has_non_prolific_conj_symb t
	|Term.Var _ -> ()
      in
      let change_conj_symb_clause is_conj c =
	Clause.iter (change_conj_symb_term is_conj) c;
	Clause.assign_has_conj_symb c;
	Clause.assign_has_non_prolific_conj_symb c
      in
(* first need consider conjectures then the rest *)
      List.iter (change_conj_symb_clause true) !(Parser_types.neg_conjectures);
      List.iter (change_conj_symb_clause false) !(Parser_types.parsed_clauses)
    in
    change_conj_symb_input ();

    (* Calculate symbol reachability? *)
    if !current_options.bmc1_symbol_reachability then

      (
	
	let reach_map_start_time = Unix.gettimeofday () in
	
	out_symb_reach_map  
	  (symbol_reach 
	     !(Parser_types.neg_conjectures));
	   
	out_str 
	  (Format.sprintf 
	     "%sTime for symbol reachability: %.3fs@\n@."
	     pref_str
	     (Unix.gettimeofday () -. reach_map_start_time));

      );


(*----debug----*)
(*    mem_test change_conj_symb_input 3; *)
  


(*---debug-------*)
(*
    let out_symb symb =
      out_str ("Symb: "
	       ^(Symbol.to_string symb)
	       ^" is conj symb: "
	       ^ (string_of_bool (Symbol.get_bool_param Symbol.is_conj_symb symb ))^"\n"
	       ^"has bound constant: "
	       ^(string_of_bool (Symbol.get_bool_param Symbol.is_bound_constant symb ))^"\n" );
    in
(*    let out_term t = 
         out_str ("Term: "
	       ^(Term.to_string t)
	       ^" has conj symb: "
	       ^ (string_of_bool (Term.get_bool_param Term.has_conj_symb t ))^" "
	       ^"has bound constant: "
		  ^(string_of_bool (Term.get_bool_param Term.has_bound_constant t ))^"\n" )
    in*)


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
(*
    SymbolDB.iter out_symb !Parser_types.symbol_db_ref;
*)
    out_str "\n\n ------------------------------\n\n";
 
(*   Tern.DB.iter out_term !Parser_types.term_db_ref;
    out_str "\n\n ------------------------------\n\n";*)
    List.iter out_cl !Parser_types.all_current_clauses;
*) 
(* end debug *)	

(*-------------------------------*)
    let current_clauses = Parser_types.all_current_clauses in 
(*-------------------------------*)
(* At the moment Parsed_input_to_db.input_clauses_ref are not memory released! *)
(* we can replace Parsed_input_to_db.input_clauses_ref with *)
(* global  Parsed_input_to_db.current_clauses, which are gradually replaced by preprocessing but should be carefull how intput caluses are used below: finite_models eq_axioms etc. *)



(*-------------------------------*)
  Prop_solver_exchange.init_solver_exchange ();
(*-------------------------------*)

(* with sat_mode one should be careful with options!*)
(* switch off resolution! *)
(*    out_str ("\n\n!!!!! Switch from Finite Models to SAT mode!!!\n\n");
   if !current_options.sat_mode 
    then
     (current_options:=(named_option_finite_models ()).options;
     sat_mode  !current_clauses )     
    else
*)
    begin	
      current_clauses := Preprocess.preprocess !current_clauses;
      assign_is_essential_input_symb !current_clauses;
      let distinct_ax_list = Eq_axioms.distinct_ax_list () in
	(* Clauses are input clauses *)
	assign_is_essential_input_symb distinct_ax_list;
	      
(*debug *)
(*	out_str "\n-----------Distinct Axioms:---------\n";
	out_str ((Clause.clause_list_to_tptp distinct_ax_list)^"\n\n");
	out_str "\n--------------------\n";
*)
(*debug *)

      current_clauses := distinct_ax_list@(!current_clauses);

      let less_range_axioms = Eq_axioms.less_range_axioms () in

(*debug *)
(*
        out_str "\n-----------Less Range Axioms:---------\n";
        out_str ((Clause.clause_list_to_tptp less_range_axioms)^"\n\n");
        out_str "\n--------------------\n";
*)
(*debug *)

	(* Clauses are input clauses *)
	assign_is_essential_input_symb less_range_axioms;
	      
	(

	  (

	    try 
	      
	      (* Get cardinality of state_type *)
	      let max_bound = 
		pred 
		  (Symbol.Map.find
		     Symbol.symb_ver_state_type
		     !Parser_types.cardinality_map)
	      in
		
		(* Override default value of maximal bound from file *)
		!current_options.bmc1_max_bound <- 
		  override_file max_bound !current_options.bmc1_max_bound
		  
	    (* Cardinality not defined, then no upper bound *)
	    with Not_found -> 
	      
	      ()

	  );
	  
	  (* BMC1 with incremental bounds? *)
	  if !current_options.bmc1_incremental then

	    (

	      (* Return axioms for all bounds from [i] to [n] *)
	      let rec skip_to_bound accum n i = 

		(* Axioms for all bounds added? *)
		if i >= n then 
		  
		  (* Return axioms *)
		  accum 

		else

		  (

		    (* Add axioms for next bound *)
		    let next_bound_axioms = 
		      Bmc1Axioms.increment_bound i (succ i)
		    in
		    
		    (* Output next bound *)
		    Format.printf 
		      "%s Incrementing BMC1 bound to %d@\n@."
		      (pref_str)
		      (succ i);
		    
		    (* Recurse until all axioms for all bounds added *)
		    skip_to_bound 
		      (next_bound_axioms @ accum)
		      n
		      (succ i)
		  )

	      in

	      (* Create clauses for initial bound *)
	      let bmc1_axioms, current_clauses' = 
		Bmc1Axioms.init_bound !current_clauses 
	      in
	      
	      out_str 
		(Format.sprintf 
		   "%sAdded initial BMC1 axioms@\n"
		   pref_str);

	      (* Add axioms from bound 0 to starting bound *)
	      let bmc1_axioms' = 
		skip_to_bound 
		  bmc1_axioms
		  (val_of_override !current_options.bmc1_min_bound)
		  0
	      in

	      (* Clauses are input clauses *)
	      assign_is_essential_input_symb bmc1_axioms';
	      
	      (* Add clauses for initial bound *)
	      current_clauses := 
		bmc1_axioms' @ current_clauses'
		  
	    )

	);
	
	(* Output maxial bound for BMC1 *)
	let max_bound = val_of_override !current_options.bmc1_max_bound in

	  if max_bound >= 0 then 
	    out_str 
	      (Format.sprintf 
		 "%sMaximal bound for BMC1 is %d@\n"
		 pref_str
		 max_bound);
	
 
(* for finite models we ommit equality axioms! *)

      let finite_models_clauses = !current_clauses in 

      current_clauses := less_range_axioms@(!current_clauses);

      (if (not (omit_eq_axioms ())) 
      then
	(
	 if !current_options.brand_transform 
	 then 
	   (
(*debug *)
(*	    out_str "\n-----------Before Brand transform:---------\n";
	    out_str ((Clause.clause_list_to_tptp !current_clauses)^"\n\n");
	    out_str "\n--------------------\n";
*)	    
	    current_clauses := (Eq_axioms.eq_axioms_flatting !current_clauses);
(*	    
	    out_str "\n-----------After Brand transform:---------\n";
	    out_str ((Clause.clause_list_to_tptp !current_clauses)^"\n\n");
	    out_str "\n--------------------\n";
*)
(*debug *)
	   )
	 else
	   (
	   let equality_axioms = Eq_axioms.axiom_list () in
(*debug *)
(*
	out_str "\n-----------Eq Axioms:---------\n";
	out_str ((Clause.clause_list_to_tptp equality_axioms)^"\n\n");
	out_str "\n--------------------\n";

*)
(*debug *)
	   current_clauses := equality_axioms@(!current_clauses)
	   )
	)
      else 
	(eq_axioms_are_omitted:=true;
	 out_str (pref_str^"Omitting Equality Axioms\n"))
      );    
 

(*--------------semantic filter---------------------------*)
      if !current_options.prep_sem_filter_out 
    then  
      (
       out_str (pref_str^"Semantically Preprocessed Clauses:\n");
       let prep_clauses = 
	 Prep_sem_filter.filter !(Parser_types.all_current_clauses) in 
       Clause.out_clause_list_tptp prep_clauses; 
       out_str "\n\n";
       exit(0);
      )
    else 
      (if (!current_options.prep_sem_filter && 
	   (not (Symbol.is_input Symbol.symb_equality)))
      then 
        current_clauses := Prep_sem_filter.filter !current_clauses
      else ()
      );
  
(*--------------End sem filter---------------------------*)
     input_problem_props:=get_problem_props !current_clauses;
      out_str (pref_str^"Problem Properties \n");
      out_str ("\n"^(problem_props_to_string !input_problem_props)^"\n");      
(*debug *)
(*
      out_str "\n\nInput_Preproccessed clauses\n\n";
      out_str (Clause.clause_list_to_tptp !current_clauses);
*)





(*-------------------------------------------------*)
	  out_str (pref_str^"Proving...\n");
(*-------------------------------------------------*)
 
(*	(if !current_options.instantiation_flag then *)
      List.iter 
	Prop_solver_exchange.add_clause_to_solver !current_clauses;
      (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
      then 
	(raise PropSolver.Unsatisfiable));
      (* Clause.out_clause_list_tptp !current_clauses; *)
      main !current_clauses finite_models_clauses
    end
  with

  |Discount.Unsatisfiable 
  |Instantiation.Unsatisfiable  |PropSolver.Unsatisfiable  
    ->
    (* Output unsatisfiable core *)
    (try 
       ignore (Prop_solver_exchange.unsat_core ())
     with Invalid_argument _ -> ());

      out_str (proved_str ());
       (if 
	(!answer_mode_ref)
      then
	Prop_solver_exchange.out_answer ()
      else
	()
      );
       	    
       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
       if (not !current_options.bmc1_incremental) || 
	 (not (val_of_override !current_options.bmc1_out_stat = 
	     BMC1_Out_Stat_None)) then
	 out_stat ()
	   
  | Discount.Empty_Clause (clause) -> 
    (
      out_str (proved_str ());

      (* Do not output statistics in BMC1 mode with
	 --bmc1_out_stat none *)
      if (not !current_options.bmc1_incremental) || 
	(not (val_of_override !current_options.bmc1_out_stat = 
	    BMC1_Out_Stat_None)) then
	out_stat ();	   
      
      out_str(" Resolution empty clause:\n");
(* in this case the unsat is already without answer clauses *)
       (if (!answer_mode_ref)
       then
	 out_str "% SZS answers Tuple [[]]"
       else ()
       );	  
  
       (if !current_options.res_out_proof
       then 
	 (Discount.out_proof_fun clause)
       else ())
      )
	
  |Discount.Satisfiable all_clauses
    -> 
      (assert (not !eq_axioms_are_omitted);
       out_str (satisfiable_str ());  
       
       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
       if (not !current_options.bmc1_incremental) || 
	 (not (val_of_override !current_options.bmc1_out_stat = 
	     BMC1_Out_Stat_None)) then
	 out_stat ();	   

       if (not (!current_options.sat_out_model = Model_None))
       then
	 out_res_model all_clauses
       else ()
      )

  |Instantiation.Satisfiable all_clauses
      ->
	(assert (not !eq_axioms_are_omitted);
	 out_str (satisfiable_str ());  

	 (* Do not output statistics in BMC1 mode with
	    --bmc1_out_stat none *)
	 if (not !current_options.bmc1_incremental) || 
	   (not (val_of_override !current_options.bmc1_out_stat = 
	       BMC1_Out_Stat_None)) then
	   out_stat ();	   

	 if (not (!current_options.sat_out_model = Model_None))
	 then
	  Model_inst.out_model (Model_inst.build_model all_clauses)
	 else ()
	)

  | Termination_Signal -> 
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "\n Termination Signal\n"; 

       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
       if (not !current_options.bmc1_incremental) || 
	 (not (val_of_override !current_options.bmc1_out_stat = 
	     BMC1_Out_Stat_None)) then
	 out_stat ())
	
  | Time_out_real -> 
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "Time Out Real\n"; 
       
       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
       if (not !current_options.bmc1_incremental) || 
	 (not (val_of_override !current_options.bmc1_out_stat = 
	     BMC1_Out_Stat_None)) then
	 out_stat()
	   
      )
	
  | Time_out_virtual ->
      (kill_all_child_processes ();
       out_str (unknown_str ()); 
       out_str "Time Out Virtual\n"; 
       
       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
       if (not !current_options.bmc1_incremental) || 
	 (not (val_of_override !current_options.bmc1_out_stat = 
	     BMC1_Out_Stat_None)) then
	 out_stat())
	
  |Schedule_Terminated ->
    (kill_all_child_processes ();
     out_str (unknown_str ()); 
     out_str "Schedule_Terminated:  try an extended schedule or with an unbounded time limit";
     
       (* Do not output statistics in BMC1 mode with
	  --bmc1_out_stat none *)
     if (not !current_options.bmc1_incremental) || 
       (not (val_of_override !current_options.bmc1_out_stat = 
	   BMC1_Out_Stat_None)) then
       out_stat ())
      
  (* Silently terminate after BMC1 maximal bound proved *)
  | Exit -> ()
  
  | x -> 
      (kill_all_child_processes ();
       out_str (unknown_str ());
       raise x)
  )    


let _ = run_iprover ()
    

(*---------------------------Commented----------------------------*)      

(*
      
      (
      
	(*debug*)
(*
	Large_theories.fill_tables !current_clauses;
	out_str ("Conjectures: "
		 ^(Clause.clause_list_to_string 
		     !Parsed_input_to_db.input_neg_conjectures_ref)^"\n"
		);
	let conj_symb = 
	  Large_theories.get_symb_list !Parsed_input_to_db.input_neg_conjectures_ref in
	let (_,key_list1)= Large_theories.get_axioms_next_keys_all conj_symb in
	
	let (_,key_list2) = Large_theories.get_axioms_next_keys_all key_list1 in
	let (_,_key_list3) = Large_theories.get_axioms_next_keys_all key_list2 in
	(*end debug*)
	*)	   
(*	else());	*)


   List.iter (fun c ->
    out_str ("\n-------------------\n"
	     ^(Clause.to_string c)^"\n"
	     ^
	       (Clause.to_string (Finite_models.flat_clause c))^"\n")) 
    !current_clauses;

  let dom_const = Finite_models.add_domain_constants 0 5 in 
  let dis_eq_axioms_list = Finite_models.dis_eq_axioms_list dom_const in
  out_str ("Domain Diseq\n"
	   ^(Clause.clause_list_to_string dis_eq_axioms_list)^"\n");
  let dom_axioms = Finite_models.domain_axioms dom_const in 
  out_str 
    ("\n-------------------\n"
     ^"Domain Ax: \n"
     ^(Clause.clause_list_to_string dom_axioms)^"\n");

*)

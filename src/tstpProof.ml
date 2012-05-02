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


(* Get parent leaf clauses of a list of clauses *)
let rec get_leaves' visited accum = function 

  (* No more clause histories to recurse *)
  | [] -> accum
      
  (* Clause already seen *)
  | (clause :: tl) when Clause.ClauseHashtbl.mem visited clause ->
      
    (* Skip clause *)
    get_leaves' visited accum tl
      
  (* New clause *)
  | clause :: tl -> 

    (* Remember clause *)
    Clause.ClauseHashtbl.add visited clause ();

    (* Get source of clause *)
    match 
      (try 
	 Clause.get_tstp_source clause 
       with Failure _ -> 
	 raise 
	   (Failure 
	      (Format.sprintf "Source of clause %s not defined" (Clause.to_string clause))))
    with

      (* Clause is from input or theory axioms *)
      | Clause.TSTP_external_source _ 
      | Clause.TSTP_internal_source _ -> 

	(* Add clause as leaf *)
	get_leaves' visited (clause :: accum) tl
	  
      (* Clause is from global propositional subsumption *)
      | Clause.TSTP_inference_record 
	  (Clause.Global_subsumption max_clause_id, [parent]) -> 
	
	(* Get justification for simplification of clause *)
	let parents' = 
	  Prop_solver_exchange.justify_prop_subsumption 
	    max_clause_id
	    parent 
	    clause
	in

	  (* Recurse to get parents of premises *)
	get_leaves' visited accum ((parent :: parents') @ tl)
	  
      (* Clause is from other inference *)
      | Clause.TSTP_inference_record (_, parents) -> 

	(* Recurse to get parents of premises *)
	get_leaves' visited accum (parents @ tl)


(* Get parent clauses of a list of clauses *)
let get_leaves clause_list = 
  get_leaves' (Clause.ClauseHashtbl.create 101) [] clause_list


let rec get_parents' visited accum = function

  (* No more clause histories to recurse *)
  | [] -> accum
      
  (* Clause already seen *)
  | (clause :: tl) when Clause.ClauseHashtbl.mem visited clause ->

    (* Clause is already in the list *)
    if Clause.ClauseHashtbl.find visited clause then
    
      (* Skip clause *)
      get_parents' visited accum tl

    else
      
      (

	(* Remember insertion of clause into list *)
	Clause.ClauseHashtbl.add visited clause true;

	(* Add clause to list *)
	get_parents' visited (clause :: accum) tl

      )
      
  (* New clause *)
  | clause :: tl -> 
    
    (* Remember recursion into parents of clause *)
    Clause.ClauseHashtbl.add visited clause false;

    (* Get source of clause *)
    match 
      (try 
	 Clause.get_tstp_source clause 
       with Failure _ -> 
	 raise 
	   (Failure 
	      (Format.sprintf "Source of clause %s not defined" (Clause.to_string clause))))
    with

      (* Clause is from input or theory axioms *)
      | Clause.TSTP_external_source _ 
      | Clause.TSTP_internal_source _ -> 

	(

	  (* Remember insertion of clause into list *)
	  Clause.ClauseHashtbl.add visited clause true;
	  
	  (* Add clause as leaf *)
	  get_parents'
	    visited 
	    (clause :: accum)
	    tl
	    
	)

      (* Clause is from global propositional subsumption *)
      | Clause.TSTP_inference_record 
	  (Clause.Global_subsumption max_clause_id, [parent]) -> 
	
	(* Get justification for simplification of clause *)
	let parents' = 
	  Prop_solver_exchange.justify_prop_subsumption 
	    max_clause_id
	    parent 
	    clause
	in

	(* Recurse to get parents of premises *)
	get_parents'
	  visited 
	  accum 
	  ((parent :: parents') @ (clause :: tl))
	  
      (* Clause is from other inference *)
      | Clause.TSTP_inference_record (_, parents) -> 

	(* Recurse to get parents of premises *)
	get_parents'
	  visited 
	  accum 
	  (parents @ (clause :: tl))
	  


(* Get parent clauses of a list of clauses *)
let get_parents clause_list = 
  List.rev 
    (get_parents' (Clause.ClauseHashtbl.create 101) [] clause_list)


let pp_bind ppf (var, term) = 
  Format.fprintf 
    ppf 
    "@[<h>bind(%a,$fot(%a))@]" 
    Var.pp_var var 
    Term.pp_term_tptp term 
  
let pp_clause_name_bind bind ppf clause = 
  Format.fprintf ppf "@[<hov>%a:[%a]@]" 
    Clause.pp_clause_name clause 
    (pp_any_list pp_bind ",") bind
  

(* Print the name of the BMC1 theory axiom *)
let pp_tstp_theory_bmc1 ppf = function 

  | Clause.TSTP_bmc1_path_axiom b -> 
    Format.fprintf ppf "bmc1,[path(%d)]" b

  | Clause.TSTP_bmc1_reachable_state_axiom b -> 
    Format.fprintf ppf "bmc1,[reachable_state(%d)]" b
    
  | Clause.TSTP_bmc1_reachable_state_on_bound_axiom b -> 
    Format.fprintf ppf "bmc1,[reachable_state_on_bound(%d)]" b
    
  | Clause.TSTP_bmc1_reachable_state_conj_axiom b -> 
    Format.fprintf ppf "bmc1,[reachable_state_conj(%d)]" b

  | Clause.TSTP_bmc1_only_bound_reachable_state_axiom b -> 
    Format.fprintf ppf "bmc1,[only_bound_reachable(%d)]" b
    
  | Clause.TSTP_bmc1_clock_axiom (b, s, _) -> 
    Format.fprintf ppf "bmc1,[clock(%a,%d)]" Symbol.pp_symbol s b

  | Clause.TSTP_bmc1_instantiated_clause (b, c) -> 
    Format.fprintf 
      ppf "bmc1,[bound_instantiate_clause(%a,%d)]" 
      Clause.pp_clause_name c 
      b
    

(* Print the name of a theory *)
let pp_tstp_theory ppf = function
  | Clause.TSTP_equality -> Format.fprintf ppf "equality"
  | Clause.TSTP_distinct -> Format.fprintf ppf "distinct"
  | Clause.TSTP_bmc1 a -> Format.fprintf ppf "%a" pp_tstp_theory_bmc1 a
  | Clause.TSTP_less -> Format.fprintf ppf "less"
  | Clause.TSTP_range -> Format.fprintf ppf "range"


(* Print name of inference rule and its useful info *)
let pp_inference_rule parents ppf = function 

  (* Useful info for instantiation are side parent clauses *)
  | Clause.Instantiation side_parents -> 

    Format.fprintf 
      ppf 
      "instantiation,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* Useful info for resolution are resolved literals *)
  | Clause.Resolution literals ->

    Format.fprintf 
      ppf 
      "resolution,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents
 
  (* Useful info for factoring are factored literals *)
  | Clause.Factoring literals ->

    Format.fprintf 
      ppf 
      "factoring,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* No useful info for global propositional subsumption *)
  | Clause.Global_subsumption _ -> 

    Format.fprintf 
      ppf 
      "global_propositional_subsumption,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* No useful info for forward subsumption resolution *)
  | Clause.Forward_subsumption_resolution -> 

    Format.fprintf 
      ppf 
      "forward_subsumption_resolution,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* No useful info for backward subsumption resolution *)
  | Clause.Backward_subsumption_resolution -> 

    Format.fprintf 
      ppf 
      "backward_subsumption_resolution,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* No useful info for splitting *)
  | Clause.Splitting symbols -> 

    Format.fprintf 
      ppf 
      "splitting,@,[status(thm),new_symbols(definition,[%a])],@,@[<hov 1>[%a]@]" 
      (pp_any_list Symbol.pp_symbol_tptp ",")
      symbols
      (pp_any_list Clause.pp_clause_name ",")
      parents

  (* No useful info for splitting *)
  | Clause.Grounding bindings -> 

    Format.fprintf 
      ppf 
      "grounding,@,[status(thm)],@,@[<hov 1>[%a]@]" 
      (pp_any_list (pp_clause_name_bind bindings) ",")
      parents


(* Print an inference record 

   An inference record is a pair of the inference rule with some useful
   information dependent on the rule and a set of parent clauses 
*)
let pp_tstp_inference_record clause ppf = function 

  (* Must get justification for global propositional subsumption here *)
  | Clause.Global_subsumption max_clause_id, [parent] -> 

    (* Get justification for simplification of clause *)
    let parents' = 
      Prop_solver_exchange.justify_prop_subsumption 
	max_clause_id 
	parent 
	clause
    in
    
    (* Simplified clause as first parent, then other parent clauses *)
    Format.fprintf 
      ppf 
      "global_propositional_subsumption,@,[status(thm)],@,@[<hov 1>[%a,@,%a]@]" 
      Clause.pp_clause_name
      parent
      (pp_any_list Clause.pp_clause_name ",")
      (List.filter ((!=) parent) parents')
    
  (* Must get justification for global propositional subsumption here *)
  | Clause.Global_subsumption _, _ -> 

    raise 
      (Failure 
	 "Global propositional subsumption of more than one parent clause")

  (* No special processing for remaining inference rules *)
  | inference_rule, parents -> 

    Format.fprintf 
      ppf 
      "%a" 
      (pp_inference_rule parents)
      inference_rule 
      

(* Print source of a clause *)
let pp_tstp_source clause ppf = function

  (* Clause is from a file *)
  | Clause.TSTP_external_source (Clause.TSTP_file_source (file, name)) -> 

    Format.fprintf ppf "file('%s', %s)" file name
      
  (* Clause is from a theory *)
  | Clause.TSTP_external_source (Clause.TSTP_theory theory) -> 
    
    Format.fprintf ppf "theory(%a)" pp_tstp_theory theory

  (* Clause is from an internal definition *)
  | Clause.TSTP_internal_source Clause.TSTP_definition ->

    Format.fprintf ppf "definition"

  (* Clause is from an internal assumption *)
  | Clause.TSTP_internal_source Clause.TSTP_assumption ->

    Format.fprintf ppf "assumption"

  (* Clause is from translation to purely equational clauses *)
  | Clause.TSTP_internal_source Clause.TSTP_non_eq_to_eq ->

    Format.fprintf ppf "non_eq_to_eq"

  (* Clause is from an inference *)
  | Clause.TSTP_inference_record inference_record ->
    
    Format.fprintf 
      ppf 
      "@[<hv 10>inference(%a)@]" 
      (pp_tstp_inference_record clause)
      inference_record

(* Print clause with source in TSTP format *)
let pp_clause_with_source ppf clause = 
  
  Format.fprintf 
    ppf 
    "@[<hv 4>cnf(%a,plain,@,@[<hv 2>%a,@]@,%a ).@]@\n@."
    Clause.pp_clause_name clause
    Clause.pp_clause_literals_tptp clause
    (pp_tstp_source clause) (Clause.get_tstp_source clause)


(* Print leaf clauses first *)
let pp_tstp_proof_resolution ppf clause =
  List.iter (pp_clause_with_source ppf) (get_parents [clause])


let pp_tstp_proof_unsat_core ppf clauses =

  Format.set_margin 72;

  (* Print derivation of clauses in unsat core *)
  List.iter (pp_clause_with_source ppf) (get_parents clauses);

  (* Separate non-ground clauses *)
  let gnd_clauses, non_gnd_clauses = 
    List.partition Clause.is_ground clauses 
  in

  (* Ground non-ground clauses *)
  let non_gnd_clauses' = 
    List.map Prop_solver_exchange.ground_clause non_gnd_clauses 
  in

  (* Print grounding of non-ground clauses in unsat core *)
  List.iter 
    (pp_clause_with_source ppf) 
    non_gnd_clauses';
    
  (* Replace a non ground clause with its ground clause in the list *)
  let rec fold_with_gnd_clauses accum gnd_clauses = function 
    | [] -> List.rev accum 
    | c :: tl when Clause.is_ground c -> 
      fold_with_gnd_clauses (c :: accum) gnd_clauses tl
    | c :: tl ->
      fold_with_gnd_clauses 
	(List.hd gnd_clauses :: accum) 
	(List.tl gnd_clauses) 
	tl
  in

  (* Replace each non ground clause with its ground clause *)
  let clauses' = fold_with_gnd_clauses [] non_gnd_clauses' clauses in

(*
  (* Get assumptions in solver *)
  let assumptions = Prop_solver_exchange.get_solver_assumptions_sat () in
*)

  (* Print refutation by minisat as a single inference *)
  Format.fprintf ppf
    "@[<hv 4>cnf(contradiction,plain,@,( $false ),@,@[<hv 10>inference(minisat,@,[status(thm)],@,@[<hov 1>[%a]@]@]) ).@]@\n@."
(*    (pp_any_list Clause.pp_clause_name ",") (gnd_clauses @ non_gnd_clauses') *)
    (pp_any_list Clause.pp_clause_name ",") clauses'




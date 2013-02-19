(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006 -2012 Konstantin Korovin and The University of Manchester.
This file is part of iProver - a theorem prover for first - order logic.

iProver is free software: you can redistribute it and / or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
iProver is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
See the GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with iProver. If not, see < http:// www.gnu.org / licenses />. *)
(*----------------------------------------------------------------------[C]-*)

open Lib
open Options

module ClauseHashtbl=Clause.Hashtbl

(* Get parent leaf clauses of a list of clauses *)
let rec get_leaves' visited accum = function
	
	(* No more clause histories to recurse *)
	| [] -> accum
	
	(* Clause already seen *)
	| (clause :: tl) when ClauseHashtbl.mem visited clause ->
	
	(* Skip clause *)
			get_leaves' visited accum tl
	
	(* New clause *)
	| clause :: tl ->
	
	(* Remember clause *)
			ClauseHashtbl.add visited clause ();
			
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
	get_leaves' (ClauseHashtbl.create 101) [] clause_list

(* Order clauses topologically: leaves at the beginning, root at the
end. First add all parents of a clause, then the clause.

visited is a hash table of clauses seen and a flag if the
clause has been added to the accumulator: a clause in the hash
table with a false value has been seen but not added to the list, a
clause with a true value is already in the list.
*)
let rec get_parents' visited accum = function
	
	(* No more clause histories to recurse *)
	| [] -> accum
	
	(* Clause already seen *)
	| (clause :: tl) when ClauseHashtbl.mem visited clause ->
	
	(* Format.eprintf "get_parents' (visited) %a@."
	Clause.pp_clause
	clause; *)
	
	(* Clause is already in the list *)
			if ClauseHashtbl.find visited clause then
				
				(* Skip clause *)
				get_parents' visited accum tl
			
			else
				
				(
					
					(* Remember insertion of clause into list *)
					ClauseHashtbl.add visited clause true;
					
					(* Add clause to list *)
					get_parents' visited (clause :: accum) tl
					
				)
	
	(* New clause *)
	| clause :: tl ->
	
	(* Format.eprintf "get_parents' (new) %a@."
	Clause.pp_clause
	clause; *)
	
	(* Remember recursion into parents of clause *)
			ClauseHashtbl.add visited clause false;
			
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
						ClauseHashtbl.add visited clause true;
						
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
		(get_parents' (ClauseHashtbl.create 101) [] clause_list)

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
			Format.fprintf ppf "bmc1,[reachable_state_(%d)]" b
	
	| Clause.TSTP_bmc1_reachable_sk_replacement (b, c) ->
			Format.fprintf
				ppf "bmc1,[reachable_sk_replacement(%a,%d)]"
				Clause.pp_clause_name c
				b
	
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
				"splitting,@,[splitting(split),new_symbols(definition,[%a])],@,@[<hov 1>[%a]@]"
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
	
	| Clause.Subtyping ->
			Format.fprintf
				ppf
				"subtyping,@,[status(esa)],@,@[<hov 1>[%a]@]"
				(pp_any_list Clause.pp_clause_name ",")
				parents
	
	| Clause.Flattening ->
			Format.fprintf
				ppf
				"flattening,@,[status(esa)],@,@[<hov 1>[%a]@]"
				(pp_any_list Clause.pp_clause_name ",")
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
let pp_tstp_source clausify_proof clause ppf = function
	
	(* Clause is from a file *)
	| Clause.TSTP_external_source (Clause.TSTP_file_source (file, name)) ->
	
	(* Rewrite source to match clausification proof? *)
			if clausify_proof then
				
				try
				
				(* Scan name of clause into u<n> *)
					let fof_id = Scanf.sscanf name "u%d" (function i -> i) in
					
					(* Output name of fof formula *)
					Format.fprintf
						ppf
						"inference(cnf_transformation,[],[f%d])"
						fof_id
				
				(* Name of clause is not u<n> *)
				with Scanf.Scan_failure _ ->
				
				(* Print source as it is *)
						Format.fprintf ppf "file('%s', %s)" file name
			
			else
				
				(* Print source as it is *)
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
let pp_clause_with_source clausify_proof ppf clause =
	
	Format.fprintf
		ppf
		"@[<hv 4>cnf(%a,plain,@,@[<hv 2>%a,@]@,%a ).@]@\n@."
		Clause.pp_clause_name clause
		Clause.pp_clause_literals_tptp clause
		(pp_tstp_source clausify_proof clause)
		(Clause.get_tstp_source clause)

(* Output a list of integers *)
let rec pp_clausify_proof_parents ppf = function
	| [] -> ()
	| [p] -> Format.fprintf ppf "%d" p
	| p :: tl ->
			pp_clausify_proof_parents ppf [p];
			Format.fprintf ppf ",";
			pp_clausify_proof_parents ppf tl

(* Output one entry of the hash table for the clausification proof *)
let pp_clausify_proof_line ppf f = function
	| s, p ->
			Format.fprintf ppf "%d: %a@\n%s@." f pp_clausify_proof_parents p s

(* Output contents of hash table for the clausification proof *)
let pp_clausify_proof ppf p =
	Hashtbl.iter (pp_clausify_proof_line ppf) p

(* Output clausification *)
let rec pp_clausification' visited clausify_proof ppf = function
	
	(* All parent clauses printed *)
	| [] -> ()
	
	(* Clause already printed *)
	| fof_id :: tl when Hashtbl.mem visited fof_id ->
			pp_clausification' visited clausify_proof ppf tl
	
	(* Clause not already printed *)
	| fof_id :: tl ->
	
			(
				
				try
				
				(* Get clause and parents from hash table *)
					let fof_clause, parents = Hashtbl.find clausify_proof fof_id in
					
					(* Print clause *)
					Format.fprintf ppf "%s@." fof_clause;
					
					(* Mark clause as printed *)
					Hashtbl.add visited fof_id true;
					
					(* Output parent clauses *)
					pp_clausification' visited clausify_proof ppf (parents @ tl)
				
				with Not_found -> ()
				
			)

(* Output clausification if clause is an input clause *)
let pp_clausification visited clausify_proof ppf clause =
	
	match Clause.get_tstp_source clause with
	
	(* Clause is from a file *)
	| Clause.TSTP_external_source (Clause.TSTP_file_source (_, name)) ->
	
			(
				
				try
				
				(* Scan name of clause into u<n> *)
					let fof_id = Scanf.sscanf name "u%d" (function i -> i) in
					
					(* Output clausification *)
					pp_clausification' visited clausify_proof ppf [fof_id]
				
				(* Skip if name of clause is not u<n> *)
				with Scanf.Scan_failure _ -> ()
				
			)
	
	(* Ignore clauses that are not input clauses *)
	| _ -> ()

(* Print derivation of clauses including clausification *)
let pp_clauses_with_clausification ppf clauses =
	
	(* Get parent clauses of unsat core clauses *)
	let parent_clauses = get_parents clauses in
	
	if
	
	(* Must output clausification for FOF problems *)
	(!ParseFiles.input_problem_type = Some ParseFiles.FOF) &&
	
	(* but cannot clausify again when input is stdin *)
	(not !current_options.stdin)
	
	then
		
		(
			
			(* Hash table for proof of clausification *)
			let clausify_proof = Hashtbl.create 1001 in
			
			(* Get command and options for clausification *)
			let clausify_cmd, clausify_arg =
				ParseFiles.clausifier_cmd_options ()
			in
			
			(* $TPTP for includes has already been set in ParseFiles on
			first clausification *)
			
			(* Array of arguments for clausify command *)
			let clausify_cmd_args =
				Array.of_list
					(clausify_cmd ::
						(Str.split (Str.regexp "[ ]+") (clausify_arg)))
			in
			
			(* Fill hash table with proof of clausification *)
			(
				
				(* Later support more than one clausifier, distinguish by
				name of executable *)
				match Filename.basename clausify_cmd with
				
				(* Vampire clausifier *)
				| "vclausify_rel" ->
				
				(* Clausify one input file and store proof in hash
				table *)
						let clausify_file file =
							
							(* Additional arguments for clausification proof *)
							let clausify_cmd_args_proof =
								[| "--print_clausifier_premises"; "on";
								"--proof"; "tptp";
								"--input_file"; file |]
							in
							
							(* Add arguments to previous arguments of
							clausification *)
							let clausify_cmd_args' =
								Array.append clausify_cmd_args clausify_cmd_args_proof
							in
							
							(* Copy of environment *)
							let env = Unix.environment () in
							
							(* Create pipe for stderr of command *)
							let cmd_stderr_out, cmd_stderr_in =
								Unix.pipe ()
							in
							
							(* Create input channel of pipe output *)
							let cmd_stderr_out_ch =
								Unix.in_channel_of_descr cmd_stderr_out
							in
							
							(* Open /dev/null for reading *)
							let devnull_in =
								Unix.openfile "/dev/null" [Unix.O_RDONLY] 0o640
							in
							
							(* Open /dev/null for writing *)
							let devnull_out =
								Unix.openfile "/dev/null" [Unix.O_WRONLY] 0o640
							in
							
							(* Create process *)
							let cmd_pid =
								Unix.create_process_env
									clausify_cmd
									clausify_cmd_args'
									env
									devnull_in
									devnull_out
									cmd_stderr_in
							in
							
							(* Close all files of process to prevent blocks *)
							Unix.close devnull_in;
							Unix.close devnull_out;
							Unix.close cmd_stderr_in;
							
							(* Parse output of clausifier *)
							let parse_out =
								Lexer_fof.parse clausify_proof cmd_stderr_out_ch
							in
							(* Wait for process to terminate *)
							let _cmd_pid_, _cmd_status =
								Unix.waitpid [Unix.WUNTRACED] cmd_pid
							in
							Unix.close cmd_stderr_out;
							parse_out
						(*
						(* Only continue if exited with 0 *)
						if cmd_status = Unix.WEXITED 0 then
						
						(* Parse output of clausifier *)
						Lexer_fof.parse clausify_proof cmd_stderr_out_ch
						*)
						in
						
						(* Clausify all input files again *)
						List.iter
							clausify_file
							!current_options.problem_files
				
				(* Unsupported clausifier *)
				| _ -> ()
				
			);
			(*
			Format.eprintf
			"%a@."
			pp_clausify_proof
			clausify_proof;
			*)
			(* Print derivation of clauses from input formulae *)
			List.iter
				(pp_clausification (Hashtbl.create 1001) clausify_proof ppf)
				parent_clauses;
			
			(* Print derivation of clauses in unsat core with rewriting
			of input clauses *)
			List.iter
				(pp_clause_with_source true ppf)
				parent_clauses;
			
		)
	
	else
		
		(
			
			(* Print derivation of clauses in unsat core *)
			List.iter (pp_clause_with_source false ppf) parent_clauses;
			
		)

(* Print leaf clauses first *)
let pp_tstp_proof_resolution ppf clause =
	
	(* Print derivation of empty clause including clausification *)
	pp_clauses_with_clausification ppf [clause]

(*
List.iter (pp_clause_with_source false ppf) (get_parents [clause])
*)

let pp_tstp_proof_unsat_core ppf clauses =
	
	(* Set width of line to 72, that works with emails *)
	Format.set_margin 72;
	
	(* Print derivation of clauses including clausification *)
	pp_clauses_with_clausification ppf clauses;
	
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
		(pp_clause_with_source false ppf)
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

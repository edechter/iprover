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
open Logic_interface

let addr_split_size = 10

type all_clauses = context


type raw_model = all_clauses

(*
let add_fun_term symb args = 
    TermDB.add_ref (Term.create_fun_term symb args) term_db_ref
*)

(* model node consists of a normalised literal, list of clauses  *)
(* where this literal is selected normalised w.r.t. the literal  *)
(*   *)
(*
type model_node =
{
model_lit : lit;
(* *)
mutable clause_set :
mutable constraint_set :
}
*)

(*
let build_model active_clauses = active_clauses
*)

(*----------------------------------------------------*)
let raw_model_to_stream s model =
	let f clause =
		if not (Clause.get_ps_in_active clause)
		then ()
		else
			begin
				s.stream_add_str "%---------------\n";
				Clause.to_stream s clause;
				s.stream_add_char ' ';
				Term.to_stream s (Clause.inst_get_sel_lit clause);
				s.stream_add_char '\n';
				s.stream_add_str ("is dead: "^(string_of_bool (Clause.get_is_dead clause))^"\n");
				s.stream_add_str ("is active: "^(string_of_bool (Clause.get_ps_in_active clause))^"\n");
				s.stream_add_str ("when born: "^(string_of_int (Clause.get_ps_when_born clause))^"\n");
				(try
					Dismatching.to_stream_constr_set s (Clause.get_inst_dismatching clause);
					s.stream_add_char '\n';
				with
					Clause.Dismatching_undef ->
						s.stream_add_str "Dism undef []\n");
			end
	in
	context_iter model f;
	s.stream_add_str "\n%---------------End Model--------------\n\n"

let out_raw_model model =
	raw_model_to_stream stdout_stream model

(*--------------------------------------------------------------------*)
(* Model representation:                                              *)
(* Several models can be extracted: 1) Positive 2) Negative 3) Mixed  *)
(* leterals a defined in the fixed model of the term algebra          *)
(*--------------------------------------------------------------------*)
(*
\forall x_1,..., x_n
(~) L(x_1,.., x_n) <->
(* we will  call it definition of a literal lit_def *)
[

\exists \bar { y }
[
(x_i_1 = t_1(\bar { y },\bar { x }) &..& x_i_m = t_m(\bar { y },\bar { x })
(* this corresponds to flattening of L(x,t,..) *)
(* let's call it subst_constr this also corresponds to the selected literal in a clause *)
(* we will pair list of clauses with this literal selected  with the set of dismatching constraints below *)

(* variables from \bar{y} can contain  some x_j below *)
&

(* this correspods to dismathcing  constraints collected from  *)
(* all active clauses where L(x,t,..) is selected              *)

\forall \bar { z } ((x_j_1 \not = s_1(\bar { z }) \/...\/ x_j_n \not = s_n(\bar { z }))) &
..............
\forall \bar { z } ((x_l_1 \not = g_1(\bar { z }) \/...\/ x_j_n \not = g_v(\bar { z })))
]
\/
......
\/
......
]

(* both subst_constr and dismathcing  constraints are represented as flat_subst, ordered and normalised *)
*)

(* there are three basic types of models positive, negative and implied *)
(* positive -- using positive definitions (\\forall x_1,..,x_n  (P(x_1,..,x_n) <=> (\\phi(x_1,..,x_n))))  *)
(* negative -- using negative definitions (\\forall x_1,..,x_n  (~P(x_1,..,x_n) <=> (\\phi(x_1,..,x_n)))) *)
(* small -- choosing between positive and negative definitions according to the size                      *)
(* implied -- definitions of the form (\\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <= (\\phi(x_1,..,x_n))))    *)
(*            if for some arguments a value of a predicate is not implied by these definitions            *)
(*            then we can complete the model by choosing an arbitrary value of this predicate on these arguments  *)
(* def_type is used to choose between <= and <=> and also when lit is undefined and <=> we need to add <=> $false *)
(* and when <= we can ommit the definition *)

type def_type = Def_Equiv | Def_Implied

(* positive:  *)

type flat_subst = Subst.flat_subst

(*--------------to_stream------------------*)
let model_pref_str =
	"%"^pref_str

let var_list_to_stream s v_list =
	List.iter (fun v ->
					Var.to_stream s v;
					s.stream_add_char ' '
		) v_list

let var_term_to_stream s (v, t) =
	Term.to_stream s t;
	s.stream_add_char '/';
	Var.to_stream s v

let to_stream_plain_fs s constr =
	s.stream_add_char '[';
	Lib.list_to_stream s var_term_to_stream constr ",";
	s.stream_add_char ']'

(* when we normalise clauses we have lit lists where the first literal is selected*)
let to_stream_plain_lit_list_first_selected s ll =
	s.stream_add_char '{';
	( match ll with
		| h:: tl ->
				s.stream_add_char '|';
				Term.to_stream s h;
				s.stream_add_char '|';
				(if (not (tl = []))
					then
						(s.stream_add_char ';';)
					else ()
				);
				Lib.list_to_stream s Term.to_stream tl ";";
		|[] -> failwith "model_inst: to_stream_plain_lit_list_first_selected at least one literal should be present"
	);
	s.stream_add_char '}'

(*------------------------------*)

let compare_vt (v1, t1) (v2, t2) =
	let v_cp = Var.compare v1 v2 in
	if v_cp = 0
	then
		Term.compare t1 t2
	else
		v_cp

(*[] is the smallest element, which is used to output [] first in maps and sets *)
let rec compare_flat_subst s1 s2 =
	match (s1, s2) with
	| (h1:: tl1, h2:: tl2) ->
			let h_cp = compare_vt h1 h2 in
			if h_cp = 0
			then
				compare_flat_subst tl1 tl2
			else
				h_cp
	| (h1:: tl,[]) -> 1
	| ([], h1:: tl) -> -1
	| ([],[]) -> 0

type flat_subst_vars =
	{
		flat_subst : flat_subst;
		(* flat_subst_vars is ordered list of vars \bar{y} in t_1(\bar{y})/x_0 ... t_n(\bar{y})/x_n *)
		(* used when we output the constraints  *)
		flat_subst_vars : var list
	}

(*we need to order flat_subst before adding to a set!*)
module FSVKey =
struct
	type t = flat_subst_vars
	let compare fsv1 fsv2 = compare_flat_subst fsv1.flat_subst fsv2.flat_subst
end

module FSVSet = Set.Make (FSVKey)

module FSVMap = Map.Make (FSVKey)

module VarMap = Map.Make (Var)

type dism_constr_set =
	| DCSet of FSVSet.t
	(* Subsumed means that all dismatching constraints are subsumed     *)
	(* by dismatching constr which is either undefined of is a renaming *)
	(* (over all vars in the clause)           *)
	(* so L(X)| (x=t & Subsumed ...) means \forall X (L(X) <=> (x=t...) *)
	| DCSSubsumed

type var_table = (var VarMap.t)

type var_table_ref = var_table ref

(*we pair old clause with the normalised lit list form this clause and constraint list*)
type norm_clause =
	(clause * ((lit list) * flat_subst list))
(* literal definition body is a map from subst_constraints into sets of dismatching constrints *)
(* paired with a list of clauses where the L\subst_constraint is selected  *)
(* dismatching constraints are normalised and only varibales in L are left *)
(*  clauses are also normalised such that L is first, vars renamed, including in dismatiching constr.*)

let to_stream_plain_norm_clause s (_clause, ((lit_list), flat_subst_list)) =
	s.stream_add_str "% ";
	to_stream_plain_lit_list_first_selected s lit_list;
	s.stream_add_str "\n% ";
	Lib.list_to_stream s to_stream_plain_fs flat_subst_list "\n% ";
	s.stream_add_char '\n'

let to_stream_plain_norm_clause_list s norm_clause_list =
	s.stream_add_str model_pref_str;
	s.stream_add_char '\n';
	Lib.list_to_stream s to_stream_plain_norm_clause norm_clause_list (model_pref_str^"\n");
	s.stream_add_char '\n'

type lit_def_body =
	(((dism_constr_set ref) * ((norm_clause list) ref)) FSVMap.t)

type lit_def =
	{
		
		(* this is a flattened normalised literal of the form (~)P(x_0,..,x_n)                       *)
		model_lit : lit;
		
		(* ordered list of vars in the literal                                                       *)
		model_lit_vars : var list;
		
		(* a) if lit_def_body is FSVMap.empty then this literal was not defined and this corresponds to          *)
		(*    \forall X ~L(X)    or \forall X (L(X) <=> $false) when output  sign(L(X)) type definition,         *)
		(*    if output "implied" definition then we do not need to output anyhting here (it's undefined)        *)
		(*    ( compl(sign L(X)) still can have "implied" definition)                                            *)
		(* b) if [] is a key in  lit_def_body, this corresponds to the empty subst_constr, there are still       *)
		(*    can be dismatching constraints corresponding to [], *)
		(*   But if the dism constr. set is empty/Subsumed then   *)
		(*   we have \forall X (L(X) <->  $true)   (all other instances of L(X) are subsumed by this)    *)
		(*   in this case we set always_true to true but still fill lit_def_body (for extra information/normalise clauses) *)
		(*   the number of constraints is 0 in this case                                                                   *)
		
		mutable model_lit_def_body : lit_def_body;
		
		(*----- below are filled when we constructed the model (could be filled during but too messy)---------*)
		(* if model_lit_undef = true then we in the a) situation *)
		
		mutable model_lit_undef : bool;
		mutable model_lit_always_true : bool;
		mutable model_lit_num_of_subst_constr : int;
		mutable model_lit_num_of_dism_constr : int;
	}

type model_node =
	{
		(* positive and negative definitions of the same predicate *)
		pos_lit_def : lit_def;
		neg_lit_def : lit_def;
	}

(* normal model is a map from predicates to model nodes definig these predicates *)
module NModel = Map.Make(Symbol)

type norm_model = (model_node NModel.t)

(* for a list of vars h::tl  returns var  next(h) *)
(* for [] returns first var                       *)

let next_top_var vtype vlist =
	match vlist with
	| h:: _ -> Var.get_next_var h
	|[] -> Var.get_first_var vtype

(*------------------------------------*)

(* var_list contains the list of new vars, max_var first *)
(* note new terms are not in term_db! *)

(*
let rec normalise_term_var' var_table_ref max_var_ref var_list_ref term =
match term with
| Term.Fun(sym, args, _) ->
let new_args =
Term.arg_map_left (normalise_term_var' var_table_ref max_var_ref var_list_ref) args in
Term.create_fun_term_args sym new_args
| Term.Var(v, _) ->
try
let new_v = VarMap.find v !var_table_ref in
Term.create_var_term new_v
with
Not_found ->
var_table_ref := VarMap.add v !max_var_ref !var_table_ref;
var_list_ref := (!max_var_ref):: (!var_list_ref);
let new_term = Term.create_var_term !max_var_ref in
max_var_ref := Var.get_next_var !max_var_ref;
new_term
*)
let bound_x = 0
let bound_y = 1

let rec normalise_term_var' renaming_env bound var_list_ref term =
	match term with
	| Term.Fun(sym, args, _) ->
			let new_args =
				Term.arg_map_left (normalise_term_var' renaming_env bound var_list_ref) args in
			Term.create_fun_term_args sym new_args
	| Term.Var(v, _) ->
			let bv = (bound, v) in
			let was_in_renaming = SubstBound.in_renaming renaming_env bv in
			let new_var = (SubstBound.find_renaming renaming_env bv) in
			(if (not was_in_renaming)
				then
					var_list_ref := (new_var)::(!var_list_ref)
				else ()
			);
			add_var_term new_var

(* takes an atom A(t0,..,tn) and makes  A(x_0,x_1,..,x_n)                     *)
(* renaming_env is a renaming from old varibles into new                      *)
(* (a map from old var to new vars)                                           *)
(* flat_subst will contain [(x_i_0,t'i_0));..;(x_i_k, t'_i_k)]                *)
(* where t'i_j  is normalised ti_j according to the renaming                  *)
(* and ti_j is either not a variable or a variable which has occurred before  *)
(*  t_'_i_j can contain both x-vars (vars from x_0,..,x_n)                    *)
(*  and y-vars (not x-vars), y-vars are existentially quantified later        *)
(* flat_subst corresponds to the subst_constr of this literal                 *)

let b_flat = 0

let rec flatten_args
		renaming_env x_var_list_ref flat_subst_ref args =
	match args with
	| h:: tl ->
		  let h_type = Term.get_term_type h in
  		(match h with
  			| Term.Var(v, _) ->
					 if (SubstBound.in_renaming renaming_env (b_flat,v))
						then
						(	
			       let next_var = SubstBound.get_next_unused_var renaming_env h_type in 							
							flat_subst_ref:= (next_var, h)::(!flat_subst_ref);
           		x_var_list_ref := next_var:: (!x_var_list_ref)							
						)
						else
						(
					 let next_var = (SubstBound.find_renaming renaming_env (b_flat,v)) in
				   x_var_list_ref := next_var:: (!x_var_list_ref)				
						)
				| Term.Fun _ ->
            (
						 let next_var = SubstBound.get_next_unused_var renaming_env h_type in 														
						flat_subst_ref:= (next_var, h)::(!flat_subst_ref);
	              	x_var_list_ref := next_var:: (!x_var_list_ref)		
             )
					);
			flatten_args
				renaming_env x_var_list_ref flat_subst_ref tl
	|[] -> ()

let normalise_flat_subst renaming_env bound y_var_list_ref flat_subst_ref =
	let rec f acc flat_subs =
		match flat_subs with
		| (v, t):: tl ->
				let new_t =
					TermDB.add_ref
						(normalise_term_var' renaming_env bound y_var_list_ref t) term_db_ref in
				f ((v, new_t):: acc) tl
		|[] -> acc
	in
	flat_subst_ref:= (f [] !flat_subst_ref)

(*
let normalise_clause var_table_ref lit_list =
let
normalise_term_var' var_table_ref max_var_ref var_list_ref term
*)

(*let normalise_dism_constr *)

let norm_and_flatten_args
		renaming_env x_var_list_ref y_var_list_ref flat_subst_ref args =
	flatten_args
		renaming_env x_var_list_ref flat_subst_ref args;
	flat_subst_ref:= List.rev !flat_subst_ref;
	normalise_flat_subst renaming_env b_flat y_var_list_ref flat_subst_ref;
	(* we need to reverse flat_subst_ref twice since the first time we need the right order for the renaming *)
	flat_subst_ref:= List.rev !flat_subst_ref;
	
	x_var_list_ref:= List.rev !x_var_list_ref;
	y_var_list_ref:= List.rev !y_var_list_ref

(*
let norm_clause
let norm_dism_constr
*)
(*
let norm_and_flatten_atom
var_table_ref x_var_list_ref y_var_list_ref flat_subst_ref atom =
match atom with
| Term.Fun(sym, args, _) ->
let new_args =
norm_and_flatten_args
var_table_ref x_var_list_ref y_var_list_ref flat_subst_ref args in
Term.create_fun_term_args sym new_args
| Term.Var _ ->
failwith "model_inst: norm_and_flatten_atom here should be a predicate\n"
*)

let extend_model clause model =
	let sel_lit = (Clause.inst_get_sel_lit clause) in
	let is_neg_lit = (Term.is_neg_lit sel_lit) in
	let sel_atom = (Term.get_atom sel_lit) in
	let x_var_list_ref = ref [] in
	let y_var_list_ref = ref [] in
	let flat_subst_ref = ref [] in
	let renaming_env = SubstBound.init_renaming_env () in 
	match sel_atom with
	| Term.Var _ -> failwith "model_inst: extend_model atom should not be a var"
	| Term.Fun(sym, args, _) ->
			norm_and_flatten_args
				renaming_env
				x_var_list_ref
				y_var_list_ref
				flat_subst_ref
				(Term.arg_to_list args);
				
			let var_term_list = List.map Term.create_var_term !x_var_list_ref in
		(*  let var_term_list = !x_var_list_ref in *)
	(*
					let new_flat_atom =
				(* if the symbol is equality it is replaced by symb_iprover_eq in order to avoid clash *)
				(* with "=" in formulas which is interpreted over the term algebra                     *)
				(* we do not change the symbol in normalised clauses since they do not participate in the definition *)
					if (sym == Symbol.symb_typed_equality)
					then
					( 
						add_fun_term sym var_term_list			
						)		
					else
						add_fun_term sym var_term_list 
					in
					*)
		  let new_flat_atom = add_fun_term sym var_term_list in
			let new_compl_flat_atom = add_compl_lit new_flat_atom in
			let (new_flat_lit, new_compl_flat_lit) =
				if (is_neg_lit)
				then
					(new_compl_flat_atom, new_flat_atom)
				else
					(new_flat_atom , new_compl_flat_atom)
			in
			(* this is the subsitution constraint x_1=t_1 ,.., x_n=t_n *)
			let subst_constr =
				{ flat_subst = !flat_subst_ref;
					flat_subst_vars = !y_var_list_ref
				}
			in
			(*--------------------Normalising clause (order literals selected first, *)
			(* apply the inverse of flattening and rename the rest of variables )---------*)
			(* apply flat_subst to flat atom  *)
			
			let new_norm_atom =
				let norm_args = List.map
						(fun v ->
									try
										List.assoc v !flat_subst_ref
									with
										Not_found ->
											Term.create_var_term v
						) !x_var_list_ref
				in
				TermDB.add_ref (Term.create_fun_term sym norm_args) term_db_ref
			in
			let norm_lit =
				if (is_neg_lit)
				then
					TermDB.add_ref (Term.compl_lit new_norm_atom) term_db_ref
				else
					new_norm_atom
			in
			let lits = Clause.get_literals clause in
			let rest_lits = List.filter (fun l -> not (l == sel_lit)) lits in

			let norm_rest_lits =
				let dummy_y_var_list_ref = ref [] in
				List.map
					(fun t ->
								TermDB.add_ref
									(normalise_term_var' renaming_env b_flat  dummy_y_var_list_ref t)
									term_db_ref
					) rest_lits in
			let norm_lits = norm_lit:: norm_rest_lits in
			
			(*------------------------End normalising the clause--------------*)
			
			(*-------------------Normalising dism. constraints---------------------*)
			let nomr_dism_constr dism_constr =
				(* first we need to normalise free vars: i.e t/x1, ..t_n/x_n we need to normalise x_i                                 *)
				(* then order subst according the new varible order, then normalise varibles in t_i (independently of var_table_ref)  *)
				let dc_norm_top_vars =
					List.map 
					(fun (v, t) ->
             if (SubstBound.in_renaming renaming_env (b_flat, v))
             then
							((SubstBound.find_renaming renaming_env (b_flat,v)),t)
						else																						
							failwith "model_inst: all vars should have been defined in var_table_ref"
						) dism_constr
				in
				let dc_ordered_top_vars =
					List.sort (fun (v1, _) (v2, _) -> Var.compare v1 v2) dc_norm_top_vars
				in
				(* this is the new clause representation of the dism. constr.*)
				let dc_clause_rep = dc_ordered_top_vars in
				(* for using dism in the model                                    *)
				(* we eliminate renaming part: y_i/x_i where y_i occurs only once *)
				(* for using dism in the clause we do not eliminate the renaming part (better reflect the implementation side)*)
				let single_var_table_ref = ref VarMap.empty in
				let non_single_var_table_ref = ref VarMap.empty in
				let rec s_var_term t =
					match t with
					| Term.Var (v, _) ->
							if (VarMap.mem v !non_single_var_table_ref)
							then ()
							else
							if (VarMap.mem v !single_var_table_ref)
							then
								(
									single_var_table_ref := VarMap.remove v !single_var_table_ref;
									non_single_var_table_ref := VarMap.add v v !non_single_var_table_ref
								)
							else
								(single_var_table_ref:= VarMap.add v v !single_var_table_ref)
					| Term.Fun (sym, args, _) ->
							Term.arg_iter s_var_term	args
				in
				List.iter (fun (_v, t) -> s_var_term t) dc_ordered_top_vars;
				let dc_removed_renamings =
					let rec f rest ((_, t) as e) =
						match t with
						| Term.Var (v, _) ->
								if (VarMap.mem v !single_var_table_ref)
								then
									(*it is a renaming -- remove*)
									rest
								else
									e:: rest
						| Term.Fun _ -> e:: rest
					in
					List.rev (List.fold_left f [] dc_ordered_top_vars)
				in
				(*!!!!!!! if t/x and x not in x_vars U y_vars than the empty constraint!!!!!!*)
				let dc_checked =
					if (List.exists
							(fun (v, _t) ->
										((not (List.mem v !x_var_list_ref)) && (not (List.mem v !y_var_list_ref)))
							)
					) dc_removed_renamings
					then []
					else
						dc_removed_renamings
				in
				(* no we rename defined varibles in dc (vars in t_i) *)
				(*let max_var_bound_dc_ref = ref !max_var_ref in*)
				let dc_y_var_list_ref = ref [] in
				let dc_model_rep =
					List.map
						(fun (v, t) ->
									(v,
										TermDB.add_ref
											(normalise_term_var' renaming_env b_flat dc_y_var_list_ref t)
											term_db_ref
									)
						) dc_checked
				in
				(* we store vars as well in dc_model_rep:  flat_subst_vars *)
				let dc_model_rep_vars =
					{
						flat_subst_vars = !dc_y_var_list_ref;
						flat_subst = dc_model_rep;
					}
				in
				(* first is clause representation and second is the model representation *)
				(dc_clause_rep, dc_model_rep_vars)
			in
			(*------------------nomr_dism_constr finished---------------*)
			let dism_constr_list =
				try
					Dismatching.to_flat_subst_list_constr_set (Clause.get_inst_dismatching clause)
				with
					Clause.Dismatching_undef -> []
			in
			let dc_list_clause_rep_ref = ref [] in
			let dc_list_model_rep_vars_ref = ref [] in
			List.iter
				(fun dc ->
							let (dc_clause_rep, dc_model_rep) = nomr_dism_constr dc in
							dc_list_clause_rep_ref:= dc_clause_rep:: (!dc_list_clause_rep_ref);
							(if not (dc_model_rep.flat_subst = [])
								then
									dc_list_model_rep_vars_ref:= dc_model_rep:: (!dc_list_model_rep_vars_ref)
							)
				) dism_constr_list;
			
			(*------------------------------Filling the Model----------------------------*)
			
			let renew_lit_def_body lit_def =
				let new_model_lit_def_body =
					try
						let (dism_constr_set_ref, norm_clause_list_ref) =
							FSVMap.find subst_constr (lit_def.model_lit_def_body)
						in
						(* a bit of useless work when DCSSubsumed we do not need to generate dc_list_clause_rep_ref *)
						(* but avoiding this creates a bit of a mess so leave it for the moment                     *)
						
						dism_constr_set_ref:=
						(match !dism_constr_set_ref with
							| DCSSubsumed -> DCSSubsumed
							| DCSet dc_set ->
									if (!dc_list_model_rep_vars_ref = [])
									then DCSSubsumed
									else
										DCSet(
											List.fold_left (fun set constr_vars -> FSVSet.add constr_vars set )
												dc_set !dc_list_model_rep_vars_ref;
										)
						);
						
						norm_clause_list_ref :=
						(clause, (norm_lits,!dc_list_clause_rep_ref)):: (!norm_clause_list_ref);
						lit_def.model_lit_def_body
					with
						Not_found ->
							let dism_constr_set_ref =
								ref
									(if (!dc_list_model_rep_vars_ref = [])
										then DCSSubsumed
										else
											DCSet(
												(List.fold_left (fun set constr_vars -> FSVSet.add constr_vars set )
														FSVSet.empty !dc_list_model_rep_vars_ref)
											)
									)
							in
							let norm_clause_list_ref = ref
									[(clause, (norm_lits, (!dc_list_clause_rep_ref)))] in
							
							FSVMap.add
								subst_constr
								(dism_constr_set_ref, norm_clause_list_ref)
								lit_def.model_lit_def_body
				in
				lit_def.model_lit_def_body <- new_model_lit_def_body
			in
			try
				let model_node = NModel.find sym model in
				let lit_def =
					if is_neg_lit
					then
						model_node.neg_lit_def
					else
						model_node.pos_lit_def
				in
				renew_lit_def_body lit_def;
				model
			with
				Not_found ->
			(* definiton for the same polarity  as lit *)
					let new_same_pol_lit_def =
						{
							model_lit = new_flat_lit;
							model_lit_vars = !x_var_list_ref;
							model_lit_def_body = FSVMap.empty;
							
							(* this will be  changed later in fill_stat_model *)
							model_lit_undef = false;
							model_lit_always_true = false;
							model_lit_num_of_subst_constr = 0;
							model_lit_num_of_dism_constr = 0;
						}
					in
					renew_lit_def_body new_same_pol_lit_def;
					(* definiton for the compl polarity  as lit *)
					let new_compl_pol_lit_def =
						{
							model_lit = new_compl_flat_lit;
							model_lit_vars = !x_var_list_ref;
							model_lit_def_body = FSVMap.empty;
							
							(* this will be  changed later in fill_stat_model *)
							model_lit_undef = false;
							model_lit_always_true = false;
							model_lit_num_of_subst_constr = 0;
							model_lit_num_of_dism_constr = 0;
						
						}
					(* we do not need to renew_lit_def_body for new_compl_pol_lit_def *)
					in
					let new_model_node =
						{
							pos_lit_def =
								(if is_neg_lit
									then new_compl_pol_lit_def
									else new_same_pol_lit_def);
							
							neg_lit_def =
								(if is_neg_lit
									then new_same_pol_lit_def
									else new_compl_pol_lit_def);
						
						}
					in
					let new_model = NModel.add sym new_model_node model in
					new_model

(*----------debug----------*)
(*
type lit_def_body = ((dism_constr_set ref) * ((norm_clause list) ref) FSVMap.t)

type lit_def =
{
(* this is a flattened normalised literal of the form (~)P(x_0,..,x_n) *)
model_lit : lit;
(* ordered list of vars in the literal *)
model_lit_vars : var list;
mutable model_lit_def_body : lit_def_body;
}

type model_node =
{
(* positive and negative definitions of the same predicate *)
pos_lit_def : lit_def;
neg_lit_def : lit_def;
}

(* normal model is a map from predicates to model nodes definig these predicates *)
module NModel = Map.Make(Symbol)

type norm_model = (model_node NModel.t)

*)
(*
stdout_stream.stream_add_str "\n normalised atom:\n";
Term.to_stream stdout_stream new_norm_atom;
stdout_stream.stream_add_str "\n normalised lit lis:\n";
Term.out_term_list norm_lits;
stdout_stream.stream_add_str "\nx_var_list_ref\n";
var_list_to_stream stdout_stream !x_var_list_ref;
stdout_stream.stream_add_str "\n!y_var_list_ref\n";
var_list_to_stream stdout_stream !y_var_list_ref;
stdout_stream.stream_add_str "\n!flat_subst_ref\n";
to_stream_plain_fs stdout_stream !flat_subst_ref
| Term.Var _ ->
failwith "model_inst: norm_and_flatten_atom here should be a predicate\n"
*)

(* stdout_stream.stream_add_str (pref_str^"Building Model"); *)
(* returns the model *)

let test clause model =
	out_str "\n!!!Begin Debug!!!!!\n";
	Dismatching.to_stream_constr_set stdout_stream (Clause.get_inst_dismatching clause);
	out_str "\n!!!End Debug!!!!!\n";
	model

let test_iter clause =
	if not (Clause.get_ps_in_active clause)
	then ()
	else
		(
			out_str "\n!!!Begin Debug!!!!!\n";
			Dismatching.to_stream_constr_set stdout_stream (Clause.get_inst_dismatching clause);
			out_str "\n!!!End Debug!!!!!\n"
		)

(*---------------- fills statistics and extras in model -------------*)
(*
mutable model_lit_undef : bool;
mutable model_lit_always_true : bool;
mutable model_lit_num_of_subs_constr : int;
mutable model_lit_num_of_dism_constr : int;
*)

let fill_stat_model model =
	let fill_lit_def ld =
		if (ld.model_lit_def_body = FSVMap.empty)
		then
			(
				ld.model_lit_undef <- true;
				ld.model_lit_num_of_subst_constr <- 0;
				ld.model_lit_num_of_dism_constr <- 0;
			)
		else
			begin
				let is_always_true =
					try
						let empty_subs_constr = { flat_subst_vars = []; flat_subst = []} in
						let (dism_constr_set_ref, _norm_clause_list_ref) = FSVMap.find empty_subs_constr ld.model_lit_def_body in
						match !dism_constr_set_ref with
						| DCSet s ->
								if s = FSVSet.empty
								then true
								else false
						| DCSSubsumed -> true
					with
						Not_found -> false
				in
				if is_always_true
				then
					(
						ld.model_lit_always_true <- true;
						ld.model_lit_num_of_subst_constr <- 0;
						ld.model_lit_num_of_dism_constr <- 0;
					)
				else
					(
						let f _subst_constr (dism_constr_set_ref, _norm_clause_list_ref) =
							ld.model_lit_num_of_subst_constr <- (ld.model_lit_num_of_subst_constr +1);
							(match !dism_constr_set_ref with
								| DCSet s ->
										ld.model_lit_num_of_dism_constr <- ld.model_lit_num_of_dism_constr + (FSVSet.cardinal s)
								| DCSSubsumed -> ()
							)
						in
						FSVMap.iter f ld.model_lit_def_body
					)
			end
	in
	let f _symb model_node =
		fill_lit_def model_node.pos_lit_def;
		fill_lit_def model_node.neg_lit_def
	in
	NModel.iter f model

let build_model all_clauses filtered_out_clauses =
	(* debug *)
	
	(*
	out_str "\n\n-----Debug Out Raw Model\n\n";
	out_raw_model all_clauses;
	*)
	
	stdout_stream.stream_add_str (pref_str^"Building Model...");
	let empty_model = NModel.empty in
	
	(* out_str "\n-------All clauses------\n";
	ClauseAssignDB.iter (fun c -> out_str ((Clause.to_string c)^"\n")) all_clauses;
	out_str "\n-------End All clauses------\n";
	*)
	
	(* first add model for fitered_out_clauses (by prep_sem_filter_unif) *)
	let model_filtered_out =
		List.fold_left
			(fun model clause -> extend_model clause model)
			empty_model
			filtered_out_clauses
	in
	(* extened the model to the rest of clauses *)
	let final_model =
		context_fold all_clauses
			(fun clause model ->
						if (Clause.get_ps_in_active clause)
						then extend_model clause model
						else model
			)
			model_filtered_out
	in
	fill_stat_model final_model;
	stdout_stream.stream_add_str ("Done\n");
	final_model

type model = norm_model

(*type model = raw_model *)
(*let build_model active_clauses = active_clauses*)

(*--------------- To stream -------------------*)

let to_stream_var_list s vl =
	s.stream_add_char '[';
	list_to_stream s Var.to_stream vl ",";
	s.stream_add_char ']'

(* eq_sign_str either  = or != *)
let to_stream_vt eq_sign_str s (v, t) =
	Var.to_stream s v;
	s.stream_add_str eq_sign_str;
	Term.to_stream s t

(* eq_sign_str either  = or !=, con_str is either "&" or "|" *)
let to_stream_fs eq_sign_str con_str s constr =
	s.stream_add_str "( ";
	Lib.list_to_stream s (to_stream_vt eq_sign_str) constr (" "^con_str^" ");
	s.stream_add_str " )"

(* returns (nonempty_quant, nonempty_body) in order to close brackets/add leading &  later*)
let to_stream_subs_constr s subs_constr =
	let nonempty_quant_ref = ref false in
	let nonempty_body_ref = ref false in
	
	(if subs_constr.flat_subst_vars = []
		then ()
		else
			(
				nonempty_quant_ref:= true;
				to_stream_space s 12;
				s.stream_add_str "? ";
				to_stream_var_list s subs_constr.flat_subst_vars;
				s.stream_add_str " : \n";
			)
	);
	to_stream_space s 14;
	s.stream_add_str "(\n";
	
	(if (subs_constr.flat_subst = [])
		then () (*(s.stream_add_char '\n')*)
		else
			(nonempty_body_ref := true;
				to_stream_space s 16;
				to_stream_fs "=" "&" s subs_constr.flat_subst
			)
	);
	(!nonempty_quant_ref, !nonempty_body_ref)
(*
(if subs_constr.flat_subst_vars = []
then ()
else
to_stream_space s 15;
s.stream_add_str ")\n"  (* (? end should be after all dism constr *)
)
*)

let to_stream_dism_constr_set exists_constr_before s dc_set =
	(* FSVSet.empty never happens since we would add [] constr which would simplified to DCSSubsumed *)
	if (dc_set = FSVSet.empty)
	then
		(to_stream_space s 15;
			s.stream_add_str "$true";)
	else
		begin
			let is_first_dc = ref (not exists_constr_before) in
			let f dc =
				(if (not !is_first_dc)
					then
						(s.stream_add_str "\n";
							to_stream_space s 15;
							s.stream_add_str "&\n";)
					else (is_first_dc:= false;)
				);
				
				to_stream_space s 16;
				(if dc.flat_subst_vars = []
					then ()
					else
						(
							s.stream_add_str "! ";
							to_stream_var_list s dc.flat_subst_vars;
							s.stream_add_str " : ";
						)
				);
				(if (dc.flat_subst = [])
					then ()
					else
						(
							to_stream_fs "!=" "|" s dc.flat_subst
						)
				);
			in
			FSVSet.iter f dc_set
		end

let to_stream_lit_def_body s opt lit_def_body =
	(* since we fill_stat_model lit_def_body = FSVMap.empty would result to          *)
	(* ld.model_lit_undef                 <- true; and would be considered before in  to_stream_lit_def *)
	assert (not (lit_def_body = FSVMap.empty));
	begin
		to_stream_space s 11;
		s.stream_add_str "(\n"; (* (.. | ..)*)
		(*  if it is not first then we add \n | \n before the constr *)
		let is_first_subs_constr = ref true in
		
		let f subs_constr (dism_constr_set_ref, norm_clause_list_ref) =
			(
				(if (not !is_first_subs_constr)
					then
						(s.stream_add_char '\n';
							to_stream_space s 12;
							s.stream_add_str " | \n";)
					else
						(is_first_subs_constr:= false;)
				);
				
				let (nonempty_quant, nonempty_body) = to_stream_subs_constr s subs_constr in
				(
					match !dism_constr_set_ref with
					| DCSet dc_set ->
							to_stream_dism_constr_set nonempty_body s dc_set;
					| DCSSubsumed -> ()
				);
				
				(* FSVMap.t *)
				(* ( if nonempty_quant
				then *)
				(s.stream_add_char '\n';
					to_stream_space s 14;
					s.stream_add_str ")\n";  (* end \(? from subs_constr *)
				);
				(if (opt = Model_Debug)
					then
						to_stream_plain_norm_clause_list s !norm_clause_list_ref
					else ()
				)
				
				(* else ()
				);*)
			)
		in
		FSVMap.iter f lit_def_body;
		s.stream_add_char '\n';
		to_stream_space s 11;
		s.stream_add_str ")\n"; (* end (.. | ..)*)
	end

(* con_str if either "<=>"  or "<=" equivalence or implication definition *)
let def_type_to_con_str def_type =
	match def_type with
	| Def_Equiv -> "<=>"
	| Def_Implied -> "<="

let to_stream_lit_def s opt def_type lit_def =
	(*
	out_str ("\n%--- model_lit_undef:"^(string_of_bool lit_def.model_lit_undef)^"\n");
	out_str ("\n%--- lit_def.model_lit_always_true: "^(string_of_bool lit_def.model_lit_always_true)^"\n");
	out_str ("\n%--- lit_def.model_lit_num_of_subs_constr : "^(string_of_int lit_def.model_lit_num_of_subst_constr)^"\n");
	out_str ("\n%--- lit_def.model_lit_num_of_dism_constr : "^(string_of_int lit_def.model_lit_num_of_dism_constr)^"\n");
	*)
	
	(* do not need to output anything if "<=" and lit was not defined  *)
	(* if "<=>" and lit is not defined we need "L <=> $false "         *)
	if (def_type = Def_Implied) && (lit_def.model_lit_undef)
	then (s.stream_add_str (model_pref_str^"Empty\n" ))
	else
		begin
			s.stream_add_str "fof(lit_def,axiom,\n";
			(*---! [X1,...,Xn] : \n-----*)
			(if (lit_def.model_lit_vars = [])
				then ()
				else
					(to_stream_space s 4;
						s.stream_add_str "(! ";
						to_stream_var_list s lit_def.model_lit_vars;
						s.stream_add_str " : \n";
					)
			);
			(*--------(L(X1,..,Xn) <=>/<=\n----*)
			to_stream_space s 6;
			s.stream_add_str "( ";
			Term.to_stream s lit_def.model_lit;
			s.stream_add_str (" "^(def_type_to_con_str def_type)^"\n");
			
			(*----definition body------*)
			(if lit_def.model_lit_always_true
				then
					(
						if (not (opt = Model_Debug))
						then
							(
								to_stream_space s 10;
								s.stream_add_str "$true\n";
							)
						else
							(
								to_stream_space s 10;
								s.stream_add_str "% $true\n";
								to_stream_lit_def_body s opt lit_def.model_lit_def_body;
							)
					)
				else
					(if lit_def.model_lit_undef
						then
							( assert (not (def_type = Def_Implied));
								to_stream_space s 10;
								s.stream_add_str "$false\n"
							)
						else
							(
								to_stream_lit_def_body s opt lit_def.model_lit_def_body;	)
					)
			);
			to_stream_space s 6; s.stream_add_str ")\n"; (* end (L(..) ..*)
			
			(if (lit_def.model_lit_vars = [])
				then ()
				else
					(to_stream_space s 4; s.stream_add_str ")\n";) (* end (! *)
			);
			
			to_stream_space s 3; s.stream_add_str ").\n" (* end fof(apt_def,axiom,( *)
		end
(*
model_lit : lit;

model_lit_vars : var list;
mutable model_lit_def_body : lit_def_body;

*)

let to_stream_model s opt model =
	if (opt = Model_None)
	then ()
	else
		(
			let def_type =
				match opt with
				| Model_Pos | Model_Neg | Model_Small | Model_Intel -> Def_Equiv
				| Model_Implied | Model_Debug -> Def_Implied
				| Model_None -> failwith ("model_inst: Model_None")
			in
			s.stream_add_char '\n';
			s.stream_add_str
				(model_pref_str^"The model is defined over ground terms (initial term algebra).\n"^
					model_pref_str^"Predicates are defined as (\\forall x_1,..,x_n  ((~)P(x_1,..,x_n) "^(def_type_to_con_str def_type)^" (\\phi(x_1,..,x_n)))) \n"^
					model_pref_str^"where \\phi is a formula over the term algebra.\n"^
					model_pref_str^"If we have equality in the problem then it is also defined as a predicate above, \n"^
					model_pref_str^"with \"=\" on the right-hand-side of the definition interpreted over the term algebra "
					^(Symbol.to_string Symbol.symb_term_algebra_type)^"\n"^
					model_pref_str^"See help for --sat_out_model for different model outputs.\n"^
					model_pref_str^"equality_sorted(X0,X1,X2) can be used in the place of usual \"=\"\n"^
					model_pref_str^"where the first argument stands for the sort ($i in the unsorted case)\n");
			
			s.stream_add_str "\n\n% SZS output start Model \n\n";
			
			let f key_sym model_node =
				s.stream_add_char '\n';
				
				let (out_pos, out_neg) =
					match opt with
					| Model_Pos -> (true, false)
					| Model_Neg -> (false, true)
					| Model_Small | Model_Intel ->
							let pos_score =
								model_node.pos_lit_def.model_lit_num_of_subst_constr
								+ model_node.pos_lit_def.model_lit_num_of_dism_constr
							in
							let neg_score =
								model_node.neg_lit_def.model_lit_num_of_subst_constr
								+ model_node.neg_lit_def.model_lit_num_of_dism_constr
							in
							if (pos_score <= neg_score)
							then (true, false)
							else (false, true)
					| Model_Implied | Model_Debug -> (true, true)
					| Model_None -> failwith ("model_inst: Model_None")
				in
				(if out_pos
					then
						(s.stream_add_str (model_pref_str^"Positive definition of "
									^(Symbol.to_string key_sym)^" \n" );
							to_stream_lit_def s opt def_type model_node.pos_lit_def;)
					else ()
				);
				(
					if out_neg
					then
						(s.stream_add_str (model_pref_str^"Negative definition of "
									^(Symbol.to_string key_sym)^" \n" );
							to_stream_lit_def s opt def_type model_node.neg_lit_def;
						)
					else ()
				)
			in
			NModel.iter f model;
			s.stream_add_str "\n\n% SZS output end Model \n\n"
		)

(*------------Experimental part for memory verification---------*)

let neg_conjectures_ref = Parser_types.neg_conjectures

(*
let is_state_type_symb symb =
match (Symbol.get_name symb) with
|"$state_type" -> true
| _ -> false

let is_address_type_symb symb =
match (Symbol.get_name symb) with
|"$address_type" -> true
| _ -> false

let is_bitindex_type_symb symb =
match (Symbol.get_name symb) with
|"$bitindex_type" -> true
| _ -> false

*)

(* get a value of predicate in the model with ground arguments *)
let get_ground_pred_value model pred_term =
(*	let var_table_ref = ref VarMap.empty in*)
	let x_var_list_ref = ref [] in
	let y_var_list_ref = ref [] in
	let flat_subst_ref = ref [] in
	(*let max_var_ref = ref (Var.get_first_var ()) in*)
 let renaming_env = SubstBound.init_renaming_env () in
		match pred_term with
	| Term.Fun(symb, args, _) ->
			norm_and_flatten_args
				renaming_env
				x_var_list_ref
				y_var_list_ref
				flat_subst_ref
				(Term.arg_to_list args);
			let subst_constr =
				{ flat_subst = !flat_subst_ref;
					flat_subst_vars = !y_var_list_ref
				}
			in
			let model_node = NModel.find symb model in
			let pos_lit_def = model_node.pos_lit_def in
			let neg_lit_def = model_node.neg_lit_def in
			if (FSVMap.mem subst_constr (pos_lit_def.model_lit_def_body))
			then Def(true)
			else
			if (FSVMap.mem subst_constr (neg_lit_def.model_lit_def_body))
			then
				Def(false)
			else
				Undef
	| Term.Var _ -> failwith "get_ground_pred_value: should not be a var"

let ground_pred_value_to_str model pred_term =
	let val_str =
		match (get_ground_pred_value model pred_term) with
		| Def true -> "1"
		| Def false -> "0"
		| Undef -> "Undef"
	in
	(Term.to_string pred_term)^":"^val_str

(*---------------------*)

let get_bitindex_from_str str =
	try
		let name = Str.string_before str 8 in
		match name with
		|"$$bitIndex" ->
				Def((int_of_string (Str.string_after str 8)))
		| _ -> Undef
	with
	(* Str.string_before can raise Invalid_argument and int_of_string can rise Failure *)
		Failure _ | Invalid_argument _ -> Undef

let addr_val_symb () =
	try
		SymbolDB.find
			(Symbol.create_template_key_symb "addressVal") !symbol_db_ref
	with
		Not_found -> failwith "addr_val_symb: addressVal was not defined"

(* address_val:  list of indexes with "true" value*)
type address_pos_val = int list

let get_ind_from_bit_ind_term bit_ind_term =
	let bitind_name = (Symbol.get_name (Term.get_top_symb bit_ind_term)) in
	get_bitindex_from_str bitind_name

(* returns address_pos_val list of indecies where addr_const is true *)
(* we can do similar from the negative side                          *)
(* or from both, then we can have "don't care" bits *)
let address_pos_val model addr_const =
	let add_val_symb = addr_val_symb () in
	let model_node = NModel.find add_val_symb model in
	let pos_lit_def = model_node.pos_lit_def in
	let f key_subs _ rest =
		match key_subs.flat_subst with
		|[(_, addr_in); (_, true_bitind_term)] ->
				if addr_in == addr_const
				then
					(
						match (get_ind_from_bit_ind_term true_bitind_term) with
						| Def(i) ->
								(i:: rest)
						| Undef -> rest
					)
				else rest
		| _ -> rest
	in
	let unsorted_addr_pos_val = FSVMap.fold f (pos_lit_def.model_lit_def_body) [] in
	List.sort Pervasives.compare unsorted_addr_pos_val

(* *)
let address_pos_val_to_string addr_pos_val =
	(* have addr_pos_val [2;..]*)
	(*  ["0:0";"1:0";"2:1";...;"n:b"] *)
	let rec f current_index next_true_index addr_val_rest out_str_rest =
		if current_index < next_true_index
		then
			let new_out_str_rest = ((string_of_int current_index)^":0"):: out_str_rest in
			let new_current_index = current_index +1 in
			f new_current_index next_true_index addr_val_rest new_out_str_rest
		else
			(*current_index = next_true_index*)
			let new_out_str_rest = ((string_of_int current_index)^":1"):: out_str_rest in
			match addr_val_rest with
			| new_next_true_index:: new_addr_val_rest ->
			
					let new_current_index = current_index +1 in
					f new_current_index new_next_true_index new_addr_val_rest new_out_str_rest
			|[] -> new_out_str_rest
	in
	let str_list =
		match addr_pos_val with
		| h:: tl ->
				List.rev (f 0 h tl [])
		|[] -> []
	in
	if str_list = []
	then "all 0" (* all zero *)
	else (String.concat " " str_list)

(* low bits first [0;1;0;...;b;1]                   *)
(* we assume that the rest could be filled with 0's *)

let norm_addr_pos_val_lsb addr_pos_val =
	let rec f current_index next_true_index addr_val_rest out_list_rest =
		if current_index < next_true_index
		then
			let new_out_list_rest = 0:: out_list_rest in
			let new_current_index = current_index +1 in
			f new_current_index next_true_index addr_val_rest new_out_list_rest
		else
			(*current_index = next_true_index*)
			let new_out_list_rest = 1:: out_list_rest in
			match addr_val_rest with
			| new_next_true_index:: new_addr_val_rest ->
			
					let new_current_index = current_index +1 in
					f new_current_index new_next_true_index new_addr_val_rest new_out_list_rest
			|[] -> new_out_list_rest
	in
	let list =
		match addr_pos_val with
		| h:: tl ->
				List.rev (f 0 h tl [])
		|[] -> []
	in
	list

(* normalise to the form most significat first MSB, where we fill fornt with 0s *)
let norm_addr_pos_val_to_msb fill_to_length addr_pos_val =
	let lsb_list = norm_addr_pos_val_lsb addr_pos_val in
	let lsb_length = List.length lsb_list in
	let num_of_zeros = fill_to_length - lsb_length in
	let msb_basic = List.rev lsb_list in
	if num_of_zeros <= 0
	then msb_basic
	else
		(
			let zero_list = list_n num_of_zeros 0 in
			zero_list@(msb_basic)
		)

(* head corr. n=1, returns rest of the list *)
let rec apply_to_first_n_rest f n list =
	if n <=0
	then
		list
	else
		(match list with
			| h:: tl ->
					f h;
					apply_to_first_n_rest f (n -1) tl
			|[] -> []
		)

(* we split bits with space every split_size bits starting from right*)
let out_msb_with_split slpit_size msb_list =
	assert (slpit_size >0);
	let msb_length = List.length msb_list in
	if(msb_length <= slpit_size)
	then
		List.iter (fun b -> print_int b) msb_list
	else
		let first_chunk = msb_length mod slpit_size in
		let rest_msb = apply_to_first_n_rest print_int first_chunk msb_list in
		(* rest msb is divisible by slpit_size *)
		
		let rec print_splits msb_left =
			if (msb_left = [])
			then ()
			else
				(
					print_char ' ';
					let new_msb = apply_to_first_n_rest print_int slpit_size msb_left in
					print_splits new_msb;
				)
		in
		print_splits rest_msb

(* eq_proper_val t_type t flat_subst: *)
(* we have typed_equality(eq_type, u,v) *)
(* the corresponding flat substitution is [(x_0,eq_type), (x_1,u), (x_2,v)] *)
(* check that eq_type == type, u==t and not (v == t)  (so it is proper and not t=t)     *)

let eq_proper_val t_type t flat_subst =
	match flat_subst with
	|[(_, eq_type); (_, u); (_, v)] ->
			if
			(
				(eq_type == t_type)
				&&
				(u == t)
				&&
				(not (v == t))
			)
			then Some v
			else None
	| _ -> None

let get_value_type_term symb =
	match (Symbol.get_stype_args_val symb) with
	| Def((_, ctype)) ->
			(
				try
					TermDB.find (Term.create_fun_term ctype []) !term_db_ref
				with
					Not_found ->
						failwith ("get_value_type_term: ctype term does not exist")
			)
	| Undef -> failwith ("get_value_type_term: type  was not defined")

let constant_val model const_term =
	let const_symb = Term.get_top_symb const_term in
	let const_type = get_value_type_term const_symb in
	let eq_model_node = NModel.find Symbol.symb_typed_equality model in
	let eq_pos_lit_def = eq_model_node.pos_lit_def in
	let eq_model_lit_def_body = eq_pos_lit_def.model_lit_def_body in
	let const_val_ref = ref None in
	let f key_subst _ =
		match !const_val_ref with
		| None ->
				(match (eq_proper_val
							const_type
							const_term
							(key_subst.flat_subst))
					with
					| Some v ->
							const_val_ref := Some v
					| None -> ()
				)
		| Some _ -> ()
	in
	FSVMap.iter f eq_model_lit_def_body;
	!const_val_ref

(*returns (skolem_bound, value) pair *)
let get_counter_ex_bound model =
	let counter_ex_bound = ref None in
	let f clause =
		match (Clause.get_skolem_bound_clause clause)
		with
		| Some(sk_bound) ->
				(match (constant_val model sk_bound) with
					| Some(sk_val) ->
							counter_ex_bound := Some ((sk_bound, sk_val));
							true
					| None -> failwith ("No value for state skolem constant"^(Term.to_string sk_bound)^"is found")
				)
		| None -> false
	in
	ignore(List.exists f !neg_conjectures_ref);
	!counter_ex_bound

let term_value_pair_to_string (t, s) =
	(Term.to_string t)^" = "^(Term.to_string s)

(* returns list of ground (with skolem constants) *)
(* memories and bitvector predicates occuring in conjectures *)
(* can be via hash tables but can not be botherd at the moment *)
let list_add_new list e =
	if List.exists (fun le -> (le == e)) list
	then list
	else e:: list

let get_conj_ground_mem_bitvec_preds () =
	let mem_list_ref = ref [] in
	let bitvec_pred_ref = ref [] in
	let f_clause clause =
		let f_lit lit =
			if (Term.is_ground lit)
			then
				let atom = Term.get_atom lit in
				let top_symb = (Term.get_top_symb atom) in
				if (Symbol.is_a_memory_pred_symb top_symb)
				then
					(mem_list_ref:= list_add_new (!mem_list_ref) atom)
				else
				if (Symbol.is_a_bitvec_pred_symb top_symb)
				then
					(bitvec_pred_ref:= list_add_new (!bitvec_pred_ref) atom)
				else ()
		in
		Clause.iter f_lit clause
	in
	List.iter f_clause !neg_conjectures_ref;
	(!mem_list_ref, !bitvec_pred_ref)

(*
let get_states_addr_bitindex_sk_from_clauses clause_list =
let state_list_ref = ref [] in
let addr_list_ref = ref [] in
let bitindex_list_ref = ref [] in
let add_const term =
*)

let get_from_states_addr_bitindex_sk_lists mem_pred_list bitvec_pred_list =
	let state_list_ref = ref [] in
	let addr_list_ref = ref [] in
	let bitindex_list_ref = ref [] in
	let f_mem pred =
		match pred with
		| Term.Fun (_symb, args, _) ->
				(match (Term.arg_to_list args) with
					|[state; addr; bitindex] ->
							(if (Term.is_skolem_const state)
								then
									state_list_ref := list_add_new !state_list_ref state
								else ()
							);
							(if (Term.is_skolem_const addr)
								then
									addr_list_ref := list_add_new !addr_list_ref addr
								else ()
							);
							(if (Term.is_skolem_const bitindex)
								then
									bitindex_list_ref := list_add_new !bitindex_list_ref bitindex
								else ()
							);
							()
					| _ -> failwith "get_from_mem_states_addr_bitindex_sk_lists: not memory"
				)
		| Term.Var _ -> failwith "get_from_mem_states_addr_bitindex_sk_lists"
	in
	List.iter f_mem mem_pred_list;
	let f_bitvec pred =
		match pred with
		| Term.Fun (_symb, args, _) ->
				(match (Term.arg_to_list args) with
					|[state; bitindex] ->
							(if (Term.is_skolem_const state)
								then
									state_list_ref := list_add_new !state_list_ref state
								else ()
							);
							(if (Term.is_skolem_const bitindex)
								then
									bitindex_list_ref := list_add_new !bitindex_list_ref bitindex
								else ()
							);
							()
					| _ -> failwith "get_from_mem_states_addr_bitindex_sk_lists: not bit-vector"
				)
		| Term.Var _ -> failwith "get_from_mem_states_addr_bitindex_sk_lists"
	in
	List.iter f_bitvec bitvec_pred_list;
	(!state_list_ref,!addr_list_ref,!bitindex_list_ref)

module ListKey =
struct
	type t = int list
	let compare = compare
end

module LMap = Map.Make (ListKey)

(*
type addr_type =
{ addr : Term.term;
addr_value : int list
}
*)

(* is used to share (find) equal addresses; in the leaves we have equal addresses *)

type address_map = ((Term.term list) ref) LMap.t

let add_address_to_map addr_map addr_pos_value addr =
	try
		let addr_list_ref = (LMap.find addr_pos_value addr_map) in
		addr_list_ref:= addr::!addr_list_ref;
		addr_map
	with
		Not_found ->
			LMap.add addr_pos_value (ref [addr]) addr_map

let get_max_length_addr_map addr_map =
	let f list _ curr_max =
		let list_ln = (List.length list) in
		if list_ln > 0
		then
			let last_pos = List.nth list (list_ln -1) in
			if (last_pos > curr_max)
			then last_pos
			else curr_max
		else curr_max
	in
	(LMap.fold f addr_map 0) +1

(*-------------bit-value preds----------*)
(* consider bit vectors or memories bv(state,i), mem(state,addr,i) *)
(* if state and addr is a fixed constant then the pred. value (depending on i) *)
(* can be represented as an bit-vector 0100101.. similar as we do with addresses *)

(* is order to collect such preds/values from the model we use a map:    *)
(* (mem_name* [state_term; addr_term]) | (bv_name* [state_term]) -> [2;3;33] *)
(* -- map from pre_terms to list of bitIndecies where this pred is true *)
(* this map is called ptv_map *)
(* later we make the inverse map [2;3;33] -> ref [pre_term_1; ...;pre_term]*)
(* this map is called vpt_map *)
(*----------------------------------*)
(* evrything is based on positive definitions (could be later extended to negative/both)*)

type pre_term = (symbol * (term list))

module PTKey =
struct
	type t = pre_term
	(*rewrite compare with == later*)
	let compare = compare
end

module PTMap = Map.Make(PTKey)

type ptv_map = ((int list) ref) PTMap.t

let get_pre_term_pos_bit_ind symb flat_subst =
	if (Symbol.is_a_memory_pred_symb symb)
	then
		(
			match flat_subst with
			|[(_, state); (_, addr); (_, bit_ind)] ->
					(match (get_ind_from_bit_ind_term bit_ind) with
						| Def(i) -> Def (((symb,[state; addr]), i))
						| Undef -> Undef
					)
			| _ -> Undef
		)
	else
	if (Symbol.is_a_bitvec_pred_symb symb)
	then
		match flat_subst with
		|[(_, state); (_, bit_ind)] ->
				(match (get_ind_from_bit_ind_term bit_ind) with
					| Def (i) -> Def (((symb,[state]), i))
					| Undef -> Undef
				)
		| _ -> Undef
	else
		Undef

(* returns ptv_map *)
let fill_ptv_map model =
	let f_model symb model_node model_ptv_map =
		if ((Symbol.is_a_memory_pred_symb symb) || (Symbol.is_a_bitvec_pred_symb symb))
		then
			begin
				let pos_lit_def = model_node.pos_lit_def in
				if (pos_lit_def.model_lit_undef)
				then
					(
						(* false for all values *)
						let pre_term = (symb,[]) in
						PTMap.add pre_term (ref []) model_ptv_map
					)
				else
					begin
						let pos_lit_def_body = pos_lit_def.model_lit_def_body in
						
						(* add when all $false *)
						let f_pos_def subst_constr
								(_dsim_constr_set_ref, _clause_list_ref) node_ptv_map =
							(match (get_pre_term_pos_bit_ind symb subst_constr.flat_subst) with
								| Def((pre_term, bit_ind)) ->
										(try
											let val_ref = PTMap.find pre_term node_ptv_map in
											val_ref:= bit_ind::!val_ref;
											node_ptv_map
										with
											Not_found ->
												PTMap.add pre_term (ref [bit_ind]) node_ptv_map
										)
								| Undef -> node_ptv_map
							)
						in
						FSVMap.fold f_pos_def pos_lit_def_body model_ptv_map
					end
			end
		else
			model_ptv_map
	in
	let vals_ptmap = NModel.fold f_model model PTMap.empty in
	let sort_vals pt val_ref =
		val_ref:= List.sort compare !val_ref
	in
	PTMap.iter sort_vals vals_ptmap;
	vals_ptmap

type vpt_map = ((pre_term list) ref) LMap.t

let fill_vpt_map ptv_map =
	let f pt v_ref vpt_map =
		try
			let pt_list_ref = LMap.find (!v_ref) vpt_map in
			pt_list_ref := pt::!pt_list_ref;
			vpt_map
		with
			Not_found ->
				LMap.add (!v_ref) (ref [pt]) vpt_map
	in
	PTMap.fold f ptv_map LMap.empty

let pre_term_to_str (symb, term_list) =
	((Symbol.to_string symb)^":"
		^(list_to_string Term.to_string term_list ":"))

let pre_term_list_to_str pt_list =
	(list_to_string pre_term_to_str pt_list "\n")

let out_vpt_map vpt_map =
	let max_val_length = get_max_length_addr_map vpt_map in
	let f v pt_list_ref =
		out_str (pre_term_list_to_str !pt_list_ref);
		out_str "\n";
		let msb_val = norm_addr_pos_val_to_msb max_val_length v in
		out_msb_with_split addr_split_size msb_val;
		out_str "\n";
		out_str (address_pos_val_to_string v);
		out_str "\n---------------------\n";
	in
	LMap.iter f vpt_map

(*--------------------------*)

let out_memory_ver model =
	let (conj_mem_pred_list, conj_bitvec_pred_list) =
		get_conj_ground_mem_bitvec_preds () in
	
	out_str "\n\n---------------------memory verification candidate counterexample----------------\n\n";
	out_str "Negated conjectures:\n";
	out_str (Clause.clause_list_to_string !neg_conjectures_ref);
	(*
	out_str "\n---------------------\n\n";
	(match (get_counter_ex_bound model) with
	| Some(sk_bound_val) ->
	out_str ("Counterexample state: "
	^(term_value_pair_to_string sk_bound_val)
	^"\n");
	| None -> out_str ("\nCounterexample state predicate was not found\n")
	);
	*)
	
	let (conj_state_list, conj_addr_list, conj_bitindex_list) =
		get_from_states_addr_bitindex_sk_lists conj_mem_pred_list conj_bitvec_pred_list
	in
	
	(if (conj_bitvec_pred_list = [])
		then ()
		else
			(out_str "\n---------------------\n";
				out_str "Counterexample bit vector values:\n";
				let f_bitvec bitvec =
					out_str ((ground_pred_value_to_str model bitvec)^"\n") in
				List.iter f_bitvec conj_bitvec_pred_list;
			)
	);
	
	(
		if (conj_mem_pred_list = [])
		then ()
		else
			(
				out_str "\n---------------------\n";
				out_str "Counterexample memory values:\n";
				let f_mem mem_pred =
					out_str ((ground_pred_value_to_str model mem_pred)^"\n")
				in
				List.iter f_mem conj_mem_pred_list;
			)
	);
	
	out_str "\n---------------------\n";
	out_str "Counterexample states: ";
	let f_state state =
		match (constant_val model state) with
		| Some(state_val) ->
				out_str ((term_value_pair_to_string (state, state_val)));
		| None -> failwith ("No value for state skolem constant"^(Term.to_string state)^"is found")
	in
	List.iter f_state conj_state_list;
	(*------------------*)
	let get_all_addresses () =
		let f_addr addr addr_map =
			if (Term.is_addr_const addr)
			then
				let addr_val = address_pos_val model addr in
				add_address_to_map addr_map addr_val addr
			else addr_map
		in
		TermDB.fold f_addr !term_db_ref LMap.empty
	in
	let addr_map = get_all_addresses () in
	let max_addr_length = get_max_length_addr_map addr_map in
	out_str ("\n max addr length: "^(string_of_int max_addr_length));
	List.iter f_state conj_state_list;
	out_str "\n---------------------\n";
	out_str "Counterexample addresses:\n";
	let f_addr addr =
		try
		(* out all addresses equal to a skolem address in a conjecture *)
			let addr_val = (address_pos_val model addr) in
			let addr_list_ref = LMap.find addr_val addr_map in
			out_str (list_to_string Term.to_string !addr_list_ref "\n");
			out_str "\n";
			let msb_val = norm_addr_pos_val_to_msb max_addr_length addr_val in
			out_msb_with_split addr_split_size msb_val;
			out_str "\n";
			out_str (address_pos_val_to_string addr_val);
			out_str "\n---------------------\n";
		(*
		out_str ((Term.to_string addr)^":");
		out_str (address_pos_val_to_string (address_pos_val model addr));
		*)
		with Not_found ->
				failwith "out_memory_ver: all addresses should be in the addr_map"
	in
	List.iter f_addr conj_addr_list;
	out_str "\n---------------------\n";
	out_str "Counterexample bit-indices:\n";
	let f_bitind bitind =
		match (constant_val model bitind) with
		| Some(bitind_val) ->
				out_str ((term_value_pair_to_string (bitind, bitind_val)));
		| None -> failwith ("No value for state skolem constant"^(Term.to_string bitind)^"is found")
	in
	List.iter f_bitind conj_bitindex_list;
	out_str "\n---------------------\n";
	out_str "All addresses:\n";
	
	let f_addr_eq addr_val addr_list_ref =
		out_str (list_to_string Term.to_string !addr_list_ref "\n");
		out_str "\n";
		let msb_val = norm_addr_pos_val_to_msb max_addr_length addr_val in
		out_msb_with_split addr_split_size msb_val;
		out_str "\n";
		out_str (address_pos_val_to_string addr_val);
		out_str "\n---------------------\n";
	in
	LMap.iter f_addr_eq addr_map;
	
	out_str "\n---------------------\n";
	out_str "All bit-vectors/memories:\n";
	out_str "---------------------\n";
	let ptv_map = fill_ptv_map model in
	let vtp_map = fill_vpt_map ptv_map in
	out_vpt_map vtp_map

(*
let f_addr_eq addr_val addr_list_ref =
if (Term.is_addr_const addr)
then
(out_str ((Term.to_string addr)^":");
out_str (address_val_to_string (address_val model addr));
out_str "\n";
)
else ()
in
*)
(*  List.iter f_addr addresses_list*)
(* TermDB.iter f_addr !term_db_ref *)

let out_model model =
	to_stream_model stdout_stream !current_options.sat_out_model model;
	if (!current_options.sat_out_model = Model_Intel)
	then
		out_memory_ver model
	else ()

(*

type dism_constr_set =
| DCSet of FSVSet.t
(* Subsumed means that all dismatching constraints are subsumed     *)
(* by dismatching constr which is either undefined of is a renaming *)
(* (over all vars in the clause)           *)
(* so L(X)| Subsumed means \forall X L(X) (in other notation \forall X (L(X) <-> true) ) *)
| DCSSubsumed

type var_table = (var VarMap.t)

type var_table_ref = var_table ref

(*we pair old clause with the normalised lit list form this clause and constraint list*)
type norm_clause =
(clause * ((lit list) * flat_subst list))
(* literal definition body is a map from subst_constraints into sets of dismatching constrints *)
(* paired with a list of clauses where the L\subst_constraint is selected  *)
(* dismatching constraints are normalised and only varibales in L are left *)
(*  clauses are also normalised such that L is first, vars renamed, including in dismatiching constr.*)

type lit_def_body = (((dism_constr_set ref) * ((norm_clause list) ref)) FSVMap.t)

type lit_def =
{

(* this is a flattened normalised literal of the form (~)P(x_0,..,x_n)                       *)
model_lit : lit;

(* ordered list of vars in the literal                                                       *)
model_lit_vars : var list;

(* a) if lit_def_body is FSVMap.empty then this literal was not defined and this corresponds to          *)
(* \forall X ~L(X)    or \forall X (L(X) <-> $false)                                                     *)
(* b) if [] is a key in  lit_def_body, this corresponds to the empty subst_constr, there are still       *)
(*    can be dismatching constraints corresponding to []                                                 *)
mutable model_lit_def_body : lit_def_body;
}
*)
(* debug *)

(*
let out_model active_clauses =
let f clause =
if not (Clause.get_bool_param Clause.in_active clause)
then ()
else
begin
stdout_stream.stream_add_str "%---------------\n";
Clause.to_stream stdout_stream clause;
stdout_stream.stream_add_char ' ';
Term.to_stream stdout_stream (Clause.get_inst_sel_lit clause);
stdout_stream.stream_add_char '\n';
(try
Dismatching.to_stream_constr_set stdout_stream (Clause.get_dismatching clause);
stdout_stream.stream_add_char '\n';
with
Clause.Dismatching_undef ->
stdout_stream.stream_add_str "[]\n");
stdout_stream.stream_add_str "%----Debug-----------\n";
(*	extend_model model clause; *)
stdout_stream.stream_add_char '\n';
end
in
ClauseAssignDB.iter f active_clauses;
stdout_stream.stream_add_str "\n%---------------End Model--------------\n\n"

*)

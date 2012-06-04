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
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol  

module SymSet = Symbol.SymSet
type sym_set = Symbol.sym_set

type csig = Clause.clause_signature

(*type symbol_db_ref = SymbolDB.symbolDB ref*)
(*type clause_db_ref = ClauseAssignDB.clauseDB ref*)

let symbol_db_ref  = Parser_types.symbol_db_ref
let term_db_ref    = Parser_types.term_db_ref

let get_sym_types sym = Symbol.get_stype_args_val_def sym

module SymbMap = Symbol.Map
let less_map_ref = Parser_types.less_map
let range_map_ref = Parser_types.range_map
let is_ess_less_range symb = 
  (Symbol.is_essential_input symb) 
    &&
  ((SymbMap.mem symb !less_map_ref) || (SymbMap.mem symb !range_map_ref))

let neg_symb       = Symbol.symb_neg
let equality_symb  = Symbol.symb_equality
let typed_equality_symb = Symbol.symb_typed_equality

let v0 = Var.get_first_var ()
let v1 = Var.get_next_var v0
let v2 = Var.get_next_var v1
let v3 = Var.get_next_var v2
let v4 = Var.get_next_var v3

(* creates term from var and adds to term_db*)
let term_var var = TermDB.add_ref (Term.create_var_term var) term_db_ref

let tv0 = term_var v0
let tv1 = term_var v1
let tv2 = term_var v2
let tv3 = term_var v3
let tv4 = term_var v4

let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let equality_term t s = 
  let args = [t;s] in
  add_fun_term equality_symb args 

let typed_equality_term stype_term t s = 
  let args = [stype_term;t;s] in
  add_fun_term typed_equality_symb args 
  
let typed_equality_term_sym eq_type_sym t s = 
  let eq_type = (add_fun_term eq_type_sym []) in
  typed_equality_term eq_type t s


let neg_atom atom = 
  let args = [atom] in
  add_fun_term neg_symb args 
    
let dis_equality t s = 
  neg_atom (equality_term t s)

let dis_typed_equality stype t s = 
  neg_atom (typed_equality_term stype t s)



let assign_eq_ax_param ax = 
  Clause.set_bool_param true Clause.eq_axiom ax ; 
  Clause.set_bool_param true Clause.input_under_eq ax;
(* Clause.assign_axiom_history Clause.Eq_Axiom ax *)
  Clause.assign_tstp_source_axiom_equality ax 
  

let reflexivity_axiom () = 
  let reflex_term = equality_term tv0 tv0 in   
  let refl_ax =  Clause.create [reflex_term] in
  assign_eq_ax_param refl_ax;
  refl_ax 
    
(* axiom x0=x1 & x2 = x1 => x2=x0 is equiv to trans & symmetry *)
let trans_symmetry_axiom () = 
  let x01 = dis_equality  tv0 tv1 in
  let x21 = dis_equality  tv2 tv1 in
  let x20 = equality_term tv2 tv0 in
  let trans_sim_ax =  Clause.create [x01;x21;x20] in
  assign_eq_ax_param trans_sim_ax;
  trans_sim_ax

(*-----typed versions--------*)
(* universal axioms over all types *)
(* we can preinstantiate for types occuring in the problem *)


(*-------reflexifity-------*)
let typed_reflexivity_axiom_var () = 
  let reflex_term = typed_equality_term tv0 tv1 tv1 in   
  let refl_ax =  Clause.create [reflex_term] in
  assign_eq_ax_param refl_ax;
  refl_ax 
  
(* some times it is useful to have instantiatied eq axioms *)
let typed_reflexivity_axiom_type eq_type_sym = 
  let eq_type = (add_fun_term eq_type_sym []) in
  let reflex_term = typed_equality_term eq_type tv1 tv1 in   
  let refl_ax = Clause.create [reflex_term] in
  assign_eq_ax_param refl_ax;
  refl_ax


let typed_reflexivity_axiom_type_set eq_type_set =
  let f eq_type rest = 
    (typed_reflexivity_axiom_type eq_type)::rest
  in
  SymSet.fold f eq_type_set []

(*---------trans_symmetry---------*)

let typed_trans_symmetry_axiom_var () = 
(* tv3 is used for types *)
(*  let type_var_term = tv3 in *)
  let x01 = dis_typed_equality tv3 tv0 tv1 in
  let x21 = dis_typed_equality tv3 tv2 tv1 in
  let x20 = typed_equality_term tv3 tv2 tv0 in
  let trans_sim_ax =  Clause.create [x01;x21;x20] in
  assign_eq_ax_param trans_sim_ax;
  trans_sim_ax


let typed_trans_symmetry_axiom_type eq_type_sym = 
  let eq_type = (add_fun_term eq_type_sym []) in
(* tv3 is used for types *)
(*  let type_var_term = tv3 in *)
  let x01 = dis_typed_equality eq_type tv0 tv1 in
  let x21 = dis_typed_equality eq_type  tv2 tv1 in
  let x20 = typed_equality_term eq_type tv2 tv0 in
  let trans_sim_ax =  Clause.create [x01;x21;x20] in
  assign_eq_ax_param trans_sim_ax;
  trans_sim_ax


let typed_trans_symmetry_axiom_type_set eq_type_set =
  let f eq_type rest = 
    (typed_trans_symmetry_axiom_type eq_type)::rest
  in
  SymSet.fold f eq_type_set []


(*-------symmetry----------*)
(* used in finite_models *)
let typed_symmetry_axiom_sym eq_type_sym = 
  let eq_type = (add_fun_term eq_type_sym []) in
  let neg_eq_x0_x1 = dis_typed_equality eq_type tv0 tv1 in
  let eq_x1_x0 = typed_equality_term eq_type tv1 tv0 in
  let sym_ax = Clause.create [neg_eq_x0_x1; eq_x1_x0] in 
  assign_eq_ax_param sym_ax;
  sym_ax


(*--------------typed version--------------*)
(* congruence axioms: given a hash table of types *)
(*(types with which sorted_euqality occurs)       *)
(* and a function f(x_1,..,x_n) we add congrunce axiom w.r.t. to the types table *)


module SymbTbl = Hashtbl.Make (Symbol)
  


let typed_congruence_axiom eq_type_set symb = 
  match (Symbol.get_stype_args_val symb) with 
  |Def (type_args, type_value) -> 
      if type_args = [] 
      then 
	(None)
      else
	let rec get_args_dis_lits 
	    current_var current_type_args args1 args2 dis_eq_lits = 
	  (match current_type_args with 
	  |h::tl ->
	 (*     out_str ("h: "^(Symbol.to_string h)^"\n");*)
	      if (SymSet.mem h eq_type_set) 
	      then 
		begin
(* different varaibles *)
		let next_var              = (Var.get_next_var current_var) in
		let current_var_term      = (term_var current_var) in
		let next_var_term         = (term_var next_var) in
		let new_current_var       = (Var.get_next_var next_var) in 
  		get_args_dis_lits 
		  new_current_var 
		  tl
		  (current_var_term::args1) 
	      	  (next_var_term::args2) 
		  ((dis_typed_equality 
		      (add_fun_term h [])
		      current_var_term  
		      next_var_term)::dis_eq_lits)
		end
	      else
(* same varaibles *)
		begin
		let current_var_term = term_var current_var in
		let new_current_var  = Var.get_next_var current_var in
		get_args_dis_lits 
		  new_current_var 
		  tl
		  (current_var_term::args1) 
	      	  (current_var_term::args2)
		  dis_eq_lits
		end
	  |[] -> 
	      ((List.rev args1),(List.rev args2), (List.rev dis_eq_lits))
	  )
	in 
	let (args1,args2,dis_eq_lits) = 
	  get_args_dis_lits 
	    v0 type_args [] [] [] in
	if (dis_eq_lits = [])
	then
	  (None)
	else
	  if (Symbol.is_pred symb) 
	  then
            let pred     = add_fun_term symb args1 in 
	    let neg_pred = neg_atom (add_fun_term symb args2) in 
	    let pred_congr_ax = 
	      Clause.normalise term_db_ref 
		(Clause.create (pred::neg_pred::dis_eq_lits))
	    in
	    assign_eq_ax_param pred_congr_ax;
	    Some(pred_congr_ax)
 	  else
	    (let pos_part = 
	      let t = add_fun_term symb args1 in
	      let s = add_fun_term symb args2 in
	      typed_equality_term (add_fun_term type_value []) t s 
	    in
	    let fun_congr_ax = 
	      Clause.normalise term_db_ref 
		(Clause.create (pos_part::dis_eq_lits)) in
	    assign_eq_ax_param fun_congr_ax;
	    Some(fun_congr_ax)
	    )	      
  |Undef -> 
      (None)



(* typed_congr_axiom_list_sym_set *)
(* generic function for getting congruence based on csig.eq_type_set             *)
(* internaly the function uses a closure of eq_type_set *)
(* under function application    *)
(*(e.g. a in eq_type_set then val_type of f(..,a,..) is also in eq_type_set *)

(* it also closes signature under function application ! *)
let typed_congr_axiom_list csig = 
(* we close eq_type_set first *)
(*  let closed_eq_type_set = ref csig.Clause.sig_eq_types in*)
  let rec f symb = 
    if (SymSet.mem symb csig.Clause.sig_eq_types) 
    then ()
    else 
      begin
	let (arg_types, val_type) = get_sym_types symb in
	List.iter f arg_types;
	let arg_is_in_closed_eq_type_set =
	  (List.exists 
	     (fun arg_sym ->  (SymSet.mem arg_sym csig.Clause.sig_eq_types))
	     arg_types
	  )
	in
	if (arg_is_in_closed_eq_type_set)&& (not (val_type == Symbol.symb_bool_type))
	then
	 (csig.Clause.sig_eq_types <- SymSet.add val_type csig.Clause.sig_eq_types
	 )
       else ()
      end
  in
  SymSet.iter f csig.Clause.sig_fun_preds;  

(*  let uf_eq_types = UF_ST.create 301 in *)
 
  let f symb rest = 
    match (typed_congruence_axiom csig.Clause.sig_eq_types symb) with 
    |Some ax -> 
	(* out_str ("ax: "^(Clause.to_string ax)^"\n --------------\n");*)
	ax::rest
    |None -> rest
  in
  SymSet.fold f csig.Clause.sig_fun_preds []


let typed_eq_axioms_sig csig =
  let typed_cong_ax_list = typed_congr_axiom_list csig in 
  if (SymSet.is_empty csig.Clause.sig_eq_types) 
  then 
    []           
  else
    ( 
      let typed_reflexivity_ax = 
	typed_reflexivity_axiom_type_set csig.Clause.sig_eq_types in

      let typed_trans_symmetry_ax = 
	typed_trans_symmetry_axiom_type_set csig.Clause.sig_eq_types in

   let eq_axioms = 
     ((typed_reflexivity_ax)@((typed_trans_symmetry_ax)@typed_cong_ax_list)) in 
   eq_axioms
     )



(*module UF_ST = Union_find.Make(Symbol)*)


(* it should be closed under funct application later *)
(* returns (sym_set, eq_types_set) *)


let get_symb_and_type_eq_set_basic clause_list = 
  let csig = Clause.clause_list_signature  clause_list in 
  csig

let eq_axiom_list clause_list = 
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  let csig = get_symb_and_type_eq_set_basic clause_list in
  typed_eq_axioms_sig csig

(*--------------------------------------------*)
let distinct_ax_list () = 
  let default_type_term = (add_fun_term Symbol.symb_default_type []) in
  if (Symbol.is_essential_input Symbol.symb_typed_equality) 
  then
    (
     let dist_axioms_one_term term term_list = 
       let f rest cterm  = 
	 let dis_eq_term =  (dis_typed_equality default_type_term term cterm) in 
	 let dis_ax = Clause.create [dis_eq_term] in
          (* Clause.assign_axiom_history Clause.Distinct_Axiom dis_ax; *)
	  Clause.assign_tstp_source_axiom_distinct dis_ax;
	 dis_ax::rest 
       in
       List.fold_left f [] term_list 
     in
     let rec distinct_axioms_from_one_dist' rest_axs cur_term dist_terms_rest =
       let new_axs =  (dist_axioms_one_term cur_term dist_terms_rest)@rest_axs in
       match dist_terms_rest with 
       |h::tl -> distinct_axioms_from_one_dist' new_axs h tl
       |[] -> new_axs
     in
     let distinct_axioms_from_one_dist rest_axs dist_term_list =
       match dist_term_list with 
       |h::tl -> distinct_axioms_from_one_dist' rest_axs  h tl 
       |[] -> rest_axs
     in
     List.fold_left distinct_axioms_from_one_dist [] !Parser_types.distinct
    )
   else
     []


(*------------ less range axioms -------------------------------*)
(* we do not need congruence axioms for less_i and range_i_j    *)


let bit_index_str i  = 
  "$$bitIndex"^(string_of_int i)

let stype_bit_index = (Symbol.create_stype [] Symbol.symb_ver_bit_index_type)

let bit_index_type_term () = 
 add_fun_term Symbol.symb_ver_bit_index_type []

let bit_index_symb i =   
  let symb = 
    (Symbol.create_from_str_type (bit_index_str i) stype_bit_index)
  in
  SymbolDB.add_ref symb symbol_db_ref 
 
let bit_index_term i = 
  add_fun_term (bit_index_symb i) []
 
let bit_index_atom symb i = 
  add_fun_term symb [(bit_index_term i)]


let get_max_bit_index () = 
  let f_less symb i curr_max = 
    if ((curr_max < i) && (Symbol.is_essential_input symb))
    then 
      ((*out_str ("Symbol "^(Symbol.to_string symb)^" "^(string_of_int i)^"\n"); *)
       i)
    else
      curr_max
  in
(* less does not include the ind_bound: +1 *)
  let max_less = (SymbMap.fold f_less !less_map_ref 0) - 1 in
 (* out_str ("\n max_less: "^(string_of_int max_less)^"\n");*)
(* we assume bit-vector notation: biggest first (71,0) *)
  let f_range symb (i,j) curr_max = 
    if ((curr_max < i) && (Symbol.is_essential_input symb))
    then
      i
    else
       curr_max
  in
  let max_less_range = SymbMap.fold f_range !range_map_ref max_less in
 (* out_str ("\n max_less_range: "^(string_of_int max_less_range)^"\n");*)
  max_less_range

  
let always_true_ax symb = 
  Clause.create [(add_fun_term symb [tv0])]

let always_false_ax symb = 
  Clause.create [(neg_atom (add_fun_term symb [tv0]))]


(*----------------*)
let less_pos_axs symb max_pos_ind =
  let f rest i = 
    (Clause.create [(bit_index_atom symb i)])::rest in 
  fold_down_interval f 0 (max_pos_ind-1) []

let less_neg_axs symb max_pos_ind max_ind =
  let f rest i = 
    (Clause.create 
       [(neg_atom (bit_index_atom symb i))])::rest in 
  fold_down_interval f max_pos_ind max_ind []


let less_eq_ax symb max_pos_ind =
  let f rest i = 
    (typed_equality_term (bit_index_type_term ()) (bit_index_term i) tv0)::rest in  
  let eq_terms = fold_down_interval f 0 (max_pos_ind-1) [] in
  let neg_less_term = neg_atom (add_fun_term symb [tv0]) in 
  Clause.create (neg_less_term::eq_terms)


(*-------------*)


let range_pos_axs symb min_int_ind max_int_ind = 
  let f rest i = 
    (Clause.create [(bit_index_atom symb i)])::rest in 
  fold_down_interval f min_int_ind max_int_ind []

let range_neg_axs symb min_int_ind max_int_ind max_ind =
  let f rest i = 
    (Clause.create [(neg_atom (bit_index_atom symb i))])::rest in 
 let left = fold_down_interval f 0 (min_int_ind-1) [] in 
 let right = fold_down_interval f (max_int_ind +1) max_ind [] in 
 left@right

let range_eq_ax symb min_int_ind max_int_ind =
  let f rest i = 
  (typed_equality_term (bit_index_type_term ()) (bit_index_term i) tv0)::rest in  
  let eq_terms = fold_down_interval f min_int_ind max_int_ind [] in
  let neg_range_term = neg_atom (add_fun_term symb [tv0]) in 
  Clause.create (neg_range_term::eq_terms)


(*let range_axiom_via_less range_symb *)
(* less axioms should be added after the range axioms since mode less symbols can be added *)

(*
let range_axiom_via_less range_symb 
*)

let less_axioms' max_ind = 
  let f symb i rest = 
(* consider to uncomment later *) 
 (*  if (i = 0)
    then 
      (always_false_ax symb)::rest 
    else 
      if (i = max_ind +1)
      then 
	(always_true_ax symb)::rest
      else
*)
    if (Symbol.is_essential_input symb)
    then
	(
	 let symb_axs = 
	   (less_eq_ax symb i)::((less_pos_axs symb i) 
            @(less_neg_axs symb i max_ind)) in	 
	 symb_axs@rest
	)
    else 
      rest
  in
  SymbMap.fold f !less_map_ref [] 


let less_axioms () = 
  let max_ind = get_max_bit_index () in 
  let less_axioms =  less_axioms' max_ind in 
  (* Clause.assign_axiom_history_cl_list Clause.Less_Axiom less_axioms; *)
  List.iter Clause.assign_tstp_source_axiom_less less_axioms;
  less_axioms

let range_axioms' max_ind = 
  let f symb (max_int_ind, min_int_ind) rest = 
(* if uncommented then incorrect sat result on  *)
(*Examples/attachments_2011_06_09_from_FMCAD2010_built_in_less_range/bpbimodalm_B2ConcreateClk_no_range_ax.cnf*)
(*
    if (min_int_ind =0 && max_int_ind = max_ind)
    then 
      (always_true_ax symb)::rest 
    else
*)
    if (Symbol.is_essential_input symb)
    then
      (
       ((range_eq_ax symb min_int_ind max_int_ind)::
	((range_pos_axs symb min_int_ind max_int_ind)
	 (*@(range_neg_axs symb min_int_ind max_int_ind max_ind)*)))@rest
      )
    else 
      rest
  in
  SymbMap.fold f !range_map_ref [] 

let range_axioms () = 
  let max_ind = get_max_bit_index () in 
  let range_axioms = range_axioms' max_ind in 
  (* Clause.assign_axiom_history_cl_list Clause.Less_Axiom range_axioms; *)
  List.iter Clause.assign_tstp_source_axiom_range range_axioms;
  range_axioms


let less_range_axioms () =
(*  out_str "\n\n out less map\n\n";
  SymbMap.iter (fun symb _-> out_str (Symbol.to_string symb)) !less_map_ref;
  out_str "\n\n end out less map\n\n";
*)
  let max_ind = get_max_bit_index () in 

(*    out_str 
      (Clause.clause_list_to_tptp (less_axioms' max_ind)); *)

  let less_range_axioms = 
    (less_axioms' max_ind) @ (range_axioms' max_ind) 
  in

  List.iter Clause.assign_tstp_source_axiom_range less_range_axioms;

  less_range_axioms

  
(*--------------- Brand's transformation -------------------*)   
(*--------------- Flattening -> no congrunce axioms --------*)

(* move *)
module TermHashKey = 
  struct
    type t    = term
    let equal = (==)
    let hash  = Term.get_fast_key
  end 

(* will have several uses*)
module TermHash = Hashtbl.Make(TermHashKey)


(* move *)
let rec get_max_var_term current_max_var_ref term =  
  match term with 
  |Term.Fun (_, args,_) ->  
      Term.arg_iter (get_max_var_term current_max_var_ref) args
  |Term.Var (v,_) -> 
      if (Var.compare v !current_max_var_ref) > 0
      then 
	(current_max_var_ref := v)
      else ()
	  
let get_max_var clause = 
  let var_ref  = ref (Var.get_first_var ()) in
  Clause.iter (get_max_var_term var_ref) clause;
  !var_ref

(*---------Basic flattening------------------------*)
(* Flattening of a clause is done in two stages:                      *)
(* First, we build a hash table (var_env) mapping non-var term into vars. *)
(* Second, we use var_env  to build flat terms.            *)
(* In "term_flattening_env var_env max_var_ref term"       *)   
(* max_var is max var used                                 *)
(* the input term itself also added to the the var_env     *)
(* if a function term t statisfies add_term_to_def_test    *)
(* we do not need to go                                    *)
(* to subterms  but add 1. a definition t->x into env and  *) 
(* 2. a definition into term_def_table (def. of all subterms of t are also added) *)
(* and later add  \neg R_t(x) to the clause *)

let rec term_flattening_env var_env max_var_ref term = 
  match term with 
  | Term.Var _ -> ()
  | Term.Fun (symb, args, _) -> 
      if (TermHash.mem var_env term) 
      then ()
      else 
	(
	 (
	  (*
	  if (Symbol.is_fun symb) 
	     && (add_term_to_def_test term)
	 then 
	   ((*out_str ("Adding to add_term_def_table term: "
		     ^(Term.to_string term)^"\n");*)
	    add_term_def_table term)
	 else
	   *)
	    (Term.arg_iter (term_flattening_env var_env max_var_ref) args)
	 );
	(* if (Symbol.is_fun symb)  
	 then
*)
	   (
	    max_var_ref:= Var.get_next_var !max_var_ref;
	   let max_var_term = 
	     TermDB.add_ref (Term.create_var_term !max_var_ref) term_db_ref in
	   TermHash.add var_env term max_var_term
	   )
(*	 else ()*)
	)


let flat_term_to_var var_env (*max_var_ref*) t = 
  if (Term.is_var t) 
  then t
  else 
    (
     try 
  (*     term_flattening_env var_env max_var_ref t;*)
       TermHash.find var_env t
     with Not_found -> failwith "flat_term_to_var: Not_found"
    )

let flat_top var_env max_var_ref term = 
   match term with 
  | Term.Fun (symb, args, _) ->       
      Term.arg_iter (term_flattening_env var_env max_var_ref) args;
      let new_args = 
	Term.arg_map (fun t -> flat_term_to_var var_env t) args in 
      TermDB.add_ref (Term.create_fun_term_args  symb new_args) term_db_ref
  | Term.Var _ -> term



let flat_lit_env var_env max_var_ref  lit = 
  let f atom = 
    match atom with 
    | Term.Fun (symb, args, _) -> 
	if (symb == Symbol.symb_typed_equality) 
	then 	
	  match (Term.arg_to_list args) with 
	  | [eq_type;t1;t2] -> 
	      let new_t1 = flat_top var_env max_var_ref t1 in 
	      let new_t2 = flat_top var_env max_var_ref t2 in 
	      typed_equality_term eq_type new_t1 new_t2
	  |_-> failwith "flat_lit_env 1"	      
		
	else
	  flat_top var_env max_var_ref atom
    | Term.Var _ -> failwith "flat_lit_env 2"	
  in 
  TermDB.add_ref (Term.apply_to_atom f lit) term_db_ref
    

(*---------------------------------*)
let flat_clause clause = 
  let var_env = TermHash.create 19 in
  let max_var_ref = ref (get_max_var clause) in
(*  let neg_var_subst_ref = ref (Subst.create ()) in*)
  let lit_list = Clause.get_literals clause in 
  let flat_lits_without_neg_def = 
    List.map (flat_lit_env var_env max_var_ref) lit_list in 
  let default_type_term = (add_fun_term Symbol.symb_default_type []) in
  let dis_eq_term t s =  (dis_typed_equality default_type_term t s) in 
  let f t x rest = 
    (dis_eq_term (flat_top var_env max_var_ref t) x)::rest in 
  let neg_def = TermHash.fold f var_env [] in
  Clause.create (Clause.normalise_lit_list term_db_ref (neg_def@flat_lits_without_neg_def))  
  

let eq_axioms_flatting clause_list = 
 if (Symbol.is_essential_input Symbol.symb_typed_equality) 
  then
    (
 
     let flat_clauses = List.map flat_clause clause_list in
     let eq_ax = [(typed_reflexivity_axiom_var ());(typed_trans_symmetry_axiom_var ())] in 
     eq_ax@flat_clauses
    )
 else
   clause_list

(*----------------Commented Below---------------------*)

(*
(*---------------------*)
(* returns ([v_1;..;v_n],[v'_1;...;v'_n]) to be used in congruence axioms*)
let rec get_two_vlists current_var n = 
  if n = 0 then ([],[])
  else
    let next_var        = Var.get_next_var current_var in
    let new_current_var = Var.get_next_var next_var in 
    let (rest1,rest2)   = get_two_vlists new_current_var (n-1) in
    ((term_var current_var)::rest1,(term_var next_var)::rest2)

exception Arity_non_positive
let congr_axiom symb = 
  let arity = Symbol.get_arity symb in 
  if arity <= 0 then raise  Arity_non_positive
  else 
    (let (vlist1,vlist2) = get_two_vlists v0 arity in
    let var_dis_part = 
      List.rev_map2 dis_equality vlist1 vlist2  
    in
    match (Symbol.get_type symb)
    with
    |Symbol.Fun ->
	let pos_part = 
	  let t = add_fun_term symb vlist1 in
	  let s = add_fun_term symb vlist2 in
	  equality_term t s 
	in
	let fun_congr_ax = 
	  Clause.normalise term_db_ref 
	  (Clause.create (pos_part::var_dis_part)) in
	  assign_eq_ax_param fun_congr_ax;
	fun_congr_ax
    |Symbol.Pred ->
	let pred     = add_fun_term symb vlist1 in 
	let neg_pred = neg_atom (add_fun_term symb vlist2) in 
	let pred_congr_ax = 
	  Clause.normalise term_db_ref 
	  (Clause.create (pred::neg_pred::var_dis_part))
	in
	assign_eq_ax_param pred_congr_ax;
	pred_congr_ax
    |_-> failwith "eq_axioms: no congr_axiom for this type of symb "
    )



let congr_axiom_list () = 
  let f symb rest = 
    if ((Symbol.is_input symb) & (not (symb == Symbol.symb_equality)))
    then
      match (Symbol.get_type symb) with 
      |Symbol.Fun|Symbol.Pred ->
	  if (Symbol.get_arity symb)>0
	  then 
	    (congr_axiom symb)::rest
	  else rest
      |_-> rest
    else rest
  in
  SymbolDB.fold f !symbol_db_ref []
    
let axiom_list () = 
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  if (Symbol.is_input equality_symb) 
  then
    let cong_ax_list = congr_axiom_list () in
    (reflexivity_axiom ())::(trans_symmetry_axiom ())::cong_ax_list
  else []

*)
(*
  let sym_set      = ref SymSet.empty in
  let eq_type_set  = ref SymSet.empty in
  let rec get_type_eq_set_form_term t = 
    match t with
    | Term.Fun(symb,args,_) -> 	
	let relevant_args = 
	  if (symb == Symbol.symb_typed_equality) 
	  then 
	    (
	    let (eq_type, t1,t2) = 
	      get_triple_from_list (Term.arg_to_list args) in
	    let eq_type_sym = Term.get_top_symb eq_type in
	    eq_type_set:= SymSet.add eq_type_sym !eq_type_set;
	    Term.list_to_arg [t1;t2]
	    )
	  else
	    (sym_set :=  SymSet.add symb !sym_set;	     
	     args
	    )
	in
	Term.arg_iter get_type_eq_set_form_term relevant_args
    |Term.Var _ -> ()
  in 
  let get_type_eq_set_form_lit lit = 
    get_type_eq_set_form_term (Term.get_atom lit)
  in
  let get_type_eq_set_form_cl cl = Clause.iter  get_type_eq_set_form_lit cl in 
  List.iter get_type_eq_set_form_cl clause_list;
  (!sym_set,!eq_type_set)
*)


(*

let get_type_eq_term t = 
  match t with
  | Term.Fun(symb,args,_) -> 
      if (symb == Symbol.symb_typed_equality)
      then
	(
	 match (Term.arg_to_list args) with 
	|stype_term::_ -> 
	    (match stype_term with
	    |Term.Fun(stype_symb,args,_) -> Some stype_symb
	    |_ -> failwith 
	       ("get_type_eq_term shouldn't happen" ^ Term.to_string t) 
	    )
	|_-> failwith 
	   ("get_type_eq_term shouldn't happen\n" ^ Term.to_string t) 
	)
      else 
	None
  |_-> None
*)

(*
  let typed_congr_axiom_list () = 
    let eq_type_table = SymbTbl.create 101 in
  


    
  let collect_essential_stypes = function

    (* Symbol is a theory symbol (not a type symbol) that occurs in an
       input term *)
    | symb when 
	(Symbol.is_essential_input symb) &&
	  not (symb == Symbol.symb_typed_equality) -> 

	(

	  (* Get type of arguments and type of result of symbol *)
	  match Symbol.get_stype_args_val symb with 
	      
	    (* Type of arguments and result determined *)
	    | Def (a, v) -> 
		
		(* Add all types to table of types except bool type $o *)
		List.iter
		  (function 
		       
		     (* Do not generate axioms for bool type $o *)
		     | s when (s == Symbol.symb_bool_type) -> ()
	
		     (* Generate axioms for all other types *)
		     | s -> 
			 
			 (* Symbol not in table? *)
			 if not (SymbTbl.mem eq_type_table s) then 
			   
			   (* Add symbol to table of types *)
			   SymbTbl.add eq_type_table s s 

		  )
		  (v :: a)
		  
	    (* Skip if type is not known *)
	    | Undef -> ()

	)

	  
    (* Symbol is declared only, but does not occur *)
    | _ -> ()
	
  in
    
    (* Iterate symbol table to find types to generate axioms for *)
    SymbolDB.iter collect_essential_stypes !symbol_db_ref;
      

    out_str ("Types to generate congruence axioms for:\n");
    SymbTbl.iter
      (fun s _ -> out_str (Symbol.to_string s))
      eq_type_table;
*)
  
(* It is not enough to consider the types in equations only, must 
   take the types of all symbols in the input as above *)
(*
(* for $equality_sorted(type, t,s) add type to symb_table *)
  let add_eq_type t = 

    match (get_type_eq_term t) with 
    |Some symb -> 	
	if (Symbol.is_essential_input symb)
	then 
	  (SymbTbl.add eq_type_table symb symb)
	else ()	  
    |None -> ()
  in	 
  TermDB.iter add_eq_type !term_db_ref;    



  let f symb rest = 
    out_str ("eq_ax: "
	     ^(Symbol.to_string symb)
	     ^" is_essential_input: "
	     ^(string_of_bool (Symbol.is_essential_input symb))
	     ^" Symbol.is_signature_symb: "
	     ^(string_of_bool (Symbol.is_signature_symb symb))^"\n");
    if 
      (
       (Symbol.is_essential_input symb) 
	 && 
       (not (symb == Symbol.symb_typed_equality)) 
	 && 
       (Symbol.is_signature_symb symb)
(*	 &&
(* We don't need congruence axioms for less and range symbols !*)
(* but slower that with the axioms... *)
       (not (is_less_range symb))*)
      )
    then
      (
       match (typed_congruence_axiom eq_type_table symb) with 
       |Some ax -> 
	   out_str ("ax: "^(Clause.to_string ax)^"\n --------------\n");
	   ax::rest
       |None -> rest
      )	
    else rest
  in
  SymbolDB.fold f !symbol_db_ref []
   
(*
  out_str "\n----------------get_type_eq_term-------\n";
      out_str ((Symbol.to_string symb)^"\n");  
*)

*)


(*
let axiom_list () = 
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  if (Symbol.is_essential_input Symbol.symb_typed_equality) 
  then
    (
     let typed_cong_ax_list = typed_congr_axiom_list () in
     (typed_reflexivity_axiom ())::(typed_trans_symmetry_axiom ())::typed_cong_ax_list) 
  else []
*)

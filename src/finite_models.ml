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

let get_sym_types sym = Symbol.get_stype_args_val_def sym

module TermHash = Term.Hashtbl
module TermMap = Term.Map

(* The flattening transformation is based on                          *)
(* Computing Finite Models by Reduction to Function-free clause logic *)
(* by Baumgartner, Fuchs, de Nivelle, Tinelli *)
(* which are extensions of ideas from Paradox *)
(* after flattening each clause is of the form *)
(* ~P_f(y,x)\/~P(x)\/Q(x)\/ x=z *)
(* 1. all P_f are neg., 2. no x \not = y *)

(*-----------Add terms, clauses--------------*)

(* change later !!!*)
(*
  let equality_term t s =
  let default_type_term = (add_fun_term Symbol.symb_default_type []) in
  let args = [default_type_term; t; s] in
  add_fun_term Symbol.symb_typed_equality args
 *)

let create_symbol symb_name stype sproperty =
  let symb =
    Symbol.create_from_str_type_property
      symb_name stype Symbol.Flat in
  let added_symb = SymbolDB.add_ref symb symbol_db_ref in
  Symbol.assign_is_essential_input true added_symb;
  Symbol.assign_is_input true added_symb;
  Symbol.incr_num_input_occur added_symb;
  added_symb

(*
  let equality_term eq_type t s =
  let args = [eq_type; t; s] in
  add_fun_term Symbol.symb_typed_equality args

  let add_typed_equality_sym eq_type_sym t s =
  let eq_type = (add_fun_term eq_type_sym []) in
  equality_term eq_type t s

  let add_typed_dis_equality eq_type t s =
  add_fun_term Symbol.symb_neg [(equality_term eq_type t s)]

  let dis_equality_sym eq_type_sym t s =
  add_fun_term Symbol.symb_neg [(add_typed_equality_sym eq_type_sym t s)]

  let add_clause_lits lit_list =
  Clause.normalise term_db_ref (Clause.create lit_list)
 *)

(* aux fun *)
let get_val_type sym = Symbol.get_val_type_def sym

(*----------------*)
module SymSet = Symbol.Set

type cyclic_types =
    {
     cyclic_types : SymSet.t;
     non_cyclic_types : SymSet.t
   }

(*----------------*)

let init_sig = ref (Clause.create_clause_sig ())

let flat_sym_set = ref SymSet.empty
let def_sym_set = ref SymSet.empty
(*let eq_type_set  = ref SymSet.empty*)

let epr_type_set = ref SymSet.empty

let epr_const_set = ref SymSet.empty

let cyc_non_cyc_types = ref { cyclic_types = SymSet.empty; non_cyclic_types = SymSet.empty }

(*-------------------------------------*)

(* can be extended later *)
let epr_type_set_init () =
  let not_epr_type_set = ref SymSet.empty in
  let val_types = ref SymSet.empty in
  not_epr_type_set := SymSet.add Symbol.symb_bool_type !not_epr_type_set;
  let f symb =
    let (arg_types, val_type) = get_sym_types symb in
    val_types := SymSet.add val_type !val_types;
    if not (arg_types = [])
    then
      not_epr_type_set := SymSet.add val_type !not_epr_type_set
    else
      ()
  in
  SymSet.iter f !init_sig.Clause.sig_fun_preds;
  let epr_set = SymSet.diff !val_types !not_epr_type_set in
  Statistics.incr_int_stat (SymSet.cardinal epr_set) Statistics.sat_num_of_epr_types;
  epr_type_set := epr_set

(* should be called after epr_type_set_init () *)
let epr_const_set_init () =
  let f symb =
    let (arg_types, val_type) = get_sym_types symb in
    if
      (arg_types = [])
	&&
      (SymSet.mem val_type !epr_type_set)
    then
      (
       epr_const_set:= SymSet.add symb !epr_const_set
      )
    else ()
  in
  SymSet.iter f !init_sig.Clause.sig_fun_preds

(*-----------------------*)

let not_to_flat_type_test stype =
  (!current_options.sat_epr_types
     &&
   (SymSet.mem stype !epr_type_set)
  )
||
  (!current_options.sat_non_cyclic_types
     &&
   (SymSet.mem stype !cyc_non_cyc_types.non_cyclic_types)
  )

(* we do not faltten terms that do not sat this test*)
let not_to_flat_symb_test symb =
  let vt = get_val_type symb in
  not_to_flat_type_test vt

let not_to_flat_atom_test atom =
  match atom with
  | Term.Var _ -> false
  | Term.Fun (symb, args, _) ->
      (
       if (symb == Symbol.symb_typed_equality)
       then
	 let (eq_type, _t1, _t2) =
	   get_triple_from_list (Term.arg_to_list args) in
	 let eq_type_sym = Term.get_top_symb eq_type in
	 (not_to_flat_type_test eq_type_sym)
       else
	 true
      )
let not_to_flat_lit_test lit =
  not_to_flat_atom_test (Term.get_atom lit)

(*
  let don_not_flat_term_test term =
 *)

(*------------------------------------*)
module SymH = Hashtbl.Make(Symbol)

(* map from flat to original *)
let flat_to_orig = SymH.create 101

let add_flat_to_orig flat orig =
  if (SymH.mem flat_to_orig flat)
  then ()
  else
    SymH.add flat_to_orig flat orig

(*--------------- Flattening Signature ----------------------------*)
(* for each fun. symbol f in signature which also occrs in the input *)
(* we add P_f of arity ar(f) + 1, the first argument of P_f corresponds *)
(* to the value of f *)
(* one should run flat_signature (once) before flattening *)

(* val pred is first arg *)
let get_val_pred_type sym =
  (* assert ((Symbol.is_flat sym) &&
     ( ( (not (Symbol.is_arity_def sym)) || (Symbol.get_arity sym) >0)
     || (Symbol.is_defpred sym)));
   *)
  let arg_types, _bool_type = Symbol.get_stype_args_val_def sym in
  let (val_type, _rest) = split_list arg_types in
  val_type

let flat_signature () =
  let f symb =
    (
     if
       (
	(Symbol.is_fun symb)
	  &&
	(not (not_to_flat_symb_test symb))
       )
     then
       (
	begin
	  let new_symb_name = ("$$iProver_Flat_"^(Symbol.get_name symb)) in
	  let flat_type =
	    match (Symbol.get_stype_args_val symb) with
	    | Def (old_args, old_val) ->
		(*            Symbol.create_stype (old_args@[old_val]) Symbol.symb_bool_type*)
		Symbol.create_stype (old_val:: old_args) Symbol.symb_bool_type
	    | Undef -> Symbol.create_stype [] Symbol.symb_bool_type
	  in
	  let add_flat_symb = create_symbol new_symb_name flat_type Symbol.Flat in
	  flat_sym_set:= SymSet.add add_flat_symb !flat_sym_set;
	  add_flat_to_orig add_flat_symb symb;
	  Symbol.assign_flattening symb add_flat_symb;
	end
       )
     else ()
    )
  in
  SymSet.iter f !init_sig.Clause.sig_fun_preds

(*
  module TermHashKey =
  struct
  type t = term
  let equal = (==)
  let hash = Term.get_fast_key
  end

(* will have several uses*)
  module TermHash = Hashtbl.Make(TermHashKey)
 *)

(*-------Definitions for Ground Terms ------------------------------------*)
(* We introduce defintions for each ground non-variable term              *)
(* this helps to shorten the resulting clauses.                           *)
(* We do not introduce explicitly new constants but use the same term for *)
(* its definition, and introduce R_t as the relation corresponding        *)
(* to this constant                                                       *)
(* term_def_table maps ground terms to symbols which are used to define   *)
(* these terms ex.: for f(g(a))                                           *)
(* the table will contain                                                 *)
(* f(g(a)) -> R_{f(g(a))}; g(a) -> R_{ga}; a -> (Symbol.get_flattening a) *)

let add_term_to_def_test t =
  (Term.is_ground t) && !current_options.sat_gr_def

let term_def_table = TermHash.create 41

(* adds definition of a ground term to the table *)
(* fix typed equality! *)
let rec add_term_def_table t =
  if (TermHash.mem term_def_table t)
  then ()
  else
    match t with
    | Term.Fun (symb, args, _) ->
	if (Term.is_constant t)
	then
	  TermHash.add term_def_table t (Symbol.get_flattening symb)
	else
	  (Term.arg_iter add_term_def_table args;
	   (* replace to a shorter name: based on a counter *)
	   let def_symb_name = ("$$iProver_Def_"^(Term.to_string t)) in
	   let def_symb_type =
	     (Symbol.create_stype [(get_val_type symb)] Symbol.symb_bool_type) in
	   let add_def_symb =
	     create_symbol def_symb_name def_symb_type Symbol.DefPred in
	   def_sym_set:= SymSet.add add_def_symb !def_sym_set;
	   TermHash.add term_def_table t add_def_symb
	  )
    | Term.Var _ -> failwith "add_term_def_table term should be ground"


(* OLD
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

   let b_orig = 0
   let b_fresh = 1 (* bound for making vars fresh *)

   let rec term_flattening_env fresh_vars_env var_env term =
   match term with
   | Term.Var (v, _) -> () (*add_var_term (SubstBound.find_renaming renaming_env (b_orig,v))*)
   | Term.Fun (symb, args, _) ->
   if (TermHash.mem var_env term)
   then ()
   else
   begin
   (if (Symbol.is_fun symb)
   && (add_term_to_def_test term)
   then
   ((* out_str ("Adding to add_term_def_table term: "
       ^(Term.to_string term)^"\n");*)
   add_term_def_table term)
   else
   (
   let relevant_args =
   if (symb == Symbol.symb_typed_equality)
   then
   let (eq_type, t1, t2) =
   get_triple_from_list (Term.arg_to_list args) in
   (* on the way we also fill set of equality types *)
   (* let eq_type_sym = Term.get_top_symb eq_type in
      eq_type_set:= SymSet.add eq_type_sym !eq_type_set;*)
   Term.list_to_arg [t1; t2]
   else
   args
   in
   Term.arg_iter (term_flattening_env fresh_vars_env var_env) relevant_args)
   );
   if (Symbol.is_fun symb)
   && (not (not_to_flat_symb_test symb))
   then
   (
   (* max_var_ref:= Var.get_next_var !max_var_ref; *)
   (*let new_var = SubstBound.get_next_unused_var renaming_env (Symbol.get_val_type_def symb) in*)
   let fresh_var = Var.get_next_fresh_var fresh_vars_env (Symbol.get_val_type_def symb) in
   let fresh_var_term = add_var_term fresh_var in
   TermHash.add var_env term fresh_var_term
   )
   else ()
   end

   let flat_term_to_var fresh_vars_env var_env t =
   if (Term.is_var t)
   then t
   else
   (
   try
   term_flattening_env fresh_vars_env var_env t;
   TermHash.find var_env t
   with Not_found -> failwith "flat_term_to_var: Not_found"
   )

   let order_term_var tv1 tv2 =
   if (Var.compare (Term.get_var tv1) (Term.get_var tv2)) > 0
   then (tv1, tv2)
   else (tv2, tv1)


(* We obtain flat def. of terms in var_env and   *)
(* a normalised subst. corresponding to x \not = y *)
(* subst is kept confluent *)
(* later this substitution will be applied to all variables*)
   let flat_lit_env fresh_vars_env var_env neg_var_subst_ref lit =
   if (not_to_flat_lit_test lit)
   then
   ()
   else
   begin
   if (Term.is_neg_lit lit)
   then
   begin
   let atom = Term.get_atom lit in
   match atom with
   | Term.Fun (symb, args, _) ->
   if (symb == Symbol.symb_typed_equality)
   then
   (* flat neg eq: t\=s 1. t->x s->y added to var_env,   *)
   (* then x\not y is normalised and added to subst.     *)
   
   (*	    let (t1,t2) = get_pair_from_list (Term.arg_to_list args) in*)
   let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
   begin
   (*	    let rec fl t1 t2 = *)
   if t1 == t2 then ()
   else
   let var_t1 = flat_term_to_var fresh_vars_env var_env t1 in
   let var_t2 = flat_term_to_var fresh_vars_env var_env t2 in
   let norm_t1 =
   Subst.find_normalised !neg_var_subst_ref var_t1 in
   let norm_t2 =
   Subst.find_normalised !neg_var_subst_ref var_t2 in
   if norm_t1 == norm_t2
   then ()
   else
   begin
   let (big_t, small_t) = order_term_var norm_t1 norm_t2 in
   neg_var_subst_ref:=
   Subst.add (Term.get_var big_t) small_t !neg_var_subst_ref
   end
   end
   (* atom is not equality *)
   else
   term_flattening_env fresh_vars_env var_env atom
   
   | Term.Var _ -> failwith "flat_lit_env: atom cannot be a var"
   end
   (* positive lit*)
   else
   term_flattening_env fresh_vars_env var_env lit
   end

(*
  let rec get_max_var_term current_max_var_ref term =
  match term with
  | Term.Fun (_, args, _) ->
  Term.arg_iter (get_max_var_term current_max_var_ref) args
  | Term.Var (v, _) ->
  if (Var.compare v !current_max_var_ref) > 0
  then
  (current_max_var_ref := v)
  else ()
 *)

(*
  let get_max_var clause =
  let var_ref = ref (Var.get_first_var ()) in
  Clause.iter (get_max_var_term var_ref) clause;
  !var_ref
 *)

 *)


(*-----------------New flattening with cyclic types but without def yet---------------------------------------*)
(* P(t,..); *)
(* get_flat_term t:*)
(* either a var if top(t) is of a to_flatten type  *)
(* or f(get_flattened term) *)
(* vars are normalised wrt neg_var_subst_ref *)
(* during get_flattend save*)
(* 1) ~P_f(var, (flattened_args args)) for to_flatten type in an flat_env*)
(* 2)  mapping from term into flat_term  so it can be used when the same term is processed later *)
(* t=s then (get_flat_term t)=(get_flat_term s) ) *)
(* t != s then if (get_flat_term t) == (get_flat_term s) remove else (get_flat_term t) == (get_flat_term s) *)

(* if one of them is var then return (v,t) if both are vars compare them in by Var.compare otherwise restun as it is *)
let order_terms t1 t2 =
  if (Term.is_var t2)
  then
    if (Term.is_var t1)
    then
      if (Var.compare (Term.get_var t1) (Term.get_var t2)) > 0
      then (t1, t2) (* both vars*)
      else (t2, t1) (* both vars *)
    else (* t2 var; t1 non var*)
      (t2, t1)
  else (*t2 is non-var, t1 var/non-var *)
    (t1, t2)

(* without (ground) term definitions yet !*)
let flat_clause clause =
  (*	let var_env = TermHash.create 19 in *)
  let term_to_flat_term_env = ref TermMap.empty in
  let clause_lits = Clause.get_literals clause in
  
  let clause_vars = Clause.get_var_list clause in
  let fresh_vars_env = Var.init_fresh_vars_env_away clause_vars in
  
  let neg_var_subst_ref = ref (Subst.create ()) in
  (* lits of the form ~P_f(flat_args) *)
  let fun_def_lits = ref [] in
  
  (*Clause.iter (flat_lit_env fresh_vars_env var_env neg_var_subst_ref) clause;*)
  
  (* add_to_neg_env checks if one of t1 or t2 is a vriable which does not occur in the other *)
  (* then adds this pair to the env and return true otherwise return false*)
  let neg_norm_term t = Subst.apply_subst_term term_db_ref !neg_var_subst_ref t in
  
  let add_to_neg_env t1 t2 =
    (* assume that neither t1 nor t2 are in neg_var_subst_ref due to normalising *)
    let norm_t1 = neg_norm_term t1 in
    let norm_t2 = neg_norm_term t2 in
    if (norm_t1 == norm_t2)
    then
      true (* ignore if they norm terms are equal *)
    else
      let (ot1, ot2) = order_terms norm_t1 norm_t2 in
      if (Term.is_var ot1) && (not (Term.is_subterm ot1 ot2))
      then
	(
	 neg_var_subst_ref := Subst.add (Term.get_var ot1) ot2 !neg_var_subst_ref;
	 true
	)
      else
	false
  in
  (* a fun/var term not lit *)
  let rec get_flat_term term =
    try
      TermMap.find term !term_to_flat_term_env
    with
    | Not_found ->
	begin
	  match term with
	  | Term.Fun (symb, args, _) ->
	      let arg_list = Term.arg_to_list args in
	      let new_args = List.map get_flat_term arg_list in
	      if (not_to_flat_symb_test symb)
	      then
		(
		 let flat_term =	add_fun_term symb new_args in
		 (* add t-> flat_term *)
		 term_to_flat_term_env := TermMap.add term flat_term !term_to_flat_term_env;
		 flat_term
		)
	      else
		(
		 (* create ~P_f(new_args) *)
		 let pred_f_symb = Symbol.get_flattening symb in
		 (*	    out_str ("new symb: "^(Symbol.to_string new_symb)^"\n");*)
		 (* the value of the function is the first argument of the relation*)
		 let fresh_var = Var.get_next_fresh_var fresh_vars_env (Symbol.get_val_type_def symb) in
		 let fresh_var_term = add_var_term fresh_var in
		 let pred_f_args = fresh_var_term:: new_args in
		 let fun_def_lit = add_neg_atom_symb pred_f_symb pred_f_args in
		 (* add ~P_f(flat_args) to list *)
		 fun_def_lits:= fun_def_lit::!fun_def_lits;
		 (* add t -> flat_term == fresh_var *)
		 term_to_flat_term_env := TermMap.add term fresh_var_term !term_to_flat_term_env;
		 fresh_var_term
		)
		  
	  | Term.Var (v, _) -> term
		(* Subst.find_normalised !neg_var_subst_ref term; normalise later after flattening *)
	end
  in
  
  let get_flat_lit rest lit =
    let atom = Term.get_atom lit in
    match atom with
    | Term.Fun (symb, args, _) ->
	if (symb == Symbol.symb_typed_equality)
	then
	  let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
	  let flat_t1 = (get_flat_term t1) in
	  let flat_t2 = (get_flat_term t2) in
	  if (Term.is_neg_lit lit)
	  then
	    if (add_to_neg_env flat_t1 flat_t2)
	    then
	      rest
	    else
	      (add_typed_disequality_term eq_type flat_t1 flat_t2):: rest
	  else (* pos eq *)
	    (add_typed_equality_term eq_type flat_t1 flat_t2):: rest
	else (* non eq pred *)
	  let flat_atom_args = List.map get_flat_term (Term.arg_to_list args) in
	  let new_lit =
	    if (Term.is_neg_lit lit)
	    then
	      add_neg_atom_symb symb flat_atom_args
	    else
	      add_fun_term symb flat_atom_args
	  in
	  new_lit:: rest
    | Term.Var _ -> failwith "flat_lit: atom cannot be var"
  in
  let flat_lits = List.fold_left get_flat_lit [] clause_lits in
  let new_lits = flat_lits@(!fun_def_lits) in
  let new_neg_norm_lits = List.map neg_norm_term new_lits in
  
  let tstp_source = Clause.tstp_source_flattening clause in
  let new_clause = create_clause tstp_source new_neg_norm_lits in
(*
  Format.printf "Flat clause: \n @[%a @]@."
  (TstpProof.pp_clause_with_source_gs ~clausify_proof: false ) new_clause;
 *)
  (*	
    out_str ("     Cl: \n"^(Clause.to_string clause)^"\n");
    out_str ("Flat Cl: \n"^(Clause.to_string new_clause)^"\n");
   *)
  new_clause

(*--------------OLD-------------------*)
(*
  let flat_clause clause =
  let var_env = TermHash.create 19 in
  let clause_vars = Clause.get_var_list clause in
  let fresh_vars_env = Var.init_fresh_vars_env_away clause_vars in
(*let max_var_ref = ref (get_max_var clause) in*)
  let neg_var_subst_ref = ref (Subst.create ()) in
  Clause.iter (flat_lit_env fresh_vars_env var_env neg_var_subst_ref) clause;
(* now we have the map of non-var terms  to corresponding vars in var_env *)
(* get var_term corresponding to the term in var_env *)

  let term_to_var_term term =
  try
  (Subst.find_normalised !neg_var_subst_ref
  (TermHash.find var_env term))
  with Not_found ->
  if (Term.is_var term)
  then Subst.find_normalised !neg_var_subst_ref term
  else
  failwith ("term_to_var_term: Not_found term: "
  ^(Term.to_string term))
  in
(* auxilary function to flatten arguments taking into account epr sorts *)
  let flat_args_fun symb old_arg_list =
  let arg_types, _val_type = get_sym_types symb in
  let (_, rev_new_args) =
  let f (arg_types_rest, new_args_rest) old_arg =
  match arg_types_rest with
  | arg_type:: tl ->
  let new_arg =
  if (to_flat_type_test arg_type)
  then
  (
(*
  out_str ("to flat type "^(Symbol.to_string arg_type)
  ^" term "^(Term.to_string old_arg)^"\n");
 *)
  term_to_var_term old_arg
  )
  else
  old_arg
  in
  (tl, new_arg:: new_args_rest)
  |[] -> failwith "flat_lit rest lit should not happen"

  in
  List.fold_left f (arg_types,[]) old_arg_list
  in
  let new_arg_list = List.rev rev_new_args in
  new_arg_list
  in

(* first we flatten top of predicates and pos. eq. *)
(* (neq eq translates to x\=y and was added to subst.), *)
(* then we add all flattenings of terms in var_env *)
  let flat_lit rest lit =
  if (not (to_flat_lit_test lit))
  then
  lit:: rest
  else
  begin
  let atom = Term.get_atom lit in
  match atom with
  | Term.Fun (symb, args, _) ->
  if (symb == Symbol.symb_typed_equality)
  then
  if (Term.is_neg_lit lit)
  then
(* all neg eq are falttend to x\not y which are added to neg_var_subst_ref *)
(* and will be added to the rest later *)
  rest
  else
(*positive eq, terms replaced by definitions *)
(* let (t1,t2) = get_pair_from_list (Term.arg_to_list args) in*)
(* replace *)
  let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
  (add_typed_equality_term eq_type (term_to_var_term t1) (term_to_var_term t2)):: rest
  else
(* non equlaity literal *)
  let new_atom =
  let old_arg_list = Term.arg_to_list args in
  let new_arg_list = flat_args_fun symb old_arg_list in
  add_fun_term symb new_arg_list
  in
  let new_lit =
  if (Term.is_neg_lit lit)
  then
  add_fun_term Symbol.symb_neg [new_atom]
  else
  new_atom
  in
  new_lit:: rest
  | Term.Var _ -> failwith "flat_lit: atom cannot be var"
  end
  in
  let flat_part = Clause.fold flat_lit [] clause in
  let get_env_part term var_term rest =
  let new_var_term =
  (Subst.find_normalised !neg_var_subst_ref var_term) in
  match term with
  | Term.Fun (symb, args, _) ->
  let new_atom =
  if (add_term_to_def_test term)
  then
  (try
  let new_symb = (TermHash.find term_def_table term) in
  add_fun_term new_symb [new_var_term]
  with Not_found ->
  failwith "get_env_part: ground term shoud be in term_def_table "
  )
  else
  (let new_symb = Symbol.get_flattening symb in
(*	    out_str ("new symb: "^(Symbol.to_string new_symb)^"\n");*)
(* the value of the function is the first argument of the relation*)

  let old_arg_list = Term.arg_to_list args in
  let non_flat_new_arg_list = flat_args_fun symb old_arg_list in

  let new_args = new_var_term:: non_flat_new_arg_list
(*	      new_var_term::(Term.arg_to_list (Term.arg_map term_to_var_term args)) *)
  in
  add_fun_term new_symb new_args
  )
  in
  let new_lit = add_fun_term Symbol.symb_neg [new_atom] in
  new_lit:: rest
  | Term.Var _ -> failwith "get_env_part should not be var term"
  in
  let env_part = TermHash.fold get_env_part var_env [] in
  add_clause_lits (env_part@flat_part)
 *)

(*----------------------------------------------------------------*)
(* Gets definitions from the term_def_table                       *)
(* Ex: we need to get f(t1,..,tn) = c_f(t1,..,tn)                 *)
(* which can be defined as                                        *)
(* \neg P_t1(X1)\/..\/ \neg P_tn(Xn) \/ \neg P_f(t1,...,tn)(Z) \/ *)
(* \/ \neg P_f(Val,X1,..,Xn)\/ Z=Val                              *)
(* constants are not redefined *)

(*----------------definitions are wrong and do not work!---------------------*)
(*--------------------fix later --------------------*)
(*let _ = out_str ("\n\n!Fix Definitions in finite_models!\n\n")*)

(*this should work for non-gound definitions but for ground should add a be better translation *)
let get_definitions () =
  let f t def_symb rest =
    match t with
    | Term.Fun (symb, args, _) ->
	if (Term.is_constant t)
	then
	  (* no def. for constants needed *)
	  rest
	else
	  (
	   (*  [\neg P_t1(X1);.. \neg P_tn(Xn)] *)
	   (* let current_var = ref (Var.get_first_var ()) in *)
	   let var_env = Var.init_fresh_vars_env () in
	   let arg_vars = ref [] in
	   let f arg_lits_rest arg_term =
	     try
	       let new_symb = TermHash.find term_def_table arg_term in
	       let new_var_term = add_var_term (Var.get_next_fresh_var var_env (Term.get_term_type arg_term)) in
	       arg_vars:= new_var_term::!arg_vars;
	       let new_lit = add_neg_atom_symb new_symb [new_var_term] in
	       new_lit:: arg_lits_rest
	     with
	       Not_found ->
		 failwith "get_definitions: term should be in term_def_table "
	   in
	   let arg_lits = Term.arg_fold_left f [] args in
	   arg_vars := List.rev !arg_vars;
	   
	   (* \neg P_f(t1,...,tn)(Z) *)
	   let val_type = Symbol.get_val_type_def symb in
	   let current_var = Var.get_next_fresh_var var_env val_type in
	   let p_f_t_lit_var = add_var_term current_var in
	   let p_f_t_lit = add_neg_atom_symb def_symb [p_f_t_lit_var] in
	   
	   (*\neg P_f(Val,X1,..,Xn) *)
	   let current_var = Var.get_next_fresh_var var_env val_type in
	   let val_var = add_var_term current_var in
	   let p_f_symb = Symbol.get_flattening symb in
	   let p_f_lit = add_neg_atom_symb p_f_symb (val_var:: (!arg_vars)) in
	   (*Z=Val*)
	   let z_val_lit = add_typed_equality_sym
	       val_type p_f_t_lit_var val_var in
	   let tstp_source = Clause.tstp_source_definition in
	   let new_clause =
	     create_clause tstp_source (z_val_lit:: p_f_lit:: p_f_t_lit:: arg_lits) in
	   new_clause:: rest
	  )
	    
    | Term.Var _ -> failwith "get_definitions: term should be ground"
  in
  TermHash.fold f term_def_table []

(* definitions should be fixed!!! *)

let flat_clause_list clause_list =
  let flat_clauses = List.map flat_clause clause_list in
  let definitions = get_definitions () in
  definitions@flat_clauses

(*---------------Axioms-------------------------*)

(* bound_pred is added to clauses which are active at the current domain bound i *)
let create_bound_pred i =
  let bound_symb_name = ("$$iProver_Bound_Pred_"^(string_of_int i)) in
  let add_bound_symb =
    create_symbol
      bound_symb_name
      (Symbol.create_stype [] Symbol.symb_bool_type)
      Symbol.DomainPred in
  add_fun_term add_bound_symb []

(*-------domains do not include epr/non-cyclic domains----------------*)
type domain =
    {
     dom_type : symbol;
     (* in increasing order *)
     mutable dom_elements : term list;
     
     (* all flat and defpred symbols with value type of domain_type *)
     mutable dom_flat_preds : symbol list;
     (*     mutable dom_def_preds : symbol list; *)
   }

let create_domain dom_type =
  {
   dom_type = dom_type;
   dom_elements =[];
   dom_flat_preds = [];
 }

(*
  module DKey =
  struct
  type t = domain
  let equal d1 d2 = Symbol.equal d1.dom_type d2.dom_type
  let hash d = Symbol.hash d.dom_type
  end
 *)

(* TDomainH hash table mapping domain_type -> domain *)
module TDomainH = Hashtbl.Make(Symbol)

let domain_table = TDomainH.create 101

(*------domains should be initialised before use!-----*)
let init_domains () =
  let f flat_pred =
    let val_type = get_val_pred_type flat_pred in
    (*  out_str ("dom pred "^(Symbol.to_string flat_pred)
	^" domain type: "^(Symbol.to_string val_type)^"\n");		*)
    try

      let dom = TDomainH.find domain_table val_type in
      dom.dom_flat_preds <- flat_pred:: (dom.dom_flat_preds)
    with
      Not_found ->
	(
	 let new_dom = create_domain val_type in
	 new_dom.dom_flat_preds <- [flat_pred];
	 TDomainH.add domain_table val_type new_dom
	)
  in
  SymSet.iter f !flat_sym_set

let add_domain_constant dom i =
  let dom_symb_name =
    ("$$iProver_Domain_"^(Symbol.to_string dom.dom_type)^"_"^(string_of_int i)) in
  
  let add_dom_symb =
    create_symbol
      dom_symb_name (Symbol.create_stype [] dom.dom_type) Symbol.DomainConstant in
  let dom_i_el = add_fun_term add_dom_symb [] in
  (* in increasing order  *)
  dom.dom_elements <- (dom.dom_elements)@[dom_i_el]
(*
  try
  let dom = TDomainH.find domain_table dom_type in
  dom.dom_elements <- dom_i_el:: (dom.dom_elements)
  with
  Not_found -> failwith "add_domain_constant: dom_type should be in domain_table"
 *)

let add_domain_constant_all_dom i =
  (*  out_str ("adding const"^(string_of_int i)^"\n");*)
  TDomainH.iter
    (fun _dom_type dom -> add_domain_constant dom i) domain_table

(*
  let add_domain_constants domain first last =

  let dom_const_list_ref = ref [] in
  for i = first to last
  do
  let add_dom_const = add_domain_constant dom_type i in
  dom_const_list_ref:= add_dom_const::!dom_const_list_ref
  done;
  !dom_const_list_ref
 *)

(*--------- disequality axioms -----------*)
let dis_eq_axioms eq_type t term_list =
  let f rest_f s =
    if not (s == t)
    then
      (let tstp_source = Clause.tstp_source_axiom_distinct in
      let new_clause = 
	create_clause tstp_source [(add_typed_disequality_sym eq_type t s)] in
      new_clause::rest_f
      )
    else
      rest_f
  in
  List.fold_left f [] term_list

(* for all pairs t s in term_list adding t!=s *)
(* we need to add both t!=s and s!=t since we don not add symmetry axioms*)
let dis_eq_axioms_list eq_type term_list =
  let f rest t =
    (dis_eq_axioms eq_type t term_list)@rest
  in
  List.fold_left f [] term_list

let dis_eq_axioms_dom dom =
  (* we do not need to add disequality axioms for non-equality types *)
  (* note that here we do  not need to close eq_types under function application *)
  if (SymSet.mem dom.dom_type !init_sig.Clause.sig_eq_types)
  then
    dis_eq_axioms_list dom.dom_type dom.dom_elements
  else
    []

let dis_eq_axioms_all_dom () =
  TDomainH.fold
    (fun _dom_type dom rest_ax -> ((dis_eq_axioms_dom dom)@rest_ax)) domain_table []

(*----------------------------*)
(* version with symmetry ax in place of explicit pairs t!=s  and s!=t *)

let dis_eq_axioms_sym_list eq_type term_list =
  let rec dis_eq_axioms_sym_list' ax_list term_list_rest =
    match term_list_rest with
    | h:: tl ->
	let new_ax = dis_eq_axioms eq_type h tl in
	let current_ax = new_ax@ax_list in
	dis_eq_axioms_sym_list' current_ax tl
    |[] -> ax_list
  in
  dis_eq_axioms_sym_list' [] term_list

let dis_eq_axioms_dom_sym dom =
  (*  out_str ("domain type"^(Symbol.to_string dom.dom_type)^" domain terms: "^(Term.term_list_to_string dom.dom_elements)^"\n");*)
  
  (* we do not need to add disequality axioms for non-equality types *)
  if (SymSet.mem dom.dom_type !init_sig.Clause.sig_eq_types)
  then
    begin
      let sym_axiom = Eq_axioms.typed_symmetry_axiom_sym dom.dom_type in
      let dis_ax = (dis_eq_axioms_sym_list dom.dom_type dom.dom_elements) in
      (* for the dome size 1 we do not need to add sym_axiom *)
      if dis_ax = []
      then []
      else sym_axiom:: dis_ax
    end
  else
    []

let dis_eq_axioms_all_dom_sym () =
  TDomainH.fold
    (fun _dom_type dom rest_ax -> ((dis_eq_axioms_dom_sym dom)@rest_ax)) domain_table []

(*-----------------*)

(* symbol is a flat symbol, dom_pred is the predicate added to the clause *)
(*to encode crurrent domain *)
(* ex if symb is R and domain terms [1;..;n] then *)
(* the result is dom_pred \/ R(1,x_1,x_2)\/R(2,x_1,x_2)\/...\/R(n,x_1,x_2)*)

let axiom_dom_pred_symb bound_pred symb dom_elements =
  let (symb_types, _bool_type) = Symbol.get_stype_args_val_def symb in
  (* first is val type  *)
  let arg_types, val_type =
    match symb_types with
    | h:: tl -> (tl, h)
    | []-> failwith "axiom_dom_pred_symb: symb should have at least one arg"
  in
  let var_env = Var.init_fresh_vars_env () in
  let rec get_var_args rest_vars rest_arg_types =
    match rest_arg_types with
    | [] -> List.rev rest_vars
    | h:: tl ->
	let new_vars = (add_var_term (Var.get_next_fresh_var var_env h)):: rest_vars in
	get_var_args new_vars tl
  in
  let var_args = get_var_args [] arg_types in
  (*
    let rec get_var_args rest current_var i =
    if i = 0 then List.rev rest
    else
    get_var_args
    ((add_var_term current_var):: rest) (Var.get_next_var current_var) (i -1)
    in
    let var_args =
    get_var_args [] (Var.get_first_var ()) ((Symbol.get_arity symb) -1)
    in
   *)
  let f rest dom_el =
    (add_fun_term symb (dom_el:: var_args)):: rest
  in
  let tstp_source = Clause.tstp_source_axiom_domain in
  let new_cl =
    (create_clause tstp_source (bound_pred:: (List.fold_left f [] dom_elements))) in
  new_cl

let domain_pred_axioms bound_pred dom =
  List.fold_left (fun rest symb ->
    ((axiom_dom_pred_symb bound_pred symb dom.dom_elements):: rest))
    []
    dom.dom_flat_preds

(* EPR congruence axioms *)

(*------------ All domain axioms without symmetry breaking --------------------*)

let domain_pred_axioms_all_dom bound_pred =
  TDomainH.fold
    (fun _dom_type dom rest_ax ->
      ((domain_pred_axioms bound_pred dom)@rest_ax)) domain_table []

(*----optimized version with restricted domain for constants----*)
(* triangular symmetry breaking: first order the constants *)
(* by the number of occurrences then  *)
(* P_c1(1)                            *)
(* P_c2(1)\/P_c2(2)                   *)
(*....................................*)
(* P_ck(1)\/......\/P_ck(k)           *)
(* P_c(k+1)(1)\/..\/P_c(k+1)(k)       *)
(*....................................*)
(* P_cn(1)\/......\/P_cn(k)           *)
(*where k is the domain size = numb dom terms *)

let domain_axioms_triangular_const_list bound_pred dom_elements ordered_flat_consts =
  let rec i_const_lits rest_dom_elements i symb =
    match rest_dom_elements with
    | [] -> []
    | h:: tl ->
	if (i =0) then []
	else
	  ((add_fun_term symb [h]):: (i_const_lits tl (i -1) symb))
  in
  let get_axioms_const (rest, i) symb =
    let tstp_source = Clause.tstp_source_axiom_domain in
    let new_clause =
      create_clause tstp_source (bound_pred:: (i_const_lits dom_elements i symb)) in
    ((new_clause:: rest), i +1)
  in
  let (axioms_const, _) =
    List.fold_left get_axioms_const ([],1) ordered_flat_consts in
  axioms_const

(*-------------------------------*)
let domain_axioms_triangular bound_pred =
  let num_of_occurences flat_sym =
    try
      let orig_symb = SymH.find flat_to_orig flat_sym in
      let num_of_occr = Symbol.get_num_input_occur orig_symb in
      (*out_str ("Orig symb: "^(Symbol.to_string orig_symb)^" Flat symb: "^(Symbol.to_string flat_sym)^" num occ "^(string_of_int num_of_occr)^"\n");*)
      num_of_occr
    with Not_found -> failwith "domain_axioms_triangular_const: should not happen"
  in
  let cmp_occur s1 s2 =
    - (compare (num_of_occurences s1) (num_of_occurences s2)) in
  
  let order_flat_consts flat_consts = List.sort cmp_occur flat_consts in
  
  (* returns (pred_const, other_pred) *)
  let split pred_list =
    List.fold_left
      (fun (pred_cont_rest, other_pred_rest) pred ->
	(if ((Symbol.get_arity pred) = 1)
	then
	  ((pred:: pred_cont_rest), other_pred_rest)
	else
	  (pred_cont_rest, (pred:: other_pred_rest))
	)
      )
      ([],[])
      pred_list
  in
  let dom_fun dom =
    let (flat_consts, other_preds) = split dom.dom_flat_preds in
    let ordered_flat_consts = order_flat_consts flat_consts in
    let flat_consts_ax =
      domain_axioms_triangular_const_list
	bound_pred dom.dom_elements ordered_flat_consts
    in
    let other_preds_ax =
      List.fold_left (fun rest symb ->
	((axiom_dom_pred_symb bound_pred symb dom.dom_elements):: rest))
	[]
	other_preds
    in
    flat_consts_ax@other_preds_ax
  in
  TDomainH.fold
    (fun _dom_type dom rest_ax ->
      ((dom_fun dom)@rest_ax)) domain_table []

(*------------------------*)

(* eq axioms for non flatten types *)
let get_non_flat_eq_axioms () =
  let non_flat_eq_types =
    if !current_options.sat_non_cyclic_types (* subsumse epr_types*)
    then
      (SymSet.inter !cyc_non_cyc_types.non_cyclic_types !init_sig.Clause.sig_eq_types)
    else
      if !current_options.sat_epr_types
      then
	(SymSet.inter !epr_type_set !init_sig.Clause.sig_eq_types)
      else
	SymSet.empty
  in
  let csig =
    {
     Clause.sig_fun_preds =
     SymSet.union !flat_sym_set !init_sig.Clause.sig_fun_preds;
     Clause.sig_eq_types = non_flat_eq_types
   }
  in
  let non_flat_eq_ax = Eq_axioms.typed_eq_axioms_sig csig in
(*	out_str ("\n NON Flat eq ax: "^(Clause.clause_list_to_string non_flat_eq_ax )^"\n");*)
  non_flat_eq_ax

(*--------- SCC based non-flattening -----------------------*)
module DGS = Graph.Imperative.Digraph.Concrete(Symbol.Key)

(* Strongly connected component *)
module DGS_SCC = Graph.Components.Make(DGS)

(* type1 -> type2 graph if there is func. with arg in type1 and val in type2 *)
(* for predicates we add vetecies without edges *)
let get_type_graph signature =
  let type_graph = DGS.create ~size:1001 () in
  let f symb =
    let (arg_types, val_type) = Symbol.get_stype_args_val_def symb in
    if (val_type == Symbol.symb_bool_type)
    then (* just add vertices *)
      (List.iter (DGS.add_vertex type_graph) arg_types)
    else (* add edges *)
      (List.iter (fun t -> DGS.add_edge type_graph t val_type) arg_types)
  in
  SymSet.iter f (signature.Clause.sig_fun_preds);
  type_graph

let get_scc type_graph =
  let scc_list = DGS_SCC.scc_list type_graph in
  (* non_cyclic separte scc consisting of a singe vertex v without an edge v->v *)
  let cyclic_scc, non_cyclic_single =
    let f scc_single =
      match scc_single with
      | [v] -> (DGS.mem_edge type_graph v v)
      | _ -> true
    in
    List.partition f scc_list
  in
  let non_cyclic_type_list = List.flatten non_cyclic_single in
  let non_cyclic_type_set = List.fold_left (fun rest t -> SymSet.add t rest) SymSet.empty non_cyclic_type_list in
  let cyclic_type_list = List.flatten cyclic_scc in
  let cyclic_type_set = List.fold_left (fun rest t -> SymSet.add t rest) SymSet.empty cyclic_type_list in
  
  (* debug out scc *)
  
(*	out_str "Signature SCC cyclic components: \n"; *)
(*	let out_scc_single tlist =
  out_str ("["^(list_to_string Symbol.to_string tlist ";")^"]\n")
  in
  List.iter out_scc_single cyclic_scc;*)
(*
  out_str "\n\n Signature SCC non-cyclic types: \n";
  out_str ("["^(list_to_string Symbol.to_string non_cyclic_type_list ";")^"]\n");
 *)	
  
  (* debug *)
  { cyclic_types = cyclic_type_set; non_cyclic_types = non_cyclic_type_set }

let cyc_non_cyc_types_init () =
  cyc_non_cyc_types := (get_scc (get_type_graph !init_sig));
  Statistics.incr_int_stat (SymSet.cardinal !cyc_non_cyc_types.non_cyclic_types) Statistics.sat_num_of_non_cyclic_types

let init_finite_models clauses =
  init_sig := Clause.clause_list_signature clauses;
  (* out_str ("clause_sig_fun_preds: ");
     (SymSet.iter
     (fun s -> (out_str ((Symbol.to_string s)^"; ")))
     !init_sig.Clause.sig_fun_preds
     );
     out_str "\n";
     (SymSet.iter
     (fun s -> (out_str ((Symbol.to_string s)^"; ")))
     !init_sig.Clause.sig_eq_types);
     out_str "\n";
   *)
  epr_type_set_init ();
  epr_const_set_init ();
  cyc_non_cyc_types_init ();
  flat_signature ();
  
  (*
    out_str " \n\n Finite Models raising SZS_Unknown after cyc_non_cyc_types_init ();\n ";
    raise SZS_Unknown;
   *)

(*--------------------Type otput---------------------*)
(*	
  out_str ("EPR types: ");
  
  (SymSet.iter
  (fun s -> (out_str ((Symbol.to_string s)^", "))) !epr_type_set);
  out_str "\n" ;
  
  out_str ("EPR const set: ");
  
  (SymSet.iter
  (fun s -> (out_str ((Symbol.to_string s)^", "))) !epr_const_set);
  out_str "\n" ;
  
  
  out_str ("Non cyclic types: ");
  
  (SymSet.iter
  (fun s -> (out_str ((Symbol.to_string s)^", "))) !cyc_non_cyc_types.non_cyclic_types);
  out_str "\n" ;
  
  out_str ("Cyclic types: ");
  
  (SymSet.iter
  (fun s -> (out_str ((Symbol.to_string s)^", "))) !cyc_non_cyc_types.cyclic_types);
  out_str "\n" ;
 *)	

  init_domains ()

(*
  (pred_const, other_pred) =
  (Symbol.get_arity s) >1) split flat_pred_list
  let dom_fun dom =
  flat_to_orig
 *)

(*--------test for variable elimination part------*)

type pos_neg_cl_lists =
    { pos_cl_list : Clause.clause list;
      neg_cl_list : Clause.clause list }

module SymbMap = Symbol.Map

let rec add_clause_pred_map pred_map clause =
  let f curr_pred_map lit =
    let atom = Term.get_atom lit in
    let pred_symb = Term.get_top_symb atom in
    try
      let clause_list = SymbMap.find pred_symb curr_pred_map in
      SymbMap.add pred_symb (clause:: clause_list) curr_pred_map
    with
      Not_found ->
	SymbMap.add pred_symb [clause] curr_pred_map
  in
  let lit_list = Clause.get_literals clause in
  List.fold_left f pred_map lit_list

let rec create_pred_map_cl_list clause_list =
  List.fold_left add_clause_pred_map SymbMap.empty clause_list

let rec add_clause_pred_map pred_map clause =
  let f curr_pred_map lit =
    let atom = Term.get_atom lit in
    let is_neg = Term.is_neg_lit lit in
    let pred_symb = Term.get_top_symb atom in
    try
      let old_pos_neg = SymbMap.find pred_symb curr_pred_map in
      let new_pos_neg =
	if is_neg then
	  { old_pos_neg with
	    neg_cl_list = clause:: (old_pos_neg.neg_cl_list)
	  }
	else
	  { old_pos_neg with
	    pos_cl_list = clause:: (old_pos_neg.pos_cl_list)
	  }
      in
      SymbMap.add pred_symb new_pos_neg curr_pred_map
    with
      Not_found ->
	let new_pos_neg =
	  if is_neg
	  then
	    { pos_cl_list = [];
	      neg_cl_list = [clause];
	    }
	  else
	    { pos_cl_list = [clause];
	      neg_cl_list = [];
	    }
	in
	SymbMap.add pred_symb new_pos_neg curr_pred_map
  in
  let lit_list = Clause.get_literals clause in
  List.fold_left f pred_map lit_list

let rec create_pred_map_cl_list clause_list =
  List.fold_left add_clause_pred_map SymbMap.empty clause_list

(* another test *)
type 'a test_rec = 
    {
     mutable test_some : 'a param;
   }


(*
  let rec1 = {test_some = Undef}
  let rec2 = {test_some = Def("abc") }

  let list =
  rec1.test_some <- Def(1);
  rec1.test_some <- Undef;
  rec1.test_some <- Def("abc"); 
  [rec1;rec2]
 *)
(*

  let domain_axioms_triangular_const dom_pred dom_terms const_list =
  let cmp c1 c2 =
  - (compare (Symbol.get_num_input_occur c1) (Symbol.get_num_input_occur c2)) in
  let ordered_const_list = List.sort cmp const_list in
  let oredered_flat_const_list = List.map Symbol.get_flattening ordered_const_list
  in
  let rec i_const_lits rest_dom_terms i symb =
  match rest_dom_terms with
  | [] -> []
  | h:: tl ->
  if (i =0) then []
  else
  ((add_fun_term symb [h]):: (i_const_lits tl (i -1) symb))
  in
  let get_axioms_const (rest, i) symb =
  let new_clause =
  add_clause_lits (dom_pred:: (i_const_lits dom_terms i symb)) in
  ((new_clause:: rest), i +1)
  in
  let (axioms_const, _) =
  List.fold_left get_axioms_const ([],1) oredered_flat_const_list in
  axioms_const

(* auxilary returns (const_list,non_const_flat_pred) in the signature*)
(* const_list is the original (not flat) and non_const_flat_pred are *)
(* non constant flat predicates *)
(* definition symbols from term_def_table are treated as other*)

  let split_input_constants_other () =
  let split_constants_other' s (const_rest, flat_pred_rest) =
  if (Symbol.is_constant s) && (Symbol.get_num_input_occur s) >0
  then (
(* out_str ((Symbol.to_string s)
   ^" num_occ: "^(string_of_int (Symbol.get_num_input_occur s))^"\n"); *)
  ((s:: const_rest), flat_pred_rest))
  else
  if (((Symbol.is_flat s) && (Symbol.get_arity s) >1)
  || (Symbol.is_defpred s))
  then
  (const_rest, (s:: flat_pred_rest))
  else
  (const_rest, flat_pred_rest)
  in
  SymbolDB.fold split_constants_other' !symbol_db_ref ([],[])

 *)

(*----Triangular axioms for constants and plus axioms for the rest-----------*)

(* Commented for the moment

   let domain_axioms_triangular dom_pred dom_terms =
   let (const_list, non_const_flat_pred) = split_input_constants_other () in
(* axioms for constants *)
   let axioms_const = domain_axioms_triangular_const dom_pred dom_terms const_list in
(* axioms for the rest: non constants *)
   let axioms_flat_rest =
   domain_axioms_symb_list dom_pred dom_terms non_const_flat_pred in
   axioms_const@axioms_flat_rest

(*-----------------------------------------*)
(*------ Unit version for constants -------*)
(*---In some cases it is enough to have unit axioms for constants:---*)
(* P_c1(1), P_c2(2),..., P_ck(k) *)
(* where we assume that number domain terms >= number of constants *)
(* This is true for problems without equality *)

   let domain_axioms_unit_const dom_pred dom_terms const_list =
(* we do not need to sort constants here but just for fun *)
   let cmp c1 c2 =
   - (compare (Symbol.get_num_input_occur c1) (Symbol.get_num_input_occur c2)) in
   let ordered_const_list = List.sort cmp const_list in
   let oredered_flat_const_list = List.map Symbol.get_flattening ordered_const_list
   in
(*
  out_str ("Flat Constants:\n "^(list_to_string Symbol.to_string oredered_flat_const_list "\n")^"\n");
  out_str ("Domain Terms:\n "^(list_to_string Term.to_string dom_terms "\n")^"\n");
 *)
   let rec f const_list_dom_terms_rest =
   match const_list_dom_terms_rest with
   | (p_c:: c_tl, t:: t_tl) ->
   (add_clause_lits [(add_fun_term p_c [t])]):: (f (c_tl, t_tl))
   | ([], _) -> []
   | (_,[]) ->
   failwith
   "domain_axioms_unit_const: domain should be greater than the number of constants"
   in
   f (oredered_flat_const_list, dom_terms)

   let domain_axioms_unit dom_pred dom_terms =
   let (const_list, non_const_flat_pred) = split_input_constants_other () in
(* axioms for constants *)
   let axioms_const = domain_axioms_unit_const dom_pred dom_terms const_list in
(* axioms for the rest: non constants *)
   let axioms_flat_rest =
   domain_axioms_symb_list dom_pred dom_terms non_const_flat_pred in
   axioms_const@axioms_flat_rest

 *)

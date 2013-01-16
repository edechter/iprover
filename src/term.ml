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

module VSet = Var.VSet

type var = Var.var
type symbol = Symbol.symbol
type fast_key = int param
type prop_key = TableArray.key
(*association list for counting the number of occurences of vars in a term*)
type var_ass_list = var num_ass_list

type fun_term_bool_param = int

let inst_in_unif_index = 0
let has_conj_symb = 1
let has_non_prolific_conj_symb = 2
let has_bound_constant = 3 (* used for BMC *)

type args = term list
and term =
	| Fun of symbol * args * fun_info
	| Var of var * var_info
and fun_info =
	{ mutable fun_fast_key : fast_key;
		mutable fun_db_id : fast_key;
		mutable num_of_symb : int param;
		(* mutable var_list   : var_list param; *)
		(* can be very expensive and is used only in resol. for kbo, *)
		(* rewrite it there...*)
		mutable num_of_var : int param;   (* cheap *)
		mutable fun_grounded : term param; (* term obtained after grounding *)
		(* prop. key of term (without grounding) used for simplifiactions *)
		mutable prop_key : prop_key param;
		(* prop. key of term after grounding *)
		mutable prop_gr_key : prop_key param;
		mutable bool_param : Bit_vec.bit_vec;
		(*     mutable fun_hash      : int param *)
	}

and var_info =
	{ mutable var_fast_key : fast_key;
		mutable var_db_id : fast_key;
		(*     mutable var_hash     : int param;*)
		mutable var_grounded : term param (*term obtained after grounding*) }

let empty_fun_info () =
	{ fun_fast_key = Undef;
		fun_db_id = Undef;
		num_of_symb = Undef;
		num_of_var = Undef;
		fun_grounded = Undef;
		prop_key = Undef;
		prop_gr_key = Undef;
		(*   fun_hash       = Undef;  *)
		bool_param = Bit_vec.false_vec }

let empty_var_info () =
	{ var_fast_key = Undef;
		var_db_id = Undef;
		(*   var_hash     = Undef;*)
		var_grounded = Undef }

(* easy to reimpliment args as arrays*)

let set_fun_info_bool_param value param fun_info =
	fun_info.bool_param <- Bit_vec.set value param fun_info.bool_param

let get_fun_info_bool_param param fun_info =
	Bit_vec.get param fun_info.bool_param

let set_fun_bool_param value param term =
	match term with
	| Fun(_, _, fun_info) ->
			fun_info.bool_param <- Bit_vec.set value param fun_info.bool_param
	| Var _ -> failwith "term set_fun_bool_param: it's a variable"

let get_fun_bool_param param term =
	match term with
	| Fun(_, _, fun_info) ->
			Bit_vec.get param fun_info.bool_param
	| Var _ -> failwith "term get_fun_bool_param: it's a variable"

type literal = term

type bound_term = term bind

(* type term = {t : pure_term; info : info} *)

exception Term_fast_key_undef
exception Term_db_id_undef
exception Term_weight_undef
exception Term_grounding_undef
exception Term_assign_fkey_to_var

let create_var_term var = Var(var, (empty_var_info ()))
let create_var_term_info var var_info = Var(var, var_info)

exception Num_of_sym_undef

let get_num_of_symb term =
	match term with
	| Fun(_, _,{ num_of_symb = Def(num) }) -> num
	| Var _ -> 1
	| _ -> raise Num_of_sym_undef

exception Num_of_var_undef
let get_num_of_var term =
	match term with
	| Fun(_, _,{ num_of_var = Def(num) }) -> num
	| Var _ -> 1
	| _ -> raise Num_of_var_undef

exception Prop_gr_key_undef
let get_prop_gr_key term =
	match term with
	| Fun(_, _,{ prop_gr_key = Def(key) }) -> key
	| _ -> raise Prop_gr_key_undef

exception Prop_key_undef
let get_prop_key term =
	match term with
	| Fun(_, _,{ prop_key = Def(key) }) -> key
	| _ -> raise Prop_key_undef

(*
exception Term_hash_undef
exception Term_var_hash_undef
let get_hash (t: term) =
match t with
| Fun(_, _, fun_info) ->
(
match fun_info.fun_hash with
| Def(hash) -> hash
| _ -> raise Term_hash_undef
)
| Var(_, var_info) ->
(
match var_info.var_hash with
| Def(hash) -> hash
| _ -> raise Term_var_hash_undef
)
*)

(*-------------------to string's-------------------*)

(*val to_stream             : 'a string_stream -> symbol -> unit*)

let var_int_to_stream s (v, int) =
	s.stream_add_char '(';
	Var.to_stream s v;
	s.stream_add_char ',';
	s.stream_add_str (string_of_int int);
	s.stream_add_char ')'

(*
let var_int_to_string (v, int) =
"("^(Var.to_string v)^","^(string_of_int int)^")"
*)

let var_list_to_stream s vl =
	s.stream_add_char '[';
	list_to_stream s var_int_to_stream vl ",";
	s.stream_add_char ']'

(*
let var_list_to_string v_l =
"["^(list_to_string var_int_to_string v_l ",")^"]"
*)

let rec to_stream s t =
	match t with
	| Fun(sym,[], _) -> Symbol.to_stream s sym
	| Fun(sym, args, _) ->
			begin
				(Symbol.to_stream s sym);
				s.stream_add_char '(';
				list_to_stream s to_stream args ",";
				s.stream_add_char ')'
			end
	| Var(v, _) -> Var.to_stream s v

let rec pp_term ppf = function
	| Fun (sym, [], _) ->
			Format.fprintf ppf "%a" Symbol.pp_symbol sym
	| Fun (sym, args, _) ->
			Format.fprintf
				ppf
				"%a(%a)"
				Symbol.pp_symbol sym
				(pp_any_list pp_term ",") args
	| Var (v, _) ->
			Format.fprintf ppf "%a" Var.pp_var v

let rec pp_term_tptp ppf = function
	
	(* Nullary symbol without arguments *)
	| Fun (sym, [], _) ->
			Format.fprintf ppf "%a" Symbol.pp_symbol_tptp sym
	
	(* Negated typed equation as != *)
	| Fun (s, [Fun(t, [_; l; r], _)], _)
	when s == Symbol.symb_neg &&
	t == Symbol.symb_typed_equality ->
			Format.fprintf
				ppf
				"%a != %a"
				pp_term_tptp l
				pp_term_tptp r
	(*
	(* Negated untyped equation as != *)
	| Fun (s, [Fun(t, [eq_type;l; r], _)], _)
	when s == Symbol.symb_neg &&
	t == Symbol.symb_equality ->
			Format.fprintf
				ppf
				"%a != %a"
				pp_term_tptp l
				pp_term_tptp r
	*)
	
	(* Negation as ~P without parentheses *)
	| Fun (s, [arg], _) when s == Symbol.symb_neg ->
			Format.fprintf
				ppf
				"~ %a"
				pp_term_tptp arg
	
	(* Non-unary negation *)
	| Fun (s, _, _) when s == Symbol.symb_neg ->
			failwith "Term.pp_term_tptp: Non-unary negation"
	
	(* Untyped equation as = *)
	| Fun(s, [_; l; r], _)
	when s == Symbol.symb_typed_equality ->
			Format.fprintf
				ppf
				"%a = %a"
				pp_term_tptp l
				pp_term_tptp r
	
	(* Typed equation as = *)
	| Fun(s, [_; l; r], _)
	when s == Symbol.symb_typed_equality ->
			Format.fprintf
				ppf
				"%a = %a"
				pp_term_tptp l
				pp_term_tptp r
	
	(* Non-nullary symbol as s(_) *)
	| Fun (sym, args, _) ->
			Format.fprintf
				ppf
				"%a(%a)"
				Symbol.pp_symbol_tptp sym
				(pp_any_list pp_term_tptp ",") args
	
	(* Variable *)
	| Var (v, _) ->
			Format.fprintf ppf "%a" Var.pp_var v

let out = to_stream stdout_stream

(*
let to_string t =
let s = create_buffer_stream 10 in
to_stream s t;
to_string_buffer_stream s
*)

let to_string =
	to_string_fun_from_to_stream_fun 10 to_stream

(*
let rec to_string_term t =
match t with
| Fun(sym,[], _) -> Symbol.to_string sym
| Fun(sym, args, _) ->
(Symbol.to_string sym)^"("^(list_to_string to_string_term args ",")^")"
| Var(v, _) -> Var.to_string v

*)

(*
let to_string_with_var_list t =
(to_string_term t)^"-"^(var_list_to_string (get_var_list t))
*)

(*
let to_string_with_num_of_sym t =
(to_string_term t)^"-num_of_symb -"^(string_of_int (get_num_of_symb t))
*)

let to_stream_with_num_of_sym s t =
	to_stream s t;
	s.stream_add_str "-num_of_symb -";
	s.stream_add_str (string_of_int (get_num_of_symb t))

(* let to_string = to_string_with_var_list *)

let term_list_to_stream s t_list =
	list_to_stream s to_stream t_list ";"

let out_term_list = term_list_to_stream stdout_stream

(*
let term_list_to_string =
*)

let term_list_to_string =
	to_string_fun_from_to_stream_fun 30 term_list_to_stream

(*
let term_list_to_string t_list =
let s = create_buffer_stream 30 in
term_list_to_stream s t_list;
to_string_buffer_stream s
*)

(*
let term_list_to_string t_list =
list_to_string to_string t_list ";"
*)

(*-----------------------end to_strings------------------------*)
(* type_check checks that val types of termlist respects types of symb *)
(* type_check is used for debugging *)


let get_term_type t =
	match t with
	| Fun(symb, _args, _inf) -> Symbol.get_val_type_def symb
	| Var(v, _) ->	Var.get_type v

let type_check symb termlist = 
	match (Symbol.get_stype_args_val symb) with 
	| Def((sym_arg_types,_val_type)) -> 
   let f symb_arg_type arg = 
		let arg_type = get_term_type arg in  
		if (Symbol.is_subtype arg_type symb_arg_type)
		then ()
		else 
			failwith 
			("term: type_check failed, symbol "
			^(Symbol.to_string symb)^" has an arg with type "^(Symbol.to_string symb_arg_type)
			^" which is not a supertype of substituted term "^(to_string arg)^" of type "^(Symbol.to_string arg_type) 
			)
			in 
			(
			try
				List.iter2 f sym_arg_types termlist
			with  
			|Invalid_argument _ ->
				failwith ("term: type_check failed, symbol "^(Symbol.to_string symb)
				^" has arity "^(string_of_int (List.length sym_arg_types))
				^" but the list of substituted arguments "^(term_list_to_string termlist)^" has length "^(string_of_int (List.length termlist)))
				)
	| Undef -> ()



let create_fun_term symbol term_list =
	let fun_info = (empty_fun_info ()) in
	(if !current_options.symbol_type_check 
	then type_check symbol term_list
   );
	Fun(symbol, term_list, fun_info)

let create_fun_term_args = create_fun_term

let create_fun_term_info symbol term_list fun_info = Fun(symbol, term_list, fun_info)

let is_constant t =
	match t with
	| Fun(symb,[], _) -> (Symbol.is_constant symb)
	| _ -> false

let assign_prop_gr_key key term =
	match term with
	| Fun(_, _, info) -> info.prop_gr_key <- Def(key)
	| _ -> failwith "Prop_gr_key can not be assigned to vars"

let assign_prop_key key term =
	match term with
	| Fun(_, _, info) -> info.prop_key <- Def(key)
	| _ -> failwith "Prop_key can not be assigned to vars"

(*-----------------complementary literal ---------------*)

let get_atom literal =
	match literal with
	| Fun(sym,[t], _) ->
			if (sym == Symbol.symb_neg) then t
			else literal
	| _ -> literal

let compl_lit literal =
	match literal with
	| Fun(sym, args, _) ->
			if sym == Symbol.symb_neg
			then List.hd args
			else create_fun_term Symbol.symb_neg [literal]
	| _ -> failwith "term: compl_lit it is not a literal"

let is_neg_lit lit =
	match lit with
	| Fun(s, _, _) -> (s == Symbol.symb_neg)
	| _ -> false

let is_complementary l1 l2 =
	match l1 with
	| Fun(sym1, args1, _) ->
			if sym1 == Symbol.symb_neg
			then
				if l2 == (List.hd args1)
				then true
				else false
			else (*l1 is positive*)
			(match l2 with
				| Fun(sym2, args2, _) ->
						if sym2 == Symbol.symb_neg
						then
							if l1 == (List.hd args2)
							then true
							else false
						else false
				| _ -> failwith "term: is_compl it is not a literal"
			)
	| _ -> failwith "term: is_compl it is not a literal"

(* works but got rid of var_list
exception Var_list_is_undef
let get_var_list term =
match term with
| Fun(_, _, fun_info) ->
( match fun_info.var_list with
| Def (vl) -> vl
| Undef -> raise Var_list_is_undef
)
| Var(v, _) -> [(v,1)]

*)

(* assume that term is a Var term*)

let get_var var_term =
	match var_term with
	| Var(v, _) -> v
	| _ -> failwith "term: get_var not a Var term"

(*
(* Get variables in term recursively *)
let rec get_vars' accum = function
	
	(* No more subterms to recurse into *)
	| [] -> accum
	
	(* Term is a functional term *)
	| Fun(_, args, _) :: tl -> get_vars' accum (args @ tl)
	
	(* Term is a variable that has already been seen *)
	| Var (v, _) :: tl when List.mem v accum -> get_vars' accum tl
	
	(* Term is a variable that has not been seen *)
	| Var (v, _) :: tl -> get_vars' (v :: accum) tl

(* Get all variables occurring in term *)
let get_vars term = get_vars' [] [term]
*)

(* not efficient*)
let rec get_var_ass_list term =
	match term with
	| Fun(_, args, _) ->
			let f rest term = append_ass_list (+) (get_var_ass_list term) rest in
			List.fold_left f [] args
	| Var(v, _) -> [(v,1)]


let rec add_var_set vset term = 
	match term with
	| Fun(_, args, _) ->
		List.fold_left add_var_set vset args
	| Var (v, _) -> 			
			VSet.add v vset
  
let get_vars t = 
	let vset = add_var_set (VSet.empty) t in
	VSet.elements vset


(*e.g. has_conj_symb, has_bound_constant *)
let get_fun_term_bool_param bool_param t =
	match t with
	| Fun(_, _, fun_info) -> (get_fun_info_bool_param bool_param fun_info)
	| Var _ -> false

(* term with such bool_param true exists in the list *)
let get_fun_term_bool_param_term_list bool_param tlist =
	List.exists (get_fun_term_bool_param bool_param) tlist

(* let has_conj_symb_fun term =
get_fun_term_bool_param has_conj_symb term

let has_non_prolific_conj_symb_fun term =
get_fun_term_bool_param has_non_prolific_conj_symb term

let has_bound_constant_fun term =
get_fun_term_bool_param has_bound_constant term
*)

let get_num_of_symb_term_list term_list =
	let f rest term = rest + (get_num_of_symb term) in
	List.fold_left f 0 term_list

let get_num_of_var_term_list term_list =
	let f rest term = rest + (get_num_of_var term) in
	List.fold_left f 0 term_list

(*
let get_has_conj_symb_term_list term_list =
List.exists has_conj_symb_fun term_list

let get_has_non_prolific_conj_symb_term_list term_list =
List.exists has_non_prolific_conj_symb_fun term_list

let get_has_bound_constant_term_list term_list =
List.exists has_bound_constant_fun term_list
*)

(*
let hash_comb rest term_hash =
(* abs((rest lsl 1) lxor term_hash)*)
((rest lsl 3) + term_hash) * 131
(* (rest + term_hash) * 131*)
(*  abs((rest lsl 3) + term_hash)*)
*)

(*
let get_hash_term_list init_hash term_list =
let hash_fun rest term =
let term_hash = get_hash term in
hash_comb rest term_hash in
List.fold_left hash_fun init_hash term_list
*)

let assign_grounding ground_term term =
	match term with
	| Fun(_, _, fun_info) ->
			fun_info.fun_grounded <- Def(ground_term)
	| Var(_, var_info) ->
			var_info.var_grounded <- Def(ground_term)

let get_grounding term =
	match term with
	| Fun(_, _,{ fun_grounded = Def(grounding) }) -> grounding
	| Var(_,{ var_grounded = Def(grounding) }) -> grounding
	| _ -> raise Term_grounding_undef

(* only atoms get assigned groundings *)
let get_grounding_lit lit =
	if (is_neg_lit lit)
	then
		let atom = get_atom lit in
		let atom_gr = get_grounding atom in
		compl_lit atom_gr
	else
		get_grounding lit

(* we assume that all subterms of the term for assingments *)
(* have everything defined and parameters of the term itself are not!*)

let assign_num_of_symb term =
	match term with
	| Fun(_, args, fun_info) ->
	(* out_str("Num Symb: "^(string_of_int ((get_num_of_symb_term_list args)+1))^"\n"); *)
			fun_info.num_of_symb <- Def((get_num_of_symb_term_list args) +1)
	| _ -> ()

let assign_num_of_var term =
	match term with
	| Fun(_, args, fun_info) ->
			fun_info.num_of_var <- Def((get_num_of_var_term_list args))
	| _ -> ()

(*
let assign_has_conj_symb term =
match term with
| Fun(symb, args, fun_info) ->
let has_conj = ((Symbol.get_bool_param Symbol.is_conj_symb symb)
|| (get_has_conj_symb_term_list args)) in
set_fun_info_bool_param has_conj has_conj_symb fun_info
| _ -> ()
*)

(* assign term_bool_param if there exists symbol with *)
(* corresponding symbol_bool_param in the term        *)

let assign_symbol_bool_param_term symb_bool_param term_bool_param term =
	match term with
	| Fun(symb, args, fun_info) ->
			let bool_param_val = ((Symbol.get_bool_param symb_bool_param symb)
					|| (get_fun_term_bool_param_term_list term_bool_param args)) in
			set_fun_info_bool_param bool_param_val term_bool_param fun_info
	| _ -> ()

let assign_has_non_prolific_conj_symb term =
	match term with
	| Fun(symb, args, fun_info) ->
			let num_of_occ_in_input = (Symbol.get_num_input_occur symb) in
			let has_non_prolific_conj =
				(
					((Symbol.get_bool_param Symbol.is_conj_symb symb)
						&& (num_of_occ_in_input > 0)
						&& (num_of_occ_in_input < !current_options.prolific_symb_bound)
					)
					|| (get_fun_term_bool_param_term_list has_non_prolific_conj_symb args)
				)
			in
			set_fun_info_bool_param
				has_non_prolific_conj has_non_prolific_conj_symb fun_info
	| _ -> ()

(* we assume that subterms term cannot  have hash undef never redefine!*)
(*
let assign_hash term =
match term with
| Fun(symb, args, fun_info) ->
(let symb_hash = Symbol.get_hash symb in
let fun_hash = (get_hash_term_list symb_hash args) in
fun_info.fun_hash <- Def(fun_hash);
(*  out_str ("fun hash: "^(string_of_int fun_hash)^"\n")*)
)

| Var(v, var_info) ->
(let var_hash = Var.hash(v) in
var_info.var_hash <- Def(var_hash)
(*     out_str ("var hash: "^(string_of_int var_hash)^"\n")) *)
*)

(*
let rec assign_hash_full term =
(try (get_hash term)
with
Term_hash_undef | Term_var_hash_undef ->
(match term with
| Fun(symb, args, fun_info) ->
(let symb_hash = Symbol.get_hash symb in
let fun_hash = (get_hash_term_list_full symb_hash args) in
fun_info.fun_hash <- Def(fun_hash);
(* out_str ("Term: "^(to_string term)^"\n");
out_str ("def fun hash: "^(string_of_int fun_hash)^"\n");*)
fun_hash
)
| Var(v, var_info) ->
(let var_hash = Var.hash(v) in
var_info.var_hash <- Def(var_hash);
(* out_str ("Term: "^(to_string term)^"\n");
out_str ("def var hash: "^(string_of_int var_hash)^"\n");*)
var_hash)
)
)

and get_hash_term_list_full symb_hash args =
let hash_fun rest arg_term =
let arg_term_hash = assign_hash_full arg_term in
(*was hash_comb rest arg_term_hash; not very good... *)
hash_comb arg_term_hash rest in
List.fold_left hash_fun symb_hash args

*)

(* f: first arg  is depth and second is sym, f is applied from top to bottom*)
let rec iter_sym_depth' f current_depth term =
	match term with
	| Fun(sym, args, _) ->
			(f current_depth sym;
				List.iter (iter_sym_depth' f (current_depth +1)) args
			)
	| _ -> ()

let iter_sym_depth f term =
	iter_sym_depth' f 1 term

(*
let assign_var_list term =
match term with
| Fun(_, args, fun_info) ->
let f rest term = append_ass_list (+) (get_var_list term) rest in
let var_list = List.fold_left f [] args in
fun_info.var_list <- Def(var_list)
| _ -> ()
*)

(* all fun info added only when we add term to term db

let create_fun_term symbol term_list =
let fun_info = (empty_fun_info ()) in
let () = fun_info.num_of_symb <- Def((get_num_of_symb_term_list term_list)) in
let f rest term = append_ass_list (+) (get_var_list term) rest in
let var_list = List.fold_left f [] term_list in
let () = fun_info.var_list <- Def(var_list) in
Fun(symbol, term_list, fun_info)
*)

let is_ground t = ((get_num_of_var t) = 0)

exception Term_fast_key_is_def

let assign_fast_key (t: term) (fkey: int) =
	match t with
	| Fun(_, _, fun_info) ->
			(match fun_info.fun_fast_key with
				| Undef -> fun_info.fun_fast_key <- Def(fkey)
				| _ -> raise Term_fast_key_is_def
			)
	| Var(_, var_info) ->
			( match var_info.var_fast_key with
				| Undef -> var_info.var_fast_key <- Def(fkey)
				| _ -> raise Term_fast_key_is_def
			)

exception Term_db_id_is_def

let assign_db_id = function
	
	(* Raise exception when db_id is already defined for functional term*)
	| Fun(_, _, { fun_db_id = Def _ }) ->
			(function _ -> raise Term_db_id_is_def)
	
	(* Raise exception when db_id is already defined for variable term *)
	| Var(_, { var_db_id = Def _ }) ->
			(function _ -> raise Term_db_id_is_def)
	
	(* Set db_id to defined value for functional term *)
	| Fun(_, _, fun_info) ->
			(function db_id -> fun_info.fun_db_id <- Def(db_id))
	
	(* Set db_id to defined value for variable *)
	| Var(_, var_info) ->
			(function db_id -> var_info.var_db_id <- Def(db_id))

(*
exception Term_hash_is_def
*)

(* todo: in one iteration all these*)

let assign_has_conj_symb term =
	assign_symbol_bool_param_term Symbol.is_conj_symb has_conj_symb term

let assign_fun_all term =
	assign_num_of_symb term;
	assign_num_of_var term;
	assign_has_conj_symb term;
	(*  assign_symbol_bool_param_term Symbol.is_conj_symb has_conj_symb term;*)
	assign_symbol_bool_param_term Symbol.is_bound_constant has_bound_constant term;
	assign_has_non_prolific_conj_symb term

let assign_var_all term = ()
(*  assign_hash term *)

(* var_list is used in resolution but not in instantiation
let assign_all term = assign_num_of_symb term; assign_var_list term *)

(*raise Term_assign_fkey_to_var*)

let arg_map = List.map
let arg_map_list = List.map
let arg_map_left = list_map_left

let arg_fold_left = List.fold_left
let arg_fold_right = List.fold_right

let arg_fold_left2 f a l1 l2 =
	try List.fold_left2 f a l1 l2
	with
		Invalid_argument(_) ->
			failwith "term: fold_left2: argumets are of different length"

let arg_for_all2 = List.for_all2

let arg_iter = List.iter
let arg_iter2 f l1 l2 =
	try
		List.iter2 f l1 l2
	with
		Invalid_argument(_) ->
			failwith "term: iter2: argumets are of different length"

let arg_map2 f l1 l2 =
	try
		List.map2 f l1 l2
	with
		Invalid_argument(_) ->
			failwith "term: map2: argumets are of different length"

let arg_find = List.find

let arg_find2 = list_find2

(* arg_return_g_if_f2 f g args1 args2 -> first (g h1 h2) such that (f h1 h2) *)
let arg_return_g_if_f2 = list_return_g_if_f2

let arg_find_not_equal = list_find_not_equal

let arg_to_list x = x
let list_to_arg x = x

let is_empty_args x = (x =[])

let get_fast_key (t: term) =
	match t with
	| Fun(_, _,{ fun_fast_key = Def(fkey) }) -> fkey
	
	| Var(_,{ var_fast_key = Def(fkey) }) -> fkey
	
	| _ -> raise Term_fast_key_undef

let rec fold_left f v t =
	match t with
	| Fun(_sym, args, _) ->
			let res_arg = List.fold_left (fold_left f) v args in
			f res_arg t
	| _ -> f v t

let rec map f t =
	match t with
	| Fun(sym, args, _) ->
			let new_args =
				List.map (map f) args in
			f (create_fun_term sym new_args)
	| v -> f v

(* f: var-> term *)
let rec map_var f t =
	match t with
	| Fun(sym, args, _) ->
			let new_args =
				List.map (map_var f) args in
			create_fun_term sym new_args
	| Var(v,_) -> f v

(* true is s is a subterm of t *)
let is_subterm s t =
	fold_left
		(fun v t -> (v || t == s)) false t

let iter f t =
	match t with
	| Fun(sym, args, _) ->
			List.iter f args;
			f t
	| v -> f v

exception Exists

let exists f t =
	let f' s =
		if (f s)
		then
			raise Exists
		else ()
	in
	try
		iter f' t;
		false
	with
	| Exists -> true

(* fold_sym folds f for all symbols in the term *)
let rec fold_sym f a term =
	match term with
	| Fun(sym, args, _) ->
			List.fold_left (fold_sym f) (f a sym) args
	| _ -> a

let rec iter_sym f term =
	match term with
	| Fun(sym, args, _) ->
			(f sym;
				List.iter (iter_sym f) args
			)
	| _ -> ()

(* replace all occurrences of subterm by byterm in t *)
(* we assume that t, p, and q are in the term db and therefore we are using == *)
(* the resulting term will need to be  added in term db separately *)

let rec replace ~subterm ~byterm t =
	let f xt =
		if xt == subterm
		then byterm
		else xt
	in
	map f t

(* if the type of the term is the same as type of the argument then replace it *)

(*let inst_all_vars_by_term_typed *)

(*
map (subterm == t)

if (subterm == t)
then
byterm
else
begin
match t with
| Fun(sym, args, _) ->
let new_args =
arg_map (replace ~subterm: subterm ~byterm: byterm) args in
create_fun_term sym new_args
| v -> v
end
*)

(* used in compare_key we assume that var alwyas greater than fun term*)
let compare_fun_var t s =
	match (t, s) with
	| (Fun _, Var _) -> cless
	| (Var _, Fun _) -> cgreater
	| _ -> cequal

(* old works but not very efficient
let rec compare_key (t1: term)(t2: term) =
match (t1, t2) with
| (Fun(symbol1, args1, _), Fun(symbol2, args2, _)) ->
let c = Symbol.compare symbol1 symbol2
in
if c = cequal then
try (arg_find_not_equal compare_key args1 args2)
with Not_found -> cequal
else c
| (Var(x, _), Var(y, _)) -> Var.compare x y
| _ -> compare_fun_var t1 t2
*)

let rec compare_key (t1: term)(t2: term) =
	match (t1, t2) with
	| (Fun(symbol1, args1, _), Fun(symbol2, args2, _)) ->
			let c = Symbol.compare symbol1 symbol2
			in
			if c = cequal then
				let f result s1 s2 =
					if not (result = cequal)
					then result
					else compare_key s1 s2
				in
				arg_fold_left2 f cequal args1 args2
			else c
	| (Var(x, _), Var(y, _)) -> Var.compare x y
	| _ -> compare_fun_var t1 t2

let compare_fast_key (t1: term)(t2: term) =
	(compare (get_fast_key t1) (get_fast_key t2))

let compare = compare_fast_key

let apply_to_atom f lit =
	match lit with
	| Fun(sym,[t], _) ->
			if (sym == Symbol.symb_neg)
			then (create_fun_term Symbol.symb_neg [(f t)])
			else f lit
	| lit -> f lit

let is_eq_atom atom =
	match atom with
	| Fun(sym, _, _) ->
			(sym == Symbol.symb_typed_equality)
	| _ -> false

let is_eq_lit lit =
	let atom = get_atom lit in
	is_eq_atom atom

let is_clock_lit lit =
	match get_atom lit with
	| Fun(symb, _, _) ->
			Symbol.get_bool_param Symbol.is_clock symb
	| _ -> false

let is_less_lit lit =
	match get_atom lit with
	| Fun(symb, _, _) ->
			Symbol.get_bool_param Symbol.is_less symb
	| _ -> false

let is_range_lit lit =
	match get_atom lit with
	| Fun(symb, _, _) ->
			Symbol.get_bool_param Symbol.is_range symb
	| _ -> false

let is_next_state_lit lit =
	match get_atom lit with
	| Fun(symb, _, _) ->
			symb == Symbol.symb_ver_next_state
	| _ -> false

let is_reachable_state_lit lit =
	match get_atom lit with
	| Fun(symb, _, _) ->
			symb == Symbol.symb_ver_reachable_state
	| _ -> false

let is_var term =
	match term with
	| Var _ -> true
	| _ -> false

exception Var_term

let get_top_symb t =
	match t with
	| Fun(sym, _, _) -> sym
	| _ -> raise Var_term

let lit_get_top_symb l =
	get_top_symb (get_atom l)

let get_args t =
	match t with
	| Fun(_sym, args, _) -> args
	| _ -> failwith "term: get_args is a var"

let rec var_in var term =
	match term with
	| Fun(_, args, _) ->
			List.exists (var_in var) args
	| Var(v, _) -> (Var.equal var v)

(*---------is epr if funct. are constants-*)
let is_epr_lit l =
	let atom = get_atom l in
	match atom with
	| Fun(symb, args, _) ->
			if (List.exists (fun t -> (not (is_constant t)) & (not (is_var t))) args)
			then false
			else true
	| _ -> true

(* in OCaml true >= false and (compare true false) = 1 *)

(* compare two terms: *)

let cmp_ground t1 t2 =
	Pervasives.compare (is_ground t1) (is_ground t2)

let cmp_num_symb t1 t2 =
	Pervasives.compare (get_num_of_symb t1) (get_num_of_symb t2)

let cmp_num_var t1 t2 =
	Pervasives.compare (get_num_of_var t1) (get_num_of_var t2)

(*pos bigger than neg*)
let cmp_sign t1 t2 =
	- (Pervasives.compare (is_neg_lit t1) (is_neg_lit t2))

let cmp_bool_param param t1 t2 =
	Pervasives.compare (get_fun_bool_param param t1) (get_fun_bool_param param t2)

let cmp_has_conj_symb t1 t2 =
	cmp_bool_param has_conj_symb t1 t2

let cmp_has_bound_constant t1 t2 =
	cmp_bool_param has_bound_constant t1 t2

let cmp_has_non_prolific_conj_symb t1 t2 =
	cmp_bool_param has_non_prolific_conj_symb t1 t2

let is_split_lit t =
	let atom = get_atom t in
	match atom with
	| Fun(symb, _, _) ->
			(Symbol.get_property symb) = Symbol.Split
	| _ -> false

let cmp_split t1 t2 =
	Pervasives.compare (is_split_lit t1) (is_split_lit t2)

let cmp_is_eq_lit t1 t2 =
	Pervasives.compare (is_eq_lit t1) (is_eq_lit t2)

let cmp_is_clock_lit t1 t2 =
	Pervasives.compare (is_clock_lit t1) (is_clock_lit t2)

let cmp_is_less_lit t1 t2 =
	Pervasives.compare (is_less_lit t1) (is_less_lit t2)

let cmp_is_range_lit t1 t2 =
	Pervasives.compare (is_range_lit t1) (is_range_lit t2)

let cmp_is_next_state_lit t1 t2 =
	Pervasives.compare (is_next_state_lit t1) (is_next_state_lit t2)

let cmp_is_reachable_state_lit t1 t2 =
	Pervasives.compare (is_reachable_state_lit t1) (is_reachable_state_lit t2)

let lit_cmp_type_to_fun t =
	match t with
	| Options.Lit_Sign b -> compose_sign b cmp_sign
	| Options.Lit_Ground b -> compose_sign b cmp_ground
	| Options.Lit_Num_of_Var b -> compose_sign b cmp_num_var
	| Options.Lit_Num_of_Symb b -> compose_sign b cmp_num_symb
	| Options.Lit_Split b -> compose_sign b cmp_split
	| Options.Lit_has_conj_symb b -> compose_sign b cmp_has_conj_symb
	| Options.Lit_has_bound_constant b -> compose_sign b cmp_has_bound_constant
	| Options.Lit_next_state b -> compose_sign b cmp_is_next_state_lit
	| Options.Lit_reachable_state b -> compose_sign b cmp_is_reachable_state_lit
	| Options.Lit_has_non_prolific_conj_symb b ->
			compose_sign b cmp_has_non_prolific_conj_symb
	| Options.Lit_eq b -> compose_sign b cmp_is_eq_lit
	| Options.Lit_clock b -> compose_sign b cmp_is_clock_lit
	| Options.Lit_less b -> compose_sign b cmp_is_less_lit
	| Options.Lit_range b -> compose_sign b cmp_is_range_lit

let lit_cmp_type_list_to_lex_fun l =
	lex_combination (List.map lit_cmp_type_to_fun l)

(*--------------------------*)

let is_skolem_name str =
	try
		match (Str.first_chars str 2) with
		|"sK" -> true
		| _ -> false
	with
		Invalid_argument _ -> false

let is_skolem_const term =
	try
		let symb = get_top_symb term in
		is_skolem_name (Symbol.get_name symb)
	with
		Var_term -> false

let is_addr_const t =
	match t with
	| Fun (symb, args, _) ->
			((arg_to_list args) = []) &&
			(Symbol.is_address_const_symb symb)
	| _ -> false

(*----------------------*)

module Key =
struct
	type t = term
	let equal = (==)
	let hash = get_fast_key
	let compare = compare_fast_key
end

module Map = Map.Make(Key)

module Set = Set.Make(Key)

module Hashtbl = Hashtbl.Make(Key)

type term_set = Set.t

(* use prop_key!
exception Term_porpos_id_not_positive
exception Term_porpos_id_not_def
let get_propos_id_term t =
let id =
(match t with
| Fun(_, _,{ fun_fast_key = Def(id) }) -> id
| Var(_,{ var_fast_key = Def(id) }) -> id
| _ -> raise Term_porpos_id_not_def)
in
if id > 0 then id
else raise Term_porpos_id_not_positive

let get_propos_id lit =
if (is_neg_lit lit)
then - (get_propos_id_term (get_atom lit))
else get_propos_id_term lit

let get_propos_gr_id lit = get_propos_id (get_grounding lit)
*)

(*
let to_string = to_string_with_num_of_symb
*)
(*
let rec subterm subt t =
if equal sumbt t then True
else
match t with
| Fun(_, args, _) -> map_arg subterm args
| _ -> False
*)

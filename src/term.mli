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

type var    = Var.var
type symbol = Symbol.symbol
type args 
type fun_info   
type var_info



(*association list for counting the number of occurences of vars in a term*)
type var_list = var num_ass_list

type term =
   Fun of symbol * args * fun_info
 | Var of var * var_info 


type literal = term 

type bound_term = term Lib.bind

exception Term_fast_key_undef
exception Term_weight_undef


val create_var_term       : var -> term
val create_var_term_info  : var -> var_info -> term

val create_fun_term       : symbol -> term list -> term
val create_fun_term_args  : symbol -> args -> term
val create_fun_term_info  : symbol -> term list -> fun_info -> term

val get_num_of_symb       : term -> int
val get_num_of_var        : term -> int

(* assume that term is a Var term*)
val get_var               : term -> var

val get_var_list          : term -> var_list  

(* bool params *)
type fun_term_bool_param 
val inst_in_unif_index      : fun_term_bool_param

val has_conj_symb       : fun_term_bool_param
val has_bound_constant  : fun_term_bool_param (* used for BMC *)

val assign_has_conj_symb      : term -> unit

val has_non_prolific_conj_symb : fun_term_bool_param
val assign_has_non_prolific_conj_symb :  term -> unit

val set_fun_bool_param : bool ->  fun_term_bool_param -> term -> unit
val get_fun_bool_param : fun_term_bool_param -> term -> bool 

(* prop_gr_key for the table prop_var-term *)

type prop_key             = TableArray.key

(* prop. key of term (without grounding) used for simplifiactions *)
exception Prop_key_undef
val get_prop_key          : term -> prop_key
val assign_prop_key       : prop_key -> term -> unit

(* prop. key of term after grounding *)
exception Prop_gr_key_undef
val get_prop_gr_key          : term -> prop_key
val assign_prop_gr_key       : prop_key -> term -> unit
(* *)


val compl_lit   : term -> term
val is_neg_lit  : term -> bool
val is_complementary : term -> term -> bool

(* apply only to literals, returns if a literal is in EPR: all arguments are eiter constants or vars*)
val is_epr_lit  : term -> bool

exception Term_grounding_undef
val get_grounding         : term -> term

val get_args : term -> args

(* use get_prop_key ! *)
(* propositional id of grounding of the literal *)
(* can raise Term_ground_undef*)
(* val get_propos_gr_id : term -> int *)

(*folds f on all symbols in the term*)
val fold_sym : ('a -> symbol -> 'a) -> 'a -> term -> 'a 

val iter_sym : (symbol-> unit) -> term -> unit


(* f: first arg  is depth and second is sym, f is applied from top to bottom*)
(* depth starts with 1, (0 if symbol does not occur) *)
val iter_sym_depth : (int -> symbol -> unit) -> term -> unit 

(* assign_fast_key is done when building termDB *)
 
val assign_fast_key   : term -> int -> unit
(* only to be used in termDB*)
val assign_num_of_symb : term -> unit
(* first arg is a ground term assigned to the second arg *)
val assign_grounding  : term  -> term -> unit
(* val assign_var_list   : term -> unit *)
val assign_fun_all        : term -> unit
val assign_var_all        : term -> unit

(*
exception Term_hash_undef
(* assume that for all subterms hash has been assigned before*)
(*val assign_hash           : term -> unit*)

(* assigns hash to term without assumptions and returns this hash *)
val assign_hash_full      : term -> int
val get_hash              : term -> int
*)

val arg_map          : (term -> term) -> args -> args	
val arg_map_list     : (term -> 'a) -> args -> 'a list
val arg_to_list      : args -> term list
val is_empty_args       : args -> bool
(* explicitly maps from left to right, 
   since order can matter when use imperative features *)
val arg_map_left     : (term -> term) -> args -> args	


val arg_fold_left    : ('a -> term -> 'a)-> 'a -> args -> 'a
val arg_fold_right   : (term -> 'a -> 'a)-> args -> 'a -> 'a 
val arg_fold_left2   : 
    ('a ->  term -> term -> 'a) -> 'a -> args -> args -> 'a
val arg_for_all2 : (term -> term -> bool) -> args -> args -> bool

val arg_iter  : (term -> unit) -> args -> unit 
val arg_iter2 : (term -> term -> unit) -> args -> args -> unit


val is_constant : term -> bool
val is_ground   : term -> bool
val is_var      : term -> bool 
val var_in      : var -> term -> bool

(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. termDB is build; 
   before that use compare_key *)  

val compare               : term -> term -> int 

(* compare_key impl. as structural equality used for termDB*)
(* variables and variables as terms Var(v,i) can have different fast keys*)
val compare_key           : term -> term -> int
val compare_fast_key      : term -> term -> int

val is_neg_lit            : literal -> bool
val get_atom              : literal -> term
val is_eq_lit             : literal -> bool


exception Var_term
val get_top_symb          : term -> symbol
val lit_get_top_symb      : term -> symbol

(* compare two terms *)
val cmp_ground   : term -> term -> int 
val cmp_num_symb : term -> term -> int 
val cmp_num_var  : term -> term -> int 
val cmp_sign     : term -> term -> int 
val cmp_split    : term -> term -> int 
val lit_cmp_type_list_to_lex_fun :  
    Options.lit_cmp_type list -> (literal -> literal -> int) 
 

val to_stream           : 'a string_stream -> term -> unit
val out                 : term -> unit

val term_list_to_stream : 'a string_stream -> (term list) -> unit
val out_term_list       : (term list) -> unit

(* better use to_stream *)
val to_string : term -> string
val term_list_to_string : (term list) -> string


(* applies function to atom i.e. if ~p then ~f(p); if p then f(p)  *)
(* f should not return negative literals *)
(* adding to term_db should be done separately  *)
val apply_to_atom : (term -> term) -> term -> term 

val get_fast_key : term -> int

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

type symbol

type t=symbol

type fast_key 

type stype (*= (symbol list) param *)

val create_stype : (symbol list) -> symbol -> stype
val create_empty_stype : unit -> stype



(* Split is pred indroduced in splitting and Flat in flattening*)
(* Domain constants and DefPred used in finite models *)

(* FunPred are Functions obtained by Non-Eq preds -> Eq translation *)
type sproperty = 
  |Theory 
  |Split 
  |Flat 
  |FunPred
  |DomainConstant
  |DomainPred
  |DefPred
  |Type
  |Quantifier
  |Connective
  |Undef_Prop
  |FDLess of int 
  |FDRange of int * int
(*
  |BitVector of int  (* size of the bv *)
  |Memory of int * int (* (size of the address space) * (size of the bit-vec space) *)
*)
	
(* Special Symbols*)
val symb_bool_type         : symbol
val symb_default_type      : symbol
val symb_type_types        : symbol
val symb_bot_type          : symbol
val symb_term_algebra_type : symbol
val symb_ver_state_type     : symbol
val symb_ver_address_type   : symbol
val symb_ver_bit_index_type : symbol

(*
val symb_and               : symbol
val symb_or                : symbol
val symb_impl              : symbol
val symb_forall            : symbol
val symb_exists            : symbol
*)

val symb_neg               : symbol
val symb_true              : symbol
val symb_false             : symbol
(*val symb_equality          : symbol*)
val symb_typed_equality    : symbol
val symb_ver_next_state    : symbol
val symb_ver_reachable_state : symbol
 
(*
val symb_plus              : symbol
val symb_product           : symbol
val symb_minus             : symbol
val symb_unaryminus        : symbol
*)

(*val symb_iprover_eq        : symbol*)
val symb_distinct          : symbol
val symb_bot               : symbol
val symb_top               : symbol
val symb_answer            : symbol

(* list of all symbols above *)
val special_symbols : symbol list

val is_special_symbol : symbol -> bool
 
val is_defined_type : symbol -> bool

exception Symbol_fast_key_undef
exception Arity_undef
exception Group_undef

(* use SymbolDB.get_num_of_sym_groups to get the actual number of groups*)
val max_num_of_sym_groups : int

val create_from_str               : ?is_sig:bool-> string -> stype -> symbol
val create_from_str_type          : ?is_sig:bool-> string -> stype -> symbol 
val create_from_str_type_property : ?is_sig:bool-> string -> stype -> sproperty -> symbol

val create_type_symb_from_str     : ?is_sig:bool ->string -> symbol

val is_signature_symb : symbol -> bool

(* can be used for checking whether a key is in db or to find a symb with this key *)
val create_template_key_symb : string -> (*stype -> sproperty ->*) symbol 

(* returns args value of the type if defined *)
val get_stype_args_val : symbol -> ((symbol list) * symbol) param

(* as above but can fail if  stype  is not  defined *)
val get_stype_args_val_def : symbol -> (symbol list) * symbol
val get_val_type_def       : symbol -> symbol

(* fast key assigned when symbolDB is creating*)
val  assign_fast_key       : symbol -> int -> unit
val  assign_db_id       : symbol -> int -> unit
(*val  assign_hash           : symbol -> int -> unit*)

val assign_group           : symbol -> int -> unit
val assign_is_input        : bool -> symbol  -> unit
val assign_is_essential_input        : bool -> symbol  -> unit
val assign_is_skolem       : bool -> symbol  -> unit

val assign_stype : symbol -> stype -> unit

	
(* assigns which are part of the key should not be used! *)
(* otherwise problems with SymbolDB                      *)
(*
val assign_property        : sproperty -> symbol -> unit
val assign_type           : stype -> symbol -> unit
val assign_type_pred       :  symbol -> unit
*)


(* bool params *)
type symbol_bool_param 

val is_conj_symb                  : symbol_bool_param
val is_bound_constant             : symbol_bool_param
val large_ax_considered_gr        : symbol_bool_param
val large_ax_considered_non_gr    : symbol_bool_param

val is_defined_symb_input         : symbol_bool_param

val is_clock : symbol_bool_param
val is_less : symbol_bool_param
val is_range : symbol_bool_param

val is_constant                 : symbol -> bool
val is_pred                     : symbol -> bool
val is_fun                      : symbol -> bool

val get_name                    : symbol -> string


val set_bool_param : bool ->  symbol_bool_param -> symbol -> unit
val get_bool_param : symbol_bool_param -> symbol -> bool 
(* inherit_bool_param param from_s to_s *)
val inherit_bool_param     :  symbol_bool_param -> symbol -> symbol -> unit
(* inherit_bool_param_all  from_s to_s *)
val inherit_bool_param_all :  symbol -> symbol -> unit

val get_num_input_occur   : symbol -> int
val incr_num_input_occur  : symbol -> unit

val assign_defined_depth  : int -> symbol -> unit 
val get_defined_depth     : symbol -> int param

val to_stream             : 'a string_stream -> symbol -> unit
val out                   : symbol -> unit
val out_full              : symbol -> unit
val prolog_to_stream      : 'a string_stream -> symbol -> unit

val to_string             : symbol -> string
val to_prolog             : symbol -> string

val pp_symbol : Format.formatter -> symbol -> unit
val pp_symbol_tptp : Format.formatter -> symbol -> unit

val to_stream_full        : 'a string_stream -> symbol -> unit
val to_string_full        : symbol -> string

val get_arity             : symbol -> int
val assign_arity          : int -> symbol -> unit
val is_arity_def          : symbol -> bool

val get_type              : symbol -> stype
val get_group             : symbol -> int
val is_input              : symbol -> bool
val is_essential_input    : symbol -> bool

(* used for flattening transform where each fun symbol *)
(* is associated with a predicate *)
(* assign_flattening  s flat *)
val assign_flattening      : symbol -> symbol -> unit
val get_flattening         : symbol -> symbol
val is_flat                : symbol -> bool
val is_defpred             : symbol -> bool

(*can raise Undef*)
val  is_skolem             : symbol -> bool
val  get_property          : symbol -> sproperty 
   
(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. symbolDB build (the same to equal and hash); 
   before that use compare_key *)  


val compare               : symbol -> symbol -> int 
val equal                 : symbol -> symbol -> bool
val compare_key           : symbol -> symbol -> int
val compare_fast_key      : symbol -> symbol -> int

(* hash is random number, small hash is number below num of symbols in db *)
(*val get_hash              : symbol -> int*)

val get_fast_key          : symbol -> int

val hash                  : symbol -> int

val is_state_type_symb     : symbol -> bool
val is_address_type_symb   : symbol -> bool
val is_bitindex_type_symb  : symbol -> bool
val is_address_const_symb  : symbol -> bool
val is_a_state_pred_symb   : symbol -> bool
val is_a_memory_pred_symb  : symbol -> bool
val is_a_bitvec_pred_symb  : symbol -> bool
val is_a_bitvec_unary_pred_symb : symbol -> bool
(*module type TMap = SMap*)

(** t is a subtype of s; currently all types are incoparable except symb_type_types being a supertype of all types *)

val is_subtype : symbol -> symbol -> bool

module Key :
  sig
    type t = symbol
    val equal : t -> t -> bool
    val hash : symbol -> int
    val compare : symbol -> symbol -> int
  end


module Map :
  sig
    type key = Key.t
    type 'a t = 'a Map.Make(Key).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end

module Hashtbl :
  sig
    type key = Key.t
    type 'a t = 'a Hashtbl.Make(Key).t
    val create : int -> 'a t
    val clear : 'a t -> unit
 (*   val reset : 'a t -> unit *)
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
(*    val stats : 'a t -> Hashtbl.statistics*)
  end



module Set :
  sig
    type elt = Key.t
    type t = Set.Make(Key).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
  end

type sym_set = Set.t

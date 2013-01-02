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
type symbol = Symbol.symbol
type var
type t=var

type bound_var = var Lib.bind

(* creates variable with symbol as type; in most cases use first_var, next_var *)
val create : symbol -> int -> var
val get_type : var -> symbol
val get_var_val : var -> int

val get_bv_type : bound_var -> symbol

(* get_first_var vtype *)
val get_first_var  : symbol -> var
val get_next_var   : var -> var

(* get_next_var(v) is greater than v *)
val compare        : var -> var -> int
val equal          : var -> var -> bool

val compare_bvar   : bound_var -> bound_var -> int
val equal_bvar     : bound_var -> bound_var -> bool
val hash           : var -> int
(* val index          : var -> int *)


val to_stream      : 'a string_stream -> var -> unit
val out            : var -> unit

val pp_var : Format.formatter -> var -> unit

val to_string      : var -> string
val to_prolog      : var -> string


(*---------------------------------*)


module VKey :
  sig
    type t = var
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
  end


module VMap :
  sig
    type key = VKey.t
    type 'a t = 'a Map.Make(VKey).t
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

module VHashtbl :
  sig
    type key = VKey.t
    type 'a t = 'a Hashtbl.Make(VKey).t
    val create : int -> 'a t
    val clear : 'a t -> unit
   (* val reset : 'a t -> unit *)
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
   (* val stats : 'a t -> Hashtbl.statistics *)
  end


module VSet :
  sig
    type elt = VKey.t
    type t = Set.Make(VKey).t
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


(* the same for bound vars *)
module BKey :
  sig
    type t = bound_var
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
  end


module BMap :
  sig
    type key = BKey.t
    type 'a t = 'a Map.Make(BKey).t
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

module BHashtbl :
  sig
    type key = BKey.t
    type 'a t = 'a Hashtbl.Make(BKey).t
    val create : int -> 'a t
    val clear : 'a t -> unit
   (* val reset : 'a t -> unit *)
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
   (* val stats : 'a t -> Hashtbl.statistics *)
  end


module BSet :
  sig
    type elt = BKey.t
    type t = Set.Make(BKey).t
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


(*--------------------------*)

(* map from types to next un-used variable of this type *)	

type fresh_vars_env

val init_fresh_vars_env : unit -> fresh_vars_env

(* creates new var of vtype in the fresh_vars_env, and declares it as used : by exteding the env with it *)	
		
val get_next_fresh_var : fresh_vars_env -> symbol -> var



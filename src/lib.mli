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


exception SZS_Unknown

val answer_mode_ref : bool ref

val iprover_start_time : float

val debug : bool

(* gets path to the iprover executable if defined by /proc/self/exe *)
(* else raises Not_found *)

val iprover_exe_name : unit -> string
val iprover_exe_path : unit -> string

(*---------------*)
exception None_opt

(* get_some get option value or raises None_opt if the option is None *)
val get_some : 'a option -> 'a
val get_some_fun : ('b -> 'a option) -> ('b -> 'a)
val is_some : 'a option -> bool

type 'a param = Def of 'a | Undef 

(* true if param is Def and false if Undef*)
val param_is_def: 'a param -> bool

exception Undef_param

(* get_param_val gets prameter value or raises Undef is the paramter is Undef *)
val get_param_val : 'a param -> 'a 
val get_param_val_fun : ('b -> 'a param) -> ('b -> 'a) 

(* elements and ref to elem of indexies and all others*)

  type 'a elem = Elem of 'a | Empty_Elem
  type 'a ref_elem = ('a elem) ref


exception Not_a_pair
val get_pair_from_list  : 'a list -> 'a * 'a
val get_pair_first : 'a * 'b -> 'a 
val get_pair_second : 'a * 'b -> 'b 


exception Not_a_triple
val get_triple_from_list  : 'a list -> 'a * 'a * 'a

val get_last_pair_from_triple_list : 'a list -> 'a * 'a

exception Empty_list
val split_list : 'a list -> 'a * ('a list) 

(* adds element to a list reference *)
val add_list_ref: 'a list ref ->  'a -> unit

(* does nothing *)
val clear_memory : unit -> unit 

val print_live_memory_usage : unit -> unit
val print_memory_usage : unit -> unit
val print_mem_time_fun : ('a->'b)-> 'a -> 'b

(*-------can be used to test memory usage running the same function n times-------*)
(*-------printing memory statistics-----------------------------------------------*)
val mem_test : (unit->unit) -> int -> unit

val string_of_char : char -> string

(* fun is a function unit -> unit, get_time_fun returns time taken by fun  *)
(* truncated by tranc digits after . *)
val get_time_fun : int -> (unit->unit)-> float

(* truncates float to n digits after . *)
val truncate_n : int -> float -> float 

(* outcome of compare fun.*)
val cequal   : int
val cgreater : int
val cless    : int

(* *)
val param_str_ref : string ref 

val pref_str      : string

(* pref string according to tptp_safe_out option*)
val s_pref_str    : unit -> string 

(* dash_str str:  ------- str ---------*)
val dash_str      : string -> string 

val add_param_str : string -> unit
val add_param_str_front : string -> unit
val param_str_new_line : unit -> unit

val compose_sign  : bool -> ('a -> 'b -> int) -> ('a -> 'b -> int)
(* hash sum where the first arg is rest and second is next number*)
val hash_sum : int -> int ->int 

(*let hash_list hash_elem list*)
val hash_list : ('a -> int) -> 'a list -> int

exception Termination_Signal

(*----------------Processes-----------------*)
(* add_child_process pid *)
val add_child_process           : int -> unit 

(* add_child_process_channels (in_channel,out_channel,error_channel) *)
val add_child_process_channels  : 
    (in_channel * out_channel * in_channel) -> unit


(* removes from the list without killing *)
val remove_top_child_process_channels : unit -> unit 

val kill_all_child_processes : unit -> unit

(*----------------End Processes-----------------*)

(* composes functions *)

val compose_12   : ('a->'b)->('c->'d ->'a) -> 'c->'d -> 'b


(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)
type 'a bind = int * 'a

val  propagate_binding_to_list :  ('a list) bind -> ('a bind) list


val apply_to_bounded : ('a -> 'b) -> 'a bind -> 'b bind

val binded_to_string  : ('a -> string) -> 'a bind ->  string

(* lexicographic comparison of pairs*)
val pair_compare_lex : ('a -> 'a -> int)-> ('b -> 'b -> int) -> 'a*'b ->'a*'b -> int

(* bool operations *)
val bool_plus : bool -> bool -> bool

(* returns 1 if true and 0 if false *)
(* in OCaml true >= false and compare true false = 1 *)
val bool_to_int : bool-> int

(*-------- folds a function over intervals -------------*)
(*  fold_up_interval f a b init_val *)
(* folds f from a to b inclusive *)
(* f rest i *)

val fold_up_interval   : ('a -> int -> 'a) -> int -> int -> 'a -> 'a
val fold_down_interval : ('a -> int -> 'a) -> int -> int -> 'a -> 'a

(*----------------lists-------------*)

(*returns a list [e;e;e;...] of legth n *)
val list_n : int -> 'a -> 'a list 

val list_skip : 'a -> 'a list -> 'a list

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)
val list_map_left : ('a -> 'b) -> 'a list -> 'b list

val list_to_string : ('a -> string) -> 'a list -> string -> string

val list_of_str_to_str : (string list) -> string -> string

val list_findf : ('a -> 'b option) -> 'a list -> 'b option

(* if tptp_safe_out_ref is true then  % is added to all out_str output *)
(* tptp_safe_out_ref by default is false reassigned by tptp_safe_out input option *)

val tptp_safe_out_ref : bool ref

val tptp_safe_str : string -> string

val out_str : string -> unit
(* out if debug is on *)
(*val out_str_debug : string -> unit*)

val out_err_str : string->unit 
(* out in stderr *)

val list_compare_lex : ('a -> 'a -> int) -> 'a list -> 'a list ->int
val lex_combination  : ('a -> 'a -> int) list -> 'a -> 'a -> int

(* in list_is_max_elem and list_get_max_elements
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
  Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s
*)    

val list_is_max_elem_v :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

val list_get_max_elements_v : ('a -> 'a -> int) -> 'a list -> 'a list

(* for usual orderings *)
val list_is_max_elem :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

(* finds max element in the list if the list is empty raises Not_found*)
val list_find_max_element : ('a -> 'a -> int) -> 'a list -> 'a

val list_find_min_element : ('a -> 'a -> int) -> 'a list -> 'a

(* as above but also filter on test *)
val list_find_max_element_p : ('a -> bool) -> ('a -> 'a -> int) -> 'a list -> 'a
val list_find_min_element_p : ('a -> bool) -> ('a -> 'a -> int) -> 'a list -> 'a

(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)

val list_remove_duplicates : ('a list) -> ('a list)

val list_find2 : ('a -> 'b -> bool) -> ('a list) -> ('b list) -> ('a *'b) 

val list_return_g_if_f2 : 
    ('a -> 'b -> bool) -> ('a -> 'b -> 'c) -> ('a list) -> ('b list) -> 'c

(* finds first el. a' b' not equal by compare_el, 
  which suppose to return ctrue if equal,
  and returns compare_el 'a 'b 
*)

val list_find_not_equal :  
    ('a -> 'b -> int) -> ('a list) -> ('b list) -> int
	
val list_find_not_identical :
    ('a list) -> ('a list) -> 'a * 'a

(* association lists *)

type ('a, 'b) ass_list = ('a*'b) list

(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f !v1 !v2))
 otherwise  appends (k1,v1) and (k2,v2)*)

val append_ass_list : 
    ('b -> 'b -> 'b) -> ('a, 'b) ass_list -> ('a, 'b) ass_list -> ('a, 'b) ass_list

type 'a num_ass_list =  ('a,int) ass_list


(*----------------------------------------------*)
(*------------- reachibility depth -------------*)
(* given a module with an elemet, and reachability relation *)
(* outputs map of rechable elements with the reachability depth *)

module type ReachRel =
  sig
    type t 
    val reach_rel : t -> t list 
    val compare : t -> t -> int
  end


module MakeReach :
  functor (ReachRel : ReachRel) ->
    sig
      type e = ReachRel.t
      module ReachMap :
          sig   
	    type key = ReachRel.t
	    type 'a t = 'a Map.Make(ReachRel).t
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
      type reach_map_el = int ReachMap.t
      val compute_reachability : ReachMap.key list -> int ReachMap.t
    end




(*----------- Output Buffers/Channels ----------------------*)

(* string stream can be e.g. a buffer or a channel *)

type 'a string_stream = 
    {
     stream : 'a;
     stream_add_char : char   -> unit;
     stream_add_str  : string -> unit;
   }

val stdout_stream : out_channel string_stream
   
(*  "list_to_stream s to_str_el l separator_str" itreates "to_str_el s el" *)
(* over all elements in l and adds sepearator str in between elem. *)

val list_to_stream : ('a string_stream) ->  
                     (('a string_stream) -> 'b -> unit) ->
		     ('b list) -> 
		      string -> 
		      unit

(* "let to_string = to_string_fun_from_to_stream_fun 30 to_stream" *)
(*    creates to_string function from to_stream function with      *)
(*    initial buffer size 30                                       *)


val to_string_fun_from_to_stream_fun :
           int -> (Buffer.t string_stream -> 'a -> 'b) -> 'a -> string
(*
val to_string_fun_from_to_stream_fun :
    int->
    ('a string_stream -> 'b -> unit) ->
    ('b -> string) 
*)

val create_buffer_stream : int -> (Buffer.t string_stream) 

val to_string_buffer_stream :  (Buffer.t string_stream) -> string




val param_to_string : ('a -> string) -> 'a param -> string

val param_to_stream : 
    ((('a string_stream) -> 'b -> unit )-> 
      ('a string_stream)  -> 'b param -> unit)


(** [formatter_of_filename a n] opens the file [n] and returns a
    formatter writing into the opened file. If [a] is true and the
    file exists it is opened for appending, otherwise it is truncated
    to zero length if it exists. Return the formatter writing to
    stdout if file name is "-".  The [Sys_error] exception is not
    caught here but passed to the calling function. *)
val formatter_of_filename : bool -> string -> Format.formatter

(** [pp_any_array pp sep ppf a] prints the elements of the array [a]
    formatted with the [pp] formatting function separated by the
    string [sep] into the formatter [ppf]. *)
val pp_any_array :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a array -> unit

(** [pp_any_list pp sep ppf l] prints the elements of the list [l]
    formatted with the [pp] formatting function separated by the
    string [sep] into the formatter [ppf]. *)
val pp_any_list :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a list -> unit

(** [pp_string_list pp sep ppf l] prints the elements of the list of
    strings [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_string_list : string -> Format.formatter -> string list -> unit

(** [pp_string_array pp sep ppf a] prints the elements of the array of
    strings [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_string_array : string -> Format.formatter -> string array -> unit

(** [pp_int_list pp sep ppf l] prints the elements of the list of
    integers [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_int_list : string -> Format.formatter -> int list -> unit

(** [pp_int_array pp sep ppf a] prints the elements of the array of
    integers [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_int_array : string -> Format.formatter -> int array -> unit

(** [pp_float_list pp sep ppf l] prints the elements of the list of
    floats [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_float_list : string -> Format.formatter -> float list -> unit

(** [pp_float_array pp sep ppf a] prints the elements of the array of
    floats [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_float_array : string -> Format.formatter -> float array -> unit

val pp_option : 
  (Format.formatter -> 'a -> unit) -> string -> Format.formatter -> 'a option -> unit

val pp_string_option : string -> Format.formatter -> string option -> unit

val string_of_string_option : string -> string option -> string


(*---------strings-----------*)

(*string filled with n spaces *)
val space_str        :  int -> string 
val space_str_sep    : char -> int -> string 


val to_stream_space : 'a string_stream -> int -> unit
val to_stream_space_sep : char -> 'a string_stream -> int -> unit


(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)
val space_padding_str :  int -> string -> string

val space_padding_str_sep : char -> int -> string -> string

(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end

(*----------------reals-----------------*)

(* decimal reals *)
type real = 
    {
     (* real_fraction Ee b*)
     mutable real_fraction    : float;
     mutable real_exponent    : int; 
   }

val real_to_string : real -> string


(*--------------Global Time Limits-------------------*)
(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)


exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)

val assign_discount_time_limit :float -> unit 
val assign_discount_start_time : unit -> unit
val unassign_discount_time_limit : unit -> unit

val check_disc_time_limit : unit -> unit

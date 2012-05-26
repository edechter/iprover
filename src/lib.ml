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

(*  question_answering_mode_ref = true if input has $answer *)





let answer_mode_ref = ref false


let iprover_start_time = Unix.gettimeofday ()

let tptp_safe_out_ref = ref false

let tptp_safe_str str = 
  if !tptp_safe_out_ref 
  then "% "^str
  else str

let out_str s = 
  if !tptp_safe_out_ref 
  then 
    print_endline ("% "^s)
  else
    print_endline s

let out_err_str s = 
   if !tptp_safe_out_ref 
  then 
   prerr_endline ("% "^s)
  else
   prerr_endline s

 
(*let out_str_debug s =
  if debug then out_str s else ()*)

(*--------------iProver version/Header--------------*)

let iprover_name_str = "iProver"

(* version is a list of integers *)
let iprover_current_version = [0;9;5]

let rec iprover_version_to_str v = 
  match v with 
  |[i] -> (string_of_int i)
  |[] -> ""
  |h::rest -> (string_of_int h)^"."^(iprover_version_to_str rest)

let iprover_version_str  = "v"^(iprover_version_to_str iprover_current_version)

(*let iprover_add_info = "(Post CASC-22)"*)
(*let iprover_add_info = "(post CASC-J5 2010)"*)

let iprover_add_info = "pre (CASC-J6 2012)"

let pref_str_head = "\n%---------------- " 

let suff_str_head = " ----------------%\n" 
    
let dash_str str = pref_str_head^str^suff_str_head

let head_str () =  
  pref_str_head
  ^iprover_name_str
  ^" "^ iprover_version_str^" "
  ^iprover_add_info
  ^suff_str_head

let _= out_str (head_str ())

(*----------------------*)
let param_str_ref = ref ""
let pref_str = "------ "

let s_pref_str () =
  if !tptp_safe_out_ref
  then ("% "^pref_str)
  else pref_str

(*--------------end iProver version/Header--------------*)

(* gets path to the iprover executable if defined by /proc/self/exe *)
(* else raises Not_found *)


let iprover_exe_name () = 
  let args = Sys.argv in
  args.(0) 
    
let iprover_exe_path () = 
  Filename.dirname (iprover_exe_name ())
    

(*
let program_path = 
  let cmd_link = "/proc/self/exe" in
  if (Sys.file_exists cmd_link) 
  then
    Filename.dirname (Unix.readlink cmd_link)
  else
    "./"
*)

(* switch on for debug mode*)
(*let debug = true*)
let debug = true

let solve_num_deb = ref 0 
let solve_pass_empty = ref 0 

let string_of_char = String.make 1

(* truncates float to n digits after . *)
let truncate_n n f = 
  let fl_n =  (10.**(float_of_int n)) in
  (float_of_int (truncate (f*.fl_n)))/.fl_n



(*---------Memory control---------*)


let mem_control_init () =
  let old_controls = Gc.get () in
  let new_controls = { old_controls with
    Gc.minor_heap_size = 4 * 1024 * 1024 * 8 / Sys.word_size; (* 4MB *)
    Gc.major_heap_increment = 8 * 1024 * 1024 * 8 / Sys.word_size; (* 8MB *)
  (*  Gc.max_overhead = 1000;*)
(*    Gc.space_overhead = 400;*)

  } in
  Gc.set new_controls   


(*
let mem_control_init () = 
  let old_controls = Gc.get () in
  let new_controls = {old_controls with Gc.major_heap_increment= 1048576} in
  Gc.set new_controls
*)

let _ =  mem_control_init ()

let clear_memory () = ()


(* first mbytes second kbites *)
type mem_size = int * int 

(* get mem in bytes *)
let get_mem_bytes () =
  let stat = Gc.stat () and control = Gc.get () in
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  let bytes = (max_words_total * ( Sys.word_size / 8) ) in
  bytes

let get_live_mem_bytes () =
  let stat = Gc.stat () and control = Gc.get () in
  let max_words_total = stat.Gc.live_words + control.Gc.minor_heap_size in
  let bytes = (max_words_total * ( Sys.word_size / 8) ) in
  bytes

let bytes_to_mem_size bytes = 
  let kbytes = (bytes / 1024) in
  let mbytes = (kbytes / 1024) in
  (mbytes, (kbytes - mbytes * 1024))

let print_memory_usage () =
  let (mbytes,kbytes) = bytes_to_mem_size (get_mem_bytes ()) in
  Printf.fprintf stderr "Allocated memory:\t%d Mbytes %d kBytes\n"
    mbytes kbytes;
  flush stderr

let print_live_memory_usage () =
   let (mbytes,kbytes) = bytes_to_mem_size (get_live_mem_bytes ()) in
   Printf.fprintf stderr "Allocated live memory:\t%d Mbytes %d kBytes\n"
    mbytes kbytes;
   flush stderr

(* 
let print_memory_usage () =
 let stat = Gc.stat () and control = Gc.get () in
 (* out_str ("space_overhead="^(string_of_int control.Gc.space_overhead)^"\n");*)
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  let bytes = (max_words_total * ( Sys.word_size / 8) ) in
  let kbytes = (bytes / 1024) in
  let mbytes = (kbytes / 1024) in
  Printf.fprintf stderr "Allocated memory:\t%d Mbytes %d kBytes\n"
    mbytes (kbytes - mbytes * 1024);
  flush stderr
*)


(* fun is a function unit -> unit, get_time_fun returns time taken by fun  *)
(* truncated by tranc digits after . *)
let get_time_fun trunc f  =
  let start_time = Unix.gettimeofday () in
  f ();
  let end_time   = Unix.gettimeofday () in 
  truncate_n trunc (end_time -. start_time)

let get_time_arg_res_fun trunc f a =
  let start_time = Unix.gettimeofday () in
  let res = f a in
  let end_time   = Unix.gettimeofday () in 
  let time = truncate_n trunc (end_time -. start_time) in
  (res,time)


(* Gc.full full_major is applied, can be time consuming *)
(* *)
let print_mem_time_fun f a = 
  Gc.full_major ();
  let before_bytes = get_mem_bytes () in
  let (res,time) = get_time_arg_res_fun 3 f a in
  Gc.full_major ();
  let after_bytes = get_mem_bytes () in
  let diff_bytes = after_bytes - before_bytes in
  let (before_mbytes,before_kbytes) = bytes_to_mem_size before_bytes in
  let (after_mbytes,after_kbytes) = bytes_to_mem_size after_bytes in
  let (diff_mbytes,diff_kbytes) = bytes_to_mem_size diff_bytes in
  out_str (s_pref_str ());
  out_str 
    ("Mem before: "
      ^(string_of_int before_mbytes)
     ^ " Mbytes "
     ^(string_of_int before_kbytes) 
     ^" kBytes\n"
     ^"Mem after: "
     ^(string_of_int after_mbytes)
     ^ " Mbytes "
     ^(string_of_int after_kbytes) 
     ^" kBytes\n"
     ^"Mem incr: "	 
     ^(string_of_int diff_mbytes)
     ^ " Mbytes "
     ^(string_of_int diff_kbytes) 
     ^" kBytes\n");
  out_str ("Used Time: "^(string_of_float time));
  res


(*-------can be used to test memory usage running the same function n times-------*)
(*-------printing memory statistics-----------------------------------------------*)

let mem_test fun_to_test n = 
  ( for i=1 to n
  do 
(*      Gc.full_major ();
      print_live_memory_usage (); 
      print_memory_usage ();*)

    ignore (print_mem_time_fun fun_to_test ()) 
  done
   );
  


(*-------------------------*)

exception Termination_Signal




(*----------Global Open Child Processes--------------*)

let child_processes_list_ref = ref []



(* processed opend by Unix.open_process_full, are closed by channels *)
(* (in_channel,out_channel,error_channel) list *)

let child_channels_list_ref = ref []

let add_child_process pid = 
  child_processes_list_ref:= pid::!child_processes_list_ref

let add_child_process_channels chs = 
  child_channels_list_ref:= chs::!child_channels_list_ref

let kill_child_process_channels chs = 
  ignore (Unix.close_process_full chs)

let kill_process_group pid = 
  try                         
    (* Kill processes in process group *)
    Unix.kill (-pid) Sys.sigkill;                             
    ignore(Unix.waitpid [] pid)
  with 
    Unix.Unix_error(Unix.ESRCH, _, _) -> ()

let remove_top_child_process () = 
  match !child_processes_list_ref with 
  |[] -> ()
  |h::tl ->
      kill_process_group h;
      child_processes_list_ref:= tl

let remove_top_child_process_channels () = 
  match !child_channels_list_ref with 
  |[] -> ()
  |h::tl ->      
      child_channels_list_ref:= tl


let kill_all_child_processes () = 
  List.iter kill_process_group !child_processes_list_ref;
  List.iter kill_child_process_channels !child_channels_list_ref

(*--------------------*)

let get_some = function 
  |None -> failwith "get_some: None"
  |Some x -> x

type 'a param = Def of 'a | Undef 


(* outcome of  compare fun *)
let cequal   =  0
let cgreater =  1
let cless    = -1

let compose_12 g f x y = g (f x y)



(* elements and ref to elem of indexies and all others*)

let () =  Random.init(13)

(*hash function called djb2*)

let hash_sum rest num = 
  ((rest lsl 5) + rest) + num (* hash * 33 + num *)

type 'a elem = Elem of 'a | Empty_Elem
type 'a ref_elem = ('a elem) ref

exception Empty_list
let split_list l =
  match l with 
  |h::tl -> (h,tl)
  |[] -> raise Empty_list


let add_param_str str = 
  param_str_ref := (!param_str_ref)^pref_str^str^"\n"

let add_param_str_front str = 
   param_str_ref := pref_str^str^"\n"^(!param_str_ref)

let param_str_new_line () = 
   param_str_ref := (!param_str_ref)^"\n"


(*compose sign with function*)

let compose_sign sign f = 
  if sign then f 
  else compose_12 (~-) f

exception Not_a_pair
let get_pair_from_list  = function
  |[a1;a2] -> (a1,a2)
  |_-> raise Not_a_pair

exception Not_a_triple
let get_triple_from_list = function 
  |[a1;a2;a3] -> (a1,a2,a3)
  |_-> raise Not_a_triple

let get_last_pair_from_triple_list  = function
  |[_;a1;a2] -> (a1,a2)
  |_-> raise Not_a_triple




(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)

type 'a bind = int * 'a

let propagate_binding_to_list blist =
  let (b_l,list) = blist in  
  List.map (fun el -> (b_l,el)) list

(* bool operations *)
let bool_plus x y = ((x&& (not y)) || ((not x)&& y))
(*    let out_str s = Printf.fprintf stdout " %s \n" s *)

    
(*let out_str_a s = Printf.fprintf stdout " %s \n" s *)

(* lexicographic comparison on pairs*)

let pair_compare_lex comp1 comp2 (x1,x2) (y1,y2) = 
  let res_comp1 = comp1 x1 y1 in
  if res_comp1=cequal then 
    let res_comp2 = comp2 x2 y2 in
      if res_comp2 = cequal then 
	cequal
      else res_comp2
  else res_comp1

(* lex combination of all compare functions in compare_fun_list*)
let rec lex_combination compare_fun_list x1 x2 = 
  match compare_fun_list with 
  | h::tl -> 
      let res = h x1 x2 in 
      if res = cequal then lex_combination tl x1 x2
      else res
  |[] -> cequal 
       



(* bound lists*)

type 'a bound_list = ('a list) bind

(*
let rec bound_list_fold_left f a (bound_list : bound_list) = 
 
 *)

(*-------- folds a function over intervals -------------*)
(* folds from a to b inclusive *)
(* f rest i *)

let fold_up_interval f a b init_val = 
  let rec g rest i = 
    if i > b 
    then 
      rest 
    else 
      let new_rest = f rest i in 
      g new_rest (i+1)
  in
  g init_val a

let fold_down_interval f a b init_val = 
  let rec g rest i = 
    if i < a 
    then 
      rest 
    else 
      let new_rest = f rest i in 
      g new_rest (i-1)
  in
  g init_val b
    



(*------------------- Lists----------------------*)

(*returns a list [e;e;e;...] of legth n *)
let list_n n e = 
  let rec list_n' rest i = 
    if i<1 then rest 
    else list_n' (e::rest) (i-1) 
  in 
  list_n' [] n

(* returns list which starts with the next elem *)
(* assume that elem in l *)
(* careful if there are duplicates*)

let rec list_skip elem l = 
  match l with 
  | h::tl -> 
      if (h==elem) then tl 
      else  list_skip elem tl	
  | [] -> failwith "Lib list_skip: elem should be in l"

  

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)

let rec list_map_left f l  = 
  match l with    
  | h::tl -> let new_h = f h in 
    new_h :: (list_map_left f tl)
  | [] -> []
	


(* stops when f is Some(e) and returns Some(e) otherwise returns None  *)
let rec list_findf f = function 
  |h::tl -> 
      (match (f h) with 
      |Some(e)-> Some(e)
      |None -> list_findf f tl
      )
  |[] -> None



let rec list_compare_lex compare_el l1 l2 =
  match (l1,l2) with
  |((h1::tl1),(h2::tl2)) -> 
      let cmp = compare_el h1 h2 in   
      if (cmp = cequal) then
	list_compare_lex compare_el tl1 tl2
      else cmp 
 |((h::_),[]) -> cequal + 1
 |([],(h::_)) -> cequal -1
 |([],[]) -> cequal


(* in list_get_max_elements_v 
   is mainly for non-ground (not exactly) orderings
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
   Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s*)    

let rec list_is_max_elem_v compare elem list = 
  match list with 
  |h::tl -> 
(*      if ((not (h == elem)) & ((compare h elem) >= 0))       
      then false 
      else (list_is_max_elem_v compare elem tl) 
*)
      if (h == elem) || not ((compare h elem) > 0) 
      then (list_is_max_elem_v compare elem tl)
      else false  
  |[] -> true

let list_get_max_elements_v compare list = 
  let f rest elem = 
    if  list_is_max_elem_v compare elem list
    then elem::rest
    else rest 
  in List.fold_left f [] list

(* for usual orderings *)
let rec list_is_max_elem compare elem list = 
  match list with 
  |h::tl -> 
      if (compare h elem) > 0
      then false 
      else (list_is_max_elem compare elem tl)
  |[] -> true

(*
let rec list_find_max_element compare list =
  match list with 
  |h::tl -> 
      if tl = [] 
      then h
      else
	let max_rest = list_find_max_element compare tl in
	if (compare max_rest h) > 0 
	then max_rest
	else h
  |[] -> raise Not_found
*)

let list_find_max_element compare list =
  let rec f max_el rest =     
    match rest with 
    |h::tl -> 
	if ((compare h max_el)>0) then 
	  f h tl 
	else 
	  f max_el tl 
    |[] -> max_el
  in
  match list with 
  |h::tl -> f h tl 
  |[] -> raise Not_found

let list_find_min_element compare list = 
  list_find_max_element (fun a b -> compare b a) list

let rec list_find_max_element_p test cmp list =
  match list with 
  |h::tl -> 
      if (test h) 
      then
	(if tl = [] 
	then h
	else
	  (try 
	    let max_rest = list_find_max_element_p test cmp tl in
	    if (cmp h max_rest) > 0 
	    then h 
	    else max_rest
	  with Not_found -> h	 
	  )
	)    
      else list_find_max_element_p test cmp tl
  |[] -> raise Not_found

let list_find_min_element_p test cmp list =
  list_find_max_element_p test (fun a b -> cmp b a) list

(*---------------removes duplicate elements from the list-----------------*)

let rec list_remove_duplicates' rest list =
  match list with 
  |h::tl -> 
      if (List.memq h rest) then 
	list_remove_duplicates' rest tl
      else 
	list_remove_duplicates' (h::rest) tl
  |[] -> rest

let list_remove_duplicates list = 
  List.rev (list_remove_duplicates' [] list) 


(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)

let rec list_remove_duplicates_ordered list = 
  match list with 
  |h1::h2::tl -> 
      if h1==h2 
      then list_remove_duplicates_ordered (h2::tl) 
      else (h1::(list_remove_duplicates (h2::tl)))
  |[h] -> [h]
  |[]   -> []


(* like List.find but for two lists in parallel*)

let rec list_find2 f l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then (h1,h2) 
      else list_find2 f tl1 tl2
  |_ -> raise Not_found

(* like list_find2 only returns (g h1 h2)  *) 

let rec list_return_g_if_f2 f g l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then g h1 h2 
      else list_return_g_if_f2 f g tl1 tl2
  |_ -> raise Not_found

(* *)
let rec list_find_not_equal compare_el l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      let c = compare_el h1 h2 in 
      if  c<>cequal then c 
      else list_find_not_equal compare_el tl1 tl2
  |_ -> raise Not_found


let rec list_find_not_identical l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      if  not (h1==h2) then (h1,h2) 
      else list_find_not_identical tl1 tl2
  |_ -> raise Not_found




(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f v1 v2))
 otherwise  appends (k1,v1) and (k2,v2)*)


let rec append_ass_list f ass_list_1 ass_list_2  = 
  match ass_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 ass_list_2 in 
       let new_list_2 = 
           (k1,(f v1 v2))::(List.remove_assoc k1 ass_list_2) in   
       append_ass_list f tl1 new_list_2  
     with
       Not_found -> append_ass_list f tl1 ((k1,v1)::ass_list_2)
     )
  |[] -> ass_list_2

(* number association lists *)

type ('a, 'b) ass_list = ('a*'b) list

type 'a num_ass_list =  ('a, int) ass_list




(* dangerous: old lists are changing...
 association lists on ref's

type 'a 'b ass_list = ('a*('b ref)) list

let rec append_ass_list f ass_list_1 ass_list_2  = 
  match n_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 n_list_2 in 
       v2 := f !v1 !v2 ;
       append_ass_list f tl1 ass_list_2  
     with
       Not_found -> (k1,v1)::n_list_2
     )
  |[] -> ass_list_2

*)

(*------------- reachibility depth ----------*)
(* given a module with an elemet, and reachability relation *)
(* outputs map of rechable elements with the reachability depth *)

module type ReachRel =
  sig
    type t 
    val reach_rel : t -> t list 
    val compare : t -> t -> int
  end

module MakeReach (ReachRel:ReachRel) = 
  struct
    type e = ReachRel.t
    module ReachMap = Map.Make(ReachRel) 
    type reach_map_el = (int ReachMap.t)

	  (* returns a map of el-> int_ref where int is the reachability depth *)
    let rec comp_reach_rec current_map current_depth el_list = 
      if (el_list = [])
      then 
	current_map
      else
	let f (reach_map, el_list) el =
	  if (ReachMap.mem el reach_map)
	  then 
	    (reach_map, el_list) 
	  else 
	    let new_map = (ReachMap.add el current_depth reach_map) in
	    let new_el_list = (ReachRel.reach_rel el)@el_list in
	    (new_map,new_el_list) 
	in 
	let (new_map,new_el_list) = 
	  List.fold_left f (current_map,[]) el_list in  
	let new_depth = current_depth+1 in
	comp_reach_rec new_map new_depth new_el_list  

    let	compute_reachability depth_0_list =
      let depth = 0 in 
      let (map : reach_map_el) = ReachMap.empty in
      comp_reach_rec map depth depth_0_list
  end




(*----------- Output Buffers/Channels ----------------------*)

(* string stream can be e.g. a buffer or a channel *)
(* all output should be via streams (for efficiency reasons) *)
(* if strings are needed then to_string       *)
(* should be called only at the most top level *)

type 'a string_stream = 
    {
     stream : 'a;
     stream_add_char : char   -> unit;
     stream_add_str  : string -> unit;
   }
   
let create_buffer_stream size = 
  let b = Buffer.create size in
  let s = {stream = b;
	   stream_add_char = Buffer.add_char b;
	   stream_add_str  = Buffer.add_string b}   
  in
  s


let to_string_buffer_stream s = 
  Buffer.contents s.stream  

let stdout_stream = 
 {stream = stdout;
  stream_add_char = print_char;
  stream_add_str  = print_string}   

(* "let to_string = to_string_fun_from_to_stream_fun 30 to_stream" *)
(*    creates to_string function from to_stream function with      *)
(*    initial buffer size 30                                       *)

let to_string_fun_from_to_stream_fun init_buff_size to_stream = 
  let out_fun a =
    let s = create_buffer_stream init_buff_size in    
    to_stream s a;
    to_string_buffer_stream s
  in
  out_fun
  

let rec list_to_stream s to_str_el l separator_str = 
  match l with
    []-> ()
  | h::[] -> to_str_el s h
  | h::rest -> 
      (to_str_el s h);
      s.stream_add_str separator_str;
      (list_to_stream s to_str_el rest separator_str)


(* Opens a file [filename] and return a formatter writing into the
   opened file. If [append] is true and the file exists it is opened
   for appending, otherwise it is truncated to zero length if it
   exists. Return the formatter writing to stdout if [filename] is
   "-".  The [Sys_error] exception is not caught here but passed to
   the calling function. *)
let formatter_of_filename append filename =

  (* Output to stdout? *)
  if filename = "-" then 

    (* Use formatter for stdout *)
    Format.std_formatter

  else

    (* Opening mode for file *)
    let open_flags = 

      (* Append to file only? *)
      if append then 

	(* Append to file, create if not existing and use text mode *)
	[Open_append; Open_creat; Open_text]

      else
	
	(* Write to file, create if not existing, truncate if existing
	   and use text mode, this is the default from open_out in
	   OCaml's pervasives.ml *)
	[Open_wronly; Open_creat; Open_trunc; Open_text]

    in

    (* Permissions if file is created, this is the default from
       open_out in OCaml's pervasives.ml *)
    let open_perm =  0o666 in
    
    (* Open file for writing or appending *)
    let formatter_channel = 
      Pervasives.open_out_gen open_flags open_perm filename 
    in
      
    (* Return formatter writing to file *)
    Format.formatter_of_out_channel formatter_channel


(* Print an array of any type with separator from an index on *)
let rec pp_any_array' pp_a sep ppf array = function
  | i when i > Array.length array -> ()
  | i when i < 0 -> ()
  | i when i = Array.length array - 1 -> 
      Format.fprintf ppf "%a" pp_a array.(i)
  | i -> 
    Format.fprintf ppf "%a%s" pp_a array.(i) sep; 
    pp_any_array' pp_a sep ppf array (succ i)

(* Print an array of any type with separator *)
let pp_any_array pp_a sep ppf array = 
  pp_any_array' pp_a sep ppf array 0


(* Print a list of any type with separator *)
let rec pp_any_list pp_a sep ppf = function
  | [] -> 
      ()
  | [a] -> 
      Format.fprintf ppf "%a" pp_a a
  | a::tl -> 
      Format.fprintf ppf "%a%s" pp_a a sep; pp_any_list pp_a sep ppf tl


(* Print a list of strings with separator *)
let pp_string_list = pp_any_list Format.pp_print_string


(* Print a list of strings with separator *)
let pp_string_array sep array = pp_any_array Format.pp_print_string sep array


(* Print a list of strings with separator *)
let pp_int_list = pp_any_list Format.pp_print_int


(* Print an array of strings with separator *)
let pp_int_array sep array = pp_any_array Format.pp_print_int sep array


(* Print a list of floats with separator *)
let pp_float_list = pp_any_list Format.pp_print_float


(* Print an array of floats with separator *)
let pp_float_array sep array = pp_any_array Format.pp_print_float sep array


(* Print an 'a option value *)
let pp_option pp none_str ppf = function
  | None -> Format.fprintf ppf "%s" none_str
  | Some s -> Format.fprintf ppf "%a" pp s


(* Print a string option value *)
let pp_string_option none_str ppf str = 
  pp_option Format.pp_print_string none_str ppf str


(* Return a string of a string option value *)
let string_of_string_option none_str str =
  ignore (Format.flush_str_formatter ());
  Format.fprintf Format.str_formatter "%a" (pp_string_option none_str) str;
  Format.flush_str_formatter ()


(* Examples a bit old: *)

(*

1)

  let b = Buffer.create 10000 in
  let s = {stream = b;
	   stream_add_char = Buffer.add_char b;
	   stream_add_str  = Buffer.add_string b}   

(* strings, chars are added at the end*)
s.add_str "first line\n"; 
s.add_str "second line\n";

2) (*        stdout          *)

  let out_model model = 
  let s = 
    {stream = stdin;
     stream_add_char = print_char ;
     stream_add_str  = print_string}   
  in
  model_to_stream s model

3)

 let s =  {stream = out_channel;
           stream_add_char = output_char out_channel;
           stream_add_str  = output_string out_channel;
           } in
 bench_to_buffer s formula; 
 flush out_channel

-----------------
(*if string is needed then *)
let b_string =  (Buffer.contents b)

(* if out buffer to channel then *)
let fun_out out_ch = Buffer.output_buffer out_ch b in

*)



let param_to_string el_to_string elp = 
  match elp with 
  |Def(el) -> el_to_string el 
  |Undef   -> "Undef"


let param_to_stream el_to_stream s elp = 
  match elp with 
  |Def(el) -> el_to_stream s el 
  |Undef   -> s.stream_add_str "Undef"

(*---------strings-----------*)

(*string filled with n spaces *)
let space_str n = 
  if n>0 
  then
    (String.make n ' ')
  else " "

let to_stream_space s n = 
  for j=1 to n
  do 
    s.stream_add_char ' '
  done


(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)

let space_padding_str distance str =
  let name_ln = String.length str in
  str^(space_str (distance - name_ln))

let rec list_to_string to_str_el l separator_str =
  match l with
    []->""
  | h::[] -> to_str_el h
  | h::rest -> 
      (to_str_el h)^separator_str^(list_to_string to_str_el rest separator_str)

let list_of_str_to_str str_list separator_str = 
    list_to_string (fun x->x) str_list separator_str


(*----------------reals----------*)

(* decimal reals *)
type real = 
    {
     (* real_fraction Ee b*)
     mutable real_fraction    : float;
     mutable real_exponent    : int; 
   }

let real_to_string r = 
  (string_of_float r.real_fraction)
  ^"Ee"^(string_of_int r.real_exponent)


(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end



(*--------------Global Time Limits-------------------*)

(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)

exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)
let discount_time_limit  = ref Undef
let start_discount_time  = ref Undef

let assign_discount_time_limit (x:float) =   discount_time_limit := Def(x)
let assign_discount_start_time () = 
  start_discount_time := Def((Unix.gettimeofday ()))

let get_start_disc_time () = 
  match !start_discount_time with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: start_time is Undef"

let get_disc_time_limit () = 
  match !discount_time_limit with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: discount_time_limit is Undef"

let check_disc_time_limit () = 
  match !discount_time_limit with
  | Def(t_limit) -> 
      if ((Unix.gettimeofday ()) -. (get_start_disc_time ())) > t_limit 
      then raise Timeout
      else ()
  |Undef -> ()

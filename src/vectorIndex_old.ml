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

exception VecIndex_add_leaf_extension
exception VecIndex_add_short_kyelist
exception VecIndex_add_emptylist_to_emptyindex
exception VecIndex_remove_path_too_long
exception VecIndex_remove_path_too_short
exception VecIndex_remove_remove_from_emptyindex


module type Key =
  sig
    type t
    val compare : t -> t -> int
  end

module type Index = 
  sig
    type key
    type keylist = key list
    type 'a index
    val create : unit  -> 'a index
(* copied from trie_func *) 
    val mem    : keylist -> 'a index -> bool
    val add    : keylist -> ('a index) ref-> 'a ref_elem
    val remove : keylist -> ('a index) ref -> unit

(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)
    val  find : keylist ->'a index -> 'a ref_elem
(* new for feature indexes*)
    val findf_leq : ('a -> 'b option) -> keylist -> ('a index) ref -> 'b option
    val findf_geq : ('a -> 'b option) -> keylist -> ('a index) ref -> 'b option

    val findf_all_geq :  
	('a ref_elem -> 'b list) -> keylist -> ('a index) ref -> 'b list 
    val findf_all_leq :  
	('a ref_elem -> 'b list) -> keylist -> ('a index) ref -> 'b list 
   end

module Make(Key:Key)  =
  struct
    module KeyDB = Tree.Make (Key)
    type key     = Key.t
    type keylist = key list
    type 'a index =
        Node of ((('a index) ref)  KeyDB.tree)
      | Leaf of 'a ref_elem
      | Empty

    let create () = Empty

(* partial list return false: ab in abcd *)

    let rec mem keylist index = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match index with 
	    |Node(keydb) ->
        	( try mem tl !(KeyDB.find key keydb) with 
		  Not_found -> false
		 ) 
	    | Leaf(_)  -> false
	    | Empty -> false 
	   )
      |[] ->
	  ( 
	    match index with 
	    |Node(_) -> false
	    |Leaf(_) -> true
	    |Empty   -> true
	   ) 
 
(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)

let rec find keylist index =
      match keylist with
      |key::tl ->
          (
            match index with
            |Node(keydb) ->
                 find tl !(KeyDB.find key keydb)
            | Leaf(_)    -> raise Not_found
            | Empty -> raise Not_found
           )
      |[] ->
          (
            match index with
            |Leaf(elem)  -> elem
            |Node(_)     -> raise Not_found
            |Empty  -> raise Not_found
           )


    let rec create_from_keys keylist = 
      match keylist with 
      |key::tl  -> 	   
	  let (rest_index,ref_leaf) = create_from_keys tl in
          let new_kdb = KeyDB.add  key (ref rest_index) (KeyDB.create ()) in
	  (Node(new_kdb),ref_leaf)
      |[] -> let ref_leaf = ref Empty_Elem in
	(Leaf(ref_leaf),ref_leaf)
	  
	    
    let rec add keylist ref_index =
      match keylist with 
      |key::tl -> 
	  ( 
	    match !ref_index with 
	    |Node(keydb) ->
		(try 
		  let n_index = (KeyDB.find key keydb) in  
		  add tl n_index 
		with 		  
		  Not_found -> 
		    let (new_index,ref_leaf)= create_from_keys tl in
		    ref_index := 
		      Node((KeyDB.add key (ref new_index) keydb));
		    ref_leaf
		)
	    | Leaf(_)  -> raise VecIndex_add_leaf_extension
	    | Empty  -> 
		let (new_index,ref_leaf) = create_from_keys keylist in
                let ()= (ref_index := new_index)  in
		ref_leaf
	   )
      |[] ->
	  ( 
	    match !ref_index with 
	    |Node(_) -> raise VecIndex_add_short_kyelist
	    |Leaf(ref_leaf) -> ref_leaf
	    |Empty   -> raise VecIndex_add_emptylist_to_emptyindex
	   ) 
	

    let rec remove keylist ref_index = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match !ref_index with 
	    |Node(keydb) -> 
		remove tl (KeyDB.find key keydb);  	  
                if !(KeyDB.find key keydb)= Empty 
                then 
		  (
		   let new_keydb = KeyDB.remove key keydb in
		   if (KeyDB.is_empty new_keydb) 
		   then ref_index := Empty
		   else ref_index := Node(new_keydb)
		  )
	    | Leaf(_)  -> raise VecIndex_remove_path_too_long
	    | Empty -> raise VecIndex_remove_path_too_long
	   )
      |[] ->    
	  (
	   match !ref_index with 
	   |Node(_) -> raise VecIndex_remove_path_too_short
	   |Leaf(_) -> (ref_index := Empty)
	   |Empty   -> raise VecIndex_remove_remove_from_emptyindex
	  ) 

(* new *)
exception VecIndex_findf_leq_keylist_too_long
exception VecIndex_findf_leq_keylist_too_short

    let rec findf_leq f keylist ref_index =
	match keylist with 
	| key::tl -> 
	    (match !ref_index with 
	    |Node(keydb) -> 
  		(KeyDB.findf_leq (findf_leq f tl) key keydb)
	    |Leaf(_)-> raise VecIndex_findf_leq_keylist_too_long
	    |Empty -> None
	    )	    
	|[] ->
	    (match !ref_index with 
	    |Leaf(elem_ref) -> 
		(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> None
		)
	    |Node(_) -> raise VecIndex_findf_leq_keylist_too_short
	    |Empty -> None
	    )

exception VecIndex_findf_geq_keylist_too_long
exception VecIndex_findf_geq_keylist_too_short

    let rec findf_geq f keylist ref_index =
	match keylist with 
	| key::tl -> 
	    (match !ref_index with 
	    |Node(keydb) -> 
  		(KeyDB.findf_geq (findf_geq f tl) key keydb)
	    |Leaf(_)-> raise VecIndex_findf_geq_keylist_too_long
	    |Empty -> None
	    )	    
	|[] ->
	    (match !ref_index with 
	    |Leaf(elem_ref) -> 
		(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> None
		)
	    |Node(_) -> raise VecIndex_findf_geq_keylist_too_short
	    |Empty -> None
	    )

exception VecIndex_findf_all_geq_keylist_too_long
exception VecIndex_findf_all_geq_keylist_too_short
	      

    let rec findf_all_geq f keylist ref_index =
      match keylist with 
      | key::tl -> 
	  (match !ref_index with 
	  |Node(keydb) -> 
  	      (KeyDB.findf_all_geq (findf_all_geq f tl) key keydb)
	  |Leaf(_)-> raise VecIndex_findf_all_geq_keylist_too_long
	  |Empty -> []
	  )	    
      |[] ->
	  (match !ref_index with 
	    |Leaf(elem_ref) ->  f elem_ref
	       (*(match !elem_ref with 
		 |Elem(elem) -> f elem
		|Empty_Elem -> []
		) *)
	    |Node(_) -> raise VecIndex_findf_all_geq_keylist_too_short
	    |Empty -> []
	  )
	    
exception VecIndex_findf_all_leq_keylist_too_long
exception VecIndex_findf_all_leq_keylist_too_short
	      

    let rec findf_all_leq f keylist ref_index =
      match keylist with 
      | key::tl -> 
	  (match !ref_index with 
	  |Node(keydb) -> 
  	      (KeyDB.findf_all_leq (findf_all_leq f tl) key keydb)
	  |Leaf(_)-> raise VecIndex_findf_all_leq_keylist_too_long
	    |Empty -> []
	  )	    
      |[] ->
	  (match !ref_index with 
	    |Leaf(elem_ref) -> f elem_ref
		(*(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> []
		)*)
	    |Node(_) -> raise VecIndex_findf_all_leq_keylist_too_short
	    |Empty -> []
	  )
	    

  end

    

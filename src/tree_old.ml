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






exception Tree_add_already_in


module type Key =
  sig
    type t
    val compare : t -> t -> int
  end


      
module type Tree =
  sig
    type key
    type 'a tree  
    val create : unit  -> 'a tree
    val is_empty : 'a tree -> bool
    val find : key -> 'a tree -> 'a
    val mem  : key -> 'a tree -> bool
    val add  : key -> 'a -> 'a tree -> 'a tree
    val remove :  key -> 'a tree -> 'a tree
    val findf_leq : ('a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_geq : ('a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_all_geq :  ('a -> 'b list) -> key -> 'a tree -> 'b list 
    val findf_all_leq :  ('a -> 'b list) -> key -> 'a tree -> 'b list 
  end

module Make(Key:Key)  =
  struct
    type key = Key.t

 (*inv: keys of right (left) subtree 
    are greater (smaller) than node key *)

    type 'a tree = 
      |Node of key * 'a * 'a tree * 'a tree   
      |Empty
 
    let create () = Empty
    let is_empty tree = (tree = Empty)

    let rec mem key = function
      |Node(ck, elem, lt, rt) -> 
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then  mem key rt 
	  else	 
	    if cmp < 0
	    then  mem key lt
	    else
	      true
      |Empty -> false 
	    
    let	rec find key = function
      |Node(ck, elem, lt, rt) -> 
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then find key rt 
	  else	 
	    if cmp < 0
	    then find key lt
	    else
	      elem
		
      |Empty -> raise Not_found

	    
    let rec add key elem = function
      |Node(ck,celem, lt, rt) -> 	
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then Node(ck,celem,lt,(add key elem rt)) 
	  else	 
	    if cmp < 0
	    then Node(ck,celem,(add key elem lt),rt)
	    else
	      raise Tree_add_already_in
		
      |Empty -> Node(key,elem,Empty,Empty)

(*  transforms tree such that the maximal key is at the top
    inv: right subtree of the result is always Empty 
   (used for removal) *)
	    
    let rec pop_max_top = function
      |Node(ck, celem, clt, crt) as tree -> 
	  if crt = Empty then 
	    tree 
	 else
	    let poped = pop_max_top crt in
	    (match poped with
	    |Node(pck, pelem, plt, _) ->
		Node(pck,pelem,Node(ck,celem,clt,plt),Empty)
	    |_->failwith "tree pop_max_top: should happen"	     
	    )
      |Empty -> Empty
	    

    let rec remove key = function
      |Node(ck,celem, clt, crt) -> 	
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then Node(ck,celem, clt,(remove key crt)) 
	  else	 
	    if cmp < 0
	    then Node(ck,celem,(remove key clt),crt)
	    else (*cmp = 0 *)
              if clt = Empty 
	      then crt
	      else
		(match (pop_max_top clt) with
		|Node(pck, pelem,plt,_) ->
                 Node(pck,pelem,plt,crt)
		|_-> failwith "tree remove: should not happen"  
		)
      |Empty -> Empty


(* traverses tree until f returns Some(v) and returne Some(v) else return None*)

    let rec findf f = function 
      |Node(ck,celem, clt, crt) -> 	
          (match (f celem) with 
	  |Some(v) -> Some(v)
	  |None -> 
	     ( match (findf f clt) with 
	      |Some(v) -> Some(v)
	      |None ->
		 (match (findf f crt) with 
		  |Some(v) -> Some(v)
		  |None -> None
		 )
	      )
	  )
      |Empty -> None


(* findf_leq applies f to elements with key less or equal to key 
   and stops if f returns Some(v) and returns Some(v) otherwise
   reterns None; used in vector index for subsumption *)

    let rec findf_leq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp >= 0
	  then 
	    match (findf f clt) with 
	    |Some(v) -> Some(v)
	    |None -> 
		(match (f celem) with
		|Some(v) -> Some(v)
		|None -> findf_leq f key crt
		)
	  else (*cmp < 0*)
            (findf_leq f key clt)
      |Empty -> None

(* as above but for greater or equal *)

    let rec findf_geq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp <= 0
	  then 
	    match (findf f crt) with 
	    |Some(v) -> Some(v)
	    |None -> 
		(match (f celem) with
		|Some(v) -> Some(v)
		|None -> findf_geq f key clt
		)
	  else (*cmp > 0*)
            (findf_geq f key crt)
      |Empty -> None

(* returns list of all elem's v obtained by applyng f to all elements *)	    

    let rec findf_all f = function 
      |Node(ck, celem, clt, crt) -> 	
	  (f celem)@(findf_all f clt)@(findf_all f crt)
      |Empty -> []
	    
(* findf_all_leq returns list of all elements with key less or eqaul to key
and [] if all f return None
*)
    let rec findf_all_leq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp >= 0
	  then 
	    (f celem)@(findf_all f clt)@(findf_all_leq f key crt)
	  else 
	    findf_all_leq f key clt
      |Empty -> []
	    
(* as above but for greater or equal *)
	    
    let rec findf_all_geq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp <= 0
	  then 
	    (f celem)@(findf_all f crt)@(findf_all_geq f key clt)
	  else 
	    findf_all_geq f key crt
      |Empty -> []
	   	    
  end


       
(* debug 

module IKey =
  struct
    type t = int
    let compare = compare
  end

module ITree = Make (IKey)

let tree1 = ITree.create ()
let tree2 = ITree.add 5 5 tree1
let tree3 = ITree.add 4 4 tree2
let tree4 = ITree.add 7 7 tree3
let tree5 = ITree.add 20 20 tree4
let tree6 = ITree.add 10 10 tree5
let tree7 =  ITree.add 15 15 tree6

let tree8 =  ITree.add 22 22 tree7

let f x = 
  if x >= 7 
  then Some(x) else None
*)

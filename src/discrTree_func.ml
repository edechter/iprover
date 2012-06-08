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






(* discrimination tree *)

open Lib

type term   = Term.term
type symbol = Symbol.symbol
type var    = Var.var
type sym_or_var = Sym of symbol | Var of var
    
module Key =
  struct
    type t = sym_or_var
          
    let compare (t:t) (s:t) =
      match (t,s) with 
      | (Sym(_),Var(_))   -> cless
      | (Var(_),Sym(_))   -> cgreater 
      | (Sym(s1),Sym(s2))  -> Symbol.compare s1 s2
      | (Var(v1),Var(v2)) -> Var.compare v1 v2

  end
 (*   
module type DiscrTree = 
  sig
    type index 
(*only for debug*)
    type sym_or_var = Sym of Symbol.symbol | Var of var  
    val get_key_list : term -> sym_or_var list
  end
*)
(* module DiscrTree = *)
  
    module IndexM  =  Trie.Make (Key)
    type 'a index = Empty|Not of 'a
      
      
    let rec get_key_list term  = 
      match term with 
      | Term.Fun(sym,args,_) -> 
	  let f list t = List.append list (get_key_list t)
	  in Sym(sym)::(Term.arg_fold_left f [] args)
      | Term.Var(v) -> 
	  [Var(v)]  

    let create () = Empty
    let add term  index  = index
    let remove term index = index 

	
(************old
   module Make (IndexData : UnifIndex.IndexData)=
  struct 
    type indexData = IndexData.t  
    module IndexM  =  
    type index = Empty|Not
	
(* var is grater than sym, 
   so in traversal we first visit sym then var*)   

    let compare_sym_var t s =
      match (t,s) with 
      | (Sym(_),Var(_))   -> cless
      | (Var(_),Sym(_))   -> cgreater 
      | (Sym(s1),Sym(s2))  -> Symbol.compare s1 s2
      | (Var(v1),Var(v2)) -> Var.compare v1 v2
	    

  

(* to be cont....  *)	    
(*    type unif_result *)
    let create () = Empty
    let add  term index  = index
    let remove term  index = index 
(*    val unify  : term -> index -> unif_result *)
	
  end
************old*)

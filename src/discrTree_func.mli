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


type term   = Term.term
type symbol = Symbol.symbol
type var    = Var.var
type sym_or_var = Sym of symbol | Var of var
    
(*module type DiscrTree = 
  sig*)
   type 'a index 
(*only for debug*)
 
    val get_key_list : term -> sym_or_var list
 (* end*)



(**** old 

(* 
  module type DiscrTree = UnifIndex.UnifIndex
*)

module Make (IndexData : UnifIndex.IndexData):
    (UnifIndex.Index with type indexData = IndexData.t)
   

(*  debug **************
type var    = Var.var
type symbol = Symbol.symbol
type term = Term.term

(*module type DiscrTree =
  sig *)

    type index 


(*only for debug*)
    type sym_or_var = Sym of Symbol.symbol | Var of var  
    val get_key_list : term -> sym_or_var list
(*  end*)

*)
**** old*)

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



type subst
type term  = Term.term
type var   = Var.var

type flat_subst = (var*term) list

exception Subst_var_already_def

val create : unit -> subst
val mem    : var -> subst -> bool 
val add    : var -> term -> subst -> subst
val remove : var -> subst -> subst 
val find   : var -> subst -> term
val map    : (term -> term) -> subst -> subst 
val fold   : (var -> term -> 'a ->'a)-> subst -> 'a -> 'a
val iter   : (var -> term -> unit) -> subst -> unit


type termDBref = TermDB.termDB ref

(* returns term in which all varibles in_term are replaced by by_term *)
(* and adds this term to termDB *)
(* we assume that  by_term and in_term are in term_db*)

                             (*by_term*) (*in_term*)
val replace_vars :  termDBref -> term -> term -> term 

                             (*by_term*) (*in_term*)
val grounding    : termDBref -> term -> term -> term 



(* normalise var term by subst*)
(* we assume  that there is no var cycles in subst *)
val find_normalised : subst -> term -> term 


(* applies substituion and adds obtained term into term_db *)
(* nothing is renamed, see substBound for this  *)
(* we assume that all terms in subst and t are in term_db *)
val apply_subst_term : termDBref -> subst -> term -> term

val to_stream      : 'a string_stream -> subst -> unit
val out            : subst -> unit


val to_string : subst -> string 

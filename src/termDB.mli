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

type term   = Term.term
type termDB  
  
val create      : unit -> termDB
val create_name : string -> termDB

(* is not yet implemented for Hashtbl version...*)
val mem         : term -> termDB -> bool 

val add         : term -> termDB -> termDB
val add_ref     : term -> termDB ref -> term

(*remove completely removes term from termDB 
  implementation with counters will be needed for removing clauses*)
val remove      : term -> termDB -> termDB 
val find        : term -> termDB -> term
val size        : termDB -> int
(*val map         : (term -> term)-> termDB -> termDB *)
val fold        : (term -> 'a -> 'a) -> termDB -> 'a -> 'a
val iter        : (term -> unit) -> termDB -> unit

val get_name    : termDB ->string

val to_stream           : 'a string_stream -> termDB -> unit
val out                 : termDB -> unit

val to_string           : termDB ->string

(*debug*)
val get_greatest_key : termDB -> int

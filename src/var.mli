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

type var
type t=var

type bound_var = var Lib.bind

val get_first_var  : unit -> var
val get_next_var   : var -> var

(* get_next_var(v) is greater than v *)
val compare        : var -> var -> int
val equal          : var -> var -> bool

val compare_bvar   : bound_var -> bound_var -> int
val equal_bvar     : bound_var -> bound_var -> bool
val hash           : var -> int
val index          : var -> int


val to_stream      : 'a string_stream -> var -> unit
val out            : var -> unit

val to_string      : var -> string
val to_prolog      : var -> string

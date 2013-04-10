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


open Logic_interface

(*
val num_of_dismatch_blockings    :  int ref 
val num_of_non_proper_inst       :  int ref 
val num_of_duplicates            :  int ref
*)

(* strict_subset_subsume by_clause to_clause *)
(* we assume that to_subs_clause has defined length *)
(* and by_clause does not, but all lits a are in    *)

val strict_subset_subsume  : clause -> clause -> bool

(* resolution, factoring can raise  Unif.Unification_failed *)
(* resolution can raise Main_subsumed_by*)

exception Main_subsumed_by of clause
val resolution    : clause -> literal -> literal ->
                      clause list -> literal -> term_db_ref -> clause list 



val resolution_dismatch   : bool -> bool -> bool -> clause -> literal -> literal ->
                      clause list -> literal -> term_db_ref -> clause list 


val subs_resolution    : clause -> literal -> literal ->
                      clause list -> literal -> term_db_ref -> clause list 

val factoring     : clause -> literal -> literal -> term_db_ref -> clause

(*
val instantiation : term_db ref -> clause -> literal -> literal ->
                      clause list -> literal -> clause list 
*)

val equality_resolution_simp: clause -> clause

val instantiation_norm : term_db_ref -> context -> clause -> literal -> literal ->
  clause list -> literal -> clause list 

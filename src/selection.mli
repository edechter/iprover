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



type term    = Term.term
type clause  = Clause.clause
type literal = Clause.literal

(*val selection :  (clause-> literal list) -> clause -> literal list*)

val sel_kbo_max : clause ->  literal list
val literal_neg_selection_max : clause -> literal list 
val literal_neg_selection_min : clause -> literal list 

(* returns selection function form type *)
(*val res_sel_type_to_fun    : Options.res_sel_fun_type -> (clause ->  literal list)*)
(*val res_sel_type_to_string : res_sel_type -> string*)

(* first argumet is a selection function *)
(*val get_sel : (clause->literal list) -> clause -> literal list*)

(* changing selection for next negative and finaly to maximal *)
(* change_sel changes selection to new and returns new selected literals *)
(* if  selection is already max then raises Max_sel  *)
(* also works when no sel is assigned*)
(* Changes sel_lits in clause and can chage res_sel_max  *)
exception Max_sel	  
val change_sel  : clause ->  literal list

val res_lit_sel : (clause -> literal list)

(* instantiation *)
(* first arg is a func. which  *)
(* chooses candidate literals from the clause i.e. true in a model *)
val inst_lit_sel : (literal -> bool) -> (clause -> literal)

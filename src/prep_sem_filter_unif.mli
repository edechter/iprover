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



type clause = Clause.clause

(* filtered_clauses  are used for output only *)
type filtered_clauses =
    {

      filtered_in  : clause list;
(* filtered out clauses are used in model representation *)
(* for convenience  clauses get assigned inst_sel_lit which *)
(* are the literals true in the model *)
      filtered_out : clause list 
   }


(* sem_filter_unif clause_list side_clause_list *)
(* side clauses are theory clauses: they are used to block removing needed     *)
(* clauses from the clause set but are not added to the resulting filtered set *)


val sem_filter_unif : clause list -> clause list -> filtered_clauses

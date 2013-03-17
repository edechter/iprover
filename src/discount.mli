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
type clause = Clause.clause

type context = Clause.context

exception Satisfiable of context

(* exception Unsatisfiable *)
exception Empty_Clause of clause

module type InputM = 
  sig
    val inst_module_name : string
(* we assume that input clauses are normalised with terms in *)
(* Parsed_input_to_db.term_db_ref *)
(* clauses are copied, but terms are not some paremters of terms such as *)
(* inst_in_unif_index can be changed *)
(* one should run clear_all () which also clears term parameters *)
    val input_clauses    : clause list
  end


module Make (InputM:InputM) : sig


(*val start_discount : clause list -> unit  *)

(* for combination with e.g. instantiation *)

(* run it once with all initial clauses incl. additional axioms*)
(*val init_discount_input_clauses : clause list -> unit *)




(* in order to get the proof we need to pass the empty clause *)

(*val sel_fun_type : Selection.res_sel_type ref *)


(* discount_loop_exchange act_to_exch_flag  pass_to_exch_flag *)
(* makes one discount loop iteration  *)
(* returns generated clauses: for exchange*) 
(* if act_to_exch_flag  is true and pass_to_exch_flag = false *) 
(* then return the clause added to active if any  *)
(* if pass_to_exch_flag is true then returns all clauses added to passive*)

(*val discount_loop_exchange     :  bool -> bool -> clause list *)

val discount_loop_exchange     :  unit -> unit

(* the clause should be fresh *)
(*(it's better to copy the clause to a new one before adding )*)
(*val add_inst_exchange_clause_to_passive : clause -> unit*)
(*
val add_new_clause_to_passive  : clause -> unit
*)




(* unassigns all structures related to discount and runs GC.full_major*)
val clear_all                  : unit -> unit

end 
(*debug*)
(*
val try_matching_all : unit -> unit
val try_subsumption_all : unit -> unit
*)

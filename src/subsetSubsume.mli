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



type clause  = Clause.clause
type literal = Clause.literal

(* restricted subset subsumption very fast but 
   very incomplete :  
   literals in clauses assumed to be ordered by e.g. fast term comparison
   then we check whether given clause (or its subclause)
   extents a clause in the index 
   and then this clause is subsumed
   or this clause is extended by a clause in the index and then the clause 
   in the index is subsumed 
*)


exception Is_subsumed 
exception Subsumes
exception Already_in 
exception No_subsumed

type index
      
val create : unit -> index

(* we assume that the literals in the clause are in term db*)   
val add_clause  : clause -> index  -> index 

(* is_subsumed returns the clause which subset subsumes clause *)
(* otherwise raises Not_found*)
val is_subsumed : clause -> index -> clause

(* returns list of  all strictly subsumed clauses by the clause 
   raises No_subsumed if no such clauses*)

val find_subsumed : clause -> index -> clause list 
    
(* removes a subtrie corr. to all subsumed by the cluase clauses *)
(* after this the cluase is not in the index *)
(* for efficience can be joint with find_subsumed  *)
(* (remove clauses from  separately)*)
(* one should separately set *)
(* Clause.set_bool_param false Clause.in_subset_subsumption_index clause *)
(* for removed cluases *)    
val  remove_subsumed : clause -> index -> index 


(* removes clause from ss index and raises Not_found if the clause is not there*)
val  remove : clause -> index -> index 

       

(* add later!
(*Restricted Subset subsumed*)
   val is_rsubset_subsumed : index -> clause -> bool
   	
(* the list of clauses (rsubset)subsumed by the given clause*)
   val subsumed_clauses : index -> clause -> clause list
	

 (*   val remove : clause -> index ref -> unit	*)
*)
 

/*----------------------------------------------------------------------(C)-*/
/* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
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
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         */
/*----------------------------------------------------------------------[C]-*/

/*
  
  Created: 2011-12-07 Christoph Sticksel

 */

extern "C" {

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

}

// #define DEBUG

/* -D flags in MiniSat mtl/template.mk */
#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS

/* includes from MiniSat simp/Main.cc */
#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include "mtl/Vec.h"
#include <utils/System.h>
#include <utils/ParseUtils.h>
#include <utils/Options.h>
#include <core/Dimacs.h>
#include <simp/SimpSolver.h>

/* Define lifted booleans as OCaml integers */
#define Val_l_True Val_int(0)
#define Val_l_False Val_int(1)
#define Val_l_Undef Val_int(2)

/* 'a option = None */
#define Val_none Val_int(0)

/* 'a option = Some of 'a */

/* Must not be used inside a nested block: CAMLlocal1 must be at the
   beginning of each function. Cannot use inline, better copy the code
   into your function: CAMLlocal and caml_alloc at the top,
   Store_field to set the value. */
/*
CAMLprim value Val_some( value v )
{   
    CAMLparam1 (v);
    CAMLlocal1 (some);
    some = caml_alloc(1, 0);
    Store_field (some, 0, v);
    CAMLreturn (some);
}
*/

#define Some_val(v) Field(v,0)

/* Switch to MiniSat namespace */
using namespace Minisat;

/* Compare two MiniSat literals */
int minisat_lit_compare(value l1_in, value l2_in) 
{

  // Get MiniSat literal from value
  Lit* l1 = (Lit*) Data_custom_val(l1_in);
  
  // Get MiniSat literal from value
  Lit* l2 = (Lit*) Data_custom_val(l2_in);

  if (*l1 == *l2) 
    {
      return 0;
    }
  else if (*l1 < *l2) 
    {
      return -1;
    }
  else
    {
      return 1;
    }

}


/* Hash a MiniSat literal */
intnat minisat_lit_hash(value l_in) 
{

  // Get MiniSat literal from value
  Lit* l = (Lit*) Data_custom_val(l_in);
  
  return (intnat) toInt(*l);

}


/* Custom OCaml operations for MiniSat literal 
   
 None of the default operations are defined. 

 TODO: think about defining some of them 
 - finalisation is not needed
 - comparing and hashing would be nice 
 - serialisation is not needed 

*/
static struct custom_operations minisat_lit_custom_ops = {
    identifier: "Minisat::Lit",
    finalize:    custom_finalize_default,
    compare:     *minisat_lit_compare,
    hash:        *minisat_lit_hash,
    serialize:   custom_serialize_default,
    deserialize: custom_deserialize_default
};

/* Copy a MiniSat literal into a newly allocated OCaml custom tag */

/* Cannot use CAMLlocal1 inside a nested block, using this function is
   probably dangerous, better copy the code inside the function. */
/*
static inline value copy_minisat_lit( Lit *lit )
{
    CAMLparam0();
    CAMLlocal1(v);
    v = caml_alloc_custom( &minisat_lit_custom_ops, sizeof(Lit), 0, 1);
    memcpy( Data_custom_val(v), lit, sizeof(Lit) );
    CAMLreturn(v);
}
*/

/* Append OCaml list of literals to a vector of MiniSat literals */
void vec_lit_of_lit_list(value* lit_list_in, vec<Lit>* lits) 
{

  // Allocate local OCaml variable 
  CAMLlocal1(head);

  // Set to head of list 
  head = *lit_list_in;

  // Iterate list of literals
  while (head != Val_emptylist) 
    {
      
      // Get head element of list 
      value lit_in = Field(head, 0);
      
      // Get MiniSat literal from value
      Lit* lit = (Lit*) Data_custom_val(lit_in);
      
#ifdef DEBUG
      fprintf(stderr, "%s%d ", 
	      sign(*lit) ? "" : "~",
	      var(*lit));
#endif
      
      // Add literal to clause 
      lits->push(*lit);
      
      // Continue with tail of list
      head = Field(head, 1);
      
    }
  
}

/* Create and return a MiniSat solver instance 

   external minisat_create_solver : unit -> minisat_solver = "minisat_create_solver" 

   The solver is created in the C++ heap, OCaml gets only a pointer in
   an Abstract_tag.

*/
extern "C" CAMLprim value minisat_create_solver(value unit)
{

  // Declare parameters 
  CAMLparam1 (unit);
  CAMLlocal1 (res);
  
  // Initialise MiniSat instance 
  Solver* s = new Solver;

  // Initialise vector for tracking literals to be assumed, this is a
  // sorted vector of literals without duplicates
  vec<Lit>* v = new vec<Lit>;

  // Allocate abstract datatype for MiniSat instance 
  res = caml_alloc(3, Abstract_tag);

  // First field is pointer to solver 
  Store_field(res, 0, (value) s); 

  // Second field is number of variables on last solve call
  Store_field(res, 1, (value) 0); 

  // Third field is vector of literals to be assumed
  Store_field(res, 2, (value) v); 

#ifdef DEBUG
  fprintf(stderr, "Created new MiniSat instance\n");
#endif

  // Return MiniSat instance 
  CAMLreturn(res);

}

/* Add a variable to MiniSat

   external minisat_add_var : minisat_solver -> int -> unit = "minisat_add_var"

   Variables are integers, the first is 0. Integers do not have to be
   allocated for OCaml.

   Each variable has to be allocated by calling newVar().
   minisat_create_lit does this on literal creation if the variable
   has not been allocated.

 */
extern "C" CAMLprim value minisat_add_var (value solver_in, value var_id_in)
{  

  // Declare parameters 
  CAMLparam2 (solver_in, var_id_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  int var_id = Int_val(var_id_in);

  // Declare variable in MiniSat
  while (var_id + 1 >= solver->nVars()) solver->newVar();

  // Return 
  CAMLreturn(Val_unit);

}

/* Create and return a literal of a variable 

   external minisat_create_lit : minisat_solver -> int -> bool -> minisat_lit = "minisat_create_lit" 

   Variables are integers, the first is 0. Use true for a positive
   literal and false for a negative one.

   A literal has to be created with the mkLit function, it is a custom
   datatype stored on the OCaml heap.

 */
extern "C" CAMLprim value minisat_create_lit(value solver_in, value lit_sign_in, value lit_var_in)
{
  
  // Declare parameters 
  CAMLparam3 (solver_in, lit_sign_in, lit_var_in);

  // Allocate for a custom datatype for literal
  CAMLlocal1 (res);
  res = caml_alloc_custom( &minisat_lit_custom_ops, sizeof(Lit), 0, 1);

  Solver* solver = (Solver*) Field(solver_in, 0);
  bool lit_sign = Bool_val(lit_sign_in);
  int lit_var = Int_val(lit_var_in);

  // First declare variable in MiniSat
  while (lit_var >= solver->nVars()) solver->newVar();

  // Must use mkLit to create literals 
  Lit lit = mkLit(lit_var, lit_sign);

#ifdef DEBUG
  fprintf(stderr, 
	  "Created literal %d from %s%d\n", 
	  toInt(lit), 
	  lit_sign ? "" : "~", 
	  lit_var);
#endif

  // Copy MiniSat literal to OCaml datatype
  memcpy(Data_custom_val(res), &lit, sizeof(Lit));

  // Return literal
  CAMLreturn(res);

}

/* Assert a clause given as a list of literals, return false if the
   clause set immediately becomes unsatisfiable, true otherwise.

   external minisat_add_clause : minisat_solver -> minisat_lit list -> bool = "minisat_add_clause" 

*/
extern "C" CAMLprim value minisat_add_clause(value solver_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam2 (solver_in, clause_in);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Clause to be asserted
  vec<Lit> lits;
  lits.clear();

#ifdef DEBUG
  fprintf(stderr, "Asserting clause ");
#endif

  // Copy clause to vector
  vec_lit_of_lit_list(&clause_in, &lits);

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Add clause to solver
  if (solver->addClause_(lits))
    {

      // Not immediately unsatisfiable 
      CAMLreturn(Val_true);

    }
  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable with added clause\n");
#endif

      // Immediately unsatisfiable with added clause
      CAMLreturn(Val_false);

    }

}


/* Assert a clause, given as a list of literals, as an interesting
   constraint clause. Return both a flag if the clause is immediately
   unsatisfiable and a possibly undefined unique id for the clause.
   
   The unique id is [None] if the clause was simplified or if it is
   unsatisfiable. A return value of [(false, None)] means the clause
   is immediately unsatisfiable, if [(true, None)] is returned, the
   clause is already satisfied, otherwise the return value is [(true,
   Some id)].

   A tracking variable is added to the clause as well as its
   complement assumed on each solve call in addition to given
   assumptions. The tracking variable is assumed negatively and added
   to the clause positively, hence the conflict clause will contain
   the tracking literal, i.e. the identifier of the clause,
   positively. 

   If the tracking variable is None, a new variable is created,
   otherwise the variable given is used to track the clause. If a
   tracking variable is given, it must have been previously obtained
   as a new variable. That is, only repeats of tracking variables are
   allowed, tracking variables cannot be arbitrarily chosen.

   external minisat_add_clause_with_id : minisat_solver -> minisat_literal list -> int option -> bool * int option = "minisat_add_clause_with_id" 

*/
extern "C" CAMLprim value minisat_add_clause_with_id(value solver_in, value id_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam3(solver_in, id_in, clause_in);

  // Allocate for OCaml pair and 'a option value
  CAMLlocal2(res, res_track_var);
  res = caml_alloc(2, 0);
  res_track_var = caml_alloc(1, 0);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Get vector of tracking literals 
  vec<Lit>* assume_lits = (vec<Lit>*) Field(solver_in, 2);

  // Clause to be asserted
  vec<Lit> lits;
  lits.clear();

  // Atom for tracking literal
  Var track_var;

  // Create a new variable if input ID is Null
  if (id_in == Val_none)

    // Create a new variable
    track_var = solver->newVar();

  else
    // Use variable given 
    // It is not necessary to allocate the variable in MiniSat, since
    // it must have been previously used
    {

#ifdef DEBUG
      fprintf(stderr, "Setting clause id to %d\n", Int_val(Some_val(id_in)));
#endif

      track_var = Int_val(Some_val(id_in));

    }

  // Create negative tracking literal as assumption literal
  Lit assume_lit = mkLit(track_var, false);

  // Add assumption literal to tracking literals only if new
  if (id_in == Val_none)
    assume_lits->push(assume_lit);

#ifdef VDEBUG
  fprintf(stderr, "Global assumptions ");

  for (int j = 0; j < assume_lits->size(); j++)
	 fprintf(stderr, "%s%d ",
		 sign(assume_lits->operator[](j)) ? "" : "~",
		 var(assume_lits->operator[](j)));
       
  fprintf(stderr, "\n");
#endif

  // Create positive literal to be added to clause as tracking literal
  Lit track_lit = mkLit(track_var, true);

  // Add tracking literal to clause as first literal
  lits.push(track_lit);

#ifdef DEBUG
  fprintf(stderr, "Asserting interesting clause %s%d ",
	  sign(track_lit) ? "" : "~",
	  var(track_lit));
#endif

  // Append clause to vector
  vec_lit_of_lit_list(&clause_in, &lits);

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Add clause to solver
  if (solver->addClause_(lits))
    {

#ifdef DEBUG
      fprintf(stderr, "Not immediately unsatisfiable with added clause\n");
#endif

      // Clause set is not immediately unsatisfiable
      Store_field(res, 0, Val_true);

      // Clause was added with uid
      Store_field(res_track_var, 0, Val_int(toInt(track_var)));
      Store_field(res, 1, res_track_var);

#ifdef DEBUG
  fprintf(stderr, "Exit minisat_add_clause_with_id\n");
#endif

      // Not immediately unsatisfiable with added clause
      CAMLreturn (res);

    }
  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable with added clause\n");
#endif

      // Clause set is immediately unsatisfiable
      Store_field(res, 0, Val_false);
      
      // Clause was not added, does not have an id
      Store_field(res, 1, Val_none);
      
      // Immediately unsatisfiable with added clause
      CAMLreturn (res);

    }

}

/* Return the position in the vector where the variables of all
   literals are smaller than the given max_lit */
int find_max_lit(const vec<Lit>& lits, int start, int end, int max_var)
{
    // Termination condition: start index greater than end index
    if(start > end)
    {
        return end;
    }
 
    // Find the middle element of the vector and use that for splitting
    // the array into two pieces.
    int middle = start + ((end - start) / 2);
 
    if(var(lits[middle]) == max_var)
      {
        return middle - 1;
      }
    else if(var(lits[middle]) > max_var)
      {
        return find_max_lit(lits, start, middle - 1, max_var);
      }
    
    return find_max_lit(lits, middle + 1, end, max_var);
}

/* Shrink the vector of literals to contain only the literals with
   variables smaller then max_var */
void vec_lit_upto(vec<Lit>& lits, int max_var) 
{ 

#ifdef DEBUG
  fprintf(stderr, "Only assumptions up to %d\n", max_var);
#endif

  // Do nothing for empty vector
  if (lits.size() > 0)
    {
      
      int max_lit = find_max_lit(lits, 0, lits.size(), max_var);

#ifdef DEBUG
      fprintf(stderr, 
	      "Splitting literal vector at %s%d, %s%d\n",
	      sign(lits[max_lit]) ? "" : "~",
	      var(lits[max_lit]),
	      sign(lits[max_lit+1]) ? "" : "~",
	      var(lits[max_lit+1]));
#endif
      
      // Otherwise shrink vector to contain only literals smaller than
      // max_var
      lits.shrink(lits.size() - max_lit - 1);
  
    }
}


/* Test the given clause set for satisfiability. Return true if
   satisfiable, false if unsatisfiable.

   external minisat_solve : minisat_solver -> Some int -> bool = "minisat_solve" 

*/
extern "C" CAMLprim value minisat_solve(value solver_in, value max_clause_id_in)
{
    
  // Declare parameters 
  CAMLparam2(solver_in, max_clause_id_in);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Get vector of tracking assumptions
  vec<Lit>* all_assume_lits = (vec<Lit>*) Field(solver_in, 2);

  // Vector of tracking assumptions to use
  vec<Lit> assume_lits;

  // Copy all assumptions
  all_assume_lits->copyTo(assume_lits);

  // Shrink vector to only tracking assumptions
  if (max_clause_id_in != Val_none)
    vec_lit_upto(assume_lits, Int_val(Some_val(max_clause_id_in)));

#ifdef VDEBUG
  fprintf(stderr, "Global assumptions ");

  for (int j = 0; j < assume_lits.size(); j++)
    fprintf(stderr, "%s%d",
	    sign(assume_lits[j]) ? "" : "~",
	    var(assume_lits[j]));
       
  fprintf(stderr, "\n");
#endif

#ifdef DEBUG
  fprintf(stderr, "Solving without assumptions\n");
#endif

#ifdef DEBUG
  fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	  (int) Field(solver_in, 1),
	  solver->nVars());
#endif

  // Must run simplify before solving under assumptions
  if (solver->simplify())
    {
    
      // Update number of variables
      Store_field(solver_in, 1, (value) solver->nVars()); 
      
      // Run MiniSat with tracking assumptions 
      bool res = solver->solve(assume_lits);
      
      // Return result
      CAMLreturn(Val_bool(res));

    }
  else
    {

      // Return result
      CAMLreturn(Val_false);

    }

}


/* Test the given clause set for satisfiability when the given
   literals are to be made true. Return l_True = 0 if the clause set
   is satisfiable with assumptions, l_Undef = 2 if the clause set is
   immediately unsatisfiable without assumptions and l_False = 1 if
   the clause set is unsatisfiable with assumptions.

   external minisat_solve_assumptions : minisat_solver -> minisat_lit list -> lbool = "minisat_solve_assumptions" 

*/
extern "C" CAMLprim value minisat_solve_assumptions(value solver_in, value assumptions_in, value max_clause_id_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, assumptions_in);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Get vector of tracking assumptions
  vec<Lit>* all_assume_lits = (vec<Lit>*) Field(solver_in, 2);

  // Vector of tracking assumptions to use
  vec<Lit> assume_lits;

  // Copy all assumptions
  all_assume_lits->copyTo(assume_lits);

  // Shrink vector to only tracking assumptions
  if (max_clause_id_in != Val_none)
    {

#ifdef DEBUG
      fprintf(stderr, 
	      "Assumptions up to %d\n", 
	      Int_val(Some_val(max_clause_id_in)));
#endif 

      vec_lit_upto(assume_lits, Int_val(Some_val(max_clause_id_in)));
    }

#ifdef VDEBUG
  fprintf(stderr, "Global assumptions ");

  for (int j = 0; j < assume_lits.size(); j++)
    fprintf(stderr, "%s%d ",
	    sign(assume_lits[j]) ? "" : "~",
	    var(assume_lits[j]));
  
  fprintf(stderr, "\n");
#endif

  // Must run simplify before solving under assumptions
  if (solver->simplify())
    {

#ifdef DEBUG
      fprintf(stderr, "Assuming ");
#endif

      // Append clause to vector
      vec_lit_of_lit_list(&assumptions_in, &assume_lits);

#ifdef DEBUG
      fprintf(stderr, "\n");
#endif


#ifdef DEBUG
  fprintf(stderr, "All assumptions ");

  for (int j = 0; j < assume_lits.size(); j++)
	 fprintf(stderr, "%s%d ",
		 sign(assume_lits[j]) ? "" : "~",
		 var(assume_lits[j]));
       
  fprintf(stderr, "\n");
#endif


#ifdef DEBUG
      fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	      (int) Field(solver_in, 1),
	      solver->nVars());
#endif
      
      // Update number of variables
      Store_field(solver_in, 1, (value) solver->nVars()); 
      
      // Solve with literal assumptions
      if (solver->solve(assume_lits))
	{
	  
#ifdef DEBUG
	  fprintf(stderr, "Satisfiable under assumptions\n");
#endif

	  // Satisfiable under assumptions
	  CAMLreturn(Val_l_True);

	}

      else
	{

#ifdef DEBUG
	  fprintf(stderr, "Unsatisfiable under assumptions\n");
#endif

	  // Unsatisfiable under assumptions
	  CAMLreturn(Val_l_False);

	}

    }

  else  
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable without assumptions\n");
#endif

      // Unsatisfiable without assumptions
      CAMLreturn(Val_l_Undef);
    }
	
}

/* Test the given clause set for satisfiability in a limited search
   when the given literals are to be made true.

   This is similar to minisat_solve_assumptions above, but the search
   is limited to the given number of conflicts. 

   Return None if satisfiability could not be determined under the
   conflict limit. Return Some l_True = Some 0 if the clause set is
   satisfiable with assumptions, Some l_Undef = Some 2 if the clause
   set is immediately unsatisfiable without assumptions and Some
   l_False = Some 1 if the clause set is unsatisfiable with
   assumptions.

   external minisat_fast_solve : minisat_solver -> minisat_lit list -> int -> lbool option = "minisat_fast_solve"

*/
extern "C" CAMLprim value minisat_fast_solve(value solver_in, value assumptions_in, value max_conflicts_in, value max_clause_id_in)
{

  // Declare parameters 
  CAMLparam3 (solver_in, assumptions_in, max_conflicts_in);

  // Allocate for two 'a option values 
  CAMLlocal2 (Val_some_l_True, Val_some_l_Undef);

  // Create one value Some l_True
  Val_some_l_True = caml_alloc(1, 0);
  Store_field (Val_some_l_True, 0, Val_l_True);

  // Create one value Some l_Undef
  Val_some_l_Undef = caml_alloc(1, 0);
  Store_field (Val_some_l_Undef, 0, Val_l_Undef);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Get vector of tracking assumptions
  vec<Lit>* all_assume_lits = (vec<Lit>*) Field(solver_in, 2);

  // Vector of tracking assumptions to use
  vec<Lit> assume_lits;

  // Copy all assumptions
  all_assume_lits->copyTo(assume_lits);

  // Shrink vector to only tracking assumptions
  if (max_clause_id_in != Val_none)
    {

#ifdef DEBUG
      fprintf(stderr, 
	      "Assumptions up to %d\n", 
	      Int_val(Some_val(max_clause_id_in)));
#endif 

      vec_lit_upto(assume_lits, Int_val(Some_val(max_clause_id_in)));
    }

  // Conflict budget for fast solving
  int max_conflicts = Int_val(max_conflicts_in);

  // Must run simplify before solving under assumptions
  if (solver->simplify())
    {

#ifdef DEBUG
      fprintf(stderr, "Assuming ");
#endif

      // Append clause to vector
      vec_lit_of_lit_list(&assumptions_in, &assume_lits);

#ifdef DEBUG
      fprintf(stderr, "\n");

      if (!assume_lits.size()) fprintf(stderr, "No assumptions\n");
#endif

      // Set budget for number of conflicts
      solver->setConfBudget(max_conflicts);

#ifdef DEBUG
      fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	      (int) Field(solver_in, 1),
	      solver->nVars());
#endif
      
      // Update number of variables
      Store_field(solver_in, 1, (value) solver->nVars()); 
      
      // Solve with literal assumptions 
      lbool res = solver->solveLimited(assume_lits);

      if (res == l_True) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Satisfiable with assumptions (fast solve)\n");
#endif

	  CAMLreturn(Val_some_l_True);
	}

      if (res == l_False) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Unsatisfiable with assumptions (fast solve)\n");
#endif

	  CAMLreturn(Val_some_l_True);
	}

      if (res == l_Undef) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Unknown (fast solve)\n");
#endif

	  CAMLreturn(Val_none);
	}
      
    }

  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable without assumptions (fast solve)\n");
#endif

      // Unsatisfiable without assumptions
      CAMLreturn(Val_some_l_Undef);
      
    }

}


/* Return the truth value of the literal in the current model: Some
    true if the literal is true, Some false if the literal is false
    and None if the literal value is undefined

  external minisat_model_value : minisat_solver -> minisat_lit -> int = "minisat_model_value"

*/
extern "C" CAMLprim value minisat_model_value (value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Get MiniSat literal from input 
  Lit* lit = (Lit*) Data_custom_val(lit_in);

  // Variable not present in last solve call?
  if (var(*lit) >= (int) Field(solver_in, 1))
    {

#ifdef DEBUG
      fprintf(stderr, "Variable %d not in model, set to l_Undef\n", var(*lit));
#endif
      
      // Return undefined without reading from model
      CAMLreturn(Val_l_Undef);
      
    }
  else
    {

      // Get value of literal in model
      lbool val = solver->modelValue(*lit);

#ifdef DEBUG
      fprintf(stderr, "Model value %s%d: %s (%d)\n", 
	      sign(*lit) ? "" : "~",
	      var(*lit),
	      val == l_True ? "l_True" : (val == l_False ? 
					  "l_False" : 
					  "l_Undef"),
	      toInt(val));
#endif

      if (val == l_True) 
	{ 
	  CAMLreturn(Val_l_True);
	}
      else if (val == l_False) 
	{ 
	  CAMLreturn(Val_l_False);
	}
      else
	{
	  CAMLreturn(Val_l_Undef);
	}
      
    }

}


/* Return final conflict clause after an unsatisfiable solve call

  external minisat_get_conflicts : minisat_solver -> int list = "minisat_get_conflicts"

*/
extern "C" CAMLprim value minisat_get_conflicts (value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Initialise return value to empty list
  CAMLlocal2(res, cons);
  res = Val_emptylist;

  // Iterate literals in conflict clause backwards to preserve order
  // of list created
  for (int j = solver->conflict.size() - 1; j >= 0; --j)
    {

#ifdef DEBUG
      fprintf(stderr, "%d ", 
	      sign(solver->conflict[j]) ? var(solver->conflict[j]) : -var(solver->conflict[j]));
#endif

      // Allocate for new list elements
      cons = caml_alloc(2, 0);

      // Head of list is literal in conflict clause
      Store_field(cons, 0, Val_int(sign(solver->conflict[j]) ? var(solver->conflict[j]) : -var(solver->conflict[j])));

      // Tail of list is previous list 
      Store_field(cons, 1, res);

      // Continue with constructed list 
      res = cons;
      
    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Return list
  CAMLreturn(res);

}


/* Minimise an unsatisfiable core

   external minisat_minimise_core : minisat_solver -> int list -> int list = "minisat_minimise_core"
   
*/
extern "C" CAMLprim value minisat_minimise_core (value solver_in, value core_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, core_in);

  // Initialise return value to empty list
  CAMLlocal2(res, cons);
  res = Val_emptylist;
  
  // Local variable for input list 
  CAMLlocal1(head);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Resulting minimal unsatisfiable core
  vec<Lit> min_core;

  // Input unsatisfiable core
  vec<Lit> core;
  core.clear();

  // Assumptions for solving 
  vec<Lit> assume_lits;
  assume_lits.clear();

  // Initialise head of list
  head = core_in;

#ifdef DEBUG
      fprintf(stderr, "Input unsat core ");
#endif

  // A literal and int to be used in the following loop
  Lit lit;  int l;

  // Iterate list of literals in core
  while (head != Val_emptylist) 
    {
      
      // Get head element of list 
      l = Int_val(Field(head, 0));

      // Literals in conflict clause are positive, identical to clause
      // id, but must be negative as assumption
      lit = mkLit(abs(l), l > 0 ? false : true);
      
#ifdef DEBUG
      fprintf(stderr, "%s%d ", 
	      sign(lit) ? "" : "~",
	      var(lit));
#endif
      
      // Add literal to assumptions
      core.push(lit);
      
      // Continue with tail of list
      head = Field(head, 1);
      
    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif
  
  // Iterate until input unsat core is empty 
  while (core.size() != 0)  
    {

      // Only if satisfiable after simplifications 
      // (Must always call simplify when solving with assumptions)
      if (solver->simplify())
	{

	  // Get last literal from input core
	  Lit last_lit = core.last();

	  // Remove last literal from input core
	  core.pop();

	  // Initialise assumptions with minimal core 
	  min_core.copyTo(assume_lits);

	  // Push all literals in remaining core to assumptions
	  for (int i = 0; i < core.size(); i++) 
	    assume_lits.push(core[i]);
	  
	  // Solve with assumptions
	  if (solver->solve(assume_lits))
	    {
	      
#ifdef DEBUG
	      fprintf(stderr, "Satisfiable without %s%d\n",
		      sign(last_lit) ? "" : "~",
		      var(last_lit));
#endif

	      // Literal tracks a transition clause, must be in minimal core
	      min_core.push(last_lit);

	    }

	  else

	    {

#ifdef DEBUG
	      fprintf(stderr, "Unsatisfiable without %s%d\n",
		      sign(last_lit) ? "" : "~",
		      var(last_lit));
#endif

	      // Literal tracks a non-transition clause, not in minimal core
	      
	    }
	  
	}
      else
	{
	  
#ifdef DEBUG
	  fprintf(stderr, "Unsatisfiable without assumptions (minimise core)\n");
#endif
	  
	  // Unsatisfiable without assumptions
	  CAMLreturn(Val_emptylist);
	  
	}
      
    }
  
#ifdef DEBUG
  fprintf(stderr, "Minimal unsat core is ");
#endif
  
  // Iterate literals in minimal unsat core 
  for (int j = 0; j < min_core.size(); j++)
    {
      
#ifdef DEBUG
      fprintf(stderr, "%d ", 
	      sign(min_core[j]) ? var(min_core[j]) : -var(min_core[j]));
#endif
      
      // Allocate for new list elements
      cons = caml_alloc(2, 0);

      // Assumption literals are negative, must use complement to map
      // to clause ids
      Store_field(cons, 
		  0, 
		  Val_int(sign(min_core[j]) ? 
			  -var(min_core[j]) : 
			  var(min_core[j])));

      // Tail of list is previous list 
      Store_field(cons, 1, res);

      // Continue with constructed list 
      res = cons;
      
    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Return list
  CAMLreturn(res);

}


/* Return the model after a satisfiable solve

  external minisat_get_model : minisat_solver -> bool option array = "minisat_get_model"

*/
extern "C" CAMLprim value minisat_get_model (value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  // Allocate for two 'a option values 
  CAMLlocal2 (Val_some_true, Val_some_false);

  // Create one value Some l_True
  Val_some_true = caml_alloc(1, 0);
  Store_field (Val_some_true, 0, Val_true);

  // Create one value Some l_Undef
  Val_some_false = caml_alloc(1, 0);
  Store_field (Val_some_false, 0, Val_false);

  // Get solver instance 
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Initialise return value to array of size of the model
  CAMLlocal1(res);
  res = caml_alloc(solver->model.size(), 0);

  // Boolean value for model value
  lbool val;

  // Iterate variables in model
  for (int j = 0; j < solver->model.size(); j++)
    {

#ifdef DEBUG
      fprintf(stderr, "%d is %s\n", 
	      j,
	      solver->modelValue(mkLit(j, true)) == l_True ? "l_True" : 
	      (solver->modelValue(mkLit(j, true)) == l_False ? "l_False" : "l_Undef"));
#endif

      // Must use modelValue of Lit, truth value of Var seems to be
      // negated
      val = solver->modelValue(mkLit(j, true));
      
      if (val == l_True) 
	{ 
	  // Store model value in array
	  Store_field(res, j, Val_some_true);
	}
      else if (val == l_False) 
	{ 
	  // Store model value in array
	  Store_field(res, j, Val_some_false);
	}
      else
	{
	  // Store model value in array
	  Store_field(res, j, Val_none);
	}

    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Return array
  CAMLreturn(res);

}


/* Return the propositional variable in the literal

   external minisat_lit_var : minisat_solver -> minisat_lit -> int = "minisat_lit_to_int"

*/
extern "C" CAMLprim value minisat_lit_var(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);
  CAMLlocal1(res);

  Lit* lit = (Lit*) Data_custom_val(lit_in);

  // Return OCaml integer
  res = Val_int(var(*lit));
  CAMLreturn(res);

}


/* Return the sign of the literal, true for a positive and false
   for a negative literal 
   
   external minisat_lit_sign : minisat_solver -> minisat_lit -> bool = "minisat_lit_to_int"
    
*/
extern "C" CAMLprim value minisat_lit_sign(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);
  CAMLlocal1(res);

  Lit* lit = (Lit*) Data_custom_val(lit_in);
  
  // Return OCaml Boolean
  res = Val_bool(sign(*lit));
  CAMLreturn(res);

}


/* Return the number of tracking literals

   external minisat_clauses_with_id : minisat_solver -> int = "minisat_clauses_with_id"
    
*/
extern "C" CAMLprim value minisat_clauses_with_id(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  // Allocate for return value 
  CAMLlocal1(res);

  vec<Lit>* assume_lits = (vec<Lit>*) Field(solver_in, 2);

  // Return OCaml integer
  res = Val_int(assume_lits->size());
  CAMLreturn(res);

}


/* Return the number of propositional variables

  external minisat_stat_vars : minisat_solver -> int = "minisat_stat_vars" 

*/
extern "C" CAMLprim value minisat_stat_vars(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  // Allocate for return value 
  CAMLlocal1(res);

  Solver* solver = (Solver*) Field(solver_in, 0);

  // Read number of variables 
  int vars = solver->nVars();

  // Return OCaml integer
  res = Val_int(vars);
  CAMLreturn(res);

}


/* Return the number of clauses
  
  external minisat_stat_clauses : minisat_solver -> int = "minisat_stat_clauses" 
*/
extern "C" CAMLprim value minisat_stat_clauses(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  // Allocate for return value 
  CAMLlocal1(res);

  Solver* solver = (Solver*) Field(solver_in, 0);

  // Read number of clauses 
  int vars = solver->nClauses();

  // Return OCaml integer
  res = Val_int(vars);
  CAMLreturn(res);

}

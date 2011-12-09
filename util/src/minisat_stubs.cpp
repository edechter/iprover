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

// -D flags in mtl/template.mk 
#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS

// includes from simp/Main.cc 
#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include <utils/System.h>
#include <utils/ParseUtils.h>
#include <utils/Options.h>
#include <core/Dimacs.h>
#include <simp/SimpSolver.h>

using namespace Minisat;

// Custom OCaml operations for MiniSat literal
static struct custom_operations minisat_lit_custom_ops = {
    identifier: "Minisat::Lit",
    finalize:    custom_finalize_default,
    compare:     custom_compare_default,
    hash:        custom_hash_default,
    serialize:   custom_serialize_default,
    deserialize: custom_deserialize_default
};

// Copy a MiniSat literal into a newly allocated OCaml custom tag 
static inline value copy_minisat_lit( Lit *lit )
{
    CAMLparam0();
    CAMLlocal1(v);
    v = caml_alloc_custom( &minisat_lit_custom_ops, sizeof(Lit), 0, 1);
    memcpy( Data_custom_val(v), lit, sizeof(Lit) );
    CAMLreturn(v);
}


// extern "C" value dummy_unit(value unit)
// {
//   CAMLparam1 (unit);
//   int res = Int_val(0);
//   CAMLreturn(Val_unit);
// }

// extern "C" value dummy_int_id(value int_in)
// {
//   CAMLparam1 (int_in);
//   int in = Int_val(int_in);
//   value res = Val_int(in);
//   CAMLreturn(res);
// }

// external minisat_create_solver : unit -> minisat_solver = "minisat_create_solver" 
extern "C" value minisat_create_solver(value unit)
{

  // Declare parameters 
  CAMLparam1 (unit);

  // Initialise MiniSat instance 
  Solver* s = new Solver;

  // Allocate abstract datatype for MiniSat instance 
  value res = caml_alloc(1, Abstract_tag);
  Store_field(res, 0, (value) s); 

  // Return MiniSat instance 
  CAMLreturn(res);

}

// external minisat_add_var : minisat_solver -> int -> unit = "minisat_add_var"
extern "C" value minisat_add_var (value solver_in, value var_id_in)
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

// external minisat_create_lit : minisat_solver -> int -> bool -> minisat_lit = "minisat_create_lit"
extern "C" value minisat_create_lit(value solver_in, value var_id_in, value sign_in)
{
  
  // Declare parameters 
  CAMLparam3 (solver_in, var_id_in, sign_in);
  CAMLlocal1 (res);

  Solver* solver = (Solver*) Field(solver_in, 0);
  int var_id = Int_val(var_id_in);
  bool sign = Bool_val(sign_in);

  // First declare variable in MiniSat
  while (var_id >= solver->nVars()) solver->newVar();

  // Must use mkLit to create literals 
  Lit lit = sign ? mkLit(var_id) : ~mkLit(var_id);

  printf("Created literal %d from %s%d\n", toInt(lit), sign ? "" : "~", var_id);

  // Allocate and copy MiniSat literal to OCaml
  res = copy_minisat_lit(&lit);

  // Return literal
  CAMLreturn(res);

}

// external minisat_lit_to_int : minisat_solver -> minisat_lit -> int = "minisat_lit_to_int"
extern "C" value minisat_lit_to_int(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);
  Solver* solver = (Solver*) Field(solver_in, 0);
  Lit* lit = (Lit*) Data_custom_val(lit_in);
  
  value res = Val_int(toInt(*lit));
  CAMLreturn(res);

}

// external minisat_add_clause : minisat_solver -> minisat_lit list -> bool = "minisat_add_clause"
extern "C" value minisat_add_clause(value solver_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam2 (solver_in, clause_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  head = clause_in;

  // Clause to be asserted
  vec<Lit> lits;

  printf("Asserting clause ");

  // Iterate list of literals
  while (head != Val_emptylist) 
    {

      // Get head element of list 
      value lit_in = Field(head, 0);

      // Get MiniSat literal from value
      Lit* lit = (Lit*) Data_custom_val(lit_in);

      printf("%d ", toInt(*lit));

      // Add literal to clause 
      lits.push(*lit);

      // Continue with tail of list
      head = Field(head, 1);

    }

  printf("\n");

  // Add clause to solver
  if (solver->addClause(lits))
    {

      // Not immediately unsatisfiable 
      CAMLreturn (Val_true);

    }
  else
    {

      // Immediately unsatisfiable with added clause
      CAMLreturn (Val_false);

    }

}


// external minisat_solve : minisat_solver -> bool = "minisat_solve"
extern "C" value minisat_solve(value solver_in)
{
    
  // Declare parameters 
  CAMLparam1(solver_in);
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Run MiniSat
  int res = solver->solve();

  // Return result
  CAMLreturn(Val_bool(res));
}


// external minisat_solve_assumptions : minisat_solver -> minisat_lit list -> bool = "minisat_solve_assumptions"
extern "C" value minisat_solve_assumptions(value solver_in, value assumptions_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, assumptions_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  head = assumptions_in;

  // Assumptions for solving
  vec<Lit> lits;

  // Only if satisfiable after simplifications
  if (solver->simplify())
    {

      printf("Assuming ");

      // Iterate list of literals
      while (head != Val_emptylist) 
	{
	  
	  // Get head element of list 
	  value lit_in = Field(head, 0);
	  
	  // Get MiniSat literal from value
	  Lit* lit = (Lit*) Data_custom_val(lit_in);
	  
	  printf("%d ", toInt(*lit));
	  
	  // Add literal to assumptions
	  lits.push(*lit);
	  
	  // Continue with tail of list
	  head = Field(head, 1);
	  
	}
      
      printf("\n");

      // Solve with literal assumptions
      if (solver->solve(lits))
	{
	  
	  printf("Satisfiable under assumptions\n");

	  // Satisfiable under assumptions
	  CAMLreturn(Val_int(toInt(l_True)));

	}

      else
	{

	  printf("Unsatisfiable under assumptions\n");

	  // Unsatisfiable under assumptions
	  CAMLreturn(Val_int(toInt(l_False)));

	}

    }

  else  
    {

      printf("Unsatisfiable without assumptions\n");

      // Unsatisfiable without assumptions
      CAMLreturn(Val_int(toInt(l_Undef)));
    }
	
}

// external minisat_fast_solve : minisat_solver -> minisat_lit list -> bool = "minisat_fast_solve"
extern "C" value minisat_fast_solve(value solver_in, value assumptions_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, assumptions_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  head = assumptions_in;

  // Assumptions for solving
  vec<Lit> lits;

  // Only if satisfiable after simplifications
  if (solver->simplify())
    {

      printf("Assuming ");

      // Iterate list of literals
      while (head != Val_emptylist) 
	{
	  
	  // Get head element of list 
	  value lit_in = Field(head, 0);
	  
	  // Get MiniSat literal from value
	  Lit* lit = (Lit*) Data_custom_val(lit_in);
	  
	  printf("%d ", toInt(*lit));
	  
	  // Add literal to assumptions
	  lits.push(*lit);
	  
	  // Continue with tail of list
	  head = Field(head, 1);
	  
	}
      
      printf("\n");

      // No conflicts allowed
      solver->setPropBudget(lits.size());

      // Solve with literal assumptions 
      CAMLreturn(Val_int(toInt(solver->solveLimited(lits))));

    }

  else
    {

      printf("Unsatisfiable without assumptions\n");

      // Unsatisfiable without assumptions
      CAMLreturn(Val_int(toInt(l_Undef)));
      
    }

}


// external minisat_model_value : minisat_solver -> minisat_lit -> int = "minisat_model_value"
extern "C" value minisat_model_value (value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);
  Solver* solver = (Solver*) Field(solver_in, 0);
  Lit* lit = (Lit*) Data_custom_val(lit_in);

  value res = Val_int(toInt(solver->modelValue (*lit)));

  CAMLreturn(res);

}


// external minisat_stat_vars : minisat_solver -> int = "minisat_stat_vars" 
extern "C" value minisat_stat_vars(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Read number of variables 
  int vars = solver->nVars();

  // Return integer
  value res = Val_int(vars);
  CAMLreturn(res);

}

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
  
  Solver* solver = (Solver*) Field(solver_in, 0);
  int var_id = Int_val(var_id_in);
  bool sign = Bool_val(sign_in);

  // First declare variable in MiniSat
  while (var_id + 1 >= solver->nVars()) solver->newVar();

  // Must use mkLit to create literals 
  Lit* plit = new Lit;
  Lit lit = sign ? mkLit(var_id) : ~mkLit(var_id);
  *plit = lit;

  printf("Created literal %d from %d (%d)\n", toInt(lit), sign ? var_id : -var_id, &lit);

  // Allocate for an abstract datatype and fill with literal
  value res = caml_alloc(1, Abstract_tag);
  Store_field(res, 0, (value) plit); 

  // Return literal
  CAMLreturn(res);
}

extern "C" value minisat_lit_to_int(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);
  Solver* solver = (Solver*) Field(solver_in, 0);
  Lit* lit = (Lit*) Field(lit_in, 0);
  
  value res = Val_int(toInt(*lit));
  CAMLreturn(res);

}


// external minisat_add_clause : minisat_solver -> minisat_lit list -> bool = "minisat_add_clause"
extern "C" value minisat_add_clause(value solver_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam2 (solver_in, clause_in);
  Solver* solver = (Solver*) Field(solver_in, 0);

  // Copy list of literals 
  value clause = clause_in;

  // Clause to be asserted
  vec<Lit> lits;

  printf("Asserting clause ");

  // Iterate list of literals
  while (clause != Val_int(0)) 
    {

      // Get head element of list 
      value lit_in = Field(clause, 0);

      // Get MiniSat literal from value
      Lit* lit = (Lit*) Field(lit_in, 0);

      printf("%d ", toInt(*lit));

      // Add literal to clause 
      lits.push(*lit);

      // Continue with tail of list
      clause = Field(clause, 1);

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

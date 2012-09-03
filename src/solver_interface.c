

#include "solver.h"
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>




struct solver_with_memory {
    solver *    solver_ptr;
    veci   *    vector_ptr;
}; 
typedef struct solver_with_memory SolverM;




//SolverM* create_solver_with_memory (solver* solver_in, veci* memory_in);


SolverM* create_solver_with_memory (solver* solver_in, veci* memory_in)
{
//Solver (capital s) here is the "solver with memory" type, not the solver (small s) which is just the normal solver.
  SolverM* solver_mem = (SolverM*)safe_malloc(sizeof(SolverM));
  solver_mem -> solver_ptr = solver_in;
  solver_mem -> vector_ptr = memory_in;
  //    fprintf(stderr, "\n Error Test return\n");
  // exit(EXIT_FAILURE);
  return solver_mem;
}

value C_create_solver(value is_sim_In)
{
  CAMLparam1(is_sim_In);

  solver * s =  solver_new();
  s->verbosity = 0;  

  bool is_sim = Bool_val(is_sim_In);
  if(is_sim)
    {
      s->sim = true;
    }
  else
    {
      s->sim = false;
    }

  // veci  lits;
  //    veci_new(&lits);
  veci* vec_lits = (veci*) safe_malloc(sizeof(veci));
    // vec_lits = &lits;
  veci_new(vec_lits);
  SolverM * solver_m 
    = create_solver_with_memory(s, vec_lits); 			
  value val = alloc(1, Abstract_tag);
  Field(val,0) = (value) solver_m; 
  CAMLreturn(val);
}

//add_var       : solver -> var_id -> unit = "C_add_var"

value C_add_var(value solver_In, value var_In)
{
  CAMLparam2 (solver_In,var_In);
  SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
  solver * solver = solver_mem -> solver_ptr;
  int  var_id = Int_val(var_In);
  if (solver->size <= var_id)
    {solver_setnvars(solver,var_id+1);}
  CAMLreturn(Val_unit);
}


value C_create_lit(value v, value solver_In,value sign_In)
{
  CAMLparam3(v, solver_In,sign_In);

  SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
  solver * solver = solver_mem -> solver_ptr;
    // int i = Long_val(v);
  int  var_id = Int_val(v);
  bool sign = Bool_val(sign_In);
  //sover->size is the number of defined vars 
  // 
  //  {solver_setnvars(solver,var_id+2);}
  // printf("  Var_id: %i \n", var_id);
  // printf(" create_lit (Var_id:) solver->size =%i \n", solver->size);
  // fflush(stdout);
  if (solver->size <= var_id)
    {solver_setnvars(solver,var_id+1);}
  int minisat_lit = (sign ? toLit(var_id) : lit_neg(toLit(var_id)));
  CAMLreturn(Val_int(minisat_lit));
}


value C_add_clause(value clause_In, value solver_In)
{	
    CAMLparam2 (clause_In, solver_In);

    SolverM * solver_mem   = (SolverM *)Field(solver_In, 0);
    solver * solver  = solver_mem -> solver_ptr;
    veci   * lits = solver_mem -> vector_ptr;
	
    int size = Wosize_val(clause_In);
    //  int arr[size];
    int i , temp ;
    veci_resize(lits,0);
    
    for (i = 0; i < size; i++)
    {
      temp = Int_val( Field(clause_In, i) );		
      veci_push(lits, temp);
    }
	
	
    lit* begin = (lit *)veci_begin(lits);
    int n = veci_size(lits);
    if (!solver_addclause(solver, begin, begin+n)){
	
	CAMLreturn (Val_bool(0));
    }
 
    CAMLreturn (Val_bool(1));
}


/*
value C_get_lit_val (value solver_In, value lit_In, value sign_In)
{
  //    CAMLparam2(solver_In, lit_In);
  CAMLparam3(solver_In,lit_In,sign_In);

  SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
  solver  * solver = solver_mem -> solver_ptr;
  bool sign = Bool_val(sign_In);
  int var = lit_var(Int_val(lit_In));


    int* model = veci_begin(&solver->model);
    int model_size = veci_size(&solver->model);
    //  lbool* model = solver->assigns;
    //	fprintf(stdout, "model_size=%i, var_id = %i \n",model_size,var);
    if (var >= model_size)
      {
	fprintf(stderr, "ERROR C_get_lit_val: var has not been defined model_size=%i, var_id = %i \n",model_size,var);
	fflush(stderr);
	fprintf(stdout, "ERROR C_get_lit_val: var has not been defined  \n");
	fflush(stdout);
	exit(EXIT_FAILURE); 
    }


  lbool var_val = model[var];

  if (var_val == l_True)
    {
      if(sign == true)
	{
	  CAMLreturn(Val_int(1));
	}
      
      else
	
	  {
	    CAMLreturn(Val_int(0));
	  }
    }
  
  else 
    if (var_val == l_False)      
      {	
	if(sign == true)
	  {
	    CAMLreturn(Val_int(0));
	  }
	else
	  {
	    CAMLreturn(Val_int(1));
	  }
	
      }
    else      
      if (var_val == l_Undef)
	{
	  CAMLreturn(Val_int(-1));
	}
      else
	{
	  CAMLreturn(Val_int(-2));
	}  
}

*/


value C_get_lit_val (value solver_In, value lit_In)
{
     CAMLparam2(solver_In, lit_In);
     // CAMLparam3(solver_In,lit_In,sign_In);

  SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
  solver  * solver = solver_mem -> solver_ptr;
  int lit = Int_val(lit_In);
  int var = lit_var(lit);
  //sign true if it is a  negative lit
  int sign =lit_sign (lit);

  int* model = veci_begin(&solver->model);
  int model_size = veci_size(&solver->model);
    //  lbool* model = solver->assigns;
    //	fprintf(stdout, "model_size=%i, var_id = %i \n",model_size,var);
    if (var >= model_size)
      {
	fprintf(stderr, "ERROR C_get_lit_val: var has not been defined model_size=%i, var_id = %i \n",model_size,var);
	fflush(stderr);
	fprintf(stdout, "ERROR C_get_lit_val: var has not been defined  \n");
	fflush(stdout);
	exit(EXIT_FAILURE); 
    }


  lbool var_val = model[var];

  if (var_val == l_True)
    {
      //     if(sign == true)
      if (!sign)
	{
	  CAMLreturn(Val_int(l_True));
	}
      
      else	
	  {
	    CAMLreturn(Val_int(l_False));
	  }
    }
  
  else 
     if (var_val == l_False)      
       {	
	 if(!sign)
	   {
	     CAMLreturn(Val_int(l_False));
	   }
	 else
	   {
	     CAMLreturn(Val_int(l_True));
	   }
	
       }
     else      
       if (var_val == l_Undef)
	 {
	   CAMLreturn(Val_int(l_Undef));
	 }
       else
	 {
	   CAMLreturn(Val_int(l_Err)); // should not happen
	 }  
}


value C_solve(value solver_In)
{
    CAMLparam1(solver_In);

    SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
    solver * solver =solver_mem -> solver_ptr;    
    // simplified inside solver_solve in solver.c  
    //    if (solver_simplify(solver))       
    //  {

	    //	    fprintf(stdout,"Before Solve:\n");
	    // fflush(stdout);
	    
    lbool solver_out = solver_solve(solver,0,0);
	    // fprintf(stdout,"After Solve:\n");
	    // fflush(stdout);
	  
    if (solver_out == l_True)
      {
	CAMLreturn(Val_bool(true));
      }
    else 
      {
	CAMLreturn(Val_bool(false));
      }
    //}
	//else
	//{CAMLreturn(Val_bool(0));}
}


value C_fast_solve(value solver_In, value assumptions)
{
  CAMLparam2 (solver_In, assumptions);
    SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
    solver * solver =solver_mem -> solver_ptr;
    veci   * lits = solver_mem -> vector_ptr;
    int size = Wosize_val(assumptions);
    int i , temp ;
    veci_resize(lits,0);
    //    printf ("Debug: Change C_fast_solve: remove solved check!\n ");
    //	    fflush(stdout);
    //     lbool   solver_out_without_ass = solver_solve(solver,0,0);
    // if (solver_out_without_ass == l_True)
    //  {	
	
    if (solver_simplify(solver))
    	  {
	    for (i = 0; i < size; i++)
	      {
		temp = Int_val( Field(assumptions, i) );		
		veci_push(lits, temp);
	      }
	    
	    lit* begin = (lit *)veci_begin(lits);
	    int n = veci_size(lits);
	    //   fprintf(stdout,"Before fast_solve:\n");
	    // fflush(stdout);
	   
	    lbool   solver_out = fast_solve(solver,begin,begin+n);
	    //fprintf(stdout,"After fast_solve:\n");
	    //fflush(stdout);

	    if (solver_out == l_True)
	      { //sat under assumprions
		CAMLreturn(Val_int(l_True));
	      }
	    else 
	      {
		if(solver_out == l_False)
		  {//unsat under assumprions
		    CAMLreturn(Val_int(l_False));}
		else
		  {
		    if(solver_out == l_Undef) 
		      {CAMLreturn(Val_int(l_Err));} //should not happen  
		  }
	      }
	  }
	else
	  { //unsat without assumptions
	    CAMLreturn(Val_int(l_Undef));
	  }
	//	 }
	//else
	// { //unsat without assumptions
	//	CAMLreturn(Val_int(0));
	// }
}



value C_solve_assumptions(value solver_In, value assumptions)
{
  CAMLparam2 (solver_In, assumptions);
    SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
    solver * solver =solver_mem -> solver_ptr;
    veci   * lits = solver_mem -> vector_ptr;
    int size = Wosize_val(assumptions);
    int i , temp ;
    veci_resize(lits,0);    
    //  lbool   solver_out_without_ass = solver_solve(solver,0,0);
    //   if (solver_out_without_ass == l_True)
    //    {	
           if (solver_simplify(solver))
    	 {
	    for (i = 0; i < size; i++)
	      {
		temp = Int_val( Field(assumptions, i) );		
		veci_push(lits, temp);
	      }
	    
	    lit* begin = (lit *)veci_begin(lits);
	    int n = veci_size(lits);
	    lbool solver_out = solver_solve(solver,begin,begin+n);
	    if (solver_out == true)
	  { //sat under assumprions
	    CAMLreturn(Val_int(l_True));
	  }
	    else 
	      { //unsat under assumptions
		CAMLreturn(Val_int(l_False));
	      }
	 }
       else
	 { //unsat without assumptions
	    CAMLreturn(Val_int(l_Undef));
	 }
       //    }
       //else
       // { //unsat without assumptions
	 // CAMLreturn(Val_int(0));
       //}
}


/* value C_add_clause(value clause_In, value solver_In)
{	
    CAMLparam2 (clause_In, solver_In);

    SolverM * solver_mem   = (SolverM *)Field(solver_In, 0);
    solver * solver  = solver_mem -> solver_ptr;
    veci   * lits = solver_mem -> vector_ptr;
	
    int size = Wosize_val(clause_In);
    //  int arr[size];
    int i , temp ;
    veci_resize(lits,0);
    
    for (i = 0; i < size; i++)
    {
      temp = Int_val( Field(clause_In, i) );		
      veci_push(lits, temp);
    }
	
	
    lit* begin = (lit *)veci_begin(lits);
    int n = veci_size(lits);
    if (!solver_addclause(solver, begin, begin+n)){
	
	CAMLreturn (Val_bool(0));
    }
 
    CAMLreturn (Val_bool(1));
}

*/


value C_get_number(value solver_In)
{
    CAMLparam1(solver_In);
    SolverM * s = (SolverM *)Field(solver_In, 0);
    solver * s1 =s -> solver_ptr;
    int i = solver_nvars(s1);
    int m  = solver_nclauses(s1);
    CAMLreturn ( Val_unit ); 
}


value C_print_array(value clause_In)
{
    CAMLparam1(clause_In);
    int size = Wosize_val(clause_In);
    int arr[size];
    
    int i , temp ;
    for (i = 0; i < size; i++)
    {
	temp = Int_val( Field(clause_In, i) );
	if (temp > 0) 
	    arr[i] = temp << 1;
	else
	    arr[i] = temp * (-2) + 1;	
    }

    CAMLreturn ( Val_unit ); 
}



 //end extern "C"

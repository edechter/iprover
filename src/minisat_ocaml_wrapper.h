
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

extern "C" value C_create_solver(value unit);
extern "C" value C_create_lit(value v, value solver_In,value sign_In);
extern "C" value C_add_clause(value clause_In, value solver_In);
extern "C" value C_solve(value solver_In);
extern "C" value C_solve_assumptions(value solver_In, value assumptions);
extern "C" value C_fast_solve(value solver_In, value assumptions);
extern "C" value C_get_lit_val (value solver_In, value lit_In)

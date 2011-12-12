
let main () =

  let solver = Minisat.create_solver false in

  let l = Minisat.create_lit solver true 0 in

  Format.printf 
    ("Solver calls: %d@\n" ^^ 
	"Fast solver calls: %d@\n" ^^ 
	"Variables: %d@\n" ^^ 
	"Clauses: %d@\n@.")
    (Minisat.num_of_solver_calls solver)
    (Minisat.num_of_fast_solver_calls solver)
    (Minisat.num_of_vars solver)
    (Minisat.num_of_clauses solver)

;;

main ()

;;

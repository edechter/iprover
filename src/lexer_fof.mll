(* Lexer for output of clausification from Vampire 

   Very simple: a line beginning with fof(f<n> is concatenated with
   the following lines until there is either
   inference(.*,[],[f<m>]). or file(.,.) at the end of a line.

   The whole line is paired with <m> and stored as the value for key
   <n> in a hash table.
   
*)

{

exception Lexing_error
  
(* Update position in lexing buffer *)
let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
      { pos with
	 Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	 Lexing.pos_bol = pos.Lexing.pos_cnum;
      }

}


(* Definitions of POSIX character classes from Mikmatch *)

let digit = ['0'-'9']

let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let digit = ['0'-'9']
let alnum = alpha | digit
(*KK uncomment punct !*)


let punct = 
  ['!' '\\' '"' '#' '$' '%' '&' '\'' '(' ')' '*' '+' ',' '-' '.' '/' ':' ';' 
     '<' '=' '>' '?' '@' '[' ']' '^' '_' '`' '{' '|' '}' '~']


let graph = alnum | punct
let blank = ' ' | '\t'


(* Entry point for lexer *)
rule line proof = parse

  (* Every line must start with fof( *)
  | "fof(f" (digit+ as fof_id) as fof_head 
  
      { 
	
	(* Format.eprintf "Parsed '%s' with id %s@." fof_head fof_id; *)

	(* Continue with rest of line *)
	cont fof_head fof_id proof lexbuf

      } 

  (* End of file reached *)
  | eof 
      { raise End_of_file }

  (* Nothing else allowed *)
  | _

      { raise Lexing_error }


(* Match continued lines, must use shortest instead of parse *)
and cont fof_head fof_id proof = shortest

  (* Keyword inference found *)
  | blank+ (alpha+ as inference) "(" graph+ ",[],[" as fof_cont 

      { 

	(* Inference rule found? *)
	if inference = "inference" then

	  (

	    (* Format.eprintf "Parsed '%s' @." fof_cont; *)
	  
	    (* Parse lists of parent formulae *)
	    parents (fof_head ^ fof_cont) fof_id proof [] lexbuf

	  )

	else

	  (
	   
	    (* Format.eprintf "Not recognised '%s' as inference keyword@\nParsing '%s' as continued line@." inference fof_cont; *)
	    
	    (* Treat as continued line *)
	    cont (fof_head ^ fof_cont) fof_id proof lexbuf 

	  )
      }

  (* Keyword file found at the end of the line *)
  | blank+ (alpha+ as introduced) "(" graph+ ",[])).\n" as fof_cont

      { 
	
	(* Introduced formula found? *)
	if introduced = "introduced" then
	  
	  (
	    
	    (* Format.eprintf "Parsed '%s' as introduced formula @." fof_cont; *)
	    
	    (* Increment line number *)
	    incr_linenum lexbuf;
	    
	    (* Add line and no parent to hash table *)
	    Hashtbl.add 
	      proof 
	      (int_of_string fof_id) 
	      ((fof_head ^ fof_cont), []);
	    
	    (* Continue with remaining lines *)
	    line proof lexbuf 
	  
	  )
	    
	else

	  (

	    (* Format.eprintf "Not recognised '%s' as introduced keyword@\nParsing '%s' as continued line@." introduced fof_cont; *)


	    (* Treat as continued line *)
	    cont (fof_head ^ fof_cont) fof_id proof lexbuf 
	    
	  )

      }
      
  (* Keyword file found at the end of the line *)
  | blank+ (alpha+ as file) "(" graph+ "," graph+ ")).\n" as fof_cont

      { 
	
	(* File source found? *)
	if file = "file" then
	  
	  (
	    
	    (* Format.eprintf "Parsed '%s' as file source @." fof_cont; *)
	    
	    (* Increment line number *)
	    incr_linenum lexbuf;

	    (* Add line and no parent to hash table *)
	    Hashtbl.add 
	      proof 
	      (int_of_string fof_id) 
	      ((fof_head ^ fof_cont), []);
	    
	    (* Continue with remaining lines *)
	    line proof lexbuf 
	      
	  )

	else
	  
	  (

	    (* Format.eprintf "Not recognised '%s' as file keyword@\nParsing '%s' as continued line@." file fof_cont; *)

	    (* Treat as continued line *)
	    cont (fof_head ^ fof_cont) fof_id proof lexbuf 
	    
	  )

      }

  (* No keywords found until the end of the line *)
  | [^ '\n']* "\n" as fof_cont
      
      { 
	
	(* Format.eprintf "Parsed '%s' as continued line@." fof_cont; *)
	
	(* Increment line number *)
	incr_linenum lexbuf;
	
	(* Append line and continue *)
	cont (fof_head ^ fof_cont) fof_id proof lexbuf 

      }

  (* End of file reached *)
  | eof 
      { raise End_of_file }


and parents fof_head fof_id proof fof_parents = parse

  (* Formula source *)
  | "f" (digit+ as parent_id) as fof_cont 

      { 

	(* Recurse to get possibly multiple parents *)
	parents 
	  (fof_head ^  fof_cont) 
	  fof_id 
	  proof 
	  ((int_of_string parent_id) :: fof_parents) 
	  lexbuf 

      }

  (* Another formula source *)
  | ",f" (digit+ as parent_id) as fof_cont 

      { 
	
	(* Recurse to get possibly multiple parents *)
	parents 
	  (fof_head ^  fof_cont) 
	  fof_id 
	  proof 
	  ((int_of_string parent_id) :: fof_parents) 
	  lexbuf 

      }

  (* End of line *)
  | "])).\n" as fof_cont 

      { 

	(* Increment line number *)
	incr_linenum lexbuf;

	(* Add line and parent to hash table *)
	Hashtbl.add 
	  proof 
	  (int_of_string fof_id) 
	  ((fof_head ^ fof_cont), fof_parents);
	
	(* Continue with remaining lines *)
	line proof lexbuf 

      }

  (* Treat line as continuation *)
  | '\n' as c
      
      {
	
	(* Increment line number *)
	incr_linenum lexbuf;

	(* Continue *)
	cont (fof_head ^ (String.make 1 c)) fof_id proof lexbuf

      }

  (* Treat line as continuation *)
  | _ as c
      
      {
	
	(* Continue *)
	cont (fof_head ^ (String.make 1 c)) fof_id proof lexbuf

      }

{      
	    
  let rec pp_proof_parents ppf = function 
    | [] -> ()
    | [p] -> Format.fprintf ppf "%d" p
    | p :: tl -> 
      pp_proof_parents ppf [p]; 
      Format.fprintf ppf ","; 
      pp_proof_parents ppf tl

  let pp_proof_line ppf f = function
    | s, p->
	Format.fprintf ppf "%d: %a@\n%s@." f pp_proof_parents p s
	  
  let pp_proof ppf p =
    Hashtbl.iter (pp_proof_line ppf) p 

  (* Parse output from channel *)
  let parse proof ch_in =

    (* Lexbuf from input channel *)
    let lexbuf = Lexing.from_channel ch_in in
      
      try 
	
	(* Parse output *)
	line proof lexbuf
	  
      with 

	| End_of_file -> 

	    (* All formulae are in hash table *)
	    ()

	| Lexing_error ->

	    (* Clear hash table *)
	    Hashtbl.clear proof

(*
(* Test function *)
let main () =
  
  (* Open channel to stdin or file if given *)
  let ch_in =
    if Array.length Sys.argv > 1
    then open_in Sys.argv.(1)
    else stdin
  in
    
  (* Pass empty result *)
  let proof = Hashtbl.create 100 in
    
    (* Parse output *)
    parse proof ch_in;
    
    (* Output result *)
    Format.printf "%a" pp_proof proof;
    
;;

  main ()
;;

*)
	  
}

(* -----------------------------------------------f-----------------------(C)- *)
(* Copyright (C) 2006-2012 Konstantin Korovin and The University of        *)
(* Manchester. This file is part of iProver - a theorem prover for         *)
(* first-order logic. iProver is free software: you can redistribute it    *)
(* and/or modify it under the terms of the GNU General Public License as   *)
(* published by the Free Software Foundation, either version 3 of the      *)
(* License, or (at your option) any later version. iProver is distributed  *)
(* in the hope that it will be useful, but WITHOUT ANY WARRANTY; without   *)
(* even the implied warranty of MERCHANTABILITY or FITNESS FOR A           *)
(* PARTICULAR PURPOSE. See the GNU General Public License for more         *)
(* details. You should have received a copy of the GNU General Public      *)
(* License along with iProver. If not, see <http://www.gnu.org/licenses/>. *)
(* ----------------------------------------------------------------------[C]- *)

(* to generate mli use "ocamlc -I obj/ -i src/parser_types.ml > src/parser_types.mli" *)

open Lib
open Statistics
(* can not open Logic_interface since its uses dbs defined here *)

exception Parsing_fails
exception FOF_format
exception TFF_format
exception THF_format

type var = Var.var
type term = Term.term
type clause = Clause.clause
module SymbMap = Symbol.Map

type buffer_name = 
  |FileName of string
  |Stdin


let buffer_name_to_string bn =
  match bn with 
  |FileName str -> str 
  |Stdin -> "stdin"
	

(* init_lexbuf should be applied before lexing, for coorect line counting *)
let position_init_lnum position =
  { Lexing.pos_fname = position.Lexing.pos_fname;
    Lexing.pos_lnum = 1;
    Lexing.pos_bol = position.Lexing.pos_bol;
    Lexing.pos_cnum = position.Lexing.pos_cnum;}

let buffer_name_ref = ref Undef

let init_lexbuf buffer_name lexbuf =
  buffer_name_ref := Def (buffer_name);
  lexbuf.Lexing.lex_curr_p <- (position_init_lnum lexbuf.Lexing.lex_curr_p)

type includes =
    {includes_file_name : string;
     include_formula_list : string list;
     include_source_file_name : buffer_name; (* full file name of the buffer where include is *)
   }

(* not used type parser_state = { symbol_db_ref : SymbolDB.symbolDB ref;   *)
(* term_db_ref : TermDB.termDB ref; mutable parsed_clauses : clause list;  *)
(* (* parsed clauses does not include negated_conjectures                  *)
   mutable neg_conjectures : clause list;
   mutable includes : includes list;

(* auxilary fields used during parsing max_var is used for renaming vars   *)
(* into iprover vars                                                       *)
   mutable max_var : var;
   mutable var_table : (string, var) Hashtbl.t;
(* mutable current_is_neg_conj : bool; *)
   }

(* not used *)
   let init_parser_state () =
   {
   symbol_db_ref = ref (SymbolDB.create_name "Symbols_DB");
   term_db_ref = ref (TermDB.create_name "Terms_DB");
   parsed_clauses = [];
   neg_conjectures = [];
   includes = [];
   max_var = Var.get_first_var();
   var_table = Hashtbl.create 1001;
(* current_is_neg_conj = false; *)
   }

(* we do not renew just keep global maping from names to vars *)
   let renew_var_table state =
   state.var_table <- (Hashtbl.create 1001)

   let parser_state = init_parser_state ()
 *)

(* ----------------Parser Out------------------------------- *)

let symbol_db_ref = ref (SymbolDB.create_name "Symbols_DB")
let term_db_ref = ref (TermDB.create_name "Terms_DB")

(*----------------*)
(* let context = Clause.context_create 21701 (* 21701 medium large prime number; context not used at the moment *) *) 

(*
   let create_clause tstp_source lits = 
   let clause = Clause.create_clause term_db_ref tstp_source lits in 
   Clause.context_add context clause 
 *)
let create_clause tstp_source lits = 
  let clause = Clause.create_clause term_db_ref tstp_source lits in
  clause 
(*	Clause.context_add context clause *)

(*
   let create_neg_conjecture tstp_source lits = 
   let clause = Clause.create_neg_conjecture term_db_ref tstp_source lits	in
   Clause.context_add context clause 
 *)

let create_neg_conjecture tstp_source lits = 
  let clause = Clause.create_neg_conjecture term_db_ref tstp_source lits	in
  clause 
(*	Clause.context_add context clause*) 

    
(*----------------*)	

let () = Statistics.assign_fun_stat
    (fun () -> TermDB.size !term_db_ref) Statistics.num_of_terms

let () = Statistics.assign_fun_stat
    (fun () -> SymbolDB.size !symbol_db_ref) Statistics.num_of_symbols

(* parsed_clauses does not include neg_conjectures *)
let parsed_clauses = ref []
let neg_conjectures = ref []
let includes = ref []
let less_map = ref SymbMap.empty
let range_map = ref SymbMap.empty

(* Clock symbols: mapped to pairs of integers, first is the initial value  *)
(* of the clock (0 for negative, 1 for positive), second is the period of  *)
(* the clock                                                               *)
let clock_map = ref SymbMap.empty

(* Symbols with cardinality: in BMC1 if the state_type symbol has a        *)
(* cardinality, this is meant to be the maximal bound plus one (bounds are *)
(* 0-based                                                                 *)
let cardinality_map = ref SymbMap.empty

(* Symbols with maximal address width: associates to an address type the   *)
(* maximal width of the addresses                                          *)
let max_address_width_map = ref SymbMap.empty

(* State symbols: associates the state to a state symbol *)
let state_constant_map = ref SymbMap.empty

(* Symbols with base names: the symbol for a higher bound is obtained by   *)
(* appending the bound to the base name                                    *)
let address_base_name_map = ref SymbMap.empty

(* maps symbol into list of strings which this symbol is the father of *)
let father_of_map = ref SymbMap.empty

let bit_vector_name_map = ref SymbMap.empty
let memory_name_map     = ref SymbMap.empty

let distinct : (((term list) list) ref) = ref []
(* list of $distinct(t_1,..,t_n) represented   *)
(* as list of lists of terms note distinct are *)
(* not in added to the clauses!                *)

let all_current_clauses : ((clause list) ref) = ref [] 

let get_clauses_without_extra_axioms () = (!neg_conjectures)@(!parsed_clauses)


let bot_term = TermDB.add_ref (Term.create_fun_term Symbol.symb_bot []) term_db_ref
let top_term = TermDB.add_ref (Term.create_fun_term Symbol.symb_top []) term_db_ref



let is_less_symb symb =
  SymbMap.mem symb !less_map

let is_range_symb symb =
  SymbMap.mem symb !range_map

let is_clock_symb symb =
  SymbMap.mem symb !clock_map

let is_less_or_range_symb symb =
  (is_less_symb symb) || (is_range_symb symb)

(* ---------------Auxilary tables-----------------------------             *)
(* ---------var table is a global mapping var_names -> vars---             *)

let default_var_type = Symbol.symb_default_type

(* at the moment input vars are not typed we create terms with variables   *)
(* over the default type and then retype before building the formula       *)
let max_var_ref = ref (Var.get_first_var default_var_type)
let var_table_ref : (((string, var) Hashtbl.t) ref) = ref (Hashtbl.create 1001)

(* we can init all references *)
let init () =
  (* symbol_db_ref := (SymbolDB.create_name "Symbols_DB"); term_db_ref :=    *)
  (* (TermDB.create_name "Terms_DB");                                        *)
  parsed_clauses := [];
  neg_conjectures := [];
  includes := [];
  distinct := [];
  all_current_clauses := [];
  less_map := SymbMap.empty;
  range_map := SymbMap.empty;
  clock_map := SymbMap.empty;
  cardinality_map := SymbMap.empty;
  max_address_width_map := SymbMap.empty;
  state_constant_map := SymbMap.empty;
  address_base_name_map := SymbMap.empty;
  father_of_map := SymbMap.empty;
  bit_vector_name_map := SymbMap.empty;
  memory_name_map := SymbMap.empty;
  (* ignore (TermDB.add_ref bot_term term_db_ref); ignore (TermDB.add_ref    *)
  (* top_term term_db_ref);                                                  *)
  max_var_ref := (Var.get_first_var default_var_type);
  var_table_ref := (Hashtbl.create 1001)

let get_clauses_without_extra_axioms () = (!neg_conjectures)@(!parsed_clauses)

(* aux functions *)

(* future: add arity check *)
let create_theory_term theory_symb args =
  Symbol.assign_is_input true theory_symb;
  Symbol.incr_num_input_occur theory_symb;
  TermDB.add_ref (Term.create_fun_term theory_symb args) term_db_ref

(* ----------------parsing functions-------------- terms are put to TermDB *)
(* during Clause.normalise                                                 *)

(* dummy fun for comments/annatations, can be changed in the future *)

let include_file_fun file_name formula_names =
  let new_include =
    { includes_file_name = file_name;
      include_formula_list = formula_names;
      include_source_file_name = get_param_val !buffer_name_ref
    }
  in
  includes := new_include::!includes

let comment_fun str = ()
let comment_E_prover_fun str = ()
let annotation_fun str = ()

let contains_distinct = ref false

let analyse_distinct lit_list =
  contains_distinct:= false;
  match lit_list with
  | [term] ->
      (
       match term with
       | Term.Fun(symb, args, _inf) ->
	   if (symb == Symbol.symb_distinct)
	   then
	     distinct:= (Term.arg_to_list args)::!distinct
	   else
	     failwith "analyse_distinct"
       | _ -> failwith "analyse_distinct"
      )
  | [] -> ()
  | _ -> failwith "analyse_distinct: distinct is only supported as a unit clause"

(* we do not rename vars at this point just change type *)
(* ttype val type of t; need this since vars are not yet typed and types are propagated from arguments *)
let rec retype_term ttype t =
  match t with
  | Term.Fun (sym, args, _) ->
      (* for typed equality eq(type_term_eq, t, s) types of t, s equal to  *)
      (* top_type to type                                                  *)
      let arg_list = (Term.arg_to_list args) in
      let new_args =
	begin
	  if (sym == Symbol.symb_typed_equality)
	  then
	    let (type_term_eq, t, s) = get_triple_from_list arg_list in
	    let eq_v_type =
	      try
		Term.get_top_symb type_term_eq
	      with Term.Var_term ->
		failwith "equality should not have var as the type argument"
	    in
	    let new_eq_terms = retype_term_list [eq_v_type; eq_v_type] [t; s]
	    in
	    type_term_eq:: new_eq_terms
	  else
	    let (arg_types, _val_type) = Symbol.get_stype_args_val_def sym
	    in
	    retype_term_list
	      arg_types
	      arg_list	      
	end
      in
      Term.create_fun_term sym new_args
	
  | Term.Var (v, _ ) ->
      let new_var =
	Var.create ttype (Var.get_var_val v) 
      in
      (Term.create_var_term new_var)
and
    retype_term_list type_list term_list =
  let f rest ttype t =
    (retype_term ttype t):: rest in
  let rev_new_list = List.fold_left2 f [] type_list term_list in
  List.rev rev_new_list

let retype_lit lit = 
  retype_term Symbol.symb_bool_type lit
    
    
let retype_lits lits =
  List.map retype_lit lits
    
let cnf_formula_fun name role formula annotations =
  incr_int_stat 1 num_of_input_clauses;
  if !contains_distinct
  then
    analyse_distinct formula
  else
    begin
      let retyped_lits = retype_lits formula in
      let tstp_source =	Clause.tstp_source_input "" name in
      
      match role with
      |"negated_conjecture" | "question" ->
	  (
	   incr_int_stat 1 num_of_input_neg_conjectures;
	   let neg_conj = create_neg_conjecture tstp_source retyped_lits in
	   neg_conjectures := neg_conj::!neg_conjectures
	  )
      | _ ->
	  (let new_clause = create_clause tstp_source retyped_lits in 
	  parsed_clauses := new_clause::!parsed_clauses
	  )
    end

(* Redo with the separate parsing for predicates !!! *)

(* Can not use assign_type, since it is part of the key ! let              *)
(* plain_atomic_formula_fun term = (* twice as much memory /time if you    *)
(* use this line ... don't know why... shift it to the end                 *)
(* Symbol.assign_type Symbol.Pred (Term.get_top_symb term);                *)
   Symbol.assign_type_pred (Term.get_top_symb term);
   term
 *)

let is_false_lit lit =
  let top_symb = Term.lit_get_top_symb lit in
  if (Term.is_neg_lit lit)
  then
    if (top_symb == Symbol.symb_true)
    then
      true
    else
      false
  else
    if (top_symb == Symbol.symb_false)
    then
      true
    else
      false

let disjunction_fun rest lit =
  if (is_false_lit lit)
  then
    rest
  else
    lit:: rest

(* let equality_fun term1 term2 = create_theory_term Symbol.symb_equality  *)
(* [term1;term2]                                                           *)

let equality_fun args =
  (* no all equalities are sorted and = is replaces by                     *)
  (* $equality_sorted(symb_default_type, args)                             *)
  let default_type_term = create_theory_term Symbol.symb_default_type [] in
  create_theory_term Symbol.symb_typed_equality (default_type_term:: args)

let inequality_fun args =
  create_theory_term Symbol.symb_neg [(equality_fun args)]

let neg_fun atom =
  create_theory_term Symbol.symb_neg [atom]

let assign_param_input_symb symb =
  (* Symbol.set_bool_param (is_clock_symb symb) Symbol.is_clock symb;        *)
  (* Symbol.set_bool_param (is_less_symb symb) Symbol.is_less symb;          *)
  (* Symbol.set_bool_param (is_range_symb symb) Symbol.is_range symb;        *)
  Symbol.assign_is_input true symb;
  Symbol.incr_num_input_occur symb

(* future: add negated_conjecture stuff after parsing symbol types:        *)
(* Pred/Fun are needed for e.g. eq axioms !                                *)
let plain_term_fun symb_name symbol_type args =
  let symb =
    SymbolDB.add_ref
      (Symbol.create_from_str_type
	 symb_name symbol_type)
      symbol_db_ref in
  assign_param_input_symb symb;
  
  (* (if !current_is_neg_conjecture then Symbol.set_bool_param true          *)
  (* Symbol.is_conj_symb symb); out_str ("Symb: " ^(Symbol.to_string symb)   *)
  (* ^" is conj symb: " ^ (string_of_bool (Symbol.get_bool_param             *)
  (* Symbol.is_conj_symb symb ))^"\n"); let args = list_map_left             *)
  (* (parsed_term_to_term var_map_ref Symbol.Fun) parsed_term_list in        *)
  Term.create_fun_term symb args

(* we assume that all symbols in terms are typed already! and added to     *)
(* SymbolDB.add_ref                                                        *)

let overriding_arities_warning_was_shown_ref = ref false

let plain_term_fun_typed ~is_top input_symb_name args =
  (* we check that the arity is the same for the untyped symbols if current  *)
  (* symbol has an occurence in DB with different arity then all occurences  *)
  (* with new arities will be prefexed by $$iProver_arity_symname we do not  *)
  (* do full type checking at the moment                                     *)
  let symb_name_ref = ref input_symb_name in
  let arity = List.length args in
  let symb =
    try
      begin	
	let symb = SymbolDB.find
	    (Symbol.create_template_key_symb !symb_name_ref) !symbol_db_ref in
	
	if ((Symbol.get_arity symb) = arity ) && (is_top = (Symbol.is_pred symb)) && (not (symb == Symbol.symb_neg))
	then
	  (symb)
	else
	  begin
	    ( if (not !overriding_arities_warning_was_shown_ref) &&
	      (not ((Symbol.get_arity symb) = arity))
	    then
	      (
	       out_warning
		 (
		  "plain_term_fun_typed: symbol "^(!symb_name_ref)
		  ^" occurred with two arities: "
		  ^(string_of_int (Symbol.get_arity symb))
		  ^" and "^(string_of_int arity)
		  ^" the latter will be replaced by fresh symbol (other similar warnings are surpressed)\n"
		 );
	       overriding_arities_warning_was_shown_ref:= true
	      )
	    else ()
	     );
	    ( if (not !overriding_arities_warning_was_shown_ref) &&
	      (not  (is_top = (Symbol.is_pred symb)))
	    then
	      (
	       out_warning
		 ("plain_term_fun_typed: symbol "^(!symb_name_ref)
		  ^" occurred as function and as predicate "
		  ^" on of them will be replaced by fresh symbol (other similar warnings are surpressed)\n"
		 );
	       overriding_arities_warning_was_shown_ref:= true
	      )
	    else ()
	     );
	    ( if (not !overriding_arities_warning_was_shown_ref) &&
	      (symb == Symbol.symb_neg)
	    then
	      (
	       out_warning
		 ("plain_term_fun_typed: symbol "^(!symb_name_ref)
		  ^" occurred as function or predcate"
		  ^" and will be replaced by a fresh symbol (other similar warnings are surpressed)\n"
		 );
	       overriding_arities_warning_was_shown_ref:= true
	      )
	    else ()
	     );

	    let pred_fun_str =
	      if is_top
	      then "pred"
	      else "fun"
	    in
	    symb_name_ref:=
	      ("$$iProver_"^"arity_"^(string_of_int arity)^"_"
	       ^pred_fun_str^"_"^(!symb_name_ref));
	    
	    let new_symb = SymbolDB.find
		(Symbol.create_template_key_symb !symb_name_ref) !symbol_db_ref in
	    (* at this point we assume that the arity problem is fixed ! *)
	    assert ((Symbol.get_arity new_symb) = arity);
	    new_symb
	      
	  end
      end
	
    with
      Not_found ->
	( let stype =
	  (* is a predicate *)
	  if is_top then
	    Symbol.create_stype
	      (list_n arity Symbol.symb_default_type) Symbol.symb_bool_type
	  else
	    (* is a fun *)
	    Symbol.create_stype
	      (list_n arity Symbol.symb_default_type) Symbol.symb_default_type
	in
	let symb = SymbolDB.add_ref
	    (Symbol.create_from_str_type
	       (* ~is_sig:true it is a signature symbol *)
	       ~is_sig: true !symb_name_ref stype) symbol_db_ref in
	symb
	 )
	  (* failwith ("parser_types, plain_term_fun_typed type of symbol "          *)
	  (* ^symb_name^" was not declared")                                         *)
	  
  in
  assign_param_input_symb symb;
  Term.create_fun_term symb args
(* terms are not added to termDB at this point but added when the clause   *)
(* is created                                                              *)

(* (if !current_is_neg_conjecture then Symbol.set_bool_param true          *)
(* Symbol.is_conj_symb symb); out_str ("Symb: " ^(Symbol.to_string symb)   *)
(* ^" is conj symb: " ^ (string_of_bool (Symbol.get_bool_param             *)
(* Symbol.is_conj_symb symb ))^"\n"); let args = list_map_left             *)
(* (parsed_term_to_term var_map_ref Symbol.Fun) parsed_term_list in        *)

let defined_term_fun name args =
  match name with
  |"$sum" 
      (* -> create_theory_term Symbol.symb_plus args *)
  |"$difference" 
    (*  -> create_theory_term Symbol.symb_minus args*)
  |"$product" 
     (* -> create_theory_term Symbol.symb_product args *)
  |"$uminus" 
    (* ->  create_theory_term Symbol.symb_unaryminus args *)
     -> failwith (name^" is not supported")
  |"$i" ->
      create_theory_term Symbol.symb_default_type args
  |"$o" ->
      create_theory_term Symbol.symb_bool_type args
	
  | _ -> failwith ("Parsing error: unsupported defined function \""^name^"\"")

let defined_pred_fun name args =
  match name with
  |"=" ->
      (* no all equalities are sorted and = is replaces by                   *)
      (* $equality_sorted(symb_default_type, args) create_theory_term        *)
      (* Symbol.symb_equality args                                           *)
      equality_fun args
	
  |"$true" ->
      create_theory_term Symbol.symb_true args
  |"$false" ->
      create_theory_term Symbol.symb_false args
  |"$$equality_sorted" | "$equality_sorted" -> (* temporaly leave $equality_sorted *)
      create_theory_term Symbol.symb_typed_equality args
	
  |"$distinct" ->
      (contains_distinct:= true;
       create_theory_term Symbol.symb_distinct args
      )
	(* moved to system symbols |"$answer" | "$$answer" |"\'$$answer\'" ->      *)
	(* answer_mode_ref := true; create_theory_term Symbol.symb_answer args     *)
  | _ -> failwith ("Parsing error: unsupported defined predicate \""^name^"\"")

let defined_infix_pred_fun pred_symb term1 term2 =
  defined_pred_fun pred_symb [term1; term2]

(* let defined_prop_fun name = () let defined_pred_fun name = *)

let reg_exp_less = Str.regexp_string "$$less_"
let reg_exp_range = Str.regexp_string "$$range_"
let reg_exp_clock = Str.regexp_string "$$bmc1_clock_"

let system_pred_name_pref_reg_expr =
  Str.regexp
    (Str.quote "$$less_"^"\\|"^
     Str.quote "$$range_"^"\\|"^
     Str.quote "$$bmc1_clock_")

let system_pred_fun name args =
  
  match name with
    
    (* Next state predicate for BMC1 *)
  | "$$nextState" ->
      create_theory_term Symbol.symb_ver_next_state args
	(* Create term like plain term plain_term_fun_typed true name args *)
	
	(* Reachable state predicate for BMC1 *)
  | "$$reachableState" ->
      create_theory_term Symbol.symb_ver_reachable_state args
	(* Create term like plain term plain_term_fun_typed true name args *)
	
	(* Less predicate for BMC1 | term when (try String.sub term 0 7 =      *)
	(* "$$less_" with
	   | Invalid_argument _ -> false ->
	   
	   (* Create term like plain term *)
	   plain_term_fun_typed true name args
	   
	   (* Range predicate for BMC1 *)
	   | term when
	   (try
	   String.sub term 0 8 = "$$range_"
	   with
	   | Invalid_argument _ -> false) ->
	   
	   (* Create term like plain term *)
	   plain_term_fun_typed true name args
	   
	 *)
	(* Sorted equality *)
  | "$$equality_sorted" ->
      
      create_theory_term Symbol.symb_typed_equality args
	
  |"$answer" | "$$answer" |"\'$$answer\'" ->
      (
       answer_mode_ref := true;
       
       let arity = List.length args in
       (* --check arity compatibility with previous answer pred---- *)
       
       (if (Symbol.is_arity_def Symbol.symb_answer) &&
	 (not ((Symbol.get_arity Symbol.symb_answer) == arity))
       then failwith "Only one arity for answer predicates is supported"
       );
       let stype =
	 Symbol.create_stype
	   (list_n arity Symbol.symb_default_type) Symbol.symb_bool_type
       in
       Symbol.assign_arity arity Symbol.symb_answer;
       Symbol.assign_stype Symbol.symb_answer stype;
       Symbol.assign_is_input true Symbol.symb_answer;
       Symbol.incr_num_input_occur Symbol.symb_answer;
       
       (* let symb = SymbolDB.add_ref (Symbol.create_from_str_type ~is_sig:true   *)
       (* it is a signature symbol ~is_sig:true symb_name stype) symbol_db_ref in *)
       
       create_theory_term Symbol.symb_answer args
      )
  | pred_name
    when
      (Str.string_match system_pred_name_pref_reg_expr pred_name 0) ->
	plain_term_fun_typed true name args
	  
  | _ ->
      
      (* Alternative: create as plain term without catching undefined *)
      failwith ("Parsing error: unsupported system predicate \""^name^"\"")

(*let constB_base_str = "$$constB"*)


let system_term_fun name args =
  
  match name with
    
    (* State constant for BMC1 *)
  | term when
      (try
	String.sub term 0 8 = "$$constB"
      with
      | Invalid_argument _ -> false) ->
	  
	  (* Create term like plain term *)
	  plain_term_fun_typed false name args
	    
	    (* bitindex term for BMC1 *)
  | term when
      (try
	String.sub term 0 10 = "$$bitIndex"
      with
      | Invalid_argument _ -> false) ->
	  
	  (* Create term like plain term *)
	  plain_term_fun_typed false name args
	    
  | _ ->
      
      (* Alternative: create as plain term without catching undefined *)
      failwith ("Parsing error: unsupported system term \""^name^"\"")

let term_variable_fun var =
  Term.create_var_term var

let variable_fun var_name =
  try
    Hashtbl.find !var_table_ref var_name
  with
    Not_found ->
      (
       let current_var = !max_var_ref in
       Hashtbl.add !var_table_ref var_name current_var;
       max_var_ref := (Var.get_next_var !max_var_ref);
       current_var
      )

(* change later on the number type *)

let num_term name =
  let symb = SymbolDB.add_ref
      (Symbol.create_from_str_type
	 name (Symbol.create_stype [] Symbol.symb_default_type)) symbol_db_ref in
  assign_param_input_symb symb;
  Term.create_fun_term symb []

let term_of_int_number_fun num =
  let name = (string_of_int num) in
  num_term name

let term_of_rat_number_fun (num, denum) =
  let name = (string_of_int num)^"/"^(string_of_int denum) in
  num_term name

let term_of_real_number_fun real =
  let name = real_to_string real in
  num_term name

(* -------------ttf--------------- Note $tType will be of $tType *)
let ttf_atomic_type_fun symb_name =
  let symb = SymbolDB.add_ref
      (Symbol.create_type_symb_from_str
	 (* ~is_sig:true since can occur in typed equalities *)
	 ~is_sig: true symb_name) symbol_db_ref in
  assign_param_input_symb symb;
  symb

let is_bound_constant_type stype =
  match (Symbol.get_stype_args_val stype) with
  | Def([], value) -> (value == Symbol.symb_ver_state_type)
  | _ -> false

let ttf_add_typed_atom_out_symb_fun symb_name stype =
  let symb =
    (Symbol.create_from_str_type symb_name stype)
  in
  let added_symb = SymbolDB.add_ref symb symbol_db_ref in
  (if (is_bound_constant_type symb)
  then
    Symbol.set_bool_param true Symbol.is_bound_constant added_symb
  else ()
  );
  if (Symbol.is_special_symbol added_symb)
      (* (Symbol.is_defined_type added_symb) || (Symbol.is_defined_symb ) *)
  then
    ( assign_param_input_symb added_symb;
      added_symb
     )
  else
    if (symb == added_symb)
    then
      (symb)  (* added_symb *) (*just return unit*)
    else
      failwith
	("parser_types, ttf_add_typed_atom_out_fun: symbol \""
	 ^symb_name
	 ^"\" was already declared!")

let ttf_add_typed_atom_fun symb_name stype =
  ignore (ttf_add_typed_atom_out_symb_fun symb_name stype)

type attr_args =
    (* Attr_Interval of int * int *)
  | Attr_List of int list
  | Attr_Int of int
  | Attr_Str of string

type attr_type =
  | ALess of int
  | ARange of int * int
	
  | AFatherOf of string
  | ASonOf of string
	
	(* A clock symbol with initial value (first) and period (second) *)
  | AClock of int list
	
	(* Cardinality of a type, currently used to determine the maximal bound in *)
	(* BMC1. The maximal bound is the value of $cardinality of the state_type  *)
	(* minus one, since states are 0-based.                                    *)
  | ACardinality of int
	
	(* A symbol for a state, usually $$constB0 *)
  | AStateConstant of int
	
	(* Base name of address term, the current bound is to be appended to the   *)
	(* base name                                                               *)
  | AAddressBaseName of string
	
	(* Maximal width of addresses, usually for address_type *)
  | AAddressMaxWidth of int

	(* size of the bv *)
  | ABitVector of int 
 
	(* AMemory: (bit-size of addresses) * (memory_word_size) *)
  | AMemory of int * int
	
  | AOther of string * attr_args

type attr =
    Attr of attr_type * attr_args

let attr_fun attr_name attr_args =
  match attr_name with
  |"less"
  |"$less"
  |"$$less" ->
      (match attr_args with
      | Attr_Int (int) -> ALess int
      | _ -> failwith "less should have one argument: int"
      )
	
  |"range"
  |"$range"
  |"$$range" ->
      (match attr_args with
      | Attr_List [i1; i2] -> ARange (i1, i2)
      | _ -> failwith "range should have one argument: interval"
      )
	
  | "clock"
  | "$clock"
  | "$$clock" ->
      (match attr_args with
      | Attr_List p -> AClock p
      | _ -> failwith "clock should have one argument: clock pattern"
      )
	
  |"father_of"
  |"$father_of"
  |"$$father_of" ->
      (match attr_args with
      | Attr_Str(str) -> AFatherOf(str)
      | _ -> failwith "father_of should have one argument: string  "
      )
	
  | "son_of"
  | "$son_of"
  | "$$son_of" ->
      (match attr_args with
      | Attr_Str(str) -> ASonOf(str)
      | _ -> failwith "son_of should have one argument: string  "
      )
	
  | "cardinality"
  | "$cardinality"
  | "$$cardinality" ->
      (match attr_args with
      | Attr_Int c -> ACardinality c
      | _ -> failwith "cardinality should have one argument: integer")
	
  | "addressMaxWidth"
  | "$addressMaxWidth"
  | "$$addressMaxWidth" ->
      (match attr_args with
      | Attr_Int c -> AAddressMaxWidth c
      | _ -> failwith "addressMaxWidth should have one argument: integer")
	
  | "state_constant"
  | "$state_constant"
  | "$$state_constant" ->
      (match attr_args with
      | Attr_Int c -> AStateConstant c
      | _ -> failwith "state_constant should have one argument: integer")
	
  | "address_base_name"
  | "$address_base_name"
  | "$$address_base_name" ->
      (match attr_args with
      | Attr_Str c -> AAddressBaseName c
      | _ -> failwith "address_base_name should have one argument: integer")

  |"$bit_vector"
  |"$constant_bit_vector" ->
      (match attr_args with
      | Attr_Int (int) -> ABitVector int
      | _ -> failwith "bit-vector should have one argument: int"
      )
  |"$memory" -> 
      (match attr_args with
      | Attr_List [i1; i2] -> AMemory (i1, i2)
      | _ -> failwith "memory should have one argument: interval"
      )
	
  | other_str -> AOther (other_str, attr_args)

(* returns (Some(range/less), Some(AFatherOF str_list)) can raise          *)
(* Not_found                                                               *)

let find_recognised_main_attr attr_list =
  try
    Some
      (List.find
	 (fun attr ->
	   match attr with
	   | ALess _
	   | ARange _
	   | AClock _
	   | ACardinality _
	   | AAddressMaxWidth _
	   | AStateConstant _
	   | AAddressBaseName _ 
	   | ABitVector _ 
	   | AMemory _
	     -> true
	   | _ -> false
	 )
	 attr_list
      )
  with
    Not_found -> None

let get_all_father_of attr_list =
  let f rest attr =
    match attr with
    | AFatherOf str -> (str:: rest)
    | _ -> rest
  in
  List.fold_left f [] attr_list

let is_defined_symbol attr_list =
  List.exists
    (fun attr ->
      match attr with
	AFatherOf _ | ASonOf _ -> true
      | _ -> false)
    attr_list

let ttf_add_typed_atom_atrr_fun symb_name stype attr_list =
  let symb = ttf_add_typed_atom_out_symb_fun symb_name stype in
  let attr = find_recognised_main_attr attr_list in
  (* fill less/range *)
  (match attr with
  | Some(ALess i) ->
      if (SymbMap.mem symb !less_map)
      then ()
      else
	(
	 less_map := SymbMap.add symb i !less_map;
	 Symbol.set_bool_param true Symbol.is_less symb
	)
  | Some(ARange (i, j)) ->
      if (SymbMap.mem symb !range_map)
      then ()
      else
	(
	 range_map := SymbMap.add symb (i, j) !range_map;
	 Symbol.set_bool_param true Symbol.is_range symb
	)
	  
	  (* Symbol is a clock with pattern p *)
  | Some (AClock p) ->
      
      (* Clock symbol already defined? *)
      if (SymbMap.mem symb !clock_map) then
	
	(* Skip *)
	()
	  
      else
	
	(
	 
	 (* Sanity check: pattern must not be empty *)
	 if p = [] then
	   failwith
	     (Format.sprintf
		"Bad $clock attribute for symbol %s: pattern must not be empty"
		(Symbol.to_string symb));
	 
	 (* Sanity check: all elements in list must be 0 or 1 *)
	 if List.exists (fun e -> not (e = 0 || e = 1)) p then
	   failwith
	     (Format.sprintf
		"Bad $clock attribute for symbol %s: pattern must contain only 0 and 1"
		(Symbol.to_string symb));
	 
	 (* Add symbol to map *)
	 clock_map := SymbMap.add symb p !clock_map;
	 Symbol.set_bool_param true Symbol.is_clock symb
	)
	  
	  (* Symbol has cardinality c *)
  | Some (ACardinality c) ->
      
      (* Cardinality of symbol already defined? *)
      if (SymbMap.mem symb !cardinality_map) then
	
	(* Skip *)
	()
	  
      else
	
	(
	 
	 (* Sanity check: cardinality must not be zero or less *)
	 if c < 1 then
	   failwith
	     (Format.sprintf
		"Bad $cardinality attribute for symbol %s: must be positive and not zero"
		(Symbol.to_string symb));
	 
	 (* Add symbol to map *)
	 cardinality_map := SymbMap.add symb c !cardinality_map
	     
	)
	  
	  (* Symbol has a maximal address width *)
  | Some (AAddressMaxWidth c) ->
      
      (* Maximal address width of symbol already defined? *)
      if (SymbMap.mem symb !max_address_width_map) then
	
	(* Skip *)
	()
	  
      else
	
	(
	 
	 (* Sanity check: must not negative *)
	 if c < 0 then
	   failwith
	     (Format.sprintf
		"Bad address_max_width attribute for symbol %s: must be positive"
		(Symbol.to_string symb));
	 
	 (* Add symbol to map *)
	 max_address_width_map := SymbMap.add symb c !max_address_width_map
	     
	)
	  
	  (* Symbol is a state constant *)
  | Some (AStateConstant c) ->
      
      (* State of symbol already defined? *)
      if (SymbMap.mem symb !state_constant_map) then
	
	(* Skip *)
	()
	  
      else
	(	 
	 (* Sanity check: state constant must not be negative *)
	 if c < 0 then
	   failwith
	     (Format.sprintf
		"Bad state_constant attribute for symbol %s: must be positive"
		(Symbol.to_string symb));
	 
	 (* Add symbol to map *)
	 state_constant_map := SymbMap.add symb c !state_constant_map
	     
	)
	  
	  (* Symbol has a base name *)
  | Some (AAddressBaseName c) ->
      
      (* Base name of symbol already defined? *)
      if (SymbMap.mem symb !address_base_name_map) then
	
	(* Skip *)
	()
	  
      else
	
	(
	 
	 (* Add symbol to map *)
	 address_base_name_map := SymbMap.add symb c !address_base_name_map
	     
	)
  | Some (ABitVector i) ->       
      if (SymbMap.mem symb !bit_vector_name_map) then	
	(* Skip *)
	()	  
      else	
	(	 
	   (* Add symbol to map *)
	   bit_vector_name_map := SymbMap.add symb i !bit_vector_name_map	     
	  )

  | Some(AMemory (i, j)) ->
      if (SymbMap.mem symb !memory_name_map)
      then ()
      else
	(
	 memory_name_map := SymbMap.add symb (i, j) !memory_name_map;
	)
	    
  | _ -> ()
  );
  (
   if (is_defined_symbol attr_list)
   then
     (Symbol.set_bool_param true Symbol.is_defined_symb_input symb)
   else ()
  );
  (* fill father_of map *)
  let all_father_of = get_all_father_of attr_list in
  if ((all_father_of = []) || (SymbMap.mem symb !father_of_map))
  then () (* should not happen since symb is defined only once *)
  else
    (
     father_of_map := SymbMap.add symb all_father_of !father_of_map
    )

(* -------------All below is commented------------------------ type tmp =  *)
(* string type language = CNF | FOF type name = string type parsed_symbol  *)
(* = string type parsed_variable = string type theory_term =
   | Equality of parsed_term * parsed_term
   | NegEquality of parsed_term * parsed_term
   | True
   | False
   | PositiveInteger of int
   | RealNumber of int * int
   | Plus of parsed_term * parsed_term
   | Minus of parsed_term * parsed_term
   | UnaryMinus of parsed_term

   and user_term =
   | Fun of parsed_symbol * (parsed_term list)
(* |Var of parsed_variable *)

   and parsed_term =
   | TheoryTerm of theory_term
   | UserTerm of user_term
   | Var of parsed_variable

   type binary_connective =
   | And
   | NegAnd
   | Or
   | NegOr
   | Equivalence
   | NegEquivalence
   | ImplicationLR
   | ImplicationRL

   type unary_connective = Negation
   type atom = parsed_term
   type quantifier = Exists | ForAll
   type variables = parsed_variable list

(* parsing gives more restrictive from: but it is not needed *)
   type formula =
   | Atom of atom
   | QuantifiedFormula of quantifier * variables * formula
   | UnaryFormula of unary_connective * formula
   | BinaryFormula of binary_connective * formula * formula

   type user_type =
   | Axiom | Hypothesis | Conjecture | Negated_conjecture
   | Lemma | Theorem | Plain | Unknown

   type source_type = Derived

   type formula_type =
   | UserSourceType of user_type * source_type
   | UserType of user_type
   | SourceType of source_type

   type source = tmp
   type useful_info = tmp

   type formula_annotation =
   | Source of source
   | Source_UsefulInfo of source * useful_info

   type comment = string
   type annotation = string
   type file_name = string
   type formula_selection = string list

   type top_element =
   | Formula of language * name * formula_type * formula * (formula_annotation list)
   | Include of file_name * formula_selection
   | Annotation of annotation
   | Comment of comment
   | CommentEprover of comment

   type parsing_type = top_element list

(* --------to_string functions------------- *)
   let init_spacing = "   "
   let language_to_string = function
   | CNF -> "cnf"
   | FOF -> "fof"

   let parsed_symbol_to_string s = s
   let parsed_variable_to_string s = s

   let rec theory_term_to_string = function
   | Equality(parsed_term1, parsed_term2) ->
   (parsed_term_to_string parsed_term1)^"="^(parsed_term_to_string parsed_term2)
   | NegEquality(parsed_term1, parsed_term2) ->
   (parsed_term_to_string parsed_term1)^"!="^(parsed_term_to_string parsed_term2)
   | True -> "$true"
   | False -> "$false"
   | PositiveInteger(int) -> string_of_int int
   | RealNumber(int1, int2) -> (string_of_int int1)^"."^(string_of_int int2)
   | Plus(parsed_term1, parsed_term2) ->
   (parsed_term_to_string parsed_term1)^"+"^(parsed_term_to_string parsed_term2)

   | Minus (parsed_term1, parsed_term2) ->
   (parsed_term_to_string parsed_term1)^"-"^(parsed_term_to_string parsed_term2)

   | UnaryMinus(parsed_term) -> (parsed_term_to_string parsed_term)

   and user_term_to_string = function
   | Fun(parsed_symbol, parsed_term_list) ->
   let symb_str = (parsed_symbol_to_string parsed_symbol) in
   if parsed_term_list = [] then
   symb_str
   else
   let args_str =
   list_of_str_to_str (List.map parsed_term_to_string parsed_term_list) ","
   in symb_str^"("^args_str^")"

(* |Var(parsed_variable) -> parsed_variable_to_string      *)
(* parsed_variable                                         *)

   and parsed_term_to_string = function
   | TheoryTerm(theory_term) -> theory_term_to_string theory_term
   | UserTerm(user_term) -> user_term_to_string user_term
   | Var(parsed_variable) -> parsed_variable_to_string parsed_variable

   let binary_connective_to_string = function
   | And ->"&"
   | NegAnd ->"~&"
   | Or ->"|"
   | NegOr ->"~|"
   | Equivalence ->"<=>"
   | NegEquivalence ->"<~>"
   | ImplicationLR ->"=>"
   | ImplicationRL ->"<="

   let unary_connective_to_string = function
   Negation -> "~"

   let atom_to_string = parsed_term_to_string

   let quantifier_to_string quantifier =
   match quantifier with
   | Exists -> "?"
   | ForAll -> "!"

   let parsed_varible_to_string s = s

   let variables_to_string variable_list =
   "["^(list_of_str_to_str (List.map parsed_varible_to_string variable_list) ",")^"]"

   let rec formula_to_string = function
   | Atom(atom) -> atom_to_string atom
   | QuantifiedFormula(quantifier, variables, formula) ->
   (quantifier_to_string quantifier)^(variables_to_string variables)^":"
   ^(formula_to_string formula)

   | UnaryFormula(unary_connective, formula) ->
   (unary_connective_to_string unary_connective)^(formula_to_string formula)
   | BinaryFormula(binary_connective, formula1, formula2) ->
   "("^(formula_to_string formula1)^"\n"
   ^init_spacing^(binary_connective_to_string binary_connective)
   ^(formula_to_string formula2)^")"

   let user_type_to_string = function
   | Axiom -> "axiom" | Hypothesis -> "hypothesis" | Conjecture -> "conjecture"
   | Negated_conjecture -> "negated_conjecture" | Lemma -> "lemma" | Theorem -> "theorem"
   | Plain -> "plain" | Unknown -> "unknown"

   let source_type_to_string = function
   Derived ->"derived"

   let formula_type_to_string = function
   | UserSourceType(user_type, source_type) ->
   (user_type_to_string user_type)^"-"^(source_type_to_string source_type)

   | UserType(user_type) -> user_type_to_string user_type
   | SourceType(source_type) -> source_type_to_string source_type

   let source_to_string s = s
   let useful_info_to_string s = s
   let formula_selection_to_string formula_selection =
   (list_of_str_to_str formula_selection ",")

   let formula_annotation_to_string = function
   | Source(source) -> source_to_string source
   | Source_UsefulInfo(source, useful_info) ->
   (source_to_string source)^","^(useful_info_to_string useful_info)

   let formula_annotation_list_to_string formula_annotation_list =
   "["^( list_of_str_to_str
   (List.map formula_annotation_to_string
   formula_annotation_list) ",")^"]"

   let top_element_to_string = function
   | Formula (language, name, formula_type, formula, (formula_annotation_list)) ->
   let lang = language_to_string language and
   form_type = formula_type_to_string formula_type and
   form = formula_to_string formula in
   if formula_annotation_list = [] then
   lang^"("^name^","^form_type^",\n"^init_spacing^form^").\n"
   else
   let annot = formula_annotation_list_to_string formula_annotation_list in
   lang^"("^name^","^form_type^",\n"^init_spacing^form^","^annot^").\n"

   | Include (file_name, formula_selection) ->
   "include("^file_name^","^(formula_selection_to_string formula_selection)^").\n"

   | Annotation(annotation) -> annotation^"\n"
   | Comment(comment) -> comment^"\n"
   | CommentEprover(comment) -> comment^"\n"

   let parsing_type_to_string parsing_type =
   let list_top_elem_str = List.map top_element_to_string parsing_type in
   list_of_str_to_str list_top_elem_str "\n"

 *)

exception Parsing_fails
exception FOF_format
exception TFF_format
exception THF_format
type var = Var.var
type term = Term.term
type clause = Clause.clause
module SymbMap :
  sig
    type key = Symbol.Key.t
    type 'a t = 'a Map.Make(Symbol.Key).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
val position_init_lnum : Lexing.position -> Lexing.position
val init_lexbuf : Lexing.lexbuf -> unit
type includes = {
  includes_file_name : string;
  include_formula_list : string list;
}
val symbol_db_ref : SymbolDB.symbolDB ref
val term_db_ref : Clause.term_db ref
val parsed_clauses : Clause.clause list ref
val neg_conjectures : Clause.clause list ref
val includes : includes list ref
val less_map : int SymbMap.t ref
val range_map : (int * int) SymbMap.t ref
val clock_map : int list SymbMap.t ref
val cardinality_map : int SymbMap.t ref
val max_address_width_map : int SymbMap.t ref
val state_constant_map : int SymbMap.t ref
val address_base_name_map : string SymbMap.t ref
val father_of_map : string list SymbMap.t ref
val distinct : term list list ref
val all_current_clauses : clause list ref
val bot_term : TermDB.term
val top_term : TermDB.term
val is_less_symb : SymbMap.key -> bool
val is_range_symb : SymbMap.key -> bool
val is_clock_symb : SymbMap.key -> bool
val is_less_or_range_symb : SymbMap.key -> bool
val default_var_type : Symbol.symbol
val max_var_ref : var ref
val var_table_ref : (string, var) Hashtbl.t ref
val init : unit -> unit
val get_clauses_without_extra_axioms : unit -> Clause.clause list
val create_theory_term : Term.symbol -> Term.term list -> TermDB.term
val include_file_fun : string -> string list -> unit
val comment_fun : 'a -> unit
val comment_E_prover_fun : 'a -> unit
val annotation_fun : 'a -> unit
val contains_distinct : bool ref
val analyse_distinct : Term.term list -> unit
val retype_term : Var.symbol -> Term.term -> Term.term
val retype_term_list : Var.symbol list -> Term.term list -> Term.term list
val retype_lit : Term.term -> Term.term
val retype_lits : Term.term list -> Term.term list
val cnf_formula_fun : string -> string -> Term.term list -> 'a -> unit
val is_false_lit : Term.literal -> bool
val disjunction_fun : Term.literal list -> Term.literal -> Term.literal list
val equality_fun : TermDB.term list -> TermDB.term
val inequality_fun : TermDB.term list -> TermDB.term
val neg_fun : Term.term -> TermDB.term
val assign_param_input_symb : Symbol.symbol -> unit
val plain_term_fun : string -> Symbol.stype -> Term.term list -> Term.term
val overriding_arities_warning_was_shown_ref : bool ref
val plain_term_fun_typed :
  is_top:bool -> string -> Term.term list -> Term.term
val defined_term_fun : string -> Term.term list -> TermDB.term
val defined_pred_fun : string -> TermDB.term list -> TermDB.term
val defined_infix_pred_fun :
  string -> TermDB.term -> TermDB.term -> TermDB.term
val reg_exp_less : Str.regexp
val reg_exp_range : Str.regexp
val reg_exp_clock : Str.regexp
val system_pred_name_pref_reg_expr : Str.regexp
val system_pred_fun : string -> Term.term list -> TermDB.term
val system_term_fun : string -> Term.term list -> Term.term
val term_variable_fun : Term.var -> Term.term
val variable_fun : string -> var
val num_term : string -> Term.term
val term_of_int_number_fun : int -> Term.term
val term_of_rat_number_fun : int * int -> Term.term
val term_of_real_number_fun : Lib.real -> Term.term
val ttf_atomic_type_fun : string -> SymbolDB.symbol
val is_bound_constant_type : Symbol.symbol -> bool
val ttf_add_typed_atom_out_symb_fun :
  string -> Symbol.stype -> SymbolDB.symbol
val ttf_add_typed_atom_fun : string -> Symbol.stype -> unit
type attr_args = Attr_List of int list | Attr_Int of int | Attr_Str of string
type attr_type =
    ALess of int
  | ARange of int * int
  | AFatherOf of string
  | ASonOf of string
  | AClock of int list
  | ACardinality of int
  | AStateConstant of int
  | AAddressBaseName of string
  | AAddressMaxWidth of int
  | AOther of string * attr_args
type attr = Attr of attr_type * attr_args
val attr_fun : string -> attr_args -> attr_type
val find_recognised_main_attr : attr_type list -> attr_type option
val get_all_father_of : attr_type list -> string list
val is_defined_symbol : attr_type list -> bool
val ttf_add_typed_atom_atrr_fun :
  string -> Symbol.stype -> attr_type list -> unit

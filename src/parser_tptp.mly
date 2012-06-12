%{
open Lib 
open Parser_types
   
 let disquote_string  str = 
      String.sub str 1 ((String.length str)-2)
 let parse_error s = raise Parser_types.Parsing_fails
%}

%nonassoc Equality NegEquality 
%token Comma Dot Column LeftParen RightParen LBrace RBrace

/* logic */
%token True False ForAll Exists And NegAnd Or NegOr 
       Equality NegEquality Negation ImplicationLR
       ImplicationRL Equivalence NegEquivalence



/* nubers */
/* %token <string> PositiveInteger Zero_numeric Non_zero_numeric */

%token <string> Positive_Decimal Decimal Decimal_fraction 

%token Plus Minus Slash Exponent

/* extra */
%token Star Arrow Less_Sign

/* key words */
%token CNF FOF TFF THF Include

/* extra token to separate similar states */
%token STATE_SEP

/* words */
%token <string> UpperWord
%token <string> LowerWord
%token <string> DollarWord
%token <string> DollarDollarWord
%token <string> String
%token <string> QuotedStr

/* comments annotations */
 %token <string> CommentPercent
 %token <string> CommentEprover
 %token <string> CommentStar 
 %token <string> AnnotationPercent 
 %token <string> AnnotationStar 

/* eof */
%token  EOF


%nonassoc Equivalence
%nonassoc NegEquivalence
%left  ImplicationRL
%right ImplicationLR
%right Or 
%right NegOr
%right And 
%right NegAnd 
%nonassoc ForAll Exists Negation 
%right Plus Minus
%nonassoc UnaryMinus 
%start main
%type <unit> main
%%


main :   /* empty */  {} 
 | main unit {}
 | EOF       {}
;



unit :
   annotated_formula {$1}
 | include_file      {$1} 
 | comment           {$1} 
 | annotation        {$1}
;


include_file : 
     Include LeftParen file_name formula_selection RightParen Dot
     {include_file_fun $3 $4}
;

file_name : single_quoted {$1}
;

formula_selection :      
     /* empty */ {[]}
 | Comma name_list {$2} /* name_list is in reverse order */
;

name_list : 
 name {[$1]}
 | name_list Comma name {$3::$1}
;

comment : 
  CommentPercent {comment_fun ($1)}
 |CommentStar    {comment_fun ($1)}
 |CommentEprover {comment_E_prover_fun ($1)}
;

/*%-----Annotations */

annotation :
  AnnotationPercent {annotation_fun ($1)}
 |AnnotationStar    {annotation_fun ($1)}
;
 

annotated_formula :
     CNF LeftParen name Comma formula_role Comma  
     cnf_formula formula_annotations RightParen Dot {(cnf_formula_fun $3 $5 $7 $8)}
 |FOF {raise FOF_format}
/* |TFF {raise TFF_format} */
 |THF {raise THF_format}
/* parse only type/fun/pred type declarations */
/* | TFF LeftParen name Comma type_word Comma type_name Column tff_typed_atom RightParen  Dot {tff_type_declaration_fun type_name typ_declaration} */
  |TFF LeftParen name Comma type_word Comma tff_typed_atom RightParen  Dot {$7}
/*{tff_type_declaration_fun type_name typ_declaration} */
  
;

type_word : 
 LowerWord { 
    if $1 = "type" 
    then $1 
    else failwith "tff: only type declarations are supported at the moment"}

type_name : functor_name {$1} 

tff_typed_atom :  						       
   tff_untyped_atom Column tff_top_level_type {ttf_add_typed_atom_fun $1 $3}
  |tff_untyped_atom Column tff_top_level_type Or attr_list 
      {ttf_add_typed_atom_atrr_fun $1 $3 (List.rev $5)}
  |LeftParen tff_typed_atom RightParen {$2}

attr_list : 
    attr {[$1]}
  | attr_list Or attr {$3::$1}

attr : 
   defined_functor LeftParen attr_name Comma attr_args  RightParen 
      {match $1 with 
      |"$attr" ->
	  attr_fun $3 $5
      |_-> raise Parser_types.Parsing_fails
(*failwith ("parsing failes: should be $attr in place of "^$1)*)
     }

attr_name : 
 functor_name {$1}
  |defined_functor {$1}
  |system_functor {$1}
 

attr_args : 
      unsigned_integer {Attr_Int ($1)}
/*  |attr_interval {$1} */
  | attr_list_arg { Attr_List $1 } 
  | attr_str_arg { Attr_Str $1 }

attr_str_arg :
      functor_name {$1}
  |defined_functor {$1}

/*
attr_interval :
  LBrace number Comma number RBrace {Attr_Interval ($2, $4)}
*/

attr_list_arg : 
  | LBrace attr_list_arg_list RBrace { $2 }
      
attr_list_arg_list :
  | unsigned_integer { [$1] }
  | unsigned_integer Comma attr_list_arg_list { $1 :: $3 }

tff_untyped_atom : 
  | functor_name {$1}
  | defined_functor {$1}
  | system_functor {$1}


tff_top_level_type : 
    tff_atomic_type {Symbol.create_stype []  $1}
| tff_mapping_type {$1}

tff_atomic_type : 
    atomic_word {ttf_atomic_type_fun $1}
|defined_type   {ttf_atomic_type_fun $1}

defined_type : DollarWord {$1} |  DollarDollarWord {$1}
/* $oType | $o | $iType | $i | $tType |
                         $real | $rat | $int */

tff_mapping_type : 
      tff_unitary_type Arrow tff_atomic_type 
      {Symbol.create_stype $1 $3}
     |LeftParen tff_unitary_type RightParen Arrow tff_atomic_type 
      {Symbol.create_stype $2 $5}
     | LeftParen tff_mapping_type RightParen {$2}


tff_unitary_type : 
	 tff_atomic_type {[$1]}
     | LeftParen tff_xprod_type RightParen {List.rev $2}

/* write reversed version the use List.rev*/
tff_xprod_type : 
    tff_atomic_type Star tff_atomic_type  {[$3;$1]}
     |tff_xprod_type  Star tff_atomic_type  {$3::$1}
     |LeftParen tff_xprod_type RightParen {$2}


/*--------------------------------------*/

formula_annotations : 
     /* empty */ {""}
 |Comma {""} /*,<source><optional_info> */


cnf_formula :
     LeftParen disjunction RightParen {$2}
 |disjunction {$1}
;

disjunction : 
     literal {disjunction_fun [] $1}
 |disjunction Or literal {disjunction_fun $1 $3 }
;

literal : 
 atomic_formula {$1}
 |fol_infix_unary {$1} 
 |Negation atomic_formula {neg_fun $2}
 |Negation LeftParen atomic_formula RightParen {neg_fun $3}


fol_infix_unary : 
     term  NegEquality term {inequality_fun [$1;$3]} 


atomic_formula : 
 | plain_atomic_formula   {$1} 
 | defined_atomic_formula {$1} 
 | system_atomic_formula  {$1}


/* we need to separate atomic_formulas from */
/* terms since we at this stage distinguish predicate symbols from function symbols */

/* plain_atomic_formula : 
    plain_term {$1} */

plain_atomic_formula : 
   functor_name {plain_term_fun_typed true $1 []} /* constant predicate */
  |functor_name LeftParen arguments RightParen 
      {plain_term_fun_typed true $1 $3}


/*predicate_name : atomic_word {$1}*/

plain_term  : 
  functor_name {plain_term_fun_typed false $1 []} /* constant */
  |functor_name LeftParen arguments RightParen {plain_term_fun_typed false $1 $3}

/* constant : functor_name {$1} */

functor_name  : atomic_word {$1}

arguments : 
      arguments_rev {List.rev $1}

arguments_rev :  
     term {[$1]}
 |arguments_rev Comma term {$3::$1} /* arguments are in reverse order */

term : 
     function_term {$1}
 |variable {term_variable_fun $1}
/* |conditional_term */

/*condition_term : */

variable : 
  UpperWord {variable_fun $1}

function_term : 
 | plain_term {$1}
 | defined_term {$1}
 | system_term {$1}

defined_term        : 
 | defined_atom {$1}
 | defined_atomic_term {$1}

defined_atom : 
 | number {$1}
 /*|    distinct_object */

defined_atomic_term : 
 | defined_plain_term {$1}

defined_plain_term  : 
 | defined_functor {defined_term_fun $1 []} /* constant */
 | defined_functor LeftParen arguments RightParen { defined_term_fun $1 $3}

system_term : 
 | system_functor {system_term_fun $1 []} /* constant */
 | system_functor LeftParen arguments RightParen { system_term_fun $1 $3}


/* defined_functor :  $itett | $uminus | $sum | $difference 
                   | $product | $to_int | $to_rat | $to_real

   defined_pred : 
    $equal | $distinct | $itef |
    $less | $lesseq | $greater | $greatereq | $evaleq |
    $is_int | $is_rat

 defined_prop :  $true | $false
   
   defined_functor's, preds etc. are recognised later by functions
 */


defined_functor : 
  | Equality {"="}
  | DollarWord {$1} 
	  
system_functor :
  | DollarDollarWord {$1}

  
/* defined_pred :  	   DollarWord{$1} */

/* do not have defined_pred since it would lead to reduce/reduce conflicts */


defined_atomic_formula : 
  defined_plain_formula {$1} 
 |defined_infix_formula {$1} 

system_atomic_formula : 
  system_plain_formula {$1} 


defined_plain_formula : 
   defined_functor  {defined_pred_fun $1 []} /* constant pred */ 
  |defined_functor LeftParen arguments RightParen { defined_pred_fun $1 $3} 
   
system_plain_formula : 
   system_functor  {system_pred_fun $1 []} /* constant pred */ 
  |system_functor LeftParen arguments RightParen { system_pred_fun $1 $3} 
   


/* 
defined_plain_formula : 
defined_plain_term  {$1} */


defined_infix_formula : 
      term defined_infix_pred term  {defined_infix_pred_fun $2 $1 $3}

defined_infix_pred :  infix_equality {$1}

infix_equality : Equality {"="} /*{Symbol.symb_equality} */


formula_role : LowerWord {$1}

/*------------Numbers---------------------*/
number : 
 integer {(term_of_int_number_fun $1)}
 |rational {(term_of_rat_number_fun $1)} 
 |real  {(term_of_real_number_fun $1)}  




rational :
  signed_rational {$1} | unsigned_rational {$1}

signed_rational :
     Plus unsigned_rational {$2}
   |Minus unsigned_rational 
  { 
   let (num,denom) = $2 in
   (-num,denom)
  }

unsigned_rational : 
     Decimal Slash Decimal {
   let num = int_of_string $1 in 
   let denom = int_of_string $3 in
   if denom > 0 then 
     ((int_of_string $1),(int_of_string $3))
   else 
     failwith ("Parsing: division by zero in "^$1^"/"^$3)
}


real  : 
  signed_real {$1} | unsigned_real {$1}

signed_real : 
     Plus unsigned_real {$2}
    |Minus unsigned_real {
      let real = $2 in 
      real.real_fraction <- (~-. (real.real_fraction)); 
      real }

unsigned_real : decimal_fraction {$1} | decimal_exponent {$1} 


decimal_fraction : Decimal_fraction 
  {
   let real = 
     {
      real_fraction = float_of_string $1;
      real_exponent = 0
    }
   in real
 } 
  
decimal_exponent :
  Decimal Exponent integer {
  let real = 
      {
       real_fraction = float_of_string $1;
       real_exponent = $3}
  in real 
  }
 | Decimal_fraction Exponent integer
   {
    let real = 
      {
       real_fraction = float_of_string $1;
       real_exponent = $3}
   in real 
  }



integer : 
 signed_integer {$1}
 | unsigned_integer {$1}

signed_integer  : 
 Plus unsigned_integer {$2}
 |Minus unsigned_integer {-$2}

unsigned_integer : Decimal {int_of_string $1}

/*--------------------------------------*/

name : 
     atomic_word {$1}
 |integer_string {$1}

atomic_word : 
     LowerWord {$1}
 |single_quoted {$1}


single_quoted : 
     QuotedStr {disquote_string $1}

integer_string :
     Decimal {$1}
 |Plus Decimal {("+"^$2)}
 |Minus Decimal {("-"^$2)}

/*
integer :
  signed_integer 
 |unsigned_integer
*/

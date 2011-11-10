type token =
  | Equality
  | NegEquality
  | Comma
  | Dot
  | Column
  | LeftParen
  | RightParen
  | LBrace
  | RBrace
  | True
  | False
  | ForAll
  | Exists
  | And
  | NegAnd
  | Or
  | NegOr
  | Negation
  | ImplicationLR
  | ImplicationRL
  | Equivalence
  | NegEquivalence
  | PositiveInteger of (string)
  | Plus
  | Minus
  | Star
  | Arrow
  | Less_Sign
  | CNF
  | FOF
  | TFF
  | THF
  | Include
  | STATE_SEP
  | UpperWord of (string)
  | LowerWord of (string)
  | DollarWord of (string)
  | DollarDollarWord of (string)
  | String of (string)
  | QuotedStr of (string)
  | CommentPercent of (string)
  | CommentEprover of (string)
  | CommentStar of (string)
  | AnnotationPercent of (string)
  | AnnotationStar of (string)
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit

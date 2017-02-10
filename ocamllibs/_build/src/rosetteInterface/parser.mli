
(* The type of tokens. *)

type token = 
  | TRUE
  | STRING of (string)
  | RPAREN
  | PLUS
  | OR
  | NULL
  | NOT
  | NIL
  | NEQ
  | MUL
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LOAD
  | LIST
  | LETREC
  | LET
  | LEQ
  | LAMBDA
  | INT of (int)
  | IF
  | ID of (string)
  | GT
  | GEQ
  | FORCE
  | FLOAT of (float)
  | FALSE
  | EQ
  | EOF
  | DIV
  | DELAY
  | DEFINEREC
  | DEFINE
  | CONS
  | CDR
  | CAR
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.expr list)

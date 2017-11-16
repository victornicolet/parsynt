{
open Rparser
exception LexError of string
open Conf



let keywords =
    [
     "set-logic", SETLOGIC;
     "define-sort", DEFSORT;
     "declare-var", DECLVAR;
     "declare-fun", DECLFUN;
     "define-fun", DEFFUN;
     "synth-fun", SYNTHFUN;
     "constraint", CONSTRAINT;
     "check-synth", CHECKSYNTH;
     "set-options", SETOPTIONS;
     "BitVec", BITVECSORT;
     "Array", ARRAYSORT;
     "Int", INTSORT;
     "Bool", BOOLSORT;
     "Enum", ENUMSORT;
     "Real", REALSORT;
     "Constant", CONSTANT;
     "Variable", VARIABLE;
     "InputVariable", INPUTVARIABLE;
     "LocalVariable", LOCALVARIABLE;
     "let", LET;
     "if", IF;
     "true", TRUE;
     "false", FALSE;
    ]

let keyword_tbl = Hashtbl.create 256
let uncurry f (a, b) = f a b
let _ = List.iter (uncurry (Hashtbl.replace keyword_tbl)) keywords
}

let specialchar = ['_', '+', '−', '*', '&', '|', !, '~', '<', '>', '=', '/', '%', '?', '.', '$', '^']
let digit = ['0'-'9']
let alpha =['a'-'z' 'A'-'Z']
let alphanumeric = (alpha | digit)
let id = (alpha | specialchar) (alphanumeric | specialchar)*
let nl = ['\n' '\r']
let ws = ['\n' '\t' '\r' ' ']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = '-'? digit* frac? exp?
let int = '-'? digit digit*

rule token = parse
  | id as id	      { try Hashtbl.find keyword_tbl id with Not_found -> SYMBOL id }
  | "("               { LPAREN }
  | ")"               { RPAREN }
  | "::"	      { DOUBLECOLON }
  | int as int        { INT (int_of_string int) }
  | float as float    { FLOAT (float_of_string float)}
  | ws                { token lexbuf }
  | ";"               { comment lexbuf }
  | '"'		      { QUOTED (string lexbuf) }
  | eof               { EOF }
  | _                 { raise (LexError ("Unexpected char: "^(Lexing.lexeme lexbuf))) }

and string = parse
    "\\\\"           { "\\" :: (string lexbuf) }
  | "\\\""           { "\"" :: (string lexbuf) }
  | "\\n"            { "\n" :: (string lexbuf) }
  | "\\t"            { "\t" :: (string lexbuf) }
  | "\""             { [] }
  | '"'		     { token lexbuf }
  | _ as c           { (String.make 1 c) :: (string lexbuf) }

(* comments *)
and comment = parse
    nl               { token lexbuf }
  | eof              { EOF }
  | _                { comment lexbuf }

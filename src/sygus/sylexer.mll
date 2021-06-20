{
open Syparser
exception LexError of string



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
     "true", TRUE;
     "false", FALSE;
    ]

let keyword_tbl = Hashtbl.create 256
let uncurry f (a, b) = f a b
let _ = List.iter (uncurry (Hashtbl.replace keyword_tbl)) keywords
}

let specialchar = ['_' '+' '-' '*' '&' '|' '!' '~' '<' '>' '=' '/' '%' '?' '.' '$' '^']
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
let bvconst = '#' ('x' digit+ | 'x' alphanumeric+)

rule token = parse
  | id as id	      { try Hashtbl.find keyword_tbl id with Not_found -> SYMBOL id }
  | "("               { LPR }
  | ")"               { RPR }
  | "::"	      { DOUBLECOLON }
  | int as int        { INT (int_of_string int) }
  | float as float    { REAL (float_of_string float)}
  | bvconst as bv     { BITVECTOR bv }
  | ws                { token lexbuf }
  | ";"               { comment lexbuf }
  | '"'		      { let buffer = Buffer.create 1 in QUOTED (stringl buffer lexbuf) }
  | eof               { EOF }
  | _                 { raise (LexError ("Unexpected char: "^(Lexing.lexeme lexbuf))) }


and  stringl buffer = parse
 | '"' { Buffer.contents buffer }
 | "\\t" { Buffer.add_char buffer '\t'; stringl buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; stringl buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; stringl buffer lexbuf }
 | '\\' '"' { Buffer.add_char buffer '"'; stringl buffer lexbuf }
 | '\\' '\\' { Buffer.add_char buffer '\\'; stringl buffer lexbuf }
 | eof { raise End_of_file }
 | _ as char { Buffer.add_char buffer char; stringl buffer lexbuf }

(* comments *)
and comment = parse
    nl               { token lexbuf }
  | eof              { EOF }
  | _                { comment lexbuf }

{
open Rparser
exception LexError of string

let keywords =
    [
     "lambda", LAMBDA;
     "let", LET;
     "if", IF;
     "define", DEFINE;
     "list", LIST;
     "cons", CONS;
     "car", CAR;
     "cdr", CDR;
     "nil", NIL;
     "null", NULL;
     "load", LOAD;
     "letrec", LETREC;
     "definerec", DEFINEREC;
     "delay", DELAY;
     "force", FORCE;
     "not", NOT;
     "min", MIN;
     "max", MAX;
     "(ArithBinops 0)", ARITHBINOPS;
     "(BasicUnopsNum 0)", BASICUNOPSNUM;
     "(ScalarOps 0)", SCALAROPS;
     "(ComparisonOps 0)" , COMPARISONOPS;
     "(BasicBinopsNum 0)" , BASICBINOPSNUM;
     "(NLBinopsNum 0)" , NLBINOPSNUM;
     "(BinopsBool 0)" , BINOPSBOOL;
     "NumExprArith" , NUMEXPRARITH;
     "NumExprNL" , NUMEXPRNL;
     "NumExprBasic" , NUMEXPRBASIC;
     "BoolExpr" , BOOLEXPR;
     "BoolExprCompar" , BOOLEXPRCOMPAR;
     "NumIte" , NUMITE;
     "ScalarExpr" , SCALAREXPR;
     "choose" , CHOOSE;
     "Scalar", SCALAR;
    ]

let keyword_tbl = Hashtbl.create 256
let uncurry f (a, b) = f a b
let _ = List.iter (uncurry (Hashtbl.replace keyword_tbl)) keywords
}

let id = ['_' 'a'-'z' 'A'-'Z' '$'] ['-' '$' '_' '#' '.' '\'' 'A'-'Z' 'a'-'z' '0'-'9']*
let nl = ['\n' '\r']
let ws = ['\n' '\t' '\r' ' ']
let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
let int = '-'? ['0'-'9'] ['0'-'9']*

rule token = parse
    id as id	{ try Hashtbl.find keyword_tbl id with Not_found -> ID id }
  | "'"	  	      { QUOTE }
  | "("               { LPAREN }
  | ")"               { RPAREN }
  | "+"               { PLUS }
  | "\""              { STRING (String.concat "" (string lexbuf)) }
  | "-"               { MINUS }
  | "*"               { MUL }
  | "/"               { DIV }
  | "~"		      { NOT }
  | "%"               { MOD }
  | "??"	      { CONST_CHOICE }
  | "&&"              { AND }
  | "||"              { OR }
  | "="               { EQ }
  | "!="              { NEQ }
  | "<"               { LT }
  | "<="              { LEQ }
  | ">"               { GT }
  | ">="              { GEQ }
  | "#t"              { TRUE }
  | "#f"              { FALSE }
  | int as int        { INT (int_of_string int) }
  | float as float    { FLOAT (float_of_string float)}
  | ws                { token lexbuf }
  | ";"               { comment lexbuf }
  | eof               { EOF }
  | _                 { raise (LexError ("Unexpected char: "^(Lexing.lexeme lexbuf))) }

and string = parse
    "\\\\"           { "\\" :: (string lexbuf) }
  | "\\\""           { "\"" :: (string lexbuf) }
  | "\\n"            { "\n" :: (string lexbuf) }
  | "\\t"            { "\t" :: (string lexbuf) }
  | "\""             { [] }
  | _ as c           { (String.make 1 c) :: (string lexbuf) }

(* comments *)
and comment = parse
    nl               { token lexbuf }
  | eof              { EOF }
  | _                { comment lexbuf }

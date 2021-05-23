{
open Minic_parser
exception LexError of string

exception SyntaxError of string

let keywords =
    [
        "as", AS;
        "assert", ASSERT;
        "abs", ABS;
        "if", IF;
        "in", IN;
        "else", ELSE;
        "boolean", TYPEBOOL;
        "int", TYPEINT;
        "return", RETURN;
        "program", PROGRAM;
        "for", FOR;
        "forall", FORALL;
        "while", WHILE;
        "false", FALSE;
        "struct", STRUCT;
        "true", TRUE;
        "typedecl", TYPEDECL;
    ]

let keyword_tbl = Hashtbl.create 256
let uncurry f (a, b) = f a b
let _ = List.iter (uncurry (Hashtbl.replace keyword_tbl)) keywords


}

let id = ['_' 'a'-'z' 'A'-'Z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']*
let nl = ['\n' '\r']
let ws = ['\n' '\t' '\r' ' ']
let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
let int = '-'? ['0'-'9'] ['0'-'9']*

rule token = parse
    id as id          { try Hashtbl.find keyword_tbl id with Not_found -> IDENT id }
  | "+="              { PLUSEQ }
  | "*="              { TIMESEQ }
  | "-="              { MINUSEQ }
  | "/="              { DIVEQ }
  | "&="              { ANDEQ }
  | "|="              { OREQ }
  | "!="              { NEQ }
  | "&&"              { AND }
  | "||"              { OR }
  | "=="              { EQEQ }
  | "<"               { LT }
  | "<="              { LE }
  | ">"               { GT }
  | ">="              { GE }
  | "--"              { MINUSMINUS }
  | "++"              { PLUSPLUS }
  | ";"               { SEMICOLON }
  | ":"               { COLON }
  | ","               { COMMA }
  | "@"               { AT }
  | ".."              { DOTDOT }
  | "("               { LPAR }
  | ")"               { RPAR }
  | "{"               { LBRACE }
  | "}"               { RBRACE }
  | "["               { LBRACKET }
  | "]"               { RBRACKET }
  | "+"               { PLUS }
  | "-"               { MINUS }
  | "*"               { TIMES }
  | "/"               { DIV }
  | "!"               { EXCLAMATION }
  | "%"               { MOD }
  | "="               { EQ }
  | "?"               { QUESTION }
  | "."				  { DOT }
  | int as int        { INT (int_of_string int) }
  | ws                { token lexbuf }
  | "//"              { comment lexbuf }
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
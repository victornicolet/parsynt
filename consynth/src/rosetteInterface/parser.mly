%{
open Ast
%}

%token DEFINE
%token DEFINEREC
%token LAMBDA
%token LET
%token LETREC
%token IF
%token LPAREN
%token RPAREN
%token DELAY
%token FORCE
%token DOT
%token EQ
%token NEQ
%token LT
%token LEQ
%token GT
%token GEQ
%token AND
%token OR
%token NOT
%token PLUS
%token MINUS
%token MUL
%token DIV
%token MOD
%token LIST
%token CONS
%token CAR
%token CDR
%token NIL
%token NULL
%token TRUE
%token FALSE
%token LOAD
%token <string> ID
%token <int> INT
%token <string> STRING
%token EOF

%type <Ast.expr list> main
%type <Ast.expr list> seq
%type <Ast.expr> expr

%start main

%%
main: seq EOF           { $1 }
      | EOF               { [] }

seq   : expr seq   { $1 :: $2 }
      | expr        { [$1] }

idseq  : ID                { [$1] }
       | LPAREN ids RPAREN { $2 }

ids    : ID ids { $1 :: $2 }
       | ID     { [$1] }

bindgroup : LPAREN bindseq RPAREN { $2 }

bindseq : binding bindseq { $1 :: $2 }
       	| binding { [$1] }

binding : LPAREN ID expr RPAREN { ($2, $3) }

expr   : INT       { Int_e $1 }
       | ID        { Id_e $1 }
       | STRING    { Str_e $1 }
       | TRUE      { Bool_e true }
       | FALSE     { Bool_e false }
       | LPAREN DELAY expr RPAREN           { Delayed_e $3 }
       | LPAREN FORCE expr RPAREN           { Forced_e $3 }
       | LPAREN LAMBDA idseq expr RPAREN    { Fun_e ($3, $4) }
       | LPAREN DEFINE idseq expr RPAREN    { Def_e ($3, $4) }
       | LPAREN DEFINEREC idseq expr RPAREN { Defrec_e ($3, $4) }
       | LPAREN LET bindgroup expr RPAREN     { Let_e ($3, $4) }
       | LPAREN LETREC bindgroup expr RPAREN  { Letrec_e ($3, $4) }
       | LPAREN binop expr expr RPAREN	      { Binop_e ($2, $3, $4) }
       | LPAREN unop expr RPAREN	    { Unop_e ($2, $3)}
       | LPAREN IF expr expr expr RPAREN    { If_e ($3, $4, $5) }
       | LPAREN expr seq RPAREN             { Apply_e ($2, $3) }
       | LPAREN LIST seq RPAREN             { List.fold_right (fun x a -> Cons_e (x, a)) $3 Nil_e }
       | LPAREN LIST RPAREN                 { Nil_e }
       | LPAREN RPAREN                      { Nil_e }
       | NIL                                { Nil_e }
       | LPAREN CONS expr expr RPAREN       { Cons_e ($3, $4) }


binop : PLUS       { Plus }
      | MINUS      { Minus }
      | MUL        { Mul }
      | DIV        { Div }
      | MOD        { Mod }
      | EQ         { Eq}
      | NEQ        { Neq }
      | LT         { Lt }
      | LEQ        { Leq }
      | GT         { Gt }
      | GEQ        { Geq }
      | AND        { And }
      | OR         { Or }

unop : NOT         { Not }
     | CAR         { Car }
     | CDR         { Cdr }
     | NULL        { Null }
     | LOAD        { Load }

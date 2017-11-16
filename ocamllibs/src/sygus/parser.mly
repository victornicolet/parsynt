%{
open Ast

%}
%token QUOTE

%token CONST_CHOICE
%token CHOOSE
%token SCALAR

%token ARITHBINOPS
%token BASICUNOPSUM
%token SCALAROPS
%token COMPARISONOPS
%token BASICBINOPSNUM
%token NLBINOPSNUM
%token BINOPSBOOL

%token NUMEXPRARITH
%token NUMEXPRNL
%token NUMEXPRBASIC
%token BOOLEXPR
%token BOOLEXPRCOMPAR
%token NUMITE
%token SCALAREXPR

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
%token MIN
%token MAX
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
%token <float> FLOAT
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

seq0  : expr seq0   { $1 }
      | expr        { $1 }

idseq  : ID                { [$1] }
       | LPAREN ids RPAREN { $2 }

ids    : ID ids { $1; $1 :: $2 }
       | ID     { $1; [$1] }

bindgroup : LPAREN bindseq RPAREN { $2 }

bindseq : binding bindseq { $1 :: $2 }
       	| binding { [$1] }

binding : LPAREN ID expr RPAREN { ($2, $3) }

expr   : INT       { Int_e $1 }
       | FLOAT 	   { Float_e $1 }
       | ID        { Id_e $1 }
       | STRING    { Str_e $1 }
       | TRUE      { Bool_e true }
       | FALSE     { Bool_e false }
       | QUOTE expr { $2 }
       | LPAREN CONST_CHOICE RPAREN		{ Id_e "??" }
       | LPAREN DELAY expr RPAREN           	{ Delayed_e $3 }
       | LPAREN FORCE expr RPAREN           	{ Forced_e $3 }
       | LPAREN LAMBDA idseq expr RPAREN    	{ Fun_e ($3, $4) }
       | LPAREN DEFINE idseq expr RPAREN    	{ Def_e ($3, $4) }
       | LPAREN DEFINEREC idseq expr RPAREN 	{ Defrec_e ($3, $4) }
       | LPAREN LET bindgroup expr RPAREN     	{ Let_e ($3, $4) }
       | LPAREN LETREC bindgroup expr RPAREN  	{ Letrec_e ($3, $4) }
       | LPAREN binop expr expr RPAREN	      	{ Binop_e ($2, $3, $4) }
       | LPAREN unop expr RPAREN	    	{ Unop_e ($2, $3)}
       | LPAREN IF expr expr expr RPAREN    	{ If_e ($3, $4, $5) }
       | LPAREN expr seq RPAREN             	{ Apply_e ($2, $3) }
       | LPAREN LIST seq RPAREN             	{ List.fold_right (fun x a -> Cons_e (x, a)) $3 Nil_e }
       | LPAREN LIST RPAREN                 	{ Nil_e }
       | LPAREN RPAREN                      	{ Nil_e }
       | LPAREN CHOOSE seq0 RPAREN		{ $3 }
       | LPAREN NUMEXPRARITH seq0 RPAREN	{ $3 }
       | LPAREN NUMEXPRNL seq0 RPAREN		{ $3 }
       | LPAREN NUMEXPRBASIC seq0 RPAREN	{ $3 }
       | LPAREN BOOLEXPR seq0 RPAREN		{ $3 }
       | LPAREN BOOLEXPRCOMPAR seq0 RPAREN	{ $3 }
       | LPAREN NUMITE seq0 RPAREN  		{ $3 }
       | LPAREN SCALAREXPR seq0 RPAREN		{ $3 }
       | LPAREN SCALAR seq0 RPAREN		{ $3 }
       | LPAREN NUMEXPRARITH RPAREN		{ Int_e 0 }
       | LPAREN NUMEXPRNL RPAREN		{ Int_e 0 }
       | LPAREN NUMEXPRBASIC RPAREN		{ Int_e 0 }
       | LPAREN BOOLEXPR RPAREN			{ Bool_e true }
       | LPAREN BOOLEXPRCOMPAR RPAREN		{ Bool_e true }
       | LPAREN NUMITE RPAREN  			{ Int_e 0 }
       | LPAREN SCALAREXPR RPAREN		{ Int_e 0 }
       | CONST_CHOICE  	    			{ Nil_e }
       | LPAREN CONS expr expr RPAREN       	{ Cons_e ($3, $4) }
       | NIL                                	{ Nil_e }

binopseq0 : binop binopseq0 {$1}
	  | binop {$1}

binop : LPAREN CHOOSE binopseq0 RPAREN { $3 }
      | PLUS       { Plus }
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
      | MIN 	   { Min }
      | MAX	   { Max }
      | ARITHBINOPS				{ Plus }
      | BASICUNOPSUM				{ Minus }
      | SCALAROPS				{ Minus }
      | COMPARISONOPS				{ Lt }
      | BASICBINOPSNUM				{ Plus }
      | NLBINOPSNUM				{ Mul }
      | BINOPSBOOL				{ And }


unop : NOT         { Not }
     | CAR         { Car }
     | CDR         { Cdr }
     | NULL        { Null }
     | LOAD        { Load }

%{
	open Synthlib2ast

%}

%token SETLOGIC
%token DEFSORT
%token DECLVAR
%token DECLFUN
%token DEFFUN
%token SYNTHFUN
%token CONSTRAINT
%token CHECKSYNTH
%token SETOPTIONS
%token BITVECSORT
%token ARRAYSORT
%token INTSORT
%token BOOLSORT
%token ENUMSORT
%token REALSORT
%token CONSTANT
%token VARIABLE
%token INPUTVARIABLE
%token LOCALVARIABLE
%token LET
%token TRUE
%token FALSE

%token EOF

%token DOUBLECOLON
%token LPAREN
%token RPAREN

%token <string> SYMBOL
%token <string> QUOTED
%token <int> INT
%token <float> REAL
%token <int> BITVECTOR

%type <Synthlib2ast.sygusFile> file

%start file

%%
file : setlogic cmds EOF					{ SyCommandsWithLogic($1, $2) }
     | cmds EOF      		  				{ SyCommands($1) }

setlogic : LPAREN SETLOGIC SYMBOL RPAREN 			{ which_logic($3) }

cmds : 	   	  	   	 				{ [] }
     | cmd 	  	   	 				{ [$1] }
     | cmd cmds							{ $1 :: $2 }

cmd : LPAREN DEFSORT SYMBOL sort RPAREN				{ SySortDefCmd($3, $4) }
    | LPAREN DECLVAR SYMBOL sort RPAREN				{ SyVarDeclCmd($3, $4) }
    | LPAREN DECLFUN SYMBOL LPAREN sorts RPAREN sort RPAREN	{ SyFunDeclCmd($3, $5, $7) }
    | LPAREN DEFFUN SYMBOL LPAREN args RPAREN sort term RPAREN	{ SyFunDefCmd($3, $5, $7, $8) }
    | LPAREN SYNTHFUN SYMBOL LPAREN args RPAREN sort LPAREN ntdefs RPAREN RPAREN
      	     	      	     	    	       	     	    	{ SynthFunCmd($3, $5, $7, $9) }
    | LPAREN CONSTRAINT term RPAREN				{ SyConstraintCmd($3) }
    | LPAREN SETOPTIONS syoptions RPAREN			{ SySetOptsCmd($3) }
    | CHECKSYNTH						{ SyCheckSynthCmd }

sorts : 	   	  	   	 			{ [] }
      | sort 							{[$1]}
      | sort sorts 						{ $1 :: $2 }

sort : BOOLSORT							{ SyBoolSort }
     | INTSORT							{ SyIntSort }
     | REALSORT							{ SyRealSort }
     | LPAREN ARRAYSORT sort sort RPAREN			{ SyArraySort($3, $4) }
     | LPAREN ENUMSORT LPAREN symbols RPAREN RPAREN		{ SyEnumSort($4) }
     | LPAREN BITVECSORT INT RPAREN				{ SyBitVecSort($3) }
     | symbol 		    					{ SyIdSort($1) }

ntdef : LPAREN SYMBOL sort LPAREN gterms RPAREN RPAREN		{ ($2, $3, $5) }

ntdefs : ntdef 							{ [$1] }
       | ntdef ntdefs 						{ $1 :: $2 }


terms : 	   	  	   	 			{ [] }
      | term 							{ [$1] }
      | term terms 						{ $1 :: $2 }


term : LPAREN SYMBOL terms RPAREN				{ SyApp($2, $3) }
     | literal	     	   					{ SyLiteral($1) }
     | SYMBOL							{ SyId($1) }
     | letterm							{ $1 }

gterms : 	   	  	   	 			{ [] }
      | gterm 							{ [$1] }
      | gterm gterms 						{ $1 :: $2 }


gterm : LPAREN SYMBOL gterms RPAREN				{ SyGApp($2, $3) }
     | literal	     	   					{ SyGLiteral($1) }
     | SYMBOL							{ SyGId($1) }
     | letgterm							{ $1 }
     | LPAREN CONSTANT sort RPAREN				{ SyGConstant($3) }
     | LPAREN VARIABLE sort RPAREN				{ SyGVariable($3) }
     | LPAREN LOCALVARIABLE sort RPAREN				{ SyGLocalVariable($3) }
     | LPAREN INPUTVARIABLE sort RPAREN				{ SyGInputVariable($3) }


letgterm : LPAREN LET LPAREN gbindings RPAREN gterm LPAREN 	{ SyGLet($4, $6) }

letterm : LPAREN LET LPAREN bindings RPAREN term LPAREN 	{ SyLet($4, $6) }

bindings : binding   	    	     	    	 		{ [$1] }
	 | binding bindings					{ $1 :: $2 }

binding : LPAREN SYMBOL sort term RPAREN			{($2, $3, $4)}

gbindings : gbinding   	    	     	    	 		{ [$1] }
	 | gbinding gbindings					{ $1 :: $2 }

gbinding : LPAREN SYMBOL sort gterm RPAREN			{($2, $3, $4)}


literal : QUOTED						{ SyString $1 }
	| INT							{ SyInt $1 }
	| REAL							{ SyReal $1 }
	| TRUE  						{ SyBool true }
	| FALSE 						{ SyBool false }
	| BITVECTOR 						{ SyBitVector $1 }
	| SYMBOL DOUBLECOLON SYMBOL				{ SyEnum($1, $3) }


syoptions : 	   	  	   	 			{ [] }
	| syoption 						{ [$1] }
	| syoption syoptions 					{ $1 :: $2 }

syoption : LPAREN SYMBOL literal RPAREN				{ ($2, $3) }

args : 	   	  	   	 				{ [] }
     | arg 							{ [$1] }
     | arg args 						{ $1 :: $2 }

arg : LPAREN SYMBOL sort RPAREN					{ ($2, $3) }


symbols : symbol						{ [$1] }
	| symbol symbols 					{ $1 :: $2 }

symbol: SYMBOL 	 						{$1}

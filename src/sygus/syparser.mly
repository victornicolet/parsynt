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
%token LPR
%token RPR

%token <string> SYMBOL
%token <string> QUOTED
%token <int> INT
%token <float> REAL
%token <string> BITVECTOR

%type <Synthlib2ast.sygusFile> file

%start file

%%
file : l=setlogic c=cmds EOF					{ SyCommandsWithLogic(l, c) }
     | c=cmds EOF      		  				{ SyCommands(c) }

setlogic : LPR SETLOGIC SYMBOL RPR 				{ which_logic($3) }

cmds : 	   	  	   	 				{ [] }
     | cmd cmds							{ $1 :: $2 }

cmd : LPR DEFSORT id=SYMBOL s=sort RPR
                                                                { SySortDefCmd(id, s) }
    | LPR; DECLVAR; id=SYMBOL s=sort RPR			{ SyVarDeclCmd(id, s) }
    | LPR DECLFUN id=SYMBOL LPR a=sorts RPR s=sort RPR		{ SyFunDeclCmd(id, a, s) }
    | LPR DEFFUN id=SYMBOL LPR a=args RPR s=sort t=term RPR	{ SyFunDefCmd(id, a,s,t) }
    | LPR SYNTHFUN id=SYMBOL LPR a=args RPR s=sort LPR n=ntdefs RPR RPR
      	     	      	     	    	       	     	    	{ SynthFunCmd(id, a, s, n) }
    | LPR CONSTRAINT t=term RPR				        { SyConstraintCmd(t) }
    | LPR SETOPTIONS o=syoptions RPR				{ SySetOptsCmd(o) }
    | LPR CHECKSYNTH RPR					{ SyCheckSynthCmd }

sorts : 	   	  	   	 			{ [] }
      | sort sorts 						{ $1 :: $2 }

sort : BOOLSORT							{ SyBoolSort }
     | INTSORT							{ SyIntSort }
     | REALSORT							{ SyRealSort }
     | LPR ARRAYSORT s1=sort s2=sort RPR			{ SyArraySort(s1, s2) }
     | LPR ENUMSORT LPR s=symbols RPR RPR			{ SyEnumSort(s) }
     | LPR BITVECSORT k=INT RPR					{ SyBitVecSort(k) }
     | s=SYMBOL 		    				{ SyIdSort(s) }

ntdef : LPR id=SYMBOL s=sort LPR t=gterms RPR RPR		{ (id, s, t) }

ntdefs : ntdef 							{ [$1] }
       | ntdef ntdefs 						{ $1 :: $2 }


terms : 	   	  	   	 			{ [] }
      | term terms 						{ $1 :: $2 }


term : LPR LET LPR b=bindings RPR t=term RPR			{ SyLet(b,t) }
     | LPR f=SYMBOL x=terms RPR					{ SyApp(f, x) }
     | l=literal	     	   				{ SyLiteral(l) }
     | s=SYMBOL							{ SyId(s) }



gterms : 	   	  	   	 			{ [] }
      | gterm gterms 						{ $1 :: $2 }


gterm : LPR f=SYMBOL x=gterms RPR				{ SyGApp(f, x) }
     | l=literal	     	   				{ SyGLiteral(l) }
     | s=SYMBOL							{ SyGId(s) }
     | LPR LET LPR b=gbindings RPR t=gterm RPR 			{ SyGLet(b, t) }
     | LPR CONSTANT s=sort RPR					{ SyGConstant(s) }
     | LPR VARIABLE s=sort RPR					{ SyGVariable(s) }
     | LPR LOCALVARIABLE s=sort RPR				{ SyGLocalVariable(s) }
     | LPR INPUTVARIABLE s=sort RPR				{ SyGInputVariable(s) }


bindings :       	    	     	    	 		{ [] }
	 | binding bindings					{ $1 :: $2 }

binding : LPR id=SYMBOL s=sort t=term RPR			{(id, s, t)}

gbindings :      	    	     	    	 		{ [] }
	 | gbinding gbindings					{ $1 :: $2 }

gbinding : LPR id=SYMBOL s=sort t=gterm RPR			{(id, s, t)}


literal : QUOTED						{ SyString $1 }
	| INT							{ SyInt $1 }
	| REAL							{ SyReal $1 }
	| TRUE  						{ SyBool true }
	| FALSE 						{ SyBool false }
	| BITVECTOR 						{ SyBitVector $1 }
	| SYMBOL DOUBLECOLON SYMBOL				{ SyEnum($1, $3) }


syoptions : 	   	  	   	 			{ [] }
	| syoption syoptions 					{ $1 :: $2 }

syoption : LPR SYMBOL literal RPR				{ ($2, $3) }

args : 	   	  	   	 				{ [] }
     | arg args 						{ $1 :: $2 }

arg : LPR id=SYMBOL s=sort RPR					{ (id, s) }


symbols : SYMBOL						{ [$1] }
	| SYMBOL symbols 					{ $1 :: $2 }

%{
    open Minic
    open Lang.Typ
%}

%token <string> IDENT
%token <int> INT
%token PLUS
%token MINUS
%token TIMES
%token AND
%token AS
%token AT
%token ABS
%token OR
%token DIV
%token MOD
%token EQ PLUSEQ TIMESEQ MINUSEQ DIVEQ ANDEQ OREQ PLUSPLUS MINUSMINUS
%token LT
%token GT
%token LE
%token GE
%token NEQ
%token RBRACE
%token LBRACE
%token RBRACKET
%token LBRACKET
%token LPAR
%token RPAR
%token TRUE
%token FALSE
%token IF
%token IN
%token ELSE
%token SEMICOLON
%token EQEQ
%token COLON
%token COMMA
%token ASSERT
%token FOR
%token FORALL
%token WHILE
%token TYPEDECL
%token TYPEINT
%token TYPEBOOL
%token RETURN
%token STRUCT
%token QUESTION
%token DOTDOT
%token EXCLAMATION
%token DOT

%token PROGRAM
%token EOF

%nonassoc QUESTION
%nonassoc COLON


%start <Minic.a_program> main

%%

main: f=list(funcdecl); EOF                     { AFunctions f }
    | PROGRAM l=list(stmt);  EOF                { ABody l }


funcdecl:
        | t=atype; f=IDENT; LPAR a=separated_list(COMMA, arg); RPAR LBRACE b=stmt; RBRACE { t, f, a, b }


arg: atype IDENT { $1, $2 }


lhvar: i=IDENT;                                             { AVar i }
     | v=lhvar; LBRACKET e=expr; RBRACKET                   { AElt (v, e) }
	 | v=lhvar; DOT m=IDENT                    				{ AMem (v, m) }



stmt:
    | LBRACE l = list(stmt); RBRACE                         { (mkAStmt_defloc  (ACompStmt (l))) }
    | FOR LPAR i = iter; RPAR s = stmt;                     { (mkAStmt_defloc  (AForStmt (i, s))) }
    | WHILE LPAR e = expr; RPAR s = stmt;                   { (mkAStmt_defloc  (AWhileStmt (e, s))) }
    | IF LPAR e = expr; RPAR s = stmt;                      { (mkAStmt_defloc  (AIfStmt(e, s, mkAStmt_defloc AEmpty))) }
    | IF LPAR e = expr; RPAR s = stmt; ELSE s2 = stmt;      { (mkAStmt_defloc  (AIfStmt(e, s, s2))) }
    | RETURN e = expr; SEMICOLON                            { (mkAStmt_defloc  (AReturn(e))) }
    | RETURN e = expr; AS prop=IDENT; SEMICOLON             { (mkAStmt_defloc  (AReturnCstr(e, prop))) }
    | d = decl; SEMICOLON                                   { (mkAStmt_defloc  (ADeclStmt(d))) }
    | TYPEDECL name=IDENT; t=atype; SEMICOLON               { (mkAStmt_defloc  (ATypeDeclStmt(name,t)))}
    | i = instr; SEMICOLON                                  { (mkAStmt_defloc  (AInstrStmt(i))) }
    | ASSERT a=assert_expr; SEMICOLON                       { (mkAStmt_defloc  (AAssertion(a)))}

assert_expr:
    | FORALL LPAR i = iter; RPAR LBRACE e = expr; RBRACE    { AAForall(i, e)}
    | e = expr;                                             { AAExpr(e)}


instr:
    | v=lhvar; EQ e=expr;                                   { Some v, e }
    | v=lhvar; PLUSEQ e=expr;                               { Some v, ABinop(Plus, AEVar v, e) }
    | v=lhvar; TIMESEQ e=expr;                              { Some v, ABinop(Times, AEVar v, e) }
    | v=lhvar; MINUSEQ e=expr;                              { Some v, ABinop(Minus, AEVar v, e) }
    | v=lhvar; DIVEQ e=expr;                                { Some v, ABinop(Div, AEVar v, e) }
    | v=lhvar; ANDEQ e=expr;                                { Some v, ABinop(And, AEVar v, e) }
    | v=lhvar; OREQ e=expr;                                 { Some v, ABinop(Or, AEVar v, e) }
    | v=lhvar; PLUSPLUS                                     { Some v, ABinop(Plus, AEVar v, AEConst (ACInt 1)) }
    | v=lhvar; MINUSMINUS                                   { Some v, ABinop(Minus, AEVar v, AEConst (ACInt 1)) }


iter :
    | i=IDENT; EQ e1=expr; DOTDOT e2=expr;                  { AIRange(i, e1, e2) }
    | i=IDENT; IN l1=expr;                                  { AIList(i, l1)}


decl : atype IDENT                                          { $1, $2, None}
     | t=atype; i=IDENT; EQ e=expr;                         { t, i, Some e}


atype:
    | atype TIMES                                           { Seq $1 }
    | a=atype AT expr                                       { a }
    | LPAR a=atype; RPAR                                    { a }
    | TYPEINT                                               { Int }
    | TYPEBOOL                                              { Bool }
    | IDENT                                                 { Named $1 }
    | STRUCT LBRACE x=list(struct_field_decl); RBRACE         { Struct x }


struct_field_decl : m=IDENT; COLON t=atype; SEMICOLON         { m, t }

const: i=INT;                                               { ACInt(i) }
     | TRUE                                                 { ACBool(true) }
     | FALSE                                                { ACBool(false) }

expr:
    LBRACKET el=separated_list(COMMA, expr); RBRACKET       { AEList el }
    | LBRACE ml=separated_list(COMMA, struct_field); RBRACE { AEStruct ml }
    | c=expr; QUESTION e1=expr; COLON e2=expr;              { ACond(c, e1, e2) }
    | logical_or_e                                          { $1 }


logical_or_e:
    | a=logical_and_e OR b=logical_or_e                             { ABinop(Or, a, b)}
    | logical_and_e                                                 { $1 }

logical_and_e:
    | a=equality_e AND b=logical_and_e                              { ABinop(And, a, b)}
    | equality_e                                                    { $1 }

equality_e:
    | a=comp_e EQEQ b=comp_e                                        { ABinop(Eq, a, b) }
    | a=comp_e NEQ b=comp_e                                         { AUnop(Not, ABinop(Eq, a, b)) }
    | comp_e                                                        { $1 }

comp_e:
    | a=add_e op=op_comp b=add_e                                    { ABinop(op, a, b) }
    | add_e                                                         { $1 }

add_e:
    | a=mult_e op=op_add b=add_e                                    { ABinop(op, a, b) }
    | mult_e                                                        { $1 }

mult_e:
    | a=unary_e op=op_mult b=mult_e                                 { ABinop(op, a, b) }
    | unary_e                                                       { $1 }

unary_e:
    | op=unop a=unary_e                                             { AUnop(op, a) }
    | fun_app_e                                                     { $1 }



fun_app_e:
    | f=IDENT; LPAR a=separated_list(COMMA, expr); RPAR             { AFunCall(f, a) }
    | primary_e                                                     { $1 }


primary_e:
    v=lhvar;                                                        { AEVar v }
    | c=const;                                                      { AEConst c}
    | LPAR t=expr RPAR                                              { t }


struct_field : m=IDENT; EQ e=expr;                        { m, e }

%inline op_comp:
    | LT        { Lt }
    | GT        { Gt }
    | LE        { Le }
    | GE        { Ge }

%inline op_add:
    | PLUS      { Plus }
    | MINUS     { Minus }

%inline op_mult:
    | DIV       { Div }
    | TIMES     { Times }
    | MOD       { Mod }

%inline unop:
    | MINUS       { Neg }
    | EXCLAMATION { Not }
    | ABS         { Abs }

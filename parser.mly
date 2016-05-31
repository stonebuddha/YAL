%{
open Syntax
%}

%token <int> INTV
%token <string> ID
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token LET
%token IN
%token FN
%token FIX
%token LAM
%token INT
%token BOOL
%token UNIT
%token END
%token RIGHTARROW
%token LPAREN
%token RPAREN
%token COMMA
%token COLON
%token EQ
%token LCURLY
%token RCURLY
%token LSQUARE
%token RSQUARE
%token LEQ
%token LT
%token GT
%token PLUS
%token TILDE
%token BAR
%token TIMES
%token DOT
%token AND
%token OR

%right RIGHTARROW
%right OR
%right AND
%left PLUS
%left TIMES
%left TILDE

%start <Syntax.context -> Syntax.term> term

%%

index:
  | a = ID
    { fun ctx -> IdVar (name2index ctx a, ctx_length ctx) }
  | i = INTV
    { fun ctx -> IdInt (i) }
  | i1 = index; PLUS; i2 = index
     { fun ctx -> IdAdd (i1 ctx, i2 ctx) }
  ;

prop:
  | TRUE
    { fun ctx -> PrTrue }
  | FALSE
    { fun ctx -> PrFalse }
  | TILDE; p = prop
    { fun ctx -> PrNeg (p ctx) }
  | p1 = prop; AND; p2 = prop
    { fun ctx -> PrAnd (p1 ctx, p2 ctx) }
  | p1 = prop; OR; p2 = prop
    { fun ctx -> PrOr (p1 ctx, p2 ctx) }
  | i1 = index; LEQ; i2 = index
    { fun ctx -> PrLe (i1 ctx, i2 ctx) }
  ;

sort:
  | INT
    { fun ctx -> SrInt }
  | LCURLY; a = ID; COLON; s = sort; BAR; p = prop; RCURLY
    { fun ctx -> SrSubset (a, s ctx, p (add_name ctx a)) }
  ;

ty:
  | INT; LPAREN; i = index; RPAREN
    { fun ctx -> TyInt (i ctx) }
  | BOOL
    { fun ctx -> TyBool }
  | UNIT
    { fun ctx -> TyUnit }
  | t1 = ty; TIMES; t2 = ty
    { fun ctx -> TyProduct (t1 ctx, t2 ctx) }
  | t1 = ty; RIGHTARROW; t2 = ty
    { fun ctx -> TyArrow (t1 ctx, t2 ctx) }
  | LCURLY; a = ID; COLON; s = sort; DOT; t = ty; RCURLY
    { fun ctx -> TyDepUni (a, s ctx, t (add_name ctx a)) }
  | LSQUARE; a = ID; COLON; s = sort; DOT; t = ty; RSQUARE
    { fun ctx -> TyDepExi (a, s ctx, t (add_name ctx a)) }
  ;


term:
  | x = ID
    { fun ctx -> TmVar (name2index ctx x, ctx_length ctx) }
  | i = INTV
    { fun ctx -> TmInt (i) }
  | TRUE
    { fun ctx -> TmBool (true) }
  | FALSE
    { fun ctx -> TmBool (false) }
  | LPAREN; RPAREN
    { fun ctx -> TmUnit }
  | LPAREN; t1 = term; COMMA; t2 = term; RPAREN
    { fun ctx -> TmPair (t1 ctx, t2 ctx) }
  | IF; t1 = term; THEN; t2 = term; ELSE; t3 = term
    { fun ctx -> TmIf (t1 ctx, t2 ctx, t3 ctx) }
  | FN; LPAREN; x = ID; COLON; t = ty; RPAREN; b = term; END
    { fun ctx -> TmAbs (x, t ctx, b (add_name ctx x)) }
  | LPAREN; t1 = term; t2 = term; RPAREN
    { fun ctx -> TmApp (t1 ctx, t2 ctx) }
  | LET; x = ID; EQ; t1 = term; IN; t2 = term
    { fun ctx -> TmLet (x, t1 ctx, t2 (add_name ctx x)) }
  | FIX; LPAREN; f = ID; COLON; t = ty; RPAREN; b = term; END
    { fun ctx -> TmFix (f, t ctx, b (add_name ctx f)) }
  | LAM; LCURLY; a = ID; COLON; s = sort; RCURLY; t = term; END
    { fun ctx -> TmDepAbs (a, s ctx, t (add_name ctx a)) }
  | LSQUARE; t = term; i = index; RSQUARE
    { fun ctx -> TmDepApp (t ctx, i ctx) }
  | LT; i = index; COMMA; b = term; COLON; t = ty; GT
    { fun ctx -> TmDepPair (i ctx, b ctx, t ctx) }
  | LET; LT; a = ID; COMMA; x = ID; GT; EQ; t1 = term; IN; t2 = term
    { fun ctx -> TmDepLet (a, x, t1 ctx, t2 (add_name (add_name ctx a) x)) }
  | LPAREN; t = term; RPAREN
    { t }
  ;
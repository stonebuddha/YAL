%{
open Elasyntax
%}

%token <int> INTV
%token <float> FLOATV
%token <string> ID
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token LET
%token IN
%token VAL
%token SORT
%token FUN
%token TYPE
%token BOOL
%token INT
%token FLOAT
%token FN
%token REC
%token END
%token MATRIX
%token VECTOR
%token DECLARE
%token UNIT
%token RIGHTARROW
%token DRIGHTARROW
%token PLUSDOT
%token MINUSDOT
%token TIMESDOT
%token DIVDOT
%token LEQDOT
%token LTDOT
%token GEQDOT
%token GTDOT
%token NEQDOT
%token EQDOT
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token AND
%token OR
%token LEQ
%token LT
%token GEQ
%token GT
%token NEQ
%token EQ
%token LPAREN
%token RPAREN
%token LCURLY
%token RCURLY
%token LSQUARE
%token RSQUARE
%token SEMI
%token COLON
%token BAR
%token TILDE
%token DOT
%token COMMA
%token EOF

%nonassoc IN
%nonassoc ELSE
%right RIGHTARROW
%right OR
%right AND
%left LEQ LT GEQ GT NEQ EQ LEQDOT LTDOT GEQDOT GTDOT NEQDOT EQDOT
%left PLUS MINUS PLUSDOT MINUSDOT
%left TIMES DIV TIMESDOT DIVDOT
%left TILDE

%start <Elasyntax.ela_context -> Elasyntax.ela_command list * Elasyntax.ela_context> prog

%%

prog:
  | EOF
    { fun ctx -> ([], ctx) }
  | c = command; SEMI; p = prog
    { fun ctx ->
        let (cmd, ctx) = c ctx in
        let (cmds, ctx) = p ctx in
          (cmd :: cmds, ctx) }
  ;

command:
  | e = expr
    { fun ctx -> (ElaCmdEval (e ctx), ctx) }
  | VAL; x = ID; EQ; e = expr
    { fun ctx -> (ElaCmdVal (x, e ctx), ela_add_name ctx x) }
  | SORT; a = ID; EQ; s = sort
    { fun ctx -> (ElaCmdSortAbb (a, s ctx), ela_add_name ctx a) }
  | FUN; f = ID; ipl = list(iparam); epl = list(eparam); COLON; t = ty; EQ; e = expr
    { fun ctx ->
        let ctx' = List.fold_left (fun ctx ip -> ela_add_name ctx (fst (ip ctx))) ctx ipl in
        let tyTres = t ctx' in
        let eps = List.map (fun ep -> ep ctx') epl in
        let tyTf = List.fold_right (fun ep tyT -> ElaTyArrow (snd ep, tyT)) eps tyTres in
        let rec build ctx ipl tyT =
          (match ipl with
           | [] -> tyT
           | ip :: rest -> let (a, sr) = ip ctx in ElaTyDepUni (a, sr, build (ela_add_name ctx a) rest tyT)) in
        let tyTf' = build ctx ipl tyTf in
        let inner_ctx = List.fold_left (fun ctx ip -> ela_add_name ctx (fst (ip ctx))) (ela_add_name ctx f) ipl in
        let inner_ctx' = List.fold_left (fun ctx ep -> ela_add_name ctx (fst (ep ctx))) inner_ctx epl in
        let inner_ex = e inner_ctx' in
        let rec build' ctx epl ex =
          (match epl with
           | [] -> ex
           | ep :: rest -> let (x, tyTx) = ep ctx in ElaExAbs (x, build' (ela_add_name ctx x) rest ex)) in
        let ex = build' inner_ctx epl inner_ex in
        let rec build'' ctx ipl ex =
          (match ipl with
           | [] -> ex
           | ip :: rest -> let (a, sr) = ip ctx in ElaExDepAbs (a, sr, build'' (ela_add_name ctx a) rest ex)) in
        let ex' = build'' (ela_add_name ctx f) ipl ex in
          (ElaCmdVal (f, ElaExFix (f, tyTf', ex')), ela_add_name ctx f) }
  | TYPE; a = ID; EQ; t = ty
    { fun ctx -> (ElaCmdTypeAbb (a, t ctx), ela_add_name ctx a) }
  | DECLARE; x = ID; COLON; t = ty
    { fun ctx -> (ElaCmdVar (x, t ctx), ela_add_name ctx x) }
  ;

eparam:
  | LPAREN; x = ID; COLON; t = ty; RPAREN
    { fun ctx -> (x, t ctx) }
  ;

iparam:
  | LCURLY; a = ID; COLON; s = sort; RCURLY
    { fun ctx -> (a, s ctx) }
  ;

sort:
  | a = ID
    { fun ctx -> ElaSrVar (ela_name_to_index ctx a, ela_ctx_length ctx) }
  | INT
    { fun ctx -> ElaSrInt }
  | BOOL
    { fun ctx -> ElaSrBool }
  | LCURLY; a = ID; COLON; s = sort; BAR; p = index; RCURLY
    { fun ctx -> ElaSrSubset (a, s ctx, p (ela_add_name ctx a)) }
  ;

index:
  | i = INTV
    { fun ctx -> ElaIdInt (i) }
  | TRUE
    { fun ctx -> ElaIdBool (true) }
  | FALSE
    { fun ctx -> ElaIdBool (false) }
  | a = ID
    { fun ctx -> ElaIdVar (ela_name_to_index ctx a, ela_ctx_length ctx) }
  | i1 = index; PLUS; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnPlus, i1 ctx, i2 ctx) }
  | i1 = index; MINUS; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnMinus, i1 ctx, i2 ctx) }
  | i1 = index; TIMES; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnTimes, i1 ctx, i2 ctx) }
  | i1 = index; DIV; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnDiv, i1 ctx, i2 ctx) }
  | i1 = index; LEQ; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnLeq, i1 ctx, i2 ctx) }
  | i1 = index; LT; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnLt, i1 ctx, i2 ctx) }
  | i1 = index; GEQ; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnGeq, i1 ctx, i2 ctx) }
  | i1 = index; GT; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnGt, i1 ctx, i2 ctx) }
  | i1 = index; NEQ; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnNeq, i1 ctx, i2 ctx) }
  | i1 = index; EQ; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnEq, i1 ctx, i2 ctx) }
  | i1 = index; AND; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnAnd, i1 ctx, i2 ctx) }
  | i1 = index; OR; i2 = index
    { fun ctx -> ElaIdBinop (ElaBnOr, i1 ctx, i2 ctx) }
  | TILDE; i1 = index
    { fun ctx -> ElaIdUnop (ElaUnNot, i1 ctx) }
  | LPAREN; i = index; RPAREN
    { i }
  ;

ty:
  | a = ID
    { fun ctx -> ElaTyVar (ela_name_to_index ctx a, ela_ctx_length ctx) }
  | BOOL; LPAREN; i = index; RPAREN
    { fun ctx -> ElaTyBool (i ctx) }
  | BOOL
    { fun ctx -> ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 1 + ela_ctx_length ctx))) }
  | FLOAT
    { fun ctx -> ElaTyFloat }
  | INT; LPAREN; i = index; RPAREN
    { fun ctx -> ElaTyInt (i ctx) }
  | INT
    { fun ctx -> ElaTyDepExi ("i", ElaSrInt, ElaTyInt (ElaIdVar (0, 1 + ela_ctx_length ctx))) }
  | MATRIX; LPAREN; i1 = index; COMMA; i2 = index; RPAREN
    { fun ctx -> ElaTyMatrix (i1 ctx, i2 ctx) }
  | MATRIX
    { fun ctx -> ElaTyDepExi ("m", ElaSrSubset ("a", ElaSrInt, ElaIdBinop (ElaBnGeq, ElaIdVar (0, 1 + ela_ctx_length ctx), ElaIdInt (0))), ElaTyDepExi ("n", ElaSrSubset ("a", ElaSrInt, ElaIdBinop (ElaBnGeq, ElaIdVar (0, 2 + ela_ctx_length ctx), ElaIdInt (0))), ElaTyMatrix (ElaIdVar (1, 2 + ela_ctx_length ctx), ElaIdVar (0, 2 + ela_ctx_length ctx)))) }
  | VECTOR; LPAREN; i = index; RPAREN
    { fun ctx -> ElaTyVector (i ctx) }
  | VECTOR
    { fun ctx -> ElaTyDepExi ("n", ElaSrSubset ("a", ElaSrInt, ElaIdBinop (ElaBnGeq, ElaIdVar (0, 1 + ela_ctx_length ctx), ElaIdInt (0))), ElaTyVector (ElaIdVar (0, 1 + ela_ctx_length ctx))) }
  | t1 = ty; RIGHTARROW; t2 = ty
    { fun ctx -> ElaTyArrow (t1 ctx, t2 ctx) }
  | LCURLY a = ID; COLON; s = sort; DOT; t = ty; RCURLY
    { fun ctx -> ElaTyDepUni (a, s ctx, t (ela_add_name ctx a)) }
  | LSQUARE a = ID; COLON; s = sort; DOT; t = ty; RSQUARE
    { fun ctx -> ElaTyDepExi (a, s ctx, t (ela_add_name ctx a)) }
  | t1 = ty; TIMES; t2 = ty
    { fun ctx -> ElaTyProduct (t1 ctx, t2 ctx) }
  | LPAREN; t = ty; RPAREN
    { t }
  | UNIT
    { fun ctx -> ElaTyUnit }
  ;

expr:
  | LSQUARE; el = list(expr); RSQUARE
    { fun ctx ->
        let es = List.map (fun e -> e ctx) el in
        List.fold_left (fun res ex -> ElaExApp (res, ex)) (List.hd es) (List.tl es) }
  | LPAREN; e = expr; COLON; t = ty; RPAREN
    { fun ctx -> ElaExAs (e ctx, t ctx) }
  | i = INTV
    { fun ctx -> ElaExInt (i) }
  | f = FLOATV
    { fun ctx -> ElaExFloat (f) }
  | LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN
    { fun ctx -> ElaExPair (e1 ctx, e2 ctx) }
  | x = ID
    { fun ctx -> ElaExVar (ela_name_to_index ctx x, ela_ctx_length ctx) }
  | e1 = expr; PLUS; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op+", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; MINUS; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op-", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; TIMES; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op*", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; DIV; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op/", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; LEQ; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op<=", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; LT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op<", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; GEQ; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op>=", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; GT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op>", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; NEQ; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op!=", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; EQ; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op=", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; PLUSDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op+.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; MINUSDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op-.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; TIMESDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op*.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; DIVDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op/.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; LEQDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op<=.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; LTDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op<.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; GEQDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op>=.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; GTDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op>.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; NEQDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op!=.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; EQDOT; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op=.", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; AND; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op&&", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | e1 = expr; OR; e2 = expr
    { fun ctx -> ElaExApp (ElaExVar (ela_name_to_index ctx "op||", ela_ctx_length ctx), ElaExPair (e1 ctx, e2 ctx)) }
  | TRUE
    { fun ctx -> ElaExBool (true) }
  | FALSE
    { fun ctx -> ElaExBool (false) }
  | IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr
    { fun ctx -> ElaExIf (e1 ctx, e2 ctx, e3 ctx) }
  | LET; x = ID; EQ; e1 = expr; IN; e2 = expr
    { fun ctx ->  ElaExLet (x, e1 ctx, e2 (ela_add_name ctx x)) }
  | FN; ipl = list(iparam); epl = list(eparam); COLON; t = ty; DRIGHTARROW; e = expr; END
    { fun ctx ->
        let ctx' = List.fold_left (fun ctx ip -> ela_add_name ctx (fst (ip ctx))) ctx ipl in
        let tyTres = t ctx' in
        let eps = List.map (fun ep -> ep ctx') epl in
        let tyTf = List.fold_right (fun ep tyT -> ElaTyArrow (snd ep, tyT)) eps tyTres in
        let rec build ctx ipl tyT =
          (match ipl with
           | [] -> tyT
           | ip :: rest -> let (a, sr) = ip ctx in ElaTyDepUni (a, sr, build (ela_add_name ctx a) rest tyT)) in
        let tyTf' = build ctx ipl tyTf in
        let inner_ctx = List.fold_left (fun ctx ep -> ela_add_name ctx (fst (ep ctx))) ctx' epl in
        let inner_ex = e inner_ctx in
        let rec build' ctx epl ex =
          (match epl with
           | [] -> ex
           | ep :: rest -> let (x, tyTx) = ep ctx in ElaExAbs (x, build' (ela_add_name ctx x) rest ex)) in
        let ex = build' ctx' epl inner_ex in
        let rec build'' ctx ipl ex =
          (match ipl with
           | [] -> ex
           | ip :: rest -> let (a, sr) = ip ctx in ElaExDepAbs (a, sr, build'' (ela_add_name ctx a) rest ex)) in
        let ex' = build'' ctx ipl ex in
          ElaExAs (ex', tyTf') }
  | REC; f = ID; ipl = list(iparam); epl = list(eparam); COLON; t = ty; DRIGHTARROW; e = expr; END
    { fun ctx ->
        let ctx' = List.fold_left (fun ctx ip -> ela_add_name ctx (fst (ip ctx))) ctx ipl in
        let tyTres = t ctx' in
        let eps = List.map (fun ep -> ep ctx') epl in
        let tyTf = List.fold_right (fun ep tyT -> ElaTyArrow (snd ep, tyT)) eps tyTres in
        let rec build ctx ipl tyT =
          (match ipl with
           | [] -> tyT
           | ip :: rest -> let (a, sr) = ip ctx in ElaTyDepUni (a, sr, build (ela_add_name ctx a) rest tyT)) in
        let tyTf' = build ctx ipl tyTf in
        let inner_ctx = List.fold_left (fun ctx ip -> ela_add_name ctx (fst (ip ctx))) (ela_add_name ctx f) ipl in
        let inner_ctx' = List.fold_left (fun ctx ep -> ela_add_name ctx (fst (ep ctx))) inner_ctx epl in
        let inner_ex = e inner_ctx' in
        let rec build' ctx epl ex =
          (match epl with
           | [] -> ex
           | ep :: rest -> let (x, tyTx) = ep ctx in ElaExAbs (x, build' (ela_add_name ctx x) rest ex)) in
        let ex = build' inner_ctx epl inner_ex in
        let rec build'' ctx ipl ex =
          (match ipl with
           | [] -> ex
           | ip :: rest -> let (a, sr) = ip ctx in ElaExDepAbs (a, sr, build'' (ela_add_name ctx a) rest ex)) in
        let ex' = build'' (ela_add_name ctx f) ipl ex in
          ElaExFix (f, tyTf', ex') }
  | LPAREN; e = expr; RPAREN
    { e }
  | LPAREN; RPAREN
    { fun ctx -> ElaExUnit }
  ;

%{
open Syntax
open GSR
open Utils.Error

%}

%token <Utils.Error.range> LPAREN RPAREN SEMI SEMISEMI COLON SLASH CARET SHARP
%token <Utils.Error.range> PLUS MINUS STAR QUESTION
%token <Utils.Error.range> FUN RARROW TRUE FALSE INT BOOL UNIT SHIFT RESET
%token <Utils.Error.range> IF THEN ELSE PURE
%token <Utils.Error.range> EQUAL GT LT LET IN REC

%token <int Utils.Error.with_range> INTV
%token <Syntax.id Utils.Error.with_range> ID

%start toplevel
%type <Syntax.GSR.program> toplevel

(* Ref: https://caml.inria.fr/pub/docs/manual-ocaml/expr.html *)
%right SEMI
%right prec_if
%left  EQUAL GT LT
%left  PLUS MINUS
%left  STAR SLASH

%%

toplevel :
  | Expr SEMISEMI { Exp $1 }
  | SHARP Directive SEMISEMI { Directive $2 }
  | LET id=ID EQUAL e=Expr SEMISEMI { LetDecl (id.value, e) }

Expr :
  | start=LET id=ID EQUAL e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      Let(r, id.value, e1, e2)}  (* ? *)
  | start=FUN u=OptionalAnswerTypeAnnot id=ID RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Fun (r, u, id.value, Typing.GSR.fresh_tyvar (), e) }
  | start=FUN u1=OptionalAnswerTypeAnnot LPAREN id=ID COLON u2=Type RPAREN RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Fun (r, u1, id.value, u2, e) }
  | start=RESET u=OptionalAnswerTypeAnnot e=Expr {
      let r = join_range start (range_of_exp e) in
      Reset (r, e, u) }
  | start=SHIFT id=ID RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Shift (r, id.value, Typing.GSR.fresh_tyfun, e) }
  | start=SHIFT LPAREN id=ID COLON u=Type RPAREN RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Shift (r, id.value, u, e) }
  | start=PURE e=Expr {
      let r = join_range start (range_of_exp e) in
      Pure (r, e) }
  (* let rec x (y:u1) (^u2) :u3 ^u4 = e1 in e2 *)
  | start=LET REC x=ID y=ID LPAREN CARET u2=Type RPAREN u3=OptionalParamTypeAnnot u4=OptionalAnswerTypeAnnot EQUAL e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      Let (r, x.value, Fix (r, x.value, y.value, Typing.GSR.fresh_tyvar (), u2, u3, u4, e1), e2) }
  | start=LET REC x=ID y=ID u3=OptionalParamTypeAnnot u4=OptionalAnswerTypeAnnot EQUAL e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      Let (r, x.value, Fix (r, x.value, y.value, Typing.GSR.fresh_tyvar (), Typing.GSR.fresh_tyvar (), u3, u4, e1), e2) }
  | start=LET REC x=ID LPAREN y=ID COLON u1=Type RPAREN LPAREN CARET u2=Type RPAREN u3=OptionalParamTypeAnnot u4=OptionalAnswerTypeAnnot EQUAL e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      Let (r, x.value, Fix (r, x.value, y.value, u1, u2, u3, u4, e1), e2) }
  | start=LET REC x=ID LPAREN y=ID COLON u1=Type RPAREN u3=OptionalParamTypeAnnot u4=OptionalAnswerTypeAnnot EQUAL e1=Expr IN e2=Expr {
      let r = join_range start (range_of_exp e2) in
      Let (r, x.value, Fix (r, x.value, y.value, u1, Typing.GSR.fresh_tyvar(), u3, u4, e1), e2) }
  | Consq_expr { $1 }

Consq_expr :
  | e1=Consq_expr SEMI e2=Consq_expr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      Consq (r, e1, e2) }
  | start=IF e1=Consq_expr THEN e2=Consq_expr ELSE e3=Consq_expr {
      let r = join_range start (range_of_exp e3) in
      If (r, e1, e2, e3) } %prec prec_if
  | e1=Consq_expr op=Op e2=Consq_expr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      BinOp (r, op, e1, e2) }
  | App_expr { $1 }

%inline Op :
  | EQUAL { Equal }
  | GT { Gt }
  | LT { Lt }
  | STAR { Mult }
  | SLASH { Div }
  | PLUS { Plus }
  | MINUS { Minus }

App_expr :
  | e1=App_expr e2=SimpleExpr {
    let r = join_range (range_of_exp e1) (range_of_exp e2) in
    App (r, e1, e2) }
  | SimpleExpr { $1 }

SimpleExpr :
  | i=INTV { Const (i.range, ConstInt i.value) }
  | r=TRUE { Const (r, ConstBool true) }
  | r=FALSE { Const (r, ConstBool false) }
  | r=LPAREN RPAREN { Const (r, ConstUnit) }
  | x=ID { Var (x.range, x.value, ref []) }
  | LPAREN Expr RPAREN { $2 }


Type :
  | AType SLASH AType RARROW AType SLASH AType  { TyFun ($1, $3, $5, $7) }
  | AType { $1 }

AType :
  | LPAREN Type RPAREN { $2 }
  | INT { TyBase TyInt }
  | BOOL { TyBase TyBool }
  | UNIT { TyBase TyUnit }
  | QUESTION { TyDyn }

OptionalAnswerTypeAnnot :
  | { Typing.GSR.fresh_tyvar () }
  | CARET Type { $2 }

OptionalParamTypeAnnot :
  | { Typing.GSR.fresh_tyvar () }
  | COLON Type { $2 }

Directive :
  | id=ID TRUE { BoolDir (id.value, true) }
  | id=ID FALSE { BoolDir (id.value, false) }

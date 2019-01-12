%{
open Syntax
open GSR
open Utils.Error

let tyvenv = ref Environment.empty

(* tyvenv -> TV *)
(* for assembling type variable appearing in annotation *)
let ftv_v tyvenv =
  let l = Environment.bindings tyvenv in
  let l' = List.map (fun (_, ty) -> ftv_ty ty) l in
  TV.big_union l'

let param_to_fun r (x, u1, u2) e = match (u1, u2) with
  | (None, None) -> Fun (r, Typing.GSR.fresh_tyvar (), x.value, Typing.GSR.fresh_tyvar (), e)
  | (Some u1, None) -> Fun (r, u1, x.value, Typing.GSR.fresh_tyvar (), e)
  | (None, Some u2) -> Fun (r, Typing.GSR.fresh_tyvar (), x.value, u2, e)
  | (Some u1, Some u2) -> Fun (r, u1, x.value, u2, e)

let insert_asc e u = match u with
  | None -> e
  | Some u -> Asc (range_of_exp e, e, u)

%}

%token <Utils.Error.range> LPAREN RPAREN SEMI SEMISEMI COLON SLASH CARET SHARP
%token <Utils.Error.range> PLUS MINUS STAR QUESTION
%token <Utils.Error.range> FUN RARROW TRUE FALSE INT BOOL UNIT SHIFT RESET
%token <Utils.Error.range> IF THEN ELSE PURE
%token <Utils.Error.range> EQUAL GT LT LET IN REC QUOTE

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
  | p=Program {
      tyvenv := Environment.empty;
      p
    }

Program :
  | Expr SEMISEMI { Exp $1 }
  | SHARP Directive SEMISEMI { Directive $2 }
  | start=LET id=ID params=list(Param) u=Opt_type_annot EQUAL e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let e = insert_asc e u in
      let e = List.fold_right (param_to_fun r) params e in
      LetDecl (id.value, e) }
  | start=LET REC x=ID y=Opt_fix_u1_annot u2=Opt_fix_u2_annot u3=Opt_fix_u3_annot u4=Opt_fix_u4_annot EQUAL e=Expr SEMISEMI {
      let r = join_range start (range_of_exp e) in
      let y, u1 = y in
      LetDecl (x.value, Fix (r, x.value, y.value, u1, u2, u3, u4, e))
  }

Expr :
  | start=LET id=ID params=list(Param) u1=Opt_type_annot EQUAL e1=Expr v=INV e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let e1 = insert_asc e1 u1 in
      let e1 = List.fold_right (param_to_fun r) params e1 in
      Let(r, ftv_v v, id.value, e1, e2)}  (* ? *)
  | start=FUN params=nonempty_list(Param) u=Opt_simple_type_annot RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      let e = insert_asc e u in
      List.fold_right (param_to_fun r) params e
  }
  | start=RESET u=OptionalAnswerTypeAnnot e=Expr {
      let r = join_range start (range_of_exp e) in
      Reset (r, e, u) }
  | start=SHIFT id=ID RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Shift (r, id.value, Typing.GSR.fresh_tyvar (), e) }
  | start=SHIFT LPAREN id=ID COLON u=Type RPAREN RARROW e=Expr {
      let r = join_range start (range_of_exp e) in
      Shift (r, id.value, u, e) }
  | start=PURE e=Expr {
      let r = join_range start (range_of_exp e) in
      Pure (r, e) }
  (* let rec x (y:u1) (^u2) :u3 ^u4 = e1 in e2 *)
  | start=LET REC x=ID y=Opt_fix_u1_annot u2=Opt_fix_u2_annot u3=Opt_fix_u3_annot u4=Opt_fix_u4_annot EQUAL e1=Expr v=INV e2=Expr {
      let r = join_range start (range_of_exp e2) in
      let y, u1 = y in
      Let (r, ftv_v v, x.value, Fix (r, x.value, y.value, u1, u2, u3, u4, e1), e2)
  }
  | Consq_expr { $1 }

Consq_expr :
  | e1=Consq_expr SEMI e2=Consq_expr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      Consq (r, e1, e2) }
  | start=IF e1=Expr THEN e2=Expr ELSE e3=Expr {
      let r = join_range start (range_of_exp e3) in
      If (r, e1, e2, e3) } %prec prec_if
  | e1=Consq_expr op=Op e2=Consq_expr {
      let r = join_range (range_of_exp e1) (range_of_exp e2) in
      BinOp (r, op, e1, e2) }
  | App_expr { $1 }
  | Unary_expr { $1 }

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
    (App (r, e1, e2)) }
  | SimpleExpr { $1 }

Unary_expr :
  | PLUS e=Unary_expr { e }
  | start_r=MINUS e=Unary_expr {
      let r = join_range start_r (range_of_exp e) in
      let zero = Const (dummy_range, ConstInt 0) in
      BinOp (r, Minus, zero, e)
    }
  | App_expr { $1 }

SimpleExpr :
  | i=INTV { Const (i.range, ConstInt i.value) }
  | r=TRUE { Const (r, ConstBool true) }
  | r=FALSE { Const (r, ConstBool false) }
  | r=LPAREN RPAREN { Const (r, ConstUnit) }
  | x=ID { Var (x.range, x.value, ref []) }
  | LPAREN Expr RPAREN { $2 }
  | start=LPAREN e=Expr COLON u=Type last=RPAREN {
      Asc (join_range start last, e, u)}

Type :
  | AType SLASH AType RARROW AType SLASH AType  { TyFun ($1, $3, $5, $7) }
  | AType { $1 }

AType :
  | LPAREN Type RPAREN { $2 }
  | INT { TyBase TyInt }
  | BOOL { TyBase TyBool }
  | UNIT { TyBase TyUnit }
  | QUESTION { TyDyn }
  | QUOTE x=ID {
      try
        Environment.find x.value !tyvenv
      with Not_found ->
        let u = Typing.GSR.fresh_tyvar () in
        tyvenv := Environment.add x.value u !tyvenv;
        u
    }

INV :
  | IN {!tyvenv}

Param :
  | x=ID {(x, None, None)}
  | LPAREN x=ID COLON u=Type RPAREN { (x, None, Some u)}
  | CARET u=Type x=ID  {(x, Some u, None)}
  | CARET u1=Type LPAREN x=ID COLON u2=Type RPAREN  {(x, Some u1, Some u2)}

%inline Opt_type_annot :
  | /* empty */ { None }
  | COLON u=Type { Some u }

%inline Opt_simple_type_annot :
  | /* empty */ { None }
  | COLON u=AType { Some u }

%inline Opt_fix_u1_annot:
  | ID { ($1, Typing.GSR.fresh_tyvar ()) }
  | LPAREN ID COLON Type RPAREN { ($2, $4 ) }

%inline Opt_fix_u2_annot:
  | /* empty */ { Typing.GSR.fresh_tyvar () }
  | LPAREN CARET Type RPAREN { $3 }

%inline Opt_fix_u3_annot:
  | /* empty */ { Typing.GSR.fresh_tyvar ()}
  | COLON AType { $2 }

%inline Opt_fix_u4_annot:
  | /* empty */ { Typing.GSR.fresh_tyvar () }
  | CARET AType { $2 }

%inline OptionalAnswerTypeAnnot :
  | /* empty */ { Typing.GSR.fresh_tyvar () }
  | CARET AType { $2 }

Directive :
  | id=ID TRUE { BoolDir (id.value, true) }
  | id=ID FALSE { BoolDir (id.value, false) }
  | id=ID  { StringDir (id.value) }

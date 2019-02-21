open Syntax
open Syntax.CSR
open Format
open Typing
open Utils.Error

(* Hard errors *)
exception Eval_fatal_error of string
(* Soft errors *)
exception Blame of range * polarity

let subst_type = Typing.subst_type2

let rec subst_exp2 s = function
  | Var (r, x, ys) ->
    let subst_type = function
      | Ty u -> Ty (subst_type s u)
      | TyNu -> TyNu
    in
    Var (r, x, List.map subst_type ys)
  | Const _ as f -> f
  | BinOp (r, op, f1, f2) -> BinOp (r, op, subst_exp2 s f1, subst_exp2 s f2)
  | If (r, f1, f2, f3) -> If (r, subst_exp2 s f1, subst_exp2 s f2, subst_exp2 s f3)
  | Fun (r, u1, x1, u2, f) -> Fun (r, subst_type s u1, x1, subst_type s u2, subst_exp2 s f)
  | App (r, f1, f2) -> App (r, subst_exp2 s f1, subst_exp2 s f2)
  | Cast (r, f, u1, u2, p) -> Cast (r, subst_exp2 s f, subst_type s u1, subst_type s u2, p)
  | Let (r, y, ys, f1, f2) ->
    (* Remove substitutions captured by let exp s *)
    let s = List.filter (fun (x, _) -> not @@ List.memq x ys) s in
    Let (r, y, ys, subst_exp2 s f1, subst_exp2 s f2)
  | Shift (r, k, k_t, f) -> Shift(r, k, subst_type s k_t, subst_exp2 s f)
  | Reset (r, f, u) -> Reset(r, subst_exp2 s f, subst_type s u)
  | Pure (r, ty, f) -> Pure (r, subst_type s ty, subst_exp2 s f)
  | Fix (r, x, y, u1, u2, u3, u4, f) ->
      Fix(r, x, y, subst_type s u1, subst_type s u2, subst_type s u3, subst_type s u4, subst_exp2 s f)
  | _ as x -> x

let fresh_typureparam =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1;
    TyPureVar (v + 1)
  in body

let nu_to_fresh = function
  | Ty u -> u
  | TyNu -> Typing.GSR.fresh_tyvar ()

let rec eval debug exp env cont =
  if debug then
    printf "eval:  %a\n"
      Pp.CSR.pp_print_exp exp;
  match exp with
  | Var (_, x, us) ->
    if Environment.mem x env then
      let xs, v = Environment.find x env in
      let us = List.map nu_to_fresh us in
      begin match v with
        | FunV proc ->
          cont (FunV(fun _ -> proc (xs, us)))
        | _  -> cont v
      end
    else
      raise @@ Eval_fatal_error ("variable not found: " ^ x)
  | Const (_, c) -> begin
      match c with
      | ConstBool b -> cont @@ BoolV b
      | ConstInt i -> cont @@ IntV i
      | ConstUnit -> cont UnitV
    end
  | BinOp (_, op, f1, f2) ->
    eval debug f1 env @@
    fun x1 -> eval debug f2 env @@
    fun x2 -> cont begin
      match op, x1, x2 with
      | Plus, IntV x1, IntV x2 -> IntV (x1 + x2)
      | Minus, IntV x1, IntV x2 -> IntV (x1 - x2)
      | Mult, IntV x1, IntV x2 -> IntV (x1 * x2)
      | Div, IntV x1, IntV x2 -> IntV (x1 / x2)
      | Equal, IntV x1, IntV x2 -> BoolV (x1 = x2)
      | Gt, IntV x1, IntV x2 -> BoolV (x1 > x2)
      | Lt, IntV x1, IntV x2 -> BoolV (x1 < x2)
      | _ -> raise @@ Eval_fatal_error "binop: unexpected type of the argument"
    end
  | Fun (_, _, x, _, f) ->
    cont @@ FunV (fun (xs, ys) -> fun v -> fun c ->
        eval debug (subst_exp2 (Utils.List.zip xs ys) f) (Environment.add x ([],v) env) c)
  | App (_, f1, f2) ->
    eval debug f1 env @@
    fun v1 -> begin
      match v1 with
      | FunV proc ->
        eval debug f2 env @@
        fun v2 ->
        proc ([], []) v2 cont
      | _ -> raise @@ Eval_fatal_error "app: application of non procedure value"
    end
  | Shift (_, k, _, f) ->
    let env' =
      Environment.add k ([],(FunV (fun _ -> fun v -> fun c -> c (cont v)))) env in
    eval debug f env' @@ fun x -> x
  | Reset (_, f, _) ->
    cont @@ eval debug f env @@ fun x -> x
  | If (_, f1, f2, f3) ->
    eval debug f1 env @@
    fun v1 -> begin match v1 with
      | BoolV b -> if b then eval debug f2 env cont else eval debug f3 env cont
      | _ -> raise @@ Eval_fatal_error "if: non-bool condition"
    end
  | Consq (_, f1, f2) ->
    eval debug f1 env @@
    fun v1 -> begin match v1 with
      | UnitV -> eval debug f2 env cont
      | _ -> raise @@ Eval_fatal_error "consq: non-unit expression"
    end
  | Cast (r, f, u1, u2, p) ->
    eval debug f env @@ fun v -> cont @@ cast debug r v u1 u2 p
  | Pure (r, a, f) ->
    let p = fresh_typureparam () in
    let k' = fresh_var () in
    let k'_ty = TyFun(a,TyDyn,p,TyDyn) in
    let f' =
      let f3 = Cast(r, Var (r, k',[]), k'_ty , TyFun (a,TyDyn,TyDyn,TyDyn), Neg) in    (* OK *)
      let f4 = f in
      let f2 = Reset(r, App(r, f3, f4), TyDyn) in
      let f1 = Cast(r, f2, TyDyn, p, Pos ) in
      Shift(r, k', k'_ty, f1) in
    eval debug f' env cont
  | Let (_, x, xs, f1, f2) ->
    let v1 = eval debug f1 env (fun m -> m) in
    let env' = Environment.add x (xs, v1) env in
    eval debug f2 env' cont
  | Fix (_, x, y, _, _, _, _, f') ->
    let f (xs, ys) v k =
      let f' = subst_exp2 (Utils.List.zip xs ys) f' in
      let rec f _ v k =
        let env = Environment.add x (xs, FunV f) env in
        let env = Environment.add y ([], v) env in
        eval debug f' env k
      in f ([], []) v k
    in cont @@ FunV f
and cast debug r v u1 u2 p = (* v: u1 => u2 *)
  if debug then
    printf "cast: %a: %a => %a\n"
      Pp.CSR.pp_print_value v
      Pp.pp_print_type u1
      Pp.pp_print_type u2;
  match u1, u2 with
  | TyVar (_, { contents = Some u1 }), u2
  | u1, TyVar (_, { contents = Some u2 }) ->
    cast debug r v u1 u2 p
  (* Base *)
  | TyVar (p1, _), TyVar (p2, _) when p1 = p2 -> v
  | TyPureVar p1, TyPureVar p2 when p1 = p2 -> v
  | TyBase b1, TyBase b2 when b1 = b2 -> v
  (* Dyn *)
  | TyDyn, TyDyn -> v
  (* Wrap *)
  | TyFun (u11, u12, u13, u14), TyFun (u21, u22, u23, u24) ->
    begin match v with FunV proc ->
      FunV (fun (xs, ys) -> fun b ->
          let subst = subst_type @@ Utils.List.zip xs ys in
          let a = cast debug r b (subst u21) (subst u11) (neg p) in
          fun k ->
            let k' = castk debug r k (subst u23, subst u22) (subst u13, subst u12) p in
            cast debug r (proc (xs, ys) a k') (subst u14) (subst u24) p
        )
                     | _ -> raise @@ Eval_fatal_error "wrap"
    end
  (* Ground *)
  | TyVar (p1, _), TyDyn -> Tagged (P p1, (cast debug r v u1 u1 p))
  | TyPureVar p1, TyDyn -> Tagged (PP p1, (cast debug r v u1 u1 p))
  | TyBase TyBool, TyDyn -> Tagged (B, (cast debug r v u1 u1 p))
  | TyBase TyInt, TyDyn -> Tagged (I, (cast debug r v u1 u1 p))
  | TyBase TyUnit, TyDyn -> Tagged (U, (cast debug r v u1 u1 p))
  | TyFun _, TyDyn -> Tagged (Ar, (cast debug r v u1 tyDynFun p))
  (* Collapse / Conflict *)
  | TyDyn, (TyVar (p2, ({contents=None} as x)) as x') -> begin
      match v with
      | Tagged (P p1, v') when p1 = p2 -> cast debug r v' u2 u2 p
      | Tagged (B |I |U as t,v) ->
        let tag_to_ty = function
          | I -> TyInt
          | B -> TyBool
          | U -> TyUnit
          | _ ->  raise @@  Eval_fatal_error "tag_to_ty" in
        let u = tag_to_ty t in
        if debug then
          printf "DTI: %a is instantiated to %a\n"
            Pp.pp_print_type x'
            Pp.pp_print_basety u;
        x := Some (TyBase u);
        v
      | Tagged (Ar, v) ->
        let u = TyFun(Typing.GSR.fresh_tyvar (),Typing.GSR.fresh_tyvar (), Typing.GSR.fresh_tyvar (), Typing.GSR.fresh_tyvar ()) in
        if debug then
          printf "DTI: %a is instantiated to %a\n"
            Pp.pp_print_type x'
            Pp.pp_print_type u;
        x := Some u;
        cast debug r v tyDynFun u p
      | Tagged (PP p1,v) ->
        if debug then
          printf "DTI: %a is instantiated to %a\n"
            Pp.pp_print_type x'
            Pp.pp_print_type (TyPureVar (p1));
        x := Some (TyPureVar (p1));
        v
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 1"
    end
  | TyDyn, TyPureVar p2 -> begin
      match v with
      | Tagged (PP p1, v') when p1 = p2 -> cast debug r v' u2 u2 p
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 6"
    end
  | TyDyn, TyBase TyBool -> begin
      match v with
      | Tagged (B, v') -> cast debug r v' (TyBase TyBool) (TyBase TyBool) p
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 2"
    end
  | TyDyn, TyBase TyInt -> begin
      match v with
      | Tagged (I, v') -> cast debug r v' (TyBase TyInt) (TyBase TyInt) p
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 3"
    end
  | TyDyn, TyBase TyUnit -> begin
      match v with
      | Tagged (U, v') -> cast debug r v' (TyBase TyUnit) (TyBase TyUnit) p
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 4"
    end
  | TyDyn, TyFun _ -> begin
      match v with
      | Tagged (Ar, v') -> cast debug r v' tyDynFun u2 p
      | Tagged (_, _) -> raise @@ Blame (r, p)
      | _ -> raise @@ Eval_fatal_error "untagged value 5"
    end
  | _ -> raise @@ Eval_fatal_error "cast is not implemented"
and castk debug r k (u12, u13) (u22, u23) p = fun v ->
  let v' = cast debug r v u22 u12 (neg p) in
  cast debug r (k v') u13 u23 p

let eval_program debug e env cont = match e with
  | Exp f ->
    env, "-", eval debug f env cont
  | LetDecl (x, xs, f) ->
    let v = eval debug f env cont in
    let env = Environment.add x (xs, v) env in
    env, x, v

open Constraints
open Syntax

(* Fatal errors *)
exception Type_fatal_error of string

(* Soft errors *)
exception Type_error of string
exception Type_error1 of
    ((Format.formatter -> ty -> unit) -> ty -> unit, Format.formatter, unit) Pervasives.format
    * ty
exception Type_error2 of
    ((Format.formatter -> ty -> unit) -> ty -> (Format.formatter -> ty -> unit) -> ty -> unit, Format.formatter, unit) Pervasives.format
    * ty * ty
exception Unification_error of
    ((Format.formatter -> constr -> unit) -> constr -> unit, Format.formatter, unit) Pervasives.format
    * constr

(* Utilities *)

let is_tyvar = function TyVar _ -> true | _ -> false

(* ty -> bool *)
let rec is_static_type = function
  | TyFun (t1, t2, t3, t4) -> (is_static_type t1) && (is_static_type t2) && (is_static_type t3) && (is_static_type t4)
  | TyDyn -> false
  | _ -> true

(* ty list -> bool *)
let is_static_types types = List.fold_left (&&) true @@ List.map is_static_type types

let domf = function
  | TyFun (u, _, _, _) -> u
  | TyDyn -> TyDyn
  | _ -> raise @@ Type_fatal_error "domf: failed to match"

let codc = function
  | TyFun (_, u, _, _) -> u
  | TyDyn -> TyDyn
  | _ -> raise @@ Type_fatal_error "codc: failed to match"

let domc = function
  | TyFun (_, _, u, _) -> u
  | TyDyn -> TyDyn
  | _ -> raise @@ Type_fatal_error "domc: failed to match"

let codf = function
  | TyFun (_, _, _, u) -> u
  | TyDyn -> TyDyn
  | _ -> raise @@ Type_fatal_error "codf: failed to match"

let rec meet u1 u2 = match u1, u2 with
  | u1, u2 when u1 = u2 -> u1
  | u, TyDyn | TyDyn, u -> u
  | TyFun (u11, u12, u13, u14), TyFun (u21, u22, u23, u24) ->
    TyFun (meet u11 u21, meet u12 u22, meet u13 u23, meet u14 u24)
  | _ -> raise @@ Type_fatal_error "meet: failed to match"

let rec is_consistent u1 u2 = match u1, u2 with
  | TyVar (p1, _), TyVar (p2, _) when p1 = p2 -> true
  | TyBase b1, TyBase b2 when b1 = b2 -> true
  | _, TyDyn
  | TyDyn, _ -> true
  | TyFun (u11, u12, u13, u14), TyFun (u21, u22, u23, u24) ->
    is_consistent u11 u21 &&
    is_consistent u12 u22 &&
    is_consistent u13 u23 &&
    is_consistent u14 u24
  | _ -> false

(* Base type or type variables *)
let is_bvp_type = function
  | TyBase _ -> true
  | TyVar _ -> true
  | _ -> false

let type_of_const c = TyBase (match c with
    | ConstBool _ -> TyBool
    | ConstInt _ -> TyInt
    | ConstUnit -> TyUnit
  )

let type_of_binop = function
  | Plus | Minus | Mult | Div -> TyBase TyInt, TyBase TyInt, TyBase TyInt
  | Equal | Gt | Lt -> TyBase TyInt, TyBase TyInt, TyBase TyBool

let fresh_var =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1;
    "!k" ^ string_of_int @@ v + 1
  in body

(* Substitutions for constraints *)

type substitution = tyvar * ty
type substitutions = substitution list

(* [x:=t]u *)
let rec subst_type (x : tyvar) (t : ty) = function
  | TyFun (u1, u2, u3, u4) -> TyFun (subst_type x t u1, subst_type x t u2, subst_type x t u3, subst_type x t u4)
  | TyVar (x', _) as u -> begin match x with (i, _) -> if x'=i then t else u end
  | _ as u -> u

(* [x:=t]e *)
let rec subst_exp x t e = GSR.map (subst_type x t) (subst_exp x t) e

(* [x:=t]c *)
let subst_constraint x t = function
  | CEqual (u1, u2) -> CEqual (subst_type x t u1, subst_type x t u2)
  | CConsistent (u1, u2) -> CConsistent (subst_type x t u1, subst_type x t u2)

(* [x:=t]C *)
let subst_constraints x t (c : constr list) =
  (* TODO: OK? *)
  List.map (subst_constraint x t) c

(* S(t) *)
let subst_type_substitutions (t : ty) (s : substitutions) =
  List.fold_left (fun u -> fun (x, t) -> subst_type x t u) t s

(* S(e) *)
let subst_exp_substitutions e (s : substitutions) =
  List.fold_left (fun e -> fun (x, t) -> subst_exp x t e) e s

(* let subst_env_substitutions env s =
   Environment.map @@ fun (TyScheme (xs, u)) -> TyScheme (subst_type2 , subst_type u) *)
(* *)


(* substitution for var argument *)
let subst_type2 (s: (tyvar * ty) list) (u: ty) =
  (* {X':->U'}(U) *)
  let rec subst u ((a', _), u' as s0) = match u with
    | TyFun (u1, u2, u3, u4) -> TyFun (subst u1 s0, subst u2 s0, subst u3 s0, subst u4 s0)
    | TyVar (a, { contents = None }) when a = a' -> u'
    | TyVar (_, { contents = Some u }) -> subst u s0
    | _ as u -> u
  in
  List.fold_left subst u s

module GSR = struct
  open Syntax.GSR

  let is_pure = function
    | Var _ -> true
    | Const _ -> true
    | Fun _  -> true
    | Reset _ -> true
    | Pure _ -> true
    | Fix _ -> true
    | _ -> false

  let fresh_tyvar =
    let counter = ref 0 in
    let body () =
      let v = !counter in
      counter := v + 1;
      TyVar (v + 1, {contents = None})
    in body

  let fresh_tyfun = TyFun(fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar ())

  (* Type Inference *)

  (* domf = *)
  let generate_constraints_domf_eq = function
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      x1, Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4)))
    | TyFun (u1, _, _, _) -> u1, Constraints.empty
    | TyDyn -> TyDyn, Constraints.empty
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: domf(%a) is undefined", u)

  (* domc = *)
  let generate_constraints_domc_eq = function
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      x3, Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4)))
    | TyFun (_, _, u3, _) -> u3, Constraints.empty
    | TyDyn -> TyDyn, Constraints.empty
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: domc(%a) is undefined", u)

  (* codc = *)
  let generate_constraints_codc_eq = function
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      x2, Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4)))
    | TyFun (_, u2, _, _) -> u2, Constraints.empty
    | TyDyn -> TyDyn, Constraints.empty
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: codc(%a) is undefined", u)

  (* codf = *)
  let generate_constraints_codf_eq = function
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      x4, Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4)))
    | TyFun (_, _, _, u4) -> u4, Constraints.empty
    | TyDyn -> TyDyn, Constraints.empty
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: codf(%a) is undefined", u)

  (* domf ~ *)
  let generate_constraints_domf_con u1 u2 = match u1 with
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      let c = Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4))) in
      Constraints.add (CConsistent (x1, u2)) c
    | TyFun (u11, _, _, _) ->
      Constraints.singleton @@ CConsistent (u11, u2)
    | TyDyn -> Constraints.singleton @@ CConsistent (u1, u2)
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: domf(%a) is undefined", u)

  (* codf ~ *)
  let generate_constraints_codf_con u1 u2 = match u1 with
    | TyVar x ->
      let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
      let c = Constraints.singleton @@ CEqual ((TyVar x), (TyFun (x1, x2, x3, x4))) in
      Constraints.add (CConsistent (x4, u2)) c
    | TyFun (_, _, _, u14) ->
      Constraints.singleton @@ CConsistent (u14, u2)
    | TyDyn -> Constraints.singleton @@ CConsistent (u1, u2)
    | _ as u -> raise @@ Type_error1 ("failed to generate constraints: codf(%a) is undefined", u)

  let rec generate_constraints_meet u1 u2 = match u1, u2 with
    | TyBase b1, TyBase b2 when b1 = b2 -> TyBase b1, Constraints.empty
    | _, TyDyn -> u1, Constraints.singleton @@ CConsistent (u1, TyDyn)
    | TyDyn, _ -> u2, Constraints.singleton @@ CConsistent (TyDyn, u2)
    | TyVar _, _ -> u1, Constraints.singleton @@ CConsistent (u1, u2)
    | _, TyVar _ -> u2, Constraints.singleton @@ CConsistent (u1, u2)
    | TyFun (u11, u12, u13, u14), TyFun (u21, u22, u23, u24) ->
      let u1, c1 = generate_constraints_meet u11 u21 in
      let u2, c2 = generate_constraints_meet u12 u22 in
      let u3, c3 = generate_constraints_meet u13 u23 in
      let u4, c4 = generate_constraints_meet u14 u24 in
      let c = Constraints.union c1 c2 in
      let c = Constraints.union c c3 in
      let c = Constraints.union c c4 in
      TyFun (u1, u2, u3, u4), c
    | _ -> raise @@ Type_error2 ("failed to generate constraints: meet(%a, %a) is undefined", u1, u2)

  let unify constraints : substitutions =
    let rec unify c =
      match c with
      | [] -> []
      | constr :: c -> begin
          match constr with
          | CConsistent (u1, u2) when u1 = u2 && is_bvp_type u1 ->
            unify c
          | CConsistent (TyDyn, _)
          | CConsistent (_, TyDyn) ->
            unify c
          | CConsistent (TyFun (u11, u12, u13, u14), TyFun (u21, u22, u23, u24)) ->
            unify @@ CConsistent (u11, u21) :: CConsistent (u12, u22) :: CConsistent (u13, u23) :: CConsistent (u14, u24) :: c
          | CConsistent (u, TyVar x) when not @@ is_tyvar u ->
            unify @@ CConsistent (TyVar x, u) :: c
          | CConsistent (TyVar x, u) when is_bvp_type u ->
            unify @@ CEqual (TyVar x, u) :: c
          | CConsistent (TyVar x, TyFun (u1, u2, u3, u4)) when not @@ TV.mem x (ftv_ty (TyFun (u1, u2, u3, u4))) ->
            let x1, x2, x3, x4 = fresh_tyvar (), fresh_tyvar (), fresh_tyvar (), fresh_tyvar () in
            unify @@ CEqual (TyVar x, TyFun (x1, x2, x3, x4)) :: CConsistent (x1, u1) :: CConsistent (x2, u2) :: CConsistent (x3, u3) :: CConsistent (x4, u4) :: c
          | CEqual (t1, t2) when t1 = t2 && is_static_type t1 && is_bvp_type t1 ->
            unify c
          | CEqual (TyFun (t11, t12, t13, t14), TyFun (t21, t22, t23, t24)) when is_static_types [t11; t12; t13; t14; t21; t22; t23; t24] ->
            unify @@ CEqual (t11, t21) :: CEqual (t12, t22) :: CEqual (t13, t23) :: CEqual (t14, t24) :: c
          | CEqual (t, TyVar x) when is_static_type t && not (is_tyvar t) ->
            unify @@ CEqual (TyVar x, t) :: c
          | CEqual (TyVar x, t) when not @@ TV.mem x (ftv_ty t) ->
            let s = unify @@ subst_constraints x t c in
            (x, t) :: s

          | CEqual (TyDyn,TyDyn) -> unify c (*add*)
          | CEqual (TyDyn,TyVar x) -> unify @@ CEqual(TyVar x,TyDyn)::c
          | CEqual (TyVar x,TyDyn) ->
            let s = unify @@ subst_constraints x TyDyn c in
            (x, TyDyn) :: s
          | CEqual (TyFun (t11, t12, t13, t14), TyFun (t21, t22, t23, t24)) ->
            unify @@ CEqual (t11, t21) :: CEqual (t12, t22) :: CEqual (t13, t23) :: CEqual (t14, t24) :: c
          | _ ->
            raise @@ Unification_error ("cannot unify: %a", constr)
        end
    in
    unify @@ Constraints.to_list constraints

  (* Utility functions for let polymorpism *)

  let closure_tyvars1 u1 env v1 =
    TV.elements @@ TV.diff (ftv_ty u1) @@ TV.union (ftv_tyenv env) (ftv_exp v1)

  (* let closure_tyvars_let_decl e u1 env =
    TV.elements @@ TV.diff (TV.union (tv_exp e) (ftv_ty u1)) (ftv_tyenv env) *)

  let closure_tyvars2 w1 env u1 v1 =
    let ftvs = TV.big_union [ftv_tyenv env; ftv_ty u1; ftv_exp v1] in
    TV.elements @@ TV.diff (Syntax.CSR.ftv_exp w1) ftvs

  let generate_constraints env e b =
    let rec generate_constraints env e b =
      let t, a, c = match e with
        | Var (_, x, ys) ->
          let u_a = b in (
            try
              let TyScheme (xs, u)= Environment.find x env in
              (* Replace type variables with fresh ones *)
              ys := List.map (fun _ -> fresh_tyvar ()) xs;
              let s = Utils.List.zip xs !ys in
              (subst_type2 s u), u_a, Constraints.empty
            with Not_found ->
              raise @@ Type_error (Printf.sprintf "variable '%s' not found in the environment" x)
          )
        | Const (_, c) ->
          let u_a = b in
          let u = type_of_const c in
          u, u_a, Constraints.empty
        | BinOp (_, op, e1, e2) ->
          let ui1, ui2, ui = type_of_binop op in
          let u_a0 = b in
          let u1, u_a1, c1 = generate_constraints env e1 u_a0 in
          let u2, u_a2, c2 = generate_constraints env e2 u_a1 in
          let c = Constraints.union c1
            @@ Constraints.union c2
            @@ (Constraints.add (CConsistent (u1, ui1))
                @@ Constraints.singleton
                @@ CConsistent (u2, ui2) )in
          ui, u_a2, c
        | Fun (_, u_g, x, u_1, e) ->
          let u_a = b in
          let u_2, u_b, c = generate_constraints (Environment.add x (tysc_of_ty u_1) env) e u_g in
          TyFun (u_1, u_b, u_2, u_g), u_a, c

        | App (_, e1, e2) ->
          let u_d = b in
          let u_1, u_g, c1 = generate_constraints env e1 u_d in
          let u_2, u_b, c2 = generate_constraints env e2 u_g in
          let u, c3 = generate_constraints_domc_eq u_1 in
          let u_a, c4 = generate_constraints_codc_eq u_1 in
          let c5 = generate_constraints_codf_con u_1 u_b in
          let c6 = generate_constraints_domf_con u_1 u_2 in
          let c = Constraints.union c1
            @@ Constraints.union c2
            @@ Constraints.union c3
            @@ Constraints.union c4
            @@ Constraints.union c5 c6 in
          u, u_a, c
        | Shift (_, k, u_s, e) ->
          let u_b = b in
          let u_d, u_d', c1 = generate_constraints (Environment.add k (tysc_of_ty u_s) env) e u_b in
          let u_a, c2 = generate_constraints_domc_eq u_s in
          let u, c3 = generate_constraints_domf_eq u_s in
          let u_g1, c4 = generate_constraints_codc_eq u_s in
          let u_g2, c5 = generate_constraints_codf_eq u_s in
          let _, c6 = generate_constraints_meet u_g1 u_g2 in
          let c = Constraints.union c1
            @@ Constraints.union c2
            @@ Constraints.union c3
            @@ Constraints.union c4
            @@ Constraints.union c5
            @@ Constraints.union c6
            @@ Constraints.singleton
            @@ CConsistent (u_d, u_d') in
          u, u_a, c
        | Reset (_, e, u) ->
          let u_a = b in
          let u_b, u_b', c = generate_constraints env e u in
          let c = Constraints.add (CConsistent (u_b, u_b')) c in
          u, u_a, c
        | If (_, e1, e2, e3) ->
          let u_b = b in
          let u_1, u_d, c1 = generate_constraints env e1 u_b in
          let u_2, u_a2, c2 = generate_constraints env e2 u_d in
          let u_3, u_a3, c3 = generate_constraints env e3 u_d in
          let u_a, c4 = generate_constraints_meet u_a2 u_a3 in
          let u, c5 = generate_constraints_meet u_2 u_3 in
          let c = Constraints.union c1
            @@ Constraints.union c2
            @@ Constraints.union c3
            @@ Constraints.union c4
            @@ Constraints.union c5
            @@ Constraints.singleton
            @@ CConsistent (u_1, TyBase TyBool) in
          u, u_a, c
        | Consq (_, e1, e2) ->
          let u_g = b in
          let u_1, u_b, c1 = generate_constraints env e1 u_g in
          let u_2, u_a, c2 = generate_constraints env e2 u_b in
          let c = Constraints.union c1
            @@ Constraints.union c2
            @@ Constraints.singleton
            @@ CConsistent (u_1, TyBase TyUnit) in
          u_2, u_a, c
        | Pure (_, e) ->
          let u_b = b in
          let a, u_a, c1 = generate_constraints env e TyDyn in
          let u_a = subst_type_substitutions u_a (unify c1) in
          if u_a = TyDyn then
            a, u_b, c1
          else
            raise @@ Type_error (Printf.sprintf "pure error")
        | Let (r, id, e1, e2) ->
          let u_b = b in
          let u1, _, c1 = generate_constraints env e1 (fresh_tyvar ()) in
          if is_pure e1 then
            let unify = unify c1 in
            let u1 = subst_type_substitutions u1 unify in
            (* let env = subst_env_substitutions env unify in *) (* problem *)
            let e1 = subst_exp_substitutions e1 unify in
            let xs = closure_tyvars1 u1 env e1 in
            let us1 = TyScheme (xs,u1) in
            let a, _, c2 = generate_constraints (Environment.add id us1 env) e2 u_b in
            let c = Constraints.union c1 c2 in
            a, u_b, c
          else
            generate_constraints env (App (r, Fun (r, fresh_tyvar (), id, fresh_tyvar(), e2), e1)) u_b
        | Fix (_, x, y, u1, u2, u3, u4, e) ->
          let u_b = b in
          let u = TyFun (u1, u2, u3, u4)  in
          let env = Environment.add x (tysc_of_ty u) (Environment.add y (tysc_of_ty u1) env) in
          let u3', u2', c1 = generate_constraints env e u4 in
          let c = Constraints.union c1
            @@ (Constraints.add (CConsistent (u2, u2'))
            @@ Constraints.singleton (CConsistent (u3, u3'))) in
          u, u_b, c
      in
      t, a, c
    in
    generate_constraints env e b

  let cast f u1 u2 = if u1 = u2 then f else CSR.Cast (CSR.range_of_exp f, f, u1, u2, Pos)

  (* if translate raises an error, it must be some problem in inference *)
  let rec translate env e u_b = match e with
    | Var (r, x, ys) -> begin
        try
          let TyScheme (xs, u) = Environment.find x env in
          let ftvs = ftv_ty u in
          let s = Utils.List.zip xs !ys in
          let ys = List.map (fun (x, u) -> if TV.mem x ftvs then CSR.Ty u else CSR.TyNu) s
          in
          let ys = ys @ Utils.List.repeat CSR.TyNu (List.length xs - List.length ys) in
          let u = subst_type2 (List.filter (fun (x, _) -> TV.mem x ftvs) s) u in
          CSR.Var (r, x, ys), u, u_b
        with Not_found ->
          raise @@ Type_fatal_error (Printf.sprintf "variable '%s' not found in the environment" x)
      end
    | Const (r, c) ->
      let u = type_of_const c in
      CSR.Const (r, c), u, u_b
    | BinOp (r, op, e1, e2) ->
      let ui1, ui2, ui = type_of_binop op in
      let f1, u1, u1_a = translate env e1 u_b in
      let f2, u2, u2_a = translate env e2 u1_a in
      if is_consistent u1 ui1 then
        if is_consistent u2 ui2 then
          CSR.BinOp (r, op, (cast  f1 u1 ui1), (cast f2 u2 ui2)), ui, u2_a
        else
          raise @@ Type_fatal_error "binop: the second argument"
      else
        raise @@ Type_fatal_error "binop: the first argument"
    | Fun (r, u_g, x, u_1, e) ->
      let u_a = u_b in
      let f, u_2, u_b = translate (Environment.add x (tysc_of_ty u_1) env) e u_g in
      CSR.Fun (r,u_g, x, u_1, f), TyFun (u_1, u_b, u_2, u_g), u_a
    | App (r, e1, e2) ->
      let f1, u1, u_g = translate env e1 u_b in
      let f2, u2, u_b = translate env e2 u_g in
      begin match is_consistent (codf u1) u_b, is_consistent (domf u1) u2 with
        | true, true ->
          CSR.App (r, cast f1 u1 (TyFun (domf u1, codc u1, domc u1, u_b)),
                   cast f2 u2 (domf u1)),
          domc u1,
          codc u1
        | _ -> raise @@ Type_fatal_error "app: not consistent"
      end
    | Shift (r, k, u_s, e) ->
      let f, u_d, u_d' = translate (Environment.add k (tysc_of_ty u_s) env) e u_b in
      let u_g = meet (codc u_s) (codf u_s) in
      let k' = fresh_var () in
      begin match is_consistent u_d u_d', is_consistent (codc u_s) (codf u_s) with
        | true, true ->
          let f' = cast f u_d u_d' in
          let u_s' = TyFun (domf u_s, u_g, domc u_s, u_g) in
          begin
            if u_s = u_s' then
              CSR.Shift (r, k, u_s', f')
            else
              CSR.Shift (
                r, k', u_s',
                CSR.App (r, CSR.Fun (r, u_b, k, u_s, f'),
                         CSR.Cast (r, CSR.Var (r, k',[]), u_s', u_s, Neg)))  (*???*)
          end,
          domf u_s,
          domc u_s
        | _ -> raise @@ Type_fatal_error "shift: not consistent"
      end
    | Reset (r, e, u) ->
      let u_a = u_b in
      let f, u_b, u_b' = translate env e u in
      if is_consistent u_b u_b' then
        CSR.Reset (r, cast f u_b u_b', u), u, u_a
      else
        raise @@ Type_fatal_error "reset: not consistent"
    | If (r, e1, e2, e3) ->
      let f1, u1, u_d = translate env e1 u_b in
      let f2, u2, u_a2 = translate env e2 u_d in
      let f3, u3, u_a3 = translate env e3 u_d in
      let u_a = meet u_a2 u_a3 in
      let u = meet u2 u3 in
      let k2, k3 = fresh_var (), fresh_var () in
      let cast_e  k' f' u' u_a' =
        let r = CSR.range_of_exp f' in
        let f' = cast f' u' u in
        if u_a = u_a' then
          f'
        else
          CSR.Shift (
            r, k', TyFun (u, u_a, u_a, u_a),
            CSR.App (
              r, CSR.Cast (r, CSR.Var (r, k',[]), TyFun (u, u_a, u_a, u_a),
                           TyFun (u, u_a, u_a, u_a'), Neg), (* ? *)
              f')) in
      if is_consistent u1 @@ TyBase TyBool then
        CSR.If (
          r,
          cast f1 u1 (TyBase TyBool),
          cast_e k2 f2 u2 u_a2,
          cast_e k3 f3 u3 u_a3
        ), u, u_a
      else
        raise @@ Type_fatal_error "if: not consistent"
    | Consq (r, e1, e2) ->
      let u_g = u_b in
      let f1, u1, u_b = translate env e1 u_g in
      let f2, u2, u_a = translate env e2 u_b in
      if is_consistent u1 @@ TyBase TyUnit then
        CSR.Consq (r, cast f1 u1 (TyBase TyUnit), f2), u2, u_a
      else
        raise @@ Type_fatal_error "consq: not consistent"
    | Pure (r, e) ->
      let u_b' = u_b in
      let f, a, u_a  = translate env e TyDyn in
      if u_a = TyDyn then
        (CSR.Pure (r, a, f)), a, u_b'
      else
        raise @@ Type_fatal_error "pure: not consistent"
    | Let (r, x, e1, e2) when is_pure  e1 ->
      let alpha = fresh_tyvar () in  (* answer type polymorphism *)
      let f1, u1, _ = translate env e1 alpha in
      let xs = closure_tyvars1 u1 env e1 in
      let ys = closure_tyvars2 f1 env u1 e1 in
      let zs = TV.elements((ftv_ty alpha)) in
      let xys = xs @ (ys @ zs) in
      let us1 = TyScheme (xys, u1) in
      let f2, u2, u_a = translate (Environment.add x us1 env) e2 u_b in
      CSR.Let (r, x, xys, f1, f2), u2, u_a
    | Let (r, x, e1, e2) ->
      let _, u1, _ = translate env e1 u_b in
      let e = App (r, Fun (r, u_b, x, u1, e2), e1) in
      translate env e u_b
    | Fix (r, x, y, u1, u2, u3, u4, e) ->   (* polarity? *)
      let u = TyFun (u1, u2, u3, u4) in
      let env = Environment.add x (tysc_of_ty u) (Environment.add y (tysc_of_ty u1) env) in
      let f, u3', u2' = translate env e u4 in
      if is_consistent u2 u2' && is_consistent u3 u3' then
        let u' = TyFun (u1, u2', u3', u4) in
        let y' = fresh_var () in
        let f' = cast (CSR.Fun(r, u4, y', u1, f)) u' u in
        CSR.Fix (r, x, y, u1, u2, u3, u4, CSR.App (r, f', Var(r, y, []))), u, u_b
      else
        raise @@ Type_fatal_error "fix not consistent"
end

(* When you're sure that this tyarg does not contain ν
 * you can convert it to ty *)
let tyarg_to_ty = function
  | CSR.Ty u -> u
  | CSR.TyNu -> raise @@ Type_fatal_error "failed to cast tyarg to ty"

module CSR = struct
  open Syntax.CSR

  let is_pure = function
    | Var _ -> true
    | Const _ -> true
    | Fun _  -> true
    | Reset _ -> true
    | Pure _ -> true
    | Fix _ -> true
    | _ -> false

  let rec type_of_exp env f ub = match f with
    | Var (_, x, ys) ->
      begin
        try
          let TyScheme (xs, u) = Environment.find x env in
          if List.length xs = List.length ys then
            let ftvs = ftv_ty u in
            let s = Utils.List.zip xs ys in
            let s = List.filter (fun (x, _) -> TV.mem x ftvs) s in
            let s = List.map (fun (x, u) -> x, tyarg_to_ty u) s in
            (subst_type2 s u), ub
          else
            raise @@ Type_fatal_error (Printf.sprintf "invalid type application")
        with Not_found ->
          raise @@ Type_fatal_error (Printf.sprintf "variable '%s' not found in the environment" x)
      end
    | Const (_, c) ->
      let u = type_of_const c in
      u, ub
    | BinOp (_, op, f1, f2) ->
      let ui1, ui2, ui = type_of_binop op in
      let u1, ua1 = type_of_exp env f1 ub in
      let u2, ua2 = type_of_exp env f2 ua1 in
      if u1 = ui1 then
        if u2 = ui2 then
          ui, ua2
        else
          raise @@ Type_fatal_error "binop: the second argument type"
      else
        raise @@ Type_fatal_error "binop: the first argument type"
    | Fun (_, ug, x, u1, f) ->
      let ua = ub in
      let u2, ub = type_of_exp (Environment.add x (tysc_of_ty u1) env) f ug in
      TyFun (u1, ub, u2, ug), ua
    | App (_, f1, f2) ->
      let ud = ub in
      let u1, ug = type_of_exp env f1 ud in
      let u2, ub = type_of_exp env f2 ug in
      begin match u1, (codf u1) = ub, (domf u1) = u2 with
        | TyFun _, true, true -> domc u1, codc u1
        | _ -> raise @@ Type_fatal_error "app"
      end
    | Shift (_, k, us, f) ->
      let ud, ud' = type_of_exp (Environment.add k (tysc_of_ty us) env) f ub in
      begin match us, (codc us) = (codf us), ud = ud' with
        | TyFun _, true, true -> domf us, domc us
        | _ -> raise @@ Type_fatal_error "shift"
      end
    | Reset (_, f, u) ->
      let ua = ub in
      let ub, ub' = type_of_exp env f u in
      if ub = ub' then
        u, ua
      else
        raise @@ Type_fatal_error "reset"
    | If (_, f1, f2, f3) ->
      let u1, ud = type_of_exp env f1 ub in
      let u2, ua2 = type_of_exp env f2 ud in
      let u3, ua3 = type_of_exp env f3 ud in
      begin match u1 = TyBase TyBool, u2 = u3, ua2 = ua3 with
        | true, true, true -> u2, ua2
        | _ -> raise @@ Type_fatal_error "if"
      end
    | Consq (_, f1, f2) ->
      let ug = ub in
      let u1, ub = type_of_exp env f1 ug in
      let u2, ua = type_of_exp env f2 ub in
      if u1 = TyBase TyUnit then
        u2, ua
      else
        raise @@ Type_fatal_error "consq"
    | Cast (_, f, u1, u2, _) ->
      let u1', ua = type_of_exp env f ub in
      begin match u1 = u1', is_consistent u1 u2 with
        | true, true -> u2, ua
        | _ -> raise @@ Type_fatal_error "cast"
      end
    | Pure (_, a, f) ->
      let a', ua = type_of_exp env f TyDyn in
      if a=a'  && ua = TyDyn then
        a, ub
      else raise @@ Type_fatal_error "pure"
    | Let (_, x, xs, f1, f2) when is_pure f1 ->
      let u1, _ = type_of_exp env f1 ub in
      let us1 = TyScheme (xs, u1) in
      let u2,u_b = type_of_exp (Environment.add x us1 env) f2 ub in
      u2, u_b
    | Let _ ->
      raise @@ Type_fatal_error "invalid translation for let expression"
    | Fix (_, x, y, u1, u2, u3, u4, f) ->
      let u = TyFun (u1, u2, u3, u4) in
      let u3', u2' = type_of_exp (Environment.add x (tysc_of_ty u) (Environment.add y (tysc_of_ty u1) env)) f u4 in
      if u2=u2' && u3=u3' then
        u, ub
      else
        raise @@ Type_fatal_error "fix"
end

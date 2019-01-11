open Utils.Error
(* Types *)
type basety =
  | TyBool
  | TyInt
  | TyUnit

type ty =
  | TyPureVar of int
  | TyVar of tyvar
  | TyBase of basety
  | TyFun of ty * ty * ty * ty
  | TyDyn
and tyvar = int * ty option ref

type tysc = TyScheme of tyvar list * ty

let tysc_of_ty u = TyScheme ([], u)

type id = string

(* Type Environment *)
module Environment = Map.Make (
  struct
    type t = id
    let compare (x : id) y = compare x y
  end
  )

(** Module for a set of type variables. *)
module TV = struct
  include Set.Make (
    struct
      type t = tyvar
      let compare (a1, _ : tyvar) (a2, _) = compare a1 a2
    end
    )
  let big_union vars = List.fold_right union vars empty
end

(** Returns a set of free type variables in a given type. *)
let rec ftv_ty: ty -> TV.t = function
  | TyVar (_, { contents = None } as x) -> TV.singleton x
  | TyVar (_, { contents = Some u }) -> ftv_ty u
  | TyFun (u1, u2, u3, u4) ->
    TV.big_union [ftv_ty u1; ftv_ty u2; ftv_ty u3; ftv_ty u4; ] (* ? *)
  | _ -> TV.empty

let ftv_tysc: tysc -> TV.t = function
  | TyScheme (xs, u) -> TV.diff (ftv_ty u) (TV.of_list xs)

let ftv_tyenv (env: tysc Environment.t): TV.t =
  Environment.fold (fun _ us vars -> TV.union vars (ftv_tysc us)) env TV.empty

let tyDynFun = TyFun (TyDyn, TyDyn, TyDyn, TyDyn)

(* Syntax *)
type const =
  | ConstBool of bool
  | ConstInt of int
  | ConstUnit

type binop =
  | Plus
  | Minus
  | Mult
  | Div
  | Equal
  | Gt
  | Lt

module GSR = struct
  type exp =
    | Var of range * id * ty list ref
    | Const of range * const
    | BinOp of range * binop * exp * exp
    | Fun of range * ty * id * ty * exp (* λ^12:3.4 *)
    | App of range * exp * exp
    | Shift of range * id * ty * exp (* S1:2.3 *)
    | Reset of range * exp * ty (* <1>^2 *)
    | If of range * exp * exp * exp
    | Consq of range * exp * exp
    | Pure of range * exp
    | Let of range * TV.t * id * exp * exp
    | Fix of range * id * id * ty * ty * ty * ty * exp
    | Asc of range * exp * ty

  let range_of_exp = function
    | Var (r, _, _)
    | Const (r, _)
    | BinOp (r, _, _, _)
    | Fun (r, _, _, _, _)
    | App (r, _, _)
    | Shift (r, _, _, _)
    | Reset (r, _, _)
    | If (r, _, _, _)
    | Consq (r, _, _)
    | Pure (r, _)
    | Let (r, _, _, _, _)
    | Fix (r, _, _, _, _, _, _, _)
    | Asc (r, _, _) -> r

  type directive =
    | BoolDir of string * bool
    | StringDir of string

  type program =
    | Exp of exp
    | Directive of directive
    | LetDecl of id * exp

  let map f_ty f_exp = function
    | Var (r, x, tyl) -> let tyl' = List.map f_ty !tyl in Var(r, x, ref tyl')
    | Const _ as e -> e
    | BinOp (r, op, e1, e2) -> BinOp (r, op, f_exp e1, f_exp e2)
    | Fun (r, g, x1, x1_t, e) -> Fun (r, f_ty g, x1, f_ty x1_t, f_exp e)
    | App (r, e1, e2) -> App (r, f_exp e1, f_exp e2)
    | Shift (r, k, k_t, e) -> Shift (r, k, f_ty k_t, f_exp e)
    | Reset (r, e, u) -> Reset (r, f_exp e, f_ty u)
    | If (r, e1, e2, e3) -> If (r, f_exp e1, f_exp e2, f_exp e3)
    | Consq (r, e1, e2) -> Consq (r, f_exp e1, f_exp e2)
    | Pure (r, e) -> Pure (r, f_exp e)
    | Let (r, v, id,e1,e2) -> Let (r, v, id, f_exp e1,f_exp e2)
    | Fix (r, x, y, u1, u2, u3, u4, e) -> Fix (r, x, y, f_ty u1, f_ty u2, f_ty u3, f_ty u4, f_exp e)
    | Asc (r, e, t) -> Asc(r, f_exp e, f_ty t)

  let rec tv_exp: exp -> TV.t = function
    | Var _
    | Const _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | If (_,  e1, e2, e3) -> TV.big_union @@ List.map tv_exp [e1; e2; e3]
    | Fun (_, g, _, x1_t, e) -> TV.big_union @@ [ftv_ty x1_t; tv_exp e; ftv_ty g]
    | App (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | Let (_, _, _, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | Shift (_, _, k_t, e) -> TV.union (ftv_ty k_t) (tv_exp e)
    | Reset (_, e, u) -> TV.union (ftv_ty u) (tv_exp e)
    | Pure (_, e) -> tv_exp e
    | Consq (_, e1, e2) -> TV.union (tv_exp e1) (tv_exp e2)
    | Fix (_, _, _, u1, u2, u3, u4, e) -> TV.big_union @@ [ftv_ty u1; ftv_ty u2; ftv_ty u3; ftv_ty u4; tv_exp e]
    | Asc (_, e, t) -> TV.union (tv_exp e) (ftv_ty t)

  let rec ftv_exp: exp -> TV.t = function
    | Var _
    | Const _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | If (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | Fun (_, _, _, _, e) -> ftv_exp e
    | App (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | Let (_, _, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | Shift (_, _, _, e) -> ftv_exp e
    | Reset (_, e, _) -> ftv_exp e
    | Pure (_, e) -> ftv_exp e
    | Consq (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | Fix (_, _, _, _, _, _, _, e) -> ftv_exp e
    | Asc (_, e, _) -> ftv_exp e
end

module CSR = struct
  type tyarg = Ty of ty | TyNu

  type polarity = Pos | Neg

  (** Returns the negation of the given polarity. *)
  let neg = function Pos -> Neg | Neg -> Pos

  type exp =
    | Var of range * id * tyarg list
    | Const of range * const
    | BinOp of range * binop * exp * exp
    | Fun of range * ty * id * ty * exp
    | App of range * exp * exp
    | Shift of range * id * ty * exp
    | Reset of range * exp * ty
    | If of range * exp * exp * exp
    | Consq of range * exp * exp
    | Cast of range * exp * ty * ty * polarity
    | Pure of range * ty * exp
    | Let of range * id * tyvar list * exp * exp
    | Fix of range * id * id * ty * ty * ty * ty * exp

  type program =
    | Exp of exp
    | LetDecl of id * tyvar list * exp

  let range_of_exp = function
    | Var (r, _, _)
    | Const (r, _)
    | BinOp (r, _, _, _)
    | Fun (r, _, _, _, _)
    | App (r, _, _)
    | Shift (r, _, _, _)
    | Reset (r, _, _)
    | If (r, _, _, _)
    | Consq (r, _, _)
    | Cast (r, _, _, _, _)
    | Pure (r, _, _)
    | Let (r, _, _, _, _)
    | Fix (r, _, _, _, _, _, _, _) -> r

  let map f_ty f_exp = function
    | Var _ as e -> e
    | Const _ as e -> e
    | BinOp (r, op, e1, e2) -> BinOp (r, op, f_exp e1, f_exp e2)
    | Fun (r, g, x1, x1_t, e) -> Fun (r, f_ty g, x1, f_ty x1_t, f_exp e)
    | App (r, e1, e2) -> App (r, f_exp e1, f_exp e2)
    | Shift (r, k, k_t, e) -> Shift (r, k, f_ty k_t, f_exp e)
    | Reset (r, e, u) -> Reset (r, f_exp e, f_ty u)
    | If (r, e1, e2, e3) -> If (r, f_exp e1, f_exp e2, f_exp e3)
    | Consq (r, e1, e2) -> Consq (r, f_exp e1, f_exp e2)
    | Cast (r, e, u1, u2, p) -> Cast (r, f_exp e, f_ty u1, f_ty u2, p)
    | Pure (r, ty, e)  -> Pure (r, f_ty ty, f_exp e)
    | Let (r, id, xs, e1, e2) -> Let (r, id, xs, f_exp e1, f_exp e2)
    | Fix (r, x, y, u1, u2, u3, u4, e) -> Fix (r, x, y, f_ty u1, f_ty u2, f_ty u3, f_ty u4, f_exp e)

  let ftv_tyarg = function
    | Ty ty -> ftv_ty ty
    | TyNu -> TV.empty

  let rec ftv_exp: exp -> TV.t = function
    | Var (_, _,us) -> List.fold_right TV.union (List.map ftv_tyarg us) TV.empty
    | Const _ -> TV.empty
    | BinOp (_, _, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | If (_, e1, e2, e3) -> TV.big_union @@ List.map ftv_exp [e1; e2; e3]
    | Fun (_, _, _, _, e) -> ftv_exp e
    | App (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | Let (_, _, xs, f1, f2) -> TV.union (TV.diff (ftv_exp f1) (TV.of_list xs)) (ftv_exp f2)
    | Shift(_, _, _, e) -> ftv_exp e
    | Reset(_, e, _) -> ftv_exp e
    | Pure (_, _, e) -> ftv_exp e
    | Consq (_, e1, e2) -> TV.union (ftv_exp e1) (ftv_exp e2)
    | Cast (_, e, u1, u2, _) -> TV.union (ftv_exp e) @@ TV.union (ftv_ty u1) (ftv_ty u2)
    | Fix (_, _, _, _, _, _, _, e) -> ftv_exp e

  type tag = P of int | PP of int | I | B | U | Ar

  type value =
    | IntV of int
    | BoolV of bool
    | UnitV
    | FunV of ((tyvar list * ty list) -> value -> cont -> value)
    | Tagged of tag * value
  and cont = value -> value
end

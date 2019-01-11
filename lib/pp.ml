open Constraints
open Format
open Syntax

let pp_sep ppf () = fprintf ppf ", "

(* binop -> string *)
let pp_print_binop ppf op =
  pp_print_string ppf begin
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Equal -> "="
    | Gt -> ">"
    | Lt -> "<"
  end

let pp_print_basety ppf b =
  pp_print_string ppf begin
    match b with
    | TyBool -> "bool"
    | TyInt -> "int"
    | TyUnit -> "unit"
  end

let rec pp_print_type ppf = function
  | TyPureVar tp -> fprintf ppf "'X%d" tp
  | TyVar (x, {contents=None}) -> fprintf ppf "'x%d" x
  | TyVar (_, {contents=Some u}) -> pp_print_type ppf u
  | TyBase b -> pp_print_basety ppf b
  | TyFun (t1, t2, t3, t4) ->
    (* TODO: can be better *)
    let with_paren ppf t = match t with
      | TyFun _ -> fprintf ppf "(%a)" pp_print_type t
      | _ -> fprintf ppf "%a" pp_print_type t
    in
    fprintf ppf "%a/%a -> %a/%a"
      with_paren t1
      with_paren t2
      with_paren t3
      with_paren t4
  | TyDyn -> pp_print_string ppf "?"

let pp_print_var ppf (x, ys) =
  if List.length ys = 0 then
    fprintf ppf "%s" x
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_print_type ppf types ~pp_sep:pp_sep in
    fprintf ppf "%s[%a]"
      x
      pp_list ys

let pp_ty2 ppf u =
  let tyvars = ref [] in
  let pp_tyvar ppf (a, _) =
    let rec index_of_tyvar pos = function
      | [] -> tyvars := !tyvars @ [a]; pos
      | a' :: rest -> if a = a' then pos else index_of_tyvar (pos + 1) rest
    in
    let pp_tyvar_of_index ppf i =
      let j = i / 26 in
      let k = i mod 26 in
      let s = String.make 1 @@ char_of_int @@ (int_of_char 'a') + k in
      let t = if j = 0 then "" else string_of_int j in
      fprintf ppf "'%s%s" s t
    in
    pp_tyvar_of_index ppf @@ index_of_tyvar 0 !tyvars
  in
  let rec pp_ty ppf = function
    | TyDyn -> pp_print_string ppf "?"
    | TyVar (_, { contents = Some u }) -> pp_ty ppf u
    | TyVar x -> pp_tyvar ppf x
    | TyBase b -> pp_print_basety ppf b
    | TyFun (t1, t2, t3, t4) ->
      (* TODO: can be better *)
      let with_paren ppf t = match t with
        | TyFun _ -> fprintf ppf "(%a)" pp_ty t
        | _ -> fprintf ppf "%a" pp_ty t
      in
      fprintf ppf "%a/%a -> %a/%a"
        with_paren t1
        with_paren t2
        with_paren t3
        with_paren t4
    | TyPureVar tp -> fprintf ppf "'X%d" tp
  in pp_ty ppf u

let pp_let_tyabses ppf tyvars =
  if List.length tyvars = 0 then
    fprintf ppf ""
  else
    let pp_sep ppf () = fprintf ppf "," in
    let pp_list ppf types = pp_print_list pp_print_type ppf types ~pp_sep:pp_sep in
    fprintf ppf "fun %a -> " pp_list @@ List.map (fun x -> TyVar x) tyvars

let pp_print_const ppf = function
  | ConstBool b -> pp_print_bool ppf b
  | ConstInt i -> pp_print_int ppf i
  | ConstUnit -> pp_print_string ppf "()"

let pp_print_type_annot ppf (x, t) =
  fprintf ppf "(%s: %a)" x pp_print_type t

let pp_print_answer_type_annot ppf t =
  fprintf ppf "^%a" pp_print_type t

let pp_print_constr ppf = function
  | CEqual (u1, u2) -> fprintf ppf "%a=%a" pp_print_type u1 pp_print_type u2
  | CConsistent (u1, u2) -> fprintf ppf "%a~%a" pp_print_type u1 pp_print_type u2

let pp_print_constraints ppf c =
  pp_print_list pp_print_constr ppf (Constraints.to_list c) ~pp_sep:pp_sep

let pp_print_subst ppf ((x, _), t) =
  fprintf ppf "x%a=%a" pp_print_int x pp_print_type t

let pp_print_substitutions ppf s =
  pp_print_list pp_print_subst ppf s ~pp_sep:pp_sep

module GSR = struct
  open GSR

  let rec pp_print_exp ppf = function
    | Var (_, x,ys) -> pp_print_var ppf (x, !ys)
    | Const (_, c) -> pp_print_const ppf c
    | BinOp (_, op, e1, e2) ->
      fprintf ppf "%a %a %a"
        pp_print_exp e1
        pp_print_binop op
        pp_print_exp e2
    | Fun (_, g, x, x_t, e) ->
      fprintf ppf "fun%a %a -> %a"
        pp_print_answer_type_annot g
        pp_print_type_annot (x, x_t)
        pp_print_exp e
    | App (_, e1, e2) ->
      fprintf ppf "((%a) (%a))"
        pp_print_exp e1
        pp_print_exp e2
    | Shift (_, k, k_t, e) ->
      fprintf ppf "shift %a -> (%a)"
        pp_print_type_annot (k, k_t)
        pp_print_exp e
    | Reset (_, e, u) ->
      fprintf ppf "reset%a (%a)"
        pp_print_answer_type_annot u
        pp_print_exp e
    | If (_, e1, e2, e3) ->
      fprintf ppf "if %a then %a else %a"
        pp_print_exp e1
        pp_print_exp e2
        pp_print_exp e3
    | Consq (_, e1, e2) ->
      fprintf ppf "%a; %a"
        pp_print_exp e1
        pp_print_exp e2
    | Pure (_, e) ->
      fprintf ppf "pure( %a )"
        pp_print_exp e
    | Let (_, _, id, e1, e2) ->
      fprintf ppf "let %s = %a in %a"
        id
        pp_print_exp e1
        pp_print_exp e2
    | Fix (_, x, y, u1, u2, u3, u4, e) ->
      fprintf ppf "fix %s (%s: %a) %a :%a %a = %a"
        x
        y
        pp_print_type u1
        pp_print_answer_type_annot u2
        pp_print_type u3
        pp_print_answer_type_annot u4
        pp_print_exp e
    | Asc (_, e, ty) ->
      fprintf ppf "(%a : %a)"
        pp_print_exp e
        pp_print_type ty
    let pp_program ppf = function
      | Exp e -> pp_print_exp ppf e
      | LetDecl (x, e) ->
        fprintf ppf "let %s = %a"
          x
          pp_print_exp e
      | _ -> raise @@ Failure ""
end

module CSR = struct
  open CSR
  let pp_tyarg ppf = function
    | Ty u -> pp_print_type ppf u
    | TyNu -> pp_print_string ppf "ν"

  let pp_print_var ppf (x, ys) =
    if List.length ys = 0 then
      fprintf ppf "%s" x
    else
      let pp_sep ppf () = fprintf ppf "," in
      let pp_list ppf types = pp_print_list pp_tyarg ppf types ~pp_sep:pp_sep in
      fprintf ppf "%s[%a]"
        x
        pp_list ys

  (* TODO print correctly *)
  let rec pp_print_exp ppf = function
    | Var (_, x, ys) -> pp_print_var ppf (x,ys)
    | Const (_, c) -> pp_print_const ppf c
    | BinOp (_, op, e1, e2) ->
      fprintf ppf "%a %a %a"
        pp_print_exp e1
        pp_print_binop op
        pp_print_exp e2
    | Fun (_, g, x, x_t, e) ->
      fprintf ppf "fun%a %a -> %a"
        pp_print_answer_type_annot g
        pp_print_type_annot (x, x_t)
        pp_print_exp e
    | App (_, e1, e2) ->
      fprintf ppf "((%a) (%a))"
        pp_print_exp e1
        pp_print_exp e2
    | Shift (_, k, k_t, e) ->
      fprintf ppf "shift %a -> (%a)"
        pp_print_type_annot (k, k_t)
        pp_print_exp e
    | Reset (_, e, u) ->
      fprintf ppf "reset%a (%a)"
        pp_print_answer_type_annot u
        pp_print_exp e
    | If (_, e1, e2, e3) ->
      fprintf ppf "if %a then %a else %a"
        pp_print_exp e1
        pp_print_exp e2
        pp_print_exp e3
    | Consq (_, e1, e2) ->
      fprintf ppf "%a; %a"
        pp_print_exp e1
        pp_print_exp e2
    | Cast (_, e, u1, u2, _) ->
      fprintf ppf "(%a : %a => %a)"
        pp_print_exp e
        pp_print_type u1
        pp_print_type u2
    | Pure (_, _, e) ->
      fprintf ppf "pure( %a )"
        pp_print_exp e
    | Let (_, id, xs, e1, e2) ->
      fprintf ppf "let %s = %a%a in %a"
        id
        pp_let_tyabses xs
        pp_print_exp e1
        pp_print_exp e2
    | Fix (_, x, y, u1, u2, u3, u4, e) ->
      fprintf ppf "fix %s (%s: %a) %a :%a %a = %a"
        x
        y
        pp_print_type u1
        pp_print_answer_type_annot u2
        pp_print_type u3
        pp_print_answer_type_annot u4
        pp_print_exp e
  let pp_print_tag ppf = function
    | P p -> fprintf ppf "'x%d" p
    | PP p -> fprintf ppf "'X%d" p
    | B -> pp_print_string ppf "bool"
    | I -> pp_print_string ppf "int"
    | U -> pp_print_string ppf "unit"
    | Ar -> pp_print_string ppf "?/? -> ?/?"

  let rec pp_print_value ppf = function
    | IntV i -> pp_print_int ppf i
    | BoolV b -> pp_print_bool ppf b
    | UnitV -> pp_print_string ppf "()"
    | FunV _ -> pp_print_string ppf "<fun>"
    | Tagged (t, v) -> fprintf ppf "%a : %a => ?" pp_print_value v pp_print_tag t

  let pp_program ppf = function
    | Exp e -> pp_print_exp ppf e
    | LetDecl (x, xs, f) ->
      fprintf ppf "let %s = %a%a"
        x
        pp_let_tyabses xs
        pp_print_exp f
end

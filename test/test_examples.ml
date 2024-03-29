open Format

open OUnit2

open Lambda_dti
open Syntax

let test_cases = [
  (* Constants *)
  ["1", "int", "1"];
  ["true", "bool", "true"];
  ["()", "unit", "()"];
  (* Unary operators *)
  ["-1", "int", "-1"];
  ["--2", "int", "2"];
  ["let x = 1 in x-1", "int", "0"];
  (* Binary operators *)
  ["1 + 2 + 3", "int", "6"];
  ["3 * 2 + 3", "int", "9"];
  ["3 * (2 + 3)", "int", "15"];
  ["3 = 3", "bool", "true"];
  (* Type ascription *)
  ["(2 : ?)", "int", "2"];
  ["((2: ?): int)", "int", "2"];
  (* if-then-else *)
  ["if 2 < 3 then 4 else 5", "int", "4"];
  ["if 3 < 3 then 4 else 5", "int", "5"];
  (* let *)
  ["let x = 3 + 4 in x", "int", "7"];
  ["let x = 3 + 4 in let y = 1 in let x = 2 in y + x", "int", "3"];
  ["let x = 10 in let x = 100 in x * x", "int", "10000"];
  (* abstraction *)
  ["fun x -> x + 1", "int/'a -> int/'a", "<fun>"];
  ["fun (x:?) -> x + 1", "'a/'b -> int/'b", "<fun>"];
  ["fun x -> x", "'a/'b -> 'a/'b", "<fun>"];
  ["fun (x: unit) -> ()", "unit/'a -> unit/'a", "<fun>"];
  ["fun (x: int/'a -> bool/'a) -> ()", "(int/'a -> bool/'a)/'b -> unit/'b", "<fun>"];
  ["fun (x: int/'a -> (bool/'b -> int/'b)/'a) -> ()", "(int/'a -> (bool/'b -> int/'b)/'a)/'c -> unit/'c", "<fun>"];
  ["fun (x:'a) (y:'b) -> x y", "('a/'b -> 'c/'d)/'e -> ('a/'b -> 'c/'d)/'e", "<fun>"];
  (* application *)
  ["(fun x -> x + 1) 3", "int", "4"];
  ["(fun (x:?) -> x + 1) 3", "int", "4"];
  ["(fun (x:?) -> x + 1) false", "int", "blame+"];
  ["(fun x y -> x + y) 3 4", "int", "7"];
  ["(fun (x:?) -> x 2) (fun y -> y)", "int", "2"];
  ["(fun (x:?) -> x 2) (fun (y: int) -> y)", "int", "2"];
  ["(fun (x:?) -> x 2) (fun y -> true)", "bool", "true"];
  ["(fun (x:?) -> x) (fun y -> true)", "'a/'b -> 'c/'d", "<fun>"];
  ["(fun x -> 1 + ((fun (y:?) -> y) x)) 2", "int", "3"];
  (* sequence *)
  ["(); 1 + 2", "int", "3"];
  ["(():?); 1 + 2", "int", "3"];
  (* dynamic type inference *)
  ["(fun (f:?) -> f 2) (fun y -> y)", "int", "2"];
  ["(fun (f:?) -> f 2) ((fun x -> x) ((fun (y:?) -> y) (fun z -> z + 1)))", "int", "3"];
  ["(fun (x:?) -> (fun y -> y) x) (fun (z:?) -> z + 1) 3", "int", "4"];
  ["(fun x -> x) ((fun (y:?) -> y) (fun x -> x + 1)) 1", "int", "2"];
  ["(fun (f:?) -> f (); f true) (fun (x:?) -> x)", "bool", "true"];
  ["(fun (f:?) -> f (); f true) (fun x -> x)", "'a", "blame-"];
  ["(fun (f:?) -> let d = f 2 in f true) (fun (x:?) -> x)", "bool", "true"];
  ["(fun (f:?) -> let d = f 2 in f true) (fun x -> x)", "'a", "blame-"];
  (* let-poly *)
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k", "'a/'b -> 'a/'b", "<fun>"];
  ["let s = fun x y z -> x z (y z) in let k = fun x y -> x in s k k 1", "int", "1"];
  ["let s = fun (x:?) (y:?) (z:?) -> x z (y z) in let k = fun x y -> x in s k k 1", "int", "1"];
  ["let succ x = x + 1 in let twice f x = f (f x) in twice succ 1", "int", "3"];
  ["let id x = x in let did (x:?) = x in let succ x = x + 1 in (fun (x:?) -> x 1) (id (did succ))", "int", "2"];
  ["let id x = x in id (); id true", "bool", "true"];
  ["let g = fun x -> ((fun y -> y) : ?/?->?/?) x in g (); g 3", "int", "3"];
  ["let f = fun x -> 1 + ((fun (y:?) -> y) x) in 2", "int", "2"];
  (* toplevel let-poly *)
  [
    (* "let f = (fun x -> x) (fun y -> y)", "'a/'b -> 'a/'b", "<fun>";
    "f", "'a/'b -> 'a/'b", "<fun>";
    "f 3", "int", "3";
    "f", "int -> int", "<fun>"; *)
  ];
  (* [
    "let twice f x = f (f x)", "('a -> 'a) -> 'a -> 'a", "<fun>";
    "twice succ 3", "int", "5";
    "twice not true", "bool", "true";
  ]; *)
  (* [
    "let dtwice (f:?) (x:?) = f (f x)", "? -> ? -> ?", "<fun>";
    "dtwice succ 3", "?", "5: int => ?";
    "dtwice not true", "?", "true: bool => ?";
  ];
  [
    "let f x: 'a = x", "'a -> 'a", "<fun>";
    "f 3", "int", "3";
    "f true", "bool", "true";
    "f", "'a -> 'a", "<fun>";
  ];
  [
    "let did (x:?) = x", "? -> ?", "<fun>";
    "let f x: 'a = did x", "'a -> 'b", "<fun>";
    "f 3", "int", "3";
    "f true", "bool", "true";
    "f", "'a -> 'b", "<fun>";
  ];
  [
    "let f: 'a -> 'a = fun x -> x", "'a -> 'a", "<fun>";
    "f 3", "int", "3";
    "f true", "bool", "true";
    "f", "'a -> 'a", "<fun>";
    "let g = f", "'a -> 'a", "<fun>";
    "g 3", "int", "3";
    "g true", "bool", "true";
    "g", "'a -> 'a", "<fun>";
    "let g: 'b = f", "'a -> 'a", "<fun>";
    "g 3", "int", "3";
    "g true", "bool", "true";
    "g", "'a -> 'a", "<fun>";
  ];
  [
    "let f: 'a = fun x -> x", "'a -> 'a", "<fun>";
    "f 3", "int", "3";
    "f true", "bool", "true";
    "f", "'a -> 'a", "<fun>";
    "let g = f", "'a -> 'a", "<fun>";
    "g 3", "int", "3";
    "g true", "bool", "true";
    "g", "'a -> 'a", "<fun>";
  ];
  [
    "let f = ((fun x -> x: 'a -> 'a): 'a -> 'a)", "'a -> 'a", "<fun>";
    "f 3", "int", "3";
    "f true", "bool", "true";
    "f", "'a -> 'a", "<fun>";
    "let g = f", "'a -> 'a", "<fun>";
    "g 3", "int", "3";
    "g true", "bool", "true";
    "g", "'a -> 'a", "<fun>";
  ];
  [
    "let f: 'a -> 'a -> ? = fun x y -> 0", "'a -> 'a -> ?", "<fun>";
    "let g1 x = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>";
    "fun x y -> f (g1 x) (g1 y)", "'a -> 'b -> ?", "<fun>";
    "let g2 (x: 'a) = ((fun y -> y) : ? -> ?) x", "'a -> ?", "<fun>";
    "fun x y -> f (g2 x) (g2 y)", "'a -> 'b -> ?", "<fun>";
  ];
  [
    "let f = ((((fun x -> x): 'a ->'a): ?): 'a->'a)", "'a -> 'a", "<fun>";
    "f 3", "int", "3";
    "f", "int -> int", "<fun>";
  ];
  [
    "let f (x: int) (y: bool) = 0", "int -> bool -> int", "<fun>";
    "let dyn x = ((fun (y: 'b) -> y): ? -> ?) x", "'a -> ?", "<fun>";
    "f (dyn 2) (dyn true)", "int", "0";
  ]; *)
  (* let-poly & recursion *)
  ["let rec fact n = if n < 1 then 1 else n * fact (n - 1) in fact 5", "int", "120"];
  ["let rec fact (n:?) = if n < 1 then 1 else n * fact (n - 1) in fact 5", "int", "120"];
  ["let rec f (x:?) = x in f 2", "int", "2"];
  ["let rec f n = fun x -> if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true"];
  ["let rec f (n:?) = fun (x:?) -> if n < 0 then x else f (n - 1) x in f 100 true", "bool", "true"];
  (* ["let rec f n (x:?) = if n <= 0 then x else f 0 x in f 0 true", "bool", "true"]; *)
  (* ["let rec f n = fun (x:?) -> if n <= 0 then x else f 0 x in f 10 true", "bool", "true"]; *)
  ["let rec id x = x in id (); id true", "bool", "true"];
  (* k of shift is polymorhic *)
  ["shift k -> if (reset k true) then (if k true then 1 else 2) else 3", "int", "1"];
  (* let answer type polymorphism *)
  ["let f = fun x -> x in if (reset f true) then (if f true then 1 else 2) else 3", "int", "1"];
  ["let f = fun^? (x:?) -> x in if (reset f true) then (if f true then 1 else 2) else 3", "int", "1"];
  (* pure(e) *)
  ["pure( 1 )", "int", "1"];
  ["pure( fun x -> x )", "'a/'b -> 'a/'b", "<fun>"];
  ["pure( reset( 1 ) )", "int", "1"];
  ["pure( reset( shift k -> 1 ) )", "int", "1"];
  ["pure( 1+1 )", "int", "2"];
  ["pure( shift (k:?) -> k 1 )", "int", "1"];
  ["pure( shift (k:?) -> k 1 + k 2 )", "int", "blame+"];
  ["pure( shift (k:?) -> 1 )", "'a", "blame+"];
  ["pure( (fun^? x -> x) 1 )", "int", "1"];
  ["pure(shift (k:?) -> k (shift l -> l 1))", "int", "1"];
  ["pure(shift (k:?) -> k (shift l -> k 1))", "int", "1"];
  ["pure(shift (k:?) -> k (k 1))", "int", "blame+"];
  ["pure(shift (k:?) -> k (shift l -> l 1 + 2))", "int", "blame+"]
]


let id x = x

let run env tyenv program =
  let parse str = Parser.toplevel Lexer.main @@ Lexing.from_string str in
  let e = parse @@ program ^ ";;" in
  let u_b = Typing.GSR.fresh_tyvar () in
  let e = Typing.GSR.let_macro e in
  let e = Typing.GSR.set_reset e u_b in
  let u, u_a, c = Typing.GSR.generate_constraints_program tyenv e u_b in
  let s = Typing.GSR.unify c in
  let tyenv, e, u, u_a, u_b = Typing.GSR.subst_program tyenv e u u_a u_b s in
  let tyenv, f, u', u_a' = Typing.GSR.translate_program tyenv e u_b in
  assert (u = u');
  assert (u_a = u_a');
  let u'', u_a'' = Typing.CSR.type_of_program tyenv f u_b in
  assert (u' = u'');
  assert (u_a' = u_a'');
  try
    let env, _, v = Eval.eval_program false f env (fun x -> x) in
    env, tyenv, asprintf "%a" Pp.pp_ty2 u, asprintf "%a" Pp.CSR.pp_print_value v
  with
  | Eval.Blame (_, CSR.Pos) -> env, tyenv, asprintf "%a" Pp.pp_ty2 u, "blame+"
  | Eval.Blame (_, CSR.Neg) -> env, tyenv, asprintf "%a" Pp.pp_ty2 u, "blame-"

let test_examples =
  let test i cases =
    (string_of_int i) >:: fun ctxt ->
      ignore @@ List.fold_left
        (fun (env, tyenv) (program, expected_ty, expected_value) ->
           let env, tyenv, actual_ty, actual_value = run env tyenv program in
           assert_equal ~ctxt:ctxt ~printer:id expected_ty actual_ty;
           assert_equal ~ctxt:ctxt ~printer:id expected_value actual_value;
           env, tyenv
        )
        Stdlib.pervasives
        cases
  in
  List.mapi test test_cases

let suite = [
  "test_examples">::: test_examples;
]

open Syntax

exception Untagged

let pervasive = []

let env =
  List.fold_right
    (fun (x, _, v) env -> Environment.add x v env)
    pervasive Environment.empty

let tyenv =
  List.fold_right
    (fun (x, u, _) tyenv -> Environment.add x u tyenv)
    pervasive Environment.empty

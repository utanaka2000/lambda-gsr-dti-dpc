open Syntax
open Syntax.CSR
open Utils.Error

exception Eval_fatal_error of string
exception Blame of range * polarity

val eval : bool -> exp -> (tyvar list * value) Environment.t -> cont -> value
val eval_program : bool -> program -> (tyvar list * value) Environment.t -> cont -> ((tyvar list * value) Environment.t * value)

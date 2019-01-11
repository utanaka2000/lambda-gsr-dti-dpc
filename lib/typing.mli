open Syntax
open Constraints

(** Type error in the given program. *)
exception Type_fatal_error of string
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

(** Returns a fresh type variable. *)


(* val is_equal : ty -> ty -> bool *)

(* [X:->u] *)
type substitution = tyvar * ty
(* if S = [X1:->X2], [X2:->u1], then S(X1)=u1 *)
type substitutions = substitution list
val subst_type2 : substitutions -> ty -> ty

val tyarg_to_ty : Syntax.CSR.tyarg -> ty

val fresh_var : unit -> string

val subst_type_substitutions : ty -> substitutions -> ty
val subst_exp_substitutions : Syntax.GSR.exp -> substitutions -> Syntax.GSR.exp

module GSR : sig
  open Syntax.GSR

  val fresh_tyvar : unit -> ty
  val let_macro : program -> program
  val fresh_tyfun : ty
  val generate_constraints : tysc Environment.t -> exp -> ty -> (ty * ty * IConstraints.t )
(* val type_of_exp : tysc Environment.t -> exp -> ty *)
  val unify : IConstraints.t -> substitutions
  val translate : tysc Environment.t -> exp -> ty -> (CSR.exp * ty * ty)

  val reset_set : program -> program
  val generate_constraints_program : tysc Environment.t -> program -> ty -> (ty * ty * IConstraints.t)
  val subst_program : tysc Environment.t -> program -> ty -> ty -> ty -> substitutions -> ( tysc Environment.t * program * ty * ty * ty)
  val translate_program : tysc Environment.t -> program -> ty -> (tysc Environment.t * CSR.program * ty * ty)
end

module CSR : sig
  open Syntax.CSR

  val type_of_exp : tysc Environment.t -> exp -> ty -> (ty * ty)
  val type_of_program : tysc Environment.t -> program -> ty -> (ty * ty)
end

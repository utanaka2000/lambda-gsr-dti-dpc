open Format
open Lambda_dti

type directives = {
  debug: bool;
}

let pp_print_flag ppf f =
  pp_print_string ppf begin
    match f with
    | true -> "enabled"
    | false -> "disabled"
  end

let rec read_eval_print lexbuf env tyenv dirs =
  (* Used in all modes *)
  let print f = fprintf std_formatter f in
  (* Used in debug mode *)
  let print_debug f =
    if dirs.debug then
      print f
    else
      let empty = make_formatter (fun _ _ _ -> ()) (fun _ -> ()) in
      fprintf empty f
  in
  let dirs = ref dirs in
  print "# @?";
  flush stderr;
  flush stdout;
  ignore @@ flush_str_formatter ();
  begin try
      let e = Parser.toplevel Lexer.main lexbuf in
      begin match e with
        | Syntax.GSR.Exp _
        | Syntax.GSR.LetDecl _ as e ->
          (* Inference *)
          let u_b = Typing.GSR.fresh_tyvar () in
          let e = Typing.GSR.reset_set e in
          print_debug "***** Typing *****\n e: %a\n Uβ: %a\n"
            Pp.GSR.pp_program e
            Pp.pp_print_type u_b;
          (* Constraints generation *)
          let u, u_a, c = Typing.GSR.generate_constraints_program tyenv e u_b in
          print_debug "Constraints: %a\n" Pp.pp_print_constraints c;
          let s = Typing.GSR.unify c in
          print_debug "Substitutions: %a\n" Pp.pp_print_substitutions s;
          let tyenv, e, u, u_a, u_b = Typing.GSR.subst_program tyenv e u u_a u_b s in
          print_debug "After Substitution:\n";
          print_debug " e: %a\n" Pp.GSR.pp_program e;
          print_debug " U: %a\n" Pp.pp_print_type u;
          print_debug " Uα: %a\n" Pp.pp_print_type u_a;
          print_debug " Uβ: %a\n" Pp.pp_print_type u_b;
          if u_a <> u_b then begin
            print "Warning: This expression is not pure.\n";
            print "Answer types are %a and %a.\n"
              Pp.pp_print_type u_a
              Pp.pp_print_type u_b
          end;
          let tyenv, f, u', u_a' = Typing.GSR.translate_program tyenv e u_b in
          (* Translation must not change types *)
          assert (u = u');
          assert (u_a = u_a');
          let u'', u_a'' = Typing.CSR.type_of_program tyenv f u_b in
          assert (u' = u'');
          assert (u_a' = u_a'');
          print_debug "***** Cast-insertion *****\n f: %a\n U: %a\n Uα: %a\n Uβ: %a\n"
            Pp.CSR.pp_program f
            Pp.pp_print_type u'
            Pp.pp_print_type u_a'
            Pp.pp_print_type u_b;
          (* Evaluation *)
          print_debug "***** Eval *****\n";
          let env, v = Eval.eval_program !dirs.debug f env (fun x -> x) in
          print "- : %a = %a\n"
            Pp.pp_ty2 u'  (* tyvar is printed like 'a *)
            (* Pp.pp_print_type u' *)
            Pp.CSR.pp_print_value v;
          read_eval_print lexbuf env tyenv !dirs
        | Syntax.GSR.Directive d ->
          begin match d with
            | Syntax.GSR.BoolDir ("debug", b) ->
              print "debug mode %a\n" pp_print_flag b;
              dirs := { debug = b }
            | _ ->
              print "unsupported directive\n"
          end
      end
    with
    | Failure message ->
      print "Failure: %s\n" message;
      Lexing.flush_input lexbuf
    (* Soft errors *)
    | Parser.Error -> (* Menhir *)
      let token = Lexing.lexeme lexbuf in
      print "Parser.Error: unexpected token %s\n" token;
      Lexing.flush_input lexbuf
    | Typing.Type_error message ->
      print "Type_error: %s\n" message
    | Typing.Type_error1 (message, u1) ->
      print ("Type_error1: " ^^ message ^^ "\n")
        Pp.pp_print_type u1;
    | Typing.Type_error2 (message, u1, u2) ->
      print ("Type_error2: " ^^ message ^^ "\n")
        Pp.pp_print_type u1
        Pp.pp_print_type u2
    | Typing.Unification_error (message, c) ->
      print ("Unification_error: " ^^ message ^^ "\n")
        Pp.pp_print_constr c
    | Eval.Blame (range, polarity) ->
      begin match polarity with
      | Pos -> print "Blame on the expression side:\n%a\n" Utils.Error.pp_range range
      | Neg -> print "Blame on the environment side:\n%a\n" Utils.Error.pp_range range
      end
    (* Fatal errors *)
    | Typing.Type_fatal_error message ->
      print "FATAL: Type_fatal_error: %s\n" message
    | Eval.Eval_fatal_error message ->
      print "FATAL: Eval_fatal_error: %s\n" message
  end;
  read_eval_print lexbuf env tyenv !dirs

let () =
  let lexbuf = Lexing.from_channel stdin in
  let env = Stdlib.env in
  let tyenv = Stdlib.tyenv in
  read_eval_print lexbuf env tyenv { debug = false }

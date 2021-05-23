open Base
open Lang.Typ
open Lang.Term
open Lang.TermUtils
open Lang.Unfold
open Utils
open Result
open Result.Let_syntax
module S = Sexplib.Sexp

let verbose = ref true

(* Parsing. Expects some handling of associative operations. *)

exception SexpParseError of string * Sexp.t

let raise_sexp_e info s = raise (SexpParseError (info, s))

let new_var (vname : string) (vtype : typ) =
  { vname; vid = Lang.Alpha.get_new_id (); vtype; vattrs = [] }

let define_var (vars : VarSet.t) ((dfname, dftype) : Sexp.t * Sexp.t) =
  let vname = Sexp.to_string dfname in
  match VarSet.find_by_name vars vname with
  | Some v -> (vars, v)
  | None ->
      let vtype = typ_of_sexp dftype in
      let var = new_var vname vtype in
      (var $++ vars, var)

let rec expr_of_sexp (vars : VarSet.t) (se : Sexp.t) : (term, Sexp.t) Result.t =
  (* Return a triple where the first element is singleton with the new variable if a new
     variable has been created, or empty if no new variable has been created.
     In the second case, returning empty allows the caller to handle the variable
     update, especially in the case of multiple let-bindings.
  *)
  let make_binding vars x te1 =
    match type_of te1 with
    | Ok t1 -> (
        match VarSet.find_by_name vars x with
        | Some vx -> Ok (VarSet.empty, vx, te1)
        | None ->
            let vx = new_var x t1 in
            Ok (VarSet.singleton vx, vx, te1) )
    | Error (s, t, e) ->
        Error Sexp.(List [ Atom "[type error]"; Atom s; sexp_of_typ t; sexp_of_expr e ])
  in
  let parse_binop se =
    match se with
    | Sexp.Atom opname -> (
        match opname with
        | "+" -> Some Plus
        | "-" -> Some Minus
        | "*" -> Some Times
        | "/" -> Some Div
        | "max" -> Some Max
        | "min" -> Some Min
        | "mod" -> Some Mod
        | "and" -> Some And
        | "&&" -> Some And
        | "or" -> Some Or
        | "xor" -> Some Xor
        | "cons" -> Some Cons
        | "append" -> Some Concat
        | ">" -> Some Gt
        | ">=" -> Some Ge
        | "<" -> Some Lt
        | "<=" -> Some Le
        | "=" -> Some Eq
        | _ -> None )
    | _ -> raise (SexpParseError ("expected atom for binop", se))
  in
  let parse_unop se =
    match se with
    | Sexp.Atom opname -> ( match opname with "not" -> Some Not | "-" -> Some Neg | _ -> None )
    | _ -> None
  in
  let parse_atom vname =
    match parse_binop (Sexp.Atom vname) with
    | Some op -> (
        match Option.(Binop.get_ac op >>| e_v) with
        | Some e -> Ok (mk_term e)
        | None -> Error (Sexp.Atom vname) )
    | None -> (
        match vname with
        | "true" -> Ok mk_true
        | "false" -> Ok mk_false
        | _ -> (
            match Caml.int_of_string_opt vname with
            | Some i -> Ok (mk_int i)
            | _ -> (
                match VarSet.find_by_name vars vname with
                | Some x -> Ok (mk_vt x)
                | None -> Error (Sexp.List [ Sexp.Atom "Unexpected atom"; Sexp.Atom vname ]) ) ) )
  in
  match se with
  | Atom s -> parse_atom s
  | List sel -> (
      match sel with
      | [] -> Ok mk_empty_list
      | [ _ ] -> failwith "Bad application"
      | f :: tl -> (
          match (parse_unop f, parse_binop f) with
          (* Unary operator *)
          | Some op, _ when List.length tl = 1 -> (
              match tl with
              | [ e ] -> Result.(expr_of_sexp vars e >>| fun x -> mk_un op x)
              | _ -> raise_sexp_e "Expected one operand for unary op" se )
          (* Binary operator. *)
          | _, Some op -> (
              match tl with
              | [ e1; e2 ] ->
                  Result.(
                    expr_of_sexp vars e1 >>= fun x ->
                    expr_of_sexp vars e2 >>| fun y -> mk_bin x op y)
              | _ when List.length tl > 2 && Binop.is_ac op -> (
                  (* Under is_ac condition get_ac should always succeed. *)
                  let f = Option.(value_exn (Binop.get_ac op >>| e_v)) in
                  match Result.combine_errors (List.map ~f:(expr_of_sexp vars) tl) with
                  | Ok args -> Ok (mk_app (mk_term f) args)
                  | Error errs -> Error (Sexp.List errs) )
              | _ ->
                  Error
                    Sexp.(List [ Atom "Expected two (or more if ac) operands for binary op"; se ]) )
          (* Not an operator, match special name. *)
          | _, _ -> (
              match f with
              | Sexp.Atom "foldl" when List.length tl = 3 ->
                  let e_f, e_init, e_l =
                    match tl with [ a; b; c ] -> (a, b, c) | _ -> failwith "Unreachable."
                  in
                  Result.(
                    expr_of_sexp vars e_f >>= fun x ->
                    expr_of_sexp vars e_init >>= fun y ->
                    expr_of_sexp vars e_l >>| fun z -> mk_term (EFoldL (x, y, z)))
              | Sexp.Atom "foldr" when List.length tl = 3 ->
                  let e_f, e_init, e_l =
                    match tl with [ a; b; c ] -> (a, b, c) | _ -> failwith "Unreachable."
                  in
                  Result.(
                    expr_of_sexp vars e_f >>= fun x ->
                    expr_of_sexp vars e_init >>= fun y ->
                    expr_of_sexp vars e_l >>| fun z -> mk_term (EFoldL (x, y, z)))
              | Sexp.Atom "ite" when List.length tl = 3 ->
                  let e_cond, e_t, e_f =
                    match tl with [ a; b; c ] -> (a, b, c) | _ -> failwith "Unreachable."
                  in
                  Result.(
                    expr_of_sexp vars e_cond >>= fun x ->
                    expr_of_sexp vars e_t >>= fun y ->
                    expr_of_sexp vars e_f >>| fun z -> mk_ite x y z)
              | Sexp.Atom "list" -> (
                  match Result.combine_errors (List.map ~f:(expr_of_sexp vars) tl) with
                  | Ok l -> Ok (mk_term (EList l))
                  | Error errs -> Error (Sexp.List errs) )
              | Sexp.Atom "$" -> (
                  match Result.combine_errors (List.map ~f:(expr_of_sexp vars) tl) with
                  | Ok l -> Ok (mk_term (ETuple l))
                  | Error errs -> Error (Sexp.List errs) )
              | Sexp.Atom "let" -> (
                  match tl with
                  (* A single let-binding *)
                  | Sexp.[ List [ List [ Atom x; se1 ] ]; se2 ]
                  | Sexp.[ List [ Sexp.Atom x; se1 ]; se2 ] ->
                      Result.(
                        expr_of_sexp vars se1 >>= make_binding vars x >>= fun (newv, vx, e1) ->
                        expr_of_sexp (newv $|| vars) se2 >>| fun e2 ->
                        mk_term (ELet (Var vx, e1, e2)))
                  (* Parallel bindings *)
                  | Sexp.[ List bindings; se2 ] -> (
                      let bindings =
                        let parse_binding sexp =
                          match sexp with
                          | Sexp.(List [ Atom x; expr_sexp ]) ->
                              Result.(expr_of_sexp vars expr_sexp >>= make_binding vars x)
                          | _ ->
                              Error Sexp.(List [ Atom "Expected a binding, could not parse"; sexp ])
                        in
                        List.map ~f:parse_binding bindings
                      in
                      match Result.combine_errors bindings with
                      | Ok ((x, vx0, e0) :: tl) ->
                          let vars' =
                            List.fold_left ((x, vx0, e0) :: tl) ~init:vars
                              ~f:(fun vs (newv, _, _) -> newv $|| vs)
                          in
                          Result.(
                            expr_of_sexp vars' se2 >>= fun e2 ->
                            Ok
                              (List.fold_left tl
                                 ~init:(mk_term (ELet (Var vx0, e0, e2)))
                                 ~f:(fun expr (_, vxi, ei) -> mk_term (ELet (Var vxi, ei, expr)))))
                      | Ok [] -> expr_of_sexp vars se2
                      | Error errs -> Error (Sexp.List errs) )
                  (* Smt solver responses contain multiplde let bindings *)
                  | _ -> Error Sexp.(List [ Atom "Bad syntax for let-expression."; se ]) )
              | Sexp.Atom "mem" -> (
                  match tl with
                  | [ expr_sexp; Atom i_str ] ->
                      Result.(
                        expr_of_sexp vars expr_sexp >>| fun x ->
                        mk_term (EMem (x, Int.of_string i_str)))
                  | _ -> Error Sexp.(List [ Atom "Bad syntax for tuple fieldber."; se ]) )
              | Sexp.Atom "lambda" -> (
                  match tl with
                  | [ Sexp.List vlt; sexp2 ] ->
                      let vars, varsl =
                        List.fold_left vlt
                          ~f:(fun (vars, varsl) vdecl ->
                            match vdecl with
                            | Sexp.(List [ Atom x; typ_sexp ]) ->
                                let vars, v = define_var vars (Atom x, typ_sexp) in
                                (vars, varsl @ [ v ])
                            | _ -> (vars, varsl)
                            (* Skip if error. TODO: error type? *))
                          ~init:(vars, [])
                      in
                      Result.(expr_of_sexp vars sexp2 >>| fun x -> mk_lambda varsl x)
                  | _ -> Error Sexp.(List [ Atom "Bad lambda form"; se ]) )
              | _ ->
                  let from_f ef =
                    match Result.combine_errors (List.map ~f:(expr_of_sexp vars) tl) with
                    | Ok l -> Ok (mk_app ef l)
                    | Error errs -> Error (Sexp.List errs)
                  in
                  Result.(expr_of_sexp vars f >>= from_f) ) ) )

(* Some external commands to be evaluated outside of this module. *)
type external_command =
  | CNormalize of bool * term list * term
  | CCollect of bool * term list * term
  | CAnnotateUnfoldings of term list * term * term
  | CDiscover of string * term * term
  | CPrint of string
  | CCEval of env * term

type file = {
  globals : term Map.M(Int).t;
  definitions : VarSet.t;
  expressions : term list;
  commands : external_command list;
}

let empty_file =
  { globals = Map.empty (module Int); definitions = VarSet.empty; expressions = []; commands = [] }

let file_add_command f c = { f with commands = f.commands @ [ c ] }

let env_of_file f = { evars = f.definitions; evals = f.globals }

let discover_command fname f_expr s0_expr file errs =
  match (expr_of_sexp file.definitions f_expr, expr_of_sexp file.definitions s0_expr) with
  | Ok func_expr, Ok s0e -> (
      match reduce ~env:(env_of_file file) func_expr with
      | Ok fexpr -> (file_add_command file (CDiscover (fname, fexpr, s0e)), errs)
      | Error t -> (file, errs @ [ Sexp.(List [ Atom "Reduce"; t ]) ]) )
  | Error e, _ | _, Error e -> (file, errs @ [ e ])

let parse_file_with_defs (filename : string) : file * Sexp.t =
  let inc = Stdio.In_channel.create filename in
  let sexps = S.input_sexps inc in
  let parse_toplevel (file, errs) s_exp =
    match s_exp with
    (* One variable declaration. *)
    | Sexp.(List [ Atom "declare"; Atom x; typ_sexp ]) ->
        ({ file with definitions = fst (define_var file.definitions (Atom x, typ_sexp)) }, errs)
    (* Multiple variable declaration. *)
    | Sexp.(List [ Atom "declare"; List xl; typ_sexp ]) ->
        ( {
            file with
            definitions =
              List.fold_left
                ~f:(fun vars x -> fst (define_var vars (x, typ_sexp)))
                ~init:file.definitions xl;
          },
          errs )
    (* Define a global binding. *)
    | Sexp.(List [ Atom "define"; List [ Atom x; typ_sexp ]; expr_sexp ]) -> (
        let vars', nv = define_var file.definitions (Atom x, typ_sexp) in
        match expr_of_sexp file.definitions expr_sexp with
        | Ok expr ->
            ( {
                file with
                definitions = vars';
                globals = Map.set file.globals ~key:nv.vid ~data:expr;
              },
              errs )
        | Error e -> (file, errs @ [ e ]) )
    (* An eval directive *)
    | Sexp.(List [ Atom "eval"; expr_sexp ]) -> (
        match
          expr_of_sexp file.definitions expr_sexp
          >>= reduce ~env:{ evars = file.definitions; evals = file.globals }
        with
        | Ok expr -> ({ file with expressions = file.expressions @ [ expr ] }, errs)
        | Error e -> (file, errs @ [ e ]) )
    | Sexp.(List [ Atom "ceval"; expr_sexp ]) -> (
        match expr_of_sexp file.definitions expr_sexp with
        | Ok expr -> (file_add_command file (CCEval (env_of_file file, expr)), errs)
        | Error e -> (file, errs @ [ e ]) )
    | Sexp.(List [ Atom "normalize"; Atom to_mcnf; List costly; expr_sexp ]) -> (
        match
          ( expr_of_sexp file.definitions expr_sexp
            >>= reduce ~env:{ evars = file.definitions; evals = file.globals },
            Result.combine_errors (List.map ~f:(expr_of_sexp file.definitions) costly) )
        with
        | Ok e', Ok cexprs ->
            let norm_mcnf = Bool.of_string to_mcnf in
            ({ file with commands = file.commands @ [ CNormalize (norm_mcnf, cexprs, e') ] }, errs)
        | Ok _, Error l -> (file, errs @ l)
        | Error e, Ok _ -> (file, errs @ [ e ])
        | Error e, Error l -> (file, errs @ l @ [ e ]) )
    | Sexp.(List [ Atom "collect"; Atom to_mcnf; List costly; expr_sexp ]) -> (
        match
          ( expr_of_sexp file.definitions expr_sexp
            >>= reduce ~env:{ evars = file.definitions; evals = file.globals },
            Result.combine_errors (List.map ~f:(expr_of_sexp file.definitions) costly) )
        with
        | Ok e', Ok cexprs ->
            let norm_mcnf = Bool.of_string to_mcnf in
            (file_add_command file (CCollect (norm_mcnf, cexprs, e')), errs)
        | Ok _, Error l -> (file, errs @ l)
        | Error e, Ok _ -> (file, errs @ [ e ])
        | Error e, Error l -> (file, errs @ l @ [ e ]) )
    | Sexp.(List [ Atom "annot"; List costly; expr_sexp1; expr_sexp2 ]) -> (
        let env = env_of_file file in
        match
          ( expr_of_sexp file.definitions expr_sexp1 >>= reduce ~env,
            expr_of_sexp file.definitions expr_sexp2 >>= reduce ~env,
            Result.combine_errors (List.map ~f:(expr_of_sexp file.definitions) costly) )
        with
        | Ok e1', Ok e2', Ok cexprs ->
            (file_add_command file (CAnnotateUnfoldings (cexprs, e1', e2')), errs)
        | Ok _, Ok _, Error l -> (file, errs @ l)
        | Error e1, Error e2, _ -> (file, errs @ [ e1; e2 ])
        | Error e1, Ok _, _ -> (file, errs @ [ e1 ])
        | Ok _, Error e2, _ -> (file, errs @ [ e2 ]) )
    | Sexp.(List [ Atom "discover"; Atom fname; f_expr; s0_expr ]) ->
        discover_command fname f_expr s0_expr file errs
    | Sexp.(List [ Atom "discover"; f_expr; s0_expr ]) ->
        discover_command "f" f_expr s0_expr file errs
    | Sexp.(List [ Atom "print"; s ]) ->
        ({ file with commands = file.commands @ [ CPrint (Sexp.to_string s) ] }, errs)
    (* An expression *)
    | _ -> (
        match expr_of_sexp file.definitions s_exp with
        | Ok expr -> ({ file with expressions = file.expressions @ [ expr ] }, errs)
        | Error e -> (file, errs @ [ e ]) )
  in
  let file, errs = List.fold_left ~init:(empty_file, []) ~f:parse_toplevel sexps in
  (file, Sexp.List errs)

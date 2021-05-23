open Lang.Typ
open Base
open Lang.Term
open Sexplib
open Scripting
open SmtLib
open Utils
module OC = Stdio.Out_channel
module IC = Stdio.In_channel

(* Logging utilities. *)
let log_queries = ref true

let solve_verbose = ref false

let log_file = "/tmp/solver.smt2"

let log_out = ref None

let open_log () = log_out := Some (OC.create log_file)

let log c =
  match !log_out with
  | Some oc -> write_command oc c
  | None -> (
      open_log ();
      match !log_out with
      | Some oc -> write_command oc c
      | None -> Log.error (wrap "Failed to open log file.") )

(* Solver response and other types. *)
type solver_response = SmtLib.solver_response

let is_sat s = match s with Sat -> true | _ -> false

let is_unsat s = match s with Unsat -> true | _ -> false

let rec sort_of_type (t : typ) =
  match t with
  | TInt -> mk_int_sort
  | TBool -> mk_bool_sort
  | TList t -> mk_seq_sort (sort_of_type t)
  | TTup tl -> mk_tuple_sort (List.map ~f:sort_of_type tl)
  | _ -> failwith "Not supported."

let build_smt_term (t : term) : smtTerm option * command list * VarSet.t =
  let to_declare = SH.create 10 in
  let vars = SH.create 10 in
  let term_of_var (v : variable) =
    if SH.mem to_declare v.vname then ()
    else (
      SH.add to_declare v.vname (mk_const_decl v.vname (sort_of_type v.vtype));
      SH.add vars v.vname v );
    mk_var v.vname
  in
  let add_function_declaration (fname : string) (fun_decl : command) =
    if SH.mem to_declare fname then () else SH.add to_declare fname fun_decl
  in
  let rec build_list lt = Option.all (List.map ~f:(fun t -> build t.texpr) lt)
  and special_case_integer_inf b e1 e2 =
    match b with
    | Lt | Le ->
        if is_min_int e1 then Some mk_true
        else if is_min_int e2 then Some mk_false
        else if is_max_int e1 then Some mk_false
        else if is_max_int e2 then Some mk_true
        else None
    | Gt | Ge ->
        if is_min_int e1 then Some mk_false
        else if is_min_int e2 then Some mk_true
        else if is_max_int e1 then Some mk_true
        else if is_max_int e2 then Some mk_false
        else None
    | Eq -> (
        match (is_min_int e1, is_min_int e2, is_max_int e1, is_max_int e2) with
        | true, true, _, _ | false, false, true, true -> Some mk_true
        | true, _, true, _ | _, true, _, true -> Some mk_false
        | _ -> None )
    | _ -> None
  and build t =
    match t with
    | EBin (b, e1, e2) -> (
        match special_case_integer_inf b e1 e2 with
        | Some t -> Some t
        | None ->
            let t1, t2 = (build e1.texpr, build e2.texpr) in
            Option.bind (Option.both t1 t2) ~f:(fun (t1, t2) ->
                match b with
                | Plus -> Some (mk_add t1 t2)
                | Minus -> Some (mk_sub t1 t2)
                | Times -> Some (mk_mul t1 t2)
                | Div -> Some (mk_div t1 t2)
                | Max ->
                    (* add_function_declaration "max" mk_max_def; *)
                    Some (mk_ite (mk_ge t1 t2) t1 t2)
                (* mk_simple_app "max" [t1;t2] *)
                | Min -> Some (mk_ite (mk_le t1 t2) t1 t2)
                (* add_function_declaration "min" mk_min_def;
                   mk_simple_app "min" [t1;t2] *)
                | Mod -> Some (mk_simple_app "mod" [ t1; t2 ])
                | And -> Some (mk_simple_app "and" [ t1; t2 ])
                | Or -> Some (mk_simple_app "or" [ t1; t2 ])
                | Xor -> Some (mk_simple_app "xor" [ t1; t2 ])
                | Impl -> Some (mk_simple_app "=>" [ t1; t2 ])
                | Cons -> Some (mk_simple_app "cons" [ t1; t2 ])
                | Concat -> Some (mk_simple_app "append" [ t1; t2 ])
                | Eq -> Some (mk_eq t1 t2)
                | Lt -> Some (mk_lt t1 t2)
                | Gt -> Some (mk_gt t1 t2)
                | Le -> Some (mk_le t1 t2)
                | Ge -> Some (mk_ge t1 t2)
                | At -> None
                | BChoice _ -> None) )
    | EIte (c, e1, e2) ->
        Option.(
          both (build c.texpr) (both (build e1.texpr) (build e2.texpr)) >>= fun (sc, (se1, se2)) ->
          Some (mk_ite sc se1 se2))
    | EUn (u, e1) -> (
        Option.(
          build e1.texpr >>= fun se1 ->
          match u with
          | Not -> Some (mk_simple_app "not" [ se1 ])
          | Neg -> Some (mk_simple_app "-" [ se1 ])
          | _ -> None) )
    | EConst c -> (
        match c with
        | CInt i -> Some (mk_int i)
        | CBool b -> Some (if b then mk_true else mk_false)
        | CEmpty -> Some mk_nil
        | _ -> None )
    | EVar (Var v) -> Some (term_of_var v)
    | EHole _ -> Some (term_of_var _HOLE_)
    | EApp (ft, args) -> (
        match ft.texpr with
        | EVar (Var f) -> (
            match Lang.AcTerm.get_op f with
            | Some x ->
                ( match x with
                | Max -> add_function_declaration "max" mk_max_def
                | Min -> add_function_declaration "min" mk_min_def
                | _ -> () );
                Option.(build_list args >>| mk_simple_app f.vname)
            | None ->
                failwith
                  Fmt.(
                    to_to_string
                      (fun f -> pf f "(VAR) not supported : %a." Lang.TermPp.pp_term)
                      (mk_term t)) )
        | _ ->
            failwith
              Fmt.(
                to_to_string
                  (fun f -> pf f "(APP) not supported : %a." Lang.TermPp.pp_term)
                  (mk_term t)) )
    | ETuple el -> Option.(build_list el >>| mk_simple_app "tuple")
    | EList el -> Option.(build_list el >>| mk_simple_app "list")
    | EMem (_, _) -> None
    | EFoldL (_, init, l) -> Option.(build_list [ init; l ] >>| mk_simple_app "foldl")
    | EFoldR (_, init, l) -> Option.(build_list [ init; l ] >>| mk_simple_app "foldr")
    | EMemStruct _ | EStruct _ ->
        Log.error (printer_msg "Struct: %a" Lang.TermPp.pp_term (mk_term t));
        Log.error (wrap "Cannot create smt term for struct");
        None
    | ELetValues _ | EChoice _ | EEmpty | EWith _ | ESetL _ | ELet _ | EPLet _ | ELambda (_, _) ->
        None
  in
  let smt_term = build t.texpr in
  (smt_term, SH.fold (fun _ decl decls -> decls @ [ decl ]) to_declare [], VarSet.of_sh vars)

let build_terms (el : term list) =
  let bt_acc (tl, decls, vars) e =
    let t, d, v = build_smt_term e in
    (tl @ [ t ], decls @ d, vars $|| v)
  in
  List.fold_left ~f:bt_acc ~init:([], [], VarSet.empty) el

type online_solver = { pid : int; inputc : OC.t; outputc : IC.t; declared : String.t Hash_set.t }

let solver_write (solver : online_solver) (c : command) : unit =
  write_command solver.inputc c;
  OC.output_char solver.inputc '\n';
  OC.flush solver.inputc

let solver_read (solver : online_solver) : solver_response =
  let l =
    try Sexp.input_sexp solver.outputc
    with Sys_error _ -> failhere Caml.__FILE__ "solver_read" "Couldn't read solver answer."
  in
  parse_response [ l ]

let exec_command (solver : online_solver) (c : command) =
  if !log_queries then log c;
  ( match c with
  | DefineSmtSort (s, _, _)
  | DeclareDatatype (s, _)
  | DeclareConst (s, _)
  | DefineFunRec (s, _, _, _)
  | DefineFun (s, _, _, _)
  | DeclareFun (s, _, _) ->
      Hash_set.add solver.declared (str_of_symb s)
  | _ -> () );
  solver_write solver c;
  solver_read solver

let silent_command (solver : online_solver) (c : command) =
  if !log_queries then log c;
  solver_write solver c;
  ignore (solver_read solver)

(* keep track of all solvers we spawn, so we can close our read/write
   FDs when the solvers exit *)
let online_solvers : (int * online_solver) list ref = ref []

let handle_sigchild (_ : int) : unit =
  if List.length !online_solvers = 0 then ignore @@ Unix.waitpid [] (-1)
  else
    let pid, _ = Unix.waitpid [] (-1) in
    (if !solve_verbose then Fmt.(pf stdout "[WARNING] Solver (pid %d) exited!@." pid));
    match List.Assoc.find !online_solvers ~equal:( = ) pid with
    | Some solver ->
        IC.close solver.outputc;
        OC.close solver.inputc
    | None -> ()

let () = Caml.Sys.set_signal Caml.Sys.sigchld (Caml.Sys.Signal_handle handle_sigchild)

let make_solver (path : string) : online_solver =
  let open Unix in
  let z3_stdin, z3_stdin_writer = pipe () in
  let z3_stdout_reader, z3_stdout = pipe () in
  (* If the ocaml ends of the pipes aren't marked close-on-exec, they
     will remain open in the fork/exec'd z3 process, and z3 won't exit
     when our main ocaml process ends. *)
  set_close_on_exec z3_stdin_writer;
  set_close_on_exec z3_stdout_reader;
  let pid = create_process path [| path; "-in"; "-smt2" |] z3_stdin z3_stdout stderr in
  let in_chan = in_channel_of_descr z3_stdout_reader in
  let out_chan = out_channel_of_descr z3_stdin_writer in
  OC.set_binary_mode out_chan false;
  IC.set_binary_mode in_chan false;
  let solver =
    { pid; inputc = out_chan; outputc = in_chan; declared = Hash_set.create (module String) }
  in
  online_solvers := (pid, solver) :: !online_solvers;
  try
    match exec_command solver mk_print_success with
    | SExps [ Sexp.Atom "success" ] -> solver
    | _ -> failwith "could not configure solver to :print-success"
  with Sys_error s -> failwith ("couldn't talk to solver, double-check path. Sys_error " ^ s)

let close_solver solver = ignore @@ exec_command solver mk_exit

(** Returns empty response if commands is empty, otherwise, executes the LAST command in the
    command list.
*)
let call_solver solver commands =
  match ListTools.last commands with
  | Some c -> exec_command solver c
  | None ->
      Log.error (wrap "Called solver without any command.");
      SExps []

(** Create a process with a Z3 sovler. *)
let make_z3_solver () = make_solver Config.z3

let call_solver_default solver commands =
  match solver with
  | Some s -> call_solver s commands
  | None ->
      let s = make_z3_solver () in
      let r = call_solver s commands in
      close_solver s;
      r

(* Helpers for solver calls to check simple formula satisfiability,
   simplify an expression, get unsat cores.
*)
exception SolverError of Sexp.t list

let solver_response_errors (response : solver_response) =
  let rec is_error_sexp sexp =
    match sexp with
    | Sexp.Atom _ -> []
    | List (Atom "error" :: _) -> [ sexp ]
    | List ls -> Caml.List.flatten (List.map ~f:is_error_sexp ls)
  in
  match response with SExps l -> Caml.List.flatten (List.map ~f:is_error_sexp l) | _ -> []

let pp_solver_response = SmtLib.pp_solver_response

let declare (solver : online_solver) (var : variable) =
  if Hash_set.mem solver.declared var.vname then
    Fmt.(
      pf stdout "[WARNING] In solver %i variable %s has already been declared.@." solver.pid
        var.vname)
  else
    let d = mk_const_decl var.vname (sort_of_type var.vtype) in
    silent_command solver d;
    Hash_set.add solver.declared var.vname

let decls_of ?(include_branches = false) t =
  List.fold_left
    ~f:(fun (c_t, decls, vars) (conj, e) ->
      let trms, decl, v = build_terms conj in
      let t', d', v' = build_smt_term e in
      let decls = decls @ decl @ if include_branches then d' else [] in
      let vars = vars $|| v $|| if include_branches then v' else VarSet.empty in
      (c_t @ [ (trms, t') ], decls, vars))
    ~init:([], [], VarSet.empty) t

let declare_symb_define (s : online_solver) (sd : symbolic_define) =
  List.iter ~f:(declare s) (VarSet.elements sd.s_vars)

let declare_all s decls =
  List.iter ~f:(fun decl -> ignore (exec_command s decl)) (remove_duplicate_decls s.declared decls)

let get_exprs_of_response (vars : VarSet.t) (r : solver_response) =
  match r with
  | SExps r -> Result.combine_errors (List.map ~f:(expr_of_sexp vars) r)
  | _ -> Error [ Atom "Bad solver response." ]

let spush solver = silent_command solver (mk_push 1)

let spop solver = silent_command solver (mk_pop 1)

let sassert solver term =
  let smtto, _, _ = build_smt_term term in
  match smtto with Some smtt -> silent_command solver (mk_assert smtt) | None -> ()

(** Perform a simple check equiv. to (assert t) (check-sat). If a solver is given,
    we assume all the variables are defined and the check is performed with
    a push/pop.
*)
let check_simple ?(solver = None) (t : term) =
  let t0 = match Lang.Unfold.reduce t with Ok _t -> _t | _ -> t in
  let t' = Lang.AcTerm.rebuild_tree_AC Terms.compare t0 in
  let term, required_decls, _ = build_smt_term t' in
  match term with
  | Some term -> (
      match solver with
      | None ->
          let assert_simple = mk_assert term in
          call_solver_default solver (required_decls @ [ assert_simple; mk_check_sat ])
      | Some s ->
          silent_command s (mk_push 1);
          silent_command s (mk_assert term);
          let r = exec_command s mk_check_sat in
          silent_command s (mk_pop 1);
          r )
  | None -> Unknown

let check_implication ?(solver = None) (t0 : term) ~implies:(implied : term) =
  match check_simple ~solver (Lang.Term.mk_not (mk_impl t0 implied)) with
  | Unsat -> true
  | _ -> false

let check_equals ~(solver : online_solver) (t0 : term) (t1 : term) =
  match check_simple ~solver:(Some solver) Lang.Term.(mk_not (mk_bin t0 Eq t1)) with
  | Unsat -> true
  | Sat -> false
  | r ->
      Log.error (printer_msg "Solver response:%a@." pp_solver_response r);
      failwith "Solver."

let get_unsat_core (solver : online_solver) (asserts : (term * string) list) : string list =
  (* Solver require the assertions to be named to track them for the unsat core *)
  let named_asserts, decls =
    List.fold_left
      ~f:(fun (x, decls) (t, name) ->
        let term, req_decls, _ = build_smt_term t in
        ( (match term with Some term -> x @ [ mk_named_assert name term ] | None -> x),
          decls @ req_decls ))
      ~init:([], []) asserts
  in
  let commands =
    [ mk_set_option "produce-unsat-cores" "true" ]
    @ remove_duplicate_decls solver.declared decls
    @ named_asserts @ [ mk_check_sat ] @ [ GetUnsatCore ]
  in
  let call_res = call_solver_default (Some solver) commands in
  let errors = solver_response_errors call_res in
  if List.length errors > 0 then raise (SolverError errors)
  else
    match call_res with
    | SExps l -> (
        match l with
        | _ :: errors_or_core -> (
            match errors_or_core with [ List core ] -> List.map ~f:Sexp.to_string core | _ -> [] )
        | _ -> [] )
    | _ -> []

let z3_simplify ~solver:(s : online_solver option) (t : term) =
  let solver = match s with Some solver -> solver | None -> make_z3_solver () in
  let simple_strategy te =
    let term, req_decls, vars = build_smt_term te in
    let response =
      match term with
      | Some term ->
          let simpl_command = mk_simplify term in
          call_solver_default (Some solver)
            (remove_duplicate_decls solver.declared req_decls @ [ simpl_command ])
      | None -> Unknown
    in
    match response with
    | SExps sexps -> (
        if not (List.length sexps = 1) then (
          ( if !solve_verbose then
            Fmt.(pf stderr "[simplify] Too many responses s-exps: %a@." Sexp.pp (Sexp.List sexps))
          );
          None )
        else
          match expr_of_sexp vars (List.hd_exn sexps) with
          | Result.Ok e -> Some e
          | Result.Error s ->
              (if !solve_verbose then Fmt.(pf stderr "[simplify] Parsing error: %a@." Sexp.pp s));
              None )
    | _ ->
        ( if !solve_verbose then
          Fmt.(pf stderr "[simplify] Bad response to simplify: %a@." pp_solver_response response) );
        None
  in
  simple_strategy t

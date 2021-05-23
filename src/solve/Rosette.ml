open Base
open Fmt
open Lang.Typ
open Lang.Term
open Lang.TermPp
open Utils
open Lwt_process
module S = Sexplib

type rosette_symbolic = RInt | RBool | RReal

let pp_rosette_symbolic (frmt : Formatter.t) (rs : rosette_symbolic) : unit =
  pf frmt "%s" (match rs with RInt -> "integer?" | RBool -> "boolean?" | RReal -> "real?")

(* Prints the variable definition and returns the univerisally quantified variables. *)
let pp_symbolic_define ?(force_name = None) (frmt : Formatter.t) (sd : symbolic_define) : VarSet.t =
  let int_decls, bool_decls, _ =
    let f v = match v.vtype with TInt -> `Fst v | TBool -> `Snd v | _ -> `Trd v in
    List.partition3_map ~f (Set.to_list sd.s_vars)
  in
  if List.length int_decls > 0 then
    pf frmt "@[<v 2>(define-symbolic %a integer?)@]@."
      (list ~sep:(Fmt.any " ") pp_variable)
      int_decls;
  if List.length bool_decls > 0 then
    pf frmt "@[<v 2>(define-symbolic %a boolean?)@]@."
      (list ~sep:(Fmt.any " ") pp_variable)
      bool_decls;
  ( match force_name with
  | None ->
      List.iter
        ~f:(fun (v, t) -> pf frmt "@[<v 2>(define %s %a)@]@." v.vname rpp_term t)
        sd.s_define
  | Some s ->
      List.iter ~f:(fun (_, t) -> pf frmt "@[<v 2>(define %s %a)@]@." s rpp_term t) sd.s_define );
  sd.s_vars

(* Parsing responses *)
exception ParseError

let enrich_error m s = Sexp.List [ Atom m; s ]

let match_int s = Str.string_match (Str.regexp "-?[0-9]+") s 0

let is_struct_field_accessor (s : string) =
  match String.split s ~on:'-' with
  | [ s_name; s_field ] -> (
      match Lang.Structs.get s_name with
      | Some (TStruct (s, fields)) ->
          if List.exists fields ~f:(fun (fs, _) -> String.equal fs s_field) then Some (s, s_field)
          else None
      | _ -> None )
  | _ -> None

let parse_fail_msg s = Log.error (printer_msg "Failed parsing %a." Sexp.pp_hum s)

let rec parse_response (env : VarSet.t) (s : Sexp.t) : term =
  let t =
    Sexp.(
      match s with
      | Atom "true" -> mk_true
      | Atom "#t" -> mk_true
      | Atom "false" -> mk_false
      | Atom "#f" -> mk_false
      | Atom a when match_int a ->
          let ival = Int.of_string a in
          if Int.(ival = int_range) then mk_vt _INT_MAX
          else if Int.(ival = -int_range) then mk_vt _INT_MIN
          else mk_int ival
      | List [ Atom a ] when is_some (parse_binop (Atom a)) -> (
          match parse_binop (Atom a) with
          | Some And -> mk_true
          | Some Or -> mk_false
          | Some Plus -> mk_int 0
          | Some Times -> mk_int 1
          | _ -> failwith "Error: semantics of Rosette for %s alone?" a )
      (* Just a variable *)
      | Atom s when is_some (VarSet.find_by_name env s) -> (
          match VarSet.find_by_name env s with
          | Some v -> mk_vt v
          | None ->
              parse_fail_msg (enrich_error "Unexpected / Variable" (Atom s));
              raise ParseError )
      (* Struct accessor *)
      | List [ Atom saccessor; struc ] when is_some (is_struct_field_accessor saccessor) -> (
          match is_struct_field_accessor saccessor with
          | Some (s, field) -> mk_struct_mem ~s field (parse_response env struc)
          | None ->
              parse_fail_msg (enrich_error "struct-accessor" s);
              raise ParseError )
      | List (Atom "list" :: rest) -> mk_list (List.map ~f:(parse_response env) rest)
      | List (Atom "choose" :: hd :: _) -> parse_response env hd
      | List [ Atom "take"; le; ie ] -> mk_un (Take (parse_response env ie)) (parse_response env le)
      | List [ List [ Atom "lambda"; List [ Atom s1 ]; List [ f; Atom s1'; e ] ]; x ]
        when String.equal s1 s1' ->
          parse_response env (List [ f; x; e ])
      | List [ Atom "lambda"; List args; body ] ->
          let args =
            let f arg =
              match arg with
              | Atom s -> (
                  match VarSet.find_by_name env s with
                  | Some v -> v
                  | _ ->
                      parse_fail_msg (enrich_error "lambda-arg" (Atom s));
                      raise ParseError )
              | _ ->
                  parse_fail_msg (enrich_error "lambda" (List args));
                  raise ParseError
            in
            List.map ~f args
          in
          mk_lambda args (parse_response env body)
      | List [ Atom "foldl"; f; init; el ] ->
          mk_foldl ~f:(parse_response env f) ~init:(parse_response env init) (parse_response env el)
      | List [ Atom "??" ] -> mk_int 0
      | List [ Atom "let"; List [ binding ]; body ] ->
          let x, t = parse_binding env binding in
          let env' = Set.add env x in
          mk_let (Var x) t (parse_response env' body)
      | List [ Atom "if"; cond; tr; fs ] ->
          mk_ite (parse_response env cond) (parse_response env tr) (parse_response env fs)
      | List [ s; op1; op2 ] when is_some (parse_binop s) -> (
          match parse_binop s with
          | Some bop -> mk_bin (parse_response env op1) bop (parse_response env op2)
          | None ->
              parse_fail_msg (enrich_error "Binop" s);
              raise ParseError )
      | List (s :: op1 :: op2 :: rest) when is_some (parse_binop s) -> (
          match parse_binop s with
          | Some bop ->
              mk_binop_of_list bop (parse_response env op1) (parse_response env op2)
                (List.map ~f:(parse_response env) rest)
          | None ->
              parse_fail_msg (List [ Atom "Binop-assoc"; s ]);
              raise ParseError )
      | List [ s; op1 ] when is_some (parse_unop s) -> (
          match parse_unop s with
          | Some uop -> mk_un uop (parse_response env op1)
          | None ->
              parse_fail_msg (List [ Atom "unop"; s ]);
              raise ParseError )
      | List [ Atom "list-ref"; li; ind ] -> (
          match parse_response env ind with
          | { texpr = EConst (CInt 0); _ } -> mk_un Hd (parse_response env li)
          | _ as ind -> mk_bin (parse_response env li) At ind )
      | List (Atom s :: fields) when is_some (Lang.Structs.get s) -> parse_struct s env fields
      | List (List (Atom "choose" :: hd :: _) :: args) -> parse_response env (List (hd :: args))
      | List (s :: args) ->
          let f =
            try parse_response env s
            with _ ->
              parse_fail_msg (List [ Atom "application"; s ]);
              raise ParseError
          in
          let args = List.map ~f:(parse_response env) args in
          mk_app f args
      | _ ->
          parse_fail_msg s;
          raise ParseError)
  in
  Lang.AcTerm.simplify_easy t

and parse_binding env s : variable * term =
  Sexp.(
    match s with
    | List [ Atom varname; body ] -> (
        let bdy = parse_response env body in
        match type_of bdy with
        | Ok t -> (mk_var ~not_fresh:true ~name:varname t, bdy)
        | _ ->
            parse_fail_msg (enrich_error "parse-binding" s);
            raise ParseError )
    | _ ->
        parse_fail_msg (enrich_error "parse-binding" s);
        raise ParseError)

and parse_struct (s : string) (env : VarSet.t) (sfields : Sexp.t list) : term =
  match Lang.Structs.get s with
  | Some (TStruct (_, fields)) -> (
      match List.map2 fields sfields ~f:(fun (a, _) b -> (a, parse_response env b)) with
      | Ok l -> mk_struct l
      | _ ->
          parse_fail_msg (enrich_error "struct-fields" Sexp.(List (Atom s :: sfields)));
          raise ParseError )
  | _ ->
      parse_fail_msg (enrich_error "struct-name" Sexp.(List (Atom s :: sfields)));
      raise ParseError

and parse_binop se =
  match se with
  | Sexp.Atom opname -> (
      match opname with
      | "+" -> Some Plus
      | "-" -> Some Minus
      | "*" -> Some Times
      | "/" -> Some Div
      | "max" -> Some Max
      | "min" -> Some Min
      | "modulo" -> Some Mod
      | "and" -> Some And
      | "&&" -> Some And
      | "or" -> Some Or
      | "||" -> Some Or
      | "xor" -> Some Xor
      | "cons" -> Some Cons
      | "append" -> Some Concat
      | ">" -> Some Gt
      | ">=" -> Some Ge
      | "<" -> Some Lt
      | "<=" -> Some Le
      | "=" -> Some Eq
      | _ -> None )
  | Sexp.(List (Atom "choose" :: choices)) -> (
      match choices with
      | hd :: _ -> parse_binop hd
      | _ ->
          parse_fail_msg (enrich_error "choose-binop" se);
          raise ParseError )
  | _ -> None

and parse_unop se =
  match se with
  | Sexp.Atom opname -> (
      match opname with
      | "not" -> Some Not
      | "abs" -> Some Abs
      | "-" -> Some Neg
      | "identity" -> Some Id
      | "car" -> Some Hd
      | "cdr" -> Some Tl
      | "empty?" -> Some IsEmpty
      | _ -> None )
  | _ -> None

let parse_with ~f maybe_solns =
  let f (si, soln) =
    match soln with
    | [] -> None
    | [ Sexp.Atom "unsat" ] -> None
    | [ Sexp.Atom "sat" ] -> Some si
    | _ -> Some (f si soln)
  in
  match maybe_solns with Some solns -> List.filter_map ~f solns | None -> []

(* Solver handles *)

let fetch_solution filename =
  Log.debug ~level:2 (fun f () -> pf f "Fetching solution in %s" filename);
  let soln = S.Sexp.input_sexps (Stdio.In_channel.create filename) in
  Log.debug ~level:4
    (printer_msg "@[Solution returned by Rosette is:@;@[%a@]@]" (list ~sep:sp Sexp.pp_hum) soln);
  soln

let is_unsat_resp sexp =
  S.Sexp.(
    match sexp with
    | [ Atom "unsat" ] -> true
    | [ List [ Atom "unsat" ] ] -> true
    | [] -> true
    | [ Atom "" ] -> true
    | _ -> false)

let lwt_racket_command ((target, outf) : string * string) : string * process_out =
  (* let racket_command = shell (str "racket %s" target) in
     (outf, open_process_out ~timeout:3600. ~stdout:`Dev_null racket_command) *)
  ( outf,
    open_process_out ~timeout:3600. ~stdout:`Dev_null (Config.racket, [| Config.racket; target |])
  )

(*
  A list of pairs of string, the first is the sketch name file,
  and the second the output file of the sketch.
 *)
let exec_solver (filenames : (string * string) list) : (string * Sexp.t list) option list =
  let processes = List.map ~f:lwt_racket_command filenames in
  (* let rec wait_first_sat processes =
     in *)
  let proc_status _ _ otf =
    let sol =
      try fetch_solution otf
      with Sys_error s ->
        Log.warning ~level:4 (printer_msg "Sys_error (%a)" string s);
        [ Atom "unsat" ]
    in
    if is_unsat_resp sol then (
      Log.debug_msg ~level:4
        Fmt.(str "@[Solution is unsat:@;@[%a@]@]" (list ~sep:sp Sexp.pp_hum) sol);
      None )
    else (
      List.iter ~f:(fun (_, proc) -> proc#kill Caml.Sys.sigkill) processes;
      Some (otf, sol) )
  in
  let cp =
    List.map ~f:(fun (otf, proc) -> Lwt.map (fun x -> proc_status proc x otf) proc#status) processes
  in
  let resps = Lwt_main.run (Lwt.all cp) in
  List.iter ~f:(fun (_, outf) -> try Caml.Sys.remove outf with _ -> ()) filenames;
  resps

let check_exit_status = function
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED r -> Log.warning_msg (Fmt.str "the process terminated with exit code (%d)!" r)
  | Unix.WSIGNALED n ->
      Log.warning_msg (Fmt.str "the process was killed by a signal (number: %d)!" n)
  | Unix.WSTOPPED n ->
      Log.warning_msg (Fmt.str "the process was stopped by a signal (number: %d)!" n)

let pid_inactive pid =
  try
    Unix.kill pid 0;
    false
  with
  | Unix.Unix_error (Unix.ESRCH, _, _) ->
      Log.debug ~level:2 (fun f () -> Fmt.(pf f "Process %i ended." pid));
      true
  | _ as exn -> raise exn

let racket_command ((target, outf) : string * string) =
  (outf, (Config.racket, [| Config.racket; target |]))

let unix_parallel_exec_solver (filenames : (string * string) list) : (string * Sexp.t list) option =
  let problem_instances = List.map ~f:racket_command filenames in
  let nullout = Unix.descr_of_out_channel (Stdio.Out_channel.create "/dev/null") in
  let processes =
    List.map
      ~f:(fun (outf, (prog, args)) ->
        let pid = Unix.create_process prog args nullout nullout nullout in
        if pid_inactive pid then
          Log.debug ~level:2 (fun f () -> Fmt.(pf f "Failed to start %i." pid))
        else Log.debug ~level:2 (fun f () -> Fmt.(pf f "Started process %i." pid));
        (outf, pid))
      problem_instances
  in
  let kill_remaining l =
    let f (_, pid) =
      if pid_inactive pid then Log.debug ~level:2 (fun f () -> Fmt.(pf f "Exited %i." pid))
      else Log.debug ~level:2 (fun f () -> Fmt.(pf f "Kill %i." pid));
      try Unix.kill pid Caml.Sys.sigint with
      | Unix.Unix_error (Unix.ESRCH, _, _) -> ()
      | _ as exn -> raise exn
    in
    ignore (List.map ~f l)
  in
  let rec loop_over_processes l =
    match l with
    | [] -> None
    | (otf, pid) :: tl ->
        Unix.sleepf 0.01;
        if pid_inactive pid then
          try
            let sol = fetch_solution otf in
            if is_unsat_resp sol then (
              Log.debug ~level:2 (fun f () -> Fmt.(pf f "Unsat."));
              loop_over_processes tl )
            else (
              kill_remaining tl;
              Some (otf, sol) )
          with Sys_error _ -> loop_over_processes tl
        else loop_over_processes (tl @ [ (otf, pid) ])
  in
  Unix.sleepf 0.05;
  let res = loop_over_processes processes in
  List.iter ~f:(fun (_, outf) -> try Caml.Sys.remove outf with _ -> ()) filenames;
  res

(**
   Solve a list of sketch name file, output file in parallel
*)
let parallel_solve ?(use_lwt = false) (problems : (string * string) list) =
  if !Config.always_use_lwt || use_lwt then exec_solver problems
  else [ unix_parallel_exec_solver problems ]

let no_solution () =
  Log.error (wrap "No solution could be synthesized.");
  failwith "Abort synthesis process."

let solve_sketches ?(use_lwt = false) (compile_func : 'a -> unit)
    (get_in_out : 'a -> string * string) (all_sketches : 'a list) =
  let rec solve_rec sketches =
    let to_solve, remaining = List.split_n sketches Config.num_parallel_processes in
    let solutions =
      List.iter ~f:compile_func to_solve;
      parallel_solve ~use_lwt (List.map ~f:(fun si -> get_in_out si) to_solve)
    in
    let solutions_with_sketch =
      let f maybe_response =
        match maybe_response with
        | Some (otf, soln) -> (
            match List.find to_solve ~f:(fun si -> String.equal otf (snd (get_in_out si))) with
            | Some si -> [ (si, soln) ]
            | None -> [] )
        | None -> []
      in
      List.concat_map ~f solutions
    in
    match solutions_with_sketch with
    | [] -> if List.length remaining > 0 then solve_rec remaining else None
    | hd :: _ -> Some [ hd ]
    (* DANGER *)
  in
  solve_rec all_sketches

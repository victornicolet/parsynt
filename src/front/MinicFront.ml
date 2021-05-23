open Base
open Lexing
open Minic
open Minic2MiniF
open Minif2Lang
open Utils
open Lang.Typ
open Lang.Term
module P = Minic_parser
module L = Minic_lexer

exception SyntaxError of string

exception Error

let verbose = ref true

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Fmt.(pf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1))

let parsefile filename =
  let lexbuf = from_channel (Stdio.In_channel.create filename) in
  try convert (P.main L.token lexbuf) with
  | SyntaxError msg ->
      Fmt.(pf stderr "%a: %s@." print_position lexbuf msg);
      raise (SyntaxError msg)
  | Error ->
      Fmt.(pf stderr "%a: syntax error@." print_position lexbuf);
      raise Error

let sanitize_loop_body (rdefs : (int * term) list IM.t) (t : term) : VarSet.t * term =
  let varset = Lang.Analyze.vars_of t in
  let l =
    let f accum v =
      match Map.find rdefs v.vid with Some [ (_, t) ] -> mk_let (Var v) t accum | _ -> accum
    in
    Set.fold varset ~init:mk_empty_term ~f
  in
  let t' = Lang.TermUtils.reduce_simple_bindings (Lang.TermUtils.append_let l t) in
  let fv = Lang.Analyze.free_variables t' in
  match t'.texpr with
  | ELet (_, bnd, { texpr = EEmpty; _ }) -> (fv, bnd)
  | _ ->
      Log.error (printer_msg "%a@." Lang.TermPp.rpp_term_r t');
      failhere Caml.__FILE__ "sanitize_loop_body"
        "Could not translate loop body to proper function."

module MFile = struct
  (* A file contains toplevel pointer to loops, globals and return statements in the program. *)
  type t = { fname : string; fstmts : ms_stmt list; fglobs : int list }

  let empty = { fname = "empty.minic"; fstmts = []; fglobs = [] }

  let add_glob (f : t) (i : int) = { f with fglobs = i :: f.fglobs }

  let add_stmt (f : t) (s : ms_stmt) =
    match s.skind with
    | MsForStmt (_, _) -> f
    | MsWhileStmt (_, _) -> f
    | MsIfStmt (_, _, _) -> f
    | MsCompStmt _ -> f
    | MsDeclStmt _ -> add_glob f s.sid
    | MsTypeDeclStmt (_, _) -> add_glob f s.sid
    | MsInstrStmt _ -> f
    | MsReturn _ -> f
    | MsReturnCstr (_, _) -> f
    | MsEmpty -> f
    | MsAssertion _ -> f

  let process (filename : string) : t =
    let program = parsefile filename in
    match program with
    | MsFunctions _ -> failwith "Not implemented for functions."
    | MsBody l -> List.fold ~f:add_stmt ~init:{ empty with fstmts = l } l
end

module FFile = struct
  (* A file contains toplevel pointer to loops, globals and return statements in the program. *)
  type t = {
    fname : string;
    fstmts : mf_stmt list;
    fglobs : int list;
    freaching : (int * term) list IM.t IM.t;
  }

  let empty = { fname = "empty.minic"; fstmts = []; fglobs = []; freaching = IM.empty }

  let from_mfile (mfile : MFile.t) : t =
    let cenv = env_of_globs mfile.fstmts mfile.fglobs in
    let fstmts = List.map ~f:(ms_stmt_to_mf_stmt cenv) mfile.fstmts in
    let prog_reaching_defs = find_reaching_fdefs fstmts in
    { fname = mfile.fname; fstmts; fglobs = mfile.fglobs; freaching = prog_reaching_defs }
end

module LangFile = struct
  type t = {
    lf_original : FFile.t;
    lf_loops : (VarSet.t * term * VarSet.t) list;
    lf_asserts : (VarSet.t * term) list;
  }

  let add_loop_body ((vs, term) : VarSet.t * term) (lf : t) : t =
    { lf with lf_loops = lf.lf_loops @ [ (vs, term, VarSet.empty) ] }

  let close_loop_body (vs : VarSet.t) (lf : t) : t =
    match (List.drop_last lf.lf_loops, List.last lf.lf_loops) with
    | Some l, Some (vars, loop_term, closing) ->
        { lf with lf_loops = l @ [ (vars, loop_term, Set.union vs closing) ] }
    | _ -> lf

  let from_ffile (ffile : FFile.t) =
    List.fold ffile.fstmts ~init:{ lf_original = ffile; lf_loops = []; lf_asserts = [] }
      ~f:(fun lfile s ->
        match s.skind with
        | FForStmt (_, _) ->
            let fdefs_at_stmt =
              match Map.find ffile.freaching s.sid with
              | Some x -> x
              | None ->
                  failhere Caml.__FILE__ "from_ffile"
                    "Unexpected : no reaching definition for loop."
            in
            let loop_term = minif2lang s in
            let loop_func_body = sanitize_loop_body fdefs_at_stmt loop_term in
            add_loop_body loop_func_body lfile
        | FReturn t -> close_loop_body (Lang.Analyze.free_variables t) lfile
        | FReturnCstr ({ texpr = EVar (Var v); _ }, "set") ->
            let vset = { v with vattrs = [ SetLike ] } in
            close_loop_body (VarSet.singleton vset) lfile
        | FAssertion ast -> (
            match ast with
            | FAForall (it, term) -> (
                match it with
                | FIList (_, li) ->
                    let fv = Lang.Analyze.free_variables li in
                    { lfile with lf_asserts = lfile.lf_asserts @ [ (fv, term) ] }
                | _ -> failhere Caml.__FILE__ "from_ffile" "Assertion not supported." )
            | FATerm t ->
                let fv = Lang.Analyze.free_variables t in
                { lfile with lf_asserts = lfile.lf_asserts @ [ (fv, t) ] } )
        | _ -> lfile)
end

let get_problems filename =
  let mfile = MFile.process filename in
  let ffile = FFile.from_mfile mfile in
  LangFile.from_ffile ffile

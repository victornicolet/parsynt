open Base
open Fmt
open Lang
open Lang.ResourceModel
open Lang.SolutionDescriptors
open Lang.Term
open Lang.TermUtils
open Lang.Typ
open Lang.Unfold
open Discover
open Utils
open TermPp
open Sexplib
open Solve.SinglePassSketches
open Solve.DivideSketches
open Solve.JoinSketches

let skip_flag = false

(* ============================================================================================= *)
(* ==================  TRANSLATION TO SFSP : DECOMPOSING FUNCTIONS   =========================== *)
(* ============================================================================================= *)

(**
  Find the list-typed fields in a list of record fields.
*)
let find_list_field = List.find ~f:(fun (_, t) -> match t with TList _ -> true | _ -> false)

let extend_init (orig_t : typ) (new_t : typ) (t : term) : term =
  match (orig_t, t.texpr, new_t) with
  | TStruct _, EStruct mems, TStruct (_, (lm, lt) :: _) ->
      let empty_list = mk_term ~ttyp:(Some lt) (EList []) in
      { t with texpr = EStruct ((lm, empty_list) :: mems); ttyp = new_t }
  | TBool, _, TStruct (_, [ (lm, lt); (sm, _) ]) | TInt, _, TStruct (_, [ (lm, lt); (sm, _) ]) ->
      let empty_list = mk_term ~ttyp:(Some lt) (EList []) in
      { t with texpr = EStruct [ (lm, empty_list); (sm, t) ]; ttyp = new_t }
  | _ ->
      Log.error (printer2_msg "(init) Cannot extend %a to type %a." rpp_term t pp_typ new_t);
      failwith "sfsp"

let extend_func (orig_t : typ) (new_t : typ) (t : term) : term =
  let ext_f x old_accum new_accum body =
    match (orig_t, new_t) with
    | TStruct (old_s, memts), TStruct (new_s, (sl, _) :: _) ->
        let body =
          List.fold ~init:body
            ~f:(fun body (fname, _) ->
              replace_expr
                ~old:(mk_struct_mem ~s:old_s fname (mk_vt old_accum))
                ~by:(mk_struct_mem ~s:new_s fname (mk_vt new_accum))
                body)
            memts
        in
        let body =
          let tr rcall term =
            match term.texpr with
            | ELet (x, e, bdy) -> Some (mk_let x e (rcall bdy))
            | EStruct mems -> (
                match type_of term with
                | Ok t when ETypes.(t = orig_t) ->
                    let z =
                      mk_bin
                        (mk_struct_mem ~s:new_s sl (mk_vt new_accum))
                        Concat
                        (mk_list [ mk_vt x ])
                    in
                    let mems = List.map ~f:(fun (_s, _t) -> (_s, rcall _t)) mems in
                    Some (mk_struct ((sl, z) :: mems))
                | _ -> None )
            | _ -> None
          in
          Transform.transform tr body
        in
        ELambda ([ x; new_accum ], body)
    | TBool, TStruct (sn, [ (sl, _); (sm, st) ]) | TInt, TStruct (sn, [ (sl, _); (sm, st) ]) ->
        let body =
          replace_expr ~old:(mk_vt old_accum) ~by:(mk_struct_mem ~s:sn sm (mk_vt new_accum)) body
        in
        let body =
          let y = mk_var st in
          let z = mk_bin (mk_struct_mem ~s:sn sl (mk_vt new_accum)) Concat (mk_list [ mk_vt x ]) in
          mk_let (Var y) body (mk_struct [ (sl, z); (sm, mk_vt y) ])
        in
        ELambda ([ x; new_accum ], body)
    | _ ->
        Log.error (printer2_msg "(func) Cannot extend %a to type %a." rpp_term t pp_typ new_t);
        failwith "sfsp"
  in
  match t.texpr with
  | ELambda ([ x; accum ], body) -> (
      let accum' = mk_var ~name:Naming.new_accumulator new_t in
      let body' = Lang.TermUtils.lang_opt_passes { t with texpr = ext_f x accum accum' body } in
      match type_term body' with
      | Ok t -> t
      | Error e ->
          typecheck_err e;
          failwith "extend_func" )
  | _ ->
      Log.error (printer_msg "Lambda in fold has wrong number of args:@;%a" rpp_term t);
      failwith "sfsp"

let get_extension ?(lfield = None) list_t orig_t : typ * string =
  match orig_t with
  | TStruct (s, fields) -> (
      let l =
        match lfield with Some s -> s | None -> Alpha.get_new_name Naming.new_struct_list_field
      in
      let mems' = (l, list_t) :: fields in
      match Structs.name_of_fields mems' with
      | None ->
          let s' = Alpha.get_new_name s in
          Structs.add_name s' mems';
          (TStruct (s', mems'), l)
      | Some s' -> (TStruct (s', mems'), l) )
  | TBool | TInt ->
      let name = Alpha.get_new_name Naming.new_accumulator_struct in
      let scal_name = Alpha.get_new_name Naming.new_struct_field in
      let l =
        match lfield with Some s -> s | None -> Alpha.get_new_name Naming.new_struct_list_field
      in
      let mems = [ (l, list_t); (scal_name, orig_t) ] in
      Structs.add_name name mems;
      (TStruct (name, mems), l)
  | _ ->
      Log.error (printer_msg "Cannot extend state for type %a" pp_typ orig_t);
      failhere Caml.__FILE__ "extend_state" "Failed to extend state."

let add_list_field input_t orig_t ofb t : string option * term * typ =
  let new_t, new_field_name = get_extension input_t orig_t in
  match ofb.texpr with
  | EFoldR (f, init, body) ->
      let init' = extend_init orig_t new_t init in
      let f' = extend_func orig_t new_t f in
      (Some new_field_name, { t with texpr = EFoldR (f', init', body); ttyp = new_t }, new_t)
  | EFoldL (f, init, body) ->
      let init' = extend_init orig_t new_t init in
      let f' = extend_func orig_t new_t f in
      (Some new_field_name, { t with texpr = EFoldL (f', init', body); ttyp = new_t }, new_t)
  | _ -> failwith "Unexpected."

let outer_fold_bodies (t : term) =
  let ofb =
    let join = Set.union in
    let init = Set.empty (module Terms) in
    let case _ t =
      match t.texpr with EFoldL _ | EFoldR _ -> Some (Set.singleton (module Terms) t) | _ -> None
    in
    Transform.recurse { init; join; case } t
  in
  match Set.to_list ofb with
  | [ x ] -> x
  | _ -> Utils.failhere Caml.__FILE__ "outer_fold_bodies" "Too many outer folds."

let inner_transform ~(tin : typ) ~(ti : typ) (pre : term) (post : acc_op) (otimes : otimes_op) =
  let maybe_lname, tli =
    match ti with
    | TList tli -> (None, tli)
    | TStruct (_, sti_fields) -> (
        match find_list_field sti_fields with
        | Some (fln, TList tli) -> (Some fln, tli)
        | _ -> failwith "Unexpected:0" )
    | _ -> failwith "Unexpected:1"
  in
  let new_t, _ = get_extension ~lfield:maybe_lname (TList tli) tin in
  let pre_body = extend_init tin new_t pre in
  let otimes_b =
    (* Give otimes as a function of e and s, a is parametric *)
    let _f = extend_func tin new_t (mk_lambda [ otimes.e; otimes.s ] otimes.body) in
    match _f.texpr with
    | ELambda ([ e; acc ], body) -> { a = otimes.a; e; s = acc; body }
    | _ -> failwith "Unexpected"
  in
  let post =
    let new_s = mk_var ~name:"_s" new_t in
    match new_t with
    | TStruct (s, (lf, _) :: others) -> (
        let nt =
          match others with
          | [ (mf, _) ] ->
              replace_expr ~old:(mk_vt post.s) ~by:(mk_struct_mem ~s mf (mk_vt new_s)) post.body
          | _ ->
              let _sname = match tin with TStruct (s, _) -> s | _ -> failwith "Unexpected." in
              let f _accum (_mf, _) =
                replace_expr
                  ~old:(mk_struct_mem ~s:_sname _mf (mk_vt post.s))
                  ~by:(mk_struct_mem ~s _mf (mk_vt new_s))
                  _accum
              in
              List.fold ~f ~init:post.body others
        in
        let fv = Set.diff (Analyze.free_variables nt) (VarSet.of_list [ new_s; post.a ]) in
        match Set.to_list fv with
        (* Should only get the old accumulator, which in this case should be of list type. *)
        | [ old_accum ] -> (
            match old_accum.vtype with
            | TStruct (sti, mems) ->
                let body =
                  let f nt (fname, _) =
                    replace_expr
                      ~old:(mk_struct_mem ~s:sti fname (mk_vt old_accum))
                      ~by:(mk_struct_mem ~s lf (mk_vt new_s))
                      nt
                  in
                  List.fold ~f ~init:nt mems
                in
                { a = otimes.a; s = new_s; body }
            | TList tli' when ETypes.(tli = tli') ->
                {
                  a = otimes.a;
                  s = new_s;
                  body =
                    replace_expr ~old:(mk_vt old_accum) ~by:(mk_struct_mem ~s lf (mk_vt new_s)) nt;
                }
            | _ -> failwith "Unexpected" )
        | _ -> failwith "Unexpected." )
    | _ -> failwith "Unexpected."
    (* Should not happen given construction of new_t *)
  in
  (pre_body, post, otimes_b)

(* Separate the body into init, pre, post, otimes *)
let dissect (body : term) : term * acc_op * acc_op * otimes_op =
  let lift_inner ti tinner (pre : term) (post : acc_op) (otimes : otimes_op) =
    let list_case tli =
      match tinner with
      | TStruct (_, stin_fields) -> (
          match find_list_field stin_fields with
          (* No need to do anything *)
          | Some _ -> (pre, post, otimes)
          (* Need to add a list field, and the projection. *)
          | None -> inner_transform ~tin:tinner ~ti pre post otimes )
      (* Both are lists of the same type, nothing to do. *)
      | TList tlin when ETypes.(tlin = tli) -> (pre, post, otimes)
      (* A simple non-struct type, need to extend. *)
      | _ -> inner_transform ~tin:tinner ~ti pre post otimes
    in
    let struct_case _ _ =
      match tinner with
      | TList _ -> failwith "Dissect single-pass function: struct_case, list"
      | TStruct (_, stin_fields) -> (
          match find_list_field stin_fields with
          | Some _ -> failwith "Unexpected missing list compoenent in struct."
          | None -> inner_transform ~tin:tinner ~ti pre post otimes )
      | _ -> inner_transform ~tin:tinner ~ti pre post otimes
    in
    (* Outer type is at least List, since it has been extended. *)
    match ti with
    | TStruct (sti, sti_fields) -> struct_case sti sti_fields
    | TList tli -> list_case tli
    | _ -> failwith "Dissect single-pass function: unexpected non-list non-struct type."
  in
  let dissect_inner ti a s lbody : term * acc_op * otimes_op =
    let ofb : term = outer_fold_bodies lbody in
    let s', e, otimes_raw, init_of_fold =
      match ofb.texpr with
      | EFoldL ({ texpr = ELambda ([ e; s' ], body); _ }, init, _)
      | EFoldR ({ texpr = ELambda ([ e; s' ], body); _ }, init, _) ->
          (s', e, body, init)
      | _ -> failwith "Dissect single-pass function: Expected fold here."
    in
    let post : acc_op =
      let post_binding =
        Transform.recurse
          {
            init = Set.empty (module Terms);
            join = Set.union;
            case =
              (fun _ t ->
                match t.texpr with
                | ELet (_, t', _) when Terms.(t' = ofb) -> Some (Set.singleton (module Terms) t)
                | _ -> None);
          }
          lbody
      in
      match Set.to_list post_binding with
      | [] -> { s; a; body = mk_vt s }
      | [ { texpr = ELet (Var x, _, body); _ } ] -> { s = x; a; body }
      | _ -> failwith "Dissect single-pass function: Expected only one fold."
    in
    let otimes : otimes_op = { s = s'; a; e; body = otimes_raw } in
    let t_inner : typ = type_of_exn otimes_raw in
    if ETypes.(t_inner = ti) then (init_of_fold, post, otimes)
    else lift_inner ti t_inner init_of_fold post otimes
  in
  match body.texpr with
  | EFoldR ({ texpr = ELambda ([ elt; acc ], lbody); _ }, init, _)
  | EFoldL ({ texpr = ELambda ([ elt; acc ], lbody); _ }, init, _) ->
      let tinit = type_of_exn init in
      let pre, post, otimes = dissect_inner tinit elt acc lbody in
      let pre' = reduce_exn pre in
      let postbody' = reduce_exn post.body in
      (init, { s = acc; a = elt; body = pre' }, { post with body = postbody' }, otimes)
  | _ -> failwith "Dissect single-pass function: Expected a fold"

let extend_state (input_type : typ) (t : term) ~(outer_fold : term) =
  match type_of outer_fold with
  | Ok (TStruct (s, fields)) -> (
      match find_list_field fields with
      | Some (l, _) -> (false, (Some l, t, TStruct (s, fields)))
      | None -> (true, add_list_field input_type (TStruct (s, fields)) outer_fold t) )
  | Ok (TList x) -> (false, (None, t, TList x))
  | Ok typ -> (true, add_list_field input_type typ outer_fold t)
  | Error s ->
      TermPp.typecheck_err s;
      Utils.failhere Caml.__FILE__ "extend_state" "Too many outer folds."

(* ============================================================================================= *)
(* ============================  SFSP SPECIFIC SKETCHING HANDLES =============================== *)
(* ============================================================================================= *)

let draw_sketches_otimes (si : soln_info) (k : int) : otimes_op list =
  let post = Unfold.reduce_exn si.post.body in
  let cond_post = Set.to_list (Analyze.get_conditions post) in
  let otimes = Unfold.reduce_exn si.otimes.body in
  let fv_ot = Lang.Analyze.free_variables otimes in
  let cond_sketches =
    let cond_seeds =
      List.map
        ~f:(fun cond ->
          match (otimes.texpr, cond.texpr) with
          | EStruct fields, EMemStruct (_, field, _) -> (
              match List.Assoc.find ~equal:String.equal fields field with
              | Some x -> Some (Solve.Sketching.diversify x k)
              | _ -> None )
          | _ -> Some (Solve.Sketching.diversify ~seeds:(Some fv_ot) cond k))
        cond_post
    in
    let otimess =
      List.map
        ~f:(fun cond_seed ->
          match (otimes.texpr, si.otimes.s.vtype) with
          | EStruct fields, TStruct (s, _) ->
              let f (fname, ft) =
                if is_list_type ft then
                  let cft =
                    type_term_exn (mk_ite cond_seed ft (mk_struct_mem ~s fname (mk_vt si.otimes.s)))
                  in
                  (fname, cft)
                else (fname, ft)
              in
              { otimes with texpr = EStruct (List.map ~f fields) }
          | _ -> otimes)
        (List.filter_map ~f:id cond_seeds)
    in
    List.map ~f:(fun y -> { si.otimes with body = y }) otimess
  in
  si.otimes :: cond_sketches

let draw_sketches_pre (si : soln_info) (k : int) : acc_op list =
  let div_pre =
    let fv = Lang.Analyze.free_variables si.pre.body in
    let seeds = Some (Set.add (Set.add fv si.pre.a) si.pre.s) in
    Solve.Sketching.diversify ~seeds si.pre.body k
  in
  [ si.pre; { si.pre with body = div_pre } ]

let draw_sketches_post (si : soln_info) (k : int) : acc_op list =
  let div_post =
    let fv = Lang.Analyze.free_variables si.post.body in
    let seeds = Some (Set.add (Set.add fv si.post.a) si.post.s) in
    Solve.Sketching.diversify ~seeds si.post.body k
  in
  [ si.post; { si.post with body = div_post } ]

let gen_sketches (base_si : soln_info) (complex : int) : soln_info list =
  let s_otimes = draw_sketches_otimes base_si complex in
  let s_pre = draw_sketches_pre base_si complex in
  let s_post = draw_sketches_post base_si complex in
  let combine x =
    let f (otimes, pre, post) =
      {
        base_si with
        tmp_file_sk = Utils.Naming.tmp_file "sfsp_sketch" Naming.ext_racket;
        tmp_file_out = Caml.Filename.temp_file "sfsp_output" ".txt";
        otimes;
        pre;
        post;
      }
    in
    List.map ~f (List.concat (List.concat x))
  in
  combine (ListTools.cartesian3 s_otimes s_pre s_post)

(* ============================================================================================= *)
(* ================================ PARSING RESPONSE =========================================== *)
(* ============================================================================================= *)

let parse_defs (si : soln_info) (definitions : Sexp.t list) : soln_info =
  let norm t = AcTerm.simplify_full (AcTerm.norm t) in
  let define_op si opn body =
    let vars =
      match opn with
      | s when String.equal s otimes_func_name ->
          VarSet.of_list [ si.otimes.a; si.otimes.e; si.otimes.s ]
      | s when String.equal s pre_func_name -> VarSet.of_list [ si.pre.a; si.pre.s ]
      | s when String.equal s post_func_name -> VarSet.of_list [ si.post.a; si.post.s ]
      | _ -> VarSet.empty
    in
    let t = norm (Solve.Rosette.parse_response vars body) in
    match opn with
    | s when String.equal s otimes_func_name -> { si with otimes = { si.otimes with body = t } }
    | s when String.equal s pre_func_name -> { si with pre = { si.pre with body = t } }
    | s when String.equal s post_func_name -> { si with post = { si.post with body = t } }
    | _ -> si
  in
  let f si definition =
    match definition with
    | Sexp.(List [ Atom "define"; List (Atom opn :: _); body ]) -> define_op si opn body
    | Sexp.Atom "'" -> si
    | _ ->
        pf stdout "%a@." Sexp.pp_hum definition;
        failwith "not a def"
  in
  List.fold ~f ~init:si definitions

(* ============================================================================================= *)
(* ================================ MAIN ENTRY POINT =========================================== *)
(* ============================================================================================= *)

let func_multiple_pass (_ : variable list) (body : term) : bool =
  match Lang.Analyze.num_nested_folds body with
  | 0 ->
      Log.debug (fun fmt () -> Fmt.pf fmt "No folds in function.");
      false
  | 1 ->
      Log.debug (fun fmt () -> Fmt.pf fmt "Only one fold in function.");
      false
  | 2 ->
      Log.debug (fun fmt () -> Fmt.pf fmt "Two nested folds in function.");
      true
  | _ ->
      Log.error (wrap "More than two nested folds not supported.");
      Utils.failhere Caml.__FILE__ "func_multiple_pass"
        "Modular approach for nested folds not implemented."

let no_solution () =
  Log.error (wrap "No single-pass function could be synthesized.");
  failwith "Abort synthesis, not a single-pass function."

(**
  Transform an input function that is a fold (or loop) on inputs to a self-forld single-pass
  implementation. The current implementation uses syntax-guided synthesis to find a suitable
  implementation, but is quite sensitive to the input being two nested folds.
  *)
let single_pass_transform (asserts : (VarSet.t * term) list) (inputs : variable list) (body : term)
    (oset : VarSet.t) : soln_info =
  let input_type, input =
    match inputs with
    | [ lv ] -> (lv.vtype, lv)
    | _ -> failwith "multiple input list not supported for now."
    (* TTup (List.map ~f:(fun v -> v.vtype) inputs) *)
  in
  let output_type =
    match type_of body with
    | Ok t -> t
    | Error e ->
        TermPp.typecheck_err e;
        failwith "Typecheck failed."
  in
  Log.info
    (printer2_msg "Synthesizing single pass function@;@[%a -> %a@]." pp_typ input_type pp_typ
       output_type);
  let synt_time = Unix.gettimeofday () in
  let outer_fold = outer_fold_bodies body in
  let func_name = Lang.Alpha.get_new_name "f" in
  let added_list, (list_field_name, target_f, target_t) =
    extend_state input_type body ~outer_fold
  in
  let f_init, pre, post, otimes = dissect target_f in
  let as_set = match Set.to_list oset with [ v ] -> Variable.has_attr SetLike v | _ -> false in
  let ia = List.find_map asserts ~f:(fun (vs, t) -> if Set.mem vs input then Some t else None) in
  let basic_sketch_info =
    {
      synt_time = 0.0;
      tmp_file_sk = Utils.Naming.tmp_file "sfsp_sketch" Naming.ext_racket;
      tmp_file_out = Caml.Filename.temp_file "sfsp_output" ".txt";
      func_name;
      func_input = input;
      func_input_assert = ia;
      func_body = body;
      return_type = output_type;
      return_type_as_set = as_set || added_list;
      target_func_name = Lang.Alpha.get_new_name (func_name ^ "_sp");
      target_accum_type = target_t;
      list_field_name;
      init = f_init;
      pre;
      post;
      otimes;
    }
  in
  let all_sketches = gen_sketches basic_sketch_info !Config.sfsp_sketch_complex in
  (* Solve in parallel by batches of Config.num_parallel_processes *)
  let maybe_solns =
    Solve.Rosette.solve_sketches ~use_lwt:true compile_sfsp_sketch
      (fun si -> (si.tmp_file_sk, si.tmp_file_out))
      all_sketches
  in
  let parsed_solns =
    let f (si, soln) =
      match soln with
      | [ Sexp.Atom "unsat" ] -> None
      | [ Sexp.Atom "sat" ] -> Some (true, si)
      | definitions -> Some (false, parse_defs si definitions)
    in
    match maybe_solns with Some solns -> List.filter_map ~f solns | None -> []
  in
  let best_soln =
    match List.filter_map ~f:(fun (sat, si) -> if sat then Some si else None) parsed_solns with
    | si :: _ -> Some si
    | [] -> ( match parsed_solns with (_, si) :: _ -> Some si | [] -> None )
  in
  let synt_time = Unix.gettimeofday () -. synt_time in
  match best_soln with
  | Some soln ->
      Log.success (fun f () ->
          Fmt.pf f "Single pass translation: solution found (%4.3f s)." synt_time);
      { soln with synt_time }
  | None -> no_solution ()

(* ============================================================================================= *)
(* ============= Entry point : translate to self-fold single-pass ============================== *)
(* ============================================================================================= *)
let to_single_pass (asserts : (VarSet.t * term) list) ((t, o) : term * VarSet.t) :
    (soln_info, float * (VarSet.t * term) list * term) Either.t =
  let start = Unix.gettimeofday () in
  (* The input is a function, and at least one argument is a list *)
  let lists, body =
    match t.texpr with
    | ELambda (args, body) ->
        (List.filter ~f:(fun v -> match v.vtype with TList _ -> true | _ -> false) args, body)
    | _ -> ([], mk_empty_term)
  in
  let applicable_assertions =
    List.filter asserts ~f:(fun (args, _) ->
        not (Set.is_empty (Set.inter args (VarSet.of_list lists))))
  in
  if List.length lists < 1 then (
    Utils.Log.error (Utils.wrap "Loops of function do not have a list as input.");
    Caml.exit 0 )
  else if func_multiple_pass lists body then
    Either.First (single_pass_transform applicable_assertions lists body o)
  else Either.Second (Unix.gettimeofday () -. start, applicable_assertions, body)

(* ============================================================================================= *)
(* ================================ PARSING RESPONSE =========================================== *)
(* ============================================================================================= *)

let div_parse_defs (pi : pred_soln) (definitions : Sexp.t list) : pred_soln =
  let aux divide =
    let partitions =
      ref (List.map ~f:(fun (vp, pbody) -> (vp.vname, (vp, pbody))) divide.partitions)
    in
    let pivots = ref divide.pivots in
    let is_pivot_func s = List.exists ~f:(fun (_, (sf, _), _) -> String.equal sf.vname s) !pivots in
    let get_pivot_func s = List.find ~f:(fun (_, (sf, _), _) -> String.equal sf.vname s) !pivots in
    let update_pivot_sel pivot_v pivot_body =
      let f (pv, (fv, fargs), t) =
        if pv.vid = pivot_v.vid then (pv, (fv, fargs), pivot_body) else (pv, (fv, fargs), t)
      in
      pivots := List.map ~f !pivots
    in
    let vars =
      VarSet.of_list ((divide.x :: ListTools.lfst divide.partitions) @ get_pivots divide)
    in
    let define_op opn body =
      match opn with
      | s when List.Assoc.mem !partitions ~equal:String.equal s ->
          let vp, pbody = List.Assoc.find_exn !partitions ~equal:String.equal s in
          let v_pbody = Lang.Analyze.vars_of pbody in
          let resp = Solve.Rosette.parse_response (vars $|| v_pbody) body in
          partitions := List.Assoc.add !partitions ~equal:String.equal s (vp, resp)
      | s when is_pivot_func s -> (
          match get_pivot_func s with
          | Some (pivot_v, (_, _), pivot_sel) ->
              let v_pi = Lang.Analyze.vars_of pivot_sel in
              let resp = Solve.Rosette.parse_response (vars $|| v_pi) body in
              update_pivot_sel pivot_v resp
          | None -> failwith "Unexpected." )
      | _ -> ()
    in
    let f definition =
      match definition with
      | Sexp.(List [ Atom "define"; List (Atom opn :: _); body ]) -> define_op opn body
      | Sexp.Atom "'" -> ()
      | _ ->
          pf stdout "%a@." Sexp.pp_hum definition;
          failwith "not a def"
    in
    List.iter ~f definitions;
    {
      pi with
      divide = Some { divide with pivots = !pivots; partitions = List.map ~f:snd !partitions };
    }
  in
  match pi.divide with Some d -> aux d | None -> pi

let join_parse_defs (ji : join_soln) (definitions : Sexp.t list) : join_soln =
  let vars = VarSet.of_list (fst ji.join) in
  let extra_env = Analyze.vars_of (snd ji.join) in
  let join = ref (snd ji.join) in
  let define_op opn body =
    match opn with
    | s when String.equal Solve.SfspSketches._join_name s ->
        let resp = Solve.Rosette.parse_response (Set.union extra_env vars) body in
        join := resp
    | _ -> ()
  in
  let f definition =
    match definition with
    | Sexp.(List [ Atom "define"; List (Atom opn :: _); body ]) -> define_op opn body
    | Sexp.Atom "'" -> ()
    | _ ->
        pf stdout "%a@." Sexp.pp_hum definition;
        failwith "not a def"
  in
  List.iter ~f definitions;
  { ji with join = (fst ji.join, !join) }

let quadratic_case pred_soln join_sketch =
  let join_time = Unix.gettimeofday () in
  let maybe_join_solns =
    Solve.Rosette.solve_sketches compile_join_sketch
      (fun ji -> (ji.tmp_file_sk, ji.tmp_file_out))
      [ add_join_to_pred_soln pred_soln join_sketch ]
  in
  let solns = Solve.Rosette.parse_with ~f:join_parse_defs maybe_join_solns in
  let join_time = Unix.gettimeofday () -. join_time in
  let solns = List.map solns ~f:(fun soln -> { soln with synt_time = join_time }) in
  (match solns with [] -> Log.warning ~level:(-1) (wrap "No join found.") | _ -> ());
  if !Config.dump_solutions then List.iter ~f:dump_join_soln solns;
  solns

let with_divide_solved join_sketch div_solns =
  let join_time = Unix.gettimeofday () in
  (* Synthesizing or checking guessed join. *)
  let maybe_join_solns =
    Solve.Rosette.solve_sketches compile_join_sketch
      (fun ji -> (ji.tmp_file_sk, ji.tmp_file_out))
      (List.map ~f:(fun pi -> add_join_to_pred_soln pi join_sketch) div_solns)
  in
  let solns = Solve.Rosette.parse_with ~f:join_parse_defs maybe_join_solns in
  let join_time = Unix.gettimeofday () -. join_time in
  let solns = List.map solns ~f:(fun soln -> { soln with synt_time = join_time }) in
  if List.length solns = 0 then
    Log.warning ~level:(-1) (fun f () ->
        Fmt.(pf f "❌ No join found (unsat in %4.2f s)." join_time))
  else Log.success (fun f () -> Fmt.(pf f "Join found in %4.2f s." join_time));
  if !Config.dump_solutions then List.iter ~f:dump_join_soln solns;
  solns

let solve_div_sketches ?(skip = false) pred_solns =
  let div_time = Unix.gettimeofday () in
  let solns =
    if skip then Some []
    else
      Solve.Rosette.solve_sketches compile_divide_sketch
        (fun pi -> (pi.tmp_file_sk, pi.tmp_file_out))
        (List.filter ~f:(fun (ps : pred_soln) -> is_some ps.divide) pred_solns)
  in
  (div_time, solns)

let parse_divs (div_start_time, solns) =
  let div_time = Unix.gettimeofday () -. div_start_time in
  let solns = Solve.Rosette.parse_with ~f:div_parse_defs solns in
  List.iter
    ~f:(fun pi ->
      Log.success (fun f () -> pf f "Divide function found in %4.2f s." div_time);
      Log.debug (fun f () ->
          Fmt.(
            pf f "Divide function :@;@[%a@]@." (option rpp_term)
              (Option.map ~f:term_of_div_soln pi.divide))))
    solns;
  add_div_synt_times div_time solns

(* ============================================================================================= *)
(* ================================ MAIN ENTRY POINT FOR PERMINV   ============================= *)
(* ============================================================================================= *)

let rec budget_loop (budget : cbudget) (sfsp : std_soln) =
  Log.success Fmt.(fun f () -> pf f "===== Budget: (%i, %i, %i) ====" budget.k budget.m budget.c);
  SymbExe.reset ();
  Solve.(
    DivideSketches.divide_len := max !DivideSketches.divide_len ((2 * budget.c) - 1);
    JoinSketches.join_len := max !JoinSketches.join_len budget.c);
  let next_budget () =
    match increase_budget budget with Some b -> budget_loop b sfsp | None -> []
  in
  Structs.restore ();
  match discover_predicate_and_sketches budget sfsp with
  | Some (pred_solns, join_sketch) -> (
      match parse_divs (solve_div_sketches ~skip:skip_flag pred_solns) with
      | _ :: _ as div_solns ->
          let solns = with_divide_solved join_sketch div_solns in
          solns @ next_budget ()
      | [] ->
          let pred_soln = List.hd_exn pred_solns in
          if Option.is_none pred_soln.divide then
            let qc = quadratic_case pred_soln join_sketch in
            qc @ next_budget ()
          else (
            (* Special lifting case: predicate is too strong, no divide found. *)
            Log.warning_msg "Predicate found, but no divide function: attempt lifting.";
            SketchBuilders.include_two_pivots := true;
            match lift_by_weakening pred_soln with
            | Some (lifted_soln, new_join_sketch) -> (
                match parse_divs (solve_div_sketches [ lifted_soln ]) with
                | [] ->
                    Log.warning_msg "Lifting succeeded, but no solution found.";
                    next_budget ()
                | _ as solns ->
                    let solns = with_divide_solved new_join_sketch solns in
                    solns @ next_budget () )
            | None ->
                Log.warning_msg "❌ No lifting found.";
                next_budget () ) )
  | None ->
      Log.warning_msg "❌ No predicate for current budget.";
      next_budget ()

let solve (si : soln_info) =
  (* Use lwt for parallel solving of sketches. Basic process creation seems to have problems
     as of now. *)
  Config.always_use_lwt := true;
  let si_std = std_soln_info si in
  Log.info (printer_msg "Single pass function:@;%a" (box pp_soln_info_func) si);
  Structs.save ();
  let starting_budget =
    if !Config.k >= 0 && !Config.m >= 0 && !Config.c >= 0 then
      { n = 2; k = !Config.k; m = !Config.m; c = !Config.c }
    else (
      Config.budget_not_specified := true;
      Config.dump_solutions := true;
      { n = 2; k = 0; c = 2; m = 2 } )
  in
  budget_loop starting_budget si_std

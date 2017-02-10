open SketchTypes
open Utils
open SPretty

let debug = ref false

let auxiliary_variables : Cil.varinfo Utils.IH.t = IH.create 10

let left_auxiliaries = ref VS.empty
let right_auxiliaries = ref VS.empty

let init () =
  IH.clear auxiliary_variables;
  left_auxiliaries := VS.empty;
  right_auxiliaries := VS.empty

(* Returns true is the expression is a hole. The second
   boolean in the pair is useful when we are trying to merge
   holes. Any merge involving a left hole yields a left hole,
   and we can have a right holes if and only if all holes merged
   are right holes. *)
let is_a_hole =
  function
  | SkHoleL _ -> true
  | SkHoleR _ -> true
  | _ -> false

let is_right_hole =
  function
  | SkHoleR _ -> true
  | _ -> false

let replace_hole_type t' =
  function
  | SkHoleR (t, cs) -> SkHoleR(t', cs)
  | SkHoleL (t, v, cs) -> SkHoleL(t', v, cs)
  | e -> e

let type_of_hole =
  function
  | SkHoleR (t, _) | SkHoleL (t, _, _) -> Some t
  | _ -> None

let completion_vars_of_hole =
  function
  | SkHoleR (_, cs) -> cs
  | SkHoleL (_, _, cs) -> cs
  | _ -> CS.empty

let rec make_holes ?(max_depth = 1) ?(is_final = false) (state : VS.t)
    (optype : operator_type) =
  let holt t = (t, optype) in
  function
  | SkVar sklv ->
    begin
      match sklv with
      | SkVarinfo vi ->
        let t = symb_type_of_ciltyp vi.Cil.vtype in
        if (IH.mem auxiliary_variables vi.Cil.vid) && is_final
        then SkVar sklv, 0
        else
          (if VS.mem vi state
           then SkHoleL (holt t, sklv, CS.complete_all (CS.of_vs state)), 1
           else SkHoleR (holt t, CS.complete_right (CS.of_vs state)), 1)
      | SkArray (sklv, expr) ->
        (** Array : for now, cannot be a stv *)
        let t = type_of_var sklv in
        (match t with
         | Vector (t, _) -> SkHoleR (holt t, CS.complete_right (CS.of_vs state)), 1
         | _ -> failwith "Unexpected type in array")
      | SkTuple vs -> SkVar (SkTuple vs), 0
    end

  | SkConst c ->
    let cs = CS.complete_right (CS.of_vs state) in
    begin
      match c with
      | CInt _ | CInt64 _ -> SkHoleR (holt Integer, cs), 1
      | CReal _ -> SkHoleR (holt Real, cs), 1
      | CBool _ -> SkHoleR (holt Boolean, cs), 1
      | _ -> SkHoleR (holt Unit, cs), 1
    end

  | SkFun skl -> SkFun (make_join ~state:state ~skip:[] skl), 0

  | SkBinop (op, e1, e2) ->
    let holes1, d1 = merge_leaves max_depth (make_holes state optype e1) in
    let holes2, d2 = merge_leaves max_depth (make_holes state optype e2) in
    SkBinop (op, holes1, holes2), max d1 d2

  | SkUnop (op, e) ->
    merge_leaves max_depth (make_holes state optype e)

  | SkCond (c, li, le) ->
    let ch, _ = make_holes state optype c in
    SkCond (ch ,
            make_join ~state:state ~skip:[] li,
            make_join ~state:state ~skip:[] le), 0

  | SkQuestion (c, ei, ee) ->
    let h1, d1  = merge_leaves max_depth (make_holes state optype ei) in
    let h2, d2 = merge_leaves max_depth (make_holes state optype ee) in
    let hc, dc = merge_leaves max_depth (make_holes state optype c) in
    SkQuestion (hc, h1, h2), max (max d1 d2) dc

  | SkApp (t, vo, args) ->
    let new_args, depths =
      ListTools.unpair (List.map (make_holes state optype) args) in
    SkApp (t, vo, new_args), ListTools.intlist_max depths

  | _ as skexpr ->  skexpr, 0


and make_hole_e
    ?(max_depth = 2)
    ?(is_final=false)
    (state : VS.t) (e : skExpr) =
  let optype = analyze_optype e in
  make_holes
    ~max_depth:max_depth
    ~is_final:is_final
    state optype e

and make_assignment_list state skip =
  List.map (fun (v, e) ->
      match e with
      | SkVar v when List.mem v skip -> (v, e)

      | _ ->
        let vi = check_option (vi_of v) in
        if VS.mem vi !left_auxiliaries ||
           VS.mem vi !right_auxiliaries  then
          (v, SkHoleL (((type_of e), Basic), v,
                       CS.complete_all (CS.of_vs state)))
        else
          (v, fst (make_hole_e ~is_final:true state e)))


and make_join ~(state : VS.t) ~(skip: skLVar list) =
  function
  | SkLetExpr ve_list ->
    SkLetExpr (make_assignment_list state skip ve_list)

  | SkLetIn (ve_list, cont) ->
    let to_skip = fst (ListTools.unpair ve_list) in
    SkLetIn (
      make_assignment_list state skip ve_list,
      make_join ~state:state ~skip:(skip@to_skip) cont)

and merge_leaves max_depth (e,d) =
  if d + 1 >= max_depth then
    begin
      match e with
      | SkUnop (op , h) when is_a_hole h ->
        let ht, ot = check_option (type_of_hole h) in
        let op_type =
          (match type_of_unop ht op with
           | Some t -> t
           | None -> failwith "Type error in holes")
        in
        let ht_final =
          if op_type = ht then op_type else Function (ht, op_type)
        in
        replace_hole_type (ht_final, ot) h, d


      | SkBinop (op, h1, h2) when is_a_hole h1 && is_a_hole h2 ->
        let t1, o1 = check_option (type_of_hole h1) in
        let t2, o2 = check_option (type_of_hole h2) in
        let rh_h1 = is_right_hole h1 in
        let rh_h2 = is_right_hole h2 in
        let vars = CS.union (completion_vars_of_hole h1)
            (completion_vars_of_hole h2)
        in
        (match (type_of_binop (res_type t1) (res_type t2) op) with
         | Some t ->
           if t1 = t2 && rh_h1 && rh_h2 then
             let ht_final = Function (t1, t) in
             SkHoleR ((ht_final, join_optypes o1 o2), vars), d
           else
             SkBinop(op, h1, h2), d + 1

         | None -> failwith "Type error in holes")

      | SkApp (t, ov, el) ->
        let all_holes, vars =
          List.fold_left
            (fun (is_h, vars) e ->
               (is_h && is_right_hole e,
                CS.union vars (completion_vars_of_hole e)))

            (true, CS.empty) el
        in
        if all_holes
        then
          SkHoleR ((t, NotNum), vars), d
        else
          let el', _ = ListTools.unpair
              (List.map (fun e_ -> merge_leaves max_depth (e_, d)) el)
          in SkApp (t, ov, el'), d

      | SkQuestion (c, ei, ee) ->
        begin
          if is_a_hole ei && is_a_hole ee && is_a_hole c then
            SkQuestion (SkHoleR ((Boolean, NotNum), completion_vars_of_hole c),
                        ei, ee), d
          else
            e, 0
        end
      (** Do not propagate expression depth into control statements*)
      | _ -> (e, 0)
    end
  else
    (e, d + 1)

let set_types_and_varsets =
  let adapt_vs_and_t cs t =
    let nvs = filter_cs_by_type (input_type_or_type t) cs in
    if CS.cardinal nvs = 0 then
      match t with
      | Function (it, rt) ->
        let nvs' = filter_cs_by_type rt cs in
        nvs', rt
      | _ -> nvs, t
    else
      nvs, t
  in
  let aux_set =
    transform_expr
      (fun e -> is_a_hole e)
      (fun rfun e ->
         match e with
         | SkHoleL ((t, o), v, vs) ->
           let nvs, nt = adapt_vs_and_t vs t in
           SkHoleL ((nt, o), v, nvs)

         | SkHoleR ((t, o), vs) ->
           let nvs, nt = adapt_vs_and_t vs t in
           SkHoleR ((nt, o), nvs)

         | _ -> rfun e)

      identity identity
  in
  transform_exprs aux_set

let build (state : VS.t) (sklet : sklet) =
  set_types_and_varsets (make_join ~state:state ~skip:[] sklet)
